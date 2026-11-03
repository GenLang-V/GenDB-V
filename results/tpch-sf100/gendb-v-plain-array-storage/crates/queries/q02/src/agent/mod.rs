//! TPC-H Q2 (minimum-cost supplier) over the flat storages.
//!
//! Plan (all structures are built inside the call):
//! 1. nations of the region `$3` (region and nation are tiny);
//! 2. in parallel: the keys of the parts with `p_size = $1 AND p_type LIKE $2` (fast path for `'%<ascii literal>'`,
//!    a byte-suffix test; any other pattern is evaluated serially with the verified `LIKE`, which also finds the
//!    statement's exact `LIKE` error), and for every supplier whether it lies in the region;
//! 3. a key set (bitmap) of the qualifying part keys;
//! 4. in parallel: the partsupp rows whose part key is in the set and whose supplier is in the region (the hits);
//! 5. the hits whose supply cost is least for their part key (the subquery's minimum) are the candidates; the answer
//!    is the first 100 candidates by `s_acctbal DESC, n_name, s_name, p_partkey`.
//! With one worker, each parallel step is a single task run on the calling thread (no spawn, and the thread stays
//! busy), and the partsupp scan uses longer batches (`PS_BATCH_SOLO`).
//! The proof: `sem_*` give the SQL meaning of the statement in terms of the stored columns (`model`), `sem_plan`
//! reduces the kept rows to the candidates (primary keys make each candidate's row unique), and `answer`/`topk`
//! show the answer is an allowed `ORDER BY .. LIMIT 100` output.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::relation::product_rows;
use crate::exec::value::EVal;
use crate::query::{param_domain, query_spec_at};
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::link::join::keep;
use crate::link::query::{view_rows, lemma_map_multiset};
use crate::link::outcome::lemma_outcome_sorted;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_sub::lits;
use crate::agent::sem_outer::*;
use crate::agent::sem_plan::*;
use crate::agent::columns::*;
use crate::agent::pipeline::*;
use crate::agent::answer::*;
use crate::agent::scan_partsupp::ps_hit;
use crate::agent::common::key_set::KeySet;
use crate::agent::common::like_suffix::suffix_pattern;

pub mod common;
pub mod scan_part;
pub mod scan_partsupp;
pub mod model;
pub mod sem_ast;
pub mod sem_sub;
pub mod sem_outer;
pub mod sem_plan;
pub mod topk;
pub mod columns;
pub mod pipeline;
pub mod answer;

verus! {

/// Whether `pat` is `%` followed by ASCII bytes other than `%`, `_` and backslash.
fn is_suffix_pattern(pat: &[u8]) -> (r: bool)
    ensures r == suffix_pattern(pat@),
{
    let n = pat.len();
    if n == 0 || pat[0] != 0x25u8 {
        return false;
    }
    let mut i: usize = 1;
    while i < n
        invariant
            n == pat@.len(), 1 <= i <= n,
            forall|j: int| 1 <= j < i ==> #[trigger] pat@[j] < 0x80u8 && pat@[j] != 0x25u8 && pat@[j] != 0x5Fu8 && pat@[j] != 0x5Cu8,
        decreases n - i,
    {
        let b = pat[i];
        if b >= 0x80u8 || b == 0x25u8 || b == 0x5Fu8 || b == 0x5Cu8 {
            return false;
        }
        i = i + 1;
    }
    true
}

/// Expected partsupp hits per 2^20 rows: (qualifying parts / parts) * (flagged suppliers / suppliers), as a capacity
/// hint for the scan's buffers (any value is correct).
fn expected_hits_per_mega(nq: usize, np: usize, nflag: usize, ns: usize) -> u64 {
    let lim: usize = 0xFFFF_FFFF;
    if np == 0 || ns == 0 || nq > lim || nflag > lim || np > lim || ns > lim {
        return 0x10_0000;
    }
    assert(nq * nflag <= 0xFFFF_FFFF * 0xFFFF_FFFF) by (nonlinear_arith) requires nq <= 0xFFFF_FFFF, nflag <= 0xFFFF_FFFF;
    assert(np * ns <= 0xFFFF_FFFF * 0xFFFF_FFFF) by (nonlinear_arith) requires np <= 0xFFFF_FFFF, ns <= 0xFFFF_FFFF;
    let num: u128 = nq as u128 * nflag as u128 * 0x10_0000u128;
    assert(np * ns >= 1) by (nonlinear_arith) requires np >= 1, ns >= 1;
    let den: u128 = np as u128 * ns as u128;
    let e = num / den;
    if e > 0x10_0000 { 0x10_0000 } else { e as u64 }
}

/// An empty table makes the statement's value the empty result.
proof fn lemma_answer_empty(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>)
    requires
        stores_wf(sv),
        int_in_range(IntKind::Int4, v),
        part_n(sv) == 0 || ps_n(sv) == 0 || supp_n(sv) == 0 || nat_n(sv) == 0 || reg_n(sv) == 0,
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db)
            ==> ordered_ok(db, query_spec_at(lits(v, pat, rp)), Ok::<Relation, SqlError>(Seq::<Row>::empty())),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies ordered_ok(db, query_spec_at(lits(v, pat, rp)), Ok::<Relation, SqlError>(Seq::<Row>::empty())) by {
        lemma_tables(sv, db);
        let ps = lits(v, pat, rp);
        lemma_query_shape(ps);
        assert forall|a: int, b: int, c: int, d: int, e: int| #[trigger] in5(sv, a, b, c, d, e) implies like_res(p_type(sv, a), pat) is Ok by {}
        lemma_body_ok(db, sv, v, pat, rp);
        let (p, s, q, n, r) = (part_rows(sv), supp_rows(sv), ps_rows(sv), nat_rows(sv), reg_rows(sv));
        let l1 = product_rows(p, s);
        let l2 = product_rows(l1, q);
        let l3 = product_rows(l2, n);
        crate::bridge::relation::lemma_product_rows_elems(p, s);
        crate::bridge::relation::lemma_product_rows_elems(l1, q);
        crate::bridge::relation::lemma_product_rows_elems(l2, n);
        crate::bridge::relation::lemma_product_rows_elems(l3, r);
        assert(from5(sv).len() == 0) by {
            if p.len() == 0 || s.len() == 0 { assert(l1.len() == 0); }
            if l1.len() == 0 || q.len() == 0 { assert(l2.len() == 0); }
            if l2.len() == 0 || n.len() == 0 { assert(l3.len() == 0); }
        }
        let kept = keep(from5(sv), outer_keep(sv, v, pat, rp));
        crate::link::join::lemma_keep_members(from5(sv), outer_keep(sv, v, pat, rp));
        let body_rows = kept.map_values(|x: Row| out_row(x));
        assert(body_rows =~= Seq::<Row>::empty());
        let pe = Seq::<Row>::empty();
        assert(sorted_by(order_keys(), pe));
        assert(pe.to_multiset() =~= body_rows.to_multiset());
        lemma_outcome_sorted(db, query_spec_at(ps), body_rows, pe);
        assert(slice_rows(pe, 0, Some(100)) =~= pe);
    }
}

/// A `LIKE` error at part row `a0` (the first one), with every table non-empty, is the statement's value.
proof fn lemma_answer_err(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, a0: int, e: SqlError)
    requires
        stores_wf(sv),
        int_in_range(IntKind::Int4, v),
        part_n(sv) > 0 && ps_n(sv) > 0 && supp_n(sv) > 0 && nat_n(sv) > 0 && reg_n(sv) > 0,
        0 <= a0 < part_n(sv),
        like_res(p_type(sv, a0), pat) == Err::<Val, SqlError>(e),
        forall|a: int| 0 <= a < a0 ==> #[trigger] like_res(p_type(sv, a), pat) is Ok,
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(lits(v, pat, rp)), Err::<Relation, SqlError>(e)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies ordered_ok(db, query_spec_at(lits(v, pat, rp)), Err::<Relation, SqlError>(e)) by {
        lemma_tables(sv, db);
        lemma_query_shape(lits(v, pat, rp));
        lemma_body_err(db, sv, v, pat, rp, a0, e);
    }
}

/// An allowed output of the candidates' rows is an allowed output of the statement.
proof fn lemma_answer_rows(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, out: Seq<Row>)
    requires
        stores_wf(sv),
        keys_ok(sv),
        int_in_range(IntKind::Int4, v),
        like_ok_all(sv, pat),
        answer_ok(sv, v, pat, rp, out),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(lits(v, pat, rp)), Ok::<Relation, SqlError>(out)),
{
    let (cs, p) = choose|cs: Seq<int>, p: Seq<Row>| #![trigger lists_cands(sv, v, pat, rp, cs), sorted_by(order_keys(), p)]
        lists_cands(sv, v, pat, rp, cs)
        && p.to_multiset() == cand_out(sv, v, pat, rp, cs).to_multiset()
        && sorted_by(order_keys(), p)
        && out == slice_rows(p, 0, Some(100));
    lemma_kept_bag(sv, v, pat, rp, cs);
    let kept = keep(from5(sv), outer_keep(sv, v, pat, rp));
    let g = cand_rows(sv, v, pat, rp, cs);
    lemma_map_multiset(kept, g, |x: Row| out_row(x));
    assert(g.map_values(|x: Row| out_row(x)) =~= cand_out(sv, v, pat, rp, cs));
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies ordered_ok(db, query_spec_at(lits(v, pat, rp)), Ok::<Relation, SqlError>(out)) by {
        lemma_tables(sv, db);
        let ps = lits(v, pat, rp);
        lemma_query_shape(ps);
        assert forall|a: int, b: int, c: int, d: int, e: int| #[trigger] in5(sv, a, b, c, d, e) implies like_res(p_type(sv, a), pat) is Ok by {
            assert(0 <= a < part_n(sv));
        }
        lemma_body_ok(db, sv, v, pat, rp);
        lemma_outcome_sorted(db, query_spec_at(ps), kept.map_values(|x: Row| out_row(x)), p);
    }
}

/// The partsupp scan's hit test is the model's hit.
proof fn lemma_hit_equiv(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, qkeys: Seq<i64>, flags: Seq<bool>, c: int)
    requires
        qkeys_ok(sv, v, pat, qkeys),
        flags.len() == supp_n(sv),
        forall|b: int| 0 <= b < supp_n(sv) ==> #[trigger] flags[b] == supp_in_reg(sv, rp, b),
        0 <= c < ps_n(sv),
    ensures ps_hit(qkeys, ps_pkeys(sv), ps_skeys(sv), s_keys(sv), flags, c) == hit(sv, v, pat, rp, c),
{
    let k = ps_pkeys(sv)[c];
    assert((exists|j: int| 0 <= j < qkeys.len() && #[trigger] qkeys[j] == k) == qual_key(sv, v, pat, k as int));
    if ps_hit(qkeys, ps_pkeys(sv), ps_skeys(sv), s_keys(sv), flags, c) {
        let b = choose|b: int| 0 <= b < s_keys(sv).len() && #[trigger] s_keys(sv)[b] == ps_skeys(sv)[c] && flags[b];
        assert(reg_supp(sv, rp, c));
    }
    if hit(sv, v, pat, rp, c) {
        let b = choose|b: int| 0 <= b < supp_n(sv) && #[trigger] s_keys(sv)[b] == ps_skeys(sv)[c] && supp_in_reg(sv, rp, b);
        assert(flags[b]);
    }
}

/// The merged scan output satisfies `hits_ok`.
proof fn lemma_hits_ok(c: Cols, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, set: Arc<KeySet>, flags: Arc<Vec<bool>>,
    dense: bool, h: HitVecs)
    requires
        cols_ok(c, sv),
        qkeys_ok(sv, v, pat, set.keys()),
        flags@.len() == supp_n(sv),
        forall|b: int| 0 <= b < supp_n(sv) ==> #[trigger] flags@[b] == supp_in_reg(sv, rp, b),
        global_ps_scan(c, set, flags, dense, s_keys(sv)[0]).covers_seqs(c.nps as int, hv_seqs(h)),
    ensures hits_ok(sv, v, pat, rp, h),
{
    let g = global_ps_scan(c, set, flags, dense, s_keys(sv)[0]);
    let hs = hv_seqs(h);
    assert forall|i: int| 0 <= i < h.c@.len() implies {
        let cc = #[trigger] h.c@[i] as int;
        let b = h.b@[i] as int;
        &&& 0 <= cc < ps_n(sv)
        &&& hit(sv, v, pat, rp, cc)
        &&& 0 <= b < supp_n(sv)
        &&& s_keys(sv)[b] == ps_skeys(sv)[cc]
        &&& h.pk@[i] == ps_pkeys(sv)[cc]
        &&& h.cost@[i] == ps_costs(sv)[cc]
        &&& h.acct@[i] == s_accts(sv)[b]
    } by {
        assert(g.seq_fields_ok(hs, c.nps as int, i));
        lemma_hit_equiv(sv, v, pat, rp, set.keys(), flags@, h.c@[i] as int);
    }
    assert forall|cc: int| 0 <= cc < ps_n(sv) && #[trigger] hit(sv, v, pat, rp, cc) implies exists|i: int| 0 <= i < h.c@.len() && h.c@[i] == cc by {
        lemma_hit_equiv(sv, v, pat, rp, set.keys(), flags@, cc);
        assert(g.hit(cc));
    }
}

/// TPC-H Q2 over the flat storages (see the module comment).
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_tables(sv, db0);
        lemma_keys(sv, db0);
    }
    let v = params.p0;
    let pat = params.p1;
    let rp = params.p2;
    let ghost ps = params@;
    proof {
        assert(ps == lits(v as int, pat@, rp@));
        assert(int_in_range(IntKind::Int4, v as int));
    }
    // An empty table makes the FROM empty.
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let nps = stores.flat_partsupp.part_len(psi::PS_PARTKEY);
    let ns = stores.flat_supplier.part_len(si::S_SUPPKEY);
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    let nr = stores.flat_region.part_len(ri::R_REGIONKEY);
    if np == 0 || nps == 0 || ns == 0 || nn == 0 || nr == 0 {
        proof { lemma_answer_empty(sv, v as int, pat@, rp@); }
        let out: Vec<Vec<EVal>> = Vec::new();
        proof { assert(view_rows(out@) =~= Seq::<Row>::empty()); }
        return Ok(Answer::Rows(out));
    }
    let cols = read_cols(stores, Ghost(sv));
    let nat_ok = nations_in_region(&cols, rp, Ghost(sv));
    let fast = is_suffix_pattern(pat);
    let suffix: &'static [u8] = if fast { let (_, s) = pat.split_at(1); s } else { pat };
    let p1 = match phase1(&cols, Ghost(sv), fast, suffix, v, Ghost(pat@), nat_ok, Ghost(rp@), workers, dispatch) {
        Ok(p) => p,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let Phase1 { qkeys: fast_keys, flags, dense, nflag } = p1;
    let qkeys = if fast {
        fast_keys
    } else {
        match general_part_keys(&cols, v, pat, Ghost(sv)) {
            Ok(ks) => ks,
            Err((a0, e)) => {
                proof { lemma_answer_err(sv, v as int, pat@, rp@, a0 as int, e); }
                return Ok(Answer::SqlError(e));
            },
        }
    };
    let est = expected_hits_per_mega(qkeys.len(), np, nflag, ns);
    let set = Arc::new(KeySet::new(qkeys));
    let flags = Arc::new(flags);
    let hits = match phase2(&cols, Ghost(sv), set, flags, dense, est, workers, dispatch) {
        Ok(h) => h,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_hits_ok(cols, sv, v as int, pat@, rp@, set, flags, dense, hits);
    }
    let rows = answer_rows(&cols, Ghost(sv), &hits, Ghost(v as int), Ghost(pat@), Ghost(rp@));
    proof {
        lemma_answer_rows(sv, v as int, pat@, rp@, view_rows(rows@));
    }
    Ok(Answer::Rows(rows))
}

} // verus!
