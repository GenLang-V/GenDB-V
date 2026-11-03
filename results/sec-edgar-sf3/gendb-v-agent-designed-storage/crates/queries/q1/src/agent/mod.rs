//! Q0 over storage `pre`: per (stmt, rfile) group with non-NULL stmt, COUNT(*), COUNT(DISTINCT adsh) and
//! AVG(line), ordered by COUNT(*) descending.
//!
//! Plan. `pre` is stored as sub-runs of equal (adsh, (stmt, rfile) group) with a group dictionary, so a group's
//! COUNT(*) is the total length of its sub-runs, its COUNT(DISTINCT adsh) the number of its sub-runs (each
//! (adsh, group) pair is one sub-run) and only `line` is read per row. Chunks of sub-runs are accumulated in
//! parallel (`kernel`), merged exactly, and one row per selected group code is built and sorted (`output`).
//!
//! Proof. `canon` states the SQL meaning in the link toolkit's normal form over the canonical rows, `store` relates
//! the stored sub-runs to it, `values`/`answer` give the GROUP BY result per group, and `failure` the outcome when a
//! count leaves int8 or an AVG division leaves the executable domain (the first such group in canonical
//! first-occurrence order decides between SQL error 22003 and Capacity).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok, capacity_domain};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec, query_spec_at};
use crate::exec::value::EVal;
use crate::exec::ast::EOrderKey;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::bridge::order::{lemma_sort_rows, all_keys_ok, keys_ok, key_ok};
use crate::link::query::{view_rows, hit, lemma_slice_all};
use crate::link::outcome::{lemma_outcome_sorted, lemma_outcome_err};
use crate::stores::pre::interface::*;
use crate::stores::pre::interface::common::cols::u64s;
use crate::stores::pre::declaration::stored_relations;

pub mod common;
pub mod runs;
pub mod canon;
pub mod store;
pub mod values;
pub mod answer;
pub mod failure;
pub mod kernel;
pub mod output;

use canon::*;
use store::*;
use answer::*;
use failure::*;
use kernel::*;
use output::*;

verus! {

/// A database bound to the stores is bound to the parts of `pre`.
proof fn lemma_bound(sv: crate::gendb_entry::stores::StoresView, db: Database)
    requires bound_db(sv, db),
    ensures bound(sv.pre, db),
{
}

/// The sorted rows of the selected codes are an allowed output.
proof fn lemma_rows_ok(p: Seq<PartView>, db: Database, codes: Seq<int>, v: Seq<Row>, out: Seq<Row>)
    requires
        bound(p, db),
        forall|g: int| #[trigger] selected(p, g) ==> code_ok(p, g),
        forall|i: int| 0 <= i < codes.len() ==> selected(p, #[trigger] codes[i]),
        forall|i: int, j: int| 0 <= i < j < codes.len() ==> #[trigger] codes[i] < #[trigger] codes[j],
        forall|g: int| #[trigger] selected(p, g) ==> codes.contains(g),
        v == codes.map_values(|g: int| prow(p, g)),
        out == sort_rows(q_order(), v),
    ensures ordered_ok(db, query_spec(), Ok::<Relation, SqlError>(out)),
{
    lemma_statement();
    lemma_success(p, db, codes);
    let body = denote_body(db, query_spec())->Ok_0;
    let fams = seq![1int];
    assert(all_keys_ok(q_order(), fams, v)) by {
        assert forall|i: int| 0 <= i < v.len() implies keys_ok(q_order(), fams, #[trigger] v[i]) by {
            assert(v[i] == prow(p, codes[i]));
            assert(v[i][2] == Val::Int(rr(p, codes[i])));
            assert(key_ok(q_order()[0], fams[0], v[i]));
        }
    }
    lemma_sort_rows(q_order(), fams, v);
    lemma_outcome_sorted(db, query_spec(), body, out);
    lemma_slice_all(out);
}

/// The failure path's choice: `gs` fails, `f` is its first canonical row, and every other failing code starts later.
proof fn lemma_failure_ok(p: Seq<PartView>, db: Database, gs: int, f: int, fos: Seq<int>, fail: Seq<bool>)
    requires
        bound(p, db),
        fail.len() == group_count(p), fos.len() == group_count(p),
        forall|g: int| 0 <= g < group_count(p) && #[trigger] fail[g] ==> selected(p, g) && !code_ok(p, g),
        forall|g: int| #[trigger] selected(p, g) && !code_ok(p, g) ==> fail[g],
        0 <= gs < group_count(p), fail[gs], first_at(p, gs, f),
        forall|c: int| 0 <= c < group_count(p) && #[trigger] fail[c] ==> first_at(p, c, fos[c]) && f <= fos[c],
    ensures
        count_err(p, gs) ==> ordered_ok(db, query_spec(), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
        !count_err(p, gs) ==> !capacity_domain(db, query_spec()),
{
    let xs = xs_of(db);
    lemma_first_row(p, db, gs, f);
    assert forall|c: int, j: int| #![trigger hit(gq(), xs_of(db)[j], key_of(p, c))]
        selected(p, c) && !code_ok(p, c) && c != gs && 0 <= j <= f implies !hit(gq(), xs_of(db)[j], key_of(p, c)) by {
        assert(fail[c]);
        let fc = fos[c];
        lemma_first_row(p, db, c, fc);
        if fc == f {
            assert((gq().key)(xs[f]) == key_of(p, c));
            assert((gq().key)(xs[f]) == key_of(p, gs));
            lemma_key_injective(p, c, gs);
        }
    }
    lemma_failure(p, db, gs, f);
    if count_err(p, gs) {
        lemma_outcome_err(db, query_spec(), SqlError::NumericValueOutOfRange);
    }
}

/// `r` is an allowed outcome for every database bound to the parts of `pre`.
pub open spec fn answers(p: Seq<PartView>, r: Result<Answer, QueryError>) -> bool {
    forall|db: Database| #[trigger] bound(p, db) ==> outcome_ok(db, query_spec(), r)
}

/// Every selected code's aggregates are values: sort the rows of the selected codes by COUNT(*) descending.
fn success_answer(rows: Vec<Vec<EVal>>, Ghost(p): Ghost<Seq<PartView>>, Ghost(codes): Ghost<Seq<int>>) -> (r: Result<Answer, QueryError>)
    requires
        forall|g: int| #[trigger] selected(p, g) ==> code_ok(p, g) && codes.contains(g),
        forall|i: int| 0 <= i < codes.len() ==> #[trigger] selected(p, codes[i]),
        forall|i: int, j: int| 0 <= i < j < codes.len() ==> #[trigger] codes[i] < #[trigger] codes[j],
        view_rows(rows@) == codes.map_values(|g: int| prow(p, g)),
    ensures answers(p, r),
{
    let mut keys: Vec<EOrderKey> = Vec::new();
    keys.push(EOrderKey { col: 2, desc: true, nulls_first: true });
    let out = sort_rows_exec(&keys, rows);
    proof {
        assert(view_keys(keys@) =~= q_order());
        assert forall|db: Database| #[trigger] bound(p, db) implies
            outcome_ok(db, query_spec(), Ok::<Answer, QueryError>(Answer::Rows(out))) by {
            lemma_rows_ok(p, db, codes, view_rows(rows@), view_rows(out@));
        }
    }
    Ok(Answer::Rows(out))
}

/// Some selected code fails: the failing code whose first canonical row comes first decides.
fn failure_answer(st: &mut StoredParts, start: &'static [u64], sub_group: &'static [u64], fail: &Vec<bool>,
    cnt: &Vec<u64>, nf: &Vec<u64>, n: usize, ns: usize, ng: usize, Ghost(w): Ghost<int>) -> (r: Result<Answer, QueryError>)
    requires
        pre_layout_ok(old(st)@),
        n == row_count(old(st)@), ns == sub_count(old(st)@), ng == group_count(old(st)@),
        start@ == st_of(old(st)@), sub_group@ == sg_of(old(st)@),
        fail@.len() == ng,
        forall|g: int| 0 <= g < ng && #[trigger] fail@[g] ==> selected(old(st)@, g) && !code_ok(old(st)@, g),
        forall|g: int| #[trigger] selected(old(st)@, g) && !code_ok(old(st)@, g) ==> fail@[g],
        0 <= w < ng, fail@[w],
        cnt@.len() == ng, nf@.len() == ng,
        forall|g: int| 0 <= g < ng && #[trigger] live_of(old(st)@, g) ==> cnt@[g] as int == rr(old(st)@, g) && nf@[g] as int == rc(old(st)@, g),
    ensures final(st)@ == old(st)@, answers(old(st)@, r),
{
    let ghost p = st@;
    proof { lemma_layout_facts(p); }
    let orig = st.extent_u64(P_ORIG, 0, n);
    proof { assert(orig@ =~= u64s(p, P_ORIG)); }
    let mut best: usize = ng;
    let mut best_f: u64 = 0;
    let ghost mut fos: Seq<int> = Seq::new(ng as nat, |g: int| 0int);
    let mut g: usize = 0;
    while g < ng
        invariant
            g <= ng, ng == group_count(p), pre_layout_ok(p), ns == sub_count(p), n == row_count(p), st@ == p,
            orig@ == u64s(p, P_ORIG), start@ == st_of(p), sub_group@ == sg_of(p),
            fail@.len() == ng, fos.len() == ng, 0 <= w < ng, fail@[w],
            forall|h: int| 0 <= h < ng && #[trigger] fail@[h] ==> selected(p, h) && !code_ok(p, h),
            best <= ng,
            best < ng ==> best < g && fail@[best as int] && first_at(p, best as int, best_f as int),
            best == ng ==> forall|c: int| 0 <= c < g ==> !#[trigger] fail@[c],
            forall|c: int| 0 <= c < g && #[trigger] fail@[c] ==> first_at(p, c, fos[c]) && best_f <= fos[c],
        decreases ng - g,
    {
        if fail[g] {
            proof {
                assert(selected(p, g as int));
                runs::lemma_rows_pos(st_of(p), sg_of(p), g as int, 0, sub_count(p));
            }
            let f = first_of(orig, start, sub_group, ns, n, g, Ghost(p));
            proof { fos = fos.update(g as int, f as int); }
            if best == ng || f < best_f {
                best = g;
                best_f = f;
            }
        }
        g = g + 1;
    }
    proof {
        assert(g == ng);
        assert(fail@[w]);
        assert(best == ng ==> !fail@[w]);
        assert(best < ng);
    }
    let gs = best;
    let count_overflow = cnt[gs] > 0x7fff_ffff_ffff_ffff || nf[gs] > 0x7fff_ffff_ffff_ffff;
    proof {
        assert(live_of(p, gs as int));
        assert(count_overflow == count_err(p, gs as int));
        assert forall|db: Database| #[trigger] bound(p, db) implies {
            &&& count_err(p, gs as int) ==> ordered_ok(db, query_spec(), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange))
            &&& !count_err(p, gs as int) ==> !capacity_domain(db, query_spec())
        } by {
            lemma_failure_ok(p, db, gs as int, best_f as int, fos, fail@);
        }
    }
    if count_overflow {
        Ok(Answer::SqlError(SqlError::NumericValueOutOfRange))
    } else {
        Ok(Answer::Capacity)
    }
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost p = stores.pre@;
    proof {
        let db0 = choose|db: Database| #[trigger] bound_db(sv, db);
        lemma_bound(sv, db0);
        lemma_layout_facts(p);
    }
    let st = &mut stores.pre;
    let n = st.part_len(P_ORIG);
    let ns1 = st.part_len(P_SUB_START);
    let ns = ns1 - 1;
    let ng = st.part_len(P_GROUP_STMT);
    let start = st.extent_u64(P_SUB_START, 0, ns1);
    let sub_group = st.extent_u64(P_SUB_GROUP, 0, ns);
    let group_stmt = st.extent_u64(P_GROUP_STMT, 0, ng);
    let group_rfile = st.extent_u64(P_GROUP_RFILE, 0, ng);
    let line = st.extent_i32(P_LINE, 0, n);
    proof {
        assert(start@ =~= st_of(p));
        assert(sub_group@ =~= sg_of(p));
        assert(group_stmt@ =~= u64s(p, P_GROUP_STMT));
        assert(group_rfile@ =~= u64s(p, P_GROUP_RFILE));
        assert(line@ =~= ln_of(p));
    }
    let acc = accumulate(start, sub_group, line, group_stmt, ns, ng, n, workers, dispatch);
    let (cnt, nf, sum) = match acc {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let live = live_flags(group_stmt, ng);
    proof {
        assert forall|g: int| 0 <= g < group_count(p) && #[trigger] live_of(p, g) implies {
            &&& cnt@[g] as int == rr(p, g)
            &&& nf@[g] as int == rc(p, g)
            &&& sum@[g] as int == rv(p, g)
        } by {
            assert(Seq::new(ng as nat, |h: int| group_stmt@[h] != 0)[g]);
        }
        assert(accs_ok(p, live@, cnt@, nf@, sum@));
    }
    let (rows, fail, any, Ghost(codes)) = build_rows(st, group_stmt, group_rfile, &live, &cnt, &nf, &sum, ng);
    proof {
        assert forall|g: int| #[trigger] selected(p, g) && !code_ok(p, g) implies fail@[g] by {
            if !fail@[g] {
                let i = choose|i: int| 0 <= i < codes.len() && codes[i] == g;
                assert(code_ok(p, codes[i]));
            }
        }
    }
    let r = if !any {
        proof {
            assert forall|g: int| #[trigger] selected(p, g) implies code_ok(p, g) && codes.contains(g) by {
                if !code_ok(p, g) { assert(fail@[g]); }
                if !codes.contains(g) { assert(fail@[g]); }
            }
        }
        success_answer(rows, Ghost(p), Ghost(codes))
    } else {
        let ghost w = choose|c: int| 0 <= c < group_count(p) && #[trigger] fail@[c];
        failure_answer(st, start, sub_group, &fail, &cnt, &nf, n, ns, ng, Ghost(w))
    };
    proof {
        assert(query_spec_at(params@) == query_spec());
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), r) by {
            lemma_bound(sv, db);
        }
    }
    r
}

} // verus!
