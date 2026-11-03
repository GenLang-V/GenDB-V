//! The database-level glue: for a bound database, the computed counts are the SQL meaning's.
//! - `lemma_ccnt`: c_count of customer row `i` (`ccnt`, the size of its LEFT JOIN match) is the number of orders rows
//!   with its key minus those whose comment matches (`cnt(kf == k) - cnt(like && kf == k)`);
//! - `lemma_dtotal`: the directory entry length of key `v` is the number of orders rows with key `v`;
//! - `canon_keys` (fallback without the facts key index): the key of every orders row from the index storage.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::*;
use crate::link::expr::ival;
use crate::stores::orders_custidx::interface as IX;
use super::sql::*;
use super::group::*;
use super::glue::*;
use super::bind::*;
use super::count::*;
use super::outer::*;
use super::phase2::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::limits::*;
use crate::exec::value::EVal;
use crate::link::query::{gcount, gkeys, full_row, view_rows, lemma_gkeys_witness, hit};
use crate::query::{param_typed, query_spec_at};

verus! {

/// The truth at `j` is `True`.
pub open spec fn tru(truths: Seq<Truth>) -> spec_fn(int) -> bool {
    |j: int| truths[j] is True
}

/// `keep_true` keeps the rows whose truth is `True`.
pub proof fn lemma_keep_true_len(rows: Seq<Row>, truths: Seq<Truth>)
    requires rows.len() == truths.len(),
    ensures keep_true(rows, truths).len() == cnt(tru(truths), 0, rows.len() as int),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (r0, t0) = (rows.drop_last(), truths.drop_last());
        lemma_keep_true_len(r0, t0);
        assert forall|j: int| 0 <= j < r0.len() implies #[trigger] tru(t0)(j) == tru(truths)(j) by {}
        lemma_cnt_ext(tru(t0), tru(truths), 0, r0.len() as int);
    }
}

/// The key of orders row `r`.
pub open spec fn okv(db: Database, r: int) -> int {
    ival(otab(db)[r][1])
}

/// The orders keys as a function.
pub open spec fn okvf(db: Database) -> spec_fn(int) -> int {
    |r: int| okv(db, r)
}

/// The orders row matches `$1` and has key `k`.
pub open spec fn pr_olk(db: Database, ps: Seq<Literal>, k: int) -> spec_fn(int) -> bool {
    |r: int| olike(otab(db)[r], ps) && okv(db, r) == k
}

/// c_count as a function of the customer row.
pub open spec fn ccntf(db: Database, ps: Seq<Literal>) -> spec_fn(int) -> int {
    |i: int| ccnt(db, ps, i) as int
}

/// c_count of customer row `i` in counts over the orders rows.
pub proof fn lemma_ccnt(db: Database, ps: Seq<Literal>, i: int)
    requires db_facts(db), 0 <= i < ctab(db).len(),
    ensures
        ccnt(db, ps, i) as int == vcount(okvf(db), ival(ctab(db)[i][0]), 0, otab(db).len() as int)
            - cnt(pr_olk(db, ps, ival(ctab(db)[i][0])), 0, otab(db).len() as int),
{
    let o = otab(db);
    let n = o.len() as int;
    let k = ival(ctab(db)[i][0]);
    let ts = lj_row_truths(db, ps, i);
    assert(lj_truths(db, ps)[i] == ts);
    lemma_keep_true_len(o, ts);
    let f = and_p(veq(okvf(db), k), |r: int| !olike(o[r], ps));
    assert forall|r: int| 0 <= r < n implies #[trigger] tru(ts)(r) == f(r) by {
        assert(ctab(db)[i][0] == Val::Int(k));
        assert(o[r][1] == Val::Int(okv(db, r)));
    }
    lemma_cnt_ext(tru(ts), f, 0, n);
    assert forall|r: int| 0 <= r < n implies #[trigger] veq(okvf(db), k)(r)
        == (f(r) || pr_olk(db, ps, k)(r)) && !(f(r) && pr_olk(db, ps, k)(r)) by {}
    lemma_cnt_or(f, pr_olk(db, ps, k), veq(okvf(db), k), 0, n);
}

/// Rows of `rel[0 .. m]` with key `Int(v)` are the rows with `okv == v`.
proof fn lemma_count_key_cnt(db: Database, v: int, m: int)
    requires
        db_facts(db),
        0 <= m <= otab(db).len(),
        idxrel(db).len() == otab(db).len(),
        forall|r: int| 0 <= r < otab(db).len() ==> #[trigger] idxrel(db)[r][0] == otab(db)[r][1],
    ensures IX::count_key(idxrel(db), v, m) == vcount(okvf(db), v, 0, m),
    decreases m,
{
    if m > 0 {
        lemma_count_key_cnt(db, v, m - 1);
        assert(idxrel(db)[m - 1][0] == otab(db)[m - 1][1]);
        assert(otab(db)[m - 1][1] == Val::Int(okv(db, m - 1)));
    }
}

/// The directory entry length of key `v` is the number of orders rows with key `v`.
pub proof fn lemma_dtotal(db: Database, p: Seq<crate::gendb_entry::layout::PartView>, v: int)
    requires
        db_facts(db),
        index_ok(p, db),
        IX::idx_i64s(p[IX::META as int])[0] == IX::MODE_DIRECTORY,
    ensures
        dtotal(IX::idx_u32s(p[IX::OFFS as int]), IX::idx_i64s(p[IX::META as int])[1] as int,
            IX::idx_u32s(p[IX::OFFS as int]).len() - 1, v) == vcount(okvf(db), v, 0, otab(db).len() as int),
{
    let offs = IX::idx_u32s(p[IX::OFFS as int]);
    let kmin = IX::idx_i64s(p[IX::META as int])[1] as int;
    let nk = offs.len() - 1;
    let n = otab(db).len() as int;
    lemma_count_key_cnt(db, v, n);
    if kmin <= v < kmin + nk {
        let e = v - kmin;
        assert(offs[e + 1] - offs[e] == IX::count_key(idxrel(db), kmin + e, n));
    } else {
        IX::lemma_directory_outside(kmin, nk, offs, IX::idx_u32s(p[IX::PERM as int]), idxrel(db), v);
    }
}

// ------------------------------------------------------------------------------------------------ errors

/// A GROUP BY over an erring input raises the same error.
proof fn lemma_groupby_err(db: Database, keys: Seq<Expr>, aggs: Seq<Agg>, input: Query, e: SqlError)
    requires eval_query(db, Seq::empty(), input) == Err::<Relation, SqlError>(e),
    ensures eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) }) == Err::<Relation, SqlError>(e),
{
}

/// The statement raises the inner GROUP BY's error.
pub proof fn lemma_body_err_inner(db: Database, ps: Seq<Literal>, e: SqlError)
    requires eval_query(db, Seq::empty(), inner_q(ps)) == Err::<Relation, SqlError>(e),
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(e),
{
    lemma_statement(ps);
    lemma_groupby_err(db, seq![Expr::Col(1)], seq![Agg::CountStar], inner_q(ps), e);
}

/// The statement raises the LEFT JOIN's error.
pub proof fn lemma_body_err_lj(db: Database, ps: Seq<Literal>, e: SqlError)
    requires eval_query(db, Seq::empty(), lj_q(ps)) == Err::<Relation, SqlError>(e),
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(e),
{
    lemma_groupby_err(db, seq![Expr::Col(0)], seq![Agg::Count(Expr::Col(8))], lj_q(ps), e);
    lemma_body_err_inner(db, ps, e);
}

// ------------------------------------------------------------------------------------------------ rows

/// `cnt_ccnt` is a count.
proof fn lemma_cnt_ccnt(db: Database, ps: Seq<Literal>, c: int, m: int)
    requires 0 <= m,
    ensures cnt_ccnt(db, ps, c, m) == vcount(ccntf(db, ps), c, 0, m),
    decreases m,
{
    if m > 0 {
        lemma_cnt_ccnt(db, ps, c, m - 1);
    }
}

/// The group count of `[c]` counts the customer rows with value `f == c` (`f` is c_count).
pub proof fn lemma_gcount_f(db: Database, ps: Seq<Literal>, f: spec_fn(int) -> int, c: int)
    requires forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] f(i) == ccnt(db, ps, i),
    ensures gcount(qspec(), inner_rows(db, ps), krow(c)) == vcount(f, c, 0, ctab(db).len() as int),
{
    let n = ctab(db).len() as int;
    lemma_gcount_ccnt(db, ps, c, n);
    assert(inner_rows(db, ps).take(n) =~= inner_rows(db, ps));
    lemma_cnt_ccnt(db, ps, c, n);
    assert forall|i: int| 0 <= i < n implies #[trigger] veq(ccntf(db, ps), c)(i) == veq(f, c)(i) by {}
    lemma_cnt_ext(veq(ccntf(db, ps), c), veq(f, c), 0, n);
}

/// A nonempty group of the outer GROUP BY is a pair.
proof fn lemma_group_pair(db: Database, ps: Seq<Literal>, f: spec_fn(int) -> int, pairs: Seq<(u64, u64)>, k: Row)
    -> (j: int)
    requires
        forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] f(i) == ccnt(db, ps, i),
        pairs_ok(pairs, f, ctab(db).len() as int),
        gcount(qspec(), inner_rows(db, ps), k) > 0,
    ensures
        0 <= j < pairs.len(),
        k == krow(pairs[j].0 as int),
        pairs[j].1 as int == gcount(qspec(), inner_rows(db, ps), k),
{
    let g = qspec();
    let irows = inner_rows(db, ps);
    let n = ctab(db).len() as int;
    crate::link::query::lemma_gkeys(g, irows);
    assert(gkeys(g, irows).contains(k));
    lemma_gkeys_witness(g, irows, k);
    let m = choose|m: int| 0 <= m < irows.len() && #[trigger] hit(g, irows[m], k);
    let c = ccnt(db, ps, m) as int;
    assert(k =~= krow(c));
    lemma_gcount_f(db, ps, f, c);
    assert(vcount(f, c, 0, n) > 0);
    let j = choose|j: int| 0 <= j < pairs.len() && pairs[j].0 as int == c;
    assert(pairs[j].1 as int == vcount(f, pairs[j].0 as int, 0, n));
    j
}

/// Every c_count and every outer group count is bounded by a pair.
proof fn lemma_rows_caps(db: Database, ps: Seq<Literal>, f: spec_fn(int) -> int, pairs: Seq<(u64, u64)>)
    requires
        forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] f(i) == ccnt(db, ps, i),
        pairs_ok(pairs, f, ctab(db).len() as int),
        forall|j: int| 0 <= j < pairs.len() ==> #[trigger] pairs[j].0 <= i64::MAX && pairs[j].1 <= i64::MAX,
    ensures
        forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] ccnt(db, ps, i) <= int8_max(),
        forall|k: Row| #[trigger] gcount(qspec(), inner_rows(db, ps), k) <= int8_max(),
{
    let n = ctab(db).len() as int;
    assert forall|i: int| 0 <= i < n implies #[trigger] ccnt(db, ps, i) <= int8_max() by {
        let c = f(i);
        lemma_vcount_at(f, c, 0, n, i);
        let j = choose|j: int| 0 <= j < pairs.len() && pairs[j].0 as int == c;
        assert(pairs[j].0 <= i64::MAX);
    }
    assert forall|k: Row| #[trigger] gcount(qspec(), inner_rows(db, ps), k) <= int8_max() by {
        if gcount(qspec(), inner_rows(db, ps), k) > 0 {
            let j = lemma_group_pair(db, ps, f, pairs, k);
            assert(pairs[j].1 <= i64::MAX);
        }
    }
}

/// The keys of the sorted pairs are exactly the nonempty groups.
proof fn lemma_rows_keys(db: Database, ps: Seq<Literal>, f: spec_fn(int) -> int, pairs: Seq<(u64, u64)>,
    sorted: Seq<(u64, u64)>, ks: Seq<Row>)
    requires
        forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] f(i) == ccnt(db, ps, i),
        pairs_ok(pairs, f, ctab(db).len() as int),
        forall|e: (u64, u64)| #[trigger] sorted.contains(e) <==> pairs.contains(e),
        ks == sorted.map_values(|e: (u64, u64)| krow(e.0 as int)),
    ensures
        forall|k: Row| #[trigger] ks.contains(k) <==> gcount(qspec(), inner_rows(db, ps), k) > 0,
{
    let g = qspec();
    let irows = inner_rows(db, ps);
    let n = ctab(db).len() as int;
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, irows, k) > 0 by {
        if ks.contains(k) {
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
            assert(sorted.contains(sorted[i]));
            let j = choose|j: int| 0 <= j < pairs.len() && pairs[j] == sorted[i];
            assert(pairs[j].1 as int == vcount(f, pairs[j].0 as int, 0, n) && pairs[j].1 > 0);
            lemma_gcount_f(db, ps, f, sorted[i].0 as int);
        }
        if gcount(g, irows, k) > 0 {
            let j = lemma_group_pair(db, ps, f, pairs, k);
            assert(pairs.contains(pairs[j]));
            assert(sorted.contains(pairs[j]));
            let i = choose|i: int| 0 <= i < sorted.len() && sorted[i] == pairs[j];
            assert(ks[i] == k);
        }
    }
}

/// The answer from the sorted pairs is an allowed output of the statement.
pub proof fn lemma_rows_ok(db: Database, ps: Seq<Literal>, f: spec_fn(int) -> int, pairs: Seq<(u64, u64)>,
    sorted: Seq<(u64, u64)>, rows: Seq<Vec<EVal>>)
    requires
        db_facts(db),
        param_typed(ps),
        !(ctab(db).len() > 0 && some_err(db, ps)),
        forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] f(i) == ccnt(db, ps, i),
        pairs_ok(pairs, f, ctab(db).len() as int),
        forall|j: int| 0 <= j < pairs.len() ==> #[trigger] pairs[j].0 <= i64::MAX && pairs[j].1 <= i64::MAX,
        sorted.len() == pairs.len(),
        forall|e: (u64, u64)| #[trigger] sorted.contains(e) <==> pairs.contains(e),
        forall|j1: int, j2: int| 0 <= j1 < sorted.len() && 0 <= j2 < sorted.len() && j1 != j2 ==>
            #[trigger] sorted[j1].0 != #[trigger] sorted[j2].0,
        forall|j1: int, j2: int| 0 <= j1 < j2 < sorted.len() ==> before(#[trigger] sorted[j1], #[trigger] sorted[j2]),
        view_rows(rows) == sorted.map_values(|e: (u64, u64)| prow(e)),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(rows))),
{
    let g = qspec();
    let irows = inner_rows(db, ps);
    lemma_rows_caps(db, ps, f, pairs);
    lemma_outer_ok(db, ps);
    let ks = sorted.map_values(|e: (u64, u64)| krow(e.0 as int));
    let full = sorted.map_values(|e: (u64, u64)| prow(e));
    assert(ks.no_duplicates()) by {
        assert forall|j1: int, j2: int| 0 <= j1 < ks.len() && 0 <= j2 < ks.len() && j1 != j2 implies ks[j1] != ks[j2] by {
            if ks[j1] == ks[j2] {
                assert(ks[j1][0] == ks[j2][0]);
            }
        }
    }
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i]).len() == 1 by {}
    lemma_rows_keys(db, ps, f, pairs, sorted, ks);
    assert forall|i: int| 0 <= i < full.len() implies #[trigger] full[i] == full_row(g, irows, ks[i]) by {
        let e = sorted[i];
        assert(sorted.contains(e));
        let j = choose|j: int| 0 <= j < pairs.len() && pairs[j] == e;
        assert(pairs[j].1 as int == vcount(f, pairs[j].0 as int, 0, ctab(db).len() as int));
        lemma_full_row(db, ps, e.0 as int);
        lemma_gcount_f(db, ps, f, e.0 as int);
    }
    assert(sorted_by(order_keys(), full)) by {
        assert forall|i: int, j: int| 0 <= i < j < full.len() implies keys_cmp(order_keys(), #[trigger] full[i], #[trigger] full[j]) <= 0 by {
            lemma_keys_cmp_rows(sorted[i], sorted[j]);
        }
    }
    lemma_answer(db, ps, ks, full);
}

/// Directory offsets are bounded by the last one.
proof fn lemma_offs_le(offs: Seq<u32>, k: int, e: int)
    requires 0 <= e <= k, offs.len() == k + 1, forall|e2: int| 0 <= e2 < k ==> #[trigger] offs[e2] <= offs[e2 + 1],
    ensures offs[e] <= offs[k],
    decreases k - e,
{
    if e < k {
        lemma_offs_le(offs, k, e + 1);
    }
}

// ------------------------------------------------------------------------------------------------ fallback keys

/// The key of every orders row from the index storage (the fallback when facts has no orders key index): directory
/// entry `e` gives its rows the key `kmin + e` (directory mode), or the per-row keys are copied (other modes).
pub fn canon_keys(dir: bool, kmin: i64, offs: &[u32], perm: &[u32], keys0: &[i64], n: usize, Ghost(rel): Ghost<Seq<Row>>)
    -> (keyc: Vec<i64>)
    requires
        rel.len() == n,
        forall|r: int| 0 <= r < n ==> (#[trigger] rel[r][0]) is Int && i64::MIN <= ival(rel[r][0]) <= i64::MAX,
        dir ==> offs@.len() >= 1 && IX::directory_ok(kmin as int, offs@.len() - 1, offs@, perm@, rel),
        !dir ==> keys0@.len() == n && forall|r: int| 0 <= r < n ==> #[trigger] rel[r][0] == Val::Int(keys0@[r] as int),
    ensures
        keyc@.len() == n,
        forall|r: int| 0 <= r < n ==> #[trigger] rel[r][0] == Val::Int(keyc@[r] as int),
{
    if !dir {
        let mut keyc: Vec<i64> = Vec::new();
        let mut r: usize = 0;
        while r < n
            invariant
                r <= n,
                keys0@.len() == n,
                keyc@ == keys0@.subrange(0, r as int),
            decreases n - r,
        {
            keyc.push(keys0[r]);
            proof { assert(keyc@ =~= keys0@.subrange(0, r + 1)); }
            r = r + 1;
        }
        proof { assert(keyc@ =~= keys0@); }
        return keyc;
    }
    let k = offs.len() - 1;
    let mut keyc: Vec<i64> = vec![0i64; n];
    let mut e: usize = 0;
    while e < k
        invariant
            dir,
            rel.len() == n,
            forall|r: int| 0 <= r < n ==> (#[trigger] rel[r][0]) is Int && i64::MIN <= ival(rel[r][0]) <= i64::MAX,
            offs@.len() == k + 1,
            IX::directory_ok(kmin as int, k as int, offs@, perm@, rel),
            e <= k,
            keyc@.len() == n,
            forall|j: int| 0 <= j < offs@[e as int] ==> #[trigger] perm@[j] < n && keyc@[perm@[j] as int] == ival(rel[perm@[j] as int][0]),
        decreases k - e,
    {
        let lo = offs[e] as usize;
        let hi = offs[e + 1] as usize;
        assert(offs@[e as int] <= offs@[e + 1]);
        proof { lemma_offs_le(offs@, k as int, e + 1); }
        assert forall|j2: int| lo <= j2 < hi implies #[trigger] perm@[j2] < n && rel[perm@[j2] as int][0] == Val::Int(kmin + e) by {
            assert(IX::in_entry(offs@, e as int, j2));
        }
        let mut j = lo;
        while j < hi
            invariant
                rel.len() == n,
                forall|r: int| 0 <= r < n ==> (#[trigger] rel[r][0]) is Int && i64::MIN <= ival(rel[r][0]) <= i64::MAX,
                forall|j2: int| lo <= j2 < hi ==> #[trigger] perm@[j2] < n && rel[perm@[j2] as int][0] == Val::Int(kmin + e),
                e < k,
                lo <= j <= hi, hi <= perm@.len(),
                keyc@.len() == n,
                forall|j2: int| 0 <= j2 < j ==> #[trigger] perm@[j2] < n && keyc@[perm@[j2] as int] == ival(rel[perm@[j2] as int][0]),
            decreases hi - j,
        {
            let r = perm[j] as usize;
            assert(rel[r as int][0] == Val::Int(kmin + e));
            let key: i64 = ((kmin as i128) + (e as i128)) as i64;
            let ghost old = keyc@;
            keyc.set(r, key);
            proof {
                assert(keyc@[r as int] == ival(rel[r as int][0]));
                assert forall|j2: int| 0 <= j2 < j + 1 implies #[trigger] perm@[j2] < n && keyc@[perm@[j2] as int] == ival(rel[perm@[j2] as int][0]) by {
                    if j2 < j && perm@[j2] as int != r as int {
                        assert(keyc@[perm@[j2] as int] == old[perm@[j2] as int]);
                    }
                }
            }
            j = j + 1;
        }
        assert(offs@[e + 1] == hi);
        e = e + 1;
    }
    proof {
        assert forall|r: int| 0 <= r < n implies #[trigger] rel[r][0] == Val::Int(keyc@[r] as int) by {
            assert(IX::listed(perm@, r));
            let j = choose|j: int| 0 <= j < perm@.len() && perm@[j] == r;
            assert(offs@[k as int] == n);
        }
    }
    keyc
}

} // verus!
