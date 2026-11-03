//! The normal form of both query blocks (`link::query::QuerySpec` over the FROM relation): the grouped outer block
//! `gq` (key `ps_partkey`) and the scalar subquery block `sq`, and the reduction of their accumulators over the
//! three-table product to sums over the stored partsupp rows (`rsum`).
//!
//! Reduction: a FROM row contributes only when its supplier row has its `ps_suppkey` and its nation row has the
//! supplier's `s_nationkey`; supplier and nation keys are duplicate-free (primary keys), so each partsupp row meets
//! at most one supplier and nation row (`common::sum_pick`). The sum over the product of a term that depends on the
//! partsupp part (`lift`) is the sum over partsupp rows of that term where the row qualifies (`down`,
//! `lemma_reduce`), which is `rsum` over the stored arrays (`lemma_rows_rsum`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::relation::product_rows;
use crate::link::expr::ival;
use crate::link::query::{QuerySpec, AggKind, hit, gcount, gsum, gabs};
use crate::link::join::{sum_of, sum_term, count_term, abs_term, lemma_acc_sum_of, lemma_sum_of_ext};
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem::*;
use crate::agent::common::sum_pick::*;

verus! {

// ------------------------------------------------------------------------------------------ the normal forms

/// The grouped outer block: `WHERE` as `qualx`, key `(ps_partkey)`, `SUM(ps_supplycost * ps_availqty)` at scale 2,
/// output `(ps_partkey, value)`.
pub open spec fn gq(p: Seq<u8>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| qualx(p, x),
        key: |x: Row| seq![x[0]],
        arg: |j: int, x: Row| ival(x[3]) * ival(x[2]),
        aggs: seq![AggKind::Sum { scale: 2 }],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

/// The scalar subquery block: the same `WHERE` and argument, one group (empty key).
pub open spec fn sq(p: Seq<u8>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| qualx(p, x),
        key: |x: Row| Seq::<Val>::empty(),
        arg: |j: int, x: Row| ival(x[3]) * ival(x[2]),
        aggs: seq![AggKind::Sum { scale: 2 }],
        outs: seq![0nat],
        grouped: false,
    }
}

/// The group key row of part key `k`.
pub open spec fn kr(k: int) -> Row {
    seq![Val::Int(k)]
}

// ------------------------------------------------------------------------------------------ sums over the stored rows

/// `t(c)` summed over the qualifying partsupp rows `c` of `[lo, hi)`.
pub open spec fn rsum(sv: StoresView, p: Seq<u8>, t: spec_fn(int) -> int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { rsum(sv, p, t, lo, hi - 1) + if qrow(sv, p, hi - 1) { t(hi - 1) } else { 0 } }
}

/// Terms: the value of a row of part key `k`, 1 for it, its absolute value; the value of every row, its absolute
/// value, 1.
pub open spec fn t_sum(sv: StoresView, k: int) -> spec_fn(int) -> int {
    |c: int| if ps_pkeys(sv)[c] == k { val(sv, c) } else { 0 }
}

pub open spec fn t_cnt(sv: StoresView, k: int) -> spec_fn(int) -> int {
    |c: int| if ps_pkeys(sv)[c] == k { 1int } else { 0int }
}

pub open spec fn t_abs(sv: StoresView, k: int) -> spec_fn(int) -> int {
    |c: int| if ps_pkeys(sv)[c] == k { abs(val(sv, c)) } else { 0 }
}

pub open spec fn t_val(sv: StoresView) -> spec_fn(int) -> int {
    |c: int| val(sv, c)
}

pub open spec fn t_absv(sv: StoresView) -> spec_fn(int) -> int {
    |c: int| abs(val(sv, c))
}

pub open spec fn t_one() -> spec_fn(int) -> int {
    |c: int| 1int
}

// ------------------------------------------------------------------------------------------ product reduction

/// A term of the FROM row through its partsupp part, where the row satisfies the WHERE condition.
pub open spec fn lift(p: Seq<u8>, t: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if qualx(p, x) { t(x.subrange(0, 5)) } else { 0 }
}

/// A partsupp row `w` meets a supplier row with its supplier key whose nation row is named `p`.
pub open spec fn ps_ok(s: Seq<Row>, n: Seq<Row>, p: Seq<u8>, w: Row) -> bool {
    &&& has_pick(s, 0, w[1])
    &&& has_pick(n, 0, s[pick(s, 0, w[1])][3])
    &&& n[pick(n, 0, s[pick(s, 0, w[1])][3])][1] == Val::Text(p)
}

/// The term of a qualifying partsupp row.
pub open spec fn down(s: Seq<Row>, n: Seq<Row>, p: Seq<u8>, t: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |w: Row| if ps_ok(s, n, p, w) { t(w) } else { 0 }
}

/// The sum over the three-table product of a lifted term is the sum over the first table of the term where the
/// row qualifies (the second and third tables joined on duplicate-free keys).
pub proof fn lemma_reduce(a: Seq<Row>, b: Seq<Row>, c: Seq<Row>, p: Seq<u8>, t: spec_fn(Row) -> int)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == 5,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]).len() == 7,
        forall|i: int| 0 <= i < c.len() ==> (#[trigger] c[i]).len() == 4,
        col_unique(b, 0),
        col_unique(c, 0),
    ensures sum_of(product_rows(product_rows(a, b), c), lift(p, t)) == sum_of(a, down(b, c, p, t)),
{
    let ab = product_rows(a, b);
    let f = lift(p, t);
    lemma_product_widths(a, b, 5, 7);
    // nation joined on s_nationkey (position 8 of the partsupp ++ supplier row)
    assert forall|i: int, j: int| 0 <= i < ab.len() && 0 <= j < c.len() && f(#[trigger] ab[i] + #[trigger] c[j]) != 0
        implies c[j][0] == ab[i][8] by {
        let x = ab[i] + c[j];
        assert(x[8] == ab[i][8] && x[12] == c[j][0]);
    }
    lemma_sum_product_right(ab, c, f, 8, 0);
    let f1 = |z: Row| at_pick(c, 0, z[8], |y: Row| f(z + y));
    // supplier joined on ps_suppkey (position 1 of the partsupp row)
    assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && f1(#[trigger] a[i] + #[trigger] b[j]) != 0
        implies b[j][0] == a[i][1] by {
        let z = a[i] + b[j];
        let h = |y: Row| f(z + y);
        lemma_at_pick_nonzero(c, 0, z[8], h);
        let q = pick(c, 0, z[8]);
        let x = z + c[q];
        assert(f(x) != 0);
        assert(x[1] == a[i][1] && x[5] == b[j][0]);
    }
    lemma_sum_product_right(a, b, f1, 1, 0);
    let f2 = |w: Row| at_pick(b, 0, w[1], |u: Row| f1(w + u));
    let g = down(b, c, p, t);
    assert forall|i: int| 0 <= i < a.len() implies f2(#[trigger] a[i]) == g(a[i]) by {
        let w = a[i];
        lemma_pick(b, 0, w[1]);
        if has_pick(b, 0, w[1]) {
            let pb = pick(b, 0, w[1]);
            let z = w + b[pb];
            assert(z[8] == b[pb][3]);
            lemma_pick(c, 0, z[8]);
            if has_pick(c, 0, z[8]) {
                let pc = pick(c, 0, z[8]);
                let x = z + c[pc];
                assert(x[1] == w[1] && x[5] == b[pb][0] && x[8] == b[pb][3] && x[12] == c[pc][0] && x[13] == c[pc][1]);
                assert(x.subrange(0, 5) =~= w);
                assert(f1(z) == f(x));
            } else {
                assert(f1(z) == 0);
            }
            assert(f2(w) == f1(z));
        }
    }
    lemma_sum_of_ext(a, f2, g);
}

// ------------------------------------------------------------------------------------------ to the stored arrays

/// Supplier and nation rows are duplicate-free in their key column.
pub proof fn lemma_cols_unique(sv: StoresView)
    requires stores_wf(sv), keys_ok(sv),
    ensures col_unique(supp_rows(sv), 0), col_unique(nat_rows(sv), 0),
{
    let s = supp_rows(sv);
    let n = nat_rows(sv);
    assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && #[trigger] s[i][0] == #[trigger] s[j][0] implies i == j by {
        assert(s[i][0] == Val::Int(s_keys(sv)[i] as int));
        assert(s[j][0] == Val::Int(s_keys(sv)[j] as int));
    }
    assert forall|i: int, j: int| 0 <= i < n.len() && 0 <= j < n.len() && #[trigger] n[i][0] == #[trigger] n[j][0] implies i == j by {
        assert(n[i][0] == Val::Int(n_keys(sv)[i] as int));
        assert(n[j][0] == Val::Int(n_keys(sv)[j] as int));
    }
}

/// The row widths of the three stored tables.
pub proof fn lemma_widths(sv: StoresView)
    ensures
        forall|i: int| 0 <= i < ps_rows(sv).len() ==> (#[trigger] ps_rows(sv)[i]).len() == 5,
        forall|i: int| 0 <= i < supp_rows(sv).len() ==> (#[trigger] supp_rows(sv)[i]).len() == 7,
        forall|i: int| 0 <= i < nat_rows(sv).len() ==> (#[trigger] nat_rows(sv)[i]).len() == 4,
{
}

/// A partsupp row qualifies (`ps_ok` over the stored rows) exactly when `qrow` holds.
pub proof fn lemma_ps_ok(sv: StoresView, p: Seq<u8>, c: int)
    requires stores_wf(sv), keys_ok(sv), 0 <= c < ps_n(sv),
    ensures ps_ok(supp_rows(sv), nat_rows(sv), p, ps_rows(sv)[c]) == qrow(sv, p, c),
{
    let s = supp_rows(sv);
    let n = nat_rows(sv);
    let w = ps_rows(sv)[c];
    let sk = ps_skeys(sv)[c] as int;
    lemma_cols_unique(sv);
    assert(w[1] == Val::Int(sk));
    lemma_pick(s, 0, w[1]);
    if ps_ok(s, n, p, w) {
        let b = pick(s, 0, w[1]);
        assert(s[b][0] == Val::Int(s_keys(sv)[b] as int));
        assert(s[b][3] == Val::Int(s_nks(sv)[b] as int));
        lemma_pick(n, 0, s[b][3]);
        let d = pick(n, 0, s[b][3]);
        assert(n[d][0] == Val::Int(n_keys(sv)[d] as int));
        assert(n[d][1] == Val::Text(n_name(sv, d)));
        assert(nat_ok(sv, p, d));
        assert(supp_ok(sv, p, b));
        assert(key_ok(sv, p, sk));
    }
    if qrow(sv, p, c) {
        let b = choose|b: int| 0 <= b < supp_n(sv) && #[trigger] s_keys(sv)[b] == sk && supp_ok(sv, p, b);
        let d = choose|d: int| 0 <= d < nat_n(sv) && #[trigger] n_keys(sv)[d] == s_nks(sv)[b] && nat_ok(sv, p, d);
        assert(s[b][0] == Val::Int(s_keys(sv)[b] as int));
        assert(has_pick(s, 0, w[1]));
        assert(pick(s, 0, w[1]) == b);
        assert(s[b][3] == Val::Int(s_nks(sv)[b] as int));
        assert(n[d][0] == Val::Int(n_keys(sv)[d] as int));
        lemma_pick(n, 0, s[b][3]);
        assert(has_pick(n, 0, s[b][3]));
        assert(pick(n, 0, s[b][3]) == d);
        assert(n[d][1] == Val::Text(n_name(sv, d)));
    }
}

/// A row-level term that agrees with an index-level term on the rows of `[lo, hi)`: the sum of `down` over those
/// rows is `rsum`.
pub proof fn lemma_rows_rsum(sv: StoresView, p: Seq<u8>, tr: spec_fn(Row) -> int, ti: spec_fn(int) -> int, lo: int, hi: int)
    requires
        stores_wf(sv), keys_ok(sv), 0 <= lo <= hi <= ps_n(sv),
        forall|c: int| lo <= c < hi ==> tr(#[trigger] ps_rows(sv)[c]) == ti(c),
    ensures sum_of(ps_rows(sv).subrange(lo, hi), down(supp_rows(sv), nat_rows(sv), p, tr)) == rsum(sv, p, ti, lo, hi),
    decreases hi - lo,
{
    let rows = ps_rows(sv).subrange(lo, hi);
    let g = down(supp_rows(sv), nat_rows(sv), p, tr);
    if hi > lo {
        lemma_rows_rsum(sv, p, tr, ti, lo, hi - 1);
        assert(rows.drop_last() =~= ps_rows(sv).subrange(lo, hi - 1));
        assert(rows.last() == ps_rows(sv)[hi - 1]);
        lemma_ps_ok(sv, p, hi - 1);
    } else {
        assert(rows.len() == 0);
    }
}

// ------------------------------------------------------------------------------------------ the accumulators

/// On every FROM row, the normal forms' terms are lifted partsupp terms.
proof fn lemma_terms_lift(sv: StoresView, p: Seq<u8>, k: int)
    requires stores_wf(sv),
    ensures
        forall|m: int| 0 <= m < from_rows(sv).len() ==>
            (sum_term(gq(p), kr(k), 0))(#[trigger] from_rows(sv)[m])
                == (lift(p, |w: Row| if w[0] == Val::Int(k) { ival(w[3]) * ival(w[2]) } else { 0 }))(from_rows(sv)[m]),
        forall|m: int| 0 <= m < from_rows(sv).len() ==>
            (count_term(gq(p), kr(k)))(#[trigger] from_rows(sv)[m])
                == (lift(p, |w: Row| if w[0] == Val::Int(k) { 1int } else { 0int }))(from_rows(sv)[m]),
        forall|m: int| 0 <= m < from_rows(sv).len() ==>
            (abs_term(gq(p), kr(k), 0))(#[trigger] from_rows(sv)[m])
                == (lift(p, |w: Row| if w[0] == Val::Int(k) { abs(ival(w[3]) * ival(w[2])) } else { 0 }))(from_rows(sv)[m]),
        forall|m: int| 0 <= m < from_rows(sv).len() ==>
            (sum_term(sq(p), Seq::<Val>::empty(), 0))(#[trigger] from_rows(sv)[m])
                == (lift(p, |w: Row| ival(w[3]) * ival(w[2])))(from_rows(sv)[m]),
        forall|m: int| 0 <= m < from_rows(sv).len() ==>
            (count_term(sq(p), Seq::<Val>::empty()))(#[trigger] from_rows(sv)[m])
                == (lift(p, |w: Row| 1int))(from_rows(sv)[m]),
        forall|m: int| 0 <= m < from_rows(sv).len() ==>
            (abs_term(sq(p), Seq::<Val>::empty(), 0))(#[trigger] from_rows(sv)[m])
                == (lift(p, |w: Row| abs(ival(w[3]) * ival(w[2]))))(from_rows(sv)[m]),
{
    assert forall|m: int| 0 <= m < from_rows(sv).len() implies {
        let x = #[trigger] from_rows(sv)[m];
        &&& x.len() == 16
        &&& x.subrange(0, 5)[0] == x[0] && x.subrange(0, 5)[2] == x[2] && x.subrange(0, 5)[3] == x[3]
        &&& (seq![x[0]] == kr(k)) == (x[0] == Val::Int(k))
    } by {
        let (a, b, d) = lemma_from_elem(sv, m);
        lemma_row3(sv, a, b, d);
        let x = from_rows(sv)[m];
        if x[0] == Val::Int(k) {
            assert(seq![x[0]] =~= kr(k));
        }
        if seq![x[0]] == kr(k) {
            assert(seq![x[0]][0] == kr(k)[0]);
        }
    }
}

/// The accumulators of the grouped block at key `kr(k)` are the stored-row sums.
pub proof fn lemma_grouped_acc(sv: StoresView, p: Seq<u8>, k: int)
    requires stores_wf(sv), keys_ok(sv),
    ensures
        gsum(gq(p), from_rows(sv), kr(k), 0) == rsum(sv, p, t_sum(sv, k), 0, ps_n(sv) as int),
        gcount(gq(p), from_rows(sv), kr(k)) == rsum(sv, p, t_cnt(sv, k), 0, ps_n(sv) as int),
        gabs(gq(p), from_rows(sv), kr(k), 0) == rsum(sv, p, t_abs(sv, k), 0, ps_n(sv) as int),
{
    let (ps, ss, ns) = (ps_rows(sv), supp_rows(sv), nat_rows(sv));
    let r = from_rows(sv);
    let n = ps_n(sv) as int;
    lemma_widths(sv);
    lemma_cols_unique(sv);
    lemma_terms_lift(sv, p, k);
    lemma_acc_sum_of(gq(p), r, kr(k), 0);
    assert(ps.subrange(0, n) =~= ps);
    // SUM
    let tr = |w: Row| if w[0] == Val::Int(k) { ival(w[3]) * ival(w[2]) } else { 0 };
    lemma_sum_of_ext(r, sum_term(gq(p), kr(k), 0), lift(p, tr));
    lemma_reduce(ps, ss, ns, p, tr);
    assert forall|c: int| 0 <= c < n implies tr(#[trigger] ps_rows(sv)[c]) == (t_sum(sv, k))(c) by {
        assert(ps[c][0] == Val::Int(ps_pkeys(sv)[c] as int));
    }
    lemma_rows_rsum(sv, p, tr, t_sum(sv, k), 0, n);
    // COUNT
    let trc = |w: Row| if w[0] == Val::Int(k) { 1int } else { 0int };
    lemma_sum_of_ext(r, count_term(gq(p), kr(k)), lift(p, trc));
    lemma_reduce(ps, ss, ns, p, trc);
    assert forall|c: int| 0 <= c < n implies trc(#[trigger] ps_rows(sv)[c]) == (t_cnt(sv, k))(c) by {
        assert(ps[c][0] == Val::Int(ps_pkeys(sv)[c] as int));
    }
    lemma_rows_rsum(sv, p, trc, t_cnt(sv, k), 0, n);
    // absolute mass
    let tra = |w: Row| if w[0] == Val::Int(k) { abs(ival(w[3]) * ival(w[2])) } else { 0 };
    lemma_sum_of_ext(r, abs_term(gq(p), kr(k), 0), lift(p, tra));
    lemma_reduce(ps, ss, ns, p, tra);
    assert forall|c: int| 0 <= c < n implies tra(#[trigger] ps_rows(sv)[c]) == (t_abs(sv, k))(c) by {
        assert(ps[c][0] == Val::Int(ps_pkeys(sv)[c] as int));
    }
    lemma_rows_rsum(sv, p, tra, t_abs(sv, k), 0, n);
}

/// The accumulators of the scalar block are the stored-row sums over all qualifying rows.
pub proof fn lemma_scalar_acc(sv: StoresView, p: Seq<u8>)
    requires stores_wf(sv), keys_ok(sv),
    ensures
        gsum(sq(p), from_rows(sv), Seq::<Val>::empty(), 0) == rsum(sv, p, t_val(sv), 0, ps_n(sv) as int),
        gcount(sq(p), from_rows(sv), Seq::<Val>::empty()) == rsum(sv, p, t_one(), 0, ps_n(sv) as int),
        gabs(sq(p), from_rows(sv), Seq::<Val>::empty(), 0) == rsum(sv, p, t_absv(sv), 0, ps_n(sv) as int),
{
    let (ps, ss, ns) = (ps_rows(sv), supp_rows(sv), nat_rows(sv));
    let r = from_rows(sv);
    let n = ps_n(sv) as int;
    let e = Seq::<Val>::empty();
    lemma_widths(sv);
    lemma_cols_unique(sv);
    lemma_terms_lift(sv, p, 0);
    lemma_acc_sum_of(sq(p), r, e, 0);
    assert(ps.subrange(0, n) =~= ps);
    let tr = |w: Row| ival(w[3]) * ival(w[2]);
    lemma_sum_of_ext(r, sum_term(sq(p), e, 0), lift(p, tr));
    lemma_reduce(ps, ss, ns, p, tr);
    lemma_rows_rsum(sv, p, tr, t_val(sv), 0, n);
    let trc = |w: Row| 1int;
    lemma_sum_of_ext(r, count_term(sq(p), e), lift(p, trc));
    lemma_reduce(ps, ss, ns, p, trc);
    lemma_rows_rsum(sv, p, trc, t_one(), 0, n);
    let tra = |w: Row| abs(ival(w[3]) * ival(w[2]));
    lemma_sum_of_ext(r, abs_term(sq(p), e, 0), lift(p, tra));
    lemma_reduce(ps, ss, ns, p, tra);
    lemma_rows_rsum(sv, p, tra, t_absv(sv), 0, n);
}

} // verus!
