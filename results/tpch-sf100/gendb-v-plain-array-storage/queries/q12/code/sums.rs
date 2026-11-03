//! The normal form's group accumulators over `orders x lineitem` as sums over lineitem rows.
//!
//! The projected FROM relation is `product_rows(po_rows(sv), pl_rows(sv))` (orders major). A joined row qualifies
//! only when its keys match, and `o_orderkey` is duplicate-free, so each lineitem row meets at most one orders row
//! (`common::sum_pick`): the accumulators of group `[ship mode m]` are sums over the lineitem rows `i` of a 0/1 term
//! that holds when row `i` passes the lineitem conditions (`l_dates_ok`: the receipt day in the stored-day window
//! `[dlo, dhi)`, `l_commitdate < l_receiptdate`, `l_shipdate < l_commitdate`), has ship mode `m`, and its order exists
//! (`cnt_term`), plus, for the high-priority count, the order's priority is high (`hi_term`) (`lemma_group_sums`).
//! Keys other than `[$1]` and `[$2]` have no rows (`lemma_other_key`). The sums are index-range sums (`common::selection::range_sum`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::product_rows;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::link::query::*;
use crate::link::expr::{ival, tval};
use crate::link::join::*;
use crate::agent::common::sum_pick::*;
use crate::agent::common::selection::*;
use crate::agent::tables::*;
use crate::agent::normal::*;

verus! {

// ------------------------------------------------------------------------------------------------ index-range sums

/// `sum_of` over the rows `r(0), .., r(n - 1)` is the index-range sum.
pub proof fn lemma_sum_of_new(n: nat, r: spec_fn(int) -> Row, f: spec_fn(Row) -> int)
    ensures sum_of(Seq::new(n, r), f) == range_sum(0, n as int, |i: int| f(r(i))),
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        lemma_sum_of_new(m, r, f);
        assert(Seq::new(n, r).drop_last() =~= Seq::new(m, r));
    }
}

// ------------------------------------------------------------------------------------------------ lineitem terms

/// Some orders row has key `k`.
pub open spec fn has_key(keys: Seq<i64>, k: i64) -> bool {
    exists|j: int| 0 <= j < keys.len() && keys[j] == k
}

/// The orders row of key `k` (when there is one).
pub open spec fn key_row(keys: Seq<i64>, k: i64) -> int {
    choose|j: int| 0 <= j < keys.len() && keys[j] == k
}

/// The lineitem conditions of row `i`: receipt day in `[dlo, dhi)`, commit before receipt, ship before commit.
pub open spec fn l_dates_ok(sv: StoresView, dlo: int, dhi: int, i: int) -> bool {
    &&& dlo <= lrd(sv)[i] < dhi
    &&& lcd(sv)[i] < lrd(sv)[i]
    &&& lsd(sv)[i] < lcd(sv)[i]
}

/// Row `i` counts for ship mode `m`: its conditions hold, its mode is `m` and its order exists.
pub open spec fn line_in(sv: StoresView, dlo: int, dhi: int, m: Seq<u8>, i: int) -> bool {
    l_dates_ok(sv, dlo, dhi, i) && mode_at(sv, i) == m && has_key(ok(sv), lok(sv)[i])
}

/// 1 for a row of group `m`.
pub open spec fn cnt_term(sv: StoresView, dlo: int, dhi: int, m: Seq<u8>) -> spec_fn(int) -> int {
    |i: int| if line_in(sv, dlo, dhi, m, i) { 1int } else { 0int }
}

/// 1 for a row of group `m` whose order has a high priority.
pub open spec fn hi_term(sv: StoresView, dlo: int, dhi: int, m: Seq<u8>) -> spec_fn(int) -> int {
    |i: int| if line_in(sv, dlo, dhi, m, i) && is_high(prio_at(sv, key_row(ok(sv), lok(sv)[i]))) { 1int } else { 0int }
}

/// 1 for a row of group `m` whose order has another priority.
pub open spec fn lo_term(sv: StoresView, dlo: int, dhi: int, m: Seq<u8>) -> spec_fn(int) -> int {
    |i: int| if line_in(sv, dlo, dhi, m, i) && !is_high(prio_at(sv, key_row(ok(sv), lok(sv)[i]))) { 1int } else { 0int }
}

// ------------------------------------------------------------------------------------------------ the window

/// The stored-day window `[dlo, dhi)` is the statement's `r >= pd AND r * usecs < t1` on SQL days `r`.
pub open spec fn win_of(dlo: int, dhi: int, pd: int, t1: int) -> bool {
    &&& dlo == pd + 10957
    &&& (dhi - 10957) * usecs() >= t1
    &&& (dhi - 10957 - 1) * usecs() < t1
}

/// `d * usecs < t1` exactly when `d < dhi - 10957`.
pub proof fn lemma_win_hi(dlo: int, dhi: int, pd: int, t1: int, d: int)
    requires win_of(dlo, dhi, pd, t1),
    ensures (d * usecs() < t1) == (d < dhi - 10957),
{
    let h = dhi - 10957;
    let u = usecs();
    if d < h {
        assert(d * u <= (h - 1) * u) by (nonlinear_arith) requires d <= h - 1, u > 0;
    } else {
        assert(d * u >= h * u) by (nonlinear_arith) requires d >= h, u > 0;
    }
}

// ------------------------------------------------------------------------------------------------ joined rows

/// The facts the sums rely on.
pub open spec fn sums_hyps(sv: StoresView, dlo: int, dhi: int, pd: int, t1: int) -> bool {
    &&& lsd(sv).len() == n_l(sv) && lcd(sv).len() == n_l(sv) && lrd(sv).len() == n_l(sv)
    &&& keys_unique(ok(sv))
    &&& win_of(dlo, dhi, pd, t1)
}

/// The normal form on the joined row of orders row `j` and lineitem row `i`.
proof fn lemma_join_row(sv: StoresView, p1: Seq<u8>, p2: Seq<u8>, dlo: int, dhi: int, pd: int, t1: int, j: int, i: int)
    requires sums_hyps(sv, dlo, dhi, pd, t1), 0 <= j < n_o(sv), 0 <= i < n_l(sv),
    ensures ({
        let x = po_row(sv, j) + pl_row(sv, i);
        let g = q12_spec(p1, p2, pd, t1);
        &&& (g.qual)(x) == (ok(sv)[j] == lok(sv)[i] && (mode_at(sv, i) == p1 || mode_at(sv, i) == p2)
                && l_dates_ok(sv, dlo, dhi, i))
        &&& (g.key)(x) == seq![Val::Text(mode_at(sv, i))]
        &&& (g.arg)(0, x) == if is_high(prio_at(sv, j)) { 1int } else { 0int }
        &&& (g.arg)(1, x) == if is_high(prio_at(sv, j)) { 0int } else { 1int }
        &&& x[0] == po_row(sv, j)[0]
        &&& x[2] == pl_row(sv, i)[0]
    }),
{
    let x = po_row(sv, j) + pl_row(sv, i);
    assert(x[0] == Val::Int(ok(sv)[j] as int));
    assert(x[1] == Val::Text(prio_at(sv, j)));
    assert(x[2] == Val::Int(lok(sv)[i] as int));
    assert(x[3] == date32_val(lsd(sv)[i]));
    assert(x[4] == date32_val(lcd(sv)[i]));
    assert(x[5] == date32_val(lrd(sv)[i]));
    assert(x[6] == Val::Text(mode_at(sv, i)));
    lemma_win_hi(dlo, dhi, pd, t1, lrd(sv)[i] - 10957);
}

/// `o_orderkey` is duplicate-free in the projected orders rows.
proof fn lemma_po_unique(sv: StoresView)
    requires keys_unique(ok(sv)),
    ensures col_unique(po_rows(sv), 0),
{
    let a = po_rows(sv);
    assert forall|p: int, q: int| 0 <= p < a.len() && 0 <= q < a.len() && #[trigger] a[p][0] == #[trigger] a[q][0] implies p == q by {
        assert(a[p] == po_row(sv, p));
        assert(a[q] == po_row(sv, q));
        assert(ok(sv)[p] == ok(sv)[q]);
    }
}

/// The picked orders row of lineitem row `i` is its key's row.
proof fn lemma_pick_row(sv: StoresView, i: int)
    requires keys_unique(ok(sv)), 0 <= i < n_l(sv),
    ensures
        has_pick(po_rows(sv), 0, Val::Int(lok(sv)[i] as int)) == has_key(ok(sv), lok(sv)[i]),
        has_key(ok(sv), lok(sv)[i]) ==> pick(po_rows(sv), 0, Val::Int(lok(sv)[i] as int)) == key_row(ok(sv), lok(sv)[i])
            && 0 <= key_row(ok(sv), lok(sv)[i]) < n_o(sv) && ok(sv)[key_row(ok(sv), lok(sv)[i])] == lok(sv)[i],
{
    let a = po_rows(sv);
    let v = Val::Int(lok(sv)[i] as int);
    let k = lok(sv)[i];
    lemma_po_unique(sv);
    lemma_pick(a, 0, v);
    if has_key(ok(sv), k) {
        let j = key_row(ok(sv), k);
        assert(a[j] == po_row(sv, j));
        assert(a[j][0] == v);
        assert(has_pick(a, 0, v));
    }
    if has_pick(a, 0, v) {
        let q = pick(a, 0, v);
        assert(a[q] == po_row(sv, q));
        assert(ok(sv)[q] == k);
        assert(has_key(ok(sv), k));
    }
}

/// A term that vanishes unless the joined row qualifies.
pub open spec fn vanishes(g: QuerySpec, f: spec_fn(Row) -> int) -> bool {
    forall|x: Row| #[trigger] f(x) != 0 ==> (g.qual)(x)
}

/// The sum over the product of a term that vanishes off qualifying rows: per lineitem row, its value at the picked
/// orders row.
proof fn lemma_product_sum(sv: StoresView, p1: Seq<u8>, p2: Seq<u8>, dlo: int, dhi: int, pd: int, t1: int, f: spec_fn(Row) -> int)
    requires sums_hyps(sv, dlo, dhi, pd, t1), vanishes(q12_spec(p1, p2, pd, t1), f),
    ensures
        sum_of(product_rows(po_rows(sv), pl_rows(sv)), f)
            == range_sum(0, n_l(sv), |i: int| at_pick(po_rows(sv), 0, pl_row(sv, i)[0], |x: Row| f(x + pl_row(sv, i)))),
{
    let (a, b) = (po_rows(sv), pl_rows(sv));
    let g = q12_spec(p1, p2, pd, t1);
    lemma_po_unique(sv);
    assert forall|p: int, q: int| 0 <= p < a.len() && 0 <= q < b.len() && f(#[trigger] a[p] + #[trigger] b[q]) != 0
        implies a[p][0] == b[q][0] by {
        assert(a[p] == po_row(sv, p));
        assert(b[q] == pl_row(sv, q));
        lemma_join_row(sv, p1, p2, dlo, dhi, pd, t1, p, q);
        assert((g.qual)(a[p] + b[q]));
    }
    lemma_sum_product_left(a, b, f, 0, 0);
    let outer = |y: Row| at_pick(a, 0, y[0], |x: Row| f(x + y));
    lemma_sum_of_new(n_l(sv) as nat, |i: int| pl_row(sv, i), outer);
    assert(b =~= Seq::new(n_l(sv) as nat, |i: int| pl_row(sv, i)));
    let h1 = |i: int| outer((|i: int| pl_row(sv, i))(i));
    let h2 = |i: int| at_pick(a, 0, pl_row(sv, i)[0], |x: Row| f(x + pl_row(sv, i)));
    assert forall|i: int| 0 <= i < n_l(sv) implies #[trigger] h1(i) == h2(i) by {}
    lemma_range_sum_ext(0, n_l(sv), h1, h2);
}

// ------------------------------------------------------------------------------------------------ the groups

/// Lineitem row `i`'s values of the three group terms at its picked orders row.
proof fn lemma_row_terms(sv: StoresView, p1: Seq<u8>, p2: Seq<u8>, dlo: int, dhi: int, pd: int, t1: int, m: Seq<u8>, i: int)
    requires sums_hyps(sv, dlo, dhi, pd, t1), m == p1 || m == p2, 0 <= i < n_l(sv),
    ensures ({
        let g = q12_spec(p1, p2, pd, t1);
        let k = seq![Val::Text(m)];
        let a = po_rows(sv);
        let y = pl_row(sv, i);
        &&& at_pick(a, 0, y[0], |x: Row| count_term(g, k)(x + y)) == cnt_term(sv, dlo, dhi, m)(i)
        &&& at_pick(a, 0, y[0], |x: Row| sum_term(g, k, 0)(x + y)) == hi_term(sv, dlo, dhi, m)(i)
        &&& at_pick(a, 0, y[0], |x: Row| sum_term(g, k, 1)(x + y)) == lo_term(sv, dlo, dhi, m)(i)
    }),
{
    let g = q12_spec(p1, p2, pd, t1);
    let k = seq![Val::Text(m)];
    let a = po_rows(sv);
    lemma_pick_row(sv, i);
    let lk = lok(sv)[i];
    assert(pl_row(sv, i)[0] == Val::Int(lk as int));
    if has_key(ok(sv), lk) {
        let j = key_row(ok(sv), lk);
        lemma_join_row(sv, p1, p2, dlo, dhi, pd, t1, j, i);
        assert(a[j] == po_row(sv, j));
        let x = po_row(sv, j) + pl_row(sv, i);
        assert(hit(g, x, k) == (l_dates_ok(sv, dlo, dhi, i) && mode_at(sv, i) == m)) by {
            if (g.key)(x) == k {
                assert(seq![Val::Text(mode_at(sv, i))][0] == k[0]);
            }
            if mode_at(sv, i) == m {
                assert(seq![Val::Text(mode_at(sv, i))] =~= k);
            }
        }
    }
}

/// The accumulators of group `[m]` (`m` one of the two modes) are the lineitem sums.
pub proof fn lemma_group_sums(sv: StoresView, p1: Seq<u8>, p2: Seq<u8>, dlo: int, dhi: int, pd: int, t1: int, m: Seq<u8>)
    requires sums_hyps(sv, dlo, dhi, pd, t1), m == p1 || m == p2,
    ensures ({
        let g = q12_spec(p1, p2, pd, t1);
        let xs = product_rows(po_rows(sv), pl_rows(sv));
        let k = seq![Val::Text(m)];
        &&& gcount(g, xs, k) == range_sum(0, n_l(sv), cnt_term(sv, dlo, dhi, m))
        &&& gsum(g, xs, k, 0) == range_sum(0, n_l(sv), hi_term(sv, dlo, dhi, m))
        &&& gsum(g, xs, k, 1) == range_sum(0, n_l(sv), lo_term(sv, dlo, dhi, m))
    }),
{
    let g = q12_spec(p1, p2, pd, t1);
    let xs = product_rows(po_rows(sv), pl_rows(sv));
    let k = seq![Val::Text(m)];
    let a = po_rows(sv);
    lemma_acc_sum_of(g, xs, k, 0);
    lemma_acc_sum_of(g, xs, k, 1);
    let fc = count_term(g, k);
    let f0 = sum_term(g, k, 0);
    let f1 = sum_term(g, k, 1);
    assert(vanishes(g, fc));
    assert(vanishes(g, f0));
    assert(vanishes(g, f1));
    lemma_product_sum(sv, p1, p2, dlo, dhi, pd, t1, fc);
    lemma_product_sum(sv, p1, p2, dlo, dhi, pd, t1, f0);
    lemma_product_sum(sv, p1, p2, dlo, dhi, pd, t1, f1);
    let pc = |i: int| at_pick(a, 0, pl_row(sv, i)[0], |x: Row| fc(x + pl_row(sv, i)));
    let p0 = |i: int| at_pick(a, 0, pl_row(sv, i)[0], |x: Row| f0(x + pl_row(sv, i)));
    let q1 = |i: int| at_pick(a, 0, pl_row(sv, i)[0], |x: Row| f1(x + pl_row(sv, i)));
    assert forall|i: int| 0 <= i < n_l(sv) implies #[trigger] pc(i) == cnt_term(sv, dlo, dhi, m)(i) by {
        lemma_row_terms(sv, p1, p2, dlo, dhi, pd, t1, m, i);
    }
    assert forall|i: int| 0 <= i < n_l(sv) implies #[trigger] p0(i) == hi_term(sv, dlo, dhi, m)(i) by {
        lemma_row_terms(sv, p1, p2, dlo, dhi, pd, t1, m, i);
    }
    assert forall|i: int| 0 <= i < n_l(sv) implies #[trigger] q1(i) == lo_term(sv, dlo, dhi, m)(i) by {
        lemma_row_terms(sv, p1, p2, dlo, dhi, pd, t1, m, i);
    }
    lemma_range_sum_ext(0, n_l(sv), pc, cnt_term(sv, dlo, dhi, m));
    lemma_range_sum_ext(0, n_l(sv), p0, hi_term(sv, dlo, dhi, m));
    lemma_range_sum_ext(0, n_l(sv), q1, lo_term(sv, dlo, dhi, m));
}

/// The low count is the count minus the high count.
pub proof fn lemma_lo_count(sv: StoresView, dlo: int, dhi: int, m: Seq<u8>, lo: int, hi: int)
    ensures range_sum(lo, hi, lo_term(sv, dlo, dhi, m)) == range_sum(lo, hi, cnt_term(sv, dlo, dhi, m)) - range_sum(lo, hi, hi_term(sv, dlo, dhi, m)),
{
    lemma_range_sum_sub(cnt_term(sv, dlo, dhi, m), hi_term(sv, dlo, dhi, m), lo_term(sv, dlo, dhi, m), lo, hi);
}

/// A key other than `[$1]` and `[$2]` has no qualifying row.
pub proof fn lemma_other_key(sv: StoresView, p1: Seq<u8>, p2: Seq<u8>, dlo: int, dhi: int, pd: int, t1: int, k: Row)
    requires sums_hyps(sv, dlo, dhi, pd, t1), k != seq![Val::Text(p1)], k != seq![Val::Text(p2)],
    ensures gcount(q12_spec(p1, p2, pd, t1), product_rows(po_rows(sv), pl_rows(sv)), k) == 0,
{
    let g = q12_spec(p1, p2, pd, t1);
    let xs = product_rows(po_rows(sv), pl_rows(sv));
    lemma_acc_sum_of(g, xs, k, 0);
    let fc = count_term(g, k);
    assert forall|t: int| 0 <= t < xs.len() implies fc(#[trigger] xs[t]) == 0 by {
        crate::agent::body::lemma_product_row(po_rows(sv), pl_rows(sv), t);
        let (j, i) = choose|j: int, i: int| 0 <= j < po_rows(sv).len() && 0 <= i < pl_rows(sv).len()
            && xs[t] == po_rows(sv)[j] + pl_rows(sv)[i];
        assert(po_rows(sv)[j] == po_row(sv, j));
        assert(pl_rows(sv)[i] == pl_row(sv, i));
        lemma_join_row(sv, p1, p2, dlo, dhi, pd, t1, j, i);
        if hit(g, xs[t], k) {
            if mode_at(sv, i) == p1 {
                assert(k =~= seq![Val::Text(p1)]);
            } else {
                assert(k =~= seq![Val::Text(p2)]);
            }
        }
    }
    lemma_sum_of_zero(xs, fc);
}

} // verus!
