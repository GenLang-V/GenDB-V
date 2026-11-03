//! Group tables as lists of (sum, key) pairs (`Seq<(int, int)>`, the `common::msort::pairs` view) and their
//! meaning over a range of partsupp rows.
//!
//! A run list `rs` describes the rows `[lo, hi)` (`runs_ok`) when, for every part key `k`, the sums of its entries
//! add up to the range sum `rsum(t_sum(k))` and `k` has an entry exactly when some qualifying row of the range has
//! it. With strictly increasing keys (`strict`) every entry is a whole group of the range (`lemma_strict_entry`).
//! Run lists of adjacent ranges concatenate (`lemma_runs_concat`). `above(rs, thr)` keeps the entries whose sum
//! exceeds `thr` (the HAVING filter, in order). A scan that stores only the entries above a lower bound `lb` of the
//! threshold loses nothing: `above(above(rs, lb), thr) == above(rs, thr)` for `lb <= thr` (`lemma_above_above`);
//! the filter commutes with permutations (`lemma_above_ms`) and, on a list sorted by sum, descending, it is the
//! prefix of the entries above the threshold (`lemma_desc_prefix`).
//!
//! Range-sum laws (`normal::rsum`): additivity (`lemma_rsum_split`), rows without qualification add nothing
//! (`lemma_rsum_skip`), sums are bounded by absolute masses (`lemma_rsum_bounds`), a key without rows has sum 0.
use vstd::prelude::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::normal::*;
use crate::agent::common::msort::desc;

verus! {

// ------------------------------------------------------------------------------------------ range-sum laws

/// Adjacent ranges add up.
pub proof fn lemma_rsum_split(sv: StoresView, p: Seq<u8>, t: spec_fn(int) -> int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures rsum(sv, p, t, lo, mid) + rsum(sv, p, t, mid, hi) == rsum(sv, p, t, lo, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_rsum_split(sv, p, t, lo, mid, hi - 1);
    }
}

/// Rows `[a, b)` without a qualifying row add nothing.
pub proof fn lemma_rsum_skip(sv: StoresView, p: Seq<u8>, t: spec_fn(int) -> int, lo: int, a: int, b: int)
    requires lo <= a <= b, forall|c: int| a <= c < b ==> !#[trigger] qrow(sv, p, c),
    ensures rsum(sv, p, t, lo, b) == rsum(sv, p, t, lo, a),
    decreases b - a,
{
    if b > a {
        lemma_rsum_skip(sv, p, t, lo, a, b - 1);
    }
}

/// One more row.
pub proof fn lemma_rsum_step(sv: StoresView, p: Seq<u8>, t: spec_fn(int) -> int, lo: int, c: int)
    requires lo <= c,
    ensures rsum(sv, p, t, lo, c + 1) == rsum(sv, p, t, lo, c) + if qrow(sv, p, c) { t(c) } else { 0 },
{
}

/// Sums of non-negative terms are non-negative and grow with the range.
pub proof fn lemma_rsum_mono(sv: StoresView, p: Seq<u8>, t: spec_fn(int) -> int, lo: int, a: int, b: int)
    requires lo <= a <= b, forall|c: int| a <= c < b ==> #[trigger] t(c) >= 0,
    ensures rsum(sv, p, t, lo, a) <= rsum(sv, p, t, lo, b),
    decreases b - a,
{
    if b > a {
        lemma_rsum_mono(sv, p, t, lo, a, b - 1);
    }
}

/// Non-negative terms have a non-negative sum.
pub proof fn lemma_rsum_nonneg(sv: StoresView, p: Seq<u8>, t: spec_fn(int) -> int, lo: int, hi: int)
    requires forall|c: int| lo <= c < hi ==> #[trigger] t(c) >= 0,
    ensures rsum(sv, p, t, lo, hi) >= 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_nonneg(sv, p, t, lo, hi - 1);
    }
}

/// A group's sum is bounded by its absolute mass, which is at most the total absolute mass; a key without rows has
/// sum 0; counts and masses are non-negative.
pub proof fn lemma_rsum_bounds(sv: StoresView, p: Seq<u8>, k: int, lo: int, hi: int)
    ensures
        -rsum(sv, p, t_abs(sv, k), lo, hi) <= rsum(sv, p, t_sum(sv, k), lo, hi) <= rsum(sv, p, t_abs(sv, k), lo, hi),
        rsum(sv, p, t_abs(sv, k), lo, hi) <= rsum(sv, p, t_absv(sv), lo, hi),
        -rsum(sv, p, t_absv(sv), lo, hi) <= rsum(sv, p, t_val(sv), lo, hi) <= rsum(sv, p, t_absv(sv), lo, hi),
        rsum(sv, p, t_cnt(sv, k), lo, hi) >= 0,
        rsum(sv, p, t_cnt(sv, k), lo, hi) <= rsum(sv, p, t_one(), lo, hi),
        rsum(sv, p, t_cnt(sv, k), lo, hi) == 0 ==> rsum(sv, p, t_sum(sv, k), lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_bounds(sv, p, k, lo, hi - 1);
    }
}

// ------------------------------------------------------------------------------------------ run lists

/// The sums of the entries of key `k`.
pub open spec fn rs_sum(rs: Seq<(int, int)>, k: int) -> int
    decreases rs.len(),
{
    if rs.len() == 0 { 0 } else { rs_sum(rs.drop_last(), k) + if rs.last().1 == k { rs.last().0 } else { 0 } }
}

/// Some entry has key `k`.
pub open spec fn rs_has(rs: Seq<(int, int)>, k: int) -> bool {
    exists|i: int| 0 <= i < rs.len() && #[trigger] rs[i].1 == k
}

/// Strictly increasing keys.
pub open spec fn strict(rs: Seq<(int, int)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < rs.len() ==> (#[trigger] rs[i]).1 < (#[trigger] rs[j]).1
}

/// The run list describes the rows `[lo, hi)`.
pub open spec fn runs_ok(sv: StoresView, p: Seq<u8>, lo: int, hi: int, rs: Seq<(int, int)>) -> bool {
    &&& forall|k: int| #[trigger] rs_sum(rs, k) == rsum(sv, p, t_sum(sv, k), lo, hi)
    &&& forall|k: int| #[trigger] rs_has(rs, k) <==> rsum(sv, p, t_cnt(sv, k), lo, hi) > 0
}

/// One more entry.
pub proof fn lemma_rs_push(rs: Seq<(int, int)>, e: (int, int), k: int)
    ensures
        rs_sum(rs.push(e), k) == rs_sum(rs, k) + if e.1 == k { e.0 } else { 0 },
        rs_has(rs.push(e), k) == (rs_has(rs, k) || e.1 == k),
{
    let s = rs.push(e);
    assert(s.drop_last() =~= rs);
    if rs_has(rs, k) {
        let i = choose|i: int| 0 <= i < rs.len() && #[trigger] rs[i].1 == k;
        assert(s[i] == rs[i]);
    }
    if e.1 == k {
        assert(s[rs.len() as int].1 == k);
    }
    if rs_has(s, k) {
        let i = choose|i: int| 0 <= i < s.len() && #[trigger] s[i].1 == k;
        if i < rs.len() {
            assert(rs[i] == s[i]);
        }
    }
}

/// The empty list describes an empty range.
pub proof fn lemma_runs_empty(sv: StoresView, p: Seq<u8>, lo: int)
    ensures runs_ok(sv, p, lo, lo, Seq::<(int, int)>::empty()),
{
}

/// Concatenation of run lists.
pub proof fn lemma_rs_concat(a: Seq<(int, int)>, b: Seq<(int, int)>, k: int)
    ensures
        rs_sum(a + b, k) == rs_sum(a, k) + rs_sum(b, k),
        rs_has(a + b, k) == (rs_has(a, k) || rs_has(b, k)),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_rs_concat(a, b.drop_last(), k);
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_rs_push(a + b.drop_last(), b.last(), k);
        lemma_rs_push(b.drop_last(), b.last(), k);
        assert(b.drop_last().push(b.last()) =~= b);
        assert((a + b.drop_last()).push(b.last()) =~= a + b);
    }
}

/// Run lists of adjacent ranges concatenate.
pub proof fn lemma_runs_concat(sv: StoresView, p: Seq<u8>, lo: int, mid: int, hi: int, a: Seq<(int, int)>, b: Seq<(int, int)>)
    requires lo <= mid <= hi, runs_ok(sv, p, lo, mid, a), runs_ok(sv, p, mid, hi, b),
    ensures runs_ok(sv, p, lo, hi, a + b),
{
    assert forall|k: int| #[trigger] rs_sum(a + b, k) == rsum(sv, p, t_sum(sv, k), lo, hi) by {
        lemma_rs_concat(a, b, k);
        lemma_rsum_split(sv, p, t_sum(sv, k), lo, mid, hi);
    }
    assert forall|k: int| #[trigger] rs_has(a + b, k) <==> rsum(sv, p, t_cnt(sv, k), lo, hi) > 0 by {
        lemma_rs_concat(a, b, k);
        lemma_rsum_split(sv, p, t_cnt(sv, k), lo, mid, hi);
        lemma_rsum_bounds(sv, p, k, lo, mid);
        lemma_rsum_bounds(sv, p, k, mid, hi);
    }
}

/// Under strictly increasing keys, the sums of key `rs[i].1` are `rs[i].0`.
pub proof fn lemma_strict_sum(rs: Seq<(int, int)>, i: int)
    requires strict(rs), 0 <= i < rs.len(),
    ensures rs_sum(rs, rs[i].1) == rs[i].0,
    decreases rs.len(),
{
    let k = rs[i].1;
    let d = rs.drop_last();
    if i == rs.len() - 1 {
        lemma_strict_absent(d, k);
    } else {
        assert(strict(d)) by {
            assert forall|a: int, b: int| 0 <= a < b < d.len() implies (#[trigger] d[a]).1 < (#[trigger] d[b]).1 by {
                assert(d[a] == rs[a] && d[b] == rs[b]);
            }
        }
        assert(d[i] == rs[i]);
        lemma_strict_sum(d, i);
        assert(rs.last().1 > k) by {
            assert(rs[i].1 < rs[rs.len() - 1].1);
        }
    }
}

/// Under strictly increasing keys below `k`, no entry has key `k`: its sum is 0.
proof fn lemma_strict_absent(d: Seq<(int, int)>, k: int)
    requires forall|j: int| 0 <= j < d.len() ==> (#[trigger] d[j]).1 < k,
    ensures rs_sum(d, k) == 0,
    decreases d.len(),
{
    if d.len() > 0 {
        let e = d.drop_last();
        assert forall|j: int| 0 <= j < e.len() implies (#[trigger] e[j]).1 < k by {
            assert(e[j] == d[j]);
        }
        lemma_strict_absent(e, k);
        assert(d.last().1 < k) by {
            assert(d[d.len() - 1].1 < k);
        }
    }
}

/// Under `runs_ok` and strictly increasing keys, every entry is a whole group of the range.
pub proof fn lemma_strict_entry(sv: StoresView, p: Seq<u8>, lo: int, hi: int, rs: Seq<(int, int)>, i: int)
    requires runs_ok(sv, p, lo, hi, rs), strict(rs), 0 <= i < rs.len(),
    ensures
        rs[i].0 == rsum(sv, p, t_sum(sv, rs[i].1), lo, hi),
        rsum(sv, p, t_cnt(sv, rs[i].1), lo, hi) > 0,
{
    lemma_strict_sum(rs, i);
    assert(rs_sum(rs, rs[i].1) == rsum(sv, p, t_sum(sv, rs[i].1), lo, hi));
    assert(rs_has(rs, rs[i].1));
}

// ------------------------------------------------------------------------------------------ the HAVING filter

/// The entries whose sum exceeds `thr`, in order.
pub open spec fn above(rs: Seq<(int, int)>, thr: int) -> Seq<(int, int)>
    decreases rs.len(),
{
    if rs.len() == 0 {
        Seq::empty()
    } else if rs.last().0 > thr {
        above(rs.drop_last(), thr).push(rs.last())
    } else {
        above(rs.drop_last(), thr)
    }
}

/// `above` keeps exactly the entries above the threshold, in order (so it keeps strict keys).
pub proof fn lemma_above(rs: Seq<(int, int)>, thr: int)
    ensures
        forall|e: (int, int)| #[trigger] above(rs, thr).contains(e) <==> (rs.contains(e) && e.0 > thr),
        strict(rs) ==> strict(above(rs, thr)),
        forall|j: int| 0 <= j < above(rs, thr).len() ==> rs.contains(#[trigger] above(rs, thr)[j]),
    decreases rs.len(),
{
    if rs.len() > 0 {
        let d = rs.drop_last();
        let x = rs.last();
        lemma_above(d, thr);
        let a = above(rs, thr);
        let ad = above(d, thr);
        assert(rs =~= d.push(x));
        assert forall|e: (int, int)| #[trigger] a.contains(e) <==> (rs.contains(e) && e.0 > thr) by {
            if a.contains(e) {
                let j = choose|j: int| 0 <= j < a.len() && a[j] == e;
                if x.0 > thr && j == ad.len() {
                    assert(rs[rs.len() - 1] == e);
                } else {
                    assert(ad[j] == e);
                    assert(ad.contains(e));
                    let i = choose|i: int| 0 <= i < d.len() && d[i] == e;
                    assert(rs[i] == e);
                }
            }
            if rs.contains(e) && e.0 > thr {
                let i = choose|i: int| 0 <= i < rs.len() && rs[i] == e;
                if i == rs.len() - 1 {
                    assert(a[ad.len() as int] == e);
                } else {
                    assert(d[i] == e);
                    assert(ad.contains(e));
                    let j = choose|j: int| 0 <= j < ad.len() && ad[j] == e;
                    assert(a[j] == e);
                }
            }
        }
        assert forall|j: int| 0 <= j < a.len() implies rs.contains(#[trigger] a[j]) by {
            assert(a.contains(a[j]));
        }
        if strict(rs) {
            assert(strict(d)) by {
                assert forall|i: int, j: int| 0 <= i < j < d.len() implies (#[trigger] d[i]).1 < (#[trigger] d[j]).1 by {
                    assert(d[i] == rs[i] && d[j] == rs[j]);
                }
            }
            if x.0 > thr {
                assert forall|i: int, j: int| 0 <= i < j < a.len() implies (#[trigger] a[i]).1 < (#[trigger] a[j]).1 by {
                    if j == ad.len() {
                        assert(ad.contains(ad[i]));
                        assert(d.contains(ad[i]));
                        let m = choose|m: int| 0 <= m < d.len() && d[m] == ad[i];
                        assert(rs[m].1 < rs[rs.len() - 1].1);
                    } else {
                        assert(a[i] == ad[i] && a[j] == ad[j]);
                    }
                }
            }
        }
    } else {
        assert(above(rs, thr) =~= Seq::<(int, int)>::empty());
    }
}

/// `above` keeps at most all entries.
pub proof fn lemma_above_len(rs: Seq<(int, int)>, thr: int)
    ensures above(rs, thr).len() <= rs.len(),
    decreases rs.len(),
{
    if rs.len() > 0 {
        lemma_above_len(rs.drop_last(), thr);
    }
}

/// A positive mass or a non-zero total needs a qualifying row.
pub proof fn lemma_some_row(sv: StoresView, p: Seq<u8>, lo: int, hi: int)
    requires rsum(sv, p, t_absv(sv), lo, hi) != 0 || rsum(sv, p, t_val(sv), lo, hi) != 0,
    ensures rsum(sv, p, t_one(), lo, hi) > 0,
    decreases hi - lo,
{
    if hi > lo {
        if rsum(sv, p, t_absv(sv), lo, hi - 1) != 0 || rsum(sv, p, t_val(sv), lo, hi - 1) != 0 {
            lemma_some_row(sv, p, lo, hi - 1);
        }
        lemma_rsum_nonneg(sv, p, t_one(), lo, hi - 1);
    }
}

/// The absolute mass of a sub-range is at most that of an enclosing range.
pub proof fn lemma_mass_sub(sv: StoresView, p: Seq<u8>, a: int, lo: int, hi: int, b: int)
    requires a <= lo <= hi <= b,
    ensures rsum(sv, p, t_absv(sv), lo, hi) <= rsum(sv, p, t_absv(sv), a, b),
{
    lemma_rsum_split(sv, p, t_absv(sv), a, lo, hi);
    lemma_rsum_split(sv, p, t_absv(sv), a, hi, b);
    assert forall|c: int| a <= c < lo implies #[trigger] (t_absv(sv))(c) >= 0 by {}
    assert forall|c: int| hi <= c < b implies #[trigger] (t_absv(sv))(c) >= 0 by {}
    lemma_rsum_nonneg(sv, p, t_absv(sv), a, lo);
    lemma_rsum_nonneg(sv, p, t_absv(sv), hi, b);
}

/// `above` of a concatenation.
pub proof fn lemma_above_concat(a: Seq<(int, int)>, b: Seq<(int, int)>, thr: int)
    ensures above(a + b, thr) == above(a, thr) + above(b, thr),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(above(a, thr) + above(b, thr) =~= above(a, thr));
    } else {
        lemma_above_concat(a, b.drop_last(), thr);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        if b.last().0 > thr {
            assert(above(a, thr) + above(b, thr) =~= (above(a, thr) + above(b.drop_last(), thr)).push(b.last()));
        }
    }
}

/// `above` of one more entry.
pub proof fn lemma_above_push(rs: Seq<(int, int)>, e: (int, int), thr: int)
    ensures above(rs.push(e), thr) == if e.0 > thr { above(rs, thr).push(e) } else { above(rs, thr) },
{
    assert(rs.push(e).drop_last() =~= rs);
    assert(rs.push(e).last() == e);
}

/// Filtering at a lower bound first loses nothing.
pub proof fn lemma_above_above(rs: Seq<(int, int)>, lb: int, thr: int)
    requires lb <= thr,
    ensures above(above(rs, lb), thr) == above(rs, thr),
    decreases rs.len(),
{
    if rs.len() > 0 {
        let d = rs.drop_last();
        let x = rs.last();
        lemma_above_above(d, lb, thr);
        if x.0 > lb {
            lemma_above_push(above(d, lb), x, thr);
        }
    }
}

/// How often `e` occurs in the filtered list.
pub proof fn lemma_above_count(rs: Seq<(int, int)>, thr: int, e: (int, int))
    ensures above(rs, thr).to_multiset().count(e) == if e.0 > thr { rs.to_multiset().count(e) } else { 0 },
    decreases rs.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;
    if rs.len() == 0 {
        assert(above(rs, thr) =~= Seq::<(int, int)>::empty());
    } else {
        let d = rs.drop_last();
        let x = rs.last();
        lemma_above_count(d, thr, e);
        assert(rs =~= d.push(x));
        assert(rs.to_multiset() == d.to_multiset().insert(x));
        if x.0 > thr {
            assert(above(rs, thr).to_multiset() == above(d, thr).to_multiset().insert(x));
        }
    }
}

/// Filters of permutations are permutations.
pub proof fn lemma_above_ms(a: Seq<(int, int)>, b: Seq<(int, int)>, thr: int)
    requires a.to_multiset() == b.to_multiset(),
    ensures above(a, thr).to_multiset() == above(b, thr).to_multiset(),
{
    assert forall|e: (int, int)| #[trigger] above(a, thr).to_multiset().count(e) == above(b, thr).to_multiset().count(e) by {
        lemma_above_count(a, thr, e);
        lemma_above_count(b, thr, e);
    }
    assert(above(a, thr).to_multiset() =~= above(b, thr).to_multiset());
}

/// A list whose entries all exceed `thr` is its own filter.
proof fn lemma_above_all(rs: Seq<(int, int)>, thr: int)
    requires forall|i: int| 0 <= i < rs.len() ==> (#[trigger] rs[i]).0 > thr,
    ensures above(rs, thr) == rs,
    decreases rs.len(),
{
    if rs.len() > 0 {
        let d = rs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]).0 > thr by {
            assert(d[i] == rs[i]);
        }
        lemma_above_all(d, thr);
        assert(rs.last().0 > thr) by {
            assert(rs[rs.len() - 1].0 > thr);
        }
        assert(d.push(rs.last()) =~= rs);
    } else {
        assert(above(rs, thr) =~= rs);
    }
}

/// In a list sorted by sum, descending, the entries above `thr` are the first `q`, where `q` is the first position
/// whose sum is at most `thr` (or the length).
pub proof fn lemma_desc_prefix(rs: Seq<(int, int)>, q: int, thr: int)
    requires
        desc(rs), 0 <= q <= rs.len(),
        forall|i: int| 0 <= i < q ==> (#[trigger] rs[i]).0 > thr,
        q < rs.len() ==> rs[q].0 <= thr,
    ensures above(rs, thr) == rs.take(q), desc(rs.take(q)),
    decreases rs.len(),
{
    if q == rs.len() {
        lemma_above_all(rs, thr);
        assert(rs.take(q) =~= rs);
    } else {
        let d = rs.drop_last();
        assert(desc(d)) by {
            assert forall|i: int, j: int| 0 <= i < j < d.len() implies (#[trigger] d[i]).0 >= (#[trigger] d[j]).0 by {
                assert(d[i] == rs[i] && d[j] == rs[j]);
            }
        }
        assert forall|i: int| 0 <= i < q implies (#[trigger] d[i]).0 > thr by {
            assert(d[i] == rs[i]);
        }
        if q < d.len() {
            assert(d[q] == rs[q]);
        }
        lemma_desc_prefix(d, q, thr);
        assert(rs.last().0 <= thr) by {
            if q < rs.len() - 1 {
                assert(rs[q].0 >= rs[rs.len() - 1].0);
            }
        }
        assert(d.take(q) =~= rs.take(q));
    }
}

/// Pairwise distinct keys.
pub open spec fn distinct(rs: Seq<(int, int)>) -> bool {
    forall|i: int, j: int| 0 <= i < rs.len() && 0 <= j < rs.len() && i != j ==> (#[trigger] rs[i]).1 != (#[trigger] rs[j]).1
}

/// Strictly increasing keys are distinct.
pub proof fn lemma_strict_distinct(rs: Seq<(int, int)>)
    requires strict(rs),
    ensures distinct(rs),
{
    assert forall|i: int, j: int| 0 <= i < rs.len() && 0 <= j < rs.len() && i != j implies (#[trigger] rs[i]).1 != (#[trigger] rs[j]).1 by {
        if i < j { assert(rs[i].1 < rs[j].1); } else { assert(rs[j].1 < rs[i].1); }
    }
}

/// `above` keeps distinct keys distinct.
pub proof fn lemma_above_distinct(rs: Seq<(int, int)>, thr: int)
    requires distinct(rs),
    ensures distinct(above(rs, thr)),
    decreases rs.len(),
{
    if rs.len() > 0 {
        let d = rs.drop_last();
        assert(distinct(d)) by {
            assert forall|i: int, j: int| 0 <= i < d.len() && 0 <= j < d.len() && i != j implies (#[trigger] d[i]).1 != (#[trigger] d[j]).1 by {
                assert(d[i] == rs[i] && d[j] == rs[j]);
            }
        }
        lemma_above_distinct(d, thr);
        lemma_above(d, thr);
        let a = above(rs, thr);
        let ad = above(d, thr);
        if rs.last().0 > thr {
            assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j implies (#[trigger] a[i]).1 != (#[trigger] a[j]).1 by {
                if i < ad.len() && j < ad.len() {
                    assert(a[i] == ad[i] && a[j] == ad[j]);
                } else {
                    let m = if i < ad.len() { i } else { j };
                    assert(a[m] == ad[m]);
                    assert(d.contains(ad[m]));
                    let q = choose|q: int| 0 <= q < d.len() && d[q] == ad[m];
                    assert(rs[q] == d[q]);
                    assert(rs[q].1 != rs[rs.len() - 1].1);
                }
            }
        }
    } else {
        assert(above(rs, thr) =~= Seq::<(int, int)>::empty());
    }
}

/// Concatenating strict lists whose keys are ordered keeps them strict.
pub proof fn lemma_strict_concat(a: Seq<(int, int)>, b: Seq<(int, int)>)
    requires
        strict(a), strict(b),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> (#[trigger] a[i]).1 < (#[trigger] b[j]).1,
    ensures strict(a + b),
{
    let s = a + b;
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies (#[trigger] s[i]).1 < (#[trigger] s[j]).1 by {
        if j < a.len() {
            assert(s[i] == a[i] && s[j] == a[j]);
        } else if i < a.len() {
            assert(s[i] == a[i] && s[j] == b[j - a.len()]);
        } else {
            assert(s[i] == b[i - a.len()] && s[j] == b[j - a.len()]);
        }
    }
}

} // verus!
