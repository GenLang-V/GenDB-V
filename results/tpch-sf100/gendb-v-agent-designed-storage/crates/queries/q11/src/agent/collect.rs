//! Collecting the filtered groups of the task ranges in range order (`append_task`). After the ranges below bound
//! `b[k]` (`acc_ok`): every collected pair is a group with its whole-table SUM above the threshold, keys strictly
//! increasing and below the next range's first key, and every group with a qualifying row below `b[k]` and a SUM
//! above the threshold collected. After the last range this is `finish::res_ok` (`lemma_acc_end`).
use vstd::prelude::*;
use super::tables::Tabs;
use super::rows::*;
use super::groups::*;
use super::tasks::*;
use super::finish::{res_ok, n_of, above};
use super::common::msort::desc;

verus! {

pub open spec fn acc_ok(t: Tabs, name: Seq<u8>, b: Seq<usize>, k: int, res: Seq<(i64, i128)>, thr: i128) -> bool {
    let n = n_of(t);
    &&& forall|i: int| 0 <= i < res.len() ==> {
        &&& kcnt(t, name, #[trigger] res[i].0 as int, 0, n) > 0
        &&& res[i].1 as int == ksum(t, name, res[i].0 as int, 0, n)
        &&& res[i].1 > thr
    }
    &&& forall|i: int, j: int| 0 <= i < res.len() && 0 <= j < res.len() && i != j ==> #[trigger] res[i].0 != #[trigger] res[j].0
    &&& b[k] < n ==> forall|i: int| 0 <= i < res.len() ==> #[trigger] res[i].0 < rkey(t, b[k] as int)
    &&& forall|key: int| #[trigger] kcnt(t, name, key, 0, b[k] as int) > 0 && ksum(t, name, key, 0, n) > thr ==>
            exists|i: int| 0 <= i < res.len() && res[i].0 as int == key
}

pub proof fn lemma_acc_start(t: Tabs, name: Seq<u8>, b: Seq<usize>, thr: i128)
    requires b.len() > 0, b[0] == 0,
    ensures acc_ok(t, name, b, 0, Seq::empty(), thr),
{
}

/// After the last range: the result pairs (`thr` decides the HAVING comparison).
pub proof fn lemma_acc_end(t: Tabs, name: Seq<u8>, b: Seq<usize>, nt: int, res: Seq<(i64, i128)>, thr: i128, pc: int)
    requires
        0 <= nt < b.len(), b[nt] == n_of(t),
        acc_ok(t, name, b, nt, res, thr),
        forall|s: int| #[trigger] above(s, tsum(t, name, 0, n_of(t)) * pc) <==> s > thr,
    ensures res_ok(t, name, res, pc),
{
    let n = n_of(t);
    let tc = tsum(t, name, 0, n);
    assert forall|i: int| 0 <= i < res.len() implies above(res[i].1 as int, tc * pc) by {
        assert(kcnt(t, name, res[i].0 as int, 0, n) > 0);
        assert(res[i].1 > thr);
        assert(above(res[i].1 as int, tc * pc) <==> res[i].1 > thr);
    }
    assert forall|key: int| #[trigger] kcnt(t, name, key, 0, n) > 0 && above(ksum(t, name, key, 0, n), tc * pc) implies
        exists|i: int| 0 <= i < res.len() && res[i].0 as int == key by {
        assert(above(ksum(t, name, key, 0, n), tc * pc) <==> ksum(t, name, key, 0, n) > thr);
    }
}

/// The bounds of range `k`: in order, inside the table, each at a change of key.
proof fn lemma_range_facts(t: Tabs, b: Seq<usize>, nt: int, n: int, k: int)
    requires bounds_ok(t, b, nt, n), 0 <= k < nt,
    ensures
        0 <= b[k] <= b[k + 1] <= n,
        b[k] == 0 || b[k] == n || rkey(t, b[k] - 1) != rkey(t, b[k] as int),
        b[k + 1] == 0 || b[k + 1] == n || rkey(t, b[k + 1] - 1) != rkey(t, b[k + 1] as int),
{
    assert forall|j: int| 0 <= j < nt implies #[trigger] b[j] <= b[j + 1] by {}
    lemma_bounds_mono(t, b, nt, n, k + 1);
}

/// Every bound is at most `n`.
proof fn lemma_bounds_mono(t: Tabs, b: Seq<usize>, nt: int, n: int, k: int)
    requires bounds_ok(t, b, nt, n), 0 <= k <= nt,
    ensures b[k] <= n,
    decreases nt - k,
{
    if k < nt {
        lemma_bounds_mono(t, b, nt, n, k + 1);
        assert(b[k] <= b[k + 1]);
    }
}

/// The range's facts per element of its filtered groups: a group of the range with the whole table's SUM.
pub open spec fn elem_ok(t: Tabs, name: Seq<u8>, lo: int, hi: int, thr: i128, e: (i64, i128)) -> bool {
    let n = n_of(t);
    &&& kcnt(t, name, e.0 as int, 0, n) > 0
    &&& e.1 as int == ksum(t, name, e.0 as int, 0, n)
    &&& e.1 > thr
    &&& lo < hi
    &&& rkey(t, lo) <= e.0
    &&& hi < n ==> e.0 < rkey(t, hi)
}

proof fn lemma_filt_global(t: Tabs, name: Seq<u8>, b: Seq<usize>, nt: int, k: int,
    keys: Seq<i64>, sums: Seq<i128>, len: int, thr: i128, lb: i128)
    requires
        sorted_rows(t, 0, n_of(t)), bounds_ok(t, b, nt, n_of(t)), 0 <= k < nt,
        groups_ok(t, name, b[k] as int, b[k + 1] as int, keys, sums, len, lb),
    ensures
        forall|x: int| 0 <= x < filt(keys, sums, len, thr).len() ==>
            elem_ok(t, name, b[k] as int, b[k + 1] as int, thr, #[trigger] filt(keys, sums, len, thr)[x]),
        forall|x: int, y: int| 0 <= x < y < filt(keys, sums, len, thr).len() ==>
            #[trigger] filt(keys, sums, len, thr)[x].0 < #[trigger] filt(keys, sums, len, thr)[y].0,
{
    hide(ksum);
    hide(kcnt);
    hide(filt);
    hide(bounds_ok);
    hide(sorted_rows);
    let n = n_of(t);
    let lo = b[k] as int;
    let hi = b[k + 1] as int;
    let f = filt(keys, sums, len, thr);
    lemma_range_facts(t, b, nt, n, k);
    lemma_filt_members(keys, sums, len, thr);
    lemma_filt_sorted(keys, sums, len, thr);
    assert forall|x: int| 0 <= x < f.len() implies elem_ok(t, name, lo, hi, thr, #[trigger] f[x]) by {
        let i = choose|i: int| 0 <= i < len && #[trigger] f[x] == (keys[i], sums[i]) && sums[i] > thr;
        assert(kcnt(t, name, keys[i] as int, lo, hi) > 0);
        if hi <= lo {
            lemma_kcnt_empty(t, name, keys[i] as int, lo, hi);
        }
        lemma_outside(t, name, n, lo, hi, keys[i] as int);
    }
}

/// Elements of a permutation: each element of `o` is one of `f` and conversely.
proof fn lemma_perm_elems(f: Seq<(i64, i128)>, o: Seq<(i64, i128)>)
    requires f.to_multiset() == o.to_multiset(),
    ensures
        forall|x: int| 0 <= x < o.len() ==> f.contains(#[trigger] o[x]),
        forall|p: int| 0 <= p < f.len() ==> o.contains(#[trigger] f[p]),
{
    assert forall|x: int| 0 <= x < o.len() implies f.contains(#[trigger] o[x]) by {
        vstd::seq_lib::to_multiset_contains(o, o[x]);
        vstd::seq_lib::to_multiset_contains(f, o[x]);
        assert(o.contains(o[x]));
        assert(o.to_multiset().count(o[x]) > 0);
        assert(f.to_multiset().count(o[x]) > 0);
        assert(f.contains(o[x]));
    }
    assert forall|p: int| 0 <= p < f.len() implies o.contains(#[trigger] f[p]) by {
        vstd::seq_lib::to_multiset_contains(f, f[p]);
        vstd::seq_lib::to_multiset_contains(o, f[p]);
        assert(f.contains(f[p]));
        assert(f.to_multiset().count(f[p]) > 0);
        assert(o.to_multiset().count(f[p]) > 0);
        assert(o.contains(f[p]));
    }
}

/// A permutation `o` of a sequence `f` with strictly increasing keys has distinct keys.
proof fn lemma_perm_distinct(f: Seq<(i64, i128)>, o: Seq<(i64, i128)>)
    requires
        f.to_multiset() == o.to_multiset(),
        forall|x: int, y: int| 0 <= x < y < f.len() ==> #[trigger] f[x].0 < #[trigger] f[y].0,
    ensures forall|x: int, y: int| 0 <= x < o.len() && 0 <= y < o.len() && x != y ==> #[trigger] o[x].0 != #[trigger] o[y].0,
{
    lemma_perm_elems(f, o);
    assert(f.no_duplicates()) by {
        assert forall|x: int, y: int| 0 <= x < f.len() && 0 <= y < f.len() && x != y implies f[x] != f[y] by {
            if x < y { assert(f[x].0 < f[y].0); } else { assert(f[y].0 < f[x].0); }
        }
    }
    f.lemma_multiset_has_no_duplicates();
    assert forall|e: (i64, i128)| o.to_multiset().contains(e) implies o.to_multiset().count(e) == 1 by {
        assert(f.to_multiset().contains(e));
    }
    o.lemma_multiset_has_no_duplicates_conv();
    assert forall|x: int, y: int| 0 <= x < o.len() && 0 <= y < o.len() && x != y implies #[trigger] o[x].0 != #[trigger] o[y].0 by {
        assert(f.contains(o[x]) && f.contains(o[y]));
        let p = choose|p: int| 0 <= p < f.len() && f[p] == o[x];
        let q = choose|q: int| 0 <= q < f.len() && f[q] == o[y];
        assert(o[x] != o[y]);
        if p != q {
            if p < q { assert(f[p].0 < f[q].0); } else { assert(f[q].0 < f[p].0); }
        }
    }
}

/// The range's facts per element of a permutation `o` of its filtered groups, keys distinct, and every filtered
/// group in `o`.
proof fn lemma_o_facts(t: Tabs, name: Seq<u8>, b: Seq<usize>, nt: int, k: int,
    keys: Seq<i64>, sums: Seq<i128>, len: int, thr: i128, o: Seq<(i64, i128)>, lb: i128)
    requires
        sorted_rows(t, 0, n_of(t)), bounds_ok(t, b, nt, n_of(t)), 0 <= k < nt,
        groups_ok(t, name, b[k] as int, b[k + 1] as int, keys, sums, len, lb),
        o.to_multiset() == filt(keys, sums, len, thr).to_multiset(),
    ensures
        forall|x: int| 0 <= x < o.len() ==> elem_ok(t, name, b[k] as int, b[k + 1] as int, thr, #[trigger] o[x]),
        forall|x: int, y: int| 0 <= x < o.len() && 0 <= y < o.len() && x != y ==> #[trigger] o[x].0 != #[trigger] o[y].0,
        forall|p: int| 0 <= p < filt(keys, sums, len, thr).len() ==> o.contains(#[trigger] filt(keys, sums, len, thr)[p]),
{
    hide(ksum);
    hide(kcnt);
    hide(rkey);
    hide(elem_ok);
    let f = filt(keys, sums, len, thr);
    lemma_filt_global(t, name, b, nt, k, keys, sums, len, thr, lb);
    lemma_perm_elems(f, o);
    lemma_perm_distinct(f, o);
    assert forall|x: int| 0 <= x < o.len() implies elem_ok(t, name, b[k] as int, b[k + 1] as int, thr, #[trigger] o[x]) by {
        assert(f.contains(o[x]));
        let p = choose|p: int| 0 <= p < f.len() && f[p] == o[x];
        assert(elem_ok(t, name, b[k] as int, b[k + 1] as int, thr, f[p]));
    }
}

proof fn lemma_append_end(t: Tabs, name: Seq<u8>, b: Seq<usize>, nt: int, k: int,
    keys: Seq<i64>, sums: Seq<i128>, len: int, thr: i128, r0: Seq<(i64, i128)>, o: Seq<(i64, i128)>, r: Seq<(i64, i128)>, lb: i128)
    requires
        sorted_rows(t, 0, n_of(t)), bounds_ok(t, b, nt, n_of(t)), 0 <= k < nt,
        acc_ok(t, name, b, k, r0, thr),
        groups_ok(t, name, b[k] as int, b[k + 1] as int, keys, sums, len, lb),
        lb <= thr,
        o.to_multiset() == filt(keys, sums, len, thr).to_multiset(),
        r == r0 + o,
    ensures acc_ok(t, name, b, k + 1, r, thr),
{
    hide(ksum);
    hide(kcnt);
    hide(filt);
    hide(rkey);
    hide(bounds_ok);
    let n = n_of(t);
    let lo = b[k] as int;
    let hi = b[k + 1] as int;
    let f = filt(keys, sums, len, thr);
    lemma_range_facts(t, b, nt, n, k);
    lemma_o_facts(t, name, b, nt, k, keys, sums, len, thr, o, lb);
    assert forall|i: int| 0 <= i < r.len() implies {
        &&& kcnt(t, name, #[trigger] r[i].0 as int, 0, n) > 0
        &&& r[i].1 as int == ksum(t, name, r[i].0 as int, 0, n)
        &&& r[i].1 > thr
    } by {
        if i >= r0.len() {
            assert(r[i] == o[i - r0.len()]);
            assert(elem_ok(t, name, lo, hi, thr, o[i - r0.len()]));
        } else {
            assert(r[i] == r0[i]);
        }
    }
    // Earlier ranges' keys are below this range's first key; this range's keys are distinct.
    assert forall|i: int, j: int| 0 <= i < r.len() && 0 <= j < r.len() && i != j implies #[trigger] r[i].0 != #[trigger] r[j].0 by {
        if i >= r0.len() && j >= r0.len() {
            assert(r[i] == o[i - r0.len()] && r[j] == o[j - r0.len()]);
        } else if i < r0.len() && j < r0.len() {
            assert(r[i] == r0[i] && r[j] == r0[j]);
        } else {
            let (a, c) = if i < r0.len() { (i, j) } else { (j, i) };
            assert(r[a] == r0[a] && r[c] == o[c - r0.len()]);
            assert(elem_ok(t, name, lo, hi, thr, o[c - r0.len()]));
            assert(lo < n);
            assert(r0[a].0 < rkey(t, lo));
        }
    }
    if hi < n {
        assert forall|i: int| 0 <= i < r.len() implies #[trigger] r[i].0 < rkey(t, hi) by {
            if i >= r0.len() {
                assert(r[i] == o[i - r0.len()]);
                assert(elem_ok(t, name, lo, hi, thr, o[i - r0.len()]));
            } else {
                assert(r[i] == r0[i]);
                assert(lo < n);
                reveal(rkey);
                assert(rkey(t, lo) <= rkey(t, hi));
            }
        }
    }
    assert forall|key: int| #[trigger] kcnt(t, name, key, 0, hi) > 0 && ksum(t, name, key, 0, n) > thr implies
        exists|i: int| 0 <= i < r.len() && r[i].0 as int == key by {
        lemma_split(t, name, key, 0, lo, hi);
        lemma_bounds(t, name, key, 0, lo);
        lemma_bounds(t, name, key, lo, hi);
        if kcnt(t, name, key, 0, lo) > 0 {
            let i = choose|i: int| 0 <= i < r0.len() && r0[i].0 as int == key;
            assert(r[i] == r0[i]);
        } else {
            assert(kcnt(t, name, key, lo, hi) > 0);
            lemma_outside(t, name, n, lo, hi, key);
            assert(ksum(t, name, key, lo, hi) > lb);
            let i = choose|i: int| 0 <= i < len && keys[i] as int == key;
            assert(sums[i] as int == ksum(t, name, key, lo, hi));
            lemma_filt_complete(keys, sums, len, thr, i);
            let p = choose|p: int| 0 <= p < f.len() && f[p] == (keys[i], sums[i]);
            assert(o.contains(f[p]));
            let x = choose|x: int| 0 <= x < o.len() && o[x] == f[p];
            assert(r[r0.len() + x] == o[x]);
        }
    }
}

/// Appends range `k`'s filtered groups `out[0 .. m]` (a permutation of `filt` of its groups `keys/sums[0 .. len]`).
pub fn append_task(res: &mut Vec<(i64, i128)>, out: &Vec<(i64, i128)>, m: usize, Ghost(t): Ghost<Tabs>,
    Ghost(name): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<usize>>, Ghost(nt): Ghost<int>, Ghost(k): Ghost<int>,
    Ghost(keys): Ghost<Seq<i64>>, Ghost(sums): Ghost<Seq<i128>>, Ghost(len): Ghost<int>, Ghost(thr): Ghost<i128>,
    Ghost(lb): Ghost<i128>)
    requires
        sorted_rows(t, 0, n_of(t)),
        bounds_ok(t, b, nt, n_of(t)),
        0 <= k < nt,
        acc_ok(t, name, b, k, old(res)@, thr),
        groups_ok(t, name, b[k] as int, b[k + 1] as int, keys, sums, len, lb),
        lb <= thr,
        m <= out@.len(),
        out@.subrange(0, m as int).to_multiset() == filt(keys, sums, len, thr).to_multiset(),
    ensures
        acc_ok(t, name, b, k + 1, final(res)@, thr),
        final(res)@ == old(res)@ + out@.subrange(0, m as int),
{
    let ghost o = out@.subrange(0, m as int);
    let ghost r0 = res@;
    let mut x: usize = 0;
    while x < m
        invariant
            m <= out@.len(), o == out@.subrange(0, m as int), x <= m,
            res@ == r0 + o.subrange(0, x as int),
        decreases m - x,
    {
        assert(out@[x as int] == o[x as int]);
        res.push(out[x]);
        x = x + 1;
        proof {
            assert(res@ =~= r0 + o.subrange(0, x as int));
        }
    }
    proof {
        assert(o.subrange(0, m as int) =~= o);
        lemma_append_end(t, name, b, nt, k, keys, sums, len, thr, r0, o, res@, lb);
    }
}

/// The prefix of a descending permutation `o` of `filt(.., lb)` holding the SUMs above `thr >= lb` is a
/// permutation of `filt(.., thr)` (keys strictly increasing, so both are duplicate-free).
pub proof fn lemma_prefix_filt(keys: Seq<i64>, sums: Seq<i128>, len: int, lb: i128, thr: i128, o: Seq<(i64, i128)>, m: int)
    requires
        0 <= len <= keys.len(), len <= sums.len(),
        forall|i: int, j: int| 0 <= i < j < len ==> #[trigger] keys[i] < #[trigger] keys[j],
        lb <= thr,
        desc(o), o.to_multiset() == filt(keys, sums, len, lb).to_multiset(),
        0 <= m <= o.len(),
        forall|x: int| 0 <= x < m ==> #[trigger] o[x].1 > thr,
        m < o.len() ==> o[m].1 <= thr,
    ensures o.subrange(0, m).to_multiset() == filt(keys, sums, len, thr).to_multiset(),
{
    let fl = filt(keys, sums, len, lb);
    let ft = filt(keys, sums, len, thr);
    let p = o.subrange(0, m);
    lemma_filt_members(keys, sums, len, lb);
    lemma_filt_members(keys, sums, len, thr);
    lemma_filt_sorted(keys, sums, len, lb);
    lemma_filt_sorted(keys, sums, len, thr);
    lemma_perm_elems(fl, o);
    lemma_perm_distinct(fl, o);
    assert(ft.no_duplicates()) by {
        assert forall|x: int, y: int| 0 <= x < ft.len() && 0 <= y < ft.len() && x != y implies ft[x] != ft[y] by {
            if x < y { assert(ft[x].0 < ft[y].0); } else { assert(ft[y].0 < ft[x].0); }
        }
    }
    assert(p.no_duplicates()) by {
        assert forall|x: int, y: int| 0 <= x < p.len() && 0 <= y < p.len() && x != y implies p[x] != p[y] by {
            assert(p[x] == o[x] && p[y] == o[y]);
            assert(o[x].0 != o[y].0);
        }
    }
    // The same elements: an element of the prefix is a group above `thr`, and a group above `thr` sits in `o`
    // before every SUM at most `thr`.
    assert forall|e: (i64, i128)| p.contains(e) <==> ft.contains(e) by {
        if p.contains(e) {
            let x = choose|x: int| 0 <= x < p.len() && p[x] == e;
            assert(p[x] == o[x]);
            assert(o[x].1 > thr);
            assert(fl.contains(o[x]));
            let y = choose|y: int| 0 <= y < fl.len() && fl[y] == o[x];
            let i = choose|i: int| 0 <= i < len && #[trigger] fl[y] == (keys[i], sums[i]) && sums[i] > lb;
            assert(sums[i] == o[x].1);
            lemma_filt_complete(keys, sums, len, thr, i);
        }
        if ft.contains(e) {
            let y = choose|y: int| 0 <= y < ft.len() && ft[y] == e;
            let i = choose|i: int| 0 <= i < len && #[trigger] ft[y] == (keys[i], sums[i]) && sums[i] > thr;
            lemma_filt_complete(keys, sums, len, lb, i);
            let z = choose|z: int| 0 <= z < fl.len() && fl[z] == (keys[i], sums[i]);
            assert(o.contains(fl[z]));
            let x = choose|x: int| 0 <= x < o.len() && o[x] == fl[z];
            if x >= m {
                if x > m {
                    assert(o[m].1 >= o[x].1);
                }
                assert(false);
            }
            assert(p[x] == o[x]);
        }
    }
    p.lemma_multiset_has_no_duplicates();
    ft.lemma_multiset_has_no_duplicates();
    assert forall|e: (i64, i128)| p.to_multiset().count(e) == ft.to_multiset().count(e) by {
        vstd::seq_lib::to_multiset_contains(p, e);
        vstd::seq_lib::to_multiset_contains(ft, e);
        if p.contains(e) {
            assert(p.to_multiset().contains(e));
            assert(ft.to_multiset().contains(e));
        } else {
            assert(!ft.contains(e));
        }
    }
    assert(p.to_multiset() =~= ft.to_multiset());
}

/// The length of the prefix of the descending `out[0 .. m]` with SUMs above `thr`.
pub fn prefix_above(out: &Vec<(i64, i128)>, m: usize, thr: i128) -> (k: usize)
    requires m <= out@.len(), desc(out@.subrange(0, m as int)),
    ensures
        k <= m,
        forall|x: int| 0 <= x < k ==> #[trigger] out@[x].1 > thr,
        k < m ==> out@[k as int].1 <= thr,
{
    let mut k: usize = 0;
    while k < m && out[k].1 > thr
        invariant m <= out@.len(), k <= m, forall|x: int| 0 <= x < k ==> #[trigger] out@[x].1 > thr,
        decreases m - k,
    {
        k = k + 1;
    }
    k
}

} // verus!
