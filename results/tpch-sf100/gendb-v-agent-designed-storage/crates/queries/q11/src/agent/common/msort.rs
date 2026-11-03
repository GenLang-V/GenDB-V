//! Merge sort of `(i64, i128)` pairs by the `i128` component, descending: `merge_into` merges two descending runs
//! into preallocated slots, `msort` sorts a range in place with a preallocated scratch buffer (no allocation, so both
//! run inside worker tasks), and `merge_vecs` merges two descending vectors into a new one (calling thread). Every
//! result is a permutation of its input (`to_multiset`) and descending (`desc`).
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::multiset::Multiset;

verus! {

broadcast use vstd::seq_lib::group_to_multiset_ensures;

/// Descending by the second component.
pub open spec fn desc(s: Seq<(i64, i128)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i].1 >= #[trigger] s[j].1
}

/// `s[lo .. hi]`.
pub open spec fn seg(s: Seq<(i64, i128)>, lo: int, hi: int) -> Seq<(i64, i128)> {
    s.subrange(lo, hi)
}

/// One more element at the end of a segment.
proof fn lemma_seg_push(s: Seq<(i64, i128)>, lo: int, hi: int)
    requires 0 <= lo <= hi < s.len(),
    ensures seg(s, lo, hi + 1) == seg(s, lo, hi).push(s[hi]),
{
    assert(seg(s, lo, hi + 1) =~= seg(s, lo, hi).push(s[hi]));
}

/// Adjacent segments concatenate.
proof fn lemma_seg_concat(s: Seq<(i64, i128)>, lo: int, mid: int, hi: int)
    requires 0 <= lo <= mid <= hi <= s.len(),
    ensures seg(s, lo, hi) == seg(s, lo, mid) + seg(s, mid, hi),
        seg(s, lo, hi).to_multiset() == seg(s, lo, mid).to_multiset().add(seg(s, mid, hi).to_multiset()),
{
    assert(seg(s, lo, hi) =~= seg(s, lo, mid) + seg(s, mid, hi));
    lemma_multiset_commutative(seg(s, lo, mid), seg(s, mid, hi));
}

/// A descending segment, by position.
proof fn lemma_desc_at(s: Seq<(i64, i128)>, lo: int, hi: int, a: int, b: int)
    requires 0 <= lo <= a <= b < hi <= s.len(), desc(seg(s, lo, hi)),
    ensures s[a].1 >= s[b].1,
{
    if a < b {
        assert(seg(s, lo, hi)[a - lo] == s[a] && seg(s, lo, hi)[b - lo] == s[b]);
    }
}

/// Appending an element not above the last keeps a sequence descending.
proof fn lemma_desc_push(s: Seq<(i64, i128)>, x: (i64, i128))
    requires desc(s), s.len() > 0 ==> s.last().1 >= x.1,
    ensures desc(s.push(x)),
{
    assert forall|a: int, b: int| 0 <= a < b < s.len() + 1 implies #[trigger] s.push(x)[a].1 >= #[trigger] s.push(x)[b].1 by {
        if b < s.len() {
            assert(s.push(x)[a] == s[a] && s.push(x)[b] == s[b]);
        } else {
            assert(s.push(x)[a] == s[a]);
            if a < s.len() - 1 {
                assert(s[a].1 >= s[s.len() - 1].1);
            }
        }
    }
}

/// The merge state after `k - lo` steps: `dst[lo .. k]` is descending, a permutation of `src[lo .. i]` and
/// `src[mid .. j]`, and its last element is at least every element still to come.
pub open spec fn merge_inv(src: Seq<(i64, i128)>, dst: Seq<(i64, i128)>, old_dst: Seq<(i64, i128)>, lo: int, mid: int, hi: int,
    i: int, j: int, k: int) -> bool
{
    &&& 0 <= lo <= i <= mid <= j <= hi <= src.len() && dst.len() == src.len() && old_dst.len() == src.len()
    &&& k == lo + (i - lo) + (j - mid)
    &&& desc(seg(src, lo, mid)) && desc(seg(src, mid, hi))
    &&& desc(seg(dst, lo, k))
    &&& seg(dst, lo, k).to_multiset() == seg(src, lo, i).to_multiset().add(seg(src, mid, j).to_multiset())
    &&& k > lo ==> (i < mid ==> dst[k - 1].1 >= src[i].1) && (j < hi ==> dst[k - 1].1 >= src[j].1)
    &&& forall|x: int| 0 <= x < dst.len() && !(lo <= x < hi) ==> #[trigger] dst[x] == old_dst[x]
}

/// One merge step: writing the larger head (`src[i]` when `left`, else `src[j]`) at `dst[k]`.
proof fn lemma_merge_step(src: Seq<(i64, i128)>, d0: Seq<(i64, i128)>, d1: Seq<(i64, i128)>, old_dst: Seq<(i64, i128)>,
    lo: int, mid: int, hi: int, i: int, j: int, k: int, left: bool)
    requires
        merge_inv(src, d0, old_dst, lo, mid, hi, i, j, k),
        left ==> i < mid && (j < hi ==> src[i].1 >= src[j].1),
        !left ==> j < hi && (i < mid ==> src[j].1 > src[i].1),
        d1 == d0.update(k, if left { src[i] } else { src[j] }),
    ensures
        left ==> merge_inv(src, d1, old_dst, lo, mid, hi, i + 1, j, k + 1),
        !left ==> merge_inv(src, d1, old_dst, lo, mid, hi, i, j + 1, k + 1),
{
    let x = if left { src[i] } else { src[j] };
    assert(k < hi);
    assert(d1.len() == d0.len());
    lemma_seg_push(d1, lo, k);
    assert(seg(d1, lo, k) =~= seg(d0, lo, k));
    if k > lo {
        assert(seg(d0, lo, k).last() == d0[k - 1]);
    }
    assert(seg(d1, lo, k + 1) == seg(d0, lo, k).push(x));
    lemma_desc_push(seg(d0, lo, k), x);
    assert(d1[k] == x);
    assert forall|y: int| 0 <= y < d1.len() && !(lo <= y < hi) implies #[trigger] d1[y] == old_dst[y] by {
        assert(d1[y] == d0[y]);
    }
    if left {
        lemma_seg_push(src, lo, i);
        if i + 1 < mid {
            lemma_desc_at(src, lo, mid, i, i + 1);
        }
        assert(seg(d1, lo, k + 1).to_multiset() =~= seg(src, lo, i + 1).to_multiset().add(seg(src, mid, j).to_multiset()));
    } else {
        lemma_seg_push(src, mid, j);
        if j + 1 < hi {
            lemma_desc_at(src, mid, hi, j, j + 1);
        }
        assert(seg(d1, lo, k + 1).to_multiset() =~= seg(src, lo, i).to_multiset().add(seg(src, mid, j + 1).to_multiset()));
    }
}

/// Merges the descending runs `src[lo .. mid]` and `src[mid .. hi]` into `dst[lo .. hi]` (other slots unchanged).
/// While both runs have elements the larger head is chosen without a branch (index select).
pub fn merge_into(src: &Vec<(i64, i128)>, lo: usize, mid: usize, hi: usize, dst: &mut Vec<(i64, i128)>)
    requires
        lo <= mid <= hi <= src@.len(), old(dst)@.len() == src@.len(),
        desc(seg(src@, lo as int, mid as int)), desc(seg(src@, mid as int, hi as int)),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        desc(seg(final(dst)@, lo as int, hi as int)),
        seg(final(dst)@, lo as int, hi as int).to_multiset() == seg(src@, lo as int, hi as int).to_multiset(),
        forall|x: int| 0 <= x < final(dst)@.len() && !(lo <= x < hi) ==> #[trigger] final(dst)@[x] == old(dst)@[x],
    no_unwind
{
    let mut i = lo;
    let mut j = mid;
    let mut k = lo;
    proof {
        let e = Seq::<(i64, i128)>::empty();
        assert(seg(dst@, lo as int, lo as int) =~= e);
        assert(seg(src@, lo as int, lo as int) =~= e);
        assert(seg(src@, mid as int, mid as int) =~= e);
        assert(e.to_multiset() =~= Multiset::empty());
        assert(Multiset::<(i64, i128)>::empty().add(Multiset::empty()) =~= Multiset::empty());
    }
    while i < mid && j < hi
        invariant merge_inv(src@, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int),
        decreases hi - k,
    {
        let ghost d0 = dst@;
        let left = src[i].1 >= src[j].1;
        let p = if left { i } else { j };
        crate::gendb_entry::work::put(dst, k, src[p]);
        proof { lemma_merge_step(src@, d0, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int, left); }
        i = if left { i + 1 } else { i };
        j = if left { j } else { j + 1 };
        k = k + 1;
    }
    while i < mid
        invariant merge_inv(src@, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int),
            i == mid || j == hi,
        decreases mid - i,
    {
        let ghost d0 = dst@;
        crate::gendb_entry::work::put(dst, k, src[i]);
        proof { lemma_merge_step(src@, d0, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int, true); }
        i = i + 1;
        k = k + 1;
    }
    while j < hi
        invariant merge_inv(src@, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int), i == mid,
        decreases hi - j,
    {
        let ghost d0 = dst@;
        crate::gendb_entry::work::put(dst, k, src[j]);
        proof { lemma_merge_step(src@, d0, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int, false); }
        j = j + 1;
        k = k + 1;
    }
    proof {
        lemma_seg_concat(src@, lo as int, mid as int, hi as int);
    }
}

/// A segment of length at most 1 is descending.
proof fn lemma_desc_short(s: Seq<(i64, i128)>, lo: int, hi: int)
    requires 0 <= lo <= hi <= s.len(), hi - lo <= 1,
    ensures desc(seg(s, lo, hi)),
{
}

/// Copies `src[lo .. hi]` into `dst[lo .. hi]` (other slots unchanged).
fn copy_seg(src: &Vec<(i64, i128)>, lo: usize, hi: usize, dst: &mut Vec<(i64, i128)>)
    requires lo <= hi <= src@.len(), old(dst)@.len() == src@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        seg(final(dst)@, lo as int, hi as int) == seg(src@, lo as int, hi as int),
        forall|x: int| 0 <= x < final(dst)@.len() && !(lo <= x < hi) ==> #[trigger] final(dst)@[x] == old(dst)@[x],
    no_unwind
{
    let mut k = lo;
    while k < hi
        invariant
            lo <= k <= hi <= src@.len(), dst@.len() == src@.len(),
            forall|x: int| lo <= x < k ==> #[trigger] dst@[x] == src@[x],
            forall|x: int| 0 <= x < dst@.len() && !(lo <= x < hi) ==> #[trigger] dst@[x] == old(dst)@[x],
        decreases hi - k,
    {
        crate::gendb_entry::work::put(dst, k, src[k]);
        k = k + 1;
    }
    assert(seg(dst@, lo as int, hi as int) =~= seg(src@, lo as int, hi as int));
}

/// Sorts `v[lo .. hi]` descending by the second component, in place (scratch `tmp`; other slots unchanged).
pub fn msort(v: &mut Vec<(i64, i128)>, tmp: &mut Vec<(i64, i128)>, lo: usize, hi: usize)
    requires lo <= hi <= old(v)@.len(), old(tmp)@.len() == old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(), final(tmp)@.len() == old(tmp)@.len(),
        desc(seg(final(v)@, lo as int, hi as int)),
        seg(final(v)@, lo as int, hi as int).to_multiset() == seg(old(v)@, lo as int, hi as int).to_multiset(),
        forall|x: int| 0 <= x < final(v)@.len() && !(lo <= x < hi) ==> #[trigger] final(v)@[x] == old(v)@[x],
    decreases hi - lo,
    no_unwind
{
    if hi - lo < 2 {
        proof { lemma_desc_short(v@, lo as int, hi as int); }
        return;
    }
    let ghost v0 = v@;
    let mid = lo + (hi - lo) / 2;
    msort(v, tmp, lo, mid);
    let ghost v1 = v@;
    msort(v, tmp, mid, hi);
    let ghost v2 = v@;
    proof {
        assert(seg(v2, lo as int, mid as int) =~= seg(v1, lo as int, mid as int));
        assert(seg(v1, mid as int, hi as int) =~= seg(v0, mid as int, hi as int));
        lemma_seg_concat(v0, lo as int, mid as int, hi as int);
        lemma_seg_concat(v2, lo as int, mid as int, hi as int);
    }
    merge_into(v, lo, mid, hi, tmp);
    copy_seg(tmp, lo, hi, v);
}

/// Sorts `v` descending by the second component (a permutation of `v`).
pub fn sort_desc(v: &mut Vec<(i64, i128)>)
    ensures desc(final(v)@), final(v)@.to_multiset() == old(v)@.to_multiset(),
{
    let n = v.len();
    let mut tmp: Vec<(i64, i128)> = vec![(0i64, 0i128); n];
    msort(v, &mut tmp, 0, n);
    proof {
        assert(seg(v@, 0, n as int) =~= v@);
        assert(seg(old(v)@, 0, n as int) =~= old(v)@);
    }
}

/// `runs` cuts `s` into consecutive descending runs: from 0 to `s.len()`, nondecreasing.
pub open spec fn runs_ok(s: Seq<(i64, i128)>, runs: Seq<usize>) -> bool {
    &&& runs.len() >= 2
    &&& runs[0] == 0
    &&& runs[runs.len() - 1] == s.len()
    &&& forall|i: int| 0 <= i < runs.len() - 1 ==> #[trigger] runs[i] <= runs[i + 1]
    &&& forall|i: int| 0 <= i < runs.len() - 1 ==> desc(#[trigger] seg(s, runs[i] as int, runs[i + 1] as int))
}

/// Run bounds stay below the end.
proof fn lemma_runs_le(s: Seq<(i64, i128)>, runs: Seq<usize>, i: int)
    requires runs_ok(s, runs), 0 <= i < runs.len(),
    ensures runs[i] <= s.len(),
    decreases runs.len() - i,
{
    if i < runs.len() - 1 {
        lemma_runs_le(s, runs, i + 1);
    }
}

/// The state of a merge pass after the input runs `0 .. i`: output runs `r` cover `dst[0 .. runs[i]]`, each
/// descending, a permutation of `src[0 .. runs[i]]`.
pub open spec fn pass_inv(src: Seq<(i64, i128)>, runs: Seq<usize>, dst: Seq<(i64, i128)>, r: Seq<usize>, i: int) -> bool {
    &&& 0 <= i < runs.len()
    &&& dst.len() == src.len()
    &&& r.len() >= 1 && r[0] == 0 && r[r.len() - 1] == runs[i]
    &&& forall|x: int| 0 <= x < r.len() - 1 ==> #[trigger] r[x] <= r[x + 1]
    &&& forall|x: int| 0 <= x < r.len() - 1 ==> desc(#[trigger] seg(dst, r[x] as int, r[x + 1] as int))
    &&& seg(dst, 0, runs[i] as int).to_multiset() == seg(src, 0, runs[i] as int).to_multiset()
}

/// One more output run `dst[lo .. hi]`, a descending permutation of `src[lo .. hi]` (earlier slots unchanged).
proof fn lemma_pass_step(src: Seq<(i64, i128)>, runs: Seq<usize>, d0: Seq<(i64, i128)>, d1: Seq<(i64, i128)>,
    r: Seq<usize>, i: int, i2: int)
    requires
        pass_inv(src, runs, d0, r, i), i < i2 < runs.len(),
        runs[i] <= runs[i2] <= src.len(),
        d1.len() == d0.len(),
        forall|x: int| 0 <= x < runs[i] ==> #[trigger] d1[x] == d0[x],
        desc(seg(d1, runs[i] as int, runs[i2] as int)),
        seg(d1, runs[i] as int, runs[i2] as int).to_multiset() == seg(src, runs[i] as int, runs[i2] as int).to_multiset(),
    ensures pass_inv(src, runs, d1, r.push(runs[i2]), i2),
{
    let lo = runs[i] as int;
    let hi = runs[i2] as int;
    let r2 = r.push(runs[i2]);
    assert(seg(d1, 0, lo) =~= seg(d0, 0, lo));
    assert forall|x: int| 0 <= x < r2.len() - 1 implies desc(#[trigger] seg(d1, r2[x] as int, r2[x + 1] as int)) by {
        if x < r.len() - 1 {
            assert(r2[x] == r[x] && r2[x + 1] == r[x + 1]);
            assert(r[x + 1] <= lo) by {
                assert forall|y: int| 0 <= y < r.len() implies #[trigger] r[y] <= lo by {
                    lemma_runs_mono(r, y, r.len() - 1);
                }
            }
            assert(seg(d1, r[x] as int, r[x + 1] as int) =~= seg(d0, r[x] as int, r[x + 1] as int));
        }
    }
    assert forall|x: int| 0 <= x < r2.len() - 1 implies #[trigger] r2[x] <= r2[x + 1] by {
        if x < r.len() - 1 {
            assert(r2[x] == r[x] && r2[x + 1] == r[x + 1]);
        }
    }
    lemma_seg_concat(d1, 0, lo, hi);
    lemma_seg_concat(src, 0, lo, hi);
}

/// Nondecreasing bounds: an earlier bound is at most a later one.
proof fn lemma_runs_mono(r: Seq<usize>, a: int, b: int)
    requires 0 <= a <= b < r.len(), forall|x: int| 0 <= x < r.len() - 1 ==> #[trigger] r[x] <= r[x + 1],
    ensures r[a] <= r[b],
    decreases b - a,
{
    if a < b {
        lemma_runs_mono(r, a, b - 1);
    }
}

/// Run `i` of a cut: in bounds and descending.
proof fn lemma_runs_at(s: Seq<(i64, i128)>, runs: Seq<usize>, i: int)
    requires runs_ok(s, runs), 0 <= i < runs.len() - 1,
    ensures runs[i] <= runs[i + 1] <= s.len(), desc(seg(s, runs[i] as int, runs[i + 1] as int)),
{
    lemma_runs_le(s, runs, i + 1);
}

/// The end of a pass: the output runs cut all of `dst`, a permutation of `src`.
proof fn lemma_pass_end(src: Seq<(i64, i128)>, runs: Seq<usize>, dst: Seq<(i64, i128)>, r: Seq<usize>)
    requires runs_ok(src, runs), pass_inv(src, runs, dst, r, runs.len() - 1), r.len() >= 2,
    ensures runs_ok(dst, r), dst.to_multiset() == src.to_multiset(),
{
    assert(seg(dst, 0, src.len() as int) =~= dst);
    assert(seg(src, 0, src.len() as int) =~= src);
}

/// One pass: merges runs `2i, 2i + 1` of `src` into `dst` (an odd last run is copied); returns the new runs.
fn merge_pass(src: &Vec<(i64, i128)>, runs: &Vec<usize>, dst: &mut Vec<(i64, i128)>) -> (r: Vec<usize>)
    requires runs_ok(src@, runs@), old(dst)@.len() == src@.len(),
    ensures
        final(dst)@.len() == src@.len(),
        runs_ok(final(dst)@, r@),
        final(dst)@.to_multiset() == src@.to_multiset(),
        2 * (r@.len() - 1) <= runs@.len(),
{
    hide(desc);
    hide(seg);
    let nr = runs.len() - 1;
    let n = src.len();
    let mut r: Vec<usize> = Vec::new();
    r.push(0);
    let mut i: usize = 0;
    proof {
        reveal(seg);
        assert(seg(dst@, 0, 0) =~= seg(src@, 0, 0));
        assert(r@ =~= seq![0usize]);
        lemma_runs_le(src@, runs@, 0);
    }
    while i < nr
        invariant
            runs_ok(src@, runs@), nr == runs@.len() - 1, n == src@.len(), dst@.len() == n,
            i <= nr,
            2 * (r@.len() - 1) == i || (i == nr && 2 * (r@.len() - 1) == i + 1),
            pass_inv(src@, runs@, dst@, r@, i as int),
        decreases nr - i,
    {
        proof { lemma_runs_at(src@, runs@, i as int); }
        let lo = runs[i];
        let ghost d0 = dst@;
        let ghost r0 = r@;
        if i + 1 < nr {
            proof { lemma_runs_at(src@, runs@, i as int + 1); }
            let mid = runs[i + 1];
            let hi = runs[i + 2];
            merge_into(src, lo, mid, hi, dst);
            proof { lemma_pass_step(src@, runs@, d0, dst@, r0, i as int, i as int + 2); }
            r.push(hi);
            i = i + 2;
        } else {
            let hi = runs[i + 1];
            copy_seg(src, lo, hi, dst);
            proof { lemma_pass_step(src@, runs@, d0, dst@, r0, i as int, i as int + 1); }
            r.push(hi);
            i = i + 1;
        }
    }
    proof { lemma_pass_end(src@, runs@, dst@, r@); }
    r
}

/// Merges the descending runs of `v` (cut by `runs`) into one descending permutation of `v`.
pub fn merge_runs(v: Vec<(i64, i128)>, runs: Vec<usize>) -> (r: Vec<(i64, i128)>)
    requires runs_ok(v@, runs@),
    ensures desc(r@), r@.to_multiset() == v@.to_multiset(),
{
    let n = v.len();
    let mut src = v;
    let mut dst: Vec<(i64, i128)> = vec![(0i64, 0i128); n];
    let mut runs = runs;
    let ghost v0 = src@;
    while runs.len() > 2
        invariant runs_ok(src@, runs@), dst@.len() == src@.len(), src@.to_multiset() == v0.to_multiset(),
        decreases runs@.len(),
    {
        let r2 = merge_pass(&src, &runs, &mut dst);
        let t = src;
        src = dst;
        dst = t;
        runs = r2;
    }
    proof {
        if runs@.len() == 2 {
            assert(seg(src@, runs@[0] as int, runs@[1] as int) =~= src@);
        }
    }
    src
}

} // verus!
