//! Merge sort of `u64` values ascending, in place on a range with a preallocated scratch buffer (no allocation, so
//! it runs inside worker tasks). Proved: the range ends up sorted, slots outside it are unchanged, and every
//! property that held for each element of the range (a ghost predicate `p`) still holds for each element of it (the
//! sort only moves elements around).
use vstd::prelude::*;

verus! {

/// Ascending.
pub open spec fn sorted64(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] <= #[trigger] s[j]
}

/// Every element of `s[lo .. hi]` satisfies `p`.
pub open spec fn all_in(s: Seq<u64>, lo: int, hi: int, p: spec_fn(u64) -> bool) -> bool {
    forall|x: int| lo <= x < hi ==> #[trigger] p(s[x])
}

/// `s[lo .. hi]`.
pub open spec fn seg64(s: Seq<u64>, lo: int, hi: int) -> Seq<u64> {
    s.subrange(lo, hi)
}

/// Appending an element not below the last keeps a sequence ascending.
proof fn lemma_sorted_push(s: Seq<u64>, x: u64)
    requires sorted64(s), s.len() > 0 ==> s.last() <= x,
    ensures sorted64(s.push(x)),
{
    let t = s.push(x);
    assert forall|a: int, b: int| 0 <= a < b < t.len() implies #[trigger] t[a] <= #[trigger] t[b] by {
        if b < s.len() {
            assert(t[a] == s[a] && t[b] == s[b]);
        } else {
            assert(t[a] == s[a]);
            if a < s.len() - 1 {
                assert(s[a] <= s[s.len() - 1]);
            }
        }
    }
}

/// Elements of an ascending segment, by position.
proof fn lemma_sorted_at(s: Seq<u64>, lo: int, hi: int, a: int, b: int)
    requires 0 <= lo <= a < b < hi <= s.len(), sorted64(seg64(s, lo, hi)),
    ensures s[a] <= s[b],
{
    assert(seg64(s, lo, hi)[a - lo] == s[a] && seg64(s, lo, hi)[b - lo] == s[b]);
}

/// The merge state after `k - lo` steps.
pub open spec fn merge_inv(src: Seq<u64>, dst: Seq<u64>, old_dst: Seq<u64>, p: spec_fn(u64) -> bool,
    lo: int, mid: int, hi: int, i: int, j: int, k: int) -> bool
{
    &&& 0 <= lo <= i <= mid <= j <= hi <= src.len() && dst.len() == src.len() && old_dst.len() == src.len()
    &&& k == lo + (i - lo) + (j - mid)
    &&& all_in(src, lo, hi, p)
    &&& all_in(dst, lo, k, p)
    &&& sorted64(seg64(src, lo, mid)) && sorted64(seg64(src, mid, hi))
    &&& sorted64(seg64(dst, lo, k))
    &&& k > lo ==> (i < mid ==> dst[k - 1] <= src[i]) && (j < hi ==> dst[k - 1] <= src[j])
    &&& forall|x: int| 0 <= x < dst.len() && !(lo <= x < hi) ==> #[trigger] dst[x] == old_dst[x]
}

/// One merge step: writing `src[i]` (when `left`) or `src[j]` at `dst[k]`.
proof fn lemma_merge_step(src: Seq<u64>, d0: Seq<u64>, d1: Seq<u64>, old_dst: Seq<u64>, p: spec_fn(u64) -> bool,
    lo: int, mid: int, hi: int, i: int, j: int, k: int, left: bool)
    requires
        merge_inv(src, d0, old_dst, p, lo, mid, hi, i, j, k),
        left ==> i < mid && (j < hi ==> src[i] <= src[j]),
        !left ==> j < hi && (i < mid ==> src[j] < src[i]),
        d1 == d0.update(k, if left { src[i] } else { src[j] }),
    ensures
        left ==> merge_inv(src, d1, old_dst, p, lo, mid, hi, i + 1, j, k + 1),
        !left ==> merge_inv(src, d1, old_dst, p, lo, mid, hi, i, j + 1, k + 1),
{
    let x = if left { src[i] } else { src[j] };
    assert(k < hi);
    assert(seg64(d1, lo, k) =~= seg64(d0, lo, k));
    assert(seg64(d1, lo, k + 1) =~= seg64(d0, lo, k).push(x));
    if k > lo {
        assert(seg64(d0, lo, k).last() == d0[k - 1]);
    }
    lemma_sorted_push(seg64(d0, lo, k), x);
    assert(d1[k] == x);
    assert forall|z: int| lo <= z < k + 1 implies #[trigger] p(d1[z]) by {
        if z < k {
            assert(d1[z] == d0[z]);
        } else if left {
            assert(p(src[i]));
        } else {
            assert(p(src[j]));
        }
    }
    assert forall|z: int| 0 <= z < d1.len() && !(lo <= z < hi) implies #[trigger] d1[z] == old_dst[z] by {
        assert(d1[z] == d0[z]);
    }
    if left {
        if i + 1 < mid {
            lemma_sorted_at(src, lo, mid, i, i + 1);
        }
    } else {
        if j + 1 < hi {
            lemma_sorted_at(src, mid, hi, j, j + 1);
        }
    }
}

/// Merges the ascending runs `src[lo .. mid]` and `src[mid .. hi]` into `dst[lo .. hi]` (other slots unchanged).
pub fn merge_into(src: &Vec<u64>, lo: usize, mid: usize, hi: usize, dst: &mut Vec<u64>, Ghost(p): Ghost<spec_fn(u64) -> bool>)
    requires
        lo <= mid <= hi <= src@.len(), old(dst)@.len() == src@.len(),
        all_in(src@, lo as int, hi as int, p),
        sorted64(seg64(src@, lo as int, mid as int)), sorted64(seg64(src@, mid as int, hi as int)),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        all_in(final(dst)@, lo as int, hi as int, p),
        sorted64(seg64(final(dst)@, lo as int, hi as int)),
        forall|x: int| 0 <= x < final(dst)@.len() && !(lo <= x < hi) ==> #[trigger] final(dst)@[x] == old(dst)@[x],
    no_unwind
{
    let mut i = lo;
    let mut j = mid;
    let mut k = lo;
    proof {
        assert(seg64(dst@, lo as int, lo as int) =~= Seq::<u64>::empty());
    }
    while i < mid && j < hi
        invariant merge_inv(src@, dst@, old(dst)@, p, lo as int, mid as int, hi as int, i as int, j as int, k as int),
        decreases hi - k,
    {
        let ghost d0 = dst@;
        let left = src[i] <= src[j];
        let q = if left { i } else { j };
        crate::gendb_entry::work::put(dst, k, src[q]);
        proof { lemma_merge_step(src@, d0, dst@, old(dst)@, p, lo as int, mid as int, hi as int, i as int, j as int, k as int, left); }
        i = if left { i + 1 } else { i };
        j = if left { j } else { j + 1 };
        k = k + 1;
    }
    while i < mid
        invariant merge_inv(src@, dst@, old(dst)@, p, lo as int, mid as int, hi as int, i as int, j as int, k as int),
            i == mid || j == hi,
        decreases mid - i,
    {
        let ghost d0 = dst@;
        crate::gendb_entry::work::put(dst, k, src[i]);
        proof { lemma_merge_step(src@, d0, dst@, old(dst)@, p, lo as int, mid as int, hi as int, i as int, j as int, k as int, true); }
        i = i + 1;
        k = k + 1;
    }
    while j < hi
        invariant merge_inv(src@, dst@, old(dst)@, p, lo as int, mid as int, hi as int, i as int, j as int, k as int),
            i == mid,
        decreases hi - j,
    {
        let ghost d0 = dst@;
        crate::gendb_entry::work::put(dst, k, src[j]);
        proof { lemma_merge_step(src@, d0, dst@, old(dst)@, p, lo as int, mid as int, hi as int, i as int, j as int, k as int, false); }
        j = j + 1;
        k = k + 1;
    }
}

/// Copies `src[lo .. hi]` into `dst[lo .. hi]` (other slots unchanged).
fn copy_seg(src: &Vec<u64>, lo: usize, hi: usize, dst: &mut Vec<u64>)
    requires lo <= hi <= src@.len(), old(dst)@.len() == src@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        forall|x: int| lo <= x < hi ==> #[trigger] final(dst)@[x] == src@[x],
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
}

/// Sorts `v[lo .. hi]` ascending, in place (scratch `tmp`; other slots of `v` unchanged).
pub fn msort64(v: &mut Vec<u64>, tmp: &mut Vec<u64>, lo: usize, hi: usize, Ghost(p): Ghost<spec_fn(u64) -> bool>)
    requires
        lo <= hi <= old(v)@.len(), old(tmp)@.len() == old(v)@.len(),
        all_in(old(v)@, lo as int, hi as int, p),
    ensures
        final(v)@.len() == old(v)@.len(), final(tmp)@.len() == old(tmp)@.len(),
        all_in(final(v)@, lo as int, hi as int, p),
        sorted64(seg64(final(v)@, lo as int, hi as int)),
        forall|x: int| 0 <= x < final(v)@.len() && !(lo <= x < hi) ==> #[trigger] final(v)@[x] == old(v)@[x],
    decreases hi - lo,
    no_unwind
{
    if hi - lo < 2 {
        return;
    }
    let mid = lo + (hi - lo) / 2;
    let ghost v0 = v@;
    msort64(v, tmp, lo, mid, Ghost(p));
    let ghost v1 = v@;
    proof {
        assert forall|x: int| lo <= x < hi implies #[trigger] p(v1[x]) by {
            if x >= mid {
                assert(v1[x] == v0[x]);
            }
        }
    }
    msort64(v, tmp, mid, hi, Ghost(p));
    let ghost v2 = v@;
    proof {
        assert(seg64(v2, lo as int, mid as int) =~= seg64(v1, lo as int, mid as int));
        assert forall|x: int| lo <= x < hi implies #[trigger] p(v2[x]) by {
            if x < mid {
                assert(v2[x] == v1[x]);
            }
        }
    }
    merge_into(v, lo, mid, hi, tmp, Ghost(p));
    let ghost t = tmp@;
    copy_seg(tmp, lo, hi, v);
    proof {
        assert(seg64(v@, lo as int, hi as int) =~= seg64(t, lo as int, hi as int));
        assert forall|x: int| lo <= x < hi implies #[trigger] p(v@[x]) by {
            assert(v@[x] == t[x]);
        }
    }
}

} // verus!
