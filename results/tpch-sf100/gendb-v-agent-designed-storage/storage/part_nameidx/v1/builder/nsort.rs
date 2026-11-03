//! Merge sort of row positions (`u32`) by the bytewise order (`lex_cmp`) of their text values, where the text of
//! position `x` is `bytes[offs[x] .. offs[x + 1]]` (offsets and bytes of a text column of `n` rows). `msort` sorts
//! a range in place with a preallocated scratch buffer (no allocation, so it runs inside worker tasks) and
//! `merge_runs` merges sorted runs (calling thread). Proved: the result is sorted and every element stays below
//! `n`; that the result is a permutation is checked at run time by the caller (`check_perm`).
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::bridge::order::{lemma_lex_cmp_antisym, lemma_lex_cmp_trans};
use crate::bridge::equality::lemma_lex_cmp_zero;

verus! {

/// The text of position `x`.
pub open spec fn nm(o: Seq<u64>, y: Seq<u8>, x: u32) -> Seq<u8> {
    y.subrange(o[x as int] as int, o[x as int + 1] as int)
}

/// The text of `a` is at most the text of `b`.
pub open spec fn le(o: Seq<u64>, y: Seq<u8>, a: u32, b: u32) -> bool {
    lex_cmp(nm(o, y, a), nm(o, y, b)) <= 0
}

/// Sorted by text.
pub open spec fn sorted(o: Seq<u64>, y: Seq<u8>, s: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] le(o, y, s[i], s[j])
}

/// Every element is below `n`.
pub open spec fn bounded(s: Seq<u32>, n: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < n
}

/// Offsets and bytes of `n` text values.
pub open spec fn texts_ok(o: Seq<u64>, y: Seq<u8>, n: int) -> bool {
    &&& o.len() == n + 1
    &&& forall|r: int| 0 <= r < n ==> #[trigger] o[r] <= o[r + 1] && o[r + 1] <= y.len()
}

/// `s[lo .. hi]`.
pub open spec fn seg(s: Seq<u32>, lo: int, hi: int) -> Seq<u32> {
    s.subrange(lo, hi)
}

/// `le` is reflexive.
proof fn lemma_le_refl(o: Seq<u64>, y: Seq<u8>, a: u32)
    ensures le(o, y, a, a),
{
    lemma_lex_cmp_zero(nm(o, y, a), nm(o, y, a));
}

/// `le` is transitive.
proof fn lemma_le_trans(o: Seq<u64>, y: Seq<u8>, a: u32, b: u32, c: u32)
    requires le(o, y, a, b), le(o, y, b, c),
    ensures le(o, y, a, c),
{
    lemma_lex_cmp_trans(nm(o, y, a), nm(o, y, b), nm(o, y, c));
}

/// `le` is total.
proof fn lemma_le_total(o: Seq<u64>, y: Seq<u8>, a: u32, b: u32)
    ensures le(o, y, a, b) || le(o, y, b, a),
{
    lemma_lex_cmp_antisym(nm(o, y, a), nm(o, y, b));
}

/// Appending an element not below the last keeps a sequence sorted.
proof fn lemma_sorted_push(o: Seq<u64>, y: Seq<u8>, s: Seq<u32>, x: u32)
    requires sorted(o, y, s), s.len() > 0 ==> le(o, y, s.last(), x),
    ensures sorted(o, y, s.push(x)),
{
    let t = s.push(x);
    assert forall|a: int, b: int| 0 <= a < b < t.len() implies #[trigger] le(o, y, t[a], t[b]) by {
        if b < s.len() {
            assert(t[a] == s[a] && t[b] == s[b]);
        } else {
            assert(t[a] == s[a] && t[b] == x);
            if a < s.len() - 1 {
                assert(le(o, y, s[a], s[s.len() - 1]));
                lemma_le_trans(o, y, s[a], s.last(), x);
            }
        }
    }
}

/// Elements of a sorted segment, by position.
proof fn lemma_sorted_at(o: Seq<u64>, y: Seq<u8>, s: Seq<u32>, lo: int, hi: int, a: int, b: int)
    requires 0 <= lo <= a < b < hi <= s.len(), sorted(o, y, seg(s, lo, hi)),
    ensures le(o, y, s[a], s[b]),
{
    assert(seg(s, lo, hi)[a - lo] == s[a] && seg(s, lo, hi)[b - lo] == s[b]);
}

/// Whether the text of `a` is at most the text of `b` (`no_unwind`).
pub fn text_le(offs: &[u64], bytes: &[u8], n: usize, a: u32, b: u32) -> (r: bool)
    requires
        texts_ok(offs@, bytes@, n as int),
        a < n, b < n,
    ensures r == le(offs@, bytes@, a, b),
    no_unwind
{
    let ai = a as usize;
    let bi = b as usize;
    let a0 = offs[ai] as usize;
    let a1 = offs[ai + 1] as usize;
    let b0 = offs[bi] as usize;
    let b1 = offs[bi + 1] as usize;
    let (_, ta) = bytes.split_at(a0);
    let (sa, _) = ta.split_at(a1 - a0);
    let (_, tb) = bytes.split_at(b0);
    let (sb, _) = tb.split_at(b1 - b0);
    proof {
        assert(sa@ =~= nm(offs@, bytes@, a));
        assert(sb@ =~= nm(offs@, bytes@, b));
    }
    crate::stores::custpart::interface::common::read::bytes_cmp(sa, a1 - a0, sb, b1 - b0) <= 0
}

/// The merge state after `k - lo` steps: `dst[lo .. k]` is sorted and its last element is at most every element
/// still to come.
pub open spec fn merge_inv(o: Seq<u64>, y: Seq<u8>, n: int, src: Seq<u32>, dst: Seq<u32>, old_dst: Seq<u32>,
    lo: int, mid: int, hi: int, i: int, j: int, k: int) -> bool
{
    &&& 0 <= lo <= i <= mid <= j <= hi <= src.len() && dst.len() == src.len() && old_dst.len() == src.len()
    &&& k == lo + (i - lo) + (j - mid)
    &&& bounded(src, n) && bounded(dst, n)
    &&& sorted(o, y, seg(src, lo, mid)) && sorted(o, y, seg(src, mid, hi))
    &&& sorted(o, y, seg(dst, lo, k))
    &&& k > lo ==> (i < mid ==> le(o, y, dst[k - 1], src[i])) && (j < hi ==> le(o, y, dst[k - 1], src[j]))
    &&& forall|x: int| 0 <= x < dst.len() && !(lo <= x < hi) ==> #[trigger] dst[x] == old_dst[x]
}

/// One merge step: writing `src[i]` (when `left`) or `src[j]` at `dst[k]`.
proof fn lemma_merge_step(o: Seq<u64>, y: Seq<u8>, n: int, src: Seq<u32>, d0: Seq<u32>, d1: Seq<u32>,
    old_dst: Seq<u32>, lo: int, mid: int, hi: int, i: int, j: int, k: int, left: bool)
    requires
        merge_inv(o, y, n, src, d0, old_dst, lo, mid, hi, i, j, k),
        left ==> i < mid && (j < hi ==> le(o, y, src[i], src[j])),
        !left ==> j < hi && (i < mid ==> !le(o, y, src[i], src[j])),
        d1 == d0.update(k, if left { src[i] } else { src[j] }),
    ensures
        left ==> merge_inv(o, y, n, src, d1, old_dst, lo, mid, hi, i + 1, j, k + 1),
        !left ==> merge_inv(o, y, n, src, d1, old_dst, lo, mid, hi, i, j + 1, k + 1),
{
    let x = if left { src[i] } else { src[j] };
    assert(k < hi);
    assert(seg(d1, lo, k) =~= seg(d0, lo, k));
    assert(seg(d1, lo, k + 1) =~= seg(d0, lo, k).push(x));
    if k > lo {
        assert(seg(d0, lo, k).last() == d0[k - 1]);
    }
    lemma_sorted_push(o, y, seg(d0, lo, k), x);
    assert(d1[k] == x);
    assert forall|z: int| 0 <= z < d1.len() implies #[trigger] d1[z] < n by {
        if z != k {
            assert(d1[z] == d0[z]);
        }
    }
    assert forall|z: int| 0 <= z < d1.len() && !(lo <= z < hi) implies #[trigger] d1[z] == old_dst[z] by {
        assert(d1[z] == d0[z]);
    }
    if left {
        if i + 1 < mid {
            lemma_sorted_at(o, y, src, lo, mid, i, i + 1);
        }
    } else {
        if i < mid {
            lemma_le_total(o, y, src[i], src[j]);
        }
        if j + 1 < hi {
            lemma_sorted_at(o, y, src, mid, hi, j, j + 1);
        }
    }
}

/// Merges the sorted runs `src[lo .. mid]` and `src[mid .. hi]` into `dst[lo .. hi]` (other slots unchanged).
pub fn merge_into(offs: &[u64], bytes: &[u8], n: usize, src: &Vec<u32>, lo: usize, mid: usize, hi: usize, dst: &mut Vec<u32>)
    requires
        texts_ok(offs@, bytes@, n as int),
        lo <= mid <= hi <= src@.len(), old(dst)@.len() == src@.len(),
        bounded(src@, n as int), bounded(old(dst)@, n as int),
        sorted(offs@, bytes@, seg(src@, lo as int, mid as int)), sorted(offs@, bytes@, seg(src@, mid as int, hi as int)),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        bounded(final(dst)@, n as int),
        sorted(offs@, bytes@, seg(final(dst)@, lo as int, hi as int)),
        forall|x: int| 0 <= x < final(dst)@.len() && !(lo <= x < hi) ==> #[trigger] final(dst)@[x] == old(dst)@[x],
    no_unwind
{
    let ghost (o, y) = (offs@, bytes@);
    let mut i = lo;
    let mut j = mid;
    let mut k = lo;
    proof {
        assert(seg(dst@, lo as int, lo as int) =~= Seq::<u32>::empty());
    }
    while i < mid && j < hi
        invariant merge_inv(o, y, n as int, src@, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int),
            texts_ok(o, y, n as int), o == offs@, y == bytes@,
        decreases hi - k,
    {
        let ghost d0 = dst@;
        let left = text_le(offs, bytes, n, src[i], src[j]);
        let p = if left { i } else { j };
        crate::gendb_entry::work::put(dst, k, src[p]);
        proof { lemma_merge_step(o, y, n as int, src@, d0, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int, left); }
        i = if left { i + 1 } else { i };
        j = if left { j } else { j + 1 };
        k = k + 1;
    }
    while i < mid
        invariant merge_inv(o, y, n as int, src@, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int),
            i == mid || j == hi,
        decreases mid - i,
    {
        let ghost d0 = dst@;
        crate::gendb_entry::work::put(dst, k, src[i]);
        proof { lemma_merge_step(o, y, n as int, src@, d0, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int, true); }
        i = i + 1;
        k = k + 1;
    }
    while j < hi
        invariant merge_inv(o, y, n as int, src@, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int),
            i == mid,
        decreases hi - j,
    {
        let ghost d0 = dst@;
        crate::gendb_entry::work::put(dst, k, src[j]);
        proof { lemma_merge_step(o, y, n as int, src@, d0, dst@, old(dst)@, lo as int, mid as int, hi as int, i as int, j as int, k as int, false); }
        j = j + 1;
        k = k + 1;
    }
}

/// Copies `src[lo .. hi]` into `dst[lo .. hi]` (other slots unchanged).
fn copy_seg(src: &Vec<u32>, lo: usize, hi: usize, dst: &mut Vec<u32>)
    requires lo <= hi <= src@.len(), old(dst)@.len() == src@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        seg(final(dst)@, lo as int, hi as int) == seg(src@, lo as int, hi as int),
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
    assert(seg(dst@, lo as int, hi as int) =~= seg(src@, lo as int, hi as int));
}

/// Sorts `v[lo .. hi]` by text, in place (scratch `tmp`; other slots unchanged).
pub fn msort(offs: &[u64], bytes: &[u8], n: usize, v: &mut Vec<u32>, tmp: &mut Vec<u32>, lo: usize, hi: usize)
    requires
        texts_ok(offs@, bytes@, n as int),
        lo <= hi <= old(v)@.len(), old(tmp)@.len() == old(v)@.len(),
        bounded(old(v)@, n as int), bounded(old(tmp)@, n as int),
    ensures
        final(v)@.len() == old(v)@.len(), final(tmp)@.len() == old(tmp)@.len(),
        bounded(final(v)@, n as int), bounded(final(tmp)@, n as int),
        sorted(offs@, bytes@, seg(final(v)@, lo as int, hi as int)),
        forall|x: int| 0 <= x < final(v)@.len() && !(lo <= x < hi) ==> #[trigger] final(v)@[x] == old(v)@[x],
    decreases hi - lo,
    no_unwind
{
    if hi - lo < 2 {
        return;
    }
    let mid = lo + (hi - lo) / 2;
    msort(offs, bytes, n, v, tmp, lo, mid);
    let ghost v1 = v@;
    msort(offs, bytes, n, v, tmp, mid, hi);
    let ghost v2 = v@;
    proof {
        assert(seg(v2, lo as int, mid as int) =~= seg(v1, lo as int, mid as int));
    }
    merge_into(offs, bytes, n, v, lo, mid, hi, tmp);
    let ghost t = tmp@;
    copy_seg(tmp, lo, hi, v);
    proof {
        assert forall|z: int| 0 <= z < v@.len() implies #[trigger] v@[z] < n by {
            if lo <= z < hi {
                assert(seg(v@, lo as int, hi as int)[z - lo] == seg(t, lo as int, hi as int)[z - lo]);
                assert(v@[z] == t[z]);
            }
        }
    }
}

/// `runs` cuts `s` into consecutive sorted runs: from 0 to `s.len()`, nondecreasing.
pub open spec fn runs_ok(o: Seq<u64>, y: Seq<u8>, s: Seq<u32>, runs: Seq<usize>) -> bool {
    &&& runs.len() >= 2
    &&& runs[0] == 0
    &&& runs[runs.len() - 1] == s.len()
    &&& forall|i: int| 0 <= i < runs.len() - 1 ==> #[trigger] runs[i] <= runs[i + 1]
    &&& forall|i: int| 0 <= i < runs.len() - 1 ==> sorted(o, y, #[trigger] seg(s, runs[i] as int, runs[i + 1] as int))
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

/// Run `i` of a cut: in bounds and sorted.
proof fn lemma_runs_at(o: Seq<u64>, y: Seq<u8>, s: Seq<u32>, runs: Seq<usize>, i: int)
    requires runs_ok(o, y, s, runs), 0 <= i < runs.len() - 1,
    ensures runs[i] <= runs[i + 1] <= s.len(), sorted(o, y, seg(s, runs[i] as int, runs[i + 1] as int)),
{
    lemma_runs_mono(runs, i + 1, runs.len() - 1);
}

/// The state of a merge pass after the input runs `0 .. i`: output runs `r` cover `dst[0 .. runs[i]]`, each sorted.
pub open spec fn pass_inv(o: Seq<u64>, y: Seq<u8>, n: int, src: Seq<u32>, runs: Seq<usize>, dst: Seq<u32>, r: Seq<usize>, i: int) -> bool {
    &&& 0 <= i < runs.len()
    &&& dst.len() == src.len()
    &&& bounded(dst, n)
    &&& r.len() >= 1 && r[0] == 0 && r[r.len() - 1] == runs[i]
    &&& forall|x: int| 0 <= x < r.len() - 1 ==> #[trigger] r[x] <= r[x + 1]
    &&& forall|x: int| 0 <= x < r.len() - 1 ==> sorted(o, y, #[trigger] seg(dst, r[x] as int, r[x + 1] as int))
}

/// One more output run `dst[lo .. hi]`, sorted (earlier slots unchanged).
proof fn lemma_pass_step(o: Seq<u64>, y: Seq<u8>, n: int, src: Seq<u32>, runs: Seq<usize>, d0: Seq<u32>, d1: Seq<u32>,
    r: Seq<usize>, i: int, i2: int)
    requires
        pass_inv(o, y, n, src, runs, d0, r, i), i < i2 < runs.len(),
        runs[i] <= runs[i2] <= src.len(),
        d1.len() == d0.len(),
        bounded(d1, n),
        forall|x: int| 0 <= x < runs[i] ==> #[trigger] d1[x] == d0[x],
        sorted(o, y, seg(d1, runs[i] as int, runs[i2] as int)),
    ensures pass_inv(o, y, n, src, runs, d1, r.push(runs[i2]), i2),
{
    let lo = runs[i] as int;
    let r2 = r.push(runs[i2]);
    assert forall|x: int| 0 <= x < r2.len() - 1 implies sorted(o, y, #[trigger] seg(d1, r2[x] as int, r2[x + 1] as int)) by {
        if x < r.len() - 1 {
            assert(r2[x] == r[x] && r2[x + 1] == r[x + 1]);
            lemma_runs_mono(r, x + 1, r.len() - 1);
            assert(seg(d1, r[x] as int, r[x + 1] as int) =~= seg(d0, r[x] as int, r[x + 1] as int));
        }
    }
    assert forall|x: int| 0 <= x < r2.len() - 1 implies #[trigger] r2[x] <= r2[x + 1] by {
        if x < r.len() - 1 {
            assert(r2[x] == r[x] && r2[x + 1] == r[x + 1]);
        }
    }
}

/// One pass: merges runs `2i, 2i + 1` of `src` into `dst` (an odd last run is copied); returns the new runs.
fn merge_pass(offs: &[u64], bytes: &[u8], n: usize, src: &Vec<u32>, runs: &Vec<usize>, dst: &mut Vec<u32>) -> (r: Vec<usize>)
    requires
        texts_ok(offs@, bytes@, n as int),
        runs_ok(offs@, bytes@, src@, runs@), old(dst)@.len() == src@.len(),
        bounded(src@, n as int), bounded(old(dst)@, n as int),
    ensures
        final(dst)@.len() == src@.len(),
        bounded(final(dst)@, n as int),
        runs_ok(offs@, bytes@, final(dst)@, r@),
        2 * (r@.len() - 1) <= runs@.len(),
{
    hide(sorted);
    hide(seg);
    let ghost (o, y) = (offs@, bytes@);
    let nr = runs.len() - 1;
    let mut r: Vec<usize> = Vec::new();
    r.push(0);
    let mut i: usize = 0;
    proof {
        assert(r@ =~= seq![0usize]);
    }
    while i < nr
        invariant
            texts_ok(o, y, n as int), o == offs@, y == bytes@,
            runs_ok(o, y, src@, runs@), nr == runs@.len() - 1, dst@.len() == src@.len(),
            bounded(src@, n as int),
            i <= nr,
            2 * (r@.len() - 1) == i || (i == nr && 2 * (r@.len() - 1) == i + 1),
            pass_inv(o, y, n as int, src@, runs@, dst@, r@, i as int),
        decreases nr - i,
    {
        proof { lemma_runs_at(o, y, src@, runs@, i as int); }
        let lo = runs[i];
        let ghost d0 = dst@;
        let ghost r0 = r@;
        if i + 1 < nr {
            proof { lemma_runs_at(o, y, src@, runs@, i as int + 1); }
            let mid = runs[i + 1];
            let hi = runs[i + 2];
            merge_into(offs, bytes, n, src, lo, mid, hi, dst);
            proof { lemma_pass_step(o, y, n as int, src@, runs@, d0, dst@, r0, i as int, i as int + 2); }
            r.push(hi);
            i = i + 2;
        } else {
            let hi = runs[i + 1];
            copy_seg(src, lo, hi, dst);
            proof {
                assert forall|z: int| 0 <= z < dst@.len() implies #[trigger] dst@[z] < n by {
                    if lo <= z < hi {
                        assert(dst@[z] == src@[z]);
                    }
                }
                lemma_pass_step(o, y, n as int, src@, runs@, d0, dst@, r0, i as int, i as int + 1);
            }
            r.push(hi);
            i = i + 1;
        }
    }
    proof {
        assert(r@.len() >= 2);
    }
    r
}

/// Merges the sorted runs of `v` (cut by `runs`) into one sorted vector of the same length.
pub fn merge_runs(offs: &[u64], bytes: &[u8], n: usize, v: Vec<u32>, runs: Vec<usize>) -> (r: Vec<u32>)
    requires
        texts_ok(offs@, bytes@, n as int),
        runs_ok(offs@, bytes@, v@, runs@),
        bounded(v@, n as int),
        n >= 1,
    ensures
        r@.len() == v@.len(),
        bounded(r@, n as int),
        sorted(offs@, bytes@, r@),
{
    let len = v.len();
    let mut src = v;
    let mut dst: Vec<u32> = vec![0u32; len];
    let mut runs = runs;
    proof {
        assert forall|z: int| 0 <= z < dst@.len() implies #[trigger] dst@[z] < n by {
            assert(dst@[z] == 0);
        }
    }
    while runs.len() > 2
        invariant
            texts_ok(offs@, bytes@, n as int), n >= 1,
            runs_ok(offs@, bytes@, src@, runs@), dst@.len() == src@.len(), src@.len() == len,
            bounded(src@, n as int), bounded(dst@, n as int),
        decreases runs@.len(),
    {
        let r2 = merge_pass(offs, bytes, n, &src, &runs, &mut dst);
        let t = src;
        src = dst;
        dst = t;
        runs = r2;
    }
    proof {
        assert(seg(src@, runs@[0] as int, runs@[1] as int) =~= src@);
    }
    src
}

} // verus!
