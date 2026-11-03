//! Code translation between two sorted dictionaries (strictly increasing text lists A and B, U64 offsets + U8
//! bytes): for each code `i` of A, the code of the same value in B, or `NONE` when B lacks it. Computed for a range
//! of A's codes by one merge, starting from the binary-searched first B entry not below A's first value, so ranges
//! can run in parallel. `no_unwind`; the output is written into a preallocated buffer.
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::order::lemma_lex_cmp_antisym;
use crate::agent::common::bytecmp::{fast_cmp, same_bytes};
use crate::stores::num::interface::common::text::{text_entry, text_parts_wf, text_strictly_sorted, text_entry_of,
    lemma_lex_cmp_lt_trans};

verus! {

/// Marks an absent code.
pub const NONE: u64 = 0xffff_ffff_ffff_ffff;

/// `m` is the translation of A's code `i` into B.
pub open spec fn dmap_ok(aoff: Seq<u64>, abytes: Seq<u8>, boff: Seq<u64>, bbytes: Seq<u8>, bn: int, i: int, m: u64) -> bool {
    if m == NONE {
        forall|j: int| 0 <= j < bn ==> #[trigger] text_entry(boff, bbytes, j) != text_entry(aoff, abytes, i)
    } else {
        m < bn && text_entry(boff, bbytes, m as int) == text_entry(aoff, abytes, i)
    }
}

/// Whether A's entries `[i0, i1)` are byte-identical to B's entries `[i0, i1)` (same offsets, same bytes): the
/// common case of two dictionaries built from the same values, checked without comparing entry by entry.
fn same_range(aoff: &[u64], abytes: &[u8], an: usize, boff: &[u64], bbytes: &[u8], bn: usize, i0: usize, i1: usize) -> (r: bool)
    requires text_parts_wf(aoff@, abytes@, an as int), text_parts_wf(boff@, bbytes@, bn as int), i0 < i1 <= an,
    ensures r ==> i1 <= bn && forall|k: int| i0 <= k < i1 ==> #[trigger] text_entry(boff@, bbytes@, k) == text_entry(aoff@, abytes@, k),
    no_unwind
{
    if i1 > bn {
        return false;
    }
    let mut k = i0;
    while k <= i1
        invariant
            i0 <= k <= i1 + 1, i1 <= an, i1 <= bn, aoff@.len() == an + 1, boff@.len() == bn + 1,
            forall|x: int| i0 <= x < k ==> #[trigger] aoff@[x] == boff@[x],
        decreases i1 + 1 - k,
    {
        if aoff[k] != boff[k] {
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(aoff@[i0 as int] <= aoff@[i1 as int] && aoff@[i1 as int] <= aoff@[an as int]);
    }
    assert(aoff@[i1 as int] <= abytes.len());
    let x0 = aoff[i0] as usize;
    let x1 = aoff[i1] as usize;
    proof {
        assert(aoff@[i1 as int] == boff@[i1 as int]);
        assert(boff@[i1 as int] <= boff@[bn as int]);
    }
    if !same_bytes(abytes, bbytes, x0, x1) {
        return false;
    }
    proof {
        assert forall|k: int| i0 <= k < i1 implies #[trigger] text_entry(boff@, bbytes@, k) == text_entry(aoff@, abytes@, k) by {
            assert(aoff@[k] == boff@[k] && aoff@[k + 1] == boff@[k + 1]);
            assert(aoff@[i0 as int] <= aoff@[k] && aoff@[k] <= aoff@[k + 1] && aoff@[k + 1] <= aoff@[i1 as int]);
            assert(text_entry(boff@, bbytes@, k) =~= text_entry(aoff@, abytes@, k));
        }
    }
    true
}

/// First position of B whose value is not below `key`.
fn lower_text(boff: &[u64], bbytes: &[u8], bn: usize, key: &[u8], kn: usize) -> (r: usize)
    requires
        text_parts_wf(boff@, bbytes@, bn as int), text_strictly_sorted(boff@, bbytes@, bn as int), kn == key@.len(),
    ensures
        r <= bn,
        forall|j: int| 0 <= j < r ==> lex_cmp(#[trigger] text_entry(boff@, bbytes@, j), key@) < 0,
        forall|j: int| r <= j < bn ==> lex_cmp(#[trigger] text_entry(boff@, bbytes@, j), key@) >= 0,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = bn;
    while lo < hi
        invariant
            lo <= hi <= bn,
            text_parts_wf(boff@, bbytes@, bn as int), text_strictly_sorted(boff@, bbytes@, bn as int), kn == key@.len(),
            forall|j: int| 0 <= j < lo ==> lex_cmp(#[trigger] text_entry(boff@, bbytes@, j), key@) < 0,
            forall|j: int| hi <= j < bn ==> lex_cmp(#[trigger] text_entry(boff@, bbytes@, j), key@) >= 0,
        decreases hi - lo,
    {
        let m = lo + (hi - lo) / 2;
        let (y, yn) = text_entry_of(boff, bbytes, bn, m);
        let c = fast_cmp(y, yn, key, kn);
        if c < 0 {
            proof {
                assert forall|j: int| 0 <= j <= m implies lex_cmp(#[trigger] text_entry(boff@, bbytes@, j), key@) < 0 by {
                    if j < m {
                        lemma_lex_cmp_lt_trans(text_entry(boff@, bbytes@, j), text_entry(boff@, bbytes@, m as int), key@);
                    }
                }
            }
            lo = m + 1;
        } else {
            proof {
                assert forall|j: int| m <= j < bn implies lex_cmp(#[trigger] text_entry(boff@, bbytes@, j), key@) >= 0 by {
                    if j > m {
                        let (e, f) = (text_entry(boff@, bbytes@, m as int), text_entry(boff@, bbytes@, j));
                        // key <= e < f
                        lemma_lex_cmp_antisym(e, key@);
                        lemma_lex_cmp_antisym(f, key@);
                        lemma_lex_cmp_zero(e, key@);
                        if lex_cmp(e, key@) == 0 {
                            assert(e == key@);
                        } else {
                            lemma_lex_cmp_lt_trans(key@, e, f);
                        }
                    }
                }
            }
            hi = m;
        }
    }
    lo
}

/// The translation of A's codes `[i0, i1)` into B, written to `out[i - i0]`.
pub fn dict_map_range(aoff: &[u64], abytes: &[u8], an: usize, boff: &[u64], bbytes: &[u8], bn: usize,
    i0: usize, i1: usize, out: &mut Vec<u64>)
    requires
        text_parts_wf(aoff@, abytes@, an as int), text_strictly_sorted(aoff@, abytes@, an as int),
        text_parts_wf(boff@, bbytes@, bn as int), text_strictly_sorted(boff@, bbytes@, bn as int),
        i0 <= i1 <= an, old(out)@.len() == i1 - i0,
    ensures
        final(out)@.len() == i1 - i0,
        forall|i: int| i0 <= i < i1 ==> dmap_ok(aoff@, abytes@, boff@, bbytes@, bn as int, i, #[trigger] final(out)@[i - i0]),
    no_unwind
{
    if i0 >= i1 {
        return;
    }
    if same_range(aoff, abytes, an, boff, bbytes, bn, i0, i1) {
        // Identical entries: the translation is the identity on this range.
        let mut i = i0;
        while i < i1
            invariant
                i0 <= i <= i1 <= an, i1 <= bn, out@.len() == i1 - i0, text_parts_wf(aoff@, abytes@, an as int),
                forall|k: int| i0 <= k < i1 ==> #[trigger] text_entry(boff@, bbytes@, k) == text_entry(aoff@, abytes@, k),
                forall|k: int| i0 <= k < i ==> dmap_ok(aoff@, abytes@, boff@, bbytes@, bn as int, k, #[trigger] out@[k - i0]),
            decreases i1 - i,
        {
            out[i - i0] = i as u64;
            i = i + 1;
        }
        return;
    }
    let (x0, x0n) = text_entry_of(aoff, abytes, an, i0);
    let mut j = lower_text(boff, bbytes, bn, x0, x0n);
    let mut i = i0;
    while i < i1
        invariant
            i0 <= i <= i1 <= an, j <= bn,
            text_parts_wf(aoff@, abytes@, an as int), text_strictly_sorted(aoff@, abytes@, an as int),
            text_parts_wf(boff@, bbytes@, bn as int), text_strictly_sorted(boff@, bbytes@, bn as int),
            out@.len() == i1 - i0,
            i < i1 ==> forall|k: int| 0 <= k < j ==> lex_cmp(#[trigger] text_entry(boff@, bbytes@, k), text_entry(aoff@, abytes@, i as int)) < 0,
            forall|k: int| i0 <= k < i ==> dmap_ok(aoff@, abytes@, boff@, bbytes@, bn as int, k, #[trigger] out@[k - i0]),
        decreases (i1 - i) + (bn - j),
    {
        let ghost ai = text_entry(aoff@, abytes@, i as int);
        if j >= bn {
            proof {
                assert forall|k: int| 0 <= k < bn implies #[trigger] text_entry(boff@, bbytes@, k) != ai by {
                    lemma_lex_cmp_zero(text_entry(boff@, bbytes@, k), ai);
                }
                lemma_next_above(aoff@, abytes@, an as int, boff@, bbytes@, j as int, i as int, i1 as int);
            }
            out[i - i0] = NONE;
            i = i + 1;
        } else {
            let (x, xn) = text_entry_of(aoff, abytes, an, i);
            let (y, yn) = text_entry_of(boff, bbytes, bn, j);
            let c = fast_cmp(x, xn, y, yn);
            if c < 0 {
                proof {
                    // ai < B[j] <= B[k] for k >= j; B[k] < ai for k < j.
                    assert forall|k: int| 0 <= k < bn implies #[trigger] text_entry(boff@, bbytes@, k) != ai by {
                        let bk = text_entry(boff@, bbytes@, k);
                        if k < j {
                            lemma_lex_cmp_zero(bk, ai);
                        } else if k > j {
                            lemma_lex_cmp_lt_trans(ai, text_entry(boff@, bbytes@, j as int), bk);
                            lemma_lex_cmp_zero(ai, bk);
                        } else {
                            lemma_lex_cmp_zero(ai, bk);
                        }
                    }
                    lemma_next_above(aoff@, abytes@, an as int, boff@, bbytes@, j as int, i as int, i1 as int);
                }
                out[i - i0] = NONE;
                i = i + 1;
            } else if c > 0 {
                proof {
                    lemma_lex_cmp_antisym(ai, text_entry(boff@, bbytes@, j as int));
                }
                j = j + 1;
            } else {
                proof {
                    lemma_lex_cmp_zero(ai, text_entry(boff@, bbytes@, j as int));
                    // B[k] < A[i] < A[i + 1] for k <= j.
                    if i + 1 < i1 {
                        let an1 = text_entry(aoff@, abytes@, i + 1);
                        assert(lex_cmp(ai, an1) < 0);
                        assert forall|k: int| 0 <= k < j + 1 implies lex_cmp(#[trigger] text_entry(boff@, bbytes@, k), an1) < 0 by {
                            if k < j {
                                lemma_lex_cmp_lt_trans(text_entry(boff@, bbytes@, k), ai, an1);
                            }
                        }
                    }
                }
                out[i - i0] = j as u64;
                i = i + 1;
                j = j + 1;
            }
        }
    }
}

/// When B's first `j` values are below A[i], they are below A[i + 1] too.
proof fn lemma_next_above(aoff: Seq<u64>, abytes: Seq<u8>, an: int, boff: Seq<u64>, bbytes: Seq<u8>, j: int, i: int, i1: int)
    requires
        text_strictly_sorted(aoff, abytes, an), i1 <= an, 0 <= i < i1,
        forall|k: int| 0 <= k < j ==> lex_cmp(#[trigger] text_entry(boff, bbytes, k), text_entry(aoff, abytes, i)) < 0,
    ensures
        i + 1 < i1 ==> forall|k: int| 0 <= k < j ==> lex_cmp(#[trigger] text_entry(boff, bbytes, k), text_entry(aoff, abytes, i + 1)) < 0,
{
    if i + 1 < i1 {
        assert forall|k: int| 0 <= k < j implies lex_cmp(#[trigger] text_entry(boff, bbytes, k), text_entry(aoff, abytes, i + 1)) < 0 by {
            lemma_lex_cmp_lt_trans(text_entry(boff, bbytes, k), text_entry(aoff, abytes, i), text_entry(aoff, abytes, i + 1));
        }
    }
}

/// Every value below position `mid + 1` sorts before `key`, when value `mid` does.
proof fn lemma_find_below(off: Seq<u64>, bytes: Seq<u8>, count: int, key: Seq<u8>, mid: int)
    requires text_strictly_sorted(off, bytes, count), 0 <= mid < count, lex_cmp(text_entry(off, bytes, mid), key) < 0,
    ensures forall|k: int| 0 <= k <= mid ==> lex_cmp(#[trigger] text_entry(off, bytes, k), key) < 0,
{
    assert forall|k: int| 0 <= k <= mid implies lex_cmp(#[trigger] text_entry(off, bytes, k), key) < 0 by {
        if k < mid {
            lemma_lex_cmp_lt_trans(text_entry(off, bytes, k), text_entry(off, bytes, mid), key);
        }
    }
}

/// Every value from position `mid` on sorts after `key`, when value `mid` does.
proof fn lemma_find_above(off: Seq<u64>, bytes: Seq<u8>, count: int, key: Seq<u8>, mid: int)
    requires text_strictly_sorted(off, bytes, count), 0 <= mid < count, lex_cmp(text_entry(off, bytes, mid), key) > 0,
    ensures forall|k: int| mid <= k < count ==> lex_cmp(#[trigger] text_entry(off, bytes, k), key) > 0,
{
    assert forall|k: int| mid <= k < count implies lex_cmp(#[trigger] text_entry(off, bytes, k), key) > 0 by {
        if k > mid {
            let (e, f) = (text_entry(off, bytes, mid), text_entry(off, bytes, k));
            lemma_lex_cmp_antisym(e, f);
            lemma_lex_cmp_antisym(key, e);
            lemma_lex_cmp_antisym(key, f);
            lemma_lex_cmp_lt_trans(key, e, f);
        }
    }
}

/// Binary search of `key` in a sorted dictionary (word-at-a-time compares): `Some(k)` exactly when value `k` is
/// `key`.
pub fn find_text_fast(off: &[u64], bytes: &[u8], count: usize, key: &[u8], key_len: usize) -> (r: Option<usize>)
    requires
        text_parts_wf(off@, bytes@, count as int), text_strictly_sorted(off@, bytes@, count as int), key_len == key@.len(),
    ensures
        r matches Some(k) ==> k < count && text_entry(off@, bytes@, k as int) == key@,
        r is None ==> forall|k: int| 0 <= k < count ==> text_entry(off@, bytes@, k) != key@,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = count;
    while lo < hi
        invariant
            lo <= hi <= count,
            text_parts_wf(off@, bytes@, count as int), text_strictly_sorted(off@, bytes@, count as int), key_len == key@.len(),
            forall|k: int| 0 <= k < lo ==> lex_cmp(#[trigger] text_entry(off@, bytes@, k), key@) < 0,
            forall|k: int| hi <= k < count ==> lex_cmp(#[trigger] text_entry(off@, bytes@, k), key@) > 0,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let (e, en) = text_entry_of(off, bytes, count, mid);
        let c = fast_cmp(e, en, key, key_len);
        if c == 0 {
            proof { lemma_lex_cmp_zero(e@, key@); }
            return Some(mid);
        } else if c < 0 {
            proof { lemma_find_below(off@, bytes@, count as int, key@, mid as int); }
            lo = mid + 1;
        } else {
            proof { lemma_find_above(off@, bytes@, count as int, key@, mid as int); }
            hi = mid;
        }
    }
    proof {
        assert forall|k: int| 0 <= k < count implies text_entry(off@, bytes@, k) != key@ by {
            lemma_lex_cmp_zero(text_entry(off@, bytes@, k), key@);
        }
    }
    None
}

/// `key`'s position in a sorted dictionary, trying the hint `h` and `h - 1` first (for a dictionary that nearly
/// coincides with another sorted list of the same values at rank `h`), else a binary search.
pub fn find_text_hint(off: &[u64], bytes: &[u8], count: usize, key: &[u8], key_len: usize, h: usize) -> (r: Option<usize>)
    requires
        text_parts_wf(off@, bytes@, count as int), text_strictly_sorted(off@, bytes@, count as int), key_len == key@.len(),
    ensures
        r matches Some(k) ==> k < count && text_entry(off@, bytes@, k as int) == key@,
        r is None ==> forall|k: int| 0 <= k < count ==> text_entry(off@, bytes@, k) != key@,
    no_unwind
{
    if h < count {
        let (e, en) = text_entry_of(off, bytes, count, h);
        if fast_cmp(e, en, key, key_len) == 0 {
            proof { lemma_lex_cmp_zero(e@, key@); }
            return Some(h);
        }
    }
    if h >= 1 && h - 1 < count {
        let (e, en) = text_entry_of(off, bytes, count, h - 1);
        if fast_cmp(e, en, key, key_len) == 0 {
            proof { lemma_lex_cmp_zero(e@, key@); }
            return Some(h - 1);
        }
    }
    find_text_fast(off, bytes, count, key, key_len)
}

} // verus!
