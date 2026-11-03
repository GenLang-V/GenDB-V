//! 64-bit masks of a range predicate over `i32` values and the iteration over their set bits. `range_mask`
//! returns the mask of `lo <= vals[base + p] < hi` for the 64 positions `p` (a loop free of branches that the
//! compiler vectorizes); `range_mask_part` does the same for fewer than 64 positions. A caller walks the set bits
//! in increasing order with `lowest_bit` (a branch-free binary search; `u64::trailing_zeros` is not `no_unwind`
//! in vstd) and `m & (m - 1)` (`lemma_clear_lowest`). Bit `b` of a word is `bitmap::wbit`.
use vstd::prelude::*;
use crate::agent::common::bitmap::wbit;

verus! {

/// OR-ing in `x << b` (`x` a single bit) sets bit `b` when `x` is 1 and keeps every other bit.
pub proof fn lemma_or_bit(w: u64, x: u64, b: u64)
    requires b < 64, x <= 1,
    ensures
        wbit(w | (x << b), b as int) == (x == 1 || wbit(w, b as int)),
        forall|c: u64| c < 64 && c != b ==> wbit(w | (x << b), c as int) == #[trigger] wbit(w, c as int),
{
    assert((((w | (x << b)) >> b) & 1u64 == 1u64) == (x == 1u64 || (w >> b) & 1u64 == 1u64)) by (bit_vector)
        requires b < 64, x <= 1;
    assert forall|c: u64| c < 64 && c != b implies wbit(w | (x << b), c as int) == #[trigger] wbit(w, c as int) by {
        assert((((w | (x << b)) >> c) & 1u64 == 1u64) == ((w >> c) & 1u64 == 1u64)) by (bit_vector)
            requires b < 64, c < 64, c != b, x <= 1;
    }
}

/// The zero word has no bit set.
pub proof fn lemma_zero_bits()
    ensures forall|c: u64| c < 64 ==> !#[trigger] wbit(0u64, c as int),
{
    assert forall|c: u64| c < 64 implies !#[trigger] wbit(0u64, c as int) by {
        assert((0u64 >> c) & 1u64 == 0u64) by (bit_vector) requires c < 64;
    }
}

/// The position `p` of the lowest set bit of a non-zero `m` (bit `p` set, every bit below clear: `m << (64 - p)`
/// is zero), by a binary search without branches (six halving steps).
pub fn lowest_bit(m: u64) -> (p: u64)
    requires m != 0,
    ensures p < 64, wbit(m, p as int), m << sub(64u64, p) == 0u64,
    no_unwind
{
    let z1: bool = m & 0xFFFF_FFFFu64 == 0;
    let n1: u64 = if z1 { 32 } else { 0 };
    assert(m << sub(64u64, n1) == 0u64 && (m >> n1) & 0xFFFF_FFFFu64 != 0u64) by (bit_vector)
        requires m != 0u64, z1 == (m & 0xFFFF_FFFFu64 == 0u64), n1 == (if z1 { 32u64 } else { 0u64 });
    let z2: bool = (m >> n1) & 0xFFFFu64 == 0;
    let n2: u64 = n1 + if z2 { 16u64 } else { 0u64 };
    assert(m << sub(64u64, n2) == 0u64 && (m >> n2) & 0xFFFFu64 != 0u64) by (bit_vector)
        requires n1 <= 32, m << sub(64u64, n1) == 0u64, (m >> n1) & 0xFFFF_FFFFu64 != 0u64,
            z2 == ((m >> n1) & 0xFFFFu64 == 0u64), n2 == add(n1, if z2 { 16u64 } else { 0u64 });
    let z3: bool = (m >> n2) & 0xFFu64 == 0;
    let n3: u64 = n2 + if z3 { 8u64 } else { 0u64 };
    assert(m << sub(64u64, n3) == 0u64 && (m >> n3) & 0xFFu64 != 0u64) by (bit_vector)
        requires n2 <= 48, m << sub(64u64, n2) == 0u64, (m >> n2) & 0xFFFFu64 != 0u64,
            z3 == ((m >> n2) & 0xFFu64 == 0u64), n3 == add(n2, if z3 { 8u64 } else { 0u64 });
    let z4: bool = (m >> n3) & 0xFu64 == 0;
    let n4: u64 = n3 + if z4 { 4u64 } else { 0u64 };
    assert(m << sub(64u64, n4) == 0u64 && (m >> n4) & 0xFu64 != 0u64) by (bit_vector)
        requires n3 <= 56, m << sub(64u64, n3) == 0u64, (m >> n3) & 0xFFu64 != 0u64,
            z4 == ((m >> n3) & 0xFu64 == 0u64), n4 == add(n3, if z4 { 4u64 } else { 0u64 });
    let z5: bool = (m >> n4) & 0x3u64 == 0;
    let n5: u64 = n4 + if z5 { 2u64 } else { 0u64 };
    assert(m << sub(64u64, n5) == 0u64 && (m >> n5) & 0x3u64 != 0u64) by (bit_vector)
        requires n4 <= 60, m << sub(64u64, n4) == 0u64, (m >> n4) & 0xFu64 != 0u64,
            z5 == ((m >> n4) & 0x3u64 == 0u64), n5 == add(n4, if z5 { 2u64 } else { 0u64 });
    let z6: bool = (m >> n5) & 0x1u64 == 0;
    let n6: u64 = n5 + if z6 { 1u64 } else { 0u64 };
    assert(m << sub(64u64, n6) == 0u64 && (m >> n6) & 0x1u64 == 1u64) by (bit_vector)
        requires n5 <= 62, m << sub(64u64, n5) == 0u64, (m >> n5) & 0x3u64 != 0u64,
            z6 == ((m >> n5) & 0x1u64 == 0u64), n6 == add(n5, if z6 { 1u64 } else { 0u64 });
    n6
}

/// For a non-zero `m` whose lowest set bit is `p` (bit `p` set, `m << (64 - p) == 0`): no bit below `p` is set, and
/// `m & (m - 1)` clears exactly bit `p`, a smaller word.
pub proof fn lemma_clear_lowest(m: u64, p: u64)
    requires m != 0, p < 64, wbit(m, p as int), m << sub(64u64, p) == 0u64,
    ensures
        forall|c: u64| c < p ==> !#[trigger] wbit(m, c as int),
        forall|c: u64| c < 64 ==> #[trigger] wbit(m & sub(m, 1u64), c as int) == (c != p && wbit(m, c as int)),
        m & sub(m, 1u64) < m,
{
    assert forall|c: u64| c < p implies !#[trigger] wbit(m, c as int) by {
        assert((m >> c) & 1u64 == 0u64) by (bit_vector) requires c < p, p < 64, m << sub(64u64, p) == 0u64;
    }
    assert forall|c: u64| c < 64 implies #[trigger] wbit(m & sub(m, 1u64), c as int) == (c != p && wbit(m, c as int)) by {
        assert((((m & sub(m, 1u64)) >> c) & 1u64 == 1u64) == (c != p && (m >> c) & 1u64 == 1u64)) by (bit_vector)
            requires m != 0u64, p < 64, c < 64, (m >> p) & 1u64 == 1u64, m << sub(64u64, p) == 0u64;
    }
    assert(m & sub(m, 1u64) < m) by (bit_vector) requires m != 0u64;
}

/// The mask of the 64 values `vals[base..base + 64)` that lie in `[lo, hi)`.
pub fn range_mask(vals: &[i32], base: usize, lo: i32, hi: i32) -> (m: u64)
    requires base + 64 <= vals@.len(), base + 64 <= usize::MAX,
    ensures forall|p: int| 0 <= p < 64 ==> #[trigger] wbit(m, p) == (lo <= vals@[base + p] < hi),
    no_unwind
{
    let mut m: u64 = 0;
    let mut p: usize = 0;
    proof { lemma_zero_bits(); }
    while p < 64
        invariant
            p <= 64, base + 64 <= vals@.len(), base + 64 <= usize::MAX,
            forall|c: u64| c < p ==> #[trigger] wbit(m, c as int) == (lo <= vals@[base + c] < hi),
            forall|c: u64| p <= c < 64 ==> !#[trigger] wbit(m, c as int),
        decreases 64 - p,
    {
        let v = vals[base + p];
        let x: u64 = if lo <= v && v < hi { 1u64 } else { 0u64 };
        let ghost m0 = m;
        m = m | (x << (p as u64));
        proof {
            lemma_or_bit(m0, x, p as u64);
            assert forall|c: u64| c < p + 1 implies #[trigger] wbit(m, c as int) == (lo <= vals@[base + c] < hi) by {
                if c < p as u64 { assert(wbit(m0, c as int) == (lo <= vals@[base + c] < hi)); } else { assert(!wbit(m0, c as int)); }
            }
            assert forall|c: u64| p + 1 <= c < 64 implies !#[trigger] wbit(m, c as int) by {
                assert(!wbit(m0, c as int));
            }
        }
        p = p + 1;
    }
    proof {
        assert forall|q: int| 0 <= q < 64 implies #[trigger] wbit(m, q) == (lo <= vals@[base + q] < hi) by {
            assert(wbit(m, (q as u64) as int) == (lo <= vals@[base + (q as u64)] < hi));
        }
    }
    m
}

/// The mask of the `cnt <= 64` values `vals[base..base + cnt)` that lie in `[lo, hi)` (higher bits clear).
pub fn range_mask_part(vals: &[i32], base: usize, cnt: usize, lo: i32, hi: i32) -> (m: u64)
    requires cnt <= 64, base + cnt <= vals@.len(), base + cnt <= usize::MAX,
    ensures forall|p: int| 0 <= p < 64 ==> #[trigger] wbit(m, p) == (p < cnt && lo <= vals@[base + p] < hi),
    no_unwind
{
    let mut m: u64 = 0;
    let mut p: usize = 0;
    proof { lemma_zero_bits(); }
    while p < cnt
        invariant
            p <= cnt <= 64, base + cnt <= vals@.len(), base + cnt <= usize::MAX,
            forall|c: u64| c < p ==> #[trigger] wbit(m, c as int) == (lo <= vals@[base + c] < hi),
            forall|c: u64| p <= c < 64 ==> !#[trigger] wbit(m, c as int),
        decreases cnt - p,
    {
        let v = vals[base + p];
        let x: u64 = if lo <= v && v < hi { 1u64 } else { 0u64 };
        let ghost m0 = m;
        m = m | (x << (p as u64));
        proof {
            lemma_or_bit(m0, x, p as u64);
            assert forall|c: u64| c < p + 1 implies #[trigger] wbit(m, c as int) == (lo <= vals@[base + c] < hi) by {
                if c < p as u64 { assert(wbit(m0, c as int) == (lo <= vals@[base + c] < hi)); } else { assert(!wbit(m0, c as int)); }
            }
            assert forall|c: u64| p + 1 <= c < 64 implies !#[trigger] wbit(m, c as int) by {
                assert(!wbit(m0, c as int));
            }
        }
        p = p + 1;
    }
    proof {
        assert forall|q: int| 0 <= q < 64 implies #[trigger] wbit(m, q) == (q < cnt && lo <= vals@[base + q] < hi) by {
            if q < cnt {
                assert(wbit(m, (q as u64) as int) == (lo <= vals@[base + (q as u64)] < hi));
            } else {
                assert(!wbit(m, (q as u64) as int));
            }
        }
    }
    m
}

} // verus!
