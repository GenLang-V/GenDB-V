//! The chunk masks of storage `li_pairmask`: bit `r * 8 + l` of a chunk's mask is set for every (l_returnflag,
//! l_linestatus) code pair `(r, l)` of the chunk's rows (`marked`). `decode_mask` reads a mask with one bit, or two
//! bits that differ in one code, as the chunk's code box `r0 ..= r1`, `l0 ..= l1` with every row's codes at the box's
//! corners, so the scan needs neither code column (one pair) or only the one that differs (two pairs).
use vstd::prelude::*;
use crate::stores::li_pairmask::interface as LP;

verus! {

/// The pair `(r, l)`'s bit is set in mask `mk` (both codes below 8).
pub open spec fn marked(mk: u64, r: u8, l: u8) -> bool {
    r < 8 && l < 8 && LP::pair_bit(mk, (r * 8 + l) as u64)
}

/// The bit index of a pair splits back into its codes.
proof fn lemma_bit_codes(x: u64, r: u64, l: u64)
    requires r < 8, l < 8, x == r * 8 + l,
    ensures x >> 3u64 == r, x & 7u64 == l,
{
    assert(x >> 3u64 == r && x & 7u64 == l) by (bit_vector)
        requires r < 8u64, l < 8u64, x == r * 8u64 + l;
}

/// A mask equal to the single bit `b`: every set bit is `b`.
proof fn lemma_one_bit(mk: u64, b: u64, x: u64)
    requires b < 64, x < 64, mk ^ (1u64 << b) == 0, (mk >> x) & 1u64 == 1u64,
    ensures x == b,
{
    assert(x == b) by (bit_vector)
        requires b < 64u64, x < 64u64, mk ^ (1u64 << b) == 0u64, (mk >> x) & 1u64 == 1u64;
}

/// A mask equal to the bits `b1` and `b2`: every set bit is one of them.
proof fn lemma_two_bits(mk: u64, b1: u64, b2: u64, x: u64)
    requires b1 < 64, b2 < 64, x < 64, (mk ^ (1u64 << b1)) ^ (1u64 << b2) == 0, (mk >> x) & 1u64 == 1u64,
    ensures x == b1 || x == b2,
{
    assert(x == b1 || x == b2) by (bit_vector)
        requires b1 < 64u64, b2 < 64u64, x < 64u64, (mk ^ (1u64 << b1)) ^ (1u64 << b2) == 0u64, (mk >> x) & 1u64 == 1u64;
}

/// A marked pair is the pair of bit `x` when `x` is its bit.
proof fn lemma_marked_codes(mk: u64, r: u8, l: u8, x: u64)
    requires marked(mk, r, l), x == r * 8 + l,
    ensures r == (x >> 3u64) as u8, l == (x & 7u64) as u8, x < 64, (mk >> x) & 1u64 == 1u64,
{
    lemma_bit_codes(x, r as u64, l as u64);
}

/// The index of the lowest set bit of a non-zero `x` (a binary search over the isolated bit). Only performance
/// depends on it being that bit: `decode_mask` checks the mask against the bits it names.
fn low_bit(x: u64) -> (b: u64)
    ensures b < 64,
    no_unwind
{
    if x == 0 {
        return 0;
    }
    assert(!x <= 0xffff_ffff_ffff_fffeu64) by (bit_vector) requires x != 0u64;
    let mut v = x & (!x + 1);
    let mut b: u64 = 0;
    if v >= 0x1_0000_0000 {
        v = v >> 32u64;
        b = b + 32;
    }
    if v >= 0x1_0000 {
        v = v >> 16u64;
        b = b + 16;
    }
    if v >= 0x100 {
        v = v >> 8u64;
        b = b + 8;
    }
    if v >= 0x10 {
        v = v >> 4u64;
        b = b + 4;
    }
    if v >= 0x4 {
        v = v >> 2u64;
        b = b + 2;
    }
    if v >= 0x2 {
        b = b + 1;
    }
    b
}

/// The code box of a mask with one bit, or two bits differing in one code: `(true, r0, r1, l0, l1)` with every
/// marked pair at a corner of the box and the box a line (`r0 == r1` or `l0 == l1`); otherwise `false`.
pub fn decode_mask(mk: u64) -> (d: (bool, u8, u8, u8, u8))
    ensures
        d.0 ==> d.1 <= d.2 && d.3 <= d.4 && (d.1 == d.2 || d.3 == d.4),
        d.0 ==> forall|r: u8, l: u8| #[trigger] marked(mk, r, l) ==> (r == d.1 || r == d.2) && (l == d.3 || l == d.4),
    no_unwind
{
    if mk == 0 {
        return (false, 0, 0, 0, 0);
    }
    let b1 = low_bit(mk);
    let rest = mk ^ (1u64 << b1);
    let ra = (b1 >> 3u64) as u8;
    let la = (b1 & 7u64) as u8;
    if rest == 0 {
        proof {
            assert forall|r: u8, l: u8| #[trigger] marked(mk, r, l) implies r == ra && l == la by {
                let x = (r * 8 + l) as u64;
                lemma_marked_codes(mk, r, l, x);
                lemma_one_bit(mk, b1, x);
            }
        }
        return (true, ra, ra, la, la);
    }
    let b2 = low_bit(rest);
    if (rest ^ (1u64 << b2)) != 0 {
        return (false, 0, 0, 0, 0);
    }
    let rb = (b2 >> 3u64) as u8;
    let lb = (b2 & 7u64) as u8;
    proof {
        assert forall|r: u8, l: u8| #[trigger] marked(mk, r, l) implies (r == ra && l == la) || (r == rb && l == lb) by {
            let x = (r * 8 + l) as u64;
            lemma_marked_codes(mk, r, l, x);
            lemma_two_bits(mk, b1, b2, x);
        }
    }
    if la == lb {
        if ra <= rb { (true, ra, rb, la, la) } else { (true, rb, ra, la, la) }
    } else if ra == rb {
        if la <= lb { (true, ra, ra, la, lb) } else { (true, ra, ra, lb, la) }
    } else {
        (false, 0, 0, 0, 0)
    }
}

} // verus!
