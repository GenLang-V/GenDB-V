//! Bit-level facts about 64-bit masks (one bit per row of a 64-row block; from an admitted query's `common::bits`):
//! setting a bit, clearing the lowest set bit, the first set bit (`trailing_zeros`, and `low_index`, which computes it
//! without a call that may unwind, for worker bodies), prefix XOR, and the number of set bits below a position.
//! Each fact is one small `bit_vector` lemma, stated for a single bit position.
use vstd::prelude::*;
use vstd::std_specs::bits::{u64_trailing_zeros, axiom_u64_trailing_zeros};

verus! {

/// Bit `u` of `m` (positions `0..64`).
pub open spec fn bit(m: u64, u: u64) -> bool { (m >> u) & 1u64 == 1u64 }

/// Number of set bits of `m` at positions `0..n`.
pub open spec fn count_below(m: u64, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { count_below(m, n - 1) + if n <= 64 && bit(m, (n - 1) as u64) { 1int } else { 0int } }
}

/// `m` with bit `t` set to `x` (`m` has bit `t` clear).
pub proof fn lemma_bit_set(m: u64, x: u64, t: u64, u: u64)
    requires t < 64, u < 64, x <= 1, !bit(m, t),
    ensures bit(m | (x << t), u) == if u == t { x == 1 } else { bit(m, u) },
{
    assert(((m >> t) & 1u64 != 1u64 && t < 64 && u < 64 && x <= 1) ==>
        ((((m | (x << t)) >> u) & 1u64 == 1u64) == if u == t { x == 1 } else { (m >> u) & 1u64 == 1u64 })) by (bit_vector);
}

/// The empty mask.
pub proof fn lemma_bit_zero(u: u64)
    ensures !bit(0, u),
{
    assert((0u64 >> u) & 1u64 != 1u64) by (bit_vector);
}

/// Bits of a conjunction.
pub proof fn lemma_bit_and(a: u64, b: u64, u: u64)
    ensures bit(a & b, u) == (bit(a, u) && bit(b, u)),
{
    assert((((a & b) >> u) & 1u64 == 1u64) == (((a >> u) & 1u64 == 1u64) && ((b >> u) & 1u64 == 1u64))) by (bit_vector);
}

/// XOR with all ones (`d == 1`) or none (`d == 0`) flips every bit or none.
pub proof fn lemma_bit_flip(p: u64, d: u64, u: u64)
    requires d <= 1, u < 64,
    ensures bit(p ^ (0u64.wrapping_sub(d)), u) == (bit(p, u) != (d == 1)),
{
    assert(0u64.wrapping_sub(d) == if d == 1 { 0xffff_ffff_ffff_ffffu64 } else { 0u64 }) by {
        assert(0u64.wrapping_sub(0) == 0u64);
    }
    assert((d <= 1 && u < 64) ==> ((((p ^ (if d == 1 { 0xffff_ffff_ffff_ffffu64 } else { 0u64 })) >> u) & 1u64 == 1u64)
        == (((p >> u) & 1u64 == 1u64) != (d == 1)))) by (bit_vector);
}

/// The first set bit of a non-zero mask: set, and every bit below it clear.
pub proof fn lemma_first_bit(c: u64)
    requires c != 0,
    ensures
        c.trailing_zeros() < 64,
        bit(c, c.trailing_zeros() as u64),
        forall|u: u64| u < c.trailing_zeros() ==> !#[trigger] bit(c, u),
{
    axiom_u64_trailing_zeros(c);
}

/// Clearing the lowest set bit `s` of `c` keeps every other bit.
pub proof fn lemma_clear_lowest(c: u64, s: u64, u: u64)
    requires
        c != 0, s < 64, u < 64, bit(c, s),
        forall|v: u64| v < s ==> !#[trigger] bit(c, v),
    ensures bit(c & sub(c, 1), u) == (bit(c, u) && u != s),
{
    if u < s {
        assert(!bit(c, u));
        assert(((c >> u) & 1u64 != 1u64 && u < s && s < 64) ==> (((c & sub(c, 1)) >> u) & 1u64 != 1u64)) by (bit_vector);
    } else if u == s {
        assert(!bit(c, 0) || s == 0);
        // the bits below s are zero, so c - 1 clears bit s and sets the bits below it
        lemma_low_bits_zero(c, s);
        assert((c & sub(sub(1u64 << s, 1), 0) == 0u64 && ((c >> s) & 1u64 == 1u64) && s < 64) ==>
            (((c & sub(c, 1)) >> s) & 1u64 != 1u64)) by (bit_vector);
    } else {
        lemma_low_bits_zero(c, s);
        assert((c & sub(sub(1u64 << s, 1), 0) == 0u64 && ((c >> s) & 1u64 == 1u64) && s < u && u < 64) ==>
            ((((c & sub(c, 1)) >> u) & 1u64 == 1u64) == ((c >> u) & 1u64 == 1u64))) by (bit_vector);
    }
}

/// The bits of `c` below `s` are clear exactly when `c & (2^s - 1) == 0`.
pub proof fn lemma_low_bits_zero(c: u64, s: u64)
    requires s < 64, forall|v: u64| v < s ==> !#[trigger] bit(c, v),
    ensures c & sub(sub(1u64 << s, 1), 0) == 0u64,
    decreases s,
{
    if s > 0 {
        assert(!bit(c, (s - 1) as u64));
        lemma_low_bits_zero(c, (s - 1) as u64);
        let t = (s - 1) as u64;
        assert((c & sub(sub(1u64 << t, 1), 0) == 0u64 && ((c >> t) & 1u64 != 1u64) && t < 63 && s == t + 1) ==>
            c & sub(sub(1u64 << s, 1), 0) == 0u64) by (bit_vector);
    } else {
        assert(c & sub(sub(1u64 << 0u64, 1), 0) == 0u64) by (bit_vector);
    }
}

/// Prefix XOR: bit `t` of the result is the XOR of bits `0..=t` of `x`.
pub open spec fn prefix_xor(x: u64) -> u64 {
    let a = x ^ (x << 1u64);
    let b = a ^ (a << 2u64);
    let c = b ^ (b << 4u64);
    let d = c ^ (c << 8u64);
    let e = d ^ (d << 16u64);
    e ^ (e << 32u64)
}

/// `prefix_xor(x)` is the `p` with `p ^ (p << 1) == x`: bit 0 is `x`'s, and bit `t` toggles bit `t - 1` by `x`'s.
pub proof fn lemma_prefix_xor(x: u64, t: u64)
    requires t < 64,
    ensures
        t == 0 ==> bit(prefix_xor(x), 0) == bit(x, 0),
        t > 0 ==> bit(prefix_xor(x), t) == (bit(prefix_xor(x), (t - 1) as u64) != bit(x, t)),
{
    let p = prefix_xor(x);
    assert({
        let a = x ^ (x << 1u64);
        let b = a ^ (a << 2u64);
        let c = b ^ (b << 4u64);
        let d = c ^ (c << 8u64);
        let e = d ^ (d << 16u64);
        let p = e ^ (e << 32u64);
        p ^ (p << 1u64) == x
    }) by (bit_vector);
    assert(p ^ (p << 1u64) == x);
    if t == 0 {
        assert((p ^ (p << 1u64) == x) ==> (((p >> 0u64) & 1u64 == 1u64) == ((x >> 0u64) & 1u64 == 1u64))) by (bit_vector);
    } else {
        let s = (t - 1) as u64;
        assert((p ^ (p << 1u64) == x && 0 < t && t < 64 && s == t - 1) ==>
            (((p >> t) & 1u64 == 1u64) == (((p >> s) & 1u64 == 1u64) != ((x >> t) & 1u64 == 1u64)))) by (bit_vector);
    }
}

/// Bit `u % 64` of word `u / 64`, for row `u` of a bitmap stored as 64-bit words.
pub open spec fn word_bit(words: Seq<u64>, u: int) -> bool {
    0 <= u && u / 64 < words.len() && bit(words[u / 64], (u % 64) as u64)
}

/// `count_below` steps.
pub proof fn lemma_count_step(m: u64, n: int)
    requires 0 <= n < 64,
    ensures count_below(m, n + 1) == count_below(m, n) + if bit(m, n as u64) { 1int } else { 0int },
{
}

/// No set bit in `p..q`: equal counts.
pub proof fn lemma_count_flat(m: u64, p: int, q: int)
    requires 0 <= p <= q <= 64, forall|u: u64| p <= u < q ==> !#[trigger] bit(m, u),
    ensures count_below(m, q) == count_below(m, p),
    decreases q - p,
{
    if q > p {
        assert(!bit(m, (q - 1) as u64));
        lemma_count_flat(m, p, q - 1);
    }
}

/// Counts are monotone and bounded by the position.
pub proof fn lemma_count_bounds(m: u64, p: int, q: int)
    requires 0 <= p <= q <= 64,
    ensures 0 <= count_below(m, p) <= count_below(m, q) <= count_below(m, p) + (q - p), count_below(m, q) <= q,
    decreases q - p,
{
    if q > p {
        lemma_count_bounds(m, p, q - 1);
    } else {
        lemma_count_nonneg(m, p);
    }
}

pub proof fn lemma_count_nonneg(m: u64, n: int)
    requires 0 <= n <= 64,
    ensures 0 <= count_below(m, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_count_nonneg(m, n - 1);
    }
}

} // verus!

verus! {

/// Population count of `x` by the SWAR steps, as bit-vector expressions.
pub open spec fn swar_a(x: u64) -> u64 { sub(x, (x >> 1u64) & 0x5555_5555_5555_5555u64) }
pub open spec fn swar_b(x: u64) -> u64 { add(swar_a(x) & 0x3333_3333_3333_3333u64, (swar_a(x) >> 2u64) & 0x3333_3333_3333_3333u64) }
pub open spec fn swar_c(x: u64) -> u64 { add(swar_b(x), swar_b(x) >> 4u64) & 0x0f0f_0f0f_0f0f_0f0fu64 }
pub open spec fn swar_d(x: u64) -> u64 { add(swar_c(x), swar_c(x) >> 8u64) }
pub open spec fn swar_e(x: u64) -> u64 { add(swar_d(x), swar_d(x) >> 16u64) }
pub open spec fn swar_pop(x: u64) -> u64 { add(swar_e(x), swar_e(x) >> 32u64) & 127u64 }

/// The index of a single set bit: the population count of the bits below it.
pub proof fn lemma_swar_low(t: u64)
    requires t < 64,
    ensures swar_pop(sub(1u64 << t, 1u64)) == t,
{
    assert(t < 64 ==> swar_pop(sub(1u64 << t, 1u64)) == t) by (bit_vector);
}

} // verus!

verus! {

/// The lowest set bit of a non-zero `x` alone: `x & (!x + 1)` is `2^t` for `t` its trailing zeros.
pub proof fn lemma_lowest_alone(x: u64, t: u64)
    requires x != 0, t < 64, bit(x, t), forall|v: u64| v < t ==> !#[trigger] bit(x, v),
    ensures
        !x < 0xffff_ffff_ffff_ffffu64,
        x & add(!x, 1u64) == 1u64 << t,
        1u64 << t >= 1u64,
{
    assert(x != 0 ==> !x < 0xffff_ffff_ffff_ffffu64) by (bit_vector);
    lemma_low_bits_zero(x, t);
    assert((x & sub(sub(1u64 << t, 1), 0) == 0u64 && ((x >> t) & 1u64 == 1u64) && t < 64) ==>
        x & add(!x, 1u64) == 1u64 << t) by (bit_vector);
    assert(t < 64 ==> 1u64 << t >= 1u64) by (bit_vector);
}

/// Bounds of the SWAR steps (no step overflows).
pub proof fn lemma_swar_bounds(y: u64)
    ensures
        (y >> 1u64) & 0x5555_5555_5555_5555u64 <= y,
        swar_a(y) & 0x3333_3333_3333_3333u64 <= 0x3333_3333_3333_3333u64,
        (swar_a(y) >> 2u64) & 0x3333_3333_3333_3333u64 <= 0x3333_3333_3333_3333u64,
        swar_b(y) <= 0x6666_6666_6666_6666u64,
        swar_b(y) >> 4u64 <= 0x0666_6666_6666_6666u64,
        add(swar_b(y), swar_b(y) >> 4u64) & 0x0f0f_0f0f_0f0f_0f0fu64 <= 0x0f0f_0f0f_0f0f_0f0fu64,
        swar_c(y) >> 8u64 <= 0x000f_0f0f_0f0f_0f0fu64,
        swar_d(y) <= 0x1f1f_1f1f_1f1f_1f1fu64,
        swar_d(y) >> 16u64 <= 0x0000_1f1f_1f1f_1f1fu64,
        swar_e(y) <= 0x3f3f_3f3f_3f3f_3f3fu64,
        swar_e(y) >> 32u64 <= 0x0000_0000_3f3f_3f3fu64,
{
    assert((y >> 1u64) & 0x5555_5555_5555_5555u64 <= y) by (bit_vector);
    let a = swar_a(y);
    assert(a & 0x3333_3333_3333_3333u64 <= 0x3333_3333_3333_3333u64) by (bit_vector);
    assert((a >> 2u64) & 0x3333_3333_3333_3333u64 <= 0x3333_3333_3333_3333u64) by (bit_vector);
    assert(swar_b(y) <= 0x6666_6666_6666_6666u64) by (bit_vector);
    let b = swar_b(y);
    assert(b <= 0x6666_6666_6666_6666u64 ==> b >> 4u64 <= 0x0666_6666_6666_6666u64) by (bit_vector);
    assert(add(b, b >> 4u64) & 0x0f0f_0f0f_0f0f_0f0fu64 <= 0x0f0f_0f0f_0f0f_0f0fu64) by (bit_vector);
    let c = swar_c(y);
    assert(c <= 0x0f0f_0f0f_0f0f_0f0fu64 ==> c >> 8u64 <= 0x000f_0f0f_0f0f_0f0fu64) by (bit_vector);
    assert(c <= 0x0f0f_0f0f_0f0f_0f0fu64 ==> add(c, c >> 8u64) <= 0x1f1f_1f1f_1f1f_1f1fu64) by (bit_vector);
    let d = swar_d(y);
    assert(d <= 0x1f1f_1f1f_1f1f_1f1fu64 ==> d >> 16u64 <= 0x0000_1f1f_1f1f_1f1fu64) by (bit_vector);
    assert(d <= 0x1f1f_1f1f_1f1f_1f1fu64 ==> add(d, d >> 16u64) <= 0x3f3f_3f3f_3f3f_3f3fu64) by (bit_vector);
    let e = swar_e(y);
    assert(e <= 0x3f3f_3f3f_3f3f_3f3fu64 ==> e >> 32u64 <= 0x0000_0000_3f3f_3f3fu64) by (bit_vector);
}

/// The index of the lowest set bit of a non-zero mask (`trailing_zeros`, computed without a call that may unwind).
pub fn low_index(x: u64) -> (t: u64)
    requires x != 0,
    ensures
        t < 64,
        bit(x, t),
        forall|u: u64| u < t ==> !#[trigger] bit(x, u),
    no_unwind
{
    proof { lemma_first_bit(x); }
    let ghost t0 = x.trailing_zeros() as u64;
    proof { lemma_lowest_alone(x, t0); }
    let nx = !x;
    let low = x & (nx + 1);
    let y = low - 1;
    proof {
        lemma_swar_bounds(y);
        lemma_swar_low(t0);
    }
    let a = y - ((y >> 1) & 0x5555_5555_5555_5555u64);
    let b = (a & 0x3333_3333_3333_3333u64) + ((a >> 2) & 0x3333_3333_3333_3333u64);
    let c = (b + (b >> 4)) & 0x0f0f_0f0f_0f0f_0f0fu64;
    let d = c + (c >> 8);
    let e = d + (d >> 16);
    let f = (e + (e >> 32)) & 127u64;
    proof {
        assert(a == swar_a(y));
        assert(b == swar_b(y));
        assert(c == swar_c(y));
        assert(d == swar_d(y));
        assert(e == swar_e(y));
        assert(f == swar_pop(y));
    }
    f
}

} // verus!
