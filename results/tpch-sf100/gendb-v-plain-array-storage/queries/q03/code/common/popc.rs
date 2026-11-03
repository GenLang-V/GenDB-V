//! Number of set bits below a position (`count_below`), by a byte table: eight lookups, no loop.
use vstd::prelude::*;
use crate::agent::common::bits::*;

verus! {

/// `t[v]` is the number of set bits of byte `v`.
pub open spec fn pc_ok(t: Seq<u8>) -> bool {
    &&& t.len() == 256
    &&& forall|v: int| 0 <= v < 256 ==> #[trigger] t[v] as int == count_below(v as u64, 8)
}

/// The bits of `v` from position 1 on are those of `v >> 1`.
proof fn lemma_count_shift(v: u64, n: int)
    requires 0 <= n < 64,
    ensures count_below(v, n + 1) == (if bit(v, 0) { 1int } else { 0int }) + count_below(v >> 1u64, n),
    decreases n,
{
    lemma_count_step(v, n);
    if n > 0 {
        lemma_count_shift(v, n - 1);
        lemma_count_step(v >> 1u64, n - 1);
        let k = n as u64;
        assert(((v >> k) & 1u64 == 1u64) == (((v >> 1u64) >> sub(k, 1u64)) & 1u64 == 1u64)) by (bit_vector)
            requires 1 <= k < 64;
        assert(bit(v, k) == bit(v >> 1u64, (k - 1) as u64));
    }
}

/// Counts agree where the bits agree.
proof fn lemma_count_eq(x: u64, m: u64, n: int)
    requires 0 <= n <= 64, forall|u: u64| u < n ==> #[trigger] bit(x, u) == bit(m, u),
    ensures count_below(x, n) == count_below(m, n),
    decreases n,
{
    if n > 0 {
        lemma_count_eq(x, m, n - 1);
        assert(bit(x, (n - 1) as u64) == bit(m, (n - 1) as u64));
    }
}

/// Byte `b` of `x` (shift `s = 8b`) holds bits `8b..8b+8`.
proof fn lemma_count_byte(x: u64, b: int, s: u64, u: int)
    requires 0 <= b < 8, s as int == 8 * b, 0 <= u <= 8,
    ensures count_below(x, 8 * b + u) == count_below(x, 8 * b) + count_below((x >> s) & 255u64, u),
    decreases u,
{
    if u > 0 {
        lemma_count_byte(x, b, s, u - 1);
        let w = (u - 1) as u64;
        let y = (x >> s) & 255u64;
        lemma_count_step(x, 8 * b + u - 1);
        lemma_count_step(y, u - 1);
        assert(((x >> add(s, w)) & 1u64 == 1u64) == ((((x >> s) & 255u64) >> w) & 1u64 == 1u64)) by (bit_vector)
            requires s <= 56, w < 8;
        assert(bit(x, (8 * b + u - 1) as u64) == bit(y, w));
    }
}

/// The table of bit counts of the bytes, checked.
pub fn pc_table() -> (r: Option<[u8; 256]>)
    ensures r matches Some(t) ==> pc_ok(t@),
    no_unwind
{
    let t: [u8; 256] = [
        0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
        1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
        1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
        2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
        1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
        2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
        2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
        3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8,
    ];
    if t[0] != 0 {
        return None;
    }
    proof {
        assert forall|k: u64| k < 8 implies !#[trigger] bit(0u64, k) by {
            assert((0u64 >> k) & 1u64 == 0u64) by (bit_vector);
        }
        lemma_count_eq(0u64, 0u64, 8);
        assert(count_below(0u64, 8) == 0) by {
            lemma_count_flat(0u64, 0, 8);
        }
    }
    let mut v: usize = 1;
    while v < 256
        invariant
            1 <= v <= 256, t@.len() == 256,
            forall|u: int| 0 <= u < v ==> #[trigger] t@[u] as int == count_below(u as u64, 8),
        decreases 256 - v,
    {
        if t[v] as usize != t[v / 2] as usize + v % 2 {
            return None;
        }
        proof {
            let x = v as u64;
            lemma_count_shift(x, 7);
            assert(x >> 1u64 == (v / 2) as u64) by (bit_vector)
                requires x == v as u64, v < 256;
            assert(bit(x, 0) == (v % 2 == 1)) by {
                assert(((x >> 0u64) & 1u64 == 1u64) == (x % 2 == 1)) by (bit_vector);
            }
            let h = x >> 1u64;
            assert(!bit(h, 7)) by {
                assert(((x >> 1u64) >> 7u64) & 1u64 == 0u64) by (bit_vector)
                    requires x < 256;
            }
            assert(count_below(h, 8) == count_below(h, 7));
            assert(t@[(v / 2) as int] as int == count_below((v / 2) as u64, 8));
        }
        v = v + 1;
    }
    Some(t)
}

/// The number of set bits of `m` at positions `0..=t`.
pub fn popc_below(m: u64, t: u64, pc: &[u8; 256]) -> (r: u64)
    requires t < 64, pc_ok(pc@),
    ensures r as int == count_below(m, t + 1),
    no_unwind
{
    let x: u64 = if t == 63 {
        m
    } else {
        assert((1u64 << add(t, 1u64)) >= 1u64) by (bit_vector) requires t < 63;
        m & ((1u64 << (t + 1)) - 1)
    };
    proof {
        assert forall|u: u64| u < 64 implies #[trigger] bit(x, u) == (u <= t && bit(m, u)) by {
            if t == 63 {
            } else {
                assert((((m & sub(1u64 << add(t, 1u64), 1u64)) >> u) & 1u64 == 1u64) == (u <= t && ((m >> u) & 1u64 == 1u64)))
                    by (bit_vector) requires t < 63, u < 64;
            }
        }
        lemma_count_eq(x, m, t + 1);
        assert forall|u: u64| t + 1 <= u < 64 implies !#[trigger] bit(x, u) by {}
        lemma_count_flat(x, t + 1, 64);
        lemma_count_byte(x, 0, 0u64, 8);
        lemma_count_byte(x, 1, 8u64, 8);
        lemma_count_byte(x, 2, 16u64, 8);
        lemma_count_byte(x, 3, 24u64, 8);
        lemma_count_byte(x, 4, 32u64, 8);
        lemma_count_byte(x, 5, 40u64, 8);
        lemma_count_byte(x, 6, 48u64, 8);
        lemma_count_byte(x, 7, 56u64, 8);
        assert(count_below(x, 0) == 0);
        assert(x >> 0u64 == x) by (bit_vector);
        assert(((x >> 0u64) & 255u64) < 256 && ((x >> 8u64) & 255u64) < 256 && ((x >> 16u64) & 255u64) < 256
            && ((x >> 24u64) & 255u64) < 256 && ((x >> 32u64) & 255u64) < 256 && ((x >> 40u64) & 255u64) < 256
            && ((x >> 48u64) & 255u64) < 256 && ((x >> 56u64) & 255u64) < 256) by (bit_vector);
    }
    let r = pc[(x & 255u64) as usize] as u64 + pc[((x >> 8u64) & 255u64) as usize] as u64
        + pc[((x >> 16u64) & 255u64) as usize] as u64 + pc[((x >> 24u64) & 255u64) as usize] as u64
        + pc[((x >> 32u64) & 255u64) as usize] as u64 + pc[((x >> 40u64) & 255u64) as usize] as u64
        + pc[((x >> 48u64) & 255u64) as usize] as u64 + pc[((x >> 56u64) & 255u64) as usize] as u64;
    r
}

} // verus!
