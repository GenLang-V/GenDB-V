//! The set bits of a bitmap range, listed in increasing order: `set_bits` writes `base + k` for every set bit `k` of
//! `[k_lo, k_hi)` (bit `k` is bit `k % 64` of word `k / 64`), one trailing-zero count per set bit. The range starts at a
//! word boundary; a partial last word must have no set bits past `k_hi`.
use vstd::prelude::*;
use crate::gendb_entry::work::put;
use super::popcnt::{swar, count_below};

verus! {

/// Bit `k % 64` of word `k / 64`.
pub open spec fn wbit(words: Seq<u64>, k: int) -> bool {
    (words[k / 64] >> ((k % 64) as u64)) & 1u64 == 1u64
}

/// `out[0 .. n]` lists, in increasing order, `base + k` for the set bits `k` of `[k_lo, pos)`.
pub open spec fn bitlist_ok(out: Seq<usize>, n: int, bm: Seq<u64>, k_lo: int, pos: int, base: int) -> bool {
    &&& 0 <= n <= pos - k_lo
    &&& forall|i: int| 0 <= i < n ==> k_lo <= #[trigger] out[i] - base < pos && wbit(bm, out[i] - base)
    &&& forall|i: int, i2: int| 0 <= i < i2 < n ==> #[trigger] out[i] < #[trigger] out[i2]
    &&& forall|k: int| k_lo <= k < pos && #[trigger] wbit(bm, k) ==> exists|i: int| 0 <= i < n && out[i] == base + k
}

/// The lowest set bit of `x != 0` (two's complement isolation, then a SWAR count of the bits below it).
proof fn lemma_lowest(x: u64)
    requires x != 0,
    ensures
        swar(((x & ((!x) + 1u64) as u64) - 1u64) as u64) < 64,
        (x >> swar(((x & ((!x) + 1u64) as u64) - 1u64) as u64)) & 1u64 == 1u64,
        x & (((1u64 << swar(((x & ((!x) + 1u64) as u64) - 1u64) as u64)) - 1u64) as u64) == 0u64,
{
    assert(swar(((x & ((!x) + 1u64) as u64) - 1u64) as u64) < 64) by (bit_vector) requires x != 0u64;
    assert((x >> swar(((x & ((!x) + 1u64) as u64) - 1u64) as u64)) & 1u64 == 1u64) by (bit_vector) requires x != 0u64;
    assert(x & (((1u64 << swar(((x & ((!x) + 1u64) as u64) - 1u64) as u64)) - 1u64) as u64) == 0u64) by (bit_vector) requires x != 0u64;
}

/// The position of the lowest set bit of `x != 0`.
fn lowest_bit(x: u64) -> (t: u64)
    requires x != 0,
    ensures
        t < 64,
        (x >> t) & 1u64 == 1u64,
        forall|b: u64| b < t ==> #[trigger] (x >> b) & 1u64 == 0u64,
    no_unwind
{
    proof {
        assert((!x) < 0xffff_ffff_ffff_ffffu64) by (bit_vector) requires x != 0u64;
        assert(x & ((!x) + 1u64) as u64 >= 1u64) by (bit_vector) requires x != 0u64;
        lemma_lowest(x);
    }
    let lsb = x & ((!x) + 1);
    let t = count_below(lsb - 1, 64);
    proof {
        assert forall|b: u64| b < t implies #[trigger] (x >> b) & 1u64 == 0u64 by {
            assert((x >> b) & 1u64 == 0u64) by (bit_vector)
                requires b < t, t < 64, x & (((1u64 << t) - 1u64) as u64) == 0u64;
        }
    }
    t
}

/// Bit `b` of `x` with bit `t` flipped.
proof fn lemma_flip_bit(x: u64, t: u64, b: u64)
    requires t < 64, b < 64,
    ensures ((x ^ (1u64 << t)) >> b) & 1u64 == if b == t { ((x >> b) & 1u64) ^ 1u64 } else { (x >> b) & 1u64 },
{
    assert(((x ^ (1u64 << t)) >> b) & 1u64 == if b == t { ((x >> b) & 1u64) ^ 1u64 } else { (x >> b) & 1u64 }) by (bit_vector)
        requires t < 64, b < 64;
}

/// A bit is 0 or 1.
proof fn lemma_bit01(x: u64, b: u64)
    requires b < 64,
    ensures (x >> b) & 1u64 == 0u64 || (x >> b) & 1u64 == 1u64,
{
    assert((x >> b) & 1u64 == 0u64 || (x >> b) & 1u64 == 1u64) by (bit_vector);
}

/// Row arithmetic of a word: position `kb + b` lies in word `kb / 64` at bit `b`.
proof fn lemma_pos(kb: int, b: int)
    requires kb >= 0, kb % 64 == 0, 0 <= b < 64,
    ensures (kb + b) / 64 == kb / 64, (kb + b) % 64 == b,
{
    assert((kb + b) / 64 == kb / 64 && (kb + b) % 64 == b) by (nonlinear_arith) requires kb >= 0, kb % 64 == 0, 0 <= b < 64;
}

/// The set bits of the word of position `kb`, from bit `lo_b` on, appended to `out[n ..]`.
fn word_bits(x0: u64, kb: usize, k_lo: usize, k_hi: usize, base: usize, out: &mut Vec<usize>, n: usize,
    Ghost(bm): Ghost<Seq<u64>>) -> (n2: usize)
    requires
        k_lo <= kb < k_hi, kb % 64 == 0, k_lo % 64 == 0,
        kb / 64 < bm.len(), x0 == bm[kb as int / 64],
        k_hi % 64 != 0 ==> forall|k: int| k_hi <= k < (k_hi / 64 + 1) * 64 ==> !#[trigger] wbit(bm, k),
        base + k_hi <= usize::MAX,
        old(out)@.len() >= k_hi - k_lo,
        bitlist_ok(old(out)@, n as int, bm, k_lo as int, kb as int, base as int),
    ensures
        final(out)@.len() == old(out)@.len(),
        bitlist_ok(final(out)@, n2 as int, bm, k_lo as int, if kb + 64 <= k_hi { kb + 64 } else { k_hi as int }, base as int),
    no_unwind
{
    let ghost end: int = if kb + 64 <= k_hi { kb + 64 } else { k_hi as int };
    let mut x = x0;
    let mut n2 = n;
    let ghost mut lo_b: int = 0;
    proof {
        assert forall|b: u64| b < 64 implies ((x >> b) & 1u64 == 1u64) == (b >= lo_b && (x0 >> b) & 1u64 == 1u64) by {}
    }
    while x != 0
        invariant
            k_lo <= kb < k_hi, kb % 64 == 0, k_lo % 64 == 0,
            kb / 64 < bm.len(), x0 == bm[kb as int / 64],
            k_hi % 64 != 0 ==> forall|k: int| k_hi <= k < (k_hi / 64 + 1) * 64 ==> !#[trigger] wbit(bm, k),
            base + k_hi <= usize::MAX,
            out@.len() == old(out)@.len(), out@.len() >= k_hi - k_lo,
            end == if kb + 64 <= k_hi { kb + 64 } else { k_hi as int },
            0 <= lo_b <= 64,
            forall|b: u64| b < 64 ==> ((x >> b) & 1u64 == 1u64) == (b >= lo_b && (x0 >> b) & 1u64 == 1u64),
            bitlist_ok(out@, n2 as int, bm, k_lo as int, if kb + lo_b < end { kb + lo_b } else { end }, base as int),
        decreases 64 - lo_b,
    {
        let t = lowest_bit(x);
        proof {
            assert(t < 64);
            assert((x >> t) & 1u64 == 1u64);
            assert(t >= lo_b);
            // the bits of the word between `lo_b` and `t` are clear, bit `t` is set
            assert forall|b: int| lo_b <= b < t implies !#[trigger] wbit(bm, kb + b) by {
                lemma_pos(kb as int, b);
                assert((x >> (b as u64)) & 1u64 == 0u64);
            }
            lemma_pos(kb as int, t as int);
            assert(wbit(bm, kb + t));
            // a set bit lies below `k_hi`
            if kb + t >= k_hi {
                assert(k_hi % 64 != 0) by {
                    if k_hi % 64 == 0 {
                        assert(kb + 64 <= k_hi) by (nonlinear_arith) requires kb < k_hi, kb % 64 == 0, k_hi % 64 == 0;
                    }
                }
                assert(kb + t < (k_hi / 64 + 1) * 64) by (nonlinear_arith) requires kb < k_hi, kb % 64 == 0, t < 64;
            }
            assert(kb + t < k_hi);
            assert(kb + lo_b <= kb + t < end);
        }
        let ghost o0 = out@;
        let v = base + kb + t as usize;
        proof {
            assert(n2 <= kb + lo_b - k_lo);
        }
        put(out, n2, v);
        proof {
            let p1 = kb + t + 1;
            assert(bitlist_ok(out@, n2 + 1, bm, k_lo as int, p1, base as int)) by {
                assert forall|i: int| 0 <= i < n2 + 1 implies k_lo <= #[trigger] out@[i] - base < p1 && wbit(bm, out@[i] - base) by {
                    if i < n2 { assert(out@[i] == o0[i]); }
                }
                assert forall|i: int, i2: int| 0 <= i < i2 < n2 + 1 implies #[trigger] out@[i] < #[trigger] out@[i2] by {
                    if i2 < n2 { assert(out@[i] == o0[i] && out@[i2] == o0[i2]); } else { assert(out@[i] == o0[i]); }
                }
                assert forall|k: int| k_lo <= k < p1 && #[trigger] wbit(bm, k) implies exists|i: int| 0 <= i < n2 + 1 && out@[i] == base + k by {
                    if k < kb + lo_b {
                        let i = choose|i: int| 0 <= i < n2 && o0[i] == base + k;
                        assert(out@[i] == o0[i]);
                    } else if k < kb + t {
                        assert(!wbit(bm, kb + (k - kb)));
                    } else {
                        assert(out@[n2 as int] == base + k);
                    }
                }
            }
        }
        let ghost x1 = x;
        x = x ^ (1u64 << t);
        n2 = n2 + 1;
        proof {
            assert forall|b: u64| b < 64 implies ((x >> b) & 1u64 == 1u64) == (b >= t + 1 && (x0 >> b) & 1u64 == 1u64) by {
                lemma_flip_bit(x1, t, b);
                lemma_bit01(x1, b);
                assert(((x1 >> b) & 1u64 == 1u64) == (b >= lo_b && (x0 >> b) & 1u64 == 1u64));
                if b < t {
                    assert((x1 >> b) & 1u64 == 0u64);
                    assert((x >> b) & 1u64 == 0u64);
                } else if b == t {
                    assert((x1 >> b) & 1u64 == 1u64);
                    assert(1u64 ^ 1u64 == 0u64) by (bit_vector);
                    assert((x >> b) & 1u64 == 0u64);
                } else {
                    assert((x >> b) & 1u64 == (x1 >> b) & 1u64);
                }
            }
            lo_b = t + 1;
        }
    }
    proof {
        // no set bit of the word remains from `lo_b` on
        assert forall|k: int| k_lo <= k < end && #[trigger] wbit(bm, k) implies exists|i: int| 0 <= i < n2 && out@[i] == base + k by {
            if k >= kb + lo_b {
                let b = k - kb;
                lemma_pos(kb as int, b);
                assert(x == 0u64);
                let bb = b as u64;
                assert((x >> bb) & 1u64 == 0u64) by (bit_vector) requires x == 0u64;
                assert(false);
            }
        }
        assert forall|i: int| 0 <= i < n2 implies k_lo <= #[trigger] out@[i] - base < end && wbit(bm, out@[i] - base) by {}
    }
    n2
}

/// The set bits of `[k_lo, k_hi)`, as `base + k` in increasing order in `out[0 .. n]`.
pub fn set_bits(bm: &Vec<u64>, k_lo: usize, k_hi: usize, base: usize, out: &mut Vec<usize>) -> (n: usize)
    requires
        k_lo <= k_hi, k_lo % 64 == 0, k_hi <= bm@.len() * 64,
        k_hi % 64 != 0 ==> forall|k: int| k_hi <= k < (k_hi / 64 + 1) * 64 ==> !#[trigger] wbit(bm@, k),
        base + k_hi <= usize::MAX, k_hi + 64 <= usize::MAX,
        old(out)@.len() >= k_hi - k_lo,
    ensures
        final(out)@.len() == old(out)@.len(),
        bitlist_ok(final(out)@, n as int, bm@, k_lo as int, k_hi as int, base as int),
    no_unwind
{
    let mut n: usize = 0;
    let mut kb = k_lo;
    while kb < k_hi
        invariant
            k_lo <= kb, k_lo % 64 == 0, kb % 64 == 0, k_hi <= bm@.len() * 64,
            k_hi % 64 != 0 ==> forall|k: int| k_hi <= k < (k_hi / 64 + 1) * 64 ==> !#[trigger] wbit(bm@, k),
            base + k_hi <= usize::MAX, k_hi + 64 <= usize::MAX, kb <= k_hi + 63,
            out@.len() == old(out)@.len(), out@.len() >= k_hi - k_lo,
            kb < k_hi ==> bitlist_ok(out@, n as int, bm@, k_lo as int, kb as int, base as int),
            kb >= k_hi ==> bitlist_ok(out@, n as int, bm@, k_lo as int, k_hi as int, base as int),
        decreases k_hi + 64 - kb,
    {
        proof {
            assert(kb / 64 < bm@.len()) by (nonlinear_arith) requires kb < k_hi, k_hi <= bm@.len() * 64;
        }
        let x = bm[kb / 64];
        n = word_bits(x, kb, k_lo, k_hi, base, out, n, Ghost(bm@));
        kb = kb + 64;
    }
    if k_lo == k_hi {
        proof {
            assert forall|k: int| k_lo <= k < k_hi && #[trigger] wbit(bm@, k) implies exists|i: int| 0 <= i < n && out@[i] == base + k by {}
        }
    }
    n
}

} // verus!
