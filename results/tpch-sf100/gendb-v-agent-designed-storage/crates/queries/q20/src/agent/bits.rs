//! Bit sets in `u64` words: bit `x` is bit `x % 64` of word `x / 64` (`bit`); `set_bit` and `get_bit` are
//! `no_unwind`, so worker tasks use them.
use vstd::prelude::*;

verus! {

/// Bit `x` of the words `v`.
pub open spec fn bit(v: Seq<u64>, x: int) -> bool {
    (v[x / 64] >> ((x % 64) as u64)) & 1u64 == 1u64
}

/// Room for `n` bits.
pub open spec fn holds(v: Seq<u64>, n: int) -> bool {
    n <= v.len() * 64
}

proof fn lemma_bv_set(a: u64, b: u64, c: u64)
    requires b < 64, c < 64,
    ensures ((a | (1u64 << b)) >> c) & 1u64 == (if b == c { 1u64 } else { (a >> c) & 1u64 }),
{
    assert(((a | (1u64 << b)) >> c) & 1u64 == (if b == c { 1u64 } else { (a >> c) & 1u64 })) by (bit_vector)
        requires b < 64, c < 64;
}

proof fn lemma_bv_zero(c: u64)
    requires c < 64,
    ensures (0u64 >> c) & 1u64 == 0u64,
{
    assert((0u64 >> c) & 1u64 == 0u64) by (bit_vector);
}

proof fn lemma_bv_test(a: u64, c: u64)
    requires c < 64,
    ensures ((a >> c) & 1u64 == 1u64) == ((a >> c) & 1u64 != 0u64),
{
    assert(((a >> c) & 1u64 == 1u64) == ((a >> c) & 1u64 != 0u64)) by (bit_vector);
}

/// Bit `x` of `v`.
pub fn get_bit(v: &Vec<u64>, x: usize) -> (b: bool)
    requires x / 64 < v@.len(),
    ensures b == bit(v@, x as int),
    no_unwind
{
    let w = v[x / 64];
    let c = (x % 64) as u64;
    proof {
        lemma_bv_test(w, c);
    }
    (w >> c) & 1u64 != 0
}

/// Set bit `x` of `v`.
pub fn set_bit(v: &mut Vec<u64>, x: usize)
    requires x / 64 < old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|y: int| 0 <= y < old(v)@.len() * 64 ==> #[trigger] bit(final(v)@, y) == (y == x || bit(old(v)@, y)),
    no_unwind
{
    let ghost v0 = v@;
    let w = x / 64;
    let c = (x % 64) as u64;
    let a = v[w];
    v[w] = a | (1u64 << c);
    proof {
        assert forall|y: int| 0 <= y < v0.len() * 64 implies #[trigger] bit(v@, y) == (y == x || bit(v0, y)) by {
            let wy = y / 64;
            let cy = (y % 64) as u64;
            if wy == w {
                lemma_bv_set(a, c, cy);
                if cy == c {
                    assert(y == x) by {
                        assert(y == wy * 64 + y % 64);
                        assert(x == w * 64 + x % 64);
                    }
                } else {
                    assert(y != x);
                }
            } else {
                assert(v@[wy] == v0[wy]);
                assert(y != x);
            }
        }
    }
}

/// Bit `i` of the words `a`, copied from word `w0` of `g` on, is bit `w0 * 64 + i` of `g`.
pub proof fn lemma_bit_words(a: Seq<u64>, g: Seq<u64>, w0: int, i: int)
    requires
        0 <= w0, 0 <= i, i / 64 < a.len(), w0 + a.len() <= g.len(),
        a == g.subrange(w0, w0 + a.len()),
    ensures bit(a, i) == bit(g, w0 * 64 + i),
{
    vstd::arithmetic::div_mod::lemma_hoist_over_denominator(i, w0, 64);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(w0, i, 64);
    assert(i + w0 * 64 == w0 * 64 + i && 64 * w0 + i == w0 * 64 + i) by (nonlinear_arith);
    assert(a[i / 64] == g[w0 + i / 64]);
}

/// The bits of a zero word are clear.
pub proof fn lemma_zero_word(v: Seq<u64>, b: int, i: int)
    requires b % 64 == 0, 0 <= b <= i < b + 64, b / 64 < v.len(), v[b / 64] == 0u64,
    ensures !bit(v, i),
{
    assert(i / 64 == b / 64);
    lemma_bv_zero((i % 64) as u64);
}

/// All bits of zero words are clear.
pub proof fn lemma_zero_bits(v: Seq<u64>, n: int)
    requires forall|i: int| 0 <= i < v.len() ==> #[trigger] v[i] == 0u64, holds(v, n),
    ensures forall|y: int| 0 <= y < n ==> !#[trigger] bit(v, y),
{
    assert forall|y: int| 0 <= y < n implies !#[trigger] bit(v, y) by {
        assert(v[y / 64] == 0u64);
        lemma_bv_zero((y % 64) as u64);
    }
}

} // verus!
