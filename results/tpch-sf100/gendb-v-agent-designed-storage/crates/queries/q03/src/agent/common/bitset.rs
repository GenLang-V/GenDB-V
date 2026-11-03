//! Bit sets over row positions (one bit per row, 64 rows per `u64` word): `bit(s, i)` is bit `i % 64` of word
//! `i / 64`. `bits_eq_u8` builds the set of the rows whose `u8` code equals a value (a cache-resident filter of a
//! low-cardinality column); `bit_at` tests one row.
use vstd::prelude::*;

verus! {

/// Row `i` is in the set `s`.
pub open spec fn bit(s: Seq<u64>, i: int) -> bool {
    (s[i / 64] >> ((i % 64) as u64)) & 1u64 == 1u64
}

/// Setting bit `i` of a word (`b` is 0 or 1) changes only bit `i`.
proof fn lemma_or_bit(x: u64, b: u64, i: u64, k: u64)
    requires i < 64, k < 64, b <= 1,
    ensures
        ((x | (b << i)) >> k) & 1u64 == if k == i { ((x >> k) & 1u64) | b } else { (x >> k) & 1u64 },
{
    assert(((x | (b << i)) >> k) & 1u64 == if k == i { ((x >> k) & 1u64) | b } else { (x >> k) & 1u64 })
        by (bit_vector)
        requires i < 64, k < 64, b <= 1;
}

/// The bits of the zero word are clear.
proof fn lemma_zero_bits(k: u64)
    requires k < 64,
    ensures (0u64 >> k) & 1u64 == 0u64,
{
    assert((0u64 >> k) & 1u64 == 0u64) by (bit_vector) requires k < 64;
}

/// Row `w * 64 + k` is bit `k` of word `w`.
proof fn lemma_word_pos(w: int, k: int)
    requires 0 <= w, 0 <= k < 64,
    ensures (w * 64 + k) / 64 == w, (w * 64 + k) % 64 == k,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(w * 64 + k, 64, w, k);
}

/// The word of the rows `[base, base + 64)` (those below `n`) whose code is `v`.
fn word_eq_u8(codes: &[u8], n: usize, base: usize, v: u8) -> (x: u64)
    requires n <= codes@.len(), base <= n, n + 64 <= usize::MAX,
    ensures forall|k: u64| k < 64 ==> (((x >> k) & 1u64 == 1u64) <==> (base + k < n && codes@[base + k] == v)),
{
    let mut x: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert forall|k: u64| k < 64 implies (((x >> k) & 1u64 == 1u64) <==> (k < i && base + k < n && codes@[base + k] == v)) by {
            lemma_zero_bits(k);
        }
    }
    while i < 64
        invariant
            n <= codes@.len(), base <= n, n + 64 <= usize::MAX,
            i <= 64,
            forall|k: u64| k < 64 ==> (((x >> k) & 1u64 == 1u64) <==> (k < i && base + k < n && codes@[base + k] == v)),
        decreases 64 - i,
    {
        let b: u64 = if base + i < n && codes[base + i] == v { 1 } else { 0 };
        let ghost x0 = x;
        x = x | (b << (i as u64));
        proof {
            assert forall|k: u64| k < 64 implies (((x >> k) & 1u64 == 1u64) <==> (k < i + 1 && base + k < n && codes@[base + k] == v)) by {
                lemma_or_bit(x0, b, i as u64, k);
                if k == i as u64 {
                    assert(((x0 >> k) & 1u64) == 0u64) by {
                        assert(((x0 >> k) & 1u64) <= 1u64) by (bit_vector);
                    }
                    assert((0u64 | b) == b) by (bit_vector);
                }
            }
        }
        i = i + 1;
    }
    x
}

/// The word of the rows `[base, base + 64)` (all below `n`) whose code is `v`: one pass without bounds tests.
fn word_eq_u8_full(codes: &[u8], n: usize, base: usize, v: u8) -> (x: u64)
    requires n <= codes@.len(), base + 64 <= n, n + 64 <= usize::MAX,
    ensures forall|k: u64| k < 64 ==> (((x >> k) & 1u64 == 1u64) <==> (base + k < n && codes@[base + k] == v)),
{
    let mut x: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert forall|k: u64| k < 64 implies (((x >> k) & 1u64 == 1u64) <==> (k < i && codes@[base + k] == v)) by {
            lemma_zero_bits(k);
        }
    }
    while i < 64
        invariant
            n <= codes@.len(), base + 64 <= n, n + 64 <= usize::MAX,
            i <= 64,
            forall|k: u64| k < 64 ==> (((x >> k) & 1u64 == 1u64) <==> (k < i && codes@[base + k] == v)),
        decreases 64 - i,
    {
        let b: u64 = if codes[base + i] == v { 1 } else { 0 };
        let ghost x0 = x;
        x = x | (b << (i as u64));
        proof {
            assert forall|k: u64| k < 64 implies (((x >> k) & 1u64 == 1u64) <==> (k < i + 1 && codes@[base + k] == v)) by {
                lemma_or_bit(x0, b, i as u64, k);
                if k == i as u64 {
                    assert(((x0 >> k) & 1u64) == 0u64) by {
                        assert(((x0 >> k) & 1u64) <= 1u64) by (bit_vector);
                    }
                    assert((0u64 | b) == b) by (bit_vector);
                }
            }
        }
        i = i + 1;
    }
    x
}

/// The set of the rows `[0, n)` whose code is `v`.
pub fn bits_eq_u8(codes: &[u8], n: usize, v: u8) -> (s: Vec<u64>)
    requires n <= codes@.len(), n + 64 <= usize::MAX,
    ensures
        s@.len() == n / 64 + 1,
        forall|i: int| 0 <= i < n ==> #[trigger] bit(s@, i) == (codes@[i] == v),
{
    let nw = n / 64 + 1;
    let mut s: Vec<u64> = Vec::with_capacity(nw);
    let mut w: usize = 0;
    while w < nw
        invariant
            n <= codes@.len(), n + 64 <= usize::MAX,
            nw == n / 64 + 1,
            w <= nw,
            s@.len() == w,
            forall|i: int| 0 <= i < n && i / 64 < w ==> #[trigger] bit(s@, i) == (codes@[i] == v),
        decreases nw - w,
    {
        proof {
            assert(w * 64 <= n) by (nonlinear_arith) requires w < n / 64 + 1;
        }
        let base = w * 64;
        let x = if base + 64 <= n { word_eq_u8_full(codes, n, base, v) } else { word_eq_u8(codes, n, base, v) };
        let ghost s0 = s@;
        s.push(x);
        proof {
            assert forall|i: int| 0 <= i < n && i / 64 < w + 1 implies #[trigger] bit(s@, i) == (codes@[i] == v) by {
                let wi = i / 64;
                let k = i % 64;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 64);
                if wi < w {
                    assert(s@[wi] == s0[wi]);
                    assert(bit(s@, i) == bit(s0, i));
                } else {
                    assert(wi == w);
                    assert(i == base + k);
                    assert(s@[wi] == x);
                    assert(((x >> (k as u64)) & 1u64 == 1u64) <==> (base + k < n && codes@[base + k] == v));
                }
            }
        }
        w = w + 1;
    }
    s
}

/// Row `i` is in the set.
pub fn bit_at(s: &Vec<u64>, i: usize) -> (r: bool)
    requires i / 64 < s@.len(),
    ensures r == bit(s@, i as int),
    no_unwind
{
    let w = s[i / 64];
    (w >> ((i % 64) as u64)) & 1u64 == 1u64
}

} // verus!
