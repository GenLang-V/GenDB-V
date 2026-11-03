//! A bitmap over positions `0..n` as `u64` words: bit `o` is bit `o % 64` of word `o / 64` (`bit_at`). Words are
//! built from 64 flags at a time (`word_of`); a bitmap of a range starting at a multiple of 64 is the tail of the
//! whole bitmap after concatenation (`lemma_concat`).
use vstd::prelude::*;
use crate::gendb_entry::work::put;

verus! {

/// Bit `o` of a word sequence.
pub open spec fn bit_at(words: Seq<u64>, o: int) -> bool {
    (words[o / 64] >> ((o % 64) as u64)) & 1u64 == 1u64
}

/// Bit `b` of one word.
pub open spec fn wbit(w: u64, b: int) -> bool {
    (w >> (b as u64)) & 1u64 == 1u64
}

/// Setting bit `b` sets it and keeps every other bit.
pub proof fn lemma_set_bit(w: u64, b: u64)
    requires b < 64,
    ensures
        wbit(w | (1u64 << b), b as int),
        forall|c: u64| c < 64 && c != b ==> wbit(w | (1u64 << b), c as int) == #[trigger] wbit(w, c as int),
{
    assert(((w | (1u64 << b)) >> b) & 1u64 == 1u64) by (bit_vector) requires b < 64;
    assert forall|c: u64| c < 64 && c != b implies wbit(w | (1u64 << b), c as int) == #[trigger] wbit(w, c as int) by {
        assert((((w | (1u64 << b)) >> c) & 1u64 == 1u64) == ((w >> c) & 1u64 == 1u64)) by (bit_vector)
            requires b < 64, c < 64, c != b;
    }
}

/// The zero word has no bit set.
pub proof fn lemma_zero_word()
    ensures forall|c: u64| c < 64 ==> !#[trigger] wbit(0u64, c as int),
{
    assert forall|c: u64| c < 64 implies !#[trigger] wbit(0u64, c as int) by {
        assert((0u64 >> c) & 1u64 == 0u64) by (bit_vector) requires c < 64;
    }
}

/// The word whose bit `b` is `flags[base + b]` (for `base + b < n`, the others zero).
pub fn word_of(flags: &Vec<u8>, base: usize, n: usize, none: u8) -> (w: u64)
    requires base <= n, n <= flags@.len(),
    ensures forall|b: int| 0 <= b < 64 ==> #[trigger] wbit(w, b) == (base + b < n && flags@[base + b] != none),
    no_unwind
{
    let mut w: u64 = 0;
    let mut b: u64 = 0;
    proof { lemma_zero_word(); }
    while b < 64
        invariant
            base <= n, n <= flags@.len(), b <= 64,
            forall|c: u64| c < b ==> #[trigger] wbit(w, c as int) == (base + c < n && flags@[base + c] != none),
            forall|c: u64| b <= c < 64 ==> !#[trigger] wbit(w, c as int),
        decreases 64 - b,
    {
        let ghost w0 = w;
        let set = base < n && b < (n - base) as u64 && flags[base + b as usize] != none;
        if set {
            w = w | (1u64 << b);
            proof { lemma_set_bit(w0, b); }
        }
        proof {
            assert(set == (base + b < n && flags@[base + b] != none));
            assert forall|c: u64| c < b + 1 implies #[trigger] wbit(w, c as int) == (base + c < n && flags@[base + c] != none) by {
                if c < b {
                    assert(wbit(w0, c as int) == (base + c < n && flags@[base + c] != none));
                } else {
                    assert(c == b);
                    if !set { assert(!wbit(w0, b as int)); }
                }
            }
            assert forall|c: u64| b + 1 <= c < 64 implies !#[trigger] wbit(w, c as int) by {
                assert(!wbit(w0, c as int));
            }
        }
        b = b + 1;
    }
    proof {
        assert forall|bb: int| 0 <= bb < 64 implies #[trigger] wbit(w, bb) == (base + bb < n && flags@[base + bb] != none) by {
            let c = bb as u64;
            assert(wbit(w, c as int) == (base + c < n && flags@[base + c] != none));
        }
    }
    w
}

/// The word whose bit `b` is `flags[base + b] != none` for all 64 bits (`base + 64 <= flags.len()`), built
/// without branches.
pub fn word_of_full(flags: &Vec<u8>, base: usize, none: u8) -> (w: u64)
    requires base + 64 <= flags@.len(), base + 64 <= usize::MAX,
    ensures forall|b: int| 0 <= b < 64 ==> #[trigger] wbit(w, b) == (flags@[base + b] != none),
    no_unwind
{
    let mut w: u64 = 0;
    let mut b: u64 = 0;
    proof { lemma_zero_word(); }
    while b < 64
        invariant
            base + 64 <= flags@.len(), base + 64 <= usize::MAX, b <= 64,
            forall|c: u64| c < b ==> #[trigger] wbit(w, c as int) == (flags@[base + c] != none),
            forall|c: u64| b <= c < 64 ==> !#[trigger] wbit(w, c as int),
        decreases 64 - b,
    {
        let ghost w0 = w;
        let x: u64 = if flags[base + b as usize] != none { 1u64 } else { 0u64 };
        w = w | (x << b);
        proof {
            assert((((w0 | (x << b)) >> b) & 1u64 == 1u64) == (x == 1u64 || (w0 >> b) & 1u64 == 1u64)) by (bit_vector)
                requires b < 64, x <= 1;
            assert forall|c: u64| c < 64 && c != b implies wbit(w, c as int) == #[trigger] wbit(w0, c as int) by {
                assert((((w0 | (x << b)) >> c) & 1u64 == 1u64) == ((w0 >> c) & 1u64 == 1u64)) by (bit_vector)
                    requires b < 64, c < 64, c != b, x <= 1;
            }
            assert forall|c: u64| c < b + 1 implies #[trigger] wbit(w, c as int) == (flags@[base + c] != none) by {
                if c < b { assert(wbit(w0, c as int) == (flags@[base + c] != none)); } else { assert(!wbit(w0, c as int)); }
            }
            assert forall|c: u64| b + 1 <= c < 64 implies !#[trigger] wbit(w, c as int) by {
                assert(!wbit(w0, c as int));
            }
        }
        b = b + 1;
    }
    proof {
        assert forall|bb: int| 0 <= bb < 64 implies #[trigger] wbit(w, bb) == (flags@[base + bb] != none) by {
            let c = bb as u64;
            assert(wbit(w, c as int) == (flags@[base + c] != none));
        }
    }
    w
}

/// Offsets inside a range that starts at word `q`: word and bit of `64 * q + x`.
pub proof fn lemma_aligned(q: int, x: int)
    requires q >= 0, x >= 0,
    ensures (64 * q + x) / 64 == q + x / 64, (64 * q + x) % 64 == x % 64,
{
    let xq = x / 64;
    let xr = x % 64;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, 64);
    assert(64 * q + x == (q + xq) * 64 + xr) by (nonlinear_arith)
        requires x == 64 * xq + xr;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(64 * q + x, 64, q + xq, xr);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(64 * q + x, 64, q + xq, xr);
}

/// The bits of `a + b`: those of `a` below `64 * a.len()`, then those of `b`.
pub proof fn lemma_concat(a: Seq<u64>, b: Seq<u64>)
    ensures
        forall|i: int| 0 <= i < 64 * a.len() ==> #[trigger] bit_at(a + b, i) == bit_at(a, i),
        forall|i: int| 64 * a.len() <= i < 64 * (a.len() + b.len()) ==> #[trigger] bit_at(a + b, i) == bit_at(b, i - 64 * a.len()),
{
    assert forall|i: int| 0 <= i < 64 * a.len() implies #[trigger] bit_at(a + b, i) == bit_at(a, i) by {
        lemma_aligned(0, i);
        assert(i / 64 < a.len()) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 64);
        }
    }
    assert forall|i: int| 64 * a.len() <= i < 64 * (a.len() + b.len()) implies #[trigger] bit_at(a + b, i) == bit_at(b, i - 64 * a.len()) by {
        let x = i - 64 * a.len();
        lemma_aligned(a.len() as int, x);
        lemma_aligned(0, x);
        assert(x / 64 < b.len()) by { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, 64); }
        assert((a + b)[i / 64] == b[x / 64]);
    }
}

/// Fills `bits` so that bit `i` is `flags[i] != none` for `i < n`.
pub fn fill_bits(flags: &Vec<u8>, n: usize, none: u8, bits: &mut Vec<u64>)
    requires n <= flags@.len(), 64 * old(bits)@.len() >= n, 64 * old(bits)@.len() < n + 64,
    ensures
        final(bits)@.len() == old(bits)@.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] bit_at(final(bits)@, i) == (flags@[i] != none),
    no_unwind
{
    let nw = bits.len();
    let mut k: usize = 0;
    let mut pos: usize = 0;
    while k < nw
        invariant
            n <= flags@.len(), bits@.len() == nw, 64 * nw >= n, 64 * nw < n + 64, k <= nw,
            pos == if 64 * k < n { 64 * k } else { n as int },
            forall|i: int| 0 <= i < n && i < 64 * k ==> #[trigger] bit_at(bits@, i) == (flags@[i] != none),
        decreases nw - k,
    {
        let base = pos;
        let w = if n - base >= 64 { word_of_full(flags, base, none) } else { word_of(flags, base, n, none) };
        let ghost b0 = bits@;
        put(bits, k, w);
        proof {
            assert forall|i: int| 0 <= i < n && i < 64 * (k + 1) implies #[trigger] bit_at(bits@, i) == (flags@[i] != none) by {
                if i < 64 * k {
                    lemma_aligned(0, i);
                    assert(i / 64 < k) by { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 64); }
                    assert(bit_at(b0, i) == (flags@[i] != none));
                    assert(bits@[i / 64] == b0[i / 64]);
                } else {
                    lemma_aligned(k as int, i - 64 * k);
                    lemma_aligned(0, i - 64 * k);
                    assert(i / 64 == k);
                    assert(base == 64 * k);
                    assert(wbit(w, i % 64) == (base + i % 64 < n && flags@[base + i % 64] != none)) by {
                        if n - base >= 64 { assert(wbit(w, i % 64) == (flags@[base + i % 64] != none)); }
                    }
                }
            }
        }
        pos = if n - pos >= 64 { pos + 64 } else { n };
        k = k + 1;
    }
}

} // verus!
