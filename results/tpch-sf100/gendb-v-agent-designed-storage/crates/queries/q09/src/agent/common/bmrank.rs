//! Rank in a bitmap of `u64` words (bit `k` is bit `k % 64` of word `k / 64`, `bitlist::wbit`): `nbelow(bm, k)` is
//! the number of set bits below position `k`. `prefix_counts` stores `nbelow` at every word start (`u32`), after
//! which `rank_at` reads `nbelow(bm, k)` with one SWAR count. Set bits have distinct ranks (`lemma_nbelow_lt`), and in
//! an increasing complete listing of the set bits of `[k_lo, k_hi)` the `i`-th listed bit has rank
//! `nbelow(bm, k_lo) + i` (`lemma_list_rank`).
use vstd::prelude::*;
use crate::gendb_entry::work::put;
use super::popcnt::{bit_at, cnt_below, count_below, lemma_cnt_step};
use super::bitlist::wbit;

verus! {

/// The number of set bits of `bm` at positions `0 .. k`.
pub open spec fn nbelow(bm: Seq<u64>, k: int) -> nat
    decreases k,
{
    if k <= 0 { 0 } else { nbelow(bm, k - 1) + if wbit(bm, k - 1) { 1nat } else { 0nat } }
}

/// One more position.
pub proof fn lemma_nbelow_step(bm: Seq<u64>, k: int)
    requires k >= 0,
    ensures nbelow(bm, k + 1) == nbelow(bm, k) + if wbit(bm, k) { 1nat } else { 0nat },
{
}

/// `nbelow` never decreases, by at most one per position.
pub proof fn lemma_nbelow_mono(bm: Seq<u64>, a: int, b: int)
    requires 0 <= a <= b,
    ensures nbelow(bm, a) <= nbelow(bm, b), nbelow(bm, b) - nbelow(bm, a) <= b - a,
    decreases b - a,
{
    if a < b {
        lemma_nbelow_mono(bm, a, b - 1);
        lemma_nbelow_step(bm, b - 1);
    }
}

/// A set bit at `a` counts below every later position.
pub proof fn lemma_nbelow_lt(bm: Seq<u64>, a: int, b: int)
    requires 0 <= a < b, wbit(bm, a),
    ensures nbelow(bm, a) < nbelow(bm, b),
{
    lemma_nbelow_step(bm, a);
    lemma_nbelow_mono(bm, a + 1, b);
}

/// At most `k` set bits below `k`.
pub proof fn lemma_nbelow_le(bm: Seq<u64>, k: int)
    requires k >= 0,
    ensures nbelow(bm, k) <= k,
{
    lemma_nbelow_mono(bm, 0, k);
}

/// No set bit in `[a, b)`: the same count.
pub proof fn lemma_nbelow_flat(bm: Seq<u64>, a: int, b: int)
    requires 0 <= a <= b, forall|k: int| a <= k < b ==> !#[trigger] wbit(bm, k),
    ensures nbelow(bm, a) == nbelow(bm, b),
    decreases b - a,
{
    if a < b {
        lemma_nbelow_flat(bm, a, b - 1);
        lemma_nbelow_step(bm, b - 1);
    }
}

/// Inside word `w`: the set bits below `64 w + b` are those below the word plus the word's bits below `b`.
pub proof fn lemma_nbelow_word(bm: Seq<u64>, w: int, b: int)
    requires 0 <= w, 0 <= b <= 64,
    ensures nbelow(bm, 64 * w + b) == nbelow(bm, 64 * w) + cnt_below(bm[w], b),
    decreases b,
{
    if b > 0 {
        lemma_nbelow_word(bm, w, b - 1);
        let k = 64 * w + b - 1;
        assert(k / 64 == w && k % 64 == b - 1) by (nonlinear_arith) requires k == 64 * w + b - 1, 0 <= w, 1 <= b <= 64;
        lemma_nbelow_step(bm, k);
        lemma_cnt_step(bm[w], b - 1);
        assert(wbit(bm, k) == ((bm[w] >> ((b - 1) as u64)) & 1u64 == 1u64));
        assert(bit_at(bm[w], b - 1) == if wbit(bm, k) { 1nat } else { 0nat });
    }
}

/// `wp[w] == nbelow(bm, 64 w)` for every word start `w <= nw`.
pub open spec fn prefix_ok(bm: Seq<u64>, wp: Seq<u32>, nw: int) -> bool {
    &&& nw + 1 <= wp.len()
    &&& nw <= bm.len()
    &&& forall|w: int| 0 <= w <= nw ==> #[trigger] wp[w] as int == nbelow(bm, 64 * w)
}

/// The set-bit counts before every word start of `bm[0 .. nw]` into `wp[0 ..= nw]`.
pub fn prefix_counts(bm: &Vec<u64>, nw: usize, wp: &mut Vec<u32>)
    requires nw <= bm@.len(), nw + 1 <= old(wp)@.len(), nw * 64 <= 0xffff_ffff,
    ensures final(wp)@.len() == old(wp)@.len(), prefix_ok(bm@, final(wp)@, nw as int),
    no_unwind
{
    let mut acc: u32 = 0;
    let mut w: usize = 0;
    while w < nw
        invariant
            nw <= bm@.len(), nw + 1 <= wp@.len(), nw * 64 <= 0xffff_ffff,
            wp@.len() == old(wp)@.len(),
            w <= nw,
            acc as int == nbelow(bm@, 64 * w),
            forall|v: int| 0 <= v < w ==> #[trigger] wp@[v] as int == nbelow(bm@, 64 * v),
        decreases nw - w,
    {
        let ghost w0 = wp@;
        put(wp, w, acc);
        let c = count_below(bm[w], 64);
        proof {
            lemma_nbelow_word(bm@, w as int, 64);
            assert(64 * w + 64 == 64 * (w + 1));
            lemma_nbelow_le(bm@, 64 * (w + 1));
            assert forall|v: int| 0 <= v < w + 1 implies #[trigger] wp@[v] as int == nbelow(bm@, 64 * v) by {
                if v < w { assert(wp@[v] == w0[v]); }
            }
        }
        acc = acc + c as u32;
        w = w + 1;
    }
    put(wp, nw, acc);
}

/// `nbelow(bm, k)` from the word prefixes.
pub fn rank_at(bm: &Vec<u64>, wp: &Vec<u32>, k: usize, Ghost(nw): Ghost<int>) -> (r: usize)
    requires prefix_ok(bm@, wp@, nw), k < nw * 64,
    ensures r as int == nbelow(bm@, k as int),
    no_unwind
{
    let w = k / 64;
    let b = k % 64;
    proof {
        assert(w < nw) by (nonlinear_arith) requires w == k / 64, k < nw * 64;
        assert(k == 64 * w + b) by (nonlinear_arith) requires w == k / 64, b == k % 64;
        lemma_nbelow_word(bm@, w as int, b as int);
        lemma_nbelow_le(bm@, k as int);
    }
    let c = count_below(bm[w], b as u64);
    wp[w] as usize + c as usize
}

/// `out[0 .. n]` lists, increasing, `base + k` for every set bit `k` of `[k_lo, k_hi)` (and nothing else).
pub open spec fn listed(out: Seq<usize>, n: int, bm: Seq<u64>, k_lo: int, k_hi: int, base: int) -> bool {
    &&& 0 <= n <= out.len()
    &&& forall|i: int| 0 <= i < n ==> k_lo <= #[trigger] out[i] - base < k_hi && wbit(bm, out[i] - base)
    &&& forall|i: int, i2: int| 0 <= i < i2 < n ==> #[trigger] out[i] < #[trigger] out[i2]
    &&& forall|k: int| k_lo <= k < k_hi && #[trigger] wbit(bm, k) ==> exists|i: int| 0 <= i < n && out[i] == base + k
}

/// A complete listing has no set bit between its `i`-th entry (or `k_lo`) and the next one.
proof fn lemma_list_gap(out: Seq<usize>, n: int, bm: Seq<u64>, k_lo: int, k_hi: int, base: int, i: int, k: int)
    requires
        listed(out, n, bm, k_lo, k_hi, base), 0 <= k_lo,
        -1 <= i < n,
        (if i < 0 { k_lo } else { out[i] - base + 1 }) <= k,
        k < (if i + 1 < n { out[i + 1] - base } else { k_hi }),
    ensures !wbit(bm, k),
{
    if wbit(bm, k) {
        let i2 = choose|i2: int| 0 <= i2 < n && out[i2] == base + k;
        if i2 <= i {
            if i2 < i { assert(out[i2] < out[i]); }
        } else if i2 > i + 1 {
            assert(out[i + 1] < out[i2]);
        }
    }
}

/// The `i`-th listed bit has rank `nbelow(bm, k_lo) + i`.
proof fn lemma_list_rank_at(out: Seq<usize>, n: int, bm: Seq<u64>, k_lo: int, k_hi: int, base: int, i: int)
    requires listed(out, n, bm, k_lo, k_hi, base), 0 <= k_lo <= k_hi, 0 <= i < n,
    ensures nbelow(bm, out[i] - base) == nbelow(bm, k_lo) + i,
    decreases i,
{
    let a = if i == 0 { k_lo } else { out[i - 1] - base + 1 };
    let b = out[i] - base;
    assert forall|k: int| a <= k < b implies !#[trigger] wbit(bm, k) by {
        lemma_list_gap(out, n, bm, k_lo, k_hi, base, i - 1, k);
    }
    if i > 0 {
        lemma_list_rank_at(out, n, bm, k_lo, k_hi, base, i - 1);
        assert(out[i - 1] < out[i]);
        lemma_nbelow_step(bm, out[i - 1] - base);
    }
    lemma_nbelow_flat(bm, a, b);
}

/// The `i`-th listed bit has rank `nbelow(bm, k_lo) + i`; the range holds `n` set bits.
pub proof fn lemma_list_rank(out: Seq<usize>, n: int, bm: Seq<u64>, k_lo: int, k_hi: int, base: int)
    requires listed(out, n, bm, k_lo, k_hi, base), 0 <= k_lo <= k_hi,
    ensures
        forall|i: int| 0 <= i < n ==> nbelow(bm, #[trigger] out[i] - base) == nbelow(bm, k_lo) + i,
        nbelow(bm, k_hi) == nbelow(bm, k_lo) + n,
{
    assert forall|i: int| 0 <= i < n implies nbelow(bm, #[trigger] out[i] - base) == nbelow(bm, k_lo) + i by {
        lemma_list_rank_at(out, n, bm, k_lo, k_hi, base, i);
    }
    let a = if n == 0 { k_lo } else { out[n - 1] - base + 1 };
    assert forall|k: int| a <= k < k_hi implies !#[trigger] wbit(bm, k) by {
        lemma_list_gap(out, n, bm, k_lo, k_hi, base, n - 1, k);
    }
    if n > 0 {
        lemma_list_rank_at(out, n, bm, k_lo, k_hi, base, n - 1);
        lemma_nbelow_step(bm, out[n - 1] - base);
    }
    lemma_nbelow_flat(bm, a, k_hi);
}

} // verus!
