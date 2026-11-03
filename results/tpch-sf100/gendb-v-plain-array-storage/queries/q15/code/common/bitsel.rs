//! Selection vectors from 64-row bitmasks: bit `j` of a mask says whether row `q + j` satisfies a condition
//! (`mask_of`); `mask_set_bit` builds such a mask one bit at a time, and `append_mask` appends the set bits, ascending,
//! as `u32` offsets to a selection buffer, extending a range filter (`selection::range_filter`) by the 64 rows.
//!
//! Bit facts are proved with the bit-vector solver: setting bit `j` of a mask whose bit `j` is clear
//! (`lemma_or_bit`), and clearing the lowest set bit with `m & (m - 1)` (`lemma_clear_lowest`).
use vstd::prelude::*;
use vstd::std_specs::bits::*;
use crate::agent::common::selection::*;

verus! {

broadcast use axiom_u64_trailing_zeros;

/// Bit `j` of `m` is set.
pub open spec fn bit_set(m: u64, j: int) -> bool {
    (m >> (j as u64)) & 1u64 == 1u64
}

/// Bit `j` of `m` says whether row `q + j` satisfies `p`, for every `j < 64`.
pub open spec fn mask_of(m: u64, q: int, p: spec_fn(int) -> bool) -> bool {
    forall|j: int| 0 <= j < 64 ==> #[trigger] bit_set(m, j) == p(q + j)
}

/// Setting bit `j` (to `b`) of a mask: bit `j` becomes `b` when it was clear, the other bits stay.
pub proof fn lemma_or_bit(m: u64, b: u64, j: u64, i: u64)
    requires j < 64, i < 64, b <= 1, (m >> j) & 1u64 == 0u64,
    ensures
        i == j ==> (((m | (b << j)) >> i) & 1u64 == 1u64) == (b == 1u64),
        i != j ==> ((m | (b << j)) >> i) & 1u64 == (m >> i) & 1u64,
{
    assert(i == j ==> (((m | (b << j)) >> i) & 1u64 == 1u64) == (b == 1u64)) by (bit_vector)
        requires j < 64, b <= 1, (m >> j) & 1u64 == 0u64;
    assert(i != j ==> ((m | (b << j)) >> i) & 1u64 == (m >> i) & 1u64) by (bit_vector)
        requires j < 64, i < 64, b <= 1;
}

/// `m & (m - 1)` clears the lowest set bit `t` of `m` (bits below `t` are clear: `m << (64 - t) == 0`).
pub proof fn lemma_clear_lowest(m: u64, t: u64, i: u64)
    requires t < 64, i < 64, (m >> t) & 1u64 == 1u64, m << sub(64, t) == 0,
    ensures
        i <= t ==> ((m & sub(m, 1)) >> i) & 1u64 == 0u64,
        i > t ==> ((m & sub(m, 1)) >> i) & 1u64 == (m >> i) & 1u64,
{
    assert(i <= t ==> ((m & sub(m, 1)) >> i) & 1u64 == 0u64) by (bit_vector)
        requires t < 64, i < 64, (m >> t) & 1u64 == 1u64, m << sub(64, t) == 0;
    assert(i > t ==> ((m & sub(m, 1)) >> i) & 1u64 == (m >> i) & 1u64) by (bit_vector)
        requires t < 64, i < 64, (m >> t) & 1u64 == 1u64, m << sub(64, t) == 0;
}

/// The bits of `m` below its lowest set bit `k` (`m << (64 - k) == 0`) are `2^k - 1`.
pub proof fn lemma_below_lowest(m: u64, k: u64)
    requires k < 64, (m >> k) & 1u64 == 1u64, m << sub(64, k) == 0,
    ensures !m & sub(m, 1) == sub(1u64 << k, 1),
{
    assert(!m & sub(m, 1) == sub(1u64 << k, 1)) by (bit_vector)
        requires k < 64, (m >> k) & 1u64 == 1u64, m << sub(64, k) == 0;
}

/// The SWAR bit count of `2^k - 1` is `k`: pair, nibble and byte counts, then the byte counts summed into the top
/// byte by three shifted additions (no carries: every byte stays below 256). The compiler turns the whole count of
/// the bits below the lowest set bit into one `tzcnt`.
pub proof fn lemma_swar_count(x: u64, k: u64, a: u64, b: u64, c: u64, d1: u64, d2: u64, d3: u64)
    requires
        k < 64,
        x == sub(1u64 << k, 1),
        a == sub(x, (x >> 1) & 0x5555_5555_5555_5555u64),
        b == add(a & 0x3333_3333_3333_3333u64, (a >> 2) & 0x3333_3333_3333_3333u64),
        c == add(b, b >> 4) & 0x0f0f_0f0f_0f0f_0f0fu64,
        d1 == add(c, c << 8),
        d2 == add(d1, d1 << 16),
        d3 == add(d2, d2 << 32),
    ensures d3 >> 56 == k,
{
    assert(d3 >> 56 == k) by (bit_vector)
        requires
            k < 64,
            x == sub(1u64 << k, 1),
            a == sub(x, (x >> 1) & 0x5555_5555_5555_5555u64),
            b == add(a & 0x3333_3333_3333_3333u64, (a >> 2) & 0x3333_3333_3333_3333u64),
            c == add(b, b >> 4) & 0x0f0f_0f0f_0f0f_0f0fu64,
            d1 == add(c, c << 8),
            d2 == add(d1, d1 << 16),
            d3 == add(d2, d2 << 32);
}

/// The index of the lowest set bit of `m != 0`: the number of bits below it, counted in parallel within the word
/// (`trailing_zeros` itself has no `no_unwind` specification, so worker bodies cannot call it).
pub fn lowest_bit(m: u64) -> (t: u32)
    requires m != 0,
    ensures t == u64_trailing_zeros(m), t < 64,
    no_unwind
{
    let ghost k = u64_trailing_zeros(m) as u64;
    proof {
        assert(k < 64);
        assert((m >> k) & 1u64 == 1u64);
        assert(m << sub(64, k) == 0);
        lemma_below_lowest(m, k);
    }
    let x = !m & (m - 1);
    proof {
        assert(((x >> 1) & 0x5555_5555_5555_5555u64) <= x) by (bit_vector);
    }
    let a = x - ((x >> 1) & 0x5555_5555_5555_5555u64);
    proof {
        assert((a & 0x3333_3333_3333_3333u64) <= 0x3333_3333_3333_3333u64) by (bit_vector);
        assert(((a >> 2) & 0x3333_3333_3333_3333u64) <= 0x3333_3333_3333_3333u64) by (bit_vector);
    }
    let b = (a & 0x3333_3333_3333_3333u64) + ((a >> 2) & 0x3333_3333_3333_3333u64);
    proof {
        assert(b <= 0x4444_4444_4444_4444u64) by (bit_vector)
            requires
                a == sub(x, (x >> 1) & 0x5555_5555_5555_5555u64),
                b == add(a & 0x3333_3333_3333_3333u64, (a >> 2) & 0x3333_3333_3333_3333u64);
        assert((b >> 4) <= b) by (bit_vector);
    }
    let c = (b + (b >> 4)) & 0x0f0f_0f0f_0f0f_0f0fu64;
    proof {
        assert(c <= 0x0f0f_0f0f_0f0f_0f0fu64) by (bit_vector) requires c == add(b, b >> 4) & 0x0f0f_0f0f_0f0f_0f0fu64;
    }
    proof {
        assert(c & 0xf0f0_f0f0_f0f0_f0f0u64 == 0) by (bit_vector) requires c == add(b, b >> 4) & 0x0f0f_0f0f_0f0f_0f0fu64;
        assert((c << 8) <= sub(0xffff_ffff_ffff_ffffu64, c)) by (bit_vector) requires c & 0xf0f0_f0f0_f0f0_f0f0u64 == 0;
    }
    let d1 = c + (c << 8);
    proof {
        assert((d1 << 16) <= sub(0xffff_ffff_ffff_ffffu64, d1)) by (bit_vector)
            requires c & 0xf0f0_f0f0_f0f0_f0f0u64 == 0, d1 == add(c, c << 8);
    }
    let d2 = d1 + (d1 << 16);
    proof {
        assert((d2 << 32) <= sub(0xffff_ffff_ffff_ffffu64, d2)) by (bit_vector)
            requires c & 0xf0f0_f0f0_f0f0_f0f0u64 == 0, d1 == add(c, c << 8), d2 == add(d1, d1 << 16);
    }
    let d3 = d2 + (d2 << 32);
    proof {
        lemma_swar_count(x, k, a, b, c, d1, d2, d3);
    }
    (d3 >> 56) as u32
}

/// A range filter does not grow over rows that do not satisfy the condition.
pub proof fn lemma_range_filter_skip(lo: int, mid: int, hi: int, p: spec_fn(int) -> bool)
    requires lo <= mid <= hi, forall|r: int| mid <= r < hi ==> !#[trigger] p(r),
    ensures range_filter(lo, hi, p) == range_filter(lo, mid, p),
    decreases hi - mid,
{
    if hi > mid {
        lemma_range_filter_skip(lo, mid, hi - 1, p);
        assert(!p(hi - 1));
    }
}

/// A range filter lists at most the rows of its range.
pub proof fn lemma_range_filter_len(lo: int, hi: int, p: spec_fn(int) -> bool)
    requires lo <= hi,
    ensures range_filter(lo, hi, p).len() <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_filter_len(lo, hi - 1, p);
    }
}

/// The mask `m` with bit `j` set to `keep` (bit `j` of `m` clear before).
pub fn mask_set_bit(m: u64, j: u64, keep: bool) -> (r: u64)
    requires j < 64, !bit_set(m, j as int),
    ensures
        bit_set(r, j as int) == keep,
        forall|i: int| 0 <= i < 64 && i != j ==> #[trigger] bit_set(r, i) == bit_set(m, i),
    no_unwind
{
    let b: u64 = if keep { 1 } else { 0 };
    let r = m | (b << j);
    proof {
        assert((j as int) as u64 == j);
        assert((m >> j) & 1u64 != 1u64 ==> (m >> j) & 1u64 == 0u64) by (bit_vector);
        lemma_or_bit(m, b, j, j);
        assert forall|i: int| 0 <= i < 64 && i != j implies #[trigger] bit_set(r, i) == bit_set(m, i) by {
            lemma_or_bit(m, b, j, i as u64);
        }
        assert(bit_set(r, j as int) == keep);
    }
    r
}

/// Appends the rows of the 64-row group at offset `off` from `start` that satisfy `p` (the set bits of `m`), as
/// offsets from `start`, to the first `k` entries of `sel`, which list the qualifying rows of `[start, start + off)`.
pub fn append_mask(m: u64, Ghost(p): Ghost<spec_fn(int) -> bool>, Ghost(start): Ghost<int>, off: u32, sel: &mut Vec<u32>,
    k: usize) -> (k2: usize)
    requires
        mask_of(m, start + off, p),
        sel_matches(old(sel)@, k as int, start, range_filter(start, start + off, p)),
        off as int + 64 <= old(sel)@.len(),
        off as int + 64 <= u32::MAX,
    ensures
        final(sel)@.len() == old(sel)@.len(),
        sel_matches(final(sel)@, k2 as int, start, range_filter(start, start + off + 64, p)),
    no_unwind
{
    let ghost q = start + off;
    let mut mm = m;
    let mut k = k;
    // `pos`: the rows `[q, q + pos)` are listed; the bits of `mm` below `pos` are clear, the others are `m`'s
    let ghost mut pos: int = 0;
    proof {
        lemma_range_filter_len(start, q, p);
    }
    while mm != 0
        invariant
            mask_of(m, q, p),
            q == start + off,
            off as int + 64 <= sel@.len(),
            off as int + 64 <= u32::MAX,
            sel@.len() == old(sel)@.len(),
            0 <= pos <= 64,
            k <= off + pos,
            forall|i: int| 0 <= i < pos ==> !#[trigger] bit_set(mm, i),
            forall|i: int| pos <= i < 64 ==> #[trigger] bit_set(mm, i) == bit_set(m, i),
            sel_matches(sel@, k as int, start, range_filter(start, q + pos, p)),
        decreases 64 - pos,
    {
        let t = lowest_bit(mm);
        proof {
            // `t < 64` is the lowest set bit of `mm`; the rows `[q + pos, q + t)` do not qualify
            assert((mm >> (t as u64)) & 1u64 == 1u64);
            assert(bit_set(mm, t as int));
            assert(t as int >= pos);
            assert forall|r: int| q + pos <= r < q + t implies !#[trigger] p(r) by {
                let i = r - q;
                assert((mm >> (i as u64)) & 1u64 == 0u64);
                assert(!bit_set(mm, i));
                assert(bit_set(m, i) == p(q + i));
            }
            lemma_range_filter_skip(start, q + pos, q + t, p);
            assert(bit_set(m, t as int) == p(q + t));
            lemma_range_filter_step(start, q + t, p);
        }
        let ghost before = sel@;
        sel[k] = off + t;
        k = k + 1;
        let ghost old_mm = mm;
        mm = mm & (mm - 1);
        proof {
            let s = range_filter(start, q + t, p);
            assert(range_filter(start, q + t + 1, p) == s.push(q + t));
            assert forall|u: int| 0 <= u < k implies start + (#[trigger] sel@[u]) as int == s.push(q + t)[u] by {
                if u < k - 1 {
                    assert(sel@[u] == before[u]);
                }
            }
            assert forall|i: int| 0 <= i < t + 1 implies !#[trigger] bit_set(mm, i) by {
                lemma_clear_lowest(old_mm, t as u64, i as u64);
            }
            assert forall|i: int| t + 1 <= i < 64 implies #[trigger] bit_set(mm, i) == bit_set(m, i) by {
                lemma_clear_lowest(old_mm, t as u64, i as u64);
                assert(bit_set(old_mm, i) == bit_set(m, i));
            }
            pos = t + 1;
        }
    }
    proof {
        // no bit of `m` at or above `pos` is set: the rest of the group does not qualify
        assert forall|r: int| q + pos <= r < q + 64 implies !#[trigger] p(r) by {
            let i = r - q;
            let x = i as u64;
            assert(0u64 >> x & 1u64 == 0u64) by (bit_vector);
            assert(!bit_set(mm, i));
            assert(bit_set(m, i) == p(q + i));
        }
        lemma_range_filter_skip(start, q + pos, q + 64, p);
    }
    k
}

} // verus!
