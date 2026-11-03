//! Lane masks in a `u64` word: lane `k` (0..64) is bit `k`. A word is built lane by lane in increasing order
//! (`put_lane`, or in `u32` halves with `put_lane32` and widened by `lemma_widen16` / `lemma_join32`, which compiles to
//! wider vector compares), and its set lanes are visited in increasing order by taking the lowest one (`lowest_lane`:
//! a de Bruijn multiply and a 64-entry table from `tz_table`, branch-free and `no_unwind`, unlike
//! `u64::trailing_zeros`) and clearing it (`clear_lowest`).
use vstd::prelude::*;
use vstd::std_specs::bits::{u64_trailing_zeros, axiom_u64_trailing_zeros};

verus! {

/// Lane `k` of word `x` is set.
pub open spec fn lane(x: u64, k: int) -> bool {
    (x >> (k as u64)) & 1u64 == 1u64
}

/// Every lane of `x` from `b` on is clear.
pub open spec fn clear_from(x: u64, b: int) -> bool {
    forall|k: int| b <= k < 64 ==> !#[trigger] lane(x, k)
}

/// The empty word has no set lane.
pub proof fn lemma_zero_lanes()
    ensures forall|k: int| 0 <= k < 64 ==> !#[trigger] lane(0u64, k),
{
    assert forall|k: int| 0 <= k < 64 implies !#[trigger] lane(0u64, k) by {
        let kk = k as u64;
        assert((0u64 >> kk) & 1u64 != 1u64) by (bit_vector);
    }
}

/// One lane of `x | (t << b)` (`t` in {0, 1}, `b < 64`): lane `b` is `t`, every other lane is `x`'s.
proof fn lemma_put_lane_at(x: u64, b: u64, t: u64, k: u64)
    requires b < 64, k < 64, t <= 1,
    ensures
        k != b ==> (((x | (t << b)) >> k) & 1u64 == 1u64) == ((x >> k) & 1u64 == 1u64),
        k == b && (x >> k) & 1u64 != 1u64 ==> (((x | (t << b)) >> k) & 1u64 == 1u64) == (t == 1),
{
    assert(k != b ==> (((x | (t << b)) >> k) & 1u64 == 1u64) == ((x >> k) & 1u64 == 1u64)) by (bit_vector)
        requires b < 64, k < 64, t <= 1;
    assert(k == b && (x >> k) & 1u64 != 1u64 ==> (((x | (t << b)) >> k) & 1u64 == 1u64) == (t == 1)) by (bit_vector)
        requires b < 64, k < 64, t <= 1;
}

/// `x` with lane `b` (clear in `x`) set to `t` in {0, 1}.
pub fn put_lane(x: u64, b: u64, t: u64) -> (y: u64)
    requires b < 64, t <= 1, !lane(x, b as int),
    ensures
        lane(y, b as int) == (t == 1),
        forall|k: int| 0 <= k < 64 && k != b ==> #[trigger] lane(y, k) == lane(x, k),
    no_unwind
{
    let y = x | (t << b);
    proof {
        assert forall|k: int| 0 <= k < 64 && k != b implies #[trigger] lane(y, k) == lane(x, k) by {
            lemma_put_lane_at(x, b, t, k as u64);
        }
        lemma_put_lane_at(x, b, t, b);
    }
    y
}

/// The de Bruijn sequence B(2, 6) as a word: its 64 six-bit windows `(DEBRUIJN << k) >> 58` (k < 64) are distinct.
pub const DEBRUIJN: u64 = 0x022f_dd63_cc95_386d;

/// The table slot of lane `k`: the top six bits of `DEBRUIJN << k` (the product of `DEBRUIJN` and `1 << k`).
pub open spec fn tz_slot(k: u64) -> u64 {
    (DEBRUIJN << k) >> 58u64
}

/// Slot `tz_slot(k)` of the table holds `k`, for every lane `k`.
pub open spec fn tz_table_ok(t: [u8; 64]) -> bool {
    forall|k: u64| k < 64 ==> #[trigger] t@[tz_slot(k) as int] == k
}

/// Slots are table indices, and distinct lanes have distinct slots.
proof fn lemma_tz_slots(i: u64, j: u64)
    requires i < 64, j < 64,
    ensures tz_slot(i) < 64, i != j ==> tz_slot(i) != tz_slot(j),
{
    assert((DEBRUIJN << i) >> 58u64 < 64) by (bit_vector);
    assert(i != j ==> (DEBRUIJN << i) >> 58u64 != (DEBRUIJN << j) >> 58u64) by (bit_vector)
        requires i < 64, j < 64, DEBRUIJN == 0x022f_dd63_cc95_386du64;
}

/// The lowest-lane table: slot `tz_slot(k)` set to `k` for each lane (built once, outside the workers).
pub fn tz_table() -> (t: [u8; 64])
    ensures tz_table_ok(t),
{
    let mut t: [u8; 64] = [0u8; 64];
    let mut i: u64 = 0;
    while i < 64
        invariant
            i <= 64,
            forall|k: u64| k < i ==> #[trigger] t@[tz_slot(k) as int] == k,
        decreases 64 - i,
    {
        let s = (DEBRUIJN << i) >> 58u64;
        proof {
            lemma_tz_slots(i, 0);
            assert forall|k: u64| k < i implies tz_slot(k) != tz_slot(i) by {
                lemma_tz_slots(i, k);
            }
        }
        t[s as usize] = i as u8;
        i = i + 1;
    }
    t
}

/// Index of the lowest set lane of a nonzero word, branch-free: `x & !(x - 1)` isolates the lowest set bit `1 << k`,
/// its product with `DEBRUIJN` is `DEBRUIJN << k`, and the top six bits of that select `k` in the table.
#[inline(always)]
pub fn lowest_lane(tab: &[u8; 64], x: u64) -> (t: u64)
    requires
        x != 0,
        tz_table_ok(*tab),
    ensures
        t < 64,
        lane(x, t as int),
        forall|k: int| 0 <= k < t ==> !#[trigger] lane(x, k),
    no_unwind
{
    let y = x - 1;
    let lb = x & !y;
    let s = lb.wrapping_mul(DEBRUIJN) >> 58u64;
    proof {
        // `k` is the index of the lowest set bit (vstd's specification of trailing zeros).
        let k = u64_trailing_zeros(x) as u64;
        axiom_u64_trailing_zeros(x);
        assert(lb == 1u64 << k) by (bit_vector)
            requires
                x != 0,
                k < 64,
                (x >> k) & 1u64 == 1u64,
                x << sub(64u64, k) == 0,
                add(y, 1u64) == x,
                lb == x & !y;
        assert(lb.wrapping_mul(DEBRUIJN) == DEBRUIJN << k) by (bit_vector)
            requires k < 64, lb == 1u64 << k, DEBRUIJN == 0x022f_dd63_cc95_386du64;
        lemma_tz_slots(k, 0);
        assert(s == tz_slot(k));
        assert(tab@[s as int] == k);
        assert forall|j: int| 0 <= j < k implies !#[trigger] lane(x, j) by {
            let jj = j as u64;
            assert((x >> jj) & 1u64 == 0u64);
        }
    }
    tab[s as usize] as u64
}

/// `x` with its lowest set lane `t` cleared (`x & (x - 1)`): every other lane is kept.
#[inline(always)]
pub fn clear_lowest(x: u64, Ghost(t): Ghost<u64>) -> (y: u64)
    requires
        t < 64,
        lane(x, t as int),
        forall|k: int| 0 <= k < t ==> !#[trigger] lane(x, k),
    ensures
        !lane(y, t as int),
        forall|k: int| 0 <= k < 64 && k != t ==> #[trigger] lane(y, k) == lane(x, k),
    no_unwind
{
    proof {
        let ghost tt = t;
        assert(x != 0) by (bit_vector)
            requires (x >> tt) & 1u64 == 1u64;
    }
    let z = x - 1;
    let y = x & z;
    proof {
        // The lanes below `t` are clear: `x << (64 - t)` is empty.
        assert forall|i: u64| i < t implies (x >> i) & 1u64 == 0u64 by {
            assert(!lane(x, i as int));
            assert((x >> i) & 1u64 == 0u64) by (bit_vector)
                requires (x >> i) & 1u64 != 1u64;
        }
        lemma_low_clear(x, t);
        assert forall|k: int| 0 <= k < 64 && k != t implies #[trigger] lane(y, k) == lane(x, k) by {
            let kk = k as u64;
            if k < t {
                assert(!lane(x, k));
                assert((y >> kk) & 1u64 != 1u64) by (bit_vector)
                    requires y == x & z, (x >> kk) & 1u64 != 1u64;
            } else {
                // Above the lowest set lane, `x - 1` keeps every lane.
                assert(((y >> kk) & 1u64 == 1u64) == ((x >> kk) & 1u64 == 1u64)) by (bit_vector)
                    requires y == x & z, add(z, 1u64) == x, (x >> t) & 1u64 == 1u64, x << sub(64u64, t) == 0,
                        t < kk, kk < 64;
            }
        }
        assert((y >> t) & 1u64 != 1u64) by (bit_vector)
            requires y == x & z, add(z, 1u64) == x, (x >> t) & 1u64 == 1u64, x << sub(64u64, t) == 0, t < 64;
    }
    y
}

/// Lanes below `t` all clear means `x << (64 - t)` is empty.
proof fn lemma_low_clear(x: u64, t: u64)
    requires
        t < 64,
        forall|i: u64| i < t ==> (x >> i) & 1u64 == 0u64,
    ensures x << sub(64u64, t) == 0,
    decreases t,
{
    if t > 0 {
        lemma_low_clear(x, (t - 1) as u64);
        let s = (t - 1) as u64;
        assert((x >> s) & 1u64 == 0u64);
        assert(x << sub(64u64, t) == 0) by (bit_vector)
            requires t >= 1, t < 64, s == sub(t, 1u64), x << sub(64u64, s) == 0, (x >> s) & 1u64 == 0u64;
    } else {
        assert(x << sub(64u64, 0u64) == 0) by (bit_vector);
    }
}

// ------------------------------------------------------------------------------------------------ u32 lane words

/// Lane `k` of the `u32` word `x` is set.
pub open spec fn lane32(x: u32, k: int) -> bool {
    (x >> (k as u32)) & 1u32 == 1u32
}

/// Every lane of `x` from `b` on is clear.
pub open spec fn clear_from32(x: u32, b: int) -> bool {
    forall|k: int| b <= k < 32 ==> !#[trigger] lane32(x, k)
}

/// The empty `u32` word has no set lane.
pub proof fn lemma_zero_lanes32()
    ensures forall|k: int| 0 <= k < 32 ==> !#[trigger] lane32(0u32, k),
{
    assert forall|k: int| 0 <= k < 32 implies !#[trigger] lane32(0u32, k) by {
        let kk = k as u32;
        assert((0u32 >> kk) & 1u32 != 1u32) by (bit_vector);
    }
}

/// One lane of `x | (t << b)` (`t` in {0, 1}, `b < 32`): lane `b` is `t`, every other lane is `x`'s.
proof fn lemma_put_lane32_at(x: u32, b: u32, t: u32, k: u32)
    requires b < 32, k < 32, t <= 1,
    ensures
        k != b ==> (((x | (t << b)) >> k) & 1u32 == 1u32) == ((x >> k) & 1u32 == 1u32),
        k == b && (x >> k) & 1u32 != 1u32 ==> (((x | (t << b)) >> k) & 1u32 == 1u32) == (t == 1),
{
    assert(k != b ==> (((x | (t << b)) >> k) & 1u32 == 1u32) == ((x >> k) & 1u32 == 1u32)) by (bit_vector)
        requires b < 32, k < 32, t <= 1;
    assert(k == b && (x >> k) & 1u32 != 1u32 ==> (((x | (t << b)) >> k) & 1u32 == 1u32) == (t == 1)) by (bit_vector)
        requires b < 32, k < 32, t <= 1;
}

/// `x` with lane `b` (clear in `x`) set to `t` in {0, 1}.
#[inline(always)]
pub fn put_lane32(x: u32, b: u32, t: u32) -> (y: u32)
    requires b < 32, t <= 1, !lane32(x, b as int),
    ensures
        lane32(y, b as int) == (t == 1),
        forall|k: int| 0 <= k < 32 && k != b ==> #[trigger] lane32(y, k) == lane32(x, k),
    no_unwind
{
    let y = x | (t << b);
    proof {
        assert forall|k: int| 0 <= k < 32 && k != b implies #[trigger] lane32(y, k) == lane32(x, k) by {
            lemma_put_lane32_at(x, b, t, k as u32);
        }
        lemma_put_lane32_at(x, b, t, b);
    }
    y
}

/// A `u32` word clear from lane 16 on, widened to `u64`: the same lanes below 16, none from 16 on.
pub proof fn lemma_widen16(y: u32)
    requires clear_from32(y, 16),
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] lane(y as u64, k) == lane32(y, k),
        clear_from(y as u64, 16),
{
    assert forall|k: int| 0 <= k < 16 implies #[trigger] lane(y as u64, k) == lane32(y, k) by {
        let kk = k as u64;
        let k32 = k as u32;
        assert((((y as u64) >> kk) & 1u64 == 1u64) == ((y >> k32) & 1u32 == 1u32)) by (bit_vector)
            requires kk < 16, k32 == kk as u32;
    }
    assert forall|k: int| 16 <= k < 64 implies !#[trigger] lane(y as u64, k) by {
        let kk = k as u64;
        if k < 32 {
            let k32 = k as u32;
            assert(!lane32(y, k));
            assert(((y as u64) >> kk) & 1u64 != 1u64) by (bit_vector)
                requires kk < 32, k32 == kk as u32, (y >> k32) & 1u32 != 1u32;
        } else {
            assert(((y as u64) >> kk) & 1u64 != 1u64) by (bit_vector)
                requires 32 <= kk < 64;
        }
    }
}

/// Two `u32` halves joined into one word (`lo` in lanes 0..32, `hi` in lanes 32..64).
pub proof fn lemma_join32(lo: u32, hi: u32, x: u64)
    requires x == (lo as u64) | ((hi as u64) << 32u64),
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] lane(x, k) == lane32(lo, k),
        forall|k: int| 32 <= k < 64 ==> #[trigger] lane(x, k) == lane32(hi, k - 32),
{
    assert forall|k: int| 0 <= k < 32 implies #[trigger] lane(x, k) == lane32(lo, k) by {
        let kk = k as u64;
        let k32 = k as u32;
        assert(((x >> kk) & 1u64 == 1u64) == ((lo >> k32) & 1u32 == 1u32)) by (bit_vector)
            requires x == (lo as u64) | ((hi as u64) << 32u64), kk < 32, k32 == kk as u32;
    }
    assert forall|k: int| 32 <= k < 64 implies #[trigger] lane(x, k) == lane32(hi, k - 32) by {
        let kk = k as u64;
        let k32 = (k - 32) as u32;
        assert(((x >> kk) & 1u64 == 1u64) == ((hi >> k32) & 1u32 == 1u32)) by (bit_vector)
            requires x == (lo as u64) | ((hi as u64) << 32u64), 32 <= kk < 64, k32 == sub(kk, 32u64) as u32;
    }
}

} // verus!
