//! A saturating SUM/COUNT accumulator: the count saturated at `2^63` (one past the largest int8), the absolute mass
//! saturated at `2^127` (one past `i128::MAX`), and the exact sum whenever the mass is below `2^127` (then every
//! partial sum fits `i128`, in any order of additions).
//!
//! `acc_ok(a, cnt, sum, mass)` relates an accumulator to the exact count, sum and mass it stands for; additions and
//! merges keep it, so a saturated field reports "beyond the limit" exactly.
use vstd::prelude::*;

verus! {

/// One past the largest int8 count.
pub const CCAP: u64 = 0x8000_0000_0000_0000u64;

/// One past `i128::MAX`.
pub const MCAP: u128 = 0x8000_0000_0000_0000_0000_0000_0000_0000u128;

/// Count (`.0`), sum (`.1`) and absolute mass (`.2`) of a set of values. A tuple of integers, so a vector of
/// zero accumulators is allocated zeroed (lazily, by the kernel) instead of being written element by element.
pub type Acc = (u64, i128, u128);

pub open spec fn min_int(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn iabs(x: int) -> int {
    if x < 0 { -x } else { x }
}

/// `a` stands for the exact count `cnt`, sum `sum` and mass `mass`.
pub open spec fn acc_ok(a: Acc, cnt: int, sum: int, mass: int) -> bool {
    &&& a.0 as int == min_int(cnt, CCAP as int)
    &&& a.2 as int == min_int(mass, MCAP as int)
    &&& (mass < MCAP as int ==> a.1 as int == sum)
}

/// The exact quantities an accumulator stands for are consistent: a count and a mass are non-negative, and the
/// mass bounds the sum.
pub open spec fn acc_sane(cnt: int, sum: int, mass: int) -> bool {
    0 <= cnt && 0 <= mass && iabs(sum) <= mass
}

/// The empty accumulator.
pub fn acc_zero() -> (a: Acc)
    ensures acc_ok(a, 0, 0, 0),
    no_unwind
{
    (0u64, 0i128, 0u128)
}

/// `|v|` as a `u128`.
#[inline(always)]
pub fn uabs(v: i128) -> (r: u128)
    ensures r as int == iabs(v as int),
    no_unwind
{
    if v >= 0 { v as u128 } else { ((-(v + 1)) as u128) + 1 }
}

/// `min(a + b, cap)` for `a, b <= cap`.
#[inline(always)]
fn sat_add_u64(a: u64, b: u64, cap: u64) -> (r: u64)
    requires a <= cap, b <= cap, cap <= CCAP,
    ensures r as int == min_int(a + b, cap as int),
    no_unwind
{
    if a >= cap - b { cap } else { a + b }
}

#[inline(always)]
fn sat_add_u128(a: u128, b: u128, cap: u128) -> (r: u128)
    requires a <= cap, b <= cap, cap <= MCAP,
    ensures r as int == min_int(a + b, cap as int),
    no_unwind
{
    if a >= cap - b { cap } else { a + b }
}

/// One more value.
#[inline(always)]
pub fn acc_add(a: Acc, v: i128, Ghost(cnt): Ghost<int>, Ghost(sum): Ghost<int>, Ghost(mass): Ghost<int>) -> (r: Acc)
    requires acc_ok(a, cnt, sum, mass), acc_sane(cnt, sum, mass),
    ensures
        acc_ok(r, cnt + 1, sum + v, mass + iabs(v as int)),
        acc_sane(cnt + 1, sum + v, mass + iabs(v as int)),
    no_unwind
{
    let av = uabs(v);
    let c = sat_add_u64(a.0, 1, CCAP);
    let ma = if av >= MCAP { MCAP } else { av };
    let m = sat_add_u128(a.2, ma, MCAP);
    proof {
        assert(min_int(mass + iabs(v as int), MCAP as int) == min_int(a.2 + ma, MCAP as int));
    }
    let s = if m < MCAP {
        proof {
            assert(mass < MCAP as int);
            assert(iabs(sum + v) <= mass + iabs(v as int));
        }
        a.1 + v
    } else {
        a.1
    };
    (c, s, m)
}

/// The union of two disjoint sets of values.
#[inline(always)]
pub fn acc_merge(a: Acc, b: Acc, Ghost(c1): Ghost<int>, Ghost(s1): Ghost<int>, Ghost(m1): Ghost<int>,
    Ghost(c2): Ghost<int>, Ghost(s2): Ghost<int>, Ghost(m2): Ghost<int>) -> (r: Acc)
    requires acc_ok(a, c1, s1, m1), acc_sane(c1, s1, m1), acc_ok(b, c2, s2, m2), acc_sane(c2, s2, m2),
    ensures acc_ok(r, c1 + c2, s1 + s2, m1 + m2), acc_sane(c1 + c2, s1 + s2, m1 + m2),
    no_unwind
{
    let c = sat_add_u64(a.0, b.0, CCAP);
    let m = sat_add_u128(a.2, b.2, MCAP);
    let s = if m < MCAP {
        proof {
            assert(m1 < MCAP as int && m2 < MCAP as int);
            assert(iabs(s1 + s2) <= m1 + m2);
        }
        a.1 + b.1
    } else {
        a.1
    };
    (c, s, m)
}

} // verus!
