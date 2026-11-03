//! An exact `i128` SUM accumulator with absolute-mass tracking (`Acc`): over a multiset of integer terms with exact
//! sum `s`, absolute mass `m` (the sum of the absolute values) and count `n`, it holds `s` and `m` exactly while
//! `m <= i128::MAX` (so no partial sum in any order overflows), and otherwise only the fact that the mass exceeds
//! `i128::MAX` (`over`, sticky); the count saturates at `u64::MAX` (`sat`). Terms are added one at a time
//! (`acc_add`) or whole accumulators merged (`acc_merge`); both are `no_unwind` and allocate nothing.
use vstd::prelude::*;
use crate::spec::numeric::abs;

verus! {

pub struct Acc {
    pub sum: i128,
    pub mass: i128,
    pub cnt: u64,
    pub over: bool,
}

/// `i128::MAX` as an integer.
pub open spec fn imax() -> int {
    0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
}

/// `n` saturated at `u64::MAX`.
pub open spec fn sat(n: int) -> int {
    if n < u64::MAX { n } else { u64::MAX as int }
}

/// `a` accumulates terms with exact sum `s`, absolute mass `m` and count `n`.
pub open spec fn acc_ok(a: Acc, s: int, m: int, n: int) -> bool {
    &&& 0 <= n
    &&& a.cnt as int == sat(n)
    &&& 0 <= m
    &&& abs(s) <= m
    &&& a.over ==> m > imax()
    &&& !a.over ==> a.sum as int == s && a.mass as int == m
}

/// The empty accumulator.
pub fn acc_zero() -> (a: Acc)
    ensures acc_ok(a, 0, 0, 0),
    no_unwind
{
    Acc { sum: 0, mass: 0, cnt: 0, over: false }
}

/// Adds the term `v` (not `i128::MIN`).
pub fn acc_add(a: &mut Acc, v: i128, Ghost(s): Ghost<int>, Ghost(m): Ghost<int>, Ghost(n): Ghost<int>)
    requires acc_ok(*old(a), s, m, n), v > i128::MIN,
    ensures acc_ok(*final(a), s + v, m + abs(v as int), n + 1),
    no_unwind
{
    let av: i128 = if v < 0 { -v } else { v };
    assert(av as int == abs(v as int));
    if a.cnt < u64::MAX {
        a.cnt = a.cnt + 1;
    }
    if !a.over {
        if a.mass > i128::MAX - av {
            a.over = true;
        } else {
            a.mass = a.mass + av;
            assert(abs(s + v) <= abs(s) + abs(v as int));
            a.sum = a.sum + v;
        }
    }
}

/// Adds the terms of `b` to `a`.
pub fn acc_merge(a: &mut Acc, b: &Acc, Ghost(s1): Ghost<int>, Ghost(m1): Ghost<int>, Ghost(n1): Ghost<int>,
    Ghost(s2): Ghost<int>, Ghost(m2): Ghost<int>, Ghost(n2): Ghost<int>)
    requires acc_ok(*old(a), s1, m1, n1), acc_ok(*b, s2, m2, n2),
    ensures acc_ok(*final(a), s1 + s2, m1 + m2, n1 + n2),
    no_unwind
{
    if a.cnt <= u64::MAX - b.cnt {
        a.cnt = a.cnt + b.cnt;
    } else {
        a.cnt = u64::MAX;
    }
    if b.over {
        a.over = true;
    } else if !a.over {
        if a.mass > i128::MAX - b.mass {
            a.over = true;
        } else {
            a.mass = a.mass + b.mass;
            assert(abs(s1 + s2) <= abs(s1) + abs(s2));
            a.sum = a.sum + b.sum;
        }
    }
}

} // verus!
