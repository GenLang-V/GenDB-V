//! Exact SUM accumulator with a saturating absolute mass: `sum` is the exact sum of the added terms and `mass` the
//! sum of their absolute values, both while that mass stays below `2^127` (`MASS_CAP`); beyond it `mass` sticks at
//! `MASS_CAP` (the SUM leaves `i128`, the statement's capacity condition). `any` records whether a term was added
//! (SUM of no row is NULL). `acc_ok(a, ts, ta, tc)` relates an accumulator to the exact sum `ts`, absolute mass
//! `ta` and term count `tc` it stands for; adding a term (`acc_add`) and merging two accumulators of disjoint
//! inputs (`acc_merge`) keep it.
use vstd::prelude::*;
use crate::spec::numeric::abs;

verus! {

/// `2^127 = i128::MAX + 1`: the saturation value of the absolute mass.
pub const MASS_CAP: u128 = 0x8000_0000_0000_0000_0000_0000_0000_0000;

/// A running SUM (see the module header).
#[derive(Clone, Copy)]
pub struct Acc {
    pub sum: i128,
    pub mass: u128,
    pub any: bool,
}

/// `a` stands for terms with exact sum `ts`, absolute mass `ta` and count `tc`.
pub open spec fn acc_ok(a: Acc, ts: int, ta: int, tc: int) -> bool {
    &&& 0 <= ta
    &&& -ta <= ts <= ta
    &&& 0 <= tc
    &&& a.mass as int == if ta < MASS_CAP as int { ta } else { MASS_CAP as int }
    &&& ta < MASS_CAP as int ==> a.sum as int == ts
    &&& a.any == (tc > 0)
}

/// The accumulator of no terms.
pub fn acc_new() -> (a: Acc)
    ensures acc_ok(a, 0, 0, 0),
    no_unwind
{
    Acc { sum: 0, mass: 0, any: false }
}

/// Adds the term `p` (`|p| < 2^127`).
pub fn acc_add(acc: &mut Acc, p: i128, Ghost(ts): Ghost<int>, Ghost(ta): Ghost<int>, Ghost(tc): Ghost<int>)
    requires
        acc_ok(*old(acc), ts, ta, tc),
        p > i128::MIN,
    ensures acc_ok(*final(acc), ts + p, ta + abs(p as int), tc + 1),
    no_unwind
{
    let a: u128 = if p < 0 { (-p) as u128 } else { p as u128 };
    if acc.mass >= MASS_CAP - a {
        acc.mass = MASS_CAP;
    } else {
        // Unsaturated: `|sum + p| <= mass + a < 2^127`.
        acc.mass = acc.mass + a;
        acc.sum = acc.sum + p;
    }
    acc.any = true;
}

/// Merges the accumulators of two disjoint term lists.
pub fn acc_merge(x: Acc, y: Acc, Ghost(s1): Ghost<int>, Ghost(a1): Ghost<int>, Ghost(c1): Ghost<int>,
    Ghost(s2): Ghost<int>, Ghost(a2): Ghost<int>, Ghost(c2): Ghost<int>) -> (r: Acc)
    requires acc_ok(x, s1, a1, c1), acc_ok(y, s2, a2, c2),
    ensures acc_ok(r, s1 + s2, a1 + a2, c1 + c2),
    no_unwind
{
    if x.mass >= MASS_CAP - y.mass {
        Acc { sum: 0, mass: MASS_CAP, any: x.any || y.any }
    } else {
        Acc { sum: x.sum + y.sum, mass: x.mass + y.mass, any: x.any || y.any }
    }
}

} // verus!
