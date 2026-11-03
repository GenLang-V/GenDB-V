//! Checked examples of the SUM/AVG capacity condition (`exec::relational::domain::sum_mass_fits`): the exact `i128`
//! boundary, conservative refusal of cancelling values, and a zero coefficient at a small scale next to a large
//! scale (the mass fits; the former row-order condition needed `10^50` to align the zero). Proved by unfolding,
//! not `by (compute)`: evaluating whole ASTs by `compute` made the pinned Verus spend minutes per example.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::relation::*;
use crate::exec::domain::fits_i128;
use crate::exec::relational::domain::*;

verus! {

pub open spec fn n(coeff: int, scale: nat) -> Val {
    Val::Num { coeff, scale }
}

pub open spec fn big() -> int { 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff }

/// One value of `i128::MAX` fits; one more unit does not.
pub proof fn pin_mass_boundary() {
    reveal_with_fuel(num_mass_at, 3);
    reveal_with_fuel(num_max_scale, 3);
    reveal_with_fuel(pow10, 1);
    let a = seq![n(big(), 0)];
    let b = a.push(n(1, 0));
    assert(a.drop_last() =~= Seq::<Val>::empty());
    assert(b.drop_last() =~= a);
    assert(num_max_scale(a) == 0 && num_max_scale(b) == 0);
    assert(num_mass_at(a, 0) == big());
    assert(num_mass_at(b, 0) == big() + 1);
    assert(sum_mass_fits(NumKind::Numeric, a));
    assert(!sum_mass_fits(NumKind::Numeric, b));
}

/// Cancelling values: the exact sum is 0, but the absolute mass exceeds `i128::MAX` (conservative `Capacity`).
pub proof fn pin_mass_cancellation() {
    reveal_with_fuel(num_mass_at, 4);
    reveal_with_fuel(num_max_scale, 4);
    reveal_with_fuel(num_sum, 4);
    reveal_with_fuel(pow10, 3);
    let a = seq![n(big(), 2)];
    let b = a.push(n(-big(), 2));
    let v = b.push(Val::Null);
    assert(a.drop_last() =~= Seq::<Val>::empty());
    assert(b.drop_last() =~= a);
    assert(v.drop_last() =~= b);
    assert(pow10(2) == 100);
    assert(pow10(0) == 1);
    assert(align(big(), 2, 2) == big());
    assert(align(-big(), 2, 2) == -big());
    assert(align(0, 0, 2) == 0);
    assert(num_sum(a) == (big(), 2nat));
    assert(num_sum(b) == (0int, 2nat));
    assert(num_sum(v) == (0int, 2nat));
    assert(num_max_scale(v) == 2);
    assert(num_mass_at(v, 2) == 2 * big());
    assert(!sum_mass_fits(NumKind::Numeric, v));
}

/// A zero coefficient at scale 0 next to `1 * 10^-50`: the result scale is 50, the mass is 1 and fits, and the
/// exact sum is `(1, 50)`; aligning the zero to scale 50 would need `10^50`, outside `i128`.
pub proof fn pin_mass_zero_alignment() {
    reveal_with_fuel(num_mass_at, 3);
    reveal_with_fuel(num_max_scale, 3);
    reveal_with_fuel(num_sum, 3);
    reveal_with_fuel(pow10, 1);
    let a = seq![n(0, 0)];
    let v = a.push(n(1, 50));
    assert(a.drop_last() =~= Seq::<Val>::empty());
    assert(v.drop_last() =~= a);
    assert(num_max_scale(v) == 50);
    assert(num_mass_at(v, 50) == 0 * pow10(50) + 1);
    assert(0 * pow10(50) == 0) by (nonlinear_arith);
    assert(sum_mass_fits(NumKind::Numeric, v));
    assert(num_sum(a) == (0int, 0nat)) by {
        assert(0 * pow10(0) == 0) by (nonlinear_arith);
    }
    assert(num_sum(v) == (0 * pow10(50) + 1, 50nat));
    assert(num_sum(v) == (1int, 50nat));
    lemma_pow10_i128_boundary();
    lemma_pow10_monotone(39, 50);
    assert(!fits_i128(pow10(50)));
}

/// Integers: the mass is the sum of absolute values; NULLs count 0.
pub proof fn pin_int_mass() {
    reveal_with_fuel(int_mass, 4);
    reveal_with_fuel(int_sum, 4);
    let a = seq![Val::Int(-5)];
    let b = a.push(Val::Null);
    let v = b.push(Val::Int(7));
    assert(a.drop_last() =~= Seq::<Val>::empty());
    assert(b.drop_last() =~= a);
    assert(v.drop_last() =~= b);
    assert(int_mass(v) == 12);
    assert(int_sum(v) == 2);
    assert(sum_mass_fits(NumKind::Int8, v));
}

} // verus!
