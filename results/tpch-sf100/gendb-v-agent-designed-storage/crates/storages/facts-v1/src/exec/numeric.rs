//! Executable `numeric` operators over `i128` coefficients and `u32` scales (a decimal is `coeff·10^-scale`):
//! powers of ten, exact `+`/`-`/`*` (`Capacity` outside `exec::domain::num_arith_fits`) and exact comparison.
use vstd::prelude::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::exec::value::*;
use crate::exec::domain::*;

verus! {

/// Three-way comparison: `-1`, `0` or `1` as `x` is below, equal to or above `y` (`sign(x - y)`).
pub fn three_way_cmp(x: i128, y: i128) -> (r: i8)
    ensures r as int == sign(x - y),
{
    if x < y { -1 } else if x == y { 0 } else { 1 }
}

/// `10^k` if it fits `i128`.
pub fn pow10_exec(k: u32) -> (r: Option<i128>)
    ensures
        match r {
            Some(p) => p as int == pow10(k as nat),
            None => !fits_i128(pow10(k as nat)),
        },
{
    let mut acc: i128 = 1;
    let mut i: u32 = 0;
    while i < k
        invariant
            i <= k,
            acc as int == pow10(i as nat),
        decreases k - i,
    {
        match acc.checked_mul(10) {
            Some(n) => {
                acc = n;
            },
            None => {
                proof {
                    lemma_pow10_positive(i as nat);
                    assert(pow10((i + 1) as nat) == 10 * pow10(i as nat));
                    lemma_pow10_monotone((i + 1) as nat, k as nat);
                }
                return None;
            },
        }
        i = i + 1;
    }
    Some(acc)
}

/// Exact numeric `+`, `-`, `*`: `(coefficient, scale)` of `spec::scalar::num_arith`, or `Capacity` exactly
/// outside `num_arith_fits`.
pub fn num_arith_exec(op: ArithOp, c1: i128, s1: u32, c2: i128, s2: u32) -> (r: Result<(i128, u32), Capacity>)
    ensures
        match r {
            Ok((c, s)) => num_arith_fits(op, c1 as int, s1 as nat, c2 as int, s2 as nat)
                && (c as int, s as nat) == num_arith(op, c1 as int, s1 as nat, c2 as int, s2 as nat),
            Err(_) => !num_arith_fits(op, c1 as int, s1 as nat, c2 as int, s2 as nat),
        },
{
    match op {
        ArithOp::Mul => {
            let c = match c1.checked_mul(c2) {
                Some(c) => c,
                None => return Err(Capacity),
            };
            let s = match s1.checked_add(s2) {
                Some(s) => s,
                None => return Err(Capacity),
            };
            Ok((c, s))
        },
        _ => {
            // Align both coefficients to the common scale `s`, then add or subtract.
            let s = if s1 >= s2 { s1 } else { s2 };
            let p1 = match pow10_exec(s - s1) {
                Some(p) => p,
                None => return Err(Capacity),
            };
            let a1 = match c1.checked_mul(p1) {
                Some(x) => x,
                None => return Err(Capacity),
            };
            let p2 = match pow10_exec(s - s2) {
                Some(p) => p,
                None => return Err(Capacity),
            };
            let a2 = match c2.checked_mul(p2) {
                Some(x) => x,
                None => return Err(Capacity),
            };
            let c = match op {
                ArithOp::Add => a1.checked_add(a2),
                _ => a1.checked_sub(a2),
            };
            match c {
                Some(c) => Ok((c, s)),
                None => Err(Capacity),
            }
        },
    }
}

/// `sign(c * 10^k - d)`, exact for all inputs (no `Capacity`): when the scaled value leaves `i128` its sign
/// decides, because `|d| <= 2^127`.
pub fn cmp_scaled(c: i128, k: u32, d: i128) -> (r: i8)
    ensures r as int == sign(c * pow10(k as nat) - d),
{
    proof {
        lemma_pow10_positive(k as nat);
    }
    match pow10_exec(k) {
        Some(p) => match c.checked_mul(p) {
            Some(x) => three_way_cmp(x, d),
            None => {
                proof {
                    if c > 0 {
                        assert(c * p > 0) by (nonlinear_arith) requires c > 0, p > 0;
                    } else if c < 0 {
                        assert(c * p < 0) by (nonlinear_arith) requires c < 0, p > 0;
                    } else {
                        assert(c * p == 0);
                    }
                }
                if c > 0 { 1 } else { -1 }
            },
        },
        None => {
            let ghost pk = pow10(k as nat);
            proof {
                // pow10(k) > i128::MAX forces k >= 39, hence pow10(k) >= 10^39 > 2^128.
                lemma_pow10_i128_boundary();
                if k <= 38 {
                    lemma_pow10_monotone(k as nat, 38);
                }
                lemma_pow10_monotone(39, k as nat);
                if c > 0 {
                    assert(c * pk >= pk) by (nonlinear_arith) requires c >= 1, pk > 0;
                } else if c < 0 {
                    assert(c * pk <= -pk) by (nonlinear_arith) requires c <= -1, pk > 0;
                }
            }
            if c > 0 { 1 } else if c < 0 { -1 } else { three_way_cmp(0, d) }
        },
    }
}

/// Exact order of two decimals (`spec::numeric::num_cmp`): the operand with the smaller scale is scaled up.
pub fn num_cmp_exec(c1: i128, s1: u32, c2: i128, s2: u32) -> (r: i8)
    ensures r as int == num_cmp(c1 as int, s1 as nat, c2 as int, s2 as nat),
{
    if s1 <= s2 {
        let r = cmp_scaled(c1, s2 - s1, c2);
        proof {
            assert(pow10(0) == 1);
            assert(align(c2 as int, s2 as nat, s2 as nat) == c2 as int);
        }
        r
    } else {
        let r = cmp_scaled(c2, s1 - s2, c1);
        proof {
            assert(pow10(0) == 1);
            assert(align(c1 as int, s1 as nat, s1 as nat) == c1 as int);
        }
        -r
    }
}

} // verus!
