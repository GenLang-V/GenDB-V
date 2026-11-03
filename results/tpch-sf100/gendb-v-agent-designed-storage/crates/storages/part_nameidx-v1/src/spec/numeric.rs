//! `numeric` semantics: exact decimals `coeff * 10^-scale` with PostgreSQL's result scales.
//!
//! Add/sub: scale `max(s1, s2)`; mul: scale `s1 + s2`; negation keeps the scale; every result is exact.
//! The only numeric error of these operators is PostgreSQL's format limit (absolute value at least
//! `10^131072`, 22003). Division is `spec::fns::div` and AVG `spec::aggs::avg`; the fragment has no rounding
//! casts. `pow10`, `max_nat`, `abs` and `sign` are the library's shared integer helpers.
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::value::*;

verus! {

/// `10^k`.
pub open spec fn pow10(k: nat) -> int
    decreases k,
{
    if k == 0 { 1 } else { 10 * pow10((k - 1) as nat) }
}

/// The coefficient of `coeff * 10^-from` written at scale `to >= from`.
pub open spec fn align(coeff: int, from: nat, to: nat) -> int {
    coeff * pow10((to - from) as nat)
}

pub open spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

pub open spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

/// Sign of an integer: -1, 0 or 1.
pub open spec fn sign(x: int) -> int {
    if x < 0 { -1 } else if x == 0 { 0 } else { 1 }
}

/// Number of decimal digits of `n >= 0` (0 has none).
pub open spec fn decimal_digits(n: int) -> nat
    decreases n,
{
    if n <= 0 { 0 } else { 1 + decimal_digits(n / 10) }
}

/// PostgreSQL's numeric format admits at most 131072 digits before the decimal point, i.e. absolute values
/// below `10^131072` (`coeff` has at most `131072 + scale` digits; see `lemma_decimal_digits_bound`).
pub open spec fn num_in_range(coeff: int, scale: nat) -> bool {
    decimal_digits(abs(coeff)) <= numeric_int_digits_max() + scale
}

/// A numeric result `coeff * 10^-scale`, or 22003 beyond PostgreSQL's numeric format.
pub open spec fn num_result(coeff: int, scale: nat) -> Result<Val, SqlError> {
    if num_in_range(coeff, scale) {
        Ok(Val::Num { coeff, scale })
    } else {
        Err(SqlError::NumericValueOutOfRange)
    }
}

/// Exact sum coefficient at scale `max(s1, s2)`.
pub open spec fn num_add_coeff(c1: int, s1: nat, c2: int, s2: nat) -> int {
    let s = max_nat(s1, s2);
    align(c1, s1, s) + align(c2, s2, s)
}

/// Exact difference coefficient at scale `max(s1, s2)`.
pub open spec fn num_sub_coeff(c1: int, s1: nat, c2: int, s2: nat) -> int {
    let s = max_nat(s1, s2);
    align(c1, s1, s) - align(c2, s2, s)
}

/// Exact order of two decimals: the sign of their difference.
pub open spec fn num_cmp(c1: int, s1: nat, c2: int, s2: nat) -> int {
    sign(num_sub_coeff(c1, s1, c2, s2))
}

pub proof fn lemma_pow10_positive(k: nat)
    ensures pow10(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow10_positive((k - 1) as nat);
    }
}

pub proof fn lemma_pow10_monotone(a: nat, b: nat)
    requires a <= b,
    ensures pow10(a) <= pow10(b),
    decreases b,
{
    if a < b {
        lemma_pow10_monotone(a, (b - 1) as nat);
        lemma_pow10_positive((b - 1) as nat);
    }
}

/// `10^38 < 2^127 <= 10^39`: the decimal digits an `i128` coefficient can hold.
pub proof fn lemma_pow10_i128_boundary()
    ensures
        pow10(38) < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
        pow10(39) > 2 * 0x8000_0000_0000_0000_0000_0000_0000_0000,
{
    assert(pow10(38) == 100000000000000000000000000000000000000) by (compute);
    assert(pow10(39) == 1000000000000000000000000000000000000000) by (compute);
}

/// `decimal_digits(n) <= k` exactly when `n < 10^k`.
pub proof fn lemma_decimal_digits_bound(n: int, k: nat)
    requires n >= 0,
    ensures decimal_digits(n) <= k <==> n < pow10(k),
    decreases n,
{
    lemma_pow10_positive(k);
    if n > 0 {
        if k == 0 {
            assert(decimal_digits(n) >= 1);
        } else {
            lemma_decimal_digits_bound(n / 10, (k - 1) as nat);
            assert(pow10(k) == 10 * pow10((k - 1) as nat));
        }
    }
}

/// Every coefficient of absolute value at most `2^127` is inside PostgreSQL's numeric format.
pub proof fn lemma_num_in_range_small(coeff: int, scale: nat)
    requires -0x8000_0000_0000_0000_0000_0000_0000_0000 <= coeff <= 0x8000_0000_0000_0000_0000_0000_0000_0000,
    ensures num_in_range(coeff, scale),
{
    lemma_pow10_i128_boundary();
    lemma_decimal_digits_bound(abs(coeff), 39);
}

} // verus!
