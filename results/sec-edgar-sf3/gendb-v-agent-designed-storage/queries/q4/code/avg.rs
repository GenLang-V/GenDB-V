//! AVG of a group from its exact sum (scale 4) and row count, with `Err` exactly outside the division's executable
//! domain (`num_div_fits`). Counts up to `i128::MAX` use `common::numdiv::num_div_exec` (the framework's, `no_unwind`); a larger count (its decimal
//! length is then 39) gives the zero quotient at display scale 56 for a zero sum, and leaves the domain otherwise
//! (the scaled dividend has at least 52 digits).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::exec::value::{EVal, view_result};
use crate::agent::common::numdiv::num_div_exec;
use crate::bridge::fns::div::lemma_nbase_first_digit_range;
use crate::bridge::order::lemma_pow10_add;
use crate::link::query::{avg_of, lemma_avg_ok};

verus! {

/// A count above `i128::MAX` (and below 2^128) has 39 decimal digits.
proof fn lemma_digits_39(c: int)
    requires 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff < c <= 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
    ensures decimal_digits(c) == 39,
{
    lemma_pow10_i128_boundary();
    assert(pow10(39) == 1000000000000000000000000000000000000000) by (compute);
    lemma_decimal_digits_bound(c, 39);
    lemma_decimal_digits_bound(c, 38);
}

/// The quotient of a zero sum by such a count: 0 at scale 56.
pub proof fn lemma_avg_zero_big(c: int)
    requires 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff < c <= 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
    ensures
        num_div_fits(0, 4, c, 0),
        avg_of(0, 4, c as nat) == (Val::Num { coeff: 0, scale: 56 }),
{
    lemma_digits_39(c);
    lemma_nbase_first_digit_range(c, 0);
    assert(nbase_weight(c, 0) == 9);
    assert(nbase_weight(0, 4) == 0);
    assert(nbase_first_digit(0, 4) == 0);
    assert(div_scale(0, 4, c, 0) == 56);
    assert(num_div_coeff(0, 4, c, 0) == 0) by {
        let x = div_round(abs(0) * pow10(56 + 0), abs(c) * pow10(4));
        assert(sign(0) == 0);
        assert(0 * sign(c) * x == 0) by (nonlinear_arith);
    }
    lemma_num_in_range_small(0, 56);
}

/// A nonzero sum by such a count leaves the division's domain.
pub proof fn lemma_avg_big_nonzero(s: int, c: int)
    requires
        s != 0, -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= s <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
        0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff < c <= 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
    ensures !num_div_fits(s, 4, c, 0),
{
    lemma_digits_39(c);
    let m = abs(s);
    let d1 = decimal_digits(m);
    lemma_pow10_i128_boundary();
    lemma_decimal_digits_bound(m, 39);
    lemma_decimal_digits_bound(m, d1);
    assert(d1 >= 1) by { if d1 == 0 { lemma_decimal_digits_bound(m, 0); assert(pow10(0) == 1); } }
    lemma_decimal_digits_bound(m, (d1 - 1) as nat);
    // m >= 10^(d1 - 1)
    assert(m >= pow10((d1 - 1) as nat));
    let w1 = nbase_weight(s, 4);
    assert(w1 == (d1 - 5) / 4);
    assert(4 * w1 <= d1 - 5) by (nonlinear_arith) requires w1 == (d1 - 5) / 4;
    assert(nbase_weight(c, 0) == 9);
    let r = div_scale(s, 4, c, 0);
    let k = r + 0 - 4;
    // r0 >= 16 - 4 (w1 - 9) >= 57 - d1, so k >= 53 - d1 >= 14 (or r is capped at 1000).
    assert(r >= 20);
    assert(pow10(52) == 10000000000000000000000000000000000000000000000000000) by (compute);
    assert(pow10(52) > u128::MAX as int);
    if r == 1000 {
        lemma_pow10_monotone(52, 996);
        lemma_pow10_positive(996);
        assert(m * pow10(996) >= pow10(996)) by (nonlinear_arith) requires m >= 1, pow10(996) >= 1;
        assert(m * pow10(k as nat) > u128::MAX as int);
    } else {
        assert(k >= 53 - d1);
        let e = (53 - d1) as nat;
        lemma_pow10_monotone(e, k as nat);
        lemma_pow10_add((d1 - 1) as nat, e);
        assert(((d1 - 1) as nat + e) as nat == 52);
        lemma_pow10_positive(e);
        lemma_pow10_positive((d1 - 1) as nat);
        assert(m * pow10(k as nat) >= pow10((d1 - 1) as nat) * pow10(e)) by (nonlinear_arith)
            requires m >= pow10((d1 - 1) as nat), pow10(k as nat) >= pow10(e), pow10(e) >= 1, pow10((d1 - 1) as nat) >= 1;
        assert(m * pow10(k as nat) > u128::MAX as int);
    }
}

/// The rounded quotient of `mm * 10^4` by a divisor of at least `10^4` is at most `mm`.
proof fn lemma_round_le(mm: int, d: int)
    requires mm >= 0, d >= 10000,
    ensures 0 <= div_round(mm * 10000, d) <= mm,
{
    let a = 2 * (mm * 10000) + d;
    let b = 2 * d;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, b);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(a, b);
    let q = a / b;
    let rm = a % b;
    assert(div_round(mm * 10000, d) == q);
    // a < b * (mm + 1): 20000 mm + d < 2 d mm + 2 d, as d mm >= 10000 mm.
    assert(a < b * (mm + 1)) by (nonlinear_arith)
        requires a == 2 * (mm * 10000) + d, b == 2 * d, d >= 10000, mm >= 0;
    assert(q <= mm) by (nonlinear_arith)
        requires a == b * q + rm, 0 <= rm, a < b * (mm + 1), b > 0;
    assert(q >= 0) by (nonlinear_arith)
        requires a == b * q + rm, rm < b, a >= 0, b > 0;
}

/// The AVG of a sum inside `i128` (scale 4) over fewer than `10^12` rows is inside the division's executable
/// domain: the quotient scale is 4 or at most `36 - digits(|sum|)`, so the scaled dividend stays below `10^32`
/// (or is the sum itself), and the rounded quotient is at most the scaled dividend.
pub proof fn lemma_avg_fits_small(s: int, c: int)
    requires
        1 <= c < 1_000_000_000_000,
        -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= s <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
    ensures num_div_fits(s, 4, c, 0),
{
    if s != 0 {
        let m = abs(s);
        let dd = decimal_digits(m);
        let e = decimal_digits(c);
        lemma_decimal_digits_bound(m, dd);
        assert(pow10(12) == 1000000000000) by (compute);
        lemma_decimal_digits_bound(c, 12);
        assert(e >= 1);
        assert(abs(c) == c);
        let w1 = nbase_weight(s, 4);
        let w2 = nbase_weight(c, 0);
        assert(w1 == (dd - 5) / 4);
        assert(w2 == (e - 1) / 4);
        assert(0 <= w2 <= 2);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(dd - 5, 4);
        vstd::arithmetic::div_mod::lemma_mod_bound(dd - 5, 4);
        assert(4 * w1 >= dd - 8);
        let r = div_scale(s, 4, c, 0);
        assert(r >= 4);
        assert(r == 4 || r <= 36 - dd);
        let k = (r - 4) as nat;
        assert(k == r + 0 - 4);
        lemma_pow10_i128_boundary();
        lemma_pow10_positive(k);
        let mm = m * pow10(k);
        assert(mm >= 0) by (nonlinear_arith) requires mm == m * pow10(k), m >= 0, pow10(k) >= 1;
        assert(mm <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff) by {
            if r == 4 {
                assert(pow10(0) == 1);
                assert(mm == m);
            } else {
                assert(dd <= 32);
                let e2 = (32 - dd) as nat;
                lemma_pow10_monotone(k, e2);
                lemma_pow10_add(dd, e2);
                assert((dd + e2) as nat == 32);
                assert(pow10(32) == 100000000000000000000000000000000) by (compute);
                lemma_pow10_positive(e2);
                assert(mm < pow10(dd) * pow10(e2)) by (nonlinear_arith)
                    requires mm == m * pow10(k), m < pow10(dd), pow10(k) <= pow10(e2), pow10(k) >= 1, m >= 0;
            }
        }
        assert(in_u128(mm));
        // The coefficient: div_round(m * 10^r, c * 10^4) with m * 10^r == mm * 10^4.
        lemma_pow10_add(k, 4);
        assert((k + 4) as nat == (r + 0) as nat);
        assert(pow10(4) == 10000) by (compute);
        assert(m * pow10((r + 0) as nat) == mm * 10000) by (nonlinear_arith)
            requires pow10((r + 0) as nat) == pow10(k) * 10000, mm == m * pow10(k);
        assert(c * pow10(4) >= 10000) by (nonlinear_arith) requires c >= 1, pow10(4) == 10000;
        lemma_round_le(mm, c * pow10(4));
        let q = div_round(abs(s) * pow10((r + 0) as nat), abs(c) * pow10(4));
        assert(0 <= q <= mm);
        assert(sign(c) == 1);
        assert(num_div_coeff(s, 4, c, 0) == sign(s) * sign(c) * q);
        assert(in_i128(num_div_coeff(s, 4, c, 0))) by {
            let (a, b) = (sign(s), sign(c));
            if s > 0 {
                assert(a * b * q == q) by (nonlinear_arith) requires a == 1, b == 1;
            } else {
                assert(a * b * q == -q) by (nonlinear_arith) requires a == -1, b == 1;
            }
        }
    }
}

/// The AVG of a group of `cnt >= 1` rows with exact sum `sum` at scale 4.
pub fn avg_eval(sum: i128, cnt: u128) -> (r: Result<EVal, ()>)
    requires cnt >= 1, sum > i128::MIN,
    ensures
        r matches Ok(v) ==> num_div_fits(sum as int, 4, cnt as int, 0) && v@ == avg_of(sum as int, 4, cnt as nat),
        r is Err ==> !num_div_fits(sum as int, 4, cnt as int, 0),
    no_unwind
{
    if cnt <= i128::MAX as u128 {
        match num_div_exec(sum, 4, cnt as i128, 0) {
            Ok(Ok(v)) => {
                proof { lemma_avg_ok(sum as int, 4, cnt as int); }
                Ok(v)
            },
            Ok(Err(_)) => {
                proof { lemma_avg_ok(sum as int, 4, cnt as int); }
                Err(())
            },
            Err(_) => Err(()),
        }
    } else if sum == 0 {
        proof { lemma_avg_zero_big(cnt as int); }
        Ok(EVal::Num { coeff: 0, scale: 56 })
    } else {
        proof { lemma_avg_big_nonzero(sum as int, cnt as int); }
        Err(())
    }
}

} // verus!
