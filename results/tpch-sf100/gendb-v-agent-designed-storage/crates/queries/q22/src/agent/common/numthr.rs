//! Integer threshold of a decimal comparison: for a fixed decimal `c·10^-r` and a scale `s`, the coefficient `t`
//! such that a decimal `a·10^-s` is greater than `c·10^-r` (`spec::numeric::num_cmp(a, s, c, r) > 0`) exactly when
//! `a > t`. A scan then compares integers per row instead of aligning scales.
//!
//! With `k = |s - r|`: for `r <= s` the threshold is `c·10^k` (saturated to the `i128` bounds when it leaves
//! `i128`, which only `a = i128::MIN` could tell apart); for `r > s` it is `floor(c / 10^k)` (`0` or `-1` once
//! `10^k` exceeds every `i128`), from `t·p <= c < (t + 1)·p` with `p = 10^k` (`lemma_floor_cmp`).
use vstd::prelude::*;
use crate::spec::numeric::*;
use crate::exec::numeric::pow10_exec;
use crate::link::expr::fits_i128;

verus! {

/// `a·p > c` exactly when `a > t`, for `t·p <= c < (t + 1)·p`.
pub proof fn lemma_floor_cmp(a: int, p: int, c: int, t: int)
    requires p > 0, t * p <= c, c < (t + 1) * p,
    ensures (a * p > c) == (a > t),
{
    if a > t {
        assert(a * p >= (t + 1) * p) by (nonlinear_arith) requires a >= t + 1, p > 0;
    } else {
        assert(a * p <= t * p) by (nonlinear_arith) requires a <= t, p > 0;
    }
}

/// `floor(c / p)` for `p > 0`, on `u128` divisions.
fn floor_div(c: i128, p: i128) -> (t: i128)
    requires p > 0,
    ensures t * p <= c, c < (t + 1) * p,
{
    if c >= 0 {
        let q = ((c as u128) / (p as u128)) as i128;
        proof {
            let (ci, pi) = (c as int, p as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ci, pi);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(ci, pi);
            assert(q as int == ci / pi);
            assert(pi * (ci / pi) == (ci / pi) * pi) by (nonlinear_arith);
            assert(((ci / pi) + 1) * pi == (ci / pi) * pi + pi) by (nonlinear_arith);
        }
        q
    } else {
        let m: i128 = -(c + 1);
        let q = ((m as u128) / (p as u128)) as i128;
        proof {
            let (mi, pi) = (m as int, p as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(mi, pi);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(mi, pi);
            assert(q as int == mi / pi);
            assert(pi * (mi / pi) == (mi / pi) * pi) by (nonlinear_arith);
            assert((-(mi / pi) - 1) * pi == -((mi / pi) * pi) - pi) by (nonlinear_arith);
            assert((-(mi / pi)) * pi == -((mi / pi) * pi)) by (nonlinear_arith);
            assert(q as int * pi <= mi) by (nonlinear_arith) requires q as int == mi / pi, pi * (mi / pi) + mi % pi == mi, mi % pi >= 0;
        }
        -q - 1
    }
}

/// The coefficient threshold of `num_cmp(a, s, c, r) > 0` over the coefficients `a` of `i128` above `i128::MIN`.
pub fn coeff_threshold(s: u32, c: i128, r: u32) -> (t: i128)
    ensures
        forall|a: int| i128::MIN < a <= i128::MAX ==> (#[trigger] num_cmp(a, s as nat, c as int, r as nat) > 0) == (a > t),
{
    if r <= s {
        let k = s - r;
        let ghost pk = pow10(k as nat);
        proof {
            lemma_pow10_positive(k as nat);
            assert forall|a: int| #![trigger num_cmp(a, s as nat, c as int, r as nat)]
                num_cmp(a, s as nat, c as int, r as nat) == sign(a - c * pk) by {
                assert(max_nat(s as nat, r as nat) == s as nat);
                assert((s - s) as nat == 0nat);
                assert(pow10(0) == 1);
                assert(align(a, s as nat, s as nat) == a);
                assert(align(c as int, r as nat, s as nat) == c * pk);
            }
        }
        if c == 0 {
            assert((c as int) * pk == 0) by (nonlinear_arith) requires c as int == 0;
            return 0;
        }
        let big: i128 = if c > 0 { i128::MAX } else { i128::MIN };
        proof {
            if c > 0 {
                assert(c * pk >= pk) by (nonlinear_arith) requires c >= 1, pk >= 1;
            } else {
                assert(c * pk <= -pk) by (nonlinear_arith) requires c <= -1, pk >= 1;
            }
        }
        match pow10_exec(k) {
            Some(p) => match c.checked_mul(p) {
                Some(x) => x,
                None => big,
            },
            None => big,
        }
    } else {
        let k = r - s;
        let ghost pk = pow10(k as nat);
        proof {
            lemma_pow10_positive(k as nat);
            assert forall|a: int| #![trigger num_cmp(a, s as nat, c as int, r as nat)]
                num_cmp(a, s as nat, c as int, r as nat) == sign(a * pk - c) by {
                assert(max_nat(s as nat, r as nat) == r as nat);
                assert((r - r) as nat == 0nat);
                assert(pow10(0) == 1);
                assert(align(c as int, r as nat, r as nat) == c as int);
                assert(align(a, s as nat, r as nat) == a * pk);
            }
        }
        let t = match pow10_exec(k) {
            Some(p) => floor_div(c, p),
            None => {
                proof {
                    // `10^k` is beyond `i128`, so it exceeds `|c|`.
                    assert(!fits_i128(pk));
                    assert(pk > i128::MAX);
                }
                if c >= 0 { 0 } else { -1 }
            },
        };
        proof {
            assert(t * pk <= c && c < (t + 1) * pk) by {
                if !fits_i128(pk) {
                    assert(pk > i128::MAX);
                    if c >= 0 {
                        assert(t == 0);
                        assert((t as int) * pk == 0) by (nonlinear_arith) requires t as int == 0;
                        assert((t as int + 1) * pk == pk) by (nonlinear_arith) requires t as int == 0;
                    } else {
                        assert(t == -1);
                        assert((t as int) * pk == -pk) by (nonlinear_arith) requires t as int == -1;
                        assert((t as int + 1) * pk == 0) by (nonlinear_arith) requires t as int == -1;
                    }
                }
            }
            assert forall|a: int| i128::MIN < a <= i128::MAX implies (#[trigger] num_cmp(a, s as nat, c as int, r as nat) > 0) == (a > t) by {
                lemma_floor_cmp(a, pk, c as int, t as int);
            }
        }
        t
    }
}

} // verus!
