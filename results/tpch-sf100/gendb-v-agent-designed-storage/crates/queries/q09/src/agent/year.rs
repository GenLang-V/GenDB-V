//! `EXTRACT(YEAR FROM d)` of a date in days since 2000-01-01 (`spec::fns::extract`: the civil year of
//! `spec::datetime::civil_from_date`, astronomical years `y <= 0` reported as `y - 1`), `no_unwind` for worker
//! bodies (the framework's `civil_from_date_exec` may unwind).
use vstd::prelude::*;
use crate::spec::datetime::*;
use crate::spec::limits::*;

verus! {

/// The reported year of `EXTRACT(YEAR ...)` for a date.
pub open spec fn year_of(d: int) -> int {
    let y = civil_from_date(d).0;
    if y > 0 { y } else { y - 1 }
}

/// Floor division `x / d` (the spec's `/`) by a positive divisor, with unsigned division only.
fn fdiv(x: i64, d: u64) -> (q: i64)
    requires 0 < d <= 0x1_0000_0000, -0x1_0000_0000_0000 <= x <= 0x1_0000_0000_0000,
    ensures q as int == x as int / d as int, q * d <= x < q * d + d,
    no_unwind
{
    if x >= 0 {
        let q = ((x as u64) / d) as i64;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, d as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, d as int);
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(x as int, d as int);
            let (xi, di, qi) = (x as int, d as int, q as int);
            assert(qi * di <= xi < qi * di + di) by (nonlinear_arith)
                requires di * qi + xi % di == xi, 0 <= xi % di < di;
        }
        q
    } else {
        let u = (-(x + 1)) as u64;
        let a = (u / d) as i64;
        let q = -a - 1;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(u as int, d as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(u as int, d as int);
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(u as int, d as int);
            let r = d - u as int % d as int - 1;
            assert(q * d + r == x) by (nonlinear_arith)
                requires d * a + u as int % d as int == u as int, q == -a - 1, r == d - u as int % d as int - 1, u as int == -(x + 1);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x as int, d as int, q as int, r);
            assert(q * d <= x < q * d + d);
        }
        q
    }
}

/// `year_of(day)` for a valid date (the computation of `exec::datetime::civil_from_date_exec`, year only).
pub fn year_exec(day: i64) -> (y: i64)
    requires date_valid(day as int),
    ensures y as int == year_of(day as int),
    no_unwind
{
    let z1 = day + 10957 + 719468;
    let era = fdiv(z1, 146097);
    let doe = z1 - era * 146097;
    assert(0 <= doe < 146097);
    assert(-0x10_0000 <= era <= 0x10_0000);
    let du = doe as u64;
    let yu = (du - du / 1460 + du / 36524 - du / 146096) / 365;
    proof {
        assert(du / 1460 <= du) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(du as int, 1, 1460);
        }
    }
    let yoe = yu as i64;
    assert(0 <= yoe <= 400);
    let yy = yoe + era * 400;
    let doy = doe - (365 * yoe + ((yu / 4) as i64) - ((yu / 100) as i64));
    assert(-200000 <= doy <= 200000);
    let mp = fdiv(5 * doy + 2, 153);
    assert(-10000 <= mp <= 10000);
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { yy + 1 } else { yy };
    if y > 0 { y } else { y - 1 }
}

} // verus!
