//! `$2 + INTERVAL '1' YEAR` never leaves the timestamp range for a `$2` of the declared domain
//! (`0001-01-01 .. 9999-12-31`): `lemma_hi_ts_ok`. The proof bounds every intermediate of `ts_add_months`
//! (`civil_from_date`, the month arithmetic and `date_from_civil`) by interval arithmetic over floor divisions;
//! the bounds are loose (the result day lies in `-1.33M .. 3.66M`, the timestamp range spans `-2.45M .. 106M` days).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::datetime::*;
use crate::spec::limits::*;
use crate::query::{param_domain, param_typed};
use super::nf::*;

verus! {

/// Floor division by a positive constant keeps bounds.
proof fn lemma_div_bounds(x: int, lo: int, hi: int, d: int)
    requires lo <= x <= hi, d > 0,
    ensures lo / d <= x / d <= hi / d,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(lo, x, d);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x, hi, d);
}

/// The fundamental floor-division facts.
proof fn lemma_divmod(x: int, d: int)
    requires d > 0,
    ensures x == (x / d) * d + x % d, 0 <= x % d < d,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, d);
    vstd::arithmetic::div_mod::lemma_mod_bound(x, d);
    assert(d * (x / d) == (x / d) * d) by (nonlinear_arith);
}

/// Bounds of `civil_from_unix_days(z)` for `z + 719468` in `0 .. 4_000_000`.
proof fn lemma_civil_bounds(z: int)
    requires 0 <= z + 719468 <= 4_000_000,
    ensures ({
        let r = civil_from_unix_days(z);
        &&& -1 <= r.0 <= 11202
        &&& -4800 <= r.1 <= 4800
        &&& -300000 <= r.2 <= 300000
    }),
{
    let z1 = z + 719468;
    let era = z1 / 146097;
    lemma_div_bounds(z1, 0, 4_000_000, 146097);
    assert(4_000_000int / 146097 == 27);
    assert(0 <= era <= 27);
    let doe = z1 - era * 146097;
    lemma_divmod(z1, 146097);
    assert(0 <= doe < 146097);
    let a = doe / 1460;
    let b = doe / 36524;
    let c = doe / 146096;
    lemma_div_bounds(doe, 0, 146096, 1460);
    lemma_div_bounds(doe, 0, 146096, 36524);
    lemma_div_bounds(doe, 0, 146096, 146096);
    lemma_divmod(doe, 1460);
    assert(a <= doe) by (nonlinear_arith) requires doe == a * 1460 + doe % 1460, doe % 1460 >= 0, a >= 0;
    assert(146096int / 1460 == 100 && 146096int / 36524 == 4 && 146096int / 146096 == 1);
    let num = doe - a + b - c;
    assert(-1 <= num <= 146101);
    let yoe = num / 365;
    lemma_div_bounds(num, -1, 146101, 365);
    assert(-1int / 365 == -1 && 146101int / 365 == 400);
    assert(-1 <= yoe <= 400);
    let y = yoe + era * 400;
    assert(-1 <= y <= 11200);
    let q4 = yoe / 4;
    let q100 = yoe / 100;
    lemma_div_bounds(yoe, -1, 400, 4);
    lemma_div_bounds(yoe, -1, 400, 100);
    assert(-1int / 4 == -1 && 400int / 4 == 100 && -1int / 100 == -1 && 400int / 100 == 4);
    let doy = doe - (365 * yoe + q4 - q100);
    assert(-146600 <= doy <= 146500);
    let mp = (5 * doy + 2) / 153;
    lemma_div_bounds(5 * doy + 2, -733000, 732502, 153);
    assert(-733000int / 153 == -4791 && 732502int / 153 == 4787);
    assert(-4791 <= mp <= 4787);
    let t = (153 * mp + 2) / 5;
    lemma_div_bounds(153 * mp + 2, -733021, 732413, 5);
    assert(-733021int / 5 == -146605 && 732413int / 5 == 146482);
    let d = doy - t + 1;
    assert(-300000 <= d <= 300000);
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    assert(-4800 <= m <= 4800);
    let r = civil_from_unix_days(z);
    assert(r == (if m <= 2 { y + 1 } else { y }, m, d));
}

/// Bounds of `unix_days_from_civil(y, m, d)` for a year in `-500 .. 12000`, a month in `1 .. 12` and a day in
/// `-300000 .. 31`.
proof fn lemma_days_bounds(y: int, m: int, d: int)
    requires -500 <= y <= 12000, 1 <= m <= 12, -300000 <= d <= 31,
    ensures -2_000_000 <= unix_days_from_civil(y, m, d) <= 5_000_000,
{
    let y1 = if m <= 2 { y - 1 } else { y };
    let era = y1 / 400;
    lemma_div_bounds(y1, -501, 12000, 400);
    assert(-501int / 400 == -2 && 12000int / 400 == 30);
    let yoe = y1 - era * 400;
    lemma_divmod(y1, 400);
    assert(0 <= yoe < 400);
    let mp = if m > 2 { m - 3 } else { m + 9 };
    assert(0 <= mp <= 11);
    let t = (153 * mp + 2) / 5;
    lemma_div_bounds(153 * mp + 2, 2, 1685, 5);
    assert(2int / 5 == 0 && 1685int / 5 == 337);
    let doy = t + d - 1;
    let q4 = yoe / 4;
    let q100 = yoe / 100;
    lemma_div_bounds(yoe, 0, 399, 4);
    lemma_div_bounds(yoe, 0, 399, 100);
    assert(399int / 4 == 99 && 399int / 100 == 3);
    let doe = yoe * 365 + q4 - q100 + doy;
    assert(-300001 - 3 <= doe <= 399 * 365 + 99 + 367);
    assert(unix_days_from_civil(y, m, d) == era * 146097 + doe - 719468);
}

/// The day and the date bounds of the domain.
pub proof fn lemma_domain_days()
    ensures
        date_from_civil(1, 1, 1) == -730119,
        date_from_civil(9999, 12, 31) == 2921939,
{
    assert(date_from_civil(1, 1, 1) == -730119) by (compute);
    assert(date_from_civil(9999, 12, 31) == 2921939) by (compute);
}

/// `$2 + INTERVAL '1' YEAR` is a timestamp in range, the midnight of some day `d1`.
pub proof fn lemma_hi_ts_ok(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        date_to_ts(d0_of(ps)) == Ok::<int, SqlError>(d0_of(ps) * usecs_per_day()),
        hi_ts(ps) is Ok,
        hi_ts(ps)->Ok_0 % usecs_per_day() == 0,
{
    let u = usecs_per_day();
    assert(u == 86_400_000_000);
    lemma_domain_days();
    let d0 = d0_of(ps);
    assert(-730119 <= d0 <= 2921939);
    assert(timestamp_min() <= d0 * u < timestamp_end()) by (nonlinear_arith)
        requires -730119 <= d0 <= 2921939, u == 86_400_000_000,
            timestamp_min() == -211813488000000000, timestamp_end() == 9223371331200000000;
    let t0 = d0 * u;
    assert(date_to_ts(d0) == Ok::<int, SqlError>(t0));
    // ts_add_months(t0, 12)
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(d0, u);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(d0, u);
    assert(t0 / u == d0) by {
        assert(u * d0 == d0 * u) by (nonlinear_arith);
    }
    assert(t0 % u == 0);
    let ymd = civil_from_date(d0);
    lemma_civil_bounds(d0 + unix_to_postgres_days());
    let total = ymd.0 * 12 + (ymd.1 - 1) + 12;
    assert(-12 - 4801 + 12 <= total <= 11202 * 12 + 4799 + 12);
    let y2 = total / 12;
    let m2 = total % 12 + 1;
    lemma_div_bounds(total, -4801, 139235, 12);
    assert(-4801int / 12 == -401 && 139235int / 12 == 11602);
    lemma_divmod(total, 12);
    assert(1 <= m2 <= 12);
    let d2 = if ymd.2 <= days_in_month(y2, m2) { ymd.2 } else { days_in_month(y2, m2) };
    assert(days_in_month(y2, m2) <= 31);
    lemma_days_bounds(y2, m2, d2);
    let k = date_from_civil(y2, m2, d2);
    assert(-2_011_000 <= k <= 5_000_000);
    assert(timestamp_min() <= k * u + 0 < timestamp_end()) by (nonlinear_arith)
        requires -2_011_000 <= k <= 5_000_000, u == 86_400_000_000,
            timestamp_min() == -211813488000000000, timestamp_end() == 9223371331200000000;
    assert(ts_add_months(t0, 12) == Ok::<int, SqlError>(k * u));
    assert(ts_add_interval(t0, 12, 0, 0) == Ok::<int, SqlError>(k * u));
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(k, u);
}

} // verus!
