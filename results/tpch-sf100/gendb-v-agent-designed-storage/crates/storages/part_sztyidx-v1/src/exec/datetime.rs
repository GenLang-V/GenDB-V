//! Executable date/timestamp operators (`spec::datetime`). Dates are days and timestamps microseconds since
//! 2000-01-01. Every result is exact over PostgreSQL's whole date/timestamp range (no `Capacity`): intermediates
//! are computed in `i64`/`i128` under proved bounds, and floor division is written out for negative operands
//! (Rust `/` truncates; the spec's `/` is floor division for positive divisors). Products with microseconds per
//! day use the literal `86_400_000_000i128` (`spec::limits::USECS_PER_DAY`): with the named constant the solver
//! sees a nonlinear product and cannot prove the overflow bounds.
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::value::*;
use crate::spec::datetime::*;

verus! {

// `spec::limits::{date_min, date_end}`: the `date` range in days.
const DATE_MIN_DAYS: i64 = -2451545;
const DATE_END_DAYS: i64 = 2145031949;
// `spec::limits::{timestamp_min, timestamp_end}`: the `timestamp` range in microseconds.
const TIMESTAMP_MIN_USECS: i128 = -211813488000000000;
const TIMESTAMP_END_USECS: i128 = 9223371331200000000;
// `spec::limits::unix_to_postgres_days`: days from 1970-01-01 to 2000-01-01.
const UNIX_TO_POSTGRES_DAYS: i64 = 10957;

/// Floor division and modulus by a positive divisor (Rust `/` truncates toward zero; the spec's `/` and `%`
/// are floor division and the non-negative remainder).
pub fn floor_divmod(x: i64, d: i64) -> (r: (i64, i64))
    requires
        0 < d,
    ensures
        r.0 as int == x as int / d as int,
        r.1 as int == x as int % d as int,
        r.0 * d + r.1 == x,
        0 <= r.1 < d,
        x >= 0 ==> 0 <= r.0 <= x,
        x < 0 ==> x <= r.0 < 0,
{
    if x >= 0 {
        let q = x / d;
        let m = x % d;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, d as int);
            assert(q * d + m == x) by (nonlinear_arith) requires d * q + m == x;
            assert(q <= x) by (nonlinear_arith) requires q * d + m == x, m >= 0, d >= 1, q >= 0;
        }
        (q, m)
    } else {
        let u = -(x + 1);
        let a = u / d;
        let b = u % d;
        let q = -a - 1;
        let m = d - b - 1;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(u as int, d as int);
            assert(q * d + m == x) by (nonlinear_arith)
                requires d * a + b == u, q == -a - 1, m == d - b - 1, u == -(x + 1);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x as int, d as int, q as int, m as int);
            assert(a <= u) by (nonlinear_arith) requires d * a + b == u, b >= 0, d >= 1, a >= 0;
        }
        (q, m)
    }
}

/// Year bound of the executable calendar helpers (far beyond PostgreSQL's timestamp years; month arithmetic on
/// a valid timestamp with any `i32` month count stays inside it).
pub open spec fn year_bound() -> int { 0x1_0000_0000 }

/// `spec::datetime::is_leap`.
pub fn is_leap_exec(y: i64) -> (r: bool)
    requires -year_bound() <= y <= year_bound(),
    ensures r == is_leap(y as int),
{
    let (_, r4) = floor_divmod(y, 4);
    let (_, r100) = floor_divmod(y, 100);
    let (_, r400) = floor_divmod(y, 400);
    r4 == 0 && (r100 != 0 || r400 == 0)
}

/// `spec::datetime::days_in_month`.
pub fn days_in_month_exec(y: i64, m: i64) -> (r: i64)
    requires -year_bound() <= y <= year_bound(),
    ensures r as int == days_in_month(y as int, m as int), 28 <= r <= 31,
{
    if m == 2 {
        if is_leap_exec(y) { 29 } else { 28 }
    } else if m == 4 || m == 6 || m == 9 || m == 11 {
        30
    } else {
        31
    }
}

/// `spec::datetime::date_from_civil` (days since 2000-01-01).
pub fn date_from_civil_exec(y: i64, m: i64, d: i64) -> (r: i64)
    requires
        -year_bound() <= y <= year_bound(),
        1 <= m <= 12,
        -0x10_0000 <= d <= 0x10_0000,
    ensures
        r as int == date_from_civil(y as int, m as int, d as int),
{
    let y1 = if m <= 2 { y - 1 } else { y };
    let (era, yoe) = floor_divmod(y1, 400);
    let mp = if m > 2 { m - 3 } else { m + 9 };
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    assert(era * 400 + yoe == y1);
    // 719468: days from 0000-03-01 to 1970-01-01 (Hinnant's `days_from_civil`).
    era * 146097 + doe - 719468 - UNIX_TO_POSTGRES_DAYS
}

/// Day-count bound of `civil_from_date_exec` (covers every valid timestamp's date and every valid date).
pub open spec fn day_bound() -> int { 0x1_0000_0000 }

/// `spec::datetime::civil_from_date`.
pub fn civil_from_date_exec(day: i64) -> (r: (i64, i64, i64))
    requires -day_bound() <= day <= day_bound(),
    ensures
        (r.0 as int, r.1 as int, r.2 as int) == civil_from_date(day as int),
        -0x1000_0000 <= r.0 <= 0x1000_0000,
        -0x10_0000 <= r.1 <= 0x10_0000,
        -0x10_0000 <= r.2 <= 0x10_0000,
{
    let z1 = day + UNIX_TO_POSTGRES_DAYS + 719468;
    let (era, doe) = floor_divmod(z1, 146097);
    assert(era * 146097 + doe == z1);
    assert(-0x10_0000 <= era <= 0x10_0000);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    assert(0 <= yoe <= 400);
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    assert(-200000 <= doy <= 200000);
    let (mp, _) = floor_divmod(5 * doy + 2, 153);
    assert(-10000 <= mp <= 10000);
    let (q5, _) = floor_divmod(153 * mp + 2, 5);
    let d = doy - q5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// `spec::datetime::date_valid`.
pub fn date_valid_exec(day: i64) -> (r: bool)
    ensures r == date_valid(day as int),
{
    DATE_MIN_DAYS <= day && day < DATE_END_DAYS
}

/// `spec::datetime::ts_valid` (an `i128` argument, so exact sums of timestamps and offsets can be checked).
pub fn ts_valid_exec(t: i128) -> (r: bool)
    ensures r == ts_valid(t as int),
{
    TIMESTAMP_MIN_USECS <= t && t < TIMESTAMP_END_USECS
}

/// The day (`t / usecs_per_day()`, floor division) and the microseconds of that day of a valid timestamp.
pub fn ts_day_and_time_exec(t: i64) -> (r: (i64, i64))
    requires ts_valid(t as int),
    ensures
        r.0 as int == t as int / usecs_per_day(),
        r.1 as int == t as int % usecs_per_day(),
        0 <= r.1 < USECS_PER_DAY,
        -0x100_0000 <= r.0 <= 0x1000_0000,
{
    let (day, time_of_day) = floor_divmod(t, USECS_PER_DAY);
    assert(-0x100_0000 <= day <= 0x1000_0000) by (nonlinear_arith)
        requires day * 86_400_000_000 + time_of_day == t, 0 <= time_of_day < 86_400_000_000,
            -211813488000000000 <= t < 9223371331200000000;
    (day, time_of_day)
}

/// `spec::datetime::date_to_ts` (22008 when the date is past the timestamp range).
pub fn date_to_ts_exec(day: i32) -> (r: Result<i64, SqlError>)
    ensures
        match (r, date_to_ts(day as int)) {
            (Ok(t), Ok(u)) => t as int == u,
            (Err(e), Err(f)) => e == f,
            _ => false,
        },
{
    let t = day as i128 * 86_400_000_000i128;
    if ts_valid_exec(t) { Ok(t as i64) } else { Err(SqlError::DatetimeFieldOverflow) }
}

/// `spec::datetime::ts_add_months` for a valid timestamp.
pub fn ts_add_months_exec(t: i64, months: i32) -> (r: Result<i64, SqlError>)
    requires ts_valid(t as int),
    ensures
        match (r, ts_add_months(t as int, months as int)) {
            (Ok(a), Ok(b)) => a as int == b,
            (Err(e), Err(f)) => e == f,
            _ => false,
        },
{
    // The callee postconditions carry the civil values; their bodies are not needed (keeps the query small).
    hide(civil_from_date);
    hide(date_from_civil);
    hide(days_in_month);
    let (day, time_of_day) = ts_day_and_time_exec(t);
    let ymd = civil_from_date_exec(day);
    let total = ymd.0 * 12 + (ymd.1 - 1) + months as i64;
    let (y2, m0) = floor_divmod(total, 12);
    let m2 = m0 + 1;
    let dim = days_in_month_exec(y2, m2);
    let d2 = if ymd.2 <= dim { ymd.2 } else { dim };
    let new_day = date_from_civil_exec(y2, m2, d2);
    let r = new_day as i128 * 86_400_000_000i128 + time_of_day as i128;
    if ts_valid_exec(r) { Ok(r as i64) } else { Err(SqlError::DatetimeFieldOverflow) }
}

/// `spec::datetime::ts_add_interval` for a valid timestamp.
pub fn ts_add_interval_exec(t: i64, months: i32, days: i32, micros: i64) -> (r: Result<i64, SqlError>)
    requires ts_valid(t as int),
    ensures
        match (r, ts_add_interval(t as int, months as int, days as int, micros as int)) {
            (Ok(a), Ok(b)) => a as int == b,
            (Err(e), Err(f)) => e == f,
            _ => false,
        },
{
    let t1 = if months != 0 {
        match ts_add_months_exec(t, months) {
            Ok(x) => x,
            Err(e) => return Err(e),
        }
    } else {
        t
    };
    let t2 = if days != 0 {
        let x = t1 as i128 + days as i128 * 86_400_000_000i128;
        if ts_valid_exec(x) { x as i64 } else { return Err(SqlError::DatetimeFieldOverflow) }
    } else {
        t1
    };
    let x = t2 as i128 + micros as i128;
    if ts_valid_exec(x) { Ok(x as i64) } else { Err(SqlError::DatetimeFieldOverflow) }
}

} // verus!
