//! `date` / `timestamp` semantics (proleptic Gregorian, astronomical year numbering, PostgreSQL epoch
//! 2000-01-01). Only what the fragment needs: date literals, `date -> timestamp`, exact cross-type comparison,
//! `timestamp + interval` with month/day/microsecond fields (PostgreSQL `timestamp_pl_interval`) and the civil
//! date of a day count (`EXTRACT`, `spec::fns::extract`).
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::value::*;

verus! {

/// `USECS_PER_DAY` as a mathematical integer.
pub open spec fn usecs_per_day() -> int { USECS_PER_DAY as int }

pub open spec fn is_leap(y: int) -> bool {
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

pub open spec fn days_in_month(y: int, m: int) -> int {
    if m == 2 {
        if is_leap(y) { 29 } else { 28 }
    } else if m == 4 || m == 6 || m == 9 || m == 11 {
        30
    } else {
        31
    }
}

pub open spec fn valid_ymd(y: int, m: int, d: int) -> bool {
    1 <= m <= 12 && 1 <= d <= days_in_month(y, m)
}

/// Days since 1970-01-01 of a civil date (H. Hinnant's `days_from_civil`; `/` and `%` are floor division
/// and modulus for positive divisors).
pub open spec fn unix_days_from_civil(y: int, m: int, d: int) -> int {
    let y1 = if m <= 2 { y - 1 } else { y };
    let era = y1 / 400;
    let yoe = y1 - era * 400;
    let mp = if m > 2 { m - 3 } else { m + 9 };
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}

/// Civil date of a day count since 1970-01-01 (Hinnant's `civil_from_days`).
pub open spec fn civil_from_unix_days(z: int) -> (int, int, int) {
    let z1 = z + 719468;
    let era = z1 / 146097;
    let doe = z1 - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// PostgreSQL `DateADT` (days since 2000-01-01) of a civil date.
pub open spec fn date_from_civil(y: int, m: int, d: int) -> int {
    unix_days_from_civil(y, m, d) - unix_to_postgres_days()
}

/// Civil `(year, month, day)` of a `DateADT`.
pub open spec fn civil_from_date(day: int) -> (int, int, int) {
    civil_from_unix_days(day + unix_to_postgres_days())
}

/// `day` is inside PostgreSQL's `date` range.
pub open spec fn date_valid(day: int) -> bool {
    date_min() <= day < date_end()
}

/// `t` is inside PostgreSQL's `timestamp` range.
pub open spec fn ts_valid(t: int) -> bool {
    timestamp_min() <= t < timestamp_end()
}

/// A timestamp result, or 22008 outside PostgreSQL's timestamp range.
pub open spec fn ts_result(t: int) -> Result<int, SqlError> {
    if ts_valid(t) { Ok(t) } else { Err(SqlError::DatetimeFieldOverflow) }
}

/// `date -> timestamp` (midnight); PostgreSQL `date2timestamp`.
pub open spec fn date_to_ts(day: int) -> Result<int, SqlError> {
    ts_result(day * usecs_per_day())
}

/// Exact comparison key of a date against timestamps (PostgreSQL compares `date` and `timestamp` exactly,
/// treating dates beyond the timestamp range as larger/smaller, never as an error).
pub open spec fn date_as_usecs(day: int) -> int {
    day * usecs_per_day()
}

/// `t + months` (PostgreSQL `timestamp_pl_interval`, month step): add to the civil month, clamp the day to
/// the target month's length, keep the time of day.
pub open spec fn ts_add_months(t: int, months: int) -> Result<int, SqlError> {
    let day = t / usecs_per_day();
    let tod = t % usecs_per_day();
    let ymd = civil_from_date(day);
    let total = ymd.0 * 12 + (ymd.1 - 1) + months;
    let y2 = total / 12;
    let m2 = total % 12 + 1;
    let d2 = if ymd.2 <= days_in_month(y2, m2) { ymd.2 } else { days_in_month(y2, m2) };
    ts_result(date_from_civil(y2, m2, d2) * usecs_per_day() + tod)
}

/// `timestamp + interval 'months months days days micros microseconds'`: months first, then days, then
/// microseconds, each step range-checked (22008), exactly as `timestamp_pl_interval`. Zero fields are skipped
/// as PostgreSQL does.
pub open spec fn ts_add_interval(t: int, months: int, days: int, micros: int) -> Result<int, SqlError> {
    let r1 = if months != 0 { ts_add_months(t, months) } else { Ok(t) };
    match r1 {
        Err(e) => Err(e),
        Ok(t1) => {
            let r2 = if days != 0 { ts_result(t1 + days * usecs_per_day()) } else { Ok(t1) };
            match r2 {
                Err(e) => Err(e),
                Ok(t2) => ts_result(t2 + micros),
            }
        },
    }
}

} // verus!
