//! Exact text -> scaled-integer / day-number parsing.
//!
//! Every routine here is total and integer-only: there is no `f32`/`f64`
//! anywhere on this path, and no rounding step exists. A token that does not
//! fit the grammar exactly is rejected; it is never coerced to a nearby value.
//!
//! Two directions are provided for each type so the value check can cross the
//! encode and the decode direction rather than trusting a single routine:
//!   * `parse_*`     : text -> machine value (accumulation)
//!   * `format_*`    : machine value -> canonical text (emission)
//!   * `normalize_*` : text -> canonical text, purely lexical (no arithmetic)
//!
//! The value check (`crate::verify`) checks `format_x(parse_x(t)) ==
//! normalize_x(t)` on every single value.

/// Precision of every TPC-H decimal column in the materialized store.
pub const DECIMAL_PRECISION: u8 = 15;
/// Scale of every TPC-H decimal column in the materialized store.
pub const DECIMAL_SCALE: i8 = 2;
/// Number of integer digits admitted by `Decimal128(15, 2)`.
pub const MAX_INTEGER_DIGITS: usize = (DECIMAL_PRECISION as usize) - (DECIMAL_SCALE as usize);
/// Largest representable scaled magnitude: 9999999999999.99 -> 999999999999999.
pub const DECIMAL_MAX_SCALED: i128 = 999_999_999_999_999;

/// Why a token was rejected. Rendered into the hard error that names the
/// source file, line and column.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenError {
    /// The token had no bytes at all.
    Empty,
    /// A leading `+` is not part of the accepted grammar.
    PlusSign,
    /// The token was only a sign.
    SignOnly,
    /// A byte outside the accepted grammar, with its offset in the token.
    BadByte(u8, usize),
    /// More than one decimal point.
    MultipleDots,
    /// No digit before the decimal point.
    NoIntegerDigits,
    /// A multi-digit integer part starting with `0`.
    LeadingZero,
    /// A decimal point with no digits after it.
    EmptyFraction,
    /// More fraction digits than the fixed scale admits.
    FractionTooLong(usize),
    /// More integer digits than the fixed precision admits.
    IntegerTooLong(usize),
    /// Magnitude beyond the declared precision.
    Overflow,
    /// `-0`, `-0.00`: a signed zero is not a canonical token.
    NegativeZero,
    /// A date token that is not exactly `YYYY-MM-DD`.
    DateShape,
    /// Month outside 1..=12.
    BadMonth(u32),
    /// Day outside 1..=days_in_month.
    BadDay(u32),
    /// An integer token that does not fit `i64`.
    IntegerOutOfRange,
    /// The token was not valid UTF-8 (string columns only).
    NotUtf8,
}

impl std::fmt::Display for TokenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenError::Empty => write!(f, "empty token"),
            TokenError::PlusSign => write!(f, "leading '+' is not accepted"),
            TokenError::SignOnly => write!(f, "sign with no digits"),
            TokenError::BadByte(b, at) => {
                write!(f, "unexpected byte {:?} at offset {at}", *b as char)
            }
            TokenError::MultipleDots => write!(f, "more than one decimal point"),
            TokenError::NoIntegerDigits => write!(f, "no digit before the decimal point"),
            TokenError::LeadingZero => write!(f, "leading zero in a multi-digit integer part"),
            TokenError::EmptyFraction => write!(f, "decimal point with no fraction digits"),
            TokenError::FractionTooLong(n) => write!(
                f,
                "{n} fraction digits, scale {DECIMAL_SCALE} admits at most {DECIMAL_SCALE}"
            ),
            TokenError::IntegerTooLong(n) => write!(
                f,
                "{n} integer digits, precision {DECIMAL_PRECISION} scale {DECIMAL_SCALE} admits at most {MAX_INTEGER_DIGITS}"
            ),
            TokenError::Overflow => write!(
                f,
                "magnitude exceeds Decimal128({DECIMAL_PRECISION}, {DECIMAL_SCALE})"
            ),
            TokenError::NegativeZero => write!(f, "negative zero is not a canonical token"),
            TokenError::DateShape => write!(f, "not a YYYY-MM-DD date"),
            TokenError::BadMonth(m) => write!(f, "month {m} outside 1..=12"),
            TokenError::BadDay(d) => write!(f, "day {d} outside the month"),
            TokenError::IntegerOutOfRange => write!(f, "integer does not fit i64"),
            TokenError::NotUtf8 => write!(f, "not valid UTF-8"),
        }
    }
}

/// Lexical decomposition of a decimal token into sign, integer digits and
/// fraction digits. Performs the full grammar check and no arithmetic.
fn split_decimal(token: &[u8]) -> Result<(bool, &[u8], &[u8]), TokenError> {
    if token.is_empty() {
        return Err(TokenError::Empty);
    }
    let (negative, rest) = match token[0] {
        b'-' => (true, &token[1..]),
        b'+' => return Err(TokenError::PlusSign),
        _ => (false, token),
    };
    if rest.is_empty() {
        return Err(TokenError::SignOnly);
    }

    let mut dot: Option<usize> = None;
    for (i, &b) in rest.iter().enumerate() {
        if b == b'.' {
            if dot.is_some() {
                return Err(TokenError::MultipleDots);
            }
            dot = Some(i);
        } else if !b.is_ascii_digit() {
            return Err(TokenError::BadByte(b, i + usize::from(negative)));
        }
    }

    let (integer, fraction) = match dot {
        Some(i) => (&rest[..i], &rest[i + 1..]),
        None => (rest, &rest[rest.len()..]),
    };
    if integer.is_empty() {
        return Err(TokenError::NoIntegerDigits);
    }
    if integer.len() > 1 && integer[0] == b'0' {
        return Err(TokenError::LeadingZero);
    }
    if integer.len() > MAX_INTEGER_DIGITS {
        return Err(TokenError::IntegerTooLong(integer.len()));
    }
    if dot.is_some() && fraction.is_empty() {
        return Err(TokenError::EmptyFraction);
    }
    if fraction.len() > DECIMAL_SCALE as usize {
        return Err(TokenError::FractionTooLong(fraction.len()));
    }
    Ok((negative, integer, fraction))
}

/// Parse a decimal token into the `Decimal128(15, 2)` scaled integer.
///
/// Accepted grammar: `-? digit{1,13} ( '.' digit{1,2} )?` with no leading zero
/// in a multi-digit integer part and no negative zero.
pub fn parse_decimal(token: &[u8]) -> Result<i128, TokenError> {
    let (negative, integer, fraction) = split_decimal(token)?;

    // At most 13 integer digits, so the accumulation cannot overflow i128.
    let mut scaled: i128 = 0;
    for &b in integer {
        scaled = scaled * 10 + i128::from(b - b'0');
    }
    scaled *= 100;
    match fraction.len() {
        0 => {}
        1 => scaled += i128::from(fraction[0] - b'0') * 10,
        _ => {
            scaled += i128::from(fraction[0] - b'0') * 10 + i128::from(fraction[1] - b'0');
        }
    }
    if scaled > DECIMAL_MAX_SCALED {
        return Err(TokenError::Overflow);
    }
    if negative {
        if scaled == 0 {
            return Err(TokenError::NegativeZero);
        }
        scaled = -scaled;
    }
    Ok(scaled)
}

/// Canonical text of a decimal token, produced lexically (pad the fraction to
/// the fixed scale) into a caller-owned buffer. Never performs arithmetic on
/// the value, and never allocates.
pub fn normalize_decimal_into(token: &[u8], out: &mut String) -> Result<(), TokenError> {
    let (negative, integer, fraction) = split_decimal(token)?;
    if negative && integer.iter().all(|&b| b == b'0') && fraction.iter().all(|&b| b == b'0') {
        return Err(TokenError::NegativeZero);
    }
    out.clear();
    if negative {
        out.push('-');
    }
    for &b in integer {
        out.push(b as char);
    }
    out.push('.');
    for &b in fraction {
        out.push(b as char);
    }
    for _ in fraction.len()..DECIMAL_SCALE as usize {
        out.push('0');
    }
    Ok(())
}

/// Allocating form of [`normalize_decimal_into`].
pub fn normalize_decimal(token: &[u8]) -> Result<String, TokenError> {
    let mut out = String::with_capacity(token.len() + 3);
    normalize_decimal_into(token, &mut out)?;
    Ok(out)
}

/// Canonical text of a scaled `Decimal128(15, 2)` value, into a caller-owned
/// buffer. Integer division only; never allocates.
pub fn format_decimal_into(scaled: i128, out: &mut String) {
    use std::fmt::Write as _;
    let negative = scaled < 0;
    let magnitude = scaled.unsigned_abs();
    let units = magnitude / 100;
    let cents = magnitude % 100;
    out.clear();
    if negative {
        out.push('-');
    }
    let _ = write!(out, "{units}.{cents:02}");
}

/// Allocating form of [`format_decimal_into`].
pub fn format_decimal(scaled: i128) -> String {
    let mut out = String::with_capacity(20);
    format_decimal_into(scaled, &mut out);
    out
}

/// Parse a signed integer token into `i64`.
///
/// Accepted grammar: `-? digit+` with no leading zero in a multi-digit token
/// and no negative zero.
pub fn parse_int(token: &[u8]) -> Result<i64, TokenError> {
    if token.is_empty() {
        return Err(TokenError::Empty);
    }
    let (negative, digits) = match token[0] {
        b'-' => (true, &token[1..]),
        b'+' => return Err(TokenError::PlusSign),
        _ => (false, token),
    };
    if digits.is_empty() {
        return Err(TokenError::SignOnly);
    }
    for (i, &b) in digits.iter().enumerate() {
        if !b.is_ascii_digit() {
            return Err(TokenError::BadByte(b, i + usize::from(negative)));
        }
    }
    if digits.len() > 1 && digits[0] == b'0' {
        return Err(TokenError::LeadingZero);
    }
    // i64::MIN has 19 magnitude digits; accumulate in i128 then range-check.
    if digits.len() > 19 {
        return Err(TokenError::IntegerOutOfRange);
    }
    let mut value: i128 = 0;
    for &b in digits {
        value = value * 10 + i128::from(b - b'0');
    }
    if negative {
        if value == 0 {
            return Err(TokenError::NegativeZero);
        }
        value = -value;
    }
    i64::try_from(value).map_err(|_| TokenError::IntegerOutOfRange)
}

/// Canonical text of an `i64`, into a caller-owned buffer. Never allocates.
pub fn format_int_into(value: i64, out: &mut String) {
    use std::fmt::Write as _;
    out.clear();
    let _ = write!(out, "{value}");
}

/// Allocating form of [`format_int_into`].
pub fn format_int(value: i64) -> String {
    value.to_string()
}

const DAYS_IN_MONTH: [u32; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

fn is_leap(year: i64) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

fn days_in_month(year: i64, month: u32) -> u32 {
    if month == 2 && is_leap(year) {
        29
    } else {
        DAYS_IN_MONTH[(month - 1) as usize]
    }
}

/// Days since 1970-01-01 for a proleptic Gregorian civil date.
/// Integer-only; the classic era/day-of-era decomposition.
pub fn days_from_civil(year: i64, month: u32, day: u32) -> i64 {
    let y = if month <= 2 { year - 1 } else { year };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400; // [0, 399]
    let m = i64::from(month);
    let mp = if month > 2 { m - 3 } else { m + 9 }; // [0, 11]
    let doy = (153 * mp + 2) / 5 + i64::from(day) - 1; // [0, 365]
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy; // [0, 146096]
    era * 146_097 + doe - 719_468
}

/// Inverse of [`days_from_civil`].
pub fn civil_from_days(days: i64) -> (i64, u32, u32) {
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365; // [0, 399]
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = doy - (153 * mp + 2) / 5 + 1; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 }; // [1, 12]
    let year = if m <= 2 { y + 1 } else { y };
    (year, m as u32, d as u32)
}

/// Parse a `YYYY-MM-DD` token into Arrow `Date32` (days since 1970-01-01).
pub fn parse_date(token: &[u8]) -> Result<i32, TokenError> {
    if token.len() != 10 || token[4] != b'-' || token[7] != b'-' {
        return Err(TokenError::DateShape);
    }
    for &i in &[0usize, 1, 2, 3, 5, 6, 8, 9] {
        if !token[i].is_ascii_digit() {
            return Err(TokenError::BadByte(token[i], i));
        }
    }
    let digits = |slice: &[u8]| -> i64 {
        let mut v: i64 = 0;
        for &b in slice {
            v = v * 10 + i64::from(b - b'0');
        }
        v
    };
    let year = digits(&token[0..4]);
    let month = digits(&token[5..7]) as u32;
    let day = digits(&token[8..10]) as u32;
    if !(1..=12).contains(&month) {
        return Err(TokenError::BadMonth(month));
    }
    if day < 1 || day > days_in_month(year, month) {
        return Err(TokenError::BadDay(day));
    }
    let days = days_from_civil(year, month, day);
    i32::try_from(days).map_err(|_| TokenError::Overflow)
}

/// Canonical `YYYY-MM-DD` text of an Arrow `Date32` value, into a
/// caller-owned buffer. Never allocates.
pub fn format_date_into(days: i32, out: &mut String) {
    use std::fmt::Write as _;
    let (year, month, day) = civil_from_days(i64::from(days));
    out.clear();
    let _ = write!(out, "{year:04}-{month:02}-{day:02}");
}

/// Allocating form of [`format_date_into`].
pub fn format_date(days: i32) -> String {
    let mut out = String::with_capacity(10);
    format_date_into(days, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dec(s: &str) -> Result<i128, TokenError> {
        parse_decimal(s.as_bytes())
    }

    #[test]
    fn parses_the_shapes_present_in_tpch() {
        // MEASURED shapes from a full census of the SF1 tables: money columns
        // carry exactly two fraction digits, l_quantity carries none, and
        // acctbal columns carry negatives.
        assert_eq!(dec("21168.23"), Ok(2_116_823));
        assert_eq!(dec("0.04"), Ok(4));
        assert_eq!(dec("0.00"), Ok(0));
        assert_eq!(dec("17"), Ok(1700));
        assert_eq!(dec("5"), Ok(500));
        assert_eq!(dec("711.56"), Ok(71_156));
        assert_eq!(dec("-917.75"), Ok(-91_775));
        assert_eq!(dec("-1.23"), Ok(-123));
    }

    #[test]
    fn parses_one_fraction_digit() {
        assert_eq!(dec("1.5"), Ok(150));
        assert_eq!(dec("-0.5"), Ok(-50));
    }

    #[test]
    fn parses_maximum_magnitude() {
        assert_eq!(dec("9999999999999.99"), Ok(DECIMAL_MAX_SCALED));
        assert_eq!(dec("-9999999999999.99"), Ok(-DECIMAL_MAX_SCALED));
        assert_eq!(dec("9999999999999"), Ok(999_999_999_999_900));
    }

    #[test]
    fn rejects_beyond_precision() {
        assert_eq!(
            dec("10000000000000.00"),
            Err(TokenError::IntegerTooLong(14))
        );
        assert_eq!(
            dec("99999999999999999"),
            Err(TokenError::IntegerTooLong(17))
        );
    }

    #[test]
    fn rejects_malformed_tokens() {
        assert_eq!(dec(""), Err(TokenError::Empty));
        assert_eq!(dec("-"), Err(TokenError::SignOnly));
        assert_eq!(dec("+1.00"), Err(TokenError::PlusSign));
        assert_eq!(dec("1.234"), Err(TokenError::FractionTooLong(3)));
        assert_eq!(dec("1."), Err(TokenError::EmptyFraction));
        assert_eq!(dec(".5"), Err(TokenError::NoIntegerDigits));
        assert_eq!(dec("1.2.3"), Err(TokenError::MultipleDots));
        assert_eq!(dec("01.00"), Err(TokenError::LeadingZero));
        assert_eq!(dec("-0.00"), Err(TokenError::NegativeZero));
        assert_eq!(dec("-0"), Err(TokenError::NegativeZero));
        assert_eq!(dec("1e5"), Err(TokenError::BadByte(b'e', 1)));
        assert_eq!(dec("1 "), Err(TokenError::BadByte(b' ', 1)));
        assert_eq!(dec("NULL"), Err(TokenError::BadByte(b'N', 0)));
        assert_eq!(dec("nan"), Err(TokenError::BadByte(b'n', 0)));
        assert_eq!(dec("-1.2x"), Err(TokenError::BadByte(b'x', 4)));
    }

    #[test]
    fn decimal_round_trips_through_canonical_text() {
        for token in [
            "21168.23",
            "0.04",
            "0.00",
            "17",
            "5",
            "-917.75",
            "1.5",
            "9999999999999.99",
            "-9999999999999.99",
        ] {
            let scaled = parse_decimal(token.as_bytes()).unwrap();
            assert_eq!(
                format_decimal(scaled),
                normalize_decimal(token.as_bytes()).unwrap(),
                "round trip disagreed on {token}"
            );
        }
    }

    #[test]
    fn normalize_pads_the_fraction_without_arithmetic() {
        assert_eq!(normalize_decimal(b"17").unwrap(), "17.00");
        assert_eq!(normalize_decimal(b"1.5").unwrap(), "1.50");
        assert_eq!(normalize_decimal(b"-1.05").unwrap(), "-1.05");
        assert_eq!(normalize_decimal(b"0.04").unwrap(), "0.04");
    }

    #[test]
    fn format_decimal_pads_cents() {
        assert_eq!(format_decimal(4), "0.04");
        assert_eq!(format_decimal(0), "0.00");
        assert_eq!(format_decimal(-4), "-0.04");
        assert_eq!(format_decimal(1700), "17.00");
        assert_eq!(format_decimal(DECIMAL_MAX_SCALED), "9999999999999.99");
        assert_eq!(format_decimal(-DECIMAL_MAX_SCALED), "-9999999999999.99");
    }

    #[test]
    fn parses_integers() {
        assert_eq!(parse_int(b"0"), Ok(0));
        assert_eq!(parse_int(b"60000000"), Ok(60_000_000));
        assert_eq!(parse_int(b"-15"), Ok(-15));
        assert_eq!(parse_int(b"9223372036854775807"), Ok(i64::MAX));
        assert_eq!(parse_int(b"-9223372036854775808"), Ok(i64::MIN));
        assert_eq!(
            parse_int(b"9223372036854775808"),
            Err(TokenError::IntegerOutOfRange)
        );
        assert_eq!(parse_int(b"007"), Err(TokenError::LeadingZero));
        assert_eq!(parse_int(b"1.0"), Err(TokenError::BadByte(b'.', 1)));
        assert_eq!(parse_int(b""), Err(TokenError::Empty));
        assert_eq!(parse_int(b"-0"), Err(TokenError::NegativeZero));
    }

    #[test]
    fn parses_dates_against_hand_computed_day_numbers() {
        assert_eq!(parse_date(b"1970-01-01"), Ok(0));
        assert_eq!(parse_date(b"1970-01-02"), Ok(1));
        assert_eq!(parse_date(b"1969-12-31"), Ok(-1));
        // 1996-03-13: 26 years + leap days after the epoch.
        assert_eq!(parse_date(b"1996-03-13"), Ok(9568));
        assert_eq!(parse_date(b"1998-12-01"), Ok(10_561));
        assert_eq!(parse_date(b"1992-01-01"), Ok(8035));
        assert_eq!(parse_date(b"2000-02-29"), Ok(11_016));
    }

    #[test]
    fn rejects_malformed_dates() {
        assert_eq!(parse_date(b"1996-3-13"), Err(TokenError::DateShape));
        assert_eq!(parse_date(b"1996/03/13"), Err(TokenError::DateShape));
        assert_eq!(parse_date(b""), Err(TokenError::DateShape));
        assert_eq!(parse_date(b"1996-13-01"), Err(TokenError::BadMonth(13)));
        assert_eq!(parse_date(b"1996-00-01"), Err(TokenError::BadMonth(0)));
        assert_eq!(parse_date(b"1996-02-30"), Err(TokenError::BadDay(30)));
        assert_eq!(parse_date(b"1997-02-29"), Err(TokenError::BadDay(29)));
        assert_eq!(parse_date(b"1996-01-00"), Err(TokenError::BadDay(0)));
        assert_eq!(parse_date(b"199x-01-01"), Err(TokenError::BadByte(b'x', 3)));
    }

    #[test]
    fn leap_years_are_gregorian() {
        assert!(is_leap(1996));
        assert!(is_leap(2000));
        assert!(!is_leap(1900));
        assert!(!is_leap(1997));
        assert_eq!(
            parse_date(b"1900-02-28").map(format_date).unwrap(),
            "1900-02-28"
        );
    }

    #[test]
    fn date_round_trips_over_the_whole_tpch_window_and_beyond() {
        // 1900-01-01 .. 2100-01-01 covers every date dbgen can emit with a
        // wide margin, checked day by day in both directions.
        let start = days_from_civil(1900, 1, 1);
        let end = days_from_civil(2100, 1, 1);
        for day in start..=end {
            let d32 = i32::try_from(day).unwrap();
            let text = format_date(d32);
            assert_eq!(
                parse_date(text.as_bytes()),
                Ok(d32),
                "round trip failed at {text}"
            );
        }
    }

    #[test]
    fn integer_round_trips() {
        for v in [0i64, 1, -1, 12345, -98765, i64::MAX, i64::MIN] {
            assert_eq!(parse_int(format_int(v).as_bytes()), Ok(v));
        }
    }
}
