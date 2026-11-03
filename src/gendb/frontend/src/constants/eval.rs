//! Evaluation of one literal-only expression or condition, exactly as SQLSpec defines it: a transcription of
//! `spec::eval::{lit_val, eval_expr, eval_pred}` and the operators of `spec::{scalar, int, numeric, datetime}`
//! (functions: `super::functions`), on the machine representation of SQLSpec's executable interpreter.
//!
//! Children are evaluated left to right and the first stop is the outcome, as in `spec::eval`. `Capacity` arises
//! exactly where the executable interpreter's domain predicates fail (`exec::domain`): numeric `+ - *` and unary
//! minus need their aligned operands, powers of ten and results in `i128` (`num_arith_fits`, `neg_fits`), numeric
//! division `spec::fns::div::num_div_fits`. Everything else is exact here as there: integer arithmetic in `i128`, dates
//! and timestamps in `i128` intermediates over PostgreSQL's whole range, exact comparisons.

use super::functions::apply_fn;
use crate::ast::{valid_ymd, FieldValue, Node};
use std::cmp::Ordering;

/// `USECS_PER_DAY` (`spec::limits`).
pub(super) const USECS_PER_DAY: i128 = 86_400_000_000;
/// `int4` range (`spec::limits`).
pub(super) const INT4_MIN: i128 = -0x8000_0000;
pub(super) const INT4_MAX: i128 = 0x7fff_ffff;
/// Days from 1970-01-01 to the PostgreSQL epoch 2000-01-01 (`unix_to_postgres_days`).
const UNIX_TO_POSTGRES_DAYS: i128 = 10957;
/// `date` range `[date_min, date_end)` and `timestamp` range `[timestamp_min, timestamp_end)` (`spec::limits`).
const DATE_MIN: i128 = -2451545;
const DATE_END: i128 = 2147483494 - 2451545;
const TIMESTAMP_MIN: i128 = -211813488000000000;
const TIMESTAMP_END: i128 = 9223371331200000000;

/// A value (`spec::value::Val`) in the executable representation: integers `i64`, numerics an `i128` coefficient
/// with a `u32` scale, dates days and timestamps microseconds since 2000-01-01, text bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Val {
    Null,
    Bool(bool),
    Int(i64),
    Num { coeff: i128, scale: u32 },
    Date(i64),
    Ts(i64),
    Text(Vec<u8>),
}

/// SQL three-valued truth (`spec::value::Truth`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Truth {
    True,
    False,
    Unknown,
}

impl Truth {
    fn of(b: bool) -> Truth {
        if b { Truth::True } else { Truth::False }
    }

    /// Kleene conjunction (`truth_and`).
    fn and(self, other: Truth) -> Truth {
        match (self, other) {
            (Truth::False, _) | (_, Truth::False) => Truth::False,
            (Truth::True, Truth::True) => Truth::True,
            _ => Truth::Unknown,
        }
    }

    /// Kleene disjunction (`truth_or`).
    fn or(self, other: Truth) -> Truth {
        match (self, other) {
            (Truth::True, _) | (_, Truth::True) => Truth::True,
            (Truth::False, Truth::False) => Truth::False,
            _ => Truth::Unknown,
        }
    }

    fn not(self) -> Truth {
        match self {
            Truth::True => Truth::False,
            Truth::False => Truth::True,
            Truth::Unknown => Truth::Unknown,
        }
    }
}

/// The SQL errors of `spec::value::SqlError` a constant can raise (`CardinalityViolation` needs a subquery).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SqlError {
    NumericValueOutOfRange,
    DatetimeFieldOverflow,
    DivisionByZero,
    SubstringError,
    InvalidEscapeSequence,
}

impl SqlError {
    pub fn sqlstate(self) -> &'static str {
        match self {
            SqlError::NumericValueOutOfRange => "22003",
            SqlError::DatetimeFieldOverflow => "22008",
            SqlError::DivisionByZero => "22012",
            SqlError::SubstringError => "22011",
            SqlError::InvalidEscapeSequence => "22025",
        }
    }

    /// PostgreSQL's condition name of the SQLSTATE.
    pub fn condition(self) -> &'static str {
        match self {
            SqlError::NumericValueOutOfRange => "numeric_value_out_of_range",
            SqlError::DatetimeFieldOverflow => "datetime_field_overflow",
            SqlError::DivisionByZero => "division_by_zero",
            SqlError::SubstringError => "substring_error",
            SqlError::InvalidEscapeSequence => "invalid_escape_sequence",
        }
    }
}

/// Why an evaluation has no value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Stop {
    /// SQLSpec raises this SQL error.
    Sql(SqlError),
    /// An intermediate leaves the executable interpreter's machine domain (its outcome `Capacity`).
    Capacity,
    /// Not decided here: a literal the executable AST cannot represent (the emitter refuses it, `executable_domain`),
    /// or ill-typed operands (SQLSpec's `TypeError`; the verified typing check refuses the statement).
    Undecided,
}

pub(super) type Outcome<T> = Result<T, Stop>;

/// Operand type of an arithmetic operator (`spec::scalar::NumKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NumKind {
    Int4,
    Int8,
    Numeric,
}

impl NumKind {
    fn parse(s: &str) -> NumKind {
        match s {
            "Int4" => NumKind::Int4,
            "Int8" => NumKind::Int8,
            _ => NumKind::Numeric,
        }
    }
}

/// Evaluator over the nodes of a decoded document (only literal-only subtrees are evaluated).
pub(super) struct Evaluator<'a> {
    pub nodes: &'a [Node],
}

impl Evaluator<'_> {
    /// `eval_expr` of a literal-only expression.
    pub fn expr(&self, id: usize) -> Outcome<Val> {
        let n = &self.nodes[id];
        match n.tag.as_str() {
            "Lit" => self.literal(child(n, "lit")),
            "Neg" => neg(NumKind::parse(enum_field(n, "kind")), self.expr(child(n, "arg"))?),
            "Arith" => {
                let a = self.expr(child(n, "a"))?;
                let b = self.expr(child(n, "b"))?;
                arith(enum_field(n, "op"), NumKind::parse(enum_field(n, "kind")), a, b)
            }
            "Cast" => cast(enum_field(n, "cast"), self.expr(child(n, "arg"))?),
            "AddInterval" => add_interval(self.expr(child(n, "arg"))?, fixed(n, "months"), fixed(n, "days"), fixed(n, "micros")),
            "Call" => {
                let args = n.children("args").expect("Call has args").iter().map(|&a| self.expr(a)).collect::<Outcome<Vec<Val>>>()?;
                apply_fn(enum_field(n, "f"), &args)
            }
            // CASE is lazy: the condition, then only the taken branch.
            "If" => match self.pred(child(n, "cond"))? {
                Truth::True => self.expr(child(n, "then_e")),
                _ => self.expr(child(n, "else_e")),
            },
            // `Col` and `Subquery` are never part of a constant.
            _ => Err(Stop::Undecided),
        }
    }

    /// `eval_pred` of a literal-only condition (AND and OR evaluate both operands, as SQLSpec does).
    pub fn pred(&self, id: usize) -> Outcome<Truth> {
        let n = &self.nodes[id];
        match n.tag.as_str() {
            "Cmp" => {
                let a = self.expr(child(n, "a"))?;
                let b = self.expr(child(n, "b"))?;
                cmp_truth(enum_field(n, "op"), &a, &b)
            }
            "And" => {
                let a = self.pred(child(n, "a"))?;
                Ok(a.and(self.pred(child(n, "b"))?))
            }
            "Or" => {
                let a = self.pred(child(n, "a"))?;
                Ok(a.or(self.pred(child(n, "b"))?))
            }
            "Not" => Ok(self.pred(child(n, "p"))?.not()),
            "IsNull" => Ok(Truth::of(self.expr(child(n, "e"))? == Val::Null)),
            "OfBool" => match self.expr(child(n, "e"))? {
                Val::Null => Ok(Truth::Unknown),
                Val::Bool(b) => Ok(Truth::of(b)),
                _ => Err(Stop::Undecided),
            },
            // `Exists` and `AnyCmp` are never part of a constant.
            _ => Err(Stop::Undecided),
        }
    }

    /// `lit_val` (the decoder has checked literal validity; a `Param` is never part of a constant).
    fn literal(&self, id: usize) -> Outcome<Val> {
        let n = &self.nodes[id];
        let int = |name: &str| match n.field(name) {
            Some(FieldValue::Int(s)) => s.as_str(),
            _ => unreachable!("decoded literal field {name}"),
        };
        Ok(match n.tag.as_str() {
            "Null" => Val::Null,
            "Bool" => Val::Bool(matches!(n.field("value"), Some(FieldValue::Bool(true)))),
            "Int" => Val::Int(int("v").parse().map_err(|_| Stop::Undecided)?),
            "Num" => {
                let scale = match n.field("scale") {
                    Some(FieldValue::Nat(s)) => u32::try_from(*s).map_err(|_| Stop::Undecided)?,
                    _ => unreachable!("decoded Num scale"),
                };
                Val::Num { coeff: int("coeff").parse().map_err(|_| Stop::Undecided)?, scale }
            }
            "Date" => {
                let (y, m, d) = (int("y").parse::<i64>(), int("m").parse::<i64>(), int("d").parse::<i64>());
                let (Ok(y), Ok(m), Ok(d)) = (y, m, d) else { return Err(Stop::Undecided) };
                let day = date_from_civil(y.into(), m.into(), d.into());
                if !valid_ymd(y, m, d) || !(DATE_MIN..DATE_END).contains(&day) {
                    return Err(Stop::Undecided);
                }
                Val::Date(day as i64)
            }
            "Text" => match n.field("bytes") {
                Some(FieldValue::Bytes(s)) => Val::Text(s.as_bytes().to_vec()),
                _ => unreachable!("decoded Text bytes"),
            },
            _ => return Err(Stop::Undecided),
        })
    }
}

fn child(n: &Node, name: &str) -> usize {
    n.child(name).unwrap_or_else(|| unreachable!("decoded {} has child {name}", n.tag))
}

fn enum_field<'n>(n: &'n Node, name: &str) -> &'n str {
    match n.field(name) {
        Some(FieldValue::Enum(s)) => s,
        _ => unreachable!("decoded {} has enum field {name}", n.tag),
    }
}

fn fixed(n: &Node, name: &str) -> i64 {
    match n.field(name) {
        Some(FieldValue::Fixed(v)) => *v,
        _ => unreachable!("decoded {} has integer field {name}", n.tag),
    }
}

// ---------------------------------------------------------------- integers and numerics (`spec::int`, `spec::numeric`)

/// `int_result`: an exact integer result of type `kind` (`Int8`, else `Int4`, as `int_kind_of`), or 22003.
pub(super) fn int_result(kind: NumKind, v: i128) -> Outcome<Val> {
    let fits = match kind {
        NumKind::Int8 => i64::try_from(v).is_ok(),
        _ => (INT4_MIN..=INT4_MAX).contains(&v),
    };
    if fits { Ok(Val::Int(v as i64)) } else { Err(Stop::Sql(SqlError::NumericValueOutOfRange)) }
}

/// `10^k` as an `i128`, `Capacity` when it does not fit.
fn pow10(k: u32) -> Outcome<i128> {
    10i128.checked_pow(k).ok_or(Stop::Capacity)
}

/// `align`: the coefficient `c·10^-from` written at scale `to >= from`.
fn align(c: i128, from: u32, to: u32) -> Outcome<i128> {
    pow10(to - from)?.checked_mul(c).ok_or(Stop::Capacity)
}

/// `num_arith` within `num_arith_fits`. The result needs no format check: an `i128` coefficient is always inside
/// PostgreSQL's numeric format (`lemma_num_in_range_small`), so the executable domain leaves no 22003 here.
fn num_arith(op: &str, c1: i128, s1: u32, c2: i128, s2: u32) -> Outcome<Val> {
    let (coeff, scale) = if op == "Mul" {
        (c1.checked_mul(c2), s1.checked_add(s2).ok_or(Stop::Capacity)?)
    } else {
        let s = s1.max(s2);
        let (a, b) = (align(c1, s1, s)?, align(c2, s2, s)?);
        (if op == "Add" { a.checked_add(b) } else { a.checked_sub(b) }, s)
    };
    Ok(Val::Num { coeff: coeff.ok_or(Stop::Capacity)?, scale })
}

/// `arith`: `a op b` at operand type `kind` (strict).
fn arith(op: &str, kind: NumKind, a: Val, b: Val) -> Outcome<Val> {
    match (a, b) {
        (Val::Null, Val::Null | Val::Int(_) | Val::Num { .. }) | (Val::Int(_) | Val::Num { .. }, Val::Null) => Ok(Val::Null),
        (Val::Int(x), Val::Int(y)) if kind != NumKind::Numeric => {
            let (x, y) = (i128::from(x), i128::from(y));
            int_result(kind, match op {
                "Add" => x + y,
                "Sub" => x - y,
                _ => x * y,
            })
        }
        (Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 }) if kind == NumKind::Numeric => num_arith(op, c1, s1, c2, s2),
        _ => Err(Stop::Undecided),
    }
}

/// `neg`: unary minus at type `kind` (`-int4min` is 22003; a numeric coefficient `-2^127` is `Capacity`).
fn neg(kind: NumKind, a: Val) -> Outcome<Val> {
    match a {
        Val::Null => Ok(Val::Null),
        Val::Int(x) if kind != NumKind::Numeric => int_result(kind, -i128::from(x)),
        Val::Num { coeff, scale } if kind == NumKind::Numeric => Ok(Val::Num { coeff: coeff.checked_neg().ok_or(Stop::Capacity)?, scale }),
        _ => Err(Stop::Undecided),
    }
}

/// `cast` (strict).
fn cast(op: &str, a: Val) -> Outcome<Val> {
    match (op, a) {
        (_, Val::Null) => Ok(Val::Null),
        ("Int4ToInt8", Val::Int(x)) => Ok(Val::Int(x)),
        ("IntToNumeric", Val::Int(x)) => Ok(Val::Num { coeff: x.into(), scale: 0 }),
        ("DateToTimestamp", Val::Date(d)) => Ok(Val::Ts(ts_result(i128::from(d) * USECS_PER_DAY)?)),
        _ => Err(Stop::Undecided),
    }
}

/// `num_cmp`: the exact order of `c1·10^-s1` and `c2·10^-s2`. The operand of smaller scale is aligned to the other's;
/// when that leaves `i128`, its magnitude exceeds every `i128`, so its sign decides.
pub(super) fn num_cmp(c1: i128, s1: u32, c2: i128, s2: u32) -> Ordering {
    if s1 > s2 {
        return num_cmp(c2, s2, c1, s1).reverse();
    }
    match 10i128.checked_pow(s2 - s1).and_then(|p| c1.checked_mul(p)) {
        Some(aligned) => aligned.cmp(&c2),
        None if c1 == 0 => 0.cmp(&c2),
        None => c1.cmp(&0),
    }
}

// ---------------------------------------------------------------- comparison (`spec::scalar::compare`)

/// `compare`: the exact order of two non-NULL values of one comparison family, `None` across families.
fn compare(a: &Val, b: &Val) -> Option<Ordering> {
    Some(match (a, b) {
        (Val::Bool(x), Val::Bool(y)) => x.cmp(y),
        (Val::Int(x), Val::Int(y)) => x.cmp(y),
        (Val::Int(x), Val::Num { coeff, scale }) => num_cmp((*x).into(), 0, *coeff, *scale),
        (Val::Num { coeff, scale }, Val::Int(y)) => num_cmp(*coeff, *scale, (*y).into(), 0),
        (Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 }) => num_cmp(*c1, *s1, *c2, *s2),
        (Val::Date(x), Val::Date(y)) => x.cmp(y),
        (Val::Date(x), Val::Ts(t)) => (i128::from(*x) * USECS_PER_DAY).cmp(&i128::from(*t)),
        (Val::Ts(t), Val::Date(y)) => i128::from(*t).cmp(&(i128::from(*y) * USECS_PER_DAY)),
        (Val::Ts(t), Val::Ts(u)) => t.cmp(u),
        // `lex_cmp`: bytewise, a proper prefix first.
        (Val::Text(x), Val::Text(y)) => x.cmp(y),
        _ => return None,
    })
}

/// `cmp_truth`: `Unknown` if an operand is NULL.
fn cmp_truth(op: &str, a: &Val, b: &Val) -> Outcome<Truth> {
    if *a == Val::Null || *b == Val::Null {
        return Ok(Truth::Unknown);
    }
    let c = compare(a, b).ok_or(Stop::Undecided)?;
    Ok(Truth::of(match op {
        "Eq" => c.is_eq(),
        "Ne" => c.is_ne(),
        "Lt" => c.is_lt(),
        "Le" => c.is_le(),
        "Gt" => c.is_gt(),
        _ => c.is_ge(),
    }))
}

// ---------------------------------------------------------------- dates and timestamps (`spec::datetime`)

fn is_leap(y: i128) -> bool {
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

fn days_in_month(y: i128, m: i128) -> i128 {
    match m {
        2 if is_leap(y) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

/// `date_from_civil`: days since 2000-01-01 (Hinnant's `days_from_civil`; floor division as the spec's `/`).
fn date_from_civil(y: i128, m: i128, d: i128) -> i128 {
    let y1 = if m <= 2 { y - 1 } else { y };
    let era = y1.div_euclid(400);
    let yoe = y1 - era * 400;
    let mp = if m > 2 { m - 3 } else { m + 9 };
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468 - UNIX_TO_POSTGRES_DAYS
}

/// `civil_from_date`: the civil `(year, month, day)` of a day count since 2000-01-01 (Hinnant's `civil_from_days`).
pub(super) fn civil_from_date(day: i128) -> (i128, i128, i128) {
    let z = day + UNIX_TO_POSTGRES_DAYS + 719468;
    let era = z.div_euclid(146097);
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// `ts_result`: a timestamp, or 22008 outside PostgreSQL's range.
fn ts_result(t: i128) -> Outcome<i64> {
    if (TIMESTAMP_MIN..TIMESTAMP_END).contains(&t) { Ok(t as i64) } else { Err(Stop::Sql(SqlError::DatetimeFieldOverflow)) }
}

/// `ts_add_months`: add to the civil month, clamp the day to the target month's length, keep the time of day.
fn ts_add_months(t: i64, months: i64) -> Outcome<i64> {
    let (day, tod) = (i128::from(t).div_euclid(USECS_PER_DAY), i128::from(t).rem_euclid(USECS_PER_DAY));
    let (y, m, d) = civil_from_date(day);
    let total = y * 12 + (m - 1) + i128::from(months);
    let (y2, m2) = (total.div_euclid(12), total.rem_euclid(12) + 1);
    ts_result(date_from_civil(y2, m2, d.min(days_in_month(y2, m2))) * USECS_PER_DAY + tod)
}

/// `add_interval` / `ts_add_interval`: months, then days, then microseconds, each step range-checked (22008); zero
/// month and day fields are skipped.
fn add_interval(a: Val, months: i64, days: i64, micros: i64) -> Outcome<Val> {
    let t = match a {
        Val::Null => return Ok(Val::Null),
        Val::Ts(t) => t,
        _ => return Err(Stop::Undecided),
    };
    let t1 = if months != 0 { ts_add_months(t, months)? } else { t };
    let t2 = if days != 0 { ts_result(i128::from(t1) + i128::from(days) * USECS_PER_DAY)? } else { t1 };
    Ok(Val::Ts(ts_result(i128::from(t2) + i128::from(micros))?))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn date(y: i128, m: i128, d: i128) -> i64 {
        date_from_civil(y, m, d) as i64
    }

    fn ts(y: i128, m: i128, d: i128) -> Val {
        Val::Ts(date(y, m, d) * USECS_PER_DAY as i64)
    }

    /// The probed PostgreSQL 18 results of month steps (the day is clamped) and the timestamp range (22008).
    #[test]
    fn interval_steps_clamp_the_day_and_check_the_range() {
        assert_eq!(date(2000, 1, 1), 0);
        assert_eq!(civil_from_date(-1), (1999, 12, 31));
        assert_eq!(add_interval(ts(2001, 3, 31), 1, 0, 0), Ok(ts(2001, 4, 30)));
        assert_eq!(add_interval(ts(2000, 2, 29), 12, 0, 0), Ok(ts(2001, 2, 28)));
        assert_eq!(add_interval(ts(2001, 1, 31), -2, 0, 0), Ok(ts(2000, 11, 30)));
        assert_eq!(add_interval(ts(1998, 12, 1), 0, -90, 0), Ok(ts(1998, 9, 2)));
        assert_eq!(add_interval(ts(2000, 1, 1), 300000 * 12, 0, 0), Err(Stop::Sql(SqlError::DatetimeFieldOverflow)));
        // The first timestamp is 4714-11-24 BC (astronomical year -4713).
        let first = date(-4713, 11, 24);
        assert_eq!(i128::from(first) * USECS_PER_DAY, TIMESTAMP_MIN);
        let back = date(1, 1, 1) - first;
        assert_eq!(add_interval(ts(1, 1, 1), 0, -back, 0), Ok(ts(-4713, 11, 24)));
        assert_eq!(add_interval(ts(1, 1, 1), 0, -back - 1, 0), Err(Stop::Sql(SqlError::DatetimeFieldOverflow)));
        assert_eq!(cast("DateToTimestamp", Val::Date(date(9999, 12, 31))), Ok(ts(9999, 12, 31)));
    }

    /// Integer results are range-checked by type; numeric intermediates beyond `i128` are `Capacity`.
    #[test]
    fn integer_overflow_and_numeric_capacity() {
        let overflow = Err(Stop::Sql(SqlError::NumericValueOutOfRange));
        assert_eq!(arith("Add", NumKind::Int4, Val::Int(2147483647), Val::Int(1)), overflow);
        assert_eq!(arith("Add", NumKind::Int8, Val::Int(2147483647), Val::Int(1)), Ok(Val::Int(2147483648)));
        assert_eq!(arith("Mul", NumKind::Int8, Val::Int(i64::MAX), Val::Int(2)), overflow);
        assert_eq!(neg(NumKind::Int4, Val::Int(-2147483648)), overflow);
        assert_eq!(arith("Sub", NumKind::Numeric, Val::Num { coeff: 6, scale: 2 }, Val::Num { coeff: 1, scale: 3 }), Ok(Val::Num { coeff: 59, scale: 3 }));
        assert_eq!(arith("Mul", NumKind::Numeric, Val::Num { coeff: 15, scale: 1 }, Val::Num { coeff: 2250, scale: 3 }), Ok(Val::Num { coeff: 33750, scale: 4 }));
        assert_eq!(arith("Mul", NumKind::Numeric, Val::Num { coeff: i128::MAX, scale: 0 }, Val::Num { coeff: 10, scale: 0 }), Err(Stop::Capacity));
        assert_eq!(arith("Add", NumKind::Numeric, Val::Num { coeff: 1, scale: 0 }, Val::Num { coeff: 1, scale: 39 }), Err(Stop::Capacity));
        assert_eq!(neg(NumKind::Numeric, Val::Num { coeff: i128::MIN, scale: 0 }), Err(Stop::Capacity));
        assert_eq!(arith("Add", NumKind::Int4, Val::Null, Val::Int(1)), Ok(Val::Null));
    }

    /// Comparisons are exact across scales, between integers and numerics, and between dates and timestamps.
    #[test]
    fn comparisons_are_exact() {
        assert_eq!(num_cmp(100, 2, 1, 0), Ordering::Equal);
        assert_eq!(num_cmp(1, 0, 1, 40), Ordering::Greater);
        assert_eq!(num_cmp(-1, 0, i128::MIN, 1), Ordering::Greater);
        assert_eq!(num_cmp(i128::MIN, 0, -1, 1), Ordering::Less);
        assert_eq!(num_cmp(i128::MAX, 0, i128::MAX, 1), Ordering::Greater);
        assert_eq!(num_cmp(0, 0, -5, 60), Ordering::Greater);
        assert_eq!(cmp_truth("Lt", &Val::Date(date(1998, 9, 2)), &ts(1998, 9, 3)), Ok(Truth::True));
        assert_eq!(cmp_truth("Eq", &Val::Int(1), &Val::Null), Ok(Truth::Unknown));
        assert_eq!(cmp_truth("Lt", &Val::Text(b"A".to_vec()), &Val::Text(b"a".to_vec())), Ok(Truth::True));
        assert_eq!(cmp_truth("Gt", &Val::Text(b"ab".to_vec()), &Val::Text(b"a".to_vec())), Ok(Truth::True));
    }
}
