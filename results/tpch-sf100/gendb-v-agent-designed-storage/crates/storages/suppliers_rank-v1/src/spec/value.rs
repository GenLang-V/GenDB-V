//! SQL values, NULL, three-valued logic, SQL errors and databases.
use vstd::prelude::*;
use crate::spec::types::*;

verus! {

/// A SQL value. Mathematical: integers are unbounded (`int`), `numeric` is the exact decimal
/// `coeff * 10^-scale` with its display scale, `date` counts days and `timestamp` microseconds since
/// 2000-01-01 (PostgreSQL's internal epoch), text is bytes (UTF-8, compared in `C` collation).
/// `Null` is NULL of every type. Which values a column may hold is `spec::typing::value_in_column`.
pub enum Val {
    Null,
    Bool(bool),
    Int(int),
    Num { coeff: int, scale: nat },
    Date(int),
    Ts(int),
    Text(Seq<u8>),
}

pub type Row = Seq<Val>;
pub type Relation = Seq<Row>;

/// Explicit SQL errors (SQLSTATE in brackets). The fragment never replaces an error by a value.
/// `TypeError` is not a PostgreSQL error: it is the fixed result of the (total) denotation on an ill-typed
/// AST, which the verified type checker refuses before evaluation; it is unreachable for well-typed input.
#[derive(Clone, Copy)]
pub enum SqlError {
    /// [22003] integer or numeric result outside its type's range.
    NumericValueOutOfRange,
    /// [22008] date/timestamp result outside PostgreSQL's range.
    DatetimeFieldOverflow,
    /// [22012] division by zero (integer and numeric division; checked before 22003).
    DivisionByZero,
    /// [21000] a scalar subquery returned more than one row.
    CardinalityViolation,
    /// [22011] negative SUBSTRING length.
    SubstringError,
    /// [22025] LIKE: an escape string longer than one character ("invalid escape string", `like_escape`), or
    /// the matcher reaching an escape at the end of the pattern ("LIKE pattern must not end with escape
    /// character"). PostgreSQL 18 uses 22025 for both (`spec::fns::like`).
    InvalidEscapeSequence,
    /// [22019] Reserved in the encoding; no supported construct raises it (PostgreSQL's LIKE uses 22025).
    InvalidEscapeCharacter,
    /// Ill-typed operands (not a SQL outcome; see above).
    TypeError,
}

/// SQL three-valued truth.
#[derive(Clone, Copy)]
pub enum Truth {
    True,
    False,
    Unknown,
}

/// A two-valued fact as a truth value.
pub open spec fn truth_of(b: bool) -> Truth {
    if b { Truth::True } else { Truth::False }
}

/// Kleene conjunction.
pub open spec fn truth_and(a: Truth, b: Truth) -> Truth {
    match (a, b) {
        (Truth::False, _) => Truth::False,
        (_, Truth::False) => Truth::False,
        (Truth::True, Truth::True) => Truth::True,
        _ => Truth::Unknown,
    }
}

/// Kleene disjunction.
pub open spec fn truth_or(a: Truth, b: Truth) -> Truth {
    match (a, b) {
        (Truth::True, _) => Truth::True,
        (_, Truth::True) => Truth::True,
        (Truth::False, Truth::False) => Truth::False,
        _ => Truth::Unknown,
    }
}

/// Kleene negation (`Unknown` stays `Unknown`).
pub open spec fn truth_not(a: Truth) -> Truth {
    match a {
        Truth::True => Truth::False,
        Truth::False => Truth::True,
        Truth::Unknown => Truth::Unknown,
    }
}

/// A database: the schema and, per table id, its rows (a finite sequence; duplicates are rows).
pub struct Database {
    pub schema: Schema,
    pub tables: Seq<Relation>,
}

} // verus!
