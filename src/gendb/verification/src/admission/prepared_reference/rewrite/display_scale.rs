//! PostgreSQL's static value type and per-row numeric display scale of the value expressions the rewrite hands to
//! DataFusion (SUM/AVG arguments, group keys), decided from the `sqlparser` tree and DataFusion's column types,
//! independently of the SQLGlot frontend. Tests, never proof.
//!
//! Why: a SQLSpec numeric carries its own display scale, SUM keeps the largest scale of its non-NULL values
//! (`spec::relation::num_sum`), and that scale changes later results (a quotient's scale, `spec::fns::div::div_scale`).
//! DataFusion carries every value of a decimal expression at one static scale. The two agree exactly when every row's
//! value has the static scale; a CASE whose branches have different scales (`CASE .. THEN price * (1 - disc) ELSE 0
//! END`: 4 or 0) does not, so its per-row scale is a SQL expression that DataFusion evaluates as a check column.
//!
//! Accepted grammar: columns, numeric and integer literals, NULL, numeric `+ - *` (integer operands convert exactly to
//! numeric at scale 0), unary `+`, unary `-` on numerics and integer literals, parentheses and CASE (conditions are
//! evaluated by DataFusion like WHERE). Named refusals: numeric division (DataFusion's quotient scale differs from
//! PostgreSQL's `select_div_scale`), `%`, casts, functions, EXTRACT ([`Untyped::ExtractValue`]; the rewrite types a
//! whole EXTRACT group key itself), and **integer arithmetic** ([`Untyped::IntegerArithmetic`]:
//! DataFusion evaluates `int op int` in wrapping 64-bit arithmetic and types `int4 op int4` as `int8`, where PostgreSQL
//! raises 22003 beyond `int4`/`int8`; so an integer value here is always a column, a literal or a CASE of them).
//!
//! Decimal arithmetic in DataFusion is also wrapping (`add_wrapping`/`mul_wrapping` on i128 coefficients) but it is a
//! ring operation modulo 2^128, so a value whose true coefficient is below 2^127 in magnitude is exact; that bound is
//! not checked here (the same unchecked bound as every DataFusion reference, recorded by the rewrite).

use datafusion::sql::sqlparser::ast::{BinaryOperator, Expr, UnaryOperator, Value as SqlValue};
use gendb_artifacts::ColType;
use std::collections::HashMap;

/// PostgreSQL's static type of a value expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ValueType {
    /// The NULL literal (takes the type of the other CASE branches).
    Null,
    /// `int4`, or `int8` when `int8`.
    Integer { int8: bool },
    Numeric(NumericScale),
    /// Text, date or boolean: not an arithmetic value.
    Other,
}

/// Why an expression has no type in this analysis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Untyped {
    /// Integer arithmetic (`int op int`, unary minus on a non-literal integer): never exact in DataFusion.
    IntegerArithmetic(String),
    /// EXTRACT as a value: PostgreSQL numeric, DataFusion `Int32` (only a whole group key or derived column is typed,
    /// by the rewrite itself).
    ExtractValue(String),
    /// Outside the accepted grammar.
    Unsupported(String),
}

impl std::fmt::Display for Untyped {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IntegerArithmetic(e) => write!(f, "integer arithmetic {e} (DataFusion wraps 64-bit integers where PostgreSQL raises 22003)"),
            Self::ExtractValue(e) => write!(f, "{e} as a value (PostgreSQL numeric, DataFusion Int32; only a whole group key)"),
            Self::Unsupported(detail) => f.write_str(detail),
        }
    }
}

/// Display scale of a numeric expression: at most `max` for every value; `per_row` is `None` when every value has
/// exactly `max`, otherwise the SQL integer expression of one row's display scale.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NumericScale {
    pub max: u32,
    pub per_row: Option<String>,
}

impl NumericScale {
    fn exact(scale: u32) -> Self {
        Self { max: scale, per_row: None }
    }

    /// SQL of one row's display scale.
    fn row_sql(&self) -> String {
        self.per_row.clone().unwrap_or_else(|| self.max.to_string())
    }
}

/// The column references in value positions of `e` (CASE results, operands, EXTRACT arguments; not CASE conditions), as
/// written.
pub(super) fn value_columns(e: &Expr, out: &mut Vec<String>) {
    match e {
        Expr::Identifier(_) | Expr::CompoundIdentifier(_) => {
            let name = e.to_string();
            if !out.contains(&name) {
                out.push(name);
            }
        }
        // An EXTRACT argument is typed so that a whole EXTRACT key or derived column can be checked to be of a date.
        Expr::Nested(inner) | Expr::UnaryOp { expr: inner, .. } | Expr::Extract { expr: inner, .. } => value_columns(inner, out),
        Expr::BinaryOp { left, right, .. } => {
            value_columns(left, out);
            value_columns(right, out);
        }
        Expr::Case { conditions, else_result, .. } => {
            for when in conditions {
                value_columns(&when.result, out);
            }
            if let Some(e) = else_result {
                value_columns(e, out);
            }
        }
        _ => {}
    }
}

/// The type of `e`; `columns` maps each value column reference (as written) to its DataFusion type.
pub(super) fn value_type(e: &Expr, columns: &HashMap<String, ColType>) -> Result<ValueType, Untyped> {
    let unsupported = |detail: String| Untyped::Unsupported(detail);
    Ok(match e {
        Expr::Nested(inner) => value_type(inner, columns)?,
        Expr::Identifier(_) | Expr::CompoundIdentifier(_) => match columns.get(&e.to_string()) {
            Some(ColType::I32) => ValueType::Integer { int8: false },
            Some(ColType::I64) => ValueType::Integer { int8: true },
            Some(ColType::Decimal { s, .. }) if *s >= 0 => ValueType::Numeric(NumericScale::exact(*s as u32)),
            Some(ColType::Utf8 | ColType::Date32 | ColType::Bool) => ValueType::Other,
            Some(other) => return Err(unsupported(format!("column {e} has type {other:?}, which the rewrite does not type"))),
            None => return Err(unsupported(format!("column {e} has no DataFusion type"))),
        },
        Expr::Value(v) => match &v.value {
            SqlValue::Null => ValueType::Null,
            SqlValue::Number(n, _) => literal_type(n).map_err(unsupported)?,
            SqlValue::SingleQuotedString(_) | SqlValue::Boolean(_) => ValueType::Other,
            other => return Err(unsupported(format!("literal {other}"))),
        },
        Expr::UnaryOp { op: op @ (UnaryOperator::Minus | UnaryOperator::Plus), expr } => match value_type(expr, columns)? {
            ValueType::Integer { .. } if *op == UnaryOperator::Minus && !matches!(expr.as_ref(), Expr::Value(_)) => {
                return Err(Untyped::IntegerArithmetic(e.to_string()));
            }
            t @ (ValueType::Integer { .. } | ValueType::Numeric(_) | ValueType::Null) => t,
            ValueType::Other => return Err(unsupported(format!("unary sign on a non-numeric value in {e}"))),
        },
        Expr::BinaryOp { left, op, right } => arithmetic_type(e, value_type(left, columns)?, op, value_type(right, columns)?)?,
        Expr::Extract { .. } => return Err(Untyped::ExtractValue(e.to_string())),
        Expr::Case { operand, conditions, else_result, .. } => {
            let mut branches = conditions.iter().map(|w| value_type(&w.result, columns)).collect::<Result<Vec<_>, _>>()?;
            branches.push(match else_result {
                Some(e) => value_type(e, columns)?,
                None => ValueType::Null,
            });
            case_type(operand.as_deref(), conditions.iter().map(|w| &w.condition), &branches)
                .ok_or_else(|| unsupported(format!("CASE branches of different kinds in {e}")))?
        }
        other => return Err(unsupported(format!("{other} (only columns, literals, numeric + - *, unary signs and CASE)"))),
    })
}

/// A numeric literal as written by `sqlparser`: `d.ddd` is numeric at the scale of its fraction digits, digits alone
/// are `int4` or `int8` by magnitude (PostgreSQL's literal typing).
pub(super) fn literal_type(n: &str) -> Result<ValueType, String> {
    if let Some((whole, fraction)) = n.split_once('.') {
        if whole.chars().chain(fraction.chars()).all(|c| c.is_ascii_digit()) {
            return Ok(ValueType::Numeric(NumericScale::exact(fraction.len() as u32)));
        }
    } else if let Ok(x) = n.parse::<i64>() {
        return Ok(ValueType::Integer { int8: i32::try_from(x).is_err() });
    }
    Err(format!("numeric literal {n} (only digits with an optional fraction, integers within bigint)"))
}

/// `left op right` (`e` names it in refusals): with a numeric operand, integers become numeric at scale 0, `+ -` take
/// the larger scale and `*` the sum of the scales (PostgreSQL's `numeric_add`/`numeric_mul`); two integer operands are
/// [`Untyped::IntegerArithmetic`].
fn arithmetic_type(e: &Expr, left: ValueType, op: &BinaryOperator, right: ValueType) -> Result<ValueType, Untyped> {
    use ValueType as T;
    if !matches!(op, BinaryOperator::Plus | BinaryOperator::Minus | BinaryOperator::Multiply | BinaryOperator::Divide) {
        return Err(Untyped::Unsupported(format!("operator {op} in {e}")));
    }
    let numeric = |t: &T| match t {
        T::Numeric(s) => Some(s.clone()),
        T::Integer { .. } => Some(NumericScale::exact(0)),
        T::Null | T::Other => None,
    };
    Ok(match (&left, &right) {
        (T::Null, _) | (_, T::Null) if left != T::Other && right != T::Other => T::Null,
        (T::Integer { .. }, T::Integer { .. }) => return Err(Untyped::IntegerArithmetic(e.to_string())),
        (T::Numeric(_), T::Integer { .. } | T::Numeric(_)) | (T::Integer { .. }, T::Numeric(_)) => {
            if *op == BinaryOperator::Divide {
                return Err(Untyped::Unsupported(format!("numeric division in {e} (DataFusion's quotient scale differs from PostgreSQL's)")));
            }
            let (a, b) = (numeric(&left).unwrap(), numeric(&right).unwrap());
            let exact = a.per_row.is_none() && b.per_row.is_none();
            T::Numeric(if *op == BinaryOperator::Multiply {
                NumericScale { max: a.max + b.max, per_row: (!exact).then(|| format!("({} + {})", a.row_sql(), b.row_sql())) }
            } else {
                NumericScale { max: a.max.max(b.max), per_row: (!exact).then(|| format!("greatest({}, {})", a.row_sql(), b.row_sql())) }
            })
        }
        _ => return Err(Untyped::Unsupported(format!("arithmetic on a non-numeric value in {e}"))),
    })
}

/// The type of a CASE with these branch types (the last one is ELSE, `Null` when absent): all integer is integer; with
/// a numeric branch, integers become numeric at scale 0 and the scale is exact only when every non-NULL branch has
/// the same exact scale. `None` when kinds mix.
fn case_type<'a>(operand: Option<&Expr>, conditions: impl Iterator<Item = &'a Expr>, branches: &[ValueType]) -> Option<ValueType> {
    use ValueType as T;
    let values: Vec<&T> = branches.iter().filter(|t| **t != T::Null).collect();
    if values.is_empty() {
        return Some(T::Null);
    }
    if values.iter().all(|t| matches!(t, T::Integer { .. })) {
        return Some(T::Integer { int8: values.iter().any(|t| **t == T::Integer { int8: true }) });
    }
    if values.iter().all(|t| **t == T::Other) {
        return Some(T::Other);
    }
    let scales: Vec<Option<NumericScale>> = branches
        .iter()
        .map(|t| match t {
            T::Numeric(s) => Some(Some(s.clone())),
            T::Integer { .. } => Some(Some(NumericScale::exact(0))),
            T::Null => Some(None),
            T::Other => None,
        })
        .collect::<Option<_>>()?;
    let present: Vec<&NumericScale> = scales.iter().flatten().collect();
    let max = present.iter().map(|s| s.max).max().unwrap_or(0);
    if present.iter().all(|s| s.per_row.is_none() && s.max == max) {
        return Some(T::Numeric(NumericScale::exact(max)));
    }
    let row = |s: &Option<NumericScale>| s.as_ref().map_or_else(|| "NULL".to_string(), NumericScale::row_sql);
    let (whens, otherwise) = scales.split_at(scales.len() - 1);
    let mut sql = match operand {
        Some(o) => format!("CASE {o}"),
        None => "CASE".to_string(),
    };
    for (condition, scale) in conditions.zip(whens) {
        sql.push_str(&format!(" WHEN {condition} THEN {}", row(scale)));
    }
    sql.push_str(&format!(" ELSE {} END", row(&otherwise[0])));
    Some(T::Numeric(NumericScale { max, per_row: Some(sql) }))
}
