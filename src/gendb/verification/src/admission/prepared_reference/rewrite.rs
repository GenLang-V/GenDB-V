//! The SUM/COUNT rewrite: the independent exact reference of a statement (concrete or a template) whose outputs
//! DataFusion does not type exactly (value-dependent numeric display scales: AVG, division, CASE of different scales).
//! Tests, never proof.
//!
//! The naive SQLSpec evaluator is NOT run on prepared (large) data: it materializes the relation and its grouping.
//! Instead, decided before any author call:
//!
//! 1. **Aggregation (DataFusion, one execution per admission binding over the prepared data).** The original SQL text
//!    is parsed by
//!    `sqlparser` (not the SQLGlot frontend the claim comes from). Every output is scalar arithmetic (`+ - * /`, unary
//!    minus, parentheses) over leaves: GROUP BY expressions, SUM/COUNT/AVG aggregates and numeric literals. The
//!    aggregate leaves become one exact query
//!    `SELECT <GROUP BY exprs>, <per leaf: SUM(e) | COUNT(*) | COUNT(e); AVG(e) -> SUM(e), COUNT(e)>, <scale checks>
//!    FROM <same> WHERE <same> [GROUP BY <same>]`. The FROM list is kept as written (base tables, comma lists, inner
//!    `JOIN .. ON`, `CROSS JOIN`, parenthesized inner joins); DataFusion plans the joins itself (no product is
//!    materialized) with SQL bag semantics. A sole non-aggregating derived table in FROM is first merged away
//!    ([`derived_table`]: its columns' expressions replace their references, its FROM and WHERE become the query's),
//!    so everything below analyses the inner expressions themselves. DataFusion counts exactly. It sums integers as `DECIMAL(38,0)`
//!    (`SUM(CAST(e AS DECIMAL(38,0)))`): at most 2^63 per value, so the i128 sum is exact below 2^64 rows; a SUM of
//!    `int4` beyond bigint is PostgreSQL's 22003 and the binding has no exact reference. Integer arithmetic inside
//!    aggregate arguments and group keys is refused, since DataFusion wraps it (see [`display_scale`]). Decimal
//!    arithmetic and sums are i128 operations modulo 2^128 in DataFusion (wrapping, no error), so a numeric SUM is exact
//!    when the true coefficients of its row values and of the sum are below 2^127 in magnitude (about 1.7e38). That
//!    bound is NOT checked; it is the same unchecked bound as the DataFusion-direct reference. Its AVG and decimal
//!    division (whose scales differ from PostgreSQL's) are never used. Without GROUP BY the aggregation has exactly one
//!    row (SUM NULL and COUNT 0 on no qualifying row).
//!
//!    **Parameters.** Placeholders `$n` stay placeholders in the aggregation SQL and its scale checks. DataFusion types
//!    it with the declared parameter types (`PREPARE`, no values) and executes it at every admission binding with its
//!    own typed binding, exactly as the DataFusion-direct reference binds (`direct::parameter`). A parameter may appear
//!    anywhere in FROM/JOIN conditions and WHERE, and inside the CASE conditions of group keys and aggregate
//!    arguments (WHEN conditions, a simple CASE's operand), which DataFusion evaluates like WHERE ([`value_parameter`]).
//!    Anywhere else in a group key, an aggregate argument or an output, its value would itself be grouped, aggregated
//!    or output, with a type and display scale this analysis does not derive: a named refusal. The typing never
//!    depends on a binding's values.
//! 2. **Types and display scales ([`display_scale`]).** PostgreSQL's type of every SUM/AVG argument and numeric group
//!    key (and the value of every COUNT argument) is decided from the `sqlparser` tree and DataFusion's column types:
//!    SUM(int4) is bigint, SUM(int8) numeric at scale 0, SUM(numeric) numeric at the largest display scale of its non-NULL values. When that scale is value
//!    dependent (CASE branches of different scales), a scale check `MAX(<row display scale>)` is aggregated too, and
//!    the binding has an exact reference only where it equals the static scale DataFusion carries the sum at (checked
//!    per binding). A group key `EXTRACT(YEAR | MONTH | DAY FROM <date column>)` is PostgreSQL `numeric` at scale 0
//!    ([`KeyType::Extract`]), which DataFusion carries as `Int32`: equal values on and after 0001-01-01. Before it
//!    DataFusion's YEAR is astronomical (1 BC is 0) and PostgreSQL has no year 0, so a year key below 1 is no exact
//!    reference at that binding. EXTRACT elsewhere in a value position is refused; in conditions (WHERE, ON, CASE
//!    conditions) DataFusion evaluates it, like every condition (trusted test infrastructure, not checked here).
//! 3. **Finalization (verified SQLSpec evaluator, few rows).** The aggregated rows become the table `gendb_oracle`,
//!    and `SELECT <each output's arithmetic over its columns and literals> ... ORDER BY <mapped keys>` is translated by
//!    the frontend and run by the verified evaluator (built once at preflight; it has no parameters: each binding's
//!    aggregated rows are its table). So the scalar arithmetic over the
//!    leaves (for example `100.00 * a0 / a1`) has SQLSpec/PostgreSQL types, values, NULL propagation and display
//!    scales. AVG is `sum / count`: `numeric / bigint` is `num_div(sum, scale, count, 0)`, exactly
//!    `spec::aggs::avg::avg_value` for a non-empty group of non-NULL values (the sum's format-range check aside). An
//!    empty scalar aggregate has NULL sums, so AVG (`NULL / 0`) and any arithmetic over a NULL sum are NULL. ORDER BY
//!    is the evaluator's sort. OFFSET and LIMIT are NOT applied: the finalization returns the full ordered body and
//!    the comparison accepts exactly the windows `ordered_ok` allows.
//!
//! Independence: grouping, filtering, joins and the exact aggregate leaves come from DataFusion over the prepared
//! columns (not from the author's code, not from the frontend); only the scalar arithmetic and ordering of the few
//! grouped rows use the verified evaluator, whose output value kinds are checked against the statement's. Shapes
//! outside this rewrite are named refusals: HAVING, DISTINCT, filtered or nested aggregates, casts and other functions
//! in outputs or aggregate arguments, integer arithmetic or numeric division inside an aggregate argument, integer
//! arithmetic in a group key, a parameter in a value position (outside CASE conditions) of a group key, an aggregate
//! argument or an output, outer/semi joins, derived tables other than a sole non-aggregating one (and its own
//! refusals, see [`derived_table`]), EXTRACT outside a whole group key, FETCH,
//! columns outside aggregates that are not GROUP BY expressions, and a query with neither aggregates nor GROUP BY.

mod derived_table;
mod display_scale;

use super::arrow_values::ReferenceValue;
use crate::admission::cases::DAYS_1970_TO_2000;
use datafusion::sql::sqlparser::{
    ast::{
        BinaryOperator, DateTimeField, Distinct, Expr, Function, FunctionArg, FunctionArgExpr, FunctionArguments, GroupByExpr, JoinConstraint, JoinOperator,
        LimitClause, OrderByKind, SelectItem, SetExpr, Statement, TableFactor, TableWithJoins, UnaryOperator, Value as SqlValue,
        visit_expressions, visit_expressions_mut,
    },
    dialect::PostgreSqlDialect,
    parser::Parser,
};
use derived_table::folded;
use display_scale::{Untyped, ValueType, value_columns, value_type};
use gendb_artifacts::{ColType, ColumnSpec};
use gendb_sqlspec::codec::HostValue;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::ops::ControlFlow;

/// Rewrite identity (recorded with every rewrite result).
pub const REWRITE_IDENTITY: &str = "gendb-verus-query-oracle-v5";
/// Table name of the finalization query.
pub const FINALIZATION_TABLE: &str = "gendb_oracle";

/// One output column of the original query (or an operand of one): scalar arithmetic over group keys, aggregation
/// columns and literals.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RewriteOutput {
    /// The group key at this position of the aggregation's key columns.
    Key { key: usize },
    /// `SUM(e)`: aggregation column.
    Sum { column: usize },
    /// `COUNT(*)` / `COUNT(e)`: aggregation column.
    Count { column: usize },
    /// `AVG(e)`: `SUM(e)` column divided by the `COUNT(e)` column in the finalization.
    Avg { sum: usize, count: usize },
    /// A numeric literal as written (`100.00`, `2`); the frontend types it in the finalization as in the original.
    Literal { text: String },
    /// `-operand`.
    Negate { operand: Box<RewriteOutput> },
    /// `left op right`.
    Arithmetic { op: ArithmeticOp, left: Box<RewriteOutput>, right: Box<RewriteOutput> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArithmeticOp {
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl ArithmeticOp {
    fn of(op: &BinaryOperator) -> Option<Self> {
        Some(match op {
            BinaryOperator::Plus => Self::Add,
            BinaryOperator::Minus => Self::Subtract,
            BinaryOperator::Multiply => Self::Multiply,
            BinaryOperator::Divide => Self::Divide,
            _ => return None,
        })
    }

    fn sql(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Subtract => "-",
            Self::Multiply => "*",
            Self::Divide => "/",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RewriteOrderKey {
    pub output: usize,
    pub desc: bool,
    pub nulls_first: Option<bool>,
}

/// PostgreSQL's type of one aggregate column, decided from the SQL (not from DataFusion's result type).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AggregateType {
    /// COUNT: bigint.
    Count,
    /// SUM of `int4`: bigint, summed as `DECIMAL(38,0)` and range-checked into bigint (22003 beyond it).
    Int4Sum,
    /// SUM of `int8`, or the sum of an integer AVG: numeric at scale 0, summed as `DECIMAL(38,0)`.
    IntegerNumeric,
    /// SUM of numeric values, carried at display scale `scale` (value dependent when a scale check names the column).
    Numeric { scale: u32 },
}

/// PostgreSQL's type of one group key, where DataFusion's result type alone does not decide it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum KeyType {
    /// DataFusion's type is PostgreSQL's (text, date, integer); a decimal key needs this exact display scale (`Err`:
    /// why it has none).
    Typed { scale: Result<u32, String> },
    /// `EXTRACT(YEAR | MONTH | DAY FROM <date column>)`: PostgreSQL numeric at scale 0, DataFusion `Int32`. For YEAR
    /// (`year`) the values agree only from 0001-01-01 on (checked per binding in [`finalization_rows`]).
    Extract { year: bool },
}

/// A SUM whose display scale is value dependent: aggregation column `gendb_s<i>` (after the finalization columns) is
/// the largest display scale of its non-NULL argument values per group. The reference is exact only where that equals
/// `scale`, the static scale DataFusion carries finalization column `column` at.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScaleCheck {
    pub column: usize,
    pub scale: u32,
}

/// The rewrite of one SQL text, decided upfront.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RewritePlan {
    pub identity: String,
    /// The DataFusion aggregation query: the finalization columns, then one column per scale check. Parameters stay
    /// placeholders `$n`, bound at each admission binding.
    pub aggregation_sql: String,
    /// Finalization column names: `gendb_k<i>` (group keys, GROUP BY order) then `gendb_a<j>` (aggregates).
    pub columns: Vec<String>,
    /// Number of GROUP BY keys (0: a scalar aggregate, exactly one aggregation row).
    pub keys: usize,
    /// PostgreSQL's type of each group key.
    pub key_types: Vec<KeyType>,
    /// PostgreSQL's type of each aggregate column (`columns[keys + j]`).
    pub aggregates: Vec<AggregateType>,
    pub scale_checks: Vec<ScaleCheck>,
    pub outputs: Vec<RewriteOutput>,
    pub order: Vec<RewriteOrderKey>,
    /// OFFSET/LIMIT of the SQL (recorded; the finalization returns the full ordered body).
    pub offset: Option<String>,
    pub limit: Option<String>,
}

/// Declared type of one finalization column.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FinalizationType {
    Text,
    Integer,
    Bigint,
    Date,
    /// `numeric(p, s)`; integer sums of `int8` values or of an integer AVG are carried here at scale 0.
    Numeric { p: u32, s: u32 },
}

impl FinalizationType {
    fn ddl(&self) -> String {
        match self {
            Self::Text => "text".into(),
            Self::Integer => "integer".into(),
            Self::Bigint => "bigint".into(),
            Self::Date => "date".into(),
            Self::Numeric { p, s } => format!("numeric({p},{s})"),
        }
    }
}

fn refuse(detail: impl std::fmt::Display) -> String {
    format!("independent reference rewrite: {detail}")
}

/// The statement with LIMIT/OFFSET/FETCH removed (ORDER BY kept): the full ordered body, rendered by `sqlparser` from
/// its parsed statement (a structured edit, no text replacement; placeholders `$n` stay placeholders). Used by the
/// DataFusion-direct reference; the comparison applies OFFSET/LIMIT tie-aware.
pub fn unsliced_sql(sql: &str) -> Result<String, String> {
    let statements = Parser::parse_sql(&PostgreSqlDialect {}, sql).map_err(|e| format!("sqlparser: {e}"))?;
    let [Statement::Query(query)] = statements.as_slice() else { return Err("not exactly one query statement".into()) };
    let mut query = query.clone();
    if query.limit_clause.is_none() && query.fetch.is_none() {
        return Ok(sql.trim().trim_end_matches(';').trim_end().to_string());
    }
    query.limit_clause = None;
    query.fetch = None;
    Ok(Statement::Query(query).to_string())
}

/// One aggregate column of the aggregation query (after the group keys).
#[derive(Clone, Debug)]
enum AggregateLeaf {
    /// `SUM(argument)`, also the sum of an AVG (`of_avg`).
    Sum { argument: Expr, of_avg: bool },
    /// `COUNT(argument)`, `COUNT(*)` without one.
    Count { argument: Option<Expr> },
}

impl AggregateLeaf {
    fn argument(&self) -> Option<&Expr> {
        match self {
            Self::Sum { argument, .. } => Some(argument),
            Self::Count { argument } => argument.as_ref(),
        }
    }
}

/// The rewrite of one SQL text before typing: [`derive`], then [`DerivedRewrite::resolve`] with DataFusion's types of
/// [`DerivedRewrite::value_columns_sql`].
#[derive(Clone, Debug)]
pub struct DerivedRewrite {
    group: Vec<Expr>,
    leaves: Vec<AggregateLeaf>,
    outputs: Vec<RewriteOutput>,
    order: Vec<RewriteOrderKey>,
    offset: Option<String>,
    limit: Option<String>,
    /// FROM, WHERE and GROUP BY of the aggregation query, as written (after a derived table's merge).
    from_where_group: String,
    from: String,
    /// A merged derived table's column expressions, used or not: each must type (error parity, [`derived_table`]).
    derived_columns: Vec<Expr>,
}

/// Derive the aggregate leaves and the output/order mapping from the original SQL text. `Err` names the refused shape
/// (recorded after `no_independent_reference: `).
pub fn derive(sql: &str) -> Result<DerivedRewrite, String> {
    let statements = Parser::parse_sql(&PostgreSqlDialect {}, sql).map_err(|e| refuse(format!("sqlparser: {e}")))?;
    let [Statement::Query(query)] = statements.as_slice() else { return Err(refuse("not exactly one SELECT statement")) };
    if query.with.is_some() || query.fetch.is_some() || !query.locks.is_empty() {
        return Err(refuse("WITH, FETCH or locking clause"));
    }
    let (offset, limit) = match &query.limit_clause {
        None => (None, None),
        Some(LimitClause::LimitOffset { limit, offset, limit_by }) if limit_by.is_empty() => {
            (offset.as_ref().map(|o| o.value.to_string()), limit.as_ref().map(|l| l.to_string()))
        }
        Some(other) => return Err(refuse(format!("limit clause {other}"))),
    };
    let SetExpr::Select(select) = query.body.as_ref() else { return Err(refuse("the body is not a plain SELECT")) };
    let merged = derived_table::merge(select, query.order_by.as_ref())?;
    let (select, order_by, derived_columns) = match &merged {
        Some(m) => (&m.select, m.order_by.as_ref(), m.derived_columns.clone()),
        None => (select.as_ref(), query.order_by.as_ref(), vec![]),
    };
    if select.distinct.is_some() && select.distinct != Some(Distinct::All) || select.having.is_some() || select.top.is_some() {
        return Err(refuse("SELECT DISTINCT, HAVING or TOP"));
    }
    if select.from.is_empty() {
        return Err(refuse("SELECT without FROM"));
    }
    for item in &select.from {
        check_inner_joins(item)?;
    }
    let GroupByExpr::Expressions(group, modifiers) = &select.group_by else { return Err(refuse("GROUP BY ALL")) };
    if !modifiers.is_empty() {
        return Err(refuse("GROUP BY modifiers"));
    }
    let mut leaves = vec![];
    let mut outputs = vec![];
    let mut aliases: Vec<Option<String>> = vec![];
    let mut exprs: Vec<Expr> = vec![];
    for item in &select.projection {
        let (expr, alias) = match item {
            SelectItem::UnnamedExpr(e) => (e, None),
            SelectItem::ExprWithAlias { expr, alias } => (expr, Some(folded(alias))),
            other => return Err(refuse(format!("select item {other}"))),
        };
        let e = unparen(expr);
        outputs.push(output_expr(e, group, &mut leaves)?);
        aliases.push(alias);
        exprs.push(e.clone());
    }
    if group.is_empty() && leaves.is_empty() {
        return Err(refuse("neither an aggregate nor GROUP BY (one output row per input row)"));
    }
    for e in group.iter().chain(leaves.iter().filter_map(AggregateLeaf::argument)) {
        if let Some(parameter) = value_parameter(e) {
            return Err(refuse(format!(
                "parameter {parameter} as a value in {e} (parameters are supported in FROM, WHERE and CASE conditions of group keys and aggregate arguments)"
            )));
        }
    }
    let mut order = vec![];
    if let Some(order_by) = order_by {
        let OrderByKind::Expressions(items) = &order_by.kind else { return Err(refuse("ORDER BY ALL")) };
        if order_by.interpolate.is_some() {
            return Err(refuse("ORDER BY INTERPOLATE"));
        }
        for item in items {
            if item.with_fill.is_some() {
                return Err(refuse("ORDER BY WITH FILL"));
            }
            let e = unparen(&item.expr);
            let by_alias = match e {
                Expr::Identifier(id) => aliases.iter().position(|a| a.as_deref() == Some(folded(id).as_str())),
                _ => None,
            };
            let by_ordinal = match e {
                Expr::Value(v) => match &v.value {
                    SqlValue::Number(n, _) => n.parse::<usize>().ok().filter(|n| (1..=outputs.len()).contains(n)).map(|n| n - 1),
                    _ => None,
                },
                _ => None,
            };
            let by_expr = exprs.iter().position(|x| x == e);
            let by_key = group.iter().position(|g| unparen(g) == e).and_then(|k| outputs.iter().position(|o| *o == RewriteOutput::Key { key: k }));
            let output = by_alias.or(by_ordinal).or(by_expr).or(by_key).ok_or_else(|| refuse(format!("ORDER BY {e} is not an output column")))?;
            order.push(RewriteOrderKey { output, desc: item.options.asc == Some(false), nulls_first: item.options.nulls_first });
        }
    }
    let from = select.from.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", ");
    let mut from_where_group = format!("FROM {from}");
    if let Some(w) = &select.selection {
        from_where_group.push_str(&format!(" WHERE {w}"));
    }
    if !group.is_empty() {
        from_where_group.push_str(&format!(" GROUP BY {}", group.iter().map(|g| g.to_string()).collect::<Vec<_>>().join(", ")));
    }
    Ok(DerivedRewrite { group: group.clone(), leaves, outputs, order, offset, limit, from_where_group, from, derived_columns })
}

/// Output expression `e` (parentheses removed) over the group keys `group`; its aggregates are appended to `leaves`.
fn output_expr(e: &Expr, group: &[Expr], leaves: &mut Vec<AggregateLeaf>) -> Result<RewriteOutput, String> {
    let e = unparen(e);
    if let Some(key) = group.iter().position(|g| unparen(g) == e) {
        return Ok(RewriteOutput::Key { key });
    }
    let mut leaf = |leaf: AggregateLeaf| {
        leaves.push(leaf);
        group.len() + leaves.len() - 1
    };
    Ok(match e {
        Expr::Function(f) => {
            let argument = single_argument(f)?;
            if let Some(a) = &argument {
                refuse_nested_aggregate(a)?;
            }
            match (f.name.to_string().to_lowercase().as_str(), argument) {
                ("sum", Some(a)) => RewriteOutput::Sum { column: leaf(AggregateLeaf::Sum { argument: a, of_avg: false }) },
                ("count", argument) => RewriteOutput::Count { column: leaf(AggregateLeaf::Count { argument }) },
                ("avg", Some(a)) => {
                    let sum = leaf(AggregateLeaf::Sum { argument: a.clone(), of_avg: true });
                    let count = leaf(AggregateLeaf::Count { argument: Some(a) });
                    RewriteOutput::Avg { sum, count }
                }
                _ => return Err(refuse(format!("function {f} (only the aggregates SUM, COUNT, AVG)"))),
            }
        }
        Expr::Value(v) => match &v.value {
            SqlValue::Number(n, _) if display_scale::literal_type(n).is_ok() => RewriteOutput::Literal { text: n.clone() },
            SqlValue::Placeholder(p) => return Err(refuse(format!("parameter {p} as an output value (its type would decide the output's arithmetic)"))),
            other => return Err(refuse(format!("literal {other} in an output (only numeric literals)"))),
        },
        Expr::UnaryOp { op: UnaryOperator::Minus, expr } => RewriteOutput::Negate { operand: Box::new(output_expr(expr, group, leaves)?) },
        Expr::BinaryOp { left, op, right } => {
            let op = ArithmeticOp::of(op).ok_or_else(|| refuse(format!("operator {op} in the output {e} (only + - * /)")))?;
            RewriteOutput::Arithmetic { op, left: Box::new(output_expr(left, group, leaves)?), right: Box::new(output_expr(right, group, leaves)?) }
        }
        Expr::Identifier(_) | Expr::CompoundIdentifier(_) => return Err(refuse(format!("column {e} outside an aggregate is not a GROUP BY expression"))),
        other => {
            return Err(refuse(format!("output expression {other} (only GROUP BY expressions, SUM/COUNT/AVG, numeric literals, + - * / and unary minus)")));
        }
    })
}

/// The first parameter `$n` in a value position of `e`: anywhere except inside a CASE's conditions (WHEN conditions and
/// a simple CASE's operand), which DataFusion evaluates like WHERE with its own typed binding. `None` when there is none.
fn value_parameter(e: &Expr) -> Option<String> {
    let mut values = e.clone();
    let _ = visit_expressions_mut(&mut values, |x| {
        if let Expr::Case { operand, conditions, .. } = x {
            *operand = None;
            for when in conditions {
                when.condition = Expr::value(SqlValue::Null);
            }
        }
        ControlFlow::<()>::Continue(())
    });
    match visit_expressions(&values, |x| match x {
        Expr::Value(v) if matches!(v.value, SqlValue::Placeholder(_)) => ControlFlow::Break(x.to_string()),
        _ => ControlFlow::Continue(()),
    }) {
        ControlFlow::Break(parameter) => Some(parameter),
        ControlFlow::Continue(()) => None,
    }
}

/// An aggregate inside an aggregate argument is refused by name (DataFusion would refuse it less clearly).
fn refuse_nested_aggregate(argument: &Expr) -> Result<(), String> {
    const AGGREGATES: [&str; 5] = ["sum", "count", "avg", "min", "max"];
    let nested = visit_expressions(argument, |e| match e {
        Expr::Function(f) if AGGREGATES.contains(&f.name.to_string().to_lowercase().as_str()) => ControlFlow::Break(f.to_string()),
        _ => ControlFlow::Continue(()),
    });
    match nested {
        ControlFlow::Break(f) => Err(refuse(format!("nested aggregate {f}"))),
        ControlFlow::Continue(()) => Ok(()),
    }
}

impl DerivedRewrite {
    /// Column references in value positions of the group keys, aggregate arguments and derived columns, as written.
    fn value_column_names(&self) -> Vec<String> {
        let mut names = vec![];
        for e in self.group.iter().chain(self.leaves.iter().filter_map(AggregateLeaf::argument)).chain(&self.derived_columns) {
            value_columns(e, &mut names);
        }
        names
    }

    /// `SELECT <value column references> FROM <same>`: DataFusion types the columns the display-scale analysis reads
    /// (planned, never executed). `None` when there are none.
    pub fn value_columns_sql(&self) -> Option<String> {
        let names = self.value_column_names();
        let items: Vec<String> = names.iter().enumerate().map(|(i, n)| format!("{n} AS gendb_c{i}")).collect();
        (!items.is_empty()).then(|| format!("SELECT {} FROM {}", items.join(", "), self.from))
    }

    /// The plan, given DataFusion's result columns of [`Self::value_columns_sql`] (none when it is `None`).
    pub fn resolve(self, value_columns: &[ColumnSpec]) -> Result<RewritePlan, String> {
        let names = self.value_column_names();
        if names.len() != value_columns.len() {
            return Err(format!("tool_failure: {} typed value columns for {} references", value_columns.len(), names.len()));
        }
        let types: HashMap<String, ColType> = names.into_iter().zip(value_columns.iter().map(|c| c.ty.clone())).collect();
        for d in &self.derived_columns {
            if extract_key(d, &types)?.is_none() {
                value_type(d, &types).map_err(|e| refuse(format!("derived column {d}: {e}")))?;
            }
        }
        let mut key_types = vec![];
        for g in &self.group {
            if let Some(key) = extract_key(g, &types)? {
                key_types.push(key);
                continue;
            }
            let scale = match value_type(g, &types) {
                Ok(ValueType::Numeric(scale)) if scale.per_row.is_none() => Ok(scale.max),
                Ok(ValueType::Numeric(_)) => Err(format!("{g} has a value-dependent display scale")),
                Ok(_) => Err(format!("{g} is not a numeric expression")),
                Err(why @ (Untyped::IntegerArithmetic(_) | Untyped::ExtractValue(_))) => return Err(refuse(format!("group key {g}: {why}"))),
                Err(Untyped::Unsupported(why)) => Err(why),
            };
            key_types.push(KeyType::Typed { scale });
        }
        let mut columns: Vec<String> = (0..self.group.len()).map(|i| format!("gendb_k{i}")).collect();
        let mut select_list: Vec<String> = self.group.iter().enumerate().map(|(i, g)| format!("{g} AS gendb_k{i}")).collect();
        let (mut aggregates, mut scale_checks, mut check_list) = (vec![], vec![], vec![]);
        for (j, leaf) in self.leaves.iter().enumerate() {
            let name = format!("gendb_a{j}");
            let ty = match leaf {
                AggregateLeaf::Count { argument } => {
                    if let Some(a) = argument {
                        // Only NULL-ness is counted, but DataFusion must evaluate the argument as PostgreSQL does.
                        value_type(a, &types).map_err(|e| refuse(format!("aggregate argument {a}: {e}")))?;
                    }
                    select_list.push(format!("COUNT({}) AS {name}", argument.as_ref().map_or("*".to_string(), |a| a.to_string())));
                    AggregateType::Count
                }
                AggregateLeaf::Sum { argument, of_avg } => {
                    match value_type(argument, &types).map_err(|e| refuse(format!("aggregate argument {argument}: {e}")))? {
                        ValueType::Integer { int8 } => {
                            select_list.push(format!("SUM(CAST({argument} AS DECIMAL(38,0))) AS {name}"));
                            if int8 || *of_avg { AggregateType::IntegerNumeric } else { AggregateType::Int4Sum }
                        }
                        ValueType::Numeric(scale) => {
                            select_list.push(format!("SUM({argument}) AS {name}"));
                            if let Some(row_scale) = &scale.per_row {
                                check_list.push(format!("MAX(CASE WHEN ({argument}) IS NULL THEN NULL ELSE {row_scale} END) AS gendb_s{}", scale_checks.len()));
                                scale_checks.push(ScaleCheck { column: columns.len(), scale: scale.max });
                            }
                            AggregateType::Numeric { scale: scale.max }
                        }
                        ValueType::Null | ValueType::Other => return Err(refuse(format!("aggregate argument {argument} is not a number"))),
                    }
                }
            };
            aggregates.push(ty);
            columns.push(name);
        }
        select_list.extend(check_list);
        Ok(RewritePlan {
            identity: REWRITE_IDENTITY.into(),
            aggregation_sql: format!("SELECT {} {}", select_list.join(", "), self.from_where_group),
            columns,
            keys: self.group.len(),
            key_types,
            aggregates,
            scale_checks,
            outputs: self.outputs,
            order: self.order,
            offset: self.offset,
            limit: self.limit,
        })
    }
}

/// `Some` iff `e` is a whole `EXTRACT(YEAR | MONTH | DAY FROM <column>)` (parentheses aside); `Err` refuses another
/// field or an argument that is not a column DataFusion types as a date.
fn extract_key(e: &Expr, types: &HashMap<String, ColType>) -> Result<Option<KeyType>, String> {
    let Expr::Extract { field, expr, .. } = unparen(e) else { return Ok(None) };
    let year = match field {
        DateTimeField::Year => true,
        DateTimeField::Month | DateTimeField::Day => false,
        other => return Err(refuse(format!("EXTRACT field {other} in {e} (YEAR, MONTH, DAY only)"))),
    };
    match unparen(expr) {
        column @ (Expr::Identifier(_) | Expr::CompoundIdentifier(_)) if types.get(&column.to_string()) == Some(&ColType::Date32) => Ok(Some(KeyType::Extract { year })),
        _ => Err(refuse(format!("EXTRACT in {e} of something other than a date column"))),
    }
}

/// The one argument of an aggregate without modifiers (`None` for `*`).
fn single_argument(f: &Function) -> Result<Option<Expr>, String> {
    if f.filter.is_some() || f.over.is_some() || !f.within_group.is_empty() || f.null_treatment.is_some() {
        return Err(refuse(format!("aggregate modifiers in {f}")));
    }
    let FunctionArguments::List(list) = &f.args else { return Err(refuse(format!("aggregate arguments of {f}"))) };
    if list.duplicate_treatment.is_some() || !list.clauses.is_empty() || list.args.len() != 1 {
        return Err(refuse(format!("DISTINCT/clauses or several arguments in {f}")));
    }
    match &list.args[0] {
        FunctionArg::Unnamed(FunctionArgExpr::Expr(e)) => Ok(Some(e.clone())),
        FunctionArg::Unnamed(FunctionArgExpr::Wildcard) => Ok(None),
        other => Err(refuse(format!("aggregate argument {other}"))),
    }
}

fn unparen(e: &Expr) -> &Expr {
    match e {
        Expr::Nested(inner) => unparen(inner),
        other => other,
    }
}

/// A FROM item of base tables combined by inner joins (`JOIN .. ON`, `INNER JOIN .. ON`, `CROSS JOIN`, parentheses).
fn check_inner_joins(t: &TableWithJoins) -> Result<(), String> {
    check_base_or_nested(&t.relation)?;
    for j in &t.joins {
        check_base_or_nested(&j.relation)?;
        match &j.join_operator {
            JoinOperator::Join(JoinConstraint::On(_)) | JoinOperator::Inner(JoinConstraint::On(_)) | JoinOperator::CrossJoin(JoinConstraint::None) => {}
            other => return Err(refuse(format!("join {other:?} (inner JOIN .. ON, CROSS JOIN and comma lists only)"))),
        }
    }
    Ok(())
}

fn check_base_or_nested(f: &TableFactor) -> Result<(), String> {
    match f {
        TableFactor::Table { args: None, .. } => Ok(()),
        TableFactor::NestedJoin { table_with_joins, .. } => check_inner_joins(table_with_joins),
        other => Err(refuse(format!("FROM item {other} (base tables and inner joins only)"))),
    }
}

/// Finalization column types from the aggregation's DataFusion result schema (finalization columns, then scale checks):
/// each must be the PostgreSQL type the plan decided, at the same numeric scale.
pub fn column_types(plan: &RewritePlan, schema: &[ColumnSpec]) -> Result<Vec<FinalizationType>, String> {
    if schema.len() != plan.columns.len() + plan.scale_checks.len() {
        return Err(format!("aggregation returned {} columns, expected {}", schema.len(), plan.columns.len() + plan.scale_checks.len()));
    }
    let (finalized, checks) = schema.split_at(plan.columns.len());
    if let Some(c) = checks.iter().find(|c| !matches!(c.ty, ColType::I32 | ColType::I64)) {
        return Err(format!("scale check {} has type {:?}", c.name, c.ty));
    }
    finalized
        .iter()
        .enumerate()
        .map(|(i, c)| if i < plan.keys { key_type(c, &plan.key_types[i]) } else { aggregate_type(c, &plan.aggregates[i - plan.keys]) })
        .collect()
}

fn key_type(c: &ColumnSpec, ty: &KeyType) -> Result<FinalizationType, String> {
    let scale = match ty {
        KeyType::Extract { .. } if c.ty == ColType::I32 => return Ok(FinalizationType::Numeric { p: 10, s: 0 }),
        KeyType::Extract { .. } => return Err(format!("EXTRACT group key {} is {:?} under DataFusion, not Int32", c.name, c.ty)),
        KeyType::Typed { scale } => scale,
    };
    Ok(match (&c.ty, scale) {
        (ColType::Utf8, _) => FinalizationType::Text,
        (ColType::Date32, _) => FinalizationType::Date,
        (ColType::I32, _) => FinalizationType::Integer,
        (ColType::I64, _) => FinalizationType::Bigint,
        (ColType::Decimal { p, s }, Ok(scale)) if *p >= 1 && *s >= 0 && *s as u32 == *scale => FinalizationType::Numeric { p: (*p as u32).min(38), s: *scale },
        (ColType::Decimal { s, .. }, Ok(scale)) => return Err(format!("numeric group key {}: DataFusion scale {s}, PostgreSQL display scale {scale}", c.name)),
        (ColType::Decimal { .. }, Err(why)) => return Err(format!("numeric group key {} without an exact display scale: {why}", c.name)),
        (other, _) => return Err(format!("independent reference column type {other:?}")),
    })
}

fn aggregate_type(c: &ColumnSpec, ty: &AggregateType) -> Result<FinalizationType, String> {
    Ok(match (&c.ty, ty) {
        (ColType::I64, AggregateType::Count) => FinalizationType::Bigint,
        (ColType::Decimal { s: 0, .. }, AggregateType::Int4Sum) => FinalizationType::Bigint,
        (ColType::Decimal { s: 0, .. }, AggregateType::IntegerNumeric) => FinalizationType::Numeric { p: 38, s: 0 },
        (ColType::Decimal { p, s }, AggregateType::Numeric { scale }) if *p >= 1 && *s >= 0 && *s as u32 == *scale => {
            FinalizationType::Numeric { p: (*p as u32).min(38), s: *scale }
        }
        (other, ty) => return Err(format!("aggregation column {} is {other:?} under DataFusion; PostgreSQL's type is {ty:?}", c.name)),
    })
}

/// DDL and SQL of the finalization query over [`FINALIZATION_TABLE`]. Every column is nullable: a group key can be
/// NULL, and a SUM over no non-NULL value is NULL, also within a group.
pub fn finalization(plan: &RewritePlan, types: &[FinalizationType]) -> (String, String) {
    let ddl = format!(
        "CREATE TABLE {FINALIZATION_TABLE} (\n{}\n);\n",
        plan.columns.iter().zip(types).map(|(c, t)| format!("    {c} {}", t.ddl())).collect::<Vec<_>>().join(",\n")
    );
    let items: Vec<String> = plan.outputs.iter().enumerate().map(|(i, o)| format!("{} AS gendb_o{i}", output_sql(o, &plan.columns))).collect();
    let mut sql = format!("SELECT {} FROM {FINALIZATION_TABLE}", items.join(", "));
    if !plan.order.is_empty() {
        let keys: Vec<String> = plan
            .order
            .iter()
            .map(|k| {
                let nulls = match k.nulls_first {
                    Some(true) => " NULLS FIRST",
                    Some(false) => " NULLS LAST",
                    None => "",
                };
                format!("gendb_o{}{}{nulls}", k.output, if k.desc { " DESC" } else { " ASC" })
            })
            .collect();
        sql.push_str(&format!(" ORDER BY {}", keys.join(", ")));
    }
    (ddl, sql)
}

/// SQL of one output over the finalization `columns`, every operation parenthesized as it was parsed.
fn output_sql(o: &RewriteOutput, columns: &[String]) -> String {
    match o {
        RewriteOutput::Key { key: column } | RewriteOutput::Sum { column } | RewriteOutput::Count { column } => columns[*column].clone(),
        RewriteOutput::Avg { sum, count } => format!("({} / {})", columns[*sum], columns[*count]),
        RewriteOutput::Literal { text } => text.clone(),
        RewriteOutput::Negate { operand } => format!("(- {})", output_sql(operand, columns)),
        RewriteOutput::Arithmetic { op, left, right } => format!("({} {} {})", output_sql(left, columns), op.sql(), output_sql(right, columns)),
    }
}

/// The aggregated rows as finalization table rows. `Err` is the recorded reason the binding has no exact reference:
/// a scale check differs from its static scale, a SUM of `int4` exceeds bigint (PostgreSQL raises 22003) or an
/// EXTRACT(YEAR) key is below 1 (all `no_independent_reference`), or a value does not convert (`tool_failure`).
pub fn finalization_rows(plan: &RewritePlan, types: &[FinalizationType], aggregated: &[Vec<ReferenceValue>]) -> Result<Vec<Vec<HostValue>>, String> {
    aggregated
        .iter()
        .map(|row| {
            if row.len() != plan.columns.len() + plan.scale_checks.len() {
                return Err("tool_failure: aggregation row arity differs".to_string());
            }
            let (values, checks) = row.split_at(plan.columns.len());
            for (check, largest) in plan.scale_checks.iter().zip(checks) {
                let largest = match largest {
                    ReferenceValue::Null => continue, // no non-NULL argument value: the SUM is NULL
                    ReferenceValue::I32(x) => *x as i64,
                    ReferenceValue::I64(x) => *x,
                    other => return Err(format!("tool_failure: scale check value {other:?}")),
                };
                if largest != check.scale as i64 {
                    return Err(format!(
                        "no_independent_reference: the SUM in {} has display scale {largest} in a group (value dependent), not the static scale {} DataFusion carries it at",
                        plan.columns[check.column], check.scale
                    ));
                }
            }
            for (k, _) in plan.key_types.iter().enumerate().filter(|(_, t)| **t == KeyType::Extract { year: true }) {
                if let ReferenceValue::I32(year) = values[k]
                    && year < 1
                {
                    return Err(format!(
                        "no_independent_reference: the EXTRACT(YEAR) key {} is {year}, a date before 0001-01-01, where DataFusion counts astronomical years and PostgreSQL has no year 0",
                        plan.columns[k]
                    ));
                }
            }
            for (j, _) in plan.aggregates.iter().enumerate().filter(|(_, a)| **a == AggregateType::Int4Sum) {
                let column = plan.keys + j;
                if let ReferenceValue::Dec { v, .. } = &values[column]
                    && i64::try_from(*v).is_err()
                {
                    return Err(format!(
                        "no_independent_reference: the SUM of int4 values in {} is {v}, beyond bigint (PostgreSQL raises 22003)",
                        plan.columns[column]
                    ));
                }
            }
            values.iter().zip(types).map(|(x, t)| finalization_value(x, t).map_err(|e| format!("tool_failure: {e}"))).collect()
        })
        .collect()
}

/// One aggregation value as a finalization table value of its declared type.
pub fn finalization_value(v: &ReferenceValue, ty: &FinalizationType) -> Result<HostValue, String> {
    use ReferenceValue as V;
    Ok(match (v, ty) {
        (V::Null, _) => HostValue::Null,
        (V::Text(s), FinalizationType::Text) => HostValue::Text(s.as_bytes().to_vec()),
        (V::I32(x), FinalizationType::Integer) => HostValue::Int(*x as i64),
        (V::I64(x), FinalizationType::Bigint | FinalizationType::Integer) => HostValue::Int(*x),
        (V::Dec { v, s: 0, .. }, FinalizationType::Bigint) => HostValue::Int(i64::try_from(*v).map_err(|_| format!("integer sum {v} beyond bigint"))?),
        (V::I32(x), FinalizationType::Numeric { s: 0, .. }) => HostValue::Num { coeff: *x as i128, scale: 0 },
        (V::I64(x), FinalizationType::Numeric { s: 0, .. }) => HostValue::Num { coeff: *x as i128, scale: 0 },
        (V::Dec { v, s, .. }, FinalizationType::Numeric { s: ts, .. }) if *s >= 0 && *s as u32 == *ts => HostValue::Num { coeff: *v, scale: *ts },
        (V::Date32(d), FinalizationType::Date) => HostValue::Date(d.checked_sub(DAYS_1970_TO_2000).ok_or("date out of range")?),
        (other, ty) => return Err(format!("aggregation value {other:?} does not fit the finalization type {ty:?}")),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const Q: &str = "SELECT l_returnflag, l_linestatus, SUM(l_quantity) AS sum_qty,
        SUM(l_extendedprice * (1 - l_discount) * (1 + l_tax)) AS sum_charge, AVG(l_discount) AS avg_disc, COUNT(*) AS count_order
        FROM lineitem WHERE l_shipdate <= DATE '1998-12-01' - INTERVAL '90' DAY
        GROUP BY l_returnflag, l_linestatus ORDER BY l_returnflag, l_linestatus;";

    const Q14: &str = "SELECT 100.00 * SUM(CASE WHEN p_type LIKE 'PROMO%' THEN l_extendedprice * (1 - l_discount) ELSE 0 END)
        / SUM(l_extendedprice * (1 - l_discount)) AS promo_revenue
        FROM lineitem, part WHERE l_partkey = p_partkey AND l_shipdate >= DATE '1995-09-01' AND l_shipdate < DATE '1995-09-01' + INTERVAL '1' MONTH;";

    fn decimal(p: u8, s: i8) -> ColType {
        ColType::Decimal { p, s }
    }

    fn spec(name: &str, ty: ColType) -> ColumnSpec {
        ColumnSpec { name: name.into(), ty, nullable: true }
    }

    /// The typing step as `choose_mode` runs it, with DataFusion's column types given by name.
    fn resolved(sql: &str, types: &[(&str, ColType)]) -> Result<RewritePlan, String> {
        let derived = derive(sql)?;
        let columns: Vec<ColumnSpec> = derived
            .value_column_names()
            .iter()
            .map(|n| spec(n, types.iter().find(|(m, _)| m == n).unwrap_or_else(|| panic!("no type for {n}")).1.clone()))
            .collect();
        derived.resolve(&columns)
    }

    fn l(v: &str, left: RewriteOutput, right: RewriteOutput) -> RewriteOutput {
        let op = match v {
            "+" => ArithmeticOp::Add,
            "-" => ArithmeticOp::Subtract,
            "*" => ArithmeticOp::Multiply,
            _ => ArithmeticOp::Divide,
        };
        RewriteOutput::Arithmetic { op, left: Box::new(left), right: Box::new(right) }
    }

    #[test]
    fn rewrite_maps_outputs_avg_and_order() {
        let text = || ColType::Utf8;
        let p = resolved(Q, &[("l_returnflag", text()), ("l_linestatus", text()), ("l_quantity", decimal(15, 2)), ("l_extendedprice", decimal(15, 2)),
            ("l_discount", decimal(15, 2)), ("l_tax", decimal(15, 2))])
        .unwrap();
        assert_eq!(p.keys, 2);
        assert_eq!(p.columns, ["gendb_k0", "gendb_k1", "gendb_a0", "gendb_a1", "gendb_a2", "gendb_a3", "gendb_a4"]);
        assert_eq!(p.outputs, [
            RewriteOutput::Key { key: 0 }, RewriteOutput::Key { key: 1 }, RewriteOutput::Sum { column: 2 }, RewriteOutput::Sum { column: 3 },
            RewriteOutput::Avg { sum: 4, count: 5 }, RewriteOutput::Count { column: 6 }]);
        assert_eq!(p.aggregates, [AggregateType::Numeric { scale: 2 }, AggregateType::Numeric { scale: 6 }, AggregateType::Numeric { scale: 2 },
            AggregateType::Count, AggregateType::Count]);
        assert!(p.scale_checks.is_empty(), "every Q1 argument has an exact display scale");
        assert_eq!(p.order, [RewriteOrderKey { output: 0, desc: false, nulls_first: None }, RewriteOrderKey { output: 1, desc: false, nulls_first: None }]);
        assert!(p.aggregation_sql.contains("SUM(l_discount) AS gendb_a2, COUNT(l_discount) AS gendb_a3"), "{}", p.aggregation_sql);
        assert!(p.aggregation_sql.contains("WHERE l_shipdate <= DATE '1998-12-01' - INTERVAL '90' DAY GROUP BY l_returnflag, l_linestatus"), "{}", p.aggregation_sql);
        assert!(!p.aggregation_sql.to_lowercase().contains("avg") && !p.aggregation_sql.contains("ORDER"));
        let schema = [("gendb_k0", text()), ("gendb_k1", text()), ("gendb_a0", decimal(25, 2)), ("gendb_a1", decimal(38, 6)), ("gendb_a2", decimal(25, 2)),
            ("gendb_a3", ColType::I64), ("gendb_a4", ColType::I64)]
            .map(|(n, ty)| spec(n, ty));
        let types = column_types(&p, &schema).unwrap();
        assert_eq!(types, [FinalizationType::Text, FinalizationType::Text, FinalizationType::Numeric { p: 25, s: 2 }, FinalizationType::Numeric { p: 38, s: 6 },
            FinalizationType::Numeric { p: 25, s: 2 }, FinalizationType::Bigint, FinalizationType::Bigint]);
        let (ddl, sql) = finalization(&p, &types);
        assert!(ddl.contains("    gendb_a2 numeric(25,2),\n") && !ddl.contains("NOT NULL"), "{ddl}");
        assert!(sql.contains("(gendb_a2 / gendb_a3) AS gendb_o4") && sql.ends_with("ORDER BY gendb_o0 ASC, gendb_o1 ASC"), "{sql}");
    }

    /// Q14's shape: arithmetic over two SUMs and a literal. The promo SUM's argument has row display scale 4 (THEN) or
    /// 0 (ELSE 0), so a scale check decides per binding whether the sum carried at scale 4 is the SQLSpec value.
    #[test]
    fn arithmetic_over_sums_with_a_value_dependent_scale() {
        let p = resolved(Q14, &[("p_type", ColType::Utf8), ("l_extendedprice", decimal(15, 2)), ("l_discount", decimal(15, 2))]).unwrap();
        assert_eq!(p.outputs, [l("/", l("*", RewriteOutput::Literal { text: "100.00".into() }, RewriteOutput::Sum { column: 0 }), RewriteOutput::Sum { column: 1 })]);
        assert_eq!(p.aggregates, [AggregateType::Numeric { scale: 4 }, AggregateType::Numeric { scale: 4 }]);
        assert_eq!(p.scale_checks, [ScaleCheck { column: 0, scale: 4 }]);
        assert!(p.aggregation_sql.ends_with(
            ", MAX(CASE WHEN (CASE WHEN p_type LIKE 'PROMO%' THEN l_extendedprice * (1 - l_discount) ELSE 0 END) IS NULL THEN NULL \
             ELSE CASE WHEN p_type LIKE 'PROMO%' THEN 4 ELSE 0 END END) AS gendb_s0 FROM lineitem, part WHERE l_partkey = p_partkey \
             AND l_shipdate >= DATE '1995-09-01' AND l_shipdate < DATE '1995-09-01' + INTERVAL '1' MONTH"),
            "{}", p.aggregation_sql);
        let schema = [spec("gendb_a0", decimal(38, 4)), spec("gendb_a1", decimal(38, 4)), spec("gendb_s0", ColType::I64)];
        let types = column_types(&p, &schema).unwrap();
        let (ddl, sql) = finalization(&p, &types);
        assert_eq!(ddl, "CREATE TABLE gendb_oracle (\n    gendb_a0 numeric(38,4),\n    gendb_a1 numeric(38,4)\n);\n");
        assert_eq!(sql, "SELECT ((100.00 * gendb_a0) / gendb_a1) AS gendb_o0 FROM gendb_oracle");
        let row = |check: ReferenceValue| vec![ReferenceValue::Dec { v: 12_5000, p: 38, s: 4 }, ReferenceValue::Dec { v: 50_0000, p: 38, s: 4 }, check];
        let num = |coeff| HostValue::Num { coeff, scale: 4 };
        assert_eq!(finalization_rows(&p, &types, &[row(ReferenceValue::I64(4))]).unwrap(), [vec![num(12_5000), num(50_0000)]]);
        let only_else = finalization_rows(&p, &types, &[row(ReferenceValue::I64(0))]).unwrap_err();
        assert!(only_else.starts_with("no_independent_reference: the SUM in gendb_a0 has display scale 0"), "{only_else}");
        // No qualifying row: both SUMs and the check are NULL; the finalization propagates NULL.
        let empty = vec![ReferenceValue::Null, ReferenceValue::Null, ReferenceValue::Null];
        assert_eq!(finalization_rows(&p, &types, &[empty]).unwrap(), [vec![HostValue::Null, HostValue::Null]]);
        assert!(column_types(&p, &[spec("gendb_a0", decimal(38, 6)), spec("gendb_a1", decimal(38, 4)), spec("gendb_s0", ColType::I64)]).is_err());
    }

    /// Nested arithmetic, unary minus, keys inside arithmetic and PostgreSQL's integer SUM/AVG types.
    #[test]
    fn nested_arithmetic_and_integer_sums() {
        let value_types = [("k", decimal(10, 2)), ("i", ColType::I32), ("b", ColType::I64)];
        let p = resolved("SELECT k, -(SUM(i) + 2 * COUNT(*)) / 3 AS x, k * SUM(b), AVG(i) FROM t GROUP BY k ORDER BY x DESC", &value_types).unwrap();
        assert_eq!(p.aggregates, [AggregateType::Int4Sum, AggregateType::Count, AggregateType::IntegerNumeric, AggregateType::IntegerNumeric,
            AggregateType::Count]);
        assert!(p.aggregation_sql.starts_with("SELECT k AS gendb_k0, SUM(CAST(i AS DECIMAL(38,0))) AS gendb_a0, COUNT(*) AS gendb_a1, \
            SUM(CAST(b AS DECIMAL(38,0))) AS gendb_a2"), "{}", p.aggregation_sql);
        assert_eq!((p.key_types.clone(), p.order.clone()), (vec![KeyType::Typed { scale: Ok(2) }], vec![RewriteOrderKey { output: 1, desc: true, nulls_first: None }]));
        let schema = [spec("gendb_k0", decimal(10, 2)), spec("gendb_a0", decimal(38, 0)), spec("gendb_a1", ColType::I64), spec("gendb_a2", decimal(38, 0)),
            spec("gendb_a3", decimal(38, 0)), spec("gendb_a4", ColType::I64)];
        let types = column_types(&p, &schema).unwrap();
        assert_eq!(types[..4], [FinalizationType::Numeric { p: 10, s: 2 }, FinalizationType::Bigint, FinalizationType::Bigint, FinalizationType::Numeric { p: 38, s: 0 }]);
        let (_, sql) = finalization(&p, &types);
        assert_eq!(sql, "SELECT gendb_k0 AS gendb_o0, ((- (gendb_a0 + (2 * gendb_a1))) / 3) AS gendb_o1, (gendb_k0 * gendb_a2) AS gendb_o2, \
            (gendb_a3 / gendb_a4) AS gendb_o3 FROM gendb_oracle ORDER BY gendb_o1 DESC");
        // A numeric outer operation keeps the integer leaves and the integer division inside it.
        let ratio = resolved("SELECT (SUM(i) / COUNT(*)) * 1.0 FROM t", &value_types).unwrap();
        assert_eq!(ratio.aggregates, [AggregateType::Int4Sum, AggregateType::Count]);
        let (_, sql) = finalization(&ratio, &[FinalizationType::Bigint, FinalizationType::Bigint]);
        assert_eq!(sql, "SELECT ((gendb_a0 / gendb_a1) * 1.0) AS gendb_o0 FROM gendb_oracle");
        let dependent_key = resolved("SELECT CASE WHEN i > 0 THEN k ELSE 0 END AS g, COUNT(*) FROM t GROUP BY CASE WHEN i > 0 THEN k ELSE 0 END", &value_types).unwrap();
        let e = column_types(&dependent_key, &[spec("gendb_k0", decimal(10, 2)), spec("gendb_a0", ColType::I64)]).unwrap_err();
        assert!(e.contains("without an exact display scale"), "{e}");
    }

    #[test]
    fn order_by_alias_ordinal_desc_and_refusals() {
        let p = derive("SELECT k, SUM(v) AS s FROM t GROUP BY k ORDER BY s DESC NULLS LAST, 1").unwrap();
        assert_eq!(p.order, [RewriteOrderKey { output: 1, desc: true, nulls_first: Some(false) }, RewriteOrderKey { output: 0, desc: false, nulls_first: None }]);
        for bad in ["SELECT k, SUM(v) FROM t GROUP BY k HAVING SUM(v) > 1", "SELECT k, SUM(DISTINCT v) FROM t GROUP BY k",
            "SELECT k, MIN(v) FROM t GROUP BY k", "SELECT a.k, SUM(b.v) FROM a LEFT JOIN b ON a.k = b.k GROUP BY a.k",
            "SELECT k, SUM(v) FROM t GROUP BY k FETCH FIRST 3 ROWS ONLY",
            "SELECT k, SUM(v) + x FROM t GROUP BY k", "SELECT CAST(SUM(v) AS numeric(10,2)) FROM t", "SELECT SUM(SUM(v)) FROM t",
            "SELECT COUNT(MAX(v)) FROM t", "SELECT ROUND(SUM(v), 2) FROM t", "SELECT SUM(v) FILTER (WHERE v > 0) FROM t", "SELECT v + 1 FROM t",
            "SELECT SUM(v) % 2 FROM t", "SELECT 'x', SUM(v) FROM t", "SELECT 1e2 * SUM(v) FROM t"] {
            let e = derive(bad).unwrap_err();
            assert!(e.starts_with("independent reference rewrite"), "{bad}: {e}");
        }
        let types = [("v", decimal(10, 2)), ("w", decimal(10, 2)), ("s", ColType::Utf8), ("i", ColType::I32)];
        for bad in ["SELECT SUM(v / w) FROM t", "SELECT SUM(CAST(v AS numeric(12,3))) FROM t", "SELECT SUM(abs(v)) FROM t", "SELECT SUM(s) FROM t",
            "SELECT SUM(v % w) FROM t", "SELECT SUM(CASE WHEN v > 0 THEN v ELSE s END) FROM t", "SELECT COUNT(abs(v)) FROM t"] {
            let e = resolved(bad, &types).unwrap_err();
            assert!(e.starts_with("independent reference rewrite: aggregate argument"), "{bad}: {e}");
        }
        // Integer arithmetic is wrapping 64-bit in DataFusion (PostgreSQL raises 22003): refused in aggregate arguments,
        // also as a subtree of a numeric expression, and in group keys; integer leaves and negative literals stay.
        for bad in ["SELECT SUM(i * 2) FROM t", "SELECT COUNT(i + 1) FROM t", "SELECT SUM(v * (i + 1)) FROM t", "SELECT SUM(-i) FROM t", "SELECT AVG(i / 2) FROM t"] {
            let e = resolved(bad, &types).unwrap_err();
            assert!(e.contains("integer arithmetic") && e.contains("22003"), "{bad}: {e}");
        }
        let e = resolved("SELECT i + 1, COUNT(*) FROM t GROUP BY i + 1", &types).unwrap_err();
        assert!(e.starts_with("independent reference rewrite: group key i + 1: integer arithmetic"), "{e}");
        let fine = resolved("SELECT SUM(v * i), SUM(CASE WHEN v > 0 THEN i ELSE -1 END), COUNT(i) FROM t", &types).unwrap();
        assert_eq!(fine.aggregates, [AggregateType::Numeric { scale: 2 }, AggregateType::Int4Sum, AggregateType::Count]);
    }

    /// A scalar aggregate has no GROUP BY (one aggregation row); OFFSET/LIMIT are recorded and not applied (the full
    /// ordered body is the reference).
    #[test]
    fn scalar_aggregates_and_limits_are_rewritten() {
        let p = resolved("SELECT SUM(v) AS s, COUNT(*) AS c, AVG(v) AS a FROM t WHERE d < DATE '2020-01-01'", &[("v", decimal(10, 2))]).unwrap();
        assert_eq!((p.keys, p.offset.clone(), p.limit.clone()), (0, None, None));
        assert!(!p.aggregation_sql.contains("GROUP BY"), "{}", p.aggregation_sql);
        let types = [FinalizationType::Numeric { p: 38, s: 2 }, FinalizationType::Bigint, FinalizationType::Numeric { p: 38, s: 2 }, FinalizationType::Bigint];
        let (ddl, sql) = finalization(&p, &types);
        assert!(ddl.contains("gendb_a0 numeric(38,2),") && ddl.contains("gendb_a1 bigint,") && ddl.contains("gendb_a2 numeric(38,2),"), "{ddl}");
        assert!(sql.contains("(gendb_a2 / gendb_a3) AS gendb_o2") && !sql.contains("ORDER BY"), "{sql}");
        assert_eq!(finalization_value(&ReferenceValue::Null, &types[0]).unwrap(), HostValue::Null);
        let q = derive("SELECT k, SUM(v) AS s FROM t GROUP BY k ORDER BY s DESC LIMIT 10 OFFSET 2").unwrap();
        assert_eq!((q.offset.as_deref(), q.limit.as_deref()), (Some("2"), Some("10")));
        let q = q.resolve(&[spec("k", ColType::Utf8), spec("v", decimal(10, 2))]).unwrap();
        let (_, sql) = finalization(&q, &[FinalizationType::Text, FinalizationType::Numeric { p: 38, s: 2 }]);
        assert!(sql.ends_with("ORDER BY gendb_o1 DESC") && !sql.contains("LIMIT") && !q.aggregation_sql.contains("LIMIT"), "{sql} / {}", q.aggregation_sql);
    }

    /// FROM lists and inner joins are kept as written (DataFusion plans the joins); the aggregation has no ORDER BY or
    /// LIMIT; the value columns are typed over the same FROM.
    #[test]
    fn joins_are_kept_as_written() {
        let d = derive("SELECT a.k, COUNT(*) AS n, SUM(b.v) AS s FROM a, b JOIN c ON b.x = c.x WHERE a.k = b.k GROUP BY a.k ORDER BY n DESC LIMIT 2").unwrap();
        assert_eq!(d.value_columns_sql().unwrap(), "SELECT a.k AS gendb_c0, b.v AS gendb_c1 FROM a, b JOIN c ON b.x = c.x");
        let p = d.resolve(&[spec("a.k", ColType::I32), spec("b.v", decimal(10, 2))]).unwrap();
        assert_eq!(p.aggregation_sql, "SELECT a.k AS gendb_k0, COUNT(*) AS gendb_a0, SUM(b.v) AS gendb_a1 FROM a, b JOIN c ON b.x = c.x WHERE a.k = b.k GROUP BY a.k");
        assert_eq!((p.keys, p.limit.as_deref()), (1, Some("2")));
        let q = resolved("SELECT SUM(t.v) FROM t CROSS JOIN u INNER JOIN w ON u.k = w.k", &[("t.v", decimal(10, 2))]).unwrap();
        assert!(q.aggregation_sql.ends_with("FROM t CROSS JOIN u INNER JOIN w ON u.k = w.k"), "{}", q.aggregation_sql);
        assert_eq!(derive("SELECT COUNT(*) FROM t").unwrap().value_columns_sql(), None);
    }

    /// Template parameters stay placeholders where DataFusion binds them like WHERE (FROM/JOIN conditions, WHERE, CASE
    /// conditions of aggregate arguments and group keys, also inside a scale check); as a value they are refused.
    #[test]
    fn parameters_in_filters_and_case_conditions_stay_placeholders() {
        let text = || ColType::Utf8;
        let q1 = Q.replace("DATE '1998-12-01' - INTERVAL '90' DAY", "$1");
        let p = resolved(&q1, &[("l_returnflag", text()), ("l_linestatus", text()), ("l_quantity", decimal(15, 2)), ("l_extendedprice", decimal(15, 2)),
            ("l_discount", decimal(15, 2)), ("l_tax", decimal(15, 2))])
        .unwrap();
        assert!(p.aggregation_sql.ends_with("FROM lineitem WHERE l_shipdate <= $1 GROUP BY l_returnflag, l_linestatus"), "{}", p.aggregation_sql);
        assert_eq!(p.outputs[4], RewriteOutput::Avg { sum: 4, count: 5 });
        // Q8's parameter position: the nation inside the CASE condition of a SUM (here over base tables), a join
        // condition and WHERE parameters, and a parameter in the condition of a CASE group key.
        let shares = "SELECT CASE WHEN p_type = $3 THEN 'match' ELSE 'other' END AS g, \
            SUM(CASE WHEN n_name = $1 THEN l_extendedprice * (1 - l_discount) ELSE 0 END) / SUM(l_extendedprice * (1 - l_discount)) AS share \
            FROM lineitem JOIN part ON l_partkey = p_partkey AND p_size > $4, nation WHERE l_suppkey = n_nationkey AND l_shipdate >= $2 \
            GROUP BY CASE WHEN p_type = $3 THEN 'match' ELSE 'other' END ORDER BY g";
        let d = derive(shares).unwrap();
        assert_eq!(d.value_columns_sql().unwrap(),
            "SELECT l_extendedprice AS gendb_c0, l_discount AS gendb_c1 FROM lineitem JOIN part ON l_partkey = p_partkey AND p_size > $4, nation");
        let p = d.resolve(&[spec("l_extendedprice", decimal(15, 2)), spec("l_discount", decimal(15, 2))]).unwrap();
        assert_eq!(p.scale_checks, [ScaleCheck { column: 1, scale: 4 }]);
        assert!(p.aggregation_sql.starts_with("SELECT CASE WHEN p_type = $3 THEN 'match' ELSE 'other' END AS gendb_k0, \
            SUM(CASE WHEN n_name = $1 THEN l_extendedprice * (1 - l_discount) ELSE 0 END) AS gendb_a0"), "{}", p.aggregation_sql);
        assert!(p.aggregation_sql.contains("ELSE CASE WHEN n_name = $1 THEN 4 ELSE 0 END END) AS gendb_s0 FROM lineitem JOIN part ON l_partkey = p_partkey \
            AND p_size > $4, nation WHERE l_suppkey = n_nationkey AND l_shipdate >= $2 GROUP BY"), "{}", p.aggregation_sql);
        let types = [("v", decimal(10, 2)), ("k", decimal(10, 2)), ("i", ColType::I32)];
        for bad in ["SELECT SUM(v * $1) FROM t", "SELECT SUM(CASE WHEN v > 0 THEN $1 ELSE v END) FROM t", "SELECT COUNT($1) FROM t",
            "SELECT k + $1, COUNT(*) FROM t GROUP BY k + $1", "SELECT $1, COUNT(*) FROM t GROUP BY $1", "SELECT SUM(CASE $1 WHEN 1 THEN v ELSE $2 END) FROM t"] {
            let e = derive(bad).unwrap_err();
            assert!(e.starts_with("independent reference rewrite: parameter $") && e.contains("as a value in"), "{bad}: {e}");
        }
        let e = derive("SELECT $1 * SUM(v) FROM t").unwrap_err();
        assert!(e.starts_with("independent reference rewrite: parameter $1 as an output value"), "{e}");
        assert!(resolved("SELECT SUM(CASE $1 WHEN 1 THEN v ELSE 0.00 END) FROM t", &types).is_ok(), "a simple CASE's operand is a condition");
    }

    /// Q8's template as the run declares it: the derived table is merged, so the nation SUM's value-dependent scale
    /// comes from the inner `volume` expression under the outer CASE; the EXTRACT(YEAR) key is PostgreSQL numeric 0.
    const Q8: &str = "SELECT o_year, SUM(CASE WHEN nation = $1 THEN volume ELSE 0 END) / SUM(volume) AS mkt_share
        FROM (SELECT EXTRACT(YEAR FROM o_orderdate) AS o_year, l_extendedprice * (1 - l_discount) AS volume, n2.n_name AS nation
            FROM part, supplier, lineitem, orders, customer, nation n1, nation n2, region
            WHERE p_partkey = l_partkey AND s_suppkey = l_suppkey AND l_orderkey = o_orderkey AND o_custkey = c_custkey
                AND c_nationkey = n1.n_nationkey AND n1.n_regionkey = r_regionkey AND r_name = $2 AND s_nationkey = n2.n_nationkey
                AND o_orderdate BETWEEN DATE '1995-01-01' AND DATE '1996-12-31' AND p_type = $3) AS all_nations
        GROUP BY o_year ORDER BY o_year";

    fn q8_types() -> [(&'static str, ColType); 4] {
        [("o_orderdate", ColType::Date32), ("l_extendedprice", decimal(15, 2)), ("l_discount", decimal(15, 2)), ("n2.n_name", ColType::Utf8)]
    }

    #[test]
    fn derived_table_merges_with_provenance_and_extract_keys() {
        let p = resolved(Q8, &q8_types()).unwrap();
        let volume = "(l_extendedprice * (1 - l_discount))";
        assert_eq!(p.aggregation_sql, format!(
            "SELECT (EXTRACT(YEAR FROM o_orderdate)) AS gendb_k0, SUM(CASE WHEN (n2.n_name) = $1 THEN {volume} ELSE 0 END) AS gendb_a0, \
             SUM({volume}) AS gendb_a1, MAX(CASE WHEN (CASE WHEN (n2.n_name) = $1 THEN {volume} ELSE 0 END) IS NULL THEN NULL \
             ELSE CASE WHEN (n2.n_name) = $1 THEN 4 ELSE 0 END END) AS gendb_s0 \
             FROM part, supplier, lineitem, orders, customer, nation n1, nation n2, region WHERE p_partkey = l_partkey AND s_suppkey = l_suppkey \
             AND l_orderkey = o_orderkey AND o_custkey = c_custkey AND c_nationkey = n1.n_nationkey AND n1.n_regionkey = r_regionkey AND r_name = $2 \
             AND s_nationkey = n2.n_nationkey AND o_orderdate BETWEEN DATE '1995-01-01' AND DATE '1996-12-31' AND p_type = $3 \
             GROUP BY (EXTRACT(YEAR FROM o_orderdate))"));
        assert_eq!(p.key_types, [KeyType::Extract { year: true }]);
        assert_eq!(p.scale_checks, [ScaleCheck { column: 1, scale: 4 }]);
        assert_eq!(p.outputs, [RewriteOutput::Key { key: 0 }, l("/", RewriteOutput::Sum { column: 1 }, RewriteOutput::Sum { column: 2 })]);
        assert_eq!(p.order, [RewriteOrderKey { output: 0, desc: false, nulls_first: None }]);
        let schema = [spec("gendb_k0", ColType::I32), spec("gendb_a0", decimal(38, 4)), spec("gendb_a1", decimal(38, 4)), spec("gendb_s0", ColType::I64)];
        let types = column_types(&p, &schema).unwrap();
        assert_eq!(types, [FinalizationType::Numeric { p: 10, s: 0 }, FinalizationType::Numeric { p: 38, s: 4 }, FinalizationType::Numeric { p: 38, s: 4 }]);
        let (ddl, sql) = finalization(&p, &types);
        assert!(ddl.contains("gendb_k0 numeric(10,0),"), "{ddl}");
        assert_eq!(sql, "SELECT gendb_k0 AS gendb_o0, (gendb_a0 / gendb_a1) AS gendb_o1 FROM gendb_oracle ORDER BY gendb_o0 ASC");
        let row = |year: i32, check: i64| vec![ReferenceValue::I32(year), ReferenceValue::Dec { v: 5, p: 38, s: 4 }, ReferenceValue::Dec { v: 20, p: 38, s: 4 },
            ReferenceValue::I64(check)];
        let num = |coeff, scale| HostValue::Num { coeff, scale };
        assert_eq!(finalization_rows(&p, &types, &[row(1995, 4), row(1996, 4)]).unwrap()[1], [num(1996, 0), num(5, 4), num(20, 4)]);
        assert!(finalization_rows(&p, &types, &[]).unwrap().is_empty(), "no qualifying row: no group, an empty reference");
        let e = finalization_rows(&p, &types, &[row(1995, 4), row(0, 4)]).unwrap_err();
        assert!(e.starts_with("no_independent_reference: the EXTRACT(YEAR) key gendb_k0 is 0"), "{e}");
        let e = finalization_rows(&p, &types, &[row(1995, 0)]).unwrap_err();
        assert!(e.starts_with("no_independent_reference: the SUM in gendb_a0 has display scale 0"), "only ELSE 0 summed in a group: {e}");
        assert!(column_types(&p, &[spec("gendb_k0", ColType::I64), schema[1].clone(), schema[2].clone(), schema[3].clone()]).is_err());

        // An outer WHERE is conjoined; a reference qualified by the derived alias resolves; an explicit output alias
        // that shadows a derived column name orders by the output, not by the derived column.
        let shadow = "SELECT SUM(d.v) AS k, k AS g FROM (SELECT l_extendedprice AS v, l_linestatus AS k FROM lineitem WHERE l_tax > 0) AS d \
            WHERE k <> $1 GROUP BY k ORDER BY k DESC";
        let p = resolved(shadow, &[("l_extendedprice", decimal(15, 2)), ("l_linestatus", ColType::Utf8)]).unwrap();
        assert!(p.aggregation_sql.ends_with("FROM lineitem WHERE (l_tax > 0) AND ((l_linestatus) <> $1) GROUP BY (l_linestatus)"), "{}", p.aggregation_sql);
        assert_eq!((p.outputs[0].clone(), p.order.clone()), (RewriteOutput::Sum { column: 1 }, vec![RewriteOrderKey { output: 0, desc: true, nulls_first: None }]));
        // Quoted names are kept as written, unquoted ones fold: "V" is not v.
        let quoted = resolved("SELECT SUM(\"V\") FROM (SELECT l_tax AS \"V\" FROM lineitem) AS d", &[("l_tax", decimal(15, 2))]).unwrap();
        assert!(quoted.aggregation_sql.starts_with("SELECT SUM((l_tax)) AS gendb_a0"), "{}", quoted.aggregation_sql);
        let e = derive("SELECT SUM(v) FROM (SELECT l_tax AS \"V\" FROM lineitem) AS d").unwrap_err();
        assert!(e.ends_with("column v is not a column of the derived table"), "{e}");
        let e = derive("SELECT SUM(\"V\") FROM (SELECT l_tax AS v FROM lineitem) AS d").unwrap_err();
        assert!(e.ends_with("column \"V\" is not a column of the derived table"), "{e}");
        // Without a derived table, an EXTRACT key is typed the same way.
        let p = resolved("SELECT EXTRACT(MONTH FROM d) AS m, COUNT(*) FROM t GROUP BY EXTRACT(MONTH FROM d)", &[("d", ColType::Date32)]).unwrap();
        assert_eq!(p.key_types, [KeyType::Extract { year: false }]);
    }

    /// Every derived-table and EXTRACT boundary is a named refusal, at derivation or at typing.
    #[test]
    fn derived_table_refusals() {
        let d = |sql: &str| derive(sql).unwrap_err();
        for (sql, why) in [
            ("SELECT c, COUNT(*) FROM (SELECT k, COUNT(v) AS c FROM t GROUP BY k) AS o GROUP BY c", "GROUP BY"),
            ("SELECT SUM(s) FROM (SELECT SUM(v) AS s FROM t) AS o", "aggregating derived table"),
            ("SELECT SUM(v) FROM (SELECT DISTINCT v FROM t) AS o", "DISTINCT"),
            ("SELECT SUM(v) FROM (SELECT v FROM t LIMIT 5) AS o", "LIMIT"),
            ("SELECT SUM(v) FROM (SELECT v FROM t UNION ALL SELECT v FROM u) AS o", "not a plain SELECT"),
            ("SELECT SUM(o.v) FROM t, LATERAL (SELECT v FROM u) AS o", "next to other FROM items"),
            ("SELECT SUM(x) FROM (SELECT v FROM t) AS o (x)", "column-alias list"),
            ("SELECT SUM(o.v) FROM (SELECT v FROM t) AS o JOIN u ON o.v = u.v", "in a join"),
            ("SELECT SUM(v) FROM (SELECT v FROM (SELECT v FROM t) AS i) AS o", "base tables and inner joins only"),
            ("SELECT SUM(v) FROM (SELECT * FROM t) AS o", "only `expr AS name` and plain columns"),
            ("SELECT SUM(v) FROM (SELECT v, v * 2 FROM t) AS o", "only `expr AS name` and plain columns"),
            ("SELECT SUM(v) FROM (SELECT v, w AS v FROM t) AS o", "two columns named v"),
            ("SELECT SUM(v) FROM (SELECT CASE WHEN k > 0 THEN w ELSE 0 END AS v FROM t) AS o", "derived column v: CASE"),
            ("SELECT SUM(v) FROM (SELECT $1 AS p, w AS v FROM t) AS o", "derived column p: parameter $1"),
            ("SELECT SUM(v) FROM (SELECT (SELECT MAX(w) FROM u) AS v FROM t) AS o", "derived column v: subquery"),
            ("SELECT SUM(x) FROM (SELECT v FROM t) AS o", "column x is not a column of the derived table"),
            ("SELECT SUM(t.v) FROM (SELECT v FROM t) AS o", "column t.v is not a column of the derived table"),
            ("SELECT SUM(v) FROM (SELECT v FROM t) AS o WHERE v IN (SELECT w FROM u)", "subquery"),
        ] {
            let e = d(sql);
            assert!(e.starts_with("independent reference rewrite: ") && e.contains(why), "{sql}: {e}");
        }
        // Typed in `resolve`: every derived column, used or not, and EXTRACT only as a whole group key of a date.
        let types = [("v", decimal(10, 2)), ("i", ColType::I32), ("s", ColType::Utf8), ("d", ColType::Date32)];
        for (sql, why) in [
            ("SELECT SUM(v) FROM (SELECT v, i + 1 AS unused FROM t) AS o", "derived column i + 1: integer arithmetic"),
            ("SELECT SUM(v) FROM (SELECT v, v / 2 AS unused FROM t) AS o", "derived column v / 2: numeric division"),
            ("SELECT SUM(v) FROM (SELECT v, abs(v) AS unused FROM t) AS o", "derived column abs(v)"),
            ("SELECT SUM(y) FROM (SELECT EXTRACT(YEAR FROM d) AS y FROM t) AS o", "aggregate argument (EXTRACT(YEAR FROM d))"),
            ("SELECT y, COUNT(*) FROM (SELECT EXTRACT(YEAR FROM s) AS y FROM t) AS o GROUP BY y", "of something other than a date column"),
            ("SELECT EXTRACT(WEEK FROM d), COUNT(*) FROM t GROUP BY EXTRACT(WEEK FROM d)", "EXTRACT field WEEK"),
            ("SELECT EXTRACT(YEAR FROM d) + 1, COUNT(*) FROM t GROUP BY EXTRACT(YEAR FROM d) + 1", "group key"),
        ] {
            let e = resolved(sql, &types).unwrap_err();
            assert!(e.starts_with("independent reference rewrite: ") && e.contains(why), "{sql}: {e}");
        }
    }

    #[test]
    fn integer_avg_sums_are_numeric_and_values_convert() {
        let p = resolved("SELECT k, AVG(i), SUM(i) FROM t GROUP BY k", &[("k", ColType::Utf8), ("i", ColType::I64)]).unwrap();
        let schema = [("gendb_k0", ColType::Utf8), ("gendb_a0", decimal(38, 0)), ("gendb_a1", ColType::I64), ("gendb_a2", decimal(38, 0))].map(|(n, ty)| spec(n, ty));
        let types = column_types(&p, &schema).unwrap();
        assert_eq!(types, [FinalizationType::Text, FinalizationType::Numeric { p: 38, s: 0 }, FinalizationType::Bigint, FinalizationType::Numeric { p: 38, s: 0 }]);
        assert!(column_types(&p, &[spec("gendb_k0", ColType::Utf8), spec("gendb_a0", ColType::I64), spec("gendb_a1", ColType::I64), spec("gendb_a2", ColType::I64)]).is_err(),
            "an integer sum must come from the DECIMAL(38,0) aggregation, never a wrapping Int64 one");
        // SUM(int8) beyond bigint is an exact numeric; SUM(int4) beyond bigint is PostgreSQL's 22003: no reference.
        let beyond = i64::MAX as i128 + 2;
        let key = || ReferenceValue::Text("x".into());
        let row = [key(), ReferenceValue::Dec { v: beyond, p: 38, s: 0 }, ReferenceValue::I64(2), ReferenceValue::Dec { v: beyond, p: 38, s: 0 }];
        assert_eq!(finalization_rows(&p, &types, &[row.to_vec()]).unwrap()[0][3], HostValue::Num { coeff: beyond, scale: 0 });
        let int4 = resolved("SELECT k, SUM(i) FROM t GROUP BY k", &[("k", ColType::Utf8), ("i", ColType::I32)]).unwrap();
        assert_eq!(int4.aggregates, [AggregateType::Int4Sum]);
        let int4_types = [FinalizationType::Text, FinalizationType::Bigint];
        let sum = |v| vec![key(), ReferenceValue::Dec { v, p: 38, s: 0 }];
        assert_eq!(finalization_rows(&int4, &int4_types, &[sum(-7)]).unwrap(), [vec![HostValue::Text(b"x".to_vec()), HostValue::Int(-7)]]);
        let e = finalization_rows(&int4, &int4_types, &[sum(beyond)]).unwrap_err();
        assert!(e.starts_with("no_independent_reference: the SUM of int4 values in gendb_a0") && e.contains("22003"), "{e}");
        assert_eq!(finalization_value(&ReferenceValue::I64(7), &types[1]).unwrap(), HostValue::Num { coeff: 7, scale: 0 });
        assert_eq!(finalization_value(&ReferenceValue::Dec { v: 123, p: 38, s: 2 }, &FinalizationType::Numeric { p: 38, s: 2 }).unwrap(), HostValue::Num { coeff: 123, scale: 2 });
        assert!(finalization_value(&ReferenceValue::Dec { v: 123, p: 38, s: 3 }, &FinalizationType::Numeric { p: 38, s: 2 }).is_err());
        assert_eq!(finalization_value(&ReferenceValue::Date32(10957), &FinalizationType::Date).unwrap(), HostValue::Date(0));
    }
}
