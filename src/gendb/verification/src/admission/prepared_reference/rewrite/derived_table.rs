//! A non-aggregating derived table merged into the SUM/COUNT rewrite (standard view merging). Tests, never proof.
//!
//! `SELECT <outer> FROM (SELECT <e_i> AS <c_i> FROM <F> [WHERE <W>]) [AS d] [WHERE <V>] ...` becomes
//! `SELECT <outer[c_i := (e_i)]> FROM <F> WHERE (<W>) AND (<V[c_i := (e_i)]>) ...`. Under bag semantics the derived
//! table is one row per qualifying row of `F`, and the merged query sees the same bag of per-row values. The rewrite
//! then analyses the inner expressions themselves (display scales, integer arithmetic, parameter positions), never a
//! derived column's static DataFusion type: a derived `price * (1 - disc)` inside an outer `CASE .. ELSE 0 END` keeps
//! its value-dependent scale check.
//!
//! **Error parity.** SQLSpec evaluates every derived column on every inner row; the merged query evaluates a derived
//! column only where the outer query uses it, after the outer WHERE. They agree because no derived column can raise:
//! here CASE (its conditions), parameters and subqueries are refused in every derived column, used or not, and
//! `DerivedRewrite::resolve` types every derived column with DataFusion's column types (the display-scale value grammar,
//! which refuses integer arithmetic, division, casts and functions, or a whole `EXTRACT(YEAR|MONTH|DAY FROM <date
//! column>)`, which never raises).
//!
//! **Names** follow PostgreSQL: an unquoted identifier folds to lower case, a quoted one is kept as written. Every outer
//! column reference must name a derived column, bare or qualified by the derived table's alias (the derived table is
//! the only name in scope). The one exception is a bare ORDER BY name equal to an explicit output alias, which
//! PostgreSQL resolves to that output column first; it is left for the rewrite's alias mapping.
//!
//! Refused by name: LATERAL, TABLESAMPLE, a column-alias list, a derived table with joins or next to other FROM items;
//! in the derived query WITH, ORDER BY, LIMIT/OFFSET/FETCH, locking and other query clauses, a body that is not a plain
//! SELECT, DISTINCT, GROUP BY, HAVING and other SELECT clauses, aggregate or window functions, wildcards, unaliased
//! non-column items, duplicate column names; subqueries in the outer query. A derived table elsewhere (inside a join,
//! nested in the derived table) is refused by the rewrite's FROM check.

use super::{refuse, unparen};
use datafusion::sql::sqlparser::ast::{
    BinaryOperator, Distinct, Expr, GroupByExpr, Ident, OrderBy, OrderByKind, Query, Select, SelectFlavor, SelectItem, SetExpr, TableFactor,
    Value as SqlValue, visit_expressions, visit_expressions_mut,
};
use std::ops::ControlFlow;

/// PostgreSQL's name of an identifier: unquoted folds to lower case, quoted is kept as written.
pub(super) fn folded(id: &Ident) -> String {
    match id.quote_style {
        None => id.value.to_lowercase(),
        Some(_) => id.value.clone(),
    }
}

/// The outer SELECT with its derived table merged away.
pub(super) struct Merged {
    pub select: Select,
    pub order_by: Option<OrderBy>,
    /// Every derived column's defining expression, used by the outer query or not (each is typed by `resolve`).
    pub derived_columns: Vec<Expr>,
}

/// Merge `select`'s derived table (with the query's `order_by`). `Ok(None)` when its FROM has no derived table item.
pub(super) fn merge(select: &Select, order_by: Option<&OrderBy>) -> Result<Option<Merged>, String> {
    let is_derived = |f: &TableFactor| matches!(f, TableFactor::Derived { .. });
    if !select.from.iter().any(|t| is_derived(&t.relation) || t.joins.iter().any(|j| is_derived(&j.relation))) {
        return Ok(None);
    }
    let [item] = select.from.as_slice() else { return Err(refuse("derived table next to other FROM items (only a sole derived table is merged)")) };
    let TableFactor::Derived { lateral, subquery, alias, sample } = &item.relation else {
        return Err(refuse("derived table in a join (only a sole derived table is merged)"));
    };
    if !item.joins.is_empty() {
        return Err(refuse("derived table in a join (only a sole derived table is merged)"));
    }
    if *lateral || sample.is_some() {
        return Err(refuse("LATERAL or TABLESAMPLE derived table"));
    }
    if alias.as_ref().is_some_and(|a| !a.columns.is_empty()) {
        return Err(refuse("derived table with a column-alias list"));
    }
    let alias = alias.as_ref().map(|a| folded(&a.name));
    let inner = plain_select(subquery)?;
    let columns = derived_columns(inner)?;

    let mut merged = select.clone();
    merged.from = inner.from.clone();
    for item in &mut merged.projection {
        if let SelectItem::UnnamedExpr(e) | SelectItem::ExprWithAlias { expr: e, .. } = item {
            substitute(e, &columns, alias.as_deref())?;
        }
    }
    let outer_where = match &select.selection {
        Some(w) => {
            let mut w = w.clone();
            substitute(&mut w, &columns, alias.as_deref())?;
            Some(w)
        }
        None => None,
    };
    merged.selection = match (inner.selection.clone(), outer_where) {
        (Some(a), Some(b)) => Some(Expr::BinaryOp { left: Box::new(Expr::Nested(Box::new(a))), op: BinaryOperator::And, right: Box::new(Expr::Nested(Box::new(b))) }),
        (a, b) => a.or(b),
    };
    if let GroupByExpr::Expressions(group, _) = &mut merged.group_by {
        for g in group {
            substitute(g, &columns, alias.as_deref())?;
        }
    }
    let output_aliases: Vec<String> = select
        .projection
        .iter()
        .filter_map(|item| match item {
            SelectItem::ExprWithAlias { alias, .. } => Some(folded(alias)),
            _ => None,
        })
        .collect();
    let mut order_by = order_by.cloned();
    if let Some(OrderBy { kind: OrderByKind::Expressions(items), .. }) = &mut order_by {
        for item in items {
            let names_output = matches!(unparen(&item.expr), Expr::Identifier(id) if output_aliases.contains(&folded(id)));
            if !names_output {
                substitute(&mut item.expr, &columns, alias.as_deref())?;
            }
        }
    }
    Ok(Some(Merged { select: merged, order_by, derived_columns: columns.into_iter().map(|(_, e)| e).collect() }))
}

/// The derived query's SELECT, refusing every clause the merge does not carry over.
fn plain_select(query: &Query) -> Result<&Select, String> {
    let clauses = query.with.is_some()
        || query.order_by.is_some()
        || query.limit_clause.is_some()
        || query.fetch.is_some()
        || !query.locks.is_empty()
        || query.for_clause.is_some()
        || query.settings.is_some()
        || query.format_clause.is_some()
        || !query.pipe_operators.is_empty();
    if clauses {
        return Err(refuse("derived table with WITH, ORDER BY, LIMIT/OFFSET/FETCH, locking or another query clause"));
    }
    let SetExpr::Select(select) = query.body.as_ref() else { return Err(refuse("derived table whose body is not a plain SELECT")) };
    let grouped = !matches!(&select.group_by, GroupByExpr::Expressions(g, m) if g.is_empty() && m.is_empty());
    let distinct = select.distinct.is_some() && select.distinct != Some(Distinct::All);
    let other = select.optimizer_hint.is_some()
        || select.select_modifiers.is_some()
        || select.top.is_some()
        || select.exclude.is_some()
        || select.into.is_some()
        || !select.lateral_views.is_empty()
        || select.prewhere.is_some()
        || !select.connect_by.is_empty()
        || !select.cluster_by.is_empty()
        || !select.distribute_by.is_empty()
        || !select.sort_by.is_empty()
        || select.having.is_some()
        || !select.named_window.is_empty()
        || select.qualify.is_some()
        || select.value_table_mode.is_some()
        || select.flavor != SelectFlavor::Standard;
    if grouped || distinct || other {
        return Err(refuse("derived table with DISTINCT, GROUP BY, HAVING or another SELECT clause (only a non-aggregating SELECT .. FROM .. WHERE is merged)"));
    }
    if select.from.is_empty() {
        return Err(refuse("derived table without FROM"));
    }
    Ok(select)
}

/// The derived columns `(name, defining expression)`, each free of what could raise or depend on a binding's value
/// where the merge does not evaluate it (see the module doc; the typed part of the check is in `resolve`).
fn derived_columns(select: &Select) -> Result<Vec<(String, Expr)>, String> {
    const AGGREGATES: [&str; 5] = ["sum", "count", "avg", "min", "max"];
    let mut columns: Vec<(String, Expr)> = vec![];
    for item in &select.projection {
        let (name, e) = match item {
            SelectItem::ExprWithAlias { expr, alias } => (folded(alias), expr),
            SelectItem::UnnamedExpr(e @ Expr::Identifier(id)) => (folded(id), e),
            SelectItem::UnnamedExpr(e @ Expr::CompoundIdentifier(parts)) => (folded(parts.last().expect("a compound identifier has parts")), e),
            other => return Err(refuse(format!("derived table item {other} (only `expr AS name` and plain columns)"))),
        };
        let found = visit_expressions(e, |x| match x {
            Expr::Function(f) if f.over.is_some() || AGGREGATES.contains(&f.name.to_string().to_lowercase().as_str()) => {
                ControlFlow::Break(format!("aggregate or window function {f} (an aggregating derived table)"))
            }
            Expr::Case { .. } => ControlFlow::Break(format!("CASE {x} (its conditions could raise on rows the merged query does not evaluate)")),
            Expr::Value(v) if matches!(v.value, SqlValue::Placeholder(_)) => ControlFlow::Break(format!("parameter {x}")),
            Expr::Subquery(_) | Expr::InSubquery { .. } | Expr::Exists { .. } => ControlFlow::Break(format!("subquery {x}")),
            _ => ControlFlow::Continue(()),
        });
        if let ControlFlow::Break(what) = found {
            return Err(refuse(format!("derived column {name}: {what}")));
        }
        if columns.iter().any(|(n, _)| *n == name) {
            return Err(refuse(format!("derived table with two columns named {name}")));
        }
        columns.push((name, e.clone()));
    }
    Ok(columns)
}

/// Replace every column reference in `e` by its derived column's parenthesized expression. The visit is post-order,
/// so a substituted expression is never visited again. `Err` names an outer subquery (whose own columns could share a
/// derived column's name) or a reference that is not a derived column.
fn substitute(e: &mut Expr, columns: &[(String, Expr)], alias: Option<&str>) -> Result<(), String> {
    let subquery = visit_expressions(e, |x| match x {
        Expr::Subquery(_) | Expr::InSubquery { .. } | Expr::Exists { .. } => ControlFlow::Break(x.to_string()),
        _ => ControlFlow::Continue(()),
    });
    if let ControlFlow::Break(x) = subquery {
        return Err(refuse(format!("subquery {x} in the query over a derived table")));
    }
    let mut refusal = None;
    let _ = visit_expressions_mut(e, |x| {
        let name = match x {
            Expr::Identifier(id) => Some(folded(id)),
            Expr::CompoundIdentifier(parts) => match parts.as_slice() {
                [table, column] if alias == Some(folded(table).as_str()) => Some(folded(column)),
                _ => None,
            },
            _ => return ControlFlow::Continue(()),
        };
        match name.and_then(|n| columns.iter().find(|(c, _)| *c == n)) {
            Some((_, derived)) => {
                *x = Expr::Nested(Box::new(derived.clone()));
                ControlFlow::Continue(())
            }
            None => {
                refusal = Some(format!("column {x} is not a column of the derived table"));
                ControlFlow::Break(())
            }
        }
    });
    refusal.map_or(Ok(()), |r| Err(refuse(r)))
}
