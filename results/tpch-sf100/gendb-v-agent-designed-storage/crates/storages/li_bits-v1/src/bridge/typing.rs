//! Type soundness at the granularity the evaluator's theorems need: every output value of a checked query on
//! a well-formed database lies in the comparison family of its static type (or is NULL), and every output row
//! has the static arity. (ORDER BY relies on it: the key order is a total preorder within a family.)
//!
//! Sections: value families and typed rows; list typing by index; expressions; aggregates (per-row arguments,
//! then values, dispatching MIN/MAX/AVG/DISTINCT to `bridge::aggs` and scalar functions to `bridge::fns`);
//! typed rows through the relational operators (via the element lemmas of `bridge::relation`); and queries.
//! Expressions and queries are one mutual recursion (a scalar subquery is an expression); the measures are
//! listed at `lemma_expr_family`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::typing::*;
use crate::spec::equality::*;
use crate::bridge::collect::*;
use crate::bridge::relation::*;
use crate::bridge::equality::*;
use crate::bridge::fns::*;
use crate::bridge::aggs::avg::*;
use crate::bridge::aggs::minmax::*;
use crate::bridge::aggs::distinct::*;

verus! {

// ------------------------------------------------------------------ value families and typed rows

/// Comparison family of a value (`spec::typing::family` of its type); NULL has none (-1).
pub open spec fn val_family(v: Val) -> int {
    match v {
        Val::Null => -1,
        Val::Bool(_) => 0,
        Val::Int(_) => 1,
        Val::Num { .. } => 1,
        Val::Date(_) => 2,
        Val::Ts(_) => 2,
        Val::Text(_) => 3,
    }
}

/// `v` is NULL or in the comparison family of `t`.
pub open spec fn val_has_family(v: Val, t: ScalarTy) -> bool {
    v is Null || val_family(v) == family(t)
}

/// A row of static column types `tys` (arity and families).
pub open spec fn row_typed(r: Row, tys: Seq<ColTy>) -> bool {
    r.len() == tys.len() && forall|i: int| 0 <= i < r.len() ==> val_has_family(#[trigger] r[i], tys[i].ty)
}

/// Concatenated typed rows are typed by the concatenated types.
pub proof fn lemma_row_typed_concat(a: Row, ta: Seq<ColTy>, b: Row, tb: Seq<ColTy>)
    requires row_typed(a, ta), row_typed(b, tb),
    ensures row_typed(a + b, ta + tb),
{
    let r = a + b;
    let t = ta + tb;
    assert forall|i: int| 0 <= i < r.len() implies val_has_family(#[trigger] r[i], t[i].ty) by {
        if i < a.len() {
            assert(r[i] == a[i] && t[i] == ta[i]);
        } else {
            assert(r[i] == b[i - a.len()] && t[i] == tb[i - a.len()]);
        }
    }
}

/// Making every type nullable keeps a row typed (families ignore nullability).
pub proof fn lemma_row_typed_nullable(r: Row, tys: Seq<ColTy>)
    requires row_typed(r, tys),
    ensures row_typed(r, nullable_all(tys)),
{
    assert forall|i: int| 0 <= i < r.len() implies val_has_family(#[trigger] r[i], nullable_all(tys)[i].ty) by {
        assert(nullable_all(tys)[i].ty == tys[i].ty);
    }
}

/// An all-NULL row of the right arity is typed.
pub proof fn lemma_null_row_typed(tys: Seq<ColTy>)
    ensures row_typed(null_row(tys.len()), tys),
{
    assert forall|i: int| 0 <= i < tys.len() implies val_has_family(#[trigger] null_row(tys.len())[i], tys[i].ty) by {}
}

/// A stored value of a column is in the family of the column's type.
pub proof fn lemma_value_in_column_family(v: Val, c: Column)
    requires value_in_column(v, c),
    ensures val_has_family(v, col_ty_of(c).ty),
{
}

// ------------------------------------------------------------------ list typing by index
// `type_exprs` / `type_aggs` recurse on the last element; these lemmas give the indexed view.

/// Element `i` of a typed expression list is typed, and its type is element `i` of the list's types.
pub proof fn lemma_type_exprs_elem(schema: Schema, tys: Seq<ColTy>, es: Seq<Expr>, i: int)
    requires type_exprs(schema, tys, es) is Some, 0 <= i < es.len(),
    ensures
        type_exprs(schema, tys, es)->0.len() == es.len(),
        type_expr(schema, tys, es[i]) is Some,
        type_exprs(schema, tys, es)->0[i] == type_expr(schema, tys, es[i])->0,
    decreases es.len(),
{
    let d = es.drop_last();
    if i < es.len() - 1 {
        lemma_type_exprs_elem(schema, tys, d, i);
    } else if d.len() > 0 {
        // The last element: only the prefix's typed length is needed.
        lemma_type_exprs_elem(schema, tys, d, 0);
    }
}

/// The same for aggregate lists.
pub proof fn lemma_type_aggs_elem(schema: Schema, tys: Seq<ColTy>, aggs: Seq<Agg>, i: int)
    requires type_aggs(schema, tys, aggs) is Some, 0 <= i < aggs.len(),
    ensures
        type_aggs(schema, tys, aggs)->0.len() == aggs.len(),
        type_agg(schema, tys, aggs[i]) is Some,
        type_aggs(schema, tys, aggs)->0[i] == type_agg(schema, tys, aggs[i])->0,
    decreases aggs.len(),
{
    let d = aggs.drop_last();
    if i < aggs.len() - 1 {
        lemma_type_aggs_elem(schema, tys, d, i);
    } else if d.len() > 0 {
        // The last element: only the prefix's typed length is needed.
        lemma_type_aggs_elem(schema, tys, d, 0);
    }
}

/// Length of a typed list (also for the empty list).
pub proof fn lemma_type_exprs_len(schema: Schema, tys: Seq<ColTy>, es: Seq<Expr>)
    requires type_exprs(schema, tys, es) is Some,
    ensures type_exprs(schema, tys, es)->0.len() == es.len(),
{
    if es.len() > 0 { lemma_type_exprs_elem(schema, tys, es, 0); }
}

pub proof fn lemma_type_aggs_len(schema: Schema, tys: Seq<ColTy>, aggs: Seq<Agg>)
    requires type_aggs(schema, tys, aggs) is Some,
    ensures type_aggs(schema, tys, aggs)->0.len() == aggs.len(),
{
    if aggs.len() > 0 { lemma_type_aggs_elem(schema, tys, aggs, 0); }
}

// ------------------------------------------------------------------ expressions

/// Every operator's result family is fixed by the operator and matches the static type. Mutually recursive
/// with `lemma_query_family` (scalar subqueries); measures: `lemma_expr_family` (e, 0), `lemma_exprs_family`
/// (es, 1), `lemma_project_typed` (exprs, 2), `lemma_agg_arg_typed` (a, 0), `lemma_agg_args_typed` (aggs, 1),
/// `lemma_aggregate_family` / `lemma_group_by_family` (q, 1), `lemma_query_family` (q, 2).
pub proof fn lemma_expr_family(db: Database, env: Row, tys: Seq<ColTy>, e: Expr)
    requires
        db_wf(db),
        row_typed(env, tys),
        type_expr(db.schema, tys, e) is Some,
        eval_expr(db, env, e) is Ok,
    ensures
        val_has_family(eval_expr(db, env, e)->Ok_0, type_expr(db.schema, tys, e)->0.ty),
    decreases e, 0nat,
{
    match e {
        Expr::Col(i) => {},
        Expr::Lit(l) => {},
        Expr::Neg { kind, arg } => {},
        Expr::Arith { op, kind, a, b } => {},
        Expr::Cast { cast: op, arg } => {},
        Expr::AddInterval { arg, months, days, micros } => {},
        Expr::Call { f, args } => {
            lemma_exprs_family(db, env, tys, args);
            lemma_fn_family(f, type_exprs(db.schema, tys, args)->0, eval_exprs(db, env, args)->Ok_0);
        },
        Expr::If { cond, then_e, else_e } => {
            // Branches of one shape: the taken branch's family is the result's.
            match eval_pred(db, env, *cond) {
                Ok(Truth::True) => lemma_expr_family(db, env, tys, *then_e),
                _ => lemma_expr_family(db, env, tys, *else_e),
            }
        },
        Expr::Subquery(q) => {
            let rows = eval_query(db, env, *q)->Ok_0;
            if rows.len() == 1 {
                lemma_query_family(db, env, tys, *q);
                assert(row_typed(rows[0], type_query(db.schema, tys, *q)->0));
            }
        },
    }
}

/// The values of a typed expression list form a row of its types.
pub proof fn lemma_exprs_family(db: Database, env: Row, tys: Seq<ColTy>, es: Seq<Expr>)
    requires
        db_wf(db),
        row_typed(env, tys),
        type_exprs(db.schema, tys, es) is Some,
        eval_exprs(db, env, es) is Ok,
    ensures
        row_typed(eval_exprs(db, env, es)->Ok_0, type_exprs(db.schema, tys, es)->0),
    decreases es, 1nat,
{
    let rs = expr_results(db, env, es);
    lemma_collect_ok(rs);
    let out = eval_exprs(db, env, es)->Ok_0;
    let t = type_exprs(db.schema, tys, es)->0;
    lemma_type_exprs_len(db.schema, tys, es);
    assert forall|i: int| 0 <= i < out.len() implies val_has_family(#[trigger] out[i], t[i].ty) by {
        assert(rs[i] == Ok::<Val, SqlError>(out[i]));
        lemma_type_exprs_elem(db.schema, tys, es, i);
        lemma_expr_family(db, env, tys, es[i]);
    }
}

// ------------------------------------------------------------------ aggregates

/// Static type of an aggregate's argument (`CountStar` has none).
pub open spec fn agg_arg_ty(schema: Schema, env: Seq<ColTy>, a: Agg) -> Option<ColTy>
    decreases a,
{
    match a {
        Agg::CountStar => None,
        Agg::Count(e) => type_expr(schema, env, e),
        Agg::Sum { kind, arg } => type_expr(schema, env, arg),
        Agg::Min(e) => type_expr(schema, env, e),
        Agg::Max(e) => type_expr(schema, env, e),
        Agg::Avg { kind, arg } => type_expr(schema, env, arg),
        Agg::DistinctAgg(inner) => agg_arg_ty(schema, env, *inner),
    }
}

/// A value in the family of an (optional) argument type.
pub open spec fn arg_typed(v: Val, t: Option<ColTy>) -> bool {
    t matches Some(c) ==> val_has_family(v, c.ty)
}

/// Every value is in the family of the (optional) argument type.
pub open spec fn vals_arg_typed(vs: Seq<Val>, t: Option<ColTy>) -> bool {
    forall|i: int| 0 <= i < vs.len() ==> arg_typed(#[trigger] vs[i], t)
}

/// One row of aggregate arguments (`r[j]` for aggregate `j`), each in its argument type's family.
pub open spec fn row_args_typed(schema: Schema, tys: Seq<ColTy>, aggs: Seq<Agg>, r: Row) -> bool {
    r.len() == aggs.len() && forall|j: int| 0 <= j < aggs.len() ==> arg_typed(#[trigger] r[j], agg_arg_ty(schema, tys, aggs[j]))
}

/// Every row of aggregate arguments is typed (`row_args_typed`).
pub open spec fn args_typed(schema: Schema, tys: Seq<ColTy>, aggs: Seq<Agg>, args: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < args.len() ==> row_args_typed(schema, tys, aggs, #[trigger] args[i])
}

/// The argument value of a typed aggregate in a typed environment lies in its argument type's family.
pub proof fn lemma_agg_arg_typed(db: Database, env: Row, tys: Seq<ColTy>, a: Agg)
    requires
        db_wf(db),
        row_typed(env, tys),
        type_agg(db.schema, tys, a) is Some,
        agg_arg(db, env, a) is Ok,
    ensures
        arg_typed(agg_arg(db, env, a)->Ok_0, agg_arg_ty(db.schema, tys, a)),
    decreases a, 0nat,
{
    match a {
        Agg::CountStar => {},
        Agg::Count(e) => lemma_expr_family(db, env, tys, e),
        Agg::Sum { kind, arg } => lemma_expr_family(db, env, tys, arg),
        Agg::Min(e) => lemma_expr_family(db, env, tys, e),
        Agg::Max(e) => lemma_expr_family(db, env, tys, e),
        Agg::Avg { kind, arg } => lemma_expr_family(db, env, tys, arg),
        Agg::DistinctAgg(inner) => lemma_agg_arg_typed(db, env, tys, *inner),
    }
}

/// The argument row of typed aggregates in a typed environment is typed.
pub proof fn lemma_agg_args_typed(db: Database, env: Row, tys: Seq<ColTy>, aggs: Seq<Agg>)
    requires
        db_wf(db),
        row_typed(env, tys),
        type_aggs(db.schema, tys, aggs) is Some,
        agg_args(db, env, aggs) is Ok,
    ensures
        row_args_typed(db.schema, tys, aggs, agg_args(db, env, aggs)->Ok_0),
    decreases aggs, 1nat,
{
    let rs = agg_arg_results(db, env, aggs);
    lemma_collect_ok(rs);
    lemma_agg_arg_results_index(db, env, aggs);
    let out = agg_args(db, env, aggs)->Ok_0;
    assert forall|j: int| 0 <= j < aggs.len() implies arg_typed(#[trigger] out[j], agg_arg_ty(db.schema, tys, aggs[j])) by {
        assert(rs[j] == Ok::<Val, SqlError>(out[j]));
        lemma_type_aggs_elem(db.schema, tys, aggs, j);
        lemma_agg_arg_typed(db, env, tys, aggs[j]);
    }
}

/// Argument values typed at `Some(t)` are each NULL or in the family of `t`: the premise of the per-aggregate
/// lemmas of `bridge::aggs`.
pub proof fn lemma_vals_in_family(vs: Seq<Val>, t: ColTy)
    requires vals_arg_typed(vs, Some(t)),
    ensures forall|i: int| 0 <= i < vs.len() ==> val_has_family(#[trigger] vs[i], t.ty),
{
    assert forall|i: int| 0 <= i < vs.len() implies val_has_family(#[trigger] vs[i], t.ty) by {
        assert(arg_typed(vs[i], Some(t)));
    }
}

/// An aggregate over argument values of its argument type has a value in its result type's family. COUNT and
/// SUM follow from their definitions; MIN/MAX, AVG and DISTINCT dispatch to `bridge::aggs`.
pub proof fn lemma_agg_family(schema: Schema, tys: Seq<ColTy>, a: Agg, vs: Seq<Val>)
    requires
        type_agg(schema, tys, a) is Some,
        agg_value(a, vs) is Ok,
        vals_arg_typed(vs, agg_arg_ty(schema, tys, a)),
    ensures
        val_has_family(agg_value(a, vs)->Ok_0, type_agg(schema, tys, a)->0.ty),
    decreases a,
{
    match a {
        Agg::Min(e) => {
            let t = type_expr(schema, tys, e)->0;
            lemma_vals_in_family(vs, t);
            lemma_min_family(t, vs);
        },
        Agg::Max(e) => {
            let t = type_expr(schema, tys, e)->0;
            lemma_vals_in_family(vs, t);
            lemma_max_family(t, vs);
        },
        Agg::Avg { kind, arg } => {
            let t = type_expr(schema, tys, arg)->0;
            lemma_vals_in_family(vs, t);
            lemma_avg_family(kind, t, vs);
        },
        Agg::DistinctAgg(inner) => {
            // The distinct values are argument values, so they are typed for the inner aggregate.
            let dv = distinct_vals(vs);
            lemma_distinct_vals_sub(vs);
            assert forall|m: int| 0 <= m < dv.len() implies arg_typed(#[trigger] dv[m], agg_arg_ty(schema, tys, *inner)) by {
                let i = choose|i: int| 0 <= i < vs.len() && vs[i] == dv[m];
                assert(arg_typed(vs[i], agg_arg_ty(schema, tys, a)));
            }
            lemma_agg_family(schema, tys, *inner, dv);
            lemma_distinct_agg_ty_family(*inner, type_agg(schema, tys, *inner)->0);
        },
        _ => {},
    }
}

/// The aggregate row of a group whose argument rows are typed is typed.
pub proof fn lemma_agg_row_family(schema: Schema, tys: Seq<ColTy>, aggs: Seq<Agg>, args: Seq<Row>)
    requires
        type_aggs(schema, tys, aggs) is Some,
        agg_row(aggs, args) is Ok,
        args_typed(schema, tys, aggs, args),
    ensures
        row_typed(agg_row(aggs, args)->Ok_0, type_aggs(schema, tys, aggs)->0),
{
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(args, j)));
    lemma_collect_ok(rs);
    let out = agg_row(aggs, args)->Ok_0;
    let t = type_aggs(schema, tys, aggs)->0;
    lemma_type_aggs_len(schema, tys, aggs);
    assert forall|j: int| 0 <= j < out.len() implies val_has_family(#[trigger] out[j], t[j].ty) by {
        assert(rs[j] == Ok::<Val, SqlError>(out[j]));
        lemma_type_aggs_elem(schema, tys, aggs, j);
        let col = column(args, j);
        assert forall|i: int| 0 <= i < col.len() implies arg_typed(#[trigger] col[i], agg_arg_ty(schema, tys, aggs[j])) by {
            assert(row_args_typed(schema, tys, aggs, args[i]));
            assert(col[i] == args[i][j]);
        }
        lemma_agg_family(schema, tys, aggs[j], col);
    }
}

// ------------------------------------------------------------------ typed rows through the operators

/// The static arity used for LEFT JOIN padding is the typed arity.
pub proof fn lemma_query_arity(schema: Schema, ctx: Seq<ColTy>, q: Query)
    requires type_query(schema, ctx, q) is Some,
    ensures type_query(schema, ctx, q)->0.len() == query_arity(schema, q),
    decreases q,
{
    match q {
        Query::Table(t) => {},
        Query::Filter { pred, input } => { lemma_query_arity(schema, ctx, *input); },
        Query::Project { exprs, input } => {
            let itys = type_query(schema, ctx, *input)->0;
            lemma_type_exprs_len(schema, ctx + itys, exprs);
        },
        Query::Product { left, right } => {
            lemma_query_arity(schema, ctx, *left);
            lemma_query_arity(schema, ctx, *right);
        },
        Query::LeftJoin { left, right, on } => {
            lemma_query_arity(schema, ctx, *left);
            lemma_query_arity(schema, ctx, *right);
            assert(nullable_all(type_query(schema, ctx, *right)->0).len() == type_query(schema, ctx, *right)->0.len());
        },
        Query::Aggregate { aggs, input } => {
            let itys = type_query(schema, ctx, *input)->0;
            lemma_type_aggs_len(schema, ctx + itys, aggs);
        },
        Query::GroupBy { keys, aggs, input } => {
            let itys = type_query(schema, ctx, *input)->0;
            lemma_type_aggs_len(schema, ctx + itys, aggs);
            lemma_type_exprs_len(schema, ctx + itys, keys);
        },
        Query::Distinct(input) => { lemma_query_arity(schema, ctx, *input); },
    }
}

/// Every row is typed by `tys`.
pub open spec fn all_typed(rows: Seq<Row>, tys: Seq<ColTy>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> row_typed(#[trigger] rows[i], tys)
}

/// WHERE keeps typed rows, for every truth sequence: the denotation's truth values are an internal `collect`
/// result, so the quantified form applies to them without naming them.
pub proof fn lemma_filter_typed(rows: Seq<Row>, tys: Seq<ColTy>)
    requires all_typed(rows, tys),
    ensures forall|truths: Seq<Truth>| all_typed(#[trigger] keep_true(rows, truths), tys),
{
    assert forall|truths: Seq<Truth>| all_typed(#[trigger] keep_true(rows, truths), tys) by {
        lemma_filter_typed_one(rows, truths, tys);
    }
}

pub proof fn lemma_filter_typed_one(rows: Seq<Row>, truths: Seq<Truth>, tys: Seq<ColTy>)
    requires all_typed(rows, tys),
    ensures all_typed(keep_true(rows, truths), tys),
{
    let out = keep_true(rows, truths);
    lemma_keep_true_sub(rows, truths);
    assert forall|i: int| 0 <= i < out.len() implies row_typed(#[trigger] out[i], tys) by {
        assert(rows.contains(out[i]));
        let j = choose|j: int| 0 <= j < rows.len() && rows[j] == out[i];
        assert(row_typed(rows[j], tys));
    }
}

/// SELECT list rows of typed input rows are typed.
pub proof fn lemma_project_typed(db: Database, ctx: Row, ctys: Seq<ColTy>, rows: Seq<Row>, itys: Seq<ColTy>, exprs: Seq<Expr>)
    requires
        db_wf(db),
        row_typed(ctx, ctys),
        all_typed(rows, itys),
        type_exprs(db.schema, ctys + itys, exprs) is Some,
        collect(Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], exprs))) is Ok,
    ensures
        all_typed(collect(Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], exprs)))->Ok_0,
            type_exprs(db.schema, ctys + itys, exprs)->0),
    decreases exprs, 2nat,
{
    let rs = Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], exprs));
    lemma_collect_ok(rs);
    let out = collect(rs)->Ok_0;
    let tys = type_exprs(db.schema, ctys + itys, exprs)->0;
    assert forall|i: int| 0 <= i < out.len() implies row_typed(#[trigger] out[i], tys) by {
        assert(rs[i] == Ok::<Row, SqlError>(out[i]));
        assert(row_typed(rows[i], itys));
        lemma_row_typed_concat(ctx, ctys, rows[i], itys);
        lemma_exprs_family(db, ctx + rows[i], ctys + itys, exprs);
    }
}

/// Cross-product rows are typed by the concatenated types.
pub proof fn lemma_product_typed(l: Seq<Row>, lt: Seq<ColTy>, r: Seq<Row>, rt: Seq<ColTy>)
    requires all_typed(l, lt), all_typed(r, rt),
    ensures all_typed(product_rows(l, r), lt + rt),
{
    let out = product_rows(l, r);
    lemma_product_rows_elems(l, r);
    assert forall|k: int| 0 <= k < out.len() implies row_typed(#[trigger] out[k], lt + rt) by {
        assert(is_concat(out[k], l, r));
        let (i, j) = choose|i: int, j: int| 0 <= i < l.len() && 0 <= j < r.len() && out[k] == #[trigger] l[i] + #[trigger] r[j];
        lemma_row_typed_concat(l[i], lt, r[j], rt);
    }
}

/// LEFT JOIN rows are typed by the left types and the nullable right types, for every ON truth matrix (quantified
/// as in `lemma_filter_typed`).
pub proof fn lemma_left_join_typed(l: Seq<Row>, lt: Seq<ColTy>, r: Seq<Row>, rt: Seq<ColTy>)
    requires all_typed(l, lt), all_typed(r, rt),
    ensures forall|truths: Seq<Seq<Truth>>| all_typed(#[trigger] left_join_rows(l, r, truths, rt.len()), lt + nullable_all(rt)),
{
    assert forall|truths: Seq<Seq<Truth>>| all_typed(#[trigger] left_join_rows(l, r, truths, rt.len()), lt + nullable_all(rt)) by {
        lemma_left_join_typed_one(l, lt, r, rt, truths);
    }
}

pub proof fn lemma_left_join_typed_one(l: Seq<Row>, lt: Seq<ColTy>, r: Seq<Row>, rt: Seq<ColTy>, truths: Seq<Seq<Truth>>)
    requires all_typed(l, lt), all_typed(r, rt),
    ensures all_typed(left_join_rows(l, r, truths, rt.len()), lt + nullable_all(rt)),
{
    let n = rt.len();
    let out = left_join_rows(l, r, truths, n);
    let tys = lt + nullable_all(rt);
    lemma_left_join_rows_elems(l, r, truths, n);
    assert forall|k: int| 0 <= k < out.len() implies row_typed(#[trigger] out[k], tys) by {
        if is_concat(out[k], l, r) {
            let (i, j) = choose|i: int, j: int| 0 <= i < l.len() && 0 <= j < r.len() && out[k] == #[trigger] l[i] + #[trigger] r[j];
            lemma_row_typed_nullable(r[j], rt);
            lemma_row_typed_concat(l[i], lt, r[j], nullable_all(rt));
        } else {
            let i = choose|i: int| 0 <= i < l.len() && out[k] == #[trigger] l[i] + null_row(n);
            lemma_null_row_typed(nullable_all(rt));
            lemma_row_typed_concat(l[i], lt, null_row(n), nullable_all(rt));
        }
    }
}

/// GROUP BY output rows are typed, given typed key tuples and typed aggregate arguments of every input row
/// (`lemma_group_by_family` establishes both per row).
pub proof fn lemma_group_typed(schema: Schema, tys: Seq<ColTy>, prepared: Seq<(Row, Row)>, keys: Seq<Expr>, aggs: Seq<Agg>)
    requires
        type_exprs(schema, tys, keys) is Some,
        type_aggs(schema, tys, aggs) is Some,
        forall|i: int| 0 <= i < prepared.len() ==> row_typed((#[trigger] prepared[i]).0, type_exprs(schema, tys, keys)->0)
            && row_args_typed(schema, tys, aggs, prepared[i].1),
        group_rows(aggs, prepared.map_values(|p: (Row, Row)| p.0), prepared.map_values(|p: (Row, Row)| p.1)) is Ok,
    ensures
        all_typed(
            group_rows(aggs, prepared.map_values(|p: (Row, Row)| p.0), prepared.map_values(|p: (Row, Row)| p.1))->Ok_0,
            type_exprs(schema, tys, keys)->0 + type_aggs(schema, tys, aggs)->0),
{
    let ks = prepared.map_values(|p: (Row, Row)| p.0);
    let args = prepared.map_values(|p: (Row, Row)| p.1);
    let out = group_rows(aggs, ks, args)->Ok_0;
    let kt = type_exprs(schema, tys, keys)->0;
    let at = type_aggs(schema, tys, aggs)->0;
    let d = distinct_rows(ks);
    lemma_distinct_rows_sub(ks);
    let gs = Seq::new(d.len(), |g: int|
        match agg_row(aggs, group_members(ks, args, d[g])) {
            Ok(a) => Ok(d[g] + a),
            Err(e) => Err(e),
        });
    lemma_collect_ok(gs);
    assert forall|g: int| 0 <= g < out.len() implies row_typed(#[trigger] out[g], kt + at) by {
        assert(gs[g] == Ok::<Row, SqlError>(out[g]));
        let members = group_members(ks, args, d[g]);
        lemma_group_members_sub(ks, args, d[g]);
        assert forall|m: int| 0 <= m < members.len() implies row_args_typed(schema, tys, aggs, #[trigger] members[m]) by {
            let i = choose|i: int| 0 <= i < args.len() && args[i] == members[m];
            assert(args[i] == prepared[i].1);
        }
        lemma_agg_row_family(schema, tys, aggs, members);
        assert(ks.contains(d[g]));
        let i = choose|i: int| 0 <= i < ks.len() && ks[i] == d[g];
        assert(ks[i] == prepared[i].0);
        lemma_row_typed_concat(d[g], kt, agg_row(aggs, members)->Ok_0, at);
    }
}

/// The rows of a table of a well-formed database are typed by its column types.
pub proof fn lemma_table_typed(db: Database, t: int)
    requires db_wf(db), 0 <= t < db.schema.len(),
    ensures all_typed(db.tables[t], table_tys(db.schema[t])),
{
    let rows = db.tables[t];
    let ts = db.schema[t];
    let tys = table_tys(ts);
    assert forall|i: int| 0 <= i < rows.len() implies row_typed(#[trigger] rows[i], tys) by {
        let r = rows[i];
        assert(row_in_table(r, ts));
        assert forall|c: int| 0 <= c < r.len() implies val_has_family(#[trigger] r[c], tys[c].ty) by {
            lemma_value_in_column_family(r[c], ts.columns[c]);
        }
    }
}

// ------------------------------------------------------------------ queries

/// Type soundness: rows of a checked query on a well-formed database have the query's static types.
pub proof fn lemma_query_family(db: Database, ctx: Row, ctys: Seq<ColTy>, q: Query)
    requires
        db_wf(db),
        row_typed(ctx, ctys),
        type_query(db.schema, ctys, q) is Some,
        eval_query(db, ctx, q) is Ok,
    ensures
        all_typed(eval_query(db, ctx, q)->Ok_0, type_query(db.schema, ctys, q)->0),
    decreases q, 2nat,
{
    let out = eval_query(db, ctx, q)->Ok_0;
    let tys = type_query(db.schema, ctys, q)->0;
    match q {
        Query::Table(t) => {
            lemma_table_typed(db, t as int);
        },
        Query::Filter { pred, input } => {
            let rows = eval_query(db, ctx, *input)->Ok_0;
            lemma_query_family(db, ctx, ctys, *input);
            lemma_filter_typed(rows, tys);
        },
        Query::Project { exprs, input } => {
            lemma_query_family(db, ctx, ctys, *input);
            lemma_collect_pointwise::<Row>();
            lemma_project_typed(db, ctx, ctys, eval_query(db, ctx, *input)->Ok_0, type_query(db.schema, ctys, *input)->0, exprs);
        },
        Query::Product { left, right } => {
            lemma_query_family(db, ctx, ctys, *left);
            lemma_query_family(db, ctx, ctys, *right);
            lemma_product_typed(eval_query(db, ctx, *left)->Ok_0, type_query(db.schema, ctys, *left)->0,
                eval_query(db, ctx, *right)->Ok_0, type_query(db.schema, ctys, *right)->0);
        },
        Query::LeftJoin { left, right, on } => {
            let l = eval_query(db, ctx, *left)->Ok_0;
            let r = eval_query(db, ctx, *right)->Ok_0;
            lemma_query_family(db, ctx, ctys, *left);
            lemma_query_family(db, ctx, ctys, *right);
            lemma_query_arity(db.schema, ctys, *right);
            lemma_left_join_typed(l, type_query(db.schema, ctys, *left)->0, r, type_query(db.schema, ctys, *right)->0);
        },
        Query::Aggregate { .. } => lemma_aggregate_family(db, ctx, ctys, q),
        Query::GroupBy { .. } => lemma_group_by_family(db, ctx, ctys, q),
        Query::Distinct(input) => {
            let rows = eval_query(db, ctx, *input)->Ok_0;
            lemma_query_family(db, ctx, ctys, *input);
            lemma_distinct_rows_sub(rows);
            assert forall|g: int| 0 <= g < out.len() implies row_typed(#[trigger] out[g], tys) by {
                let i = choose|i: int| 0 <= i < rows.len() && rows[i] == out[g];
            }
        },
    }
}

/// Aggregate without GROUP BY: every input row's argument row is typed, so the one output row is.
pub proof fn lemma_aggregate_family(db: Database, ctx: Row, ctys: Seq<ColTy>, q: Query)
    requires
        q is Aggregate,
        db_wf(db),
        row_typed(ctx, ctys),
        type_query(db.schema, ctys, q) is Some,
        eval_query(db, ctx, q) is Ok,
    ensures
        all_typed(eval_query(db, ctx, q)->Ok_0, type_query(db.schema, ctys, q)->0),
    decreases q, 1nat,
{
    if let Query::Aggregate { aggs, input } = q {
        let rows = eval_query(db, ctx, *input)->Ok_0;
        let itys = type_query(db.schema, ctys, *input)->0;
        lemma_query_family(db, ctx, ctys, *input);
        lemma_collect_pointwise::<Row>();
        let rs = Seq::new(rows.len(), |i: int| agg_args(db, ctx + rows[i], aggs));
        lemma_collect_ok(rs);
        let args = collect(rs)->Ok_0;
        assert forall|i: int| 0 <= i < args.len() implies row_args_typed(db.schema, ctys + itys, aggs, #[trigger] args[i]) by {
            assert(rs[i] == Ok::<Row, SqlError>(args[i]));
            assert(row_typed(rows[i], itys));
            lemma_row_typed_concat(ctx, ctys, rows[i], itys);
            lemma_agg_args_typed(db, ctx + rows[i], ctys + itys, aggs);
        }
        lemma_agg_row_family(db.schema, ctys + itys, aggs, args);
    }
}

/// GROUP BY: every input row's key tuple and argument row are typed, so every group row is.
pub proof fn lemma_group_by_family(db: Database, ctx: Row, ctys: Seq<ColTy>, q: Query)
    requires
        q is GroupBy,
        db_wf(db),
        row_typed(ctx, ctys),
        type_query(db.schema, ctys, q) is Some,
        eval_query(db, ctx, q) is Ok,
    ensures
        all_typed(eval_query(db, ctx, q)->Ok_0, type_query(db.schema, ctys, q)->0),
    decreases q, 1nat,
{
    if let Query::GroupBy { keys, aggs, input } = q {
        let rows = eval_query(db, ctx, *input)->Ok_0;
        let itys = type_query(db.schema, ctys, *input)->0;
        let tys = ctys + itys;
        lemma_query_family(db, ctx, ctys, *input);
        lemma_collect_pointwise::<(Row, Row)>();
        let rs = Seq::new(rows.len(), |i: int| group_input(db, ctx + rows[i], keys, aggs));
        // `eval_query` inlines `group_input`; identify its per-row sequence with `rs`.
        assert(collect(rs) == collect(Seq::new(rows.len(), |i: int|
            match eval_exprs(db, ctx + rows[i], keys) {
                Err(err) => Err(err),
                Ok(k) => match agg_args(db, ctx + rows[i], aggs) {
                    Err(err) => Err(err),
                    Ok(a) => Ok((k, a)),
                },
            })));
        lemma_collect_ok(rs);
        let prepared = collect(rs)->Ok_0;
        assert forall|i: int| 0 <= i < prepared.len() implies
            row_typed((#[trigger] prepared[i]).0, type_exprs(db.schema, tys, keys)->0)
            && row_args_typed(db.schema, tys, aggs, prepared[i].1) by {
            assert(rs[i] == Ok::<(Row, Row), SqlError>(prepared[i]));
            assert(row_typed(rows[i], itys));
            lemma_row_typed_concat(ctx, ctys, rows[i], itys);
            lemma_exprs_family(db, ctx + rows[i], tys, keys);
            lemma_agg_args_typed(db, ctx + rows[i], tys, aggs);
        }
        lemma_group_typed(db.schema, tys, prepared, keys, aggs);
    }
}

} // verus!
