//! L3 soundness (engine toolkit; nothing here names a query, a table or a column).
//!
//! `lemma_query_sound` (and the expression, list, condition and aggregate forms): on a well-formed database, in a
//! context whose values lie in the context classes, a node the analysis of `engine_link::classes` classifies
//! raises only the errors its analysis allows, its values (rows) lie in the analysed classes (and a query marked
//! `one_row` yields at most one row), and where the analysis says it fits, it is inside the executable domain.
//! The three classes follow (`lemma_*_total`, `lemma_*_uniform`, `lemma_*_exact`).
//!
//! The proof follows the analysis' mutual recursion: expressions `(e, 2)` dispatching to one lemma per
//! constructor at `(e, 1)`, lists `(es, 0)`, conditions `(p, 1)`, aggregate arguments `(a, 0)` and `(aggs, 0)`,
//! queries `(q, 2)` dispatching to one lemma per constructor at `(q, 1)`. Each step unfolds one node of the
//! denotation through the named per-row sequences of `exec::relational::domain` (with the denotation hidden) and
//! applies one value-level lemma of `engine_link::classes_values`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::typing::*;
use crate::spec::equality::*;
use crate::spec::fns::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::bridge::collect::*;
use crate::bridge::relation::*;
use crate::bridge::equality::*;
use crate::link::expr::{closed_expr, closed_db, lemma_expr_closed};
use crate::link::query::lemma_row_exact;
use crate::engine_link::classes::*;
use crate::engine_link::classes_values::*;
use crate::engine_link::locality::{lemma_fits_project_unfold, lemma_fits_aggregate_unfold};

verus! {

// ------------------------------------------------------------------------------------- what soundness says

pub open spec fn expr_sound(db: Database, env: Row, e: Expr, i: ExprInfo) -> bool {
    &&& errs_allow(eval_expr(db, env, e), i.errs)
    &&& (eval_expr(db, env, e) matches Ok(v) ==> in_class(v, i.cls))
    &&& (i.fits ==> fits_expr(db, env, e))
}

pub open spec fn exprs_sound(db: Database, env: Row, es: Seq<Expr>, l: ListInfo) -> bool {
    &&& errs_allow(eval_exprs(db, env, es), l.errs)
    &&& (eval_exprs(db, env, es) matches Ok(vs) ==> row_in(vs, l.classes))
    &&& (l.fits ==> fits_exprs(db, env, es))
}

pub open spec fn pred_sound(db: Database, env: Row, p: Pred, i: PredInfo) -> bool {
    &&& errs_allow(eval_pred(db, env, p), i.errs)
    &&& (i.fits ==> fits_pred(db, env, p))
}

pub open spec fn agg_arg_sound(db: Database, env: Row, a: Agg, i: ExprInfo) -> bool {
    &&& errs_allow(agg_arg(db, env, a), i.errs)
    &&& (agg_arg(db, env, a) matches Ok(v) ==> in_class(v, i.cls))
    &&& (i.fits ==> fits_agg_arg(db, env, a))
}

pub open spec fn aggs_arg_sound(db: Database, env: Row, aggs: Seq<Agg>, l: ListInfo) -> bool {
    &&& errs_allow(agg_args(db, env, aggs), l.errs)
    &&& (agg_args(db, env, aggs) matches Ok(vs) ==> row_in(vs, l.classes))
    &&& (l.fits ==> fits_agg_args(db, env, aggs))
}

pub open spec fn query_sound(db: Database, ctx: Row, q: Query, qi: QueryInfo) -> bool {
    &&& errs_allow(eval_query(db, ctx, q), qi.errs)
    &&& (eval_query(db, ctx, q) matches Ok(rows) ==> rows_in(rows, qi.cols) && (qi.one_row ==> rows.len() <= 1))
    &&& (qi.fits ==> fits_query(db, ctx, q))
}

// ------------------------------------------------------------------------------------- list analyses by index

/// Containment of error sets is transitive.
pub proof fn lemma_errs_le_trans(a: Errs, b: Errs, c: Errs)
    requires errs_le(a, b), errs_le(b, c),
    ensures errs_le(a, c),
{
}

/// `exprs_info` element by element: each expression's analysis, its class at its position, its errors contained.
pub proof fn lemma_exprs_info_index(schema: Schema, env: Seq<VClass>, es: Seq<Expr>)
    requires exprs_info(schema, env, es) is Some,
    ensures ({
        let l = exprs_info(schema, env, es)->Some_0;
        &&& l.classes.len() == es.len()
        &&& forall|i: int| 0 <= i < es.len() ==> {
            &&& #[trigger] expr_info(schema, env, es[i]) is Some
            &&& expr_info(schema, env, es[i])->Some_0.cls == l.classes[i]
            &&& errs_le(expr_info(schema, env, es[i])->Some_0.errs, l.errs)
            &&& (l.fits ==> expr_info(schema, env, es[i])->Some_0.fits)
        }
    }),
    decreases es.len(),
{
    if es.len() > 0 {
        let d = es.drop_last();
        lemma_exprs_info_index(schema, env, d);
        let l = exprs_info(schema, env, es)->Some_0;
        let ld = exprs_info(schema, env, d)->Some_0;
        let x = expr_info(schema, env, es.last())->Some_0;
        lemma_errs_join(ld.errs, x.errs);
        assert forall|i: int| 0 <= i < es.len() implies {
            &&& #[trigger] expr_info(schema, env, es[i]) is Some
            &&& expr_info(schema, env, es[i])->Some_0.cls == l.classes[i]
            &&& errs_le(expr_info(schema, env, es[i])->Some_0.errs, l.errs)
            &&& (l.fits ==> expr_info(schema, env, es[i])->Some_0.fits)
        } by {
            if i < d.len() {
                assert(d[i] == es[i]);
                lemma_errs_le_trans(expr_info(schema, env, es[i])->Some_0.errs, ld.errs, l.errs);
            }
        }
    }
}

/// `aggs_arg_info` element by element.
pub proof fn lemma_aggs_arg_info_index(schema: Schema, env: Seq<VClass>, aggs: Seq<Agg>)
    requires aggs_arg_info(schema, env, aggs) is Some,
    ensures ({
        let l = aggs_arg_info(schema, env, aggs)->Some_0;
        &&& l.classes.len() == aggs.len()
        &&& forall|j: int| 0 <= j < aggs.len() ==> {
            &&& #[trigger] agg_arg_info(schema, env, aggs[j]) is Some
            &&& agg_arg_info(schema, env, aggs[j])->Some_0.cls == l.classes[j]
            &&& errs_le(agg_arg_info(schema, env, aggs[j])->Some_0.errs, l.errs)
            &&& (l.fits ==> agg_arg_info(schema, env, aggs[j])->Some_0.fits)
        }
    }),
    decreases aggs.len(),
{
    if aggs.len() > 0 {
        let d = aggs.drop_last();
        lemma_aggs_arg_info_index(schema, env, d);
        let l = aggs_arg_info(schema, env, aggs)->Some_0;
        let ld = aggs_arg_info(schema, env, d)->Some_0;
        let x = agg_arg_info(schema, env, aggs.last())->Some_0;
        lemma_errs_join(ld.errs, x.errs);
        assert forall|j: int| 0 <= j < aggs.len() implies {
            &&& #[trigger] agg_arg_info(schema, env, aggs[j]) is Some
            &&& agg_arg_info(schema, env, aggs[j])->Some_0.cls == l.classes[j]
            &&& errs_le(agg_arg_info(schema, env, aggs[j])->Some_0.errs, l.errs)
            &&& (l.fits ==> agg_arg_info(schema, env, aggs[j])->Some_0.fits)
        } by {
            if j < d.len() {
                assert(d[j] == aggs[j]);
                lemma_errs_le_trans(agg_arg_info(schema, env, aggs[j])->Some_0.errs, ld.errs, l.errs);
            }
        }
    }
}

/// `aggs_value_info` element by element.
pub proof fn lemma_aggs_value_info_index(aggs: Seq<Agg>, cs: Seq<VClass>)
    requires aggs_value_info(aggs, cs) is Some,
    ensures ({
        let l = aggs_value_info(aggs, cs)->Some_0;
        &&& l.classes.len() == aggs.len()
        &&& cs.len() == aggs.len()
        &&& forall|j: int| 0 <= j < aggs.len() ==> {
            &&& #[trigger] agg_value_info(aggs[j], cs[j]) is Some
            &&& agg_value_info(aggs[j], cs[j])->Some_0.cls == l.classes[j]
            &&& errs_le(agg_value_info(aggs[j], cs[j])->Some_0.errs, l.errs)
            &&& (l.fits ==> agg_value_info(aggs[j], cs[j])->Some_0.fits)
        }
    }),
    decreases aggs.len(),
{
    if aggs.len() > 0 {
        let (d, dc) = (aggs.drop_last(), cs.drop_last());
        lemma_aggs_value_info_index(d, dc);
        let l = aggs_value_info(aggs, cs)->Some_0;
        let ld = aggs_value_info(d, dc)->Some_0;
        let x = agg_value_info(aggs.last(), cs.last())->Some_0;
        lemma_errs_join(ld.errs, x.errs);
        assert forall|j: int| 0 <= j < aggs.len() implies {
            &&& #[trigger] agg_value_info(aggs[j], cs[j]) is Some
            &&& agg_value_info(aggs[j], cs[j])->Some_0.cls == l.classes[j]
            &&& errs_le(agg_value_info(aggs[j], cs[j])->Some_0.errs, l.errs)
            &&& (l.fits ==> agg_value_info(aggs[j], cs[j])->Some_0.fits)
        } by {
            if j < d.len() {
                assert(d[j] == aggs[j] && dc[j] == cs[j]);
                lemma_errs_le_trans(agg_value_info(aggs[j], cs[j])->Some_0.errs, ld.errs, l.errs);
            }
        }
    }
}

/// Every expression of a list inside its domain: the list is.
pub proof fn lemma_fits_exprs_all(db: Database, env: Row, es: Seq<Expr>)
    requires forall|i: int| 0 <= i < es.len() ==> #[trigger] fits_expr(db, env, es[i]),
    ensures fits_exprs(db, env, es),
    decreases es.len(),
{
    if es.len() > 0 {
        let d = es.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] fits_expr(db, env, d[i]) by {
            assert(d[i] == es[i]);
        }
        lemma_fits_exprs_all(db, env, d);
        lemma_fits_exprs_unfold(db, env, es);
        assert(fits_expr(db, env, es[es.len() - 1]));
    }
}

/// Number of output columns of a classified query: `query_arity`.
pub proof fn lemma_query_info_arity(schema: Schema, ctx: Seq<VClass>, q: Query)
    requires query_info(schema, ctx, q) is Some,
    ensures query_info(schema, ctx, q)->Some_0.cols.len() == query_arity(schema, q),
    decreases q,
{
    match q {
        Query::Table(t) => {},
        Query::Filter { pred, input } => lemma_query_info_arity(schema, ctx, *input),
        Query::Project { exprs, input } => {
            let i = query_info(schema, ctx, *input)->Some_0;
            lemma_exprs_info_index(schema, ctx + i.cols, exprs);
        },
        Query::Product { left, right } => {
            lemma_query_info_arity(schema, ctx, *left);
            lemma_query_info_arity(schema, ctx, *right);
        },
        Query::LeftJoin { left, right, on } => {
            lemma_query_info_arity(schema, ctx, *left);
            lemma_query_info_arity(schema, ctx, *right);
        },
        Query::Aggregate { aggs, input } => {
            let i = query_info(schema, ctx, *input)->Some_0;
            let a = aggs_arg_info(schema, ctx + i.cols, aggs)->Some_0;
            lemma_aggs_value_info_index(aggs, a.classes);
        },
        Query::GroupBy { keys, aggs, input } => {
            let i = query_info(schema, ctx, *input)->Some_0;
            let a = aggs_arg_info(schema, ctx + i.cols, aggs)->Some_0;
            lemma_exprs_info_index(schema, ctx + i.cols, keys);
            lemma_aggs_value_info_index(aggs, a.classes);
        },
        Query::Distinct(input) => lemma_query_info_arity(schema, ctx, *input),
    }
}

// ------------------------------------------------------------------------------------- closed expressions

/// A closed expression is inside the domain in every environment exactly when it is once.
pub proof fn lemma_closed_fits(db: Database, env: Row, e: Expr)
    requires closed_expr(e),
    ensures fits_expr(db, env, e) == fits_expr(closed_db(), Seq::empty(), e),
    decreases e,
{
    match e {
        Expr::Neg { kind, arg } => {
            lemma_closed_fits(db, env, *arg);
            lemma_expr_closed(db, env, *arg);
        },
        Expr::Arith { op, kind, a, b } => {
            lemma_closed_fits(db, env, *a);
            lemma_closed_fits(db, env, *b);
            lemma_expr_closed(db, env, *a);
            lemma_expr_closed(db, env, *b);
        },
        Expr::Cast { cast, arg } => lemma_closed_fits(db, env, *arg),
        Expr::AddInterval { arg, months, days, micros } => lemma_closed_fits(db, env, *arg),
        _ => {},
    }
}

proof fn lemma_closed_sound(db: Database, env: Row, e: Expr)
    requires closed_info(e) is Some,
    ensures expr_sound(db, env, e, closed_info(e)->Some_0),
{
    let v = closed_value(e)->Some_0;
    lemma_expr_closed(db, env, e);
    lemma_closed_fits(db, env, e);
    lemma_const_class(v);
}

// ------------------------------------------------------------------------------------- expressions

/// L3 soundness of the expression analysis (`expr_sound`): errors allowed, value in class, domain when it fits.
pub proof fn lemma_expr_sound(db: Database, env: Row, cls: Seq<VClass>, e: Expr)
    requires db_wf(db), row_in(env, cls), expr_info(db.schema, cls, e) is Some,
    ensures expr_sound(db, env, e, expr_info(db.schema, cls, e)->Some_0),
    decreases e, 2nat,
{
    if closed_expr(e) {
        lemma_closed_sound(db, env, e);
    } else {
        match e {
            Expr::Col(i) => {
                assert(in_class(env[i as int], cls[i as int]));
            },
            Expr::Lit(_) => {},
            Expr::Neg { .. } | Expr::Cast { .. } | Expr::AddInterval { .. } => lemma_unary_sound(db, env, cls, e),
            Expr::Arith { .. } => lemma_arith_sound(db, env, cls, e),
            Expr::Call { .. } => lemma_call_sound(db, env, cls, e),
            Expr::If { .. } => lemma_if_sound(db, env, cls, e),
            Expr::Subquery(_) => lemma_subquery_sound(db, env, cls, e),
        }
    }
}

proof fn lemma_unary_sound(db: Database, env: Row, cls: Seq<VClass>, e: Expr)
    requires
        db_wf(db), row_in(env, cls), !closed_expr(e), e is Neg || e is Cast || e is AddInterval,
        expr_info(db.schema, cls, e) is Some,
    ensures expr_sound(db, env, e, expr_info(db.schema, cls, e)->Some_0),
    decreases e, 1nat,
{
    let info = expr_info(db.schema, cls, e)->Some_0;
    match e {
        Expr::Neg { kind, arg } => {
            lemma_expr_sound(db, env, cls, *arg);
            let a = expr_info(db.schema, cls, *arg)->Some_0;
            let o = neg_op(kind, a.cls)->Some_0;
            lemma_errs_join(a.errs, o.errs);
            if let Ok(v) = eval_expr(db, env, *arg) {
                lemma_neg_op(kind, a.cls, v);
            }
        },
        Expr::Cast { cast, arg } => {
            lemma_expr_sound(db, env, cls, *arg);
            let a = expr_info(db.schema, cls, *arg)->Some_0;
            let o = cast_op(cast, a.cls)->Some_0;
            lemma_errs_join(a.errs, o.errs);
            if let Ok(v) = eval_expr(db, env, *arg) {
                lemma_cast_op(cast, a.cls, v);
            }
        },
        Expr::AddInterval { arg, months, days, micros } => {
            lemma_expr_sound(db, env, cls, *arg);
            let a = expr_info(db.schema, cls, *arg)->Some_0;
            let o = interval_op(months, days, micros, a.cls)->Some_0;
            lemma_errs_join(a.errs, o.errs);
            if let Ok(v) = eval_expr(db, env, *arg) {
                lemma_interval_op(months, days, micros, a.cls, v);
            }
        },
        _ => {},
    }
}

proof fn lemma_arith_sound(db: Database, env: Row, cls: Seq<VClass>, e: Expr)
    requires db_wf(db), row_in(env, cls), !closed_expr(e), e is Arith, expr_info(db.schema, cls, e) is Some,
    ensures expr_sound(db, env, e, expr_info(db.schema, cls, e)->Some_0),
    decreases e, 1nat,
{
    if let Expr::Arith { op, kind, a, b } = e {
        lemma_expr_sound(db, env, cls, *a);
        lemma_expr_sound(db, env, cls, *b);
        let x = expr_info(db.schema, cls, *a)->Some_0;
        let y = expr_info(db.schema, cls, *b)->Some_0;
        let o = arith_op(op, kind, x.cls, y.cls)->Some_0;
        lemma_errs_join(x.errs, y.errs);
        let xy = errs_join(x.errs, y.errs)->Some_0;
        lemma_errs_join(xy, o.errs);
        let j = errs_join(xy, o.errs)->Some_0;
        lemma_errs_le_trans(x.errs, xy, j);
        lemma_errs_le_trans(y.errs, xy, j);
        if let (Ok(va), Ok(vb)) = (eval_expr(db, env, *a), eval_expr(db, env, *b)) {
            lemma_arith_op(op, kind, x.cls, y.cls, va, vb);
        }
    }
}

proof fn lemma_call_sound(db: Database, env: Row, cls: Seq<VClass>, e: Expr)
    requires db_wf(db), row_in(env, cls), !closed_expr(e), e is Call, expr_info(db.schema, cls, e) is Some,
    ensures expr_sound(db, env, e, expr_info(db.schema, cls, e)->Some_0),
    decreases e, 1nat,
{
    if let Expr::Call { f, args } = e {
        lemma_exprs_sound(db, env, cls, args);
        let l = exprs_info(db.schema, cls, args)->Some_0;
        let o = call_op(f, args, l.classes)->Some_0;
        lemma_errs_join(l.errs, o.errs);
        if let Ok(vs) = eval_exprs(db, env, args) {
            lemma_call_op(db, env, f, args, l.classes, vs);
        }
    }
}

proof fn lemma_if_sound(db: Database, env: Row, cls: Seq<VClass>, e: Expr)
    requires db_wf(db), row_in(env, cls), !closed_expr(e), e is If, expr_info(db.schema, cls, e) is Some,
    ensures expr_sound(db, env, e, expr_info(db.schema, cls, e)->Some_0),
    decreases e, 1nat,
{
    if let Expr::If { cond, then_e, else_e } = e {
        lemma_pred_sound(db, env, cls, *cond);
        lemma_expr_sound(db, env, cls, *then_e);
        lemma_expr_sound(db, env, cls, *else_e);
        let c = pred_info(db.schema, cls, *cond)->Some_0;
        let t = expr_info(db.schema, cls, *then_e)->Some_0;
        let f = expr_info(db.schema, cls, *else_e)->Some_0;
        lemma_errs_join(c.errs, t.errs);
        let ct = errs_join(c.errs, t.errs)->Some_0;
        lemma_errs_join(ct, f.errs);
        let j = errs_join(ct, f.errs)->Some_0;
        lemma_errs_le_trans(c.errs, ct, j);
        lemma_errs_le_trans(t.errs, ct, j);
        if let Ok(v) = eval_expr(db, env, *then_e) {
            lemma_class_join(v, t.cls, f.cls);
        }
        if let Ok(v) = eval_expr(db, env, *else_e) {
            lemma_class_join(v, t.cls, f.cls);
        }
    }
}

proof fn lemma_subquery_sound(db: Database, env: Row, cls: Seq<VClass>, e: Expr)
    requires db_wf(db), row_in(env, cls), !closed_expr(e), e is Subquery, expr_info(db.schema, cls, e) is Some,
    ensures expr_sound(db, env, e, expr_info(db.schema, cls, e)->Some_0),
    decreases e, 1nat,
{
    if let Expr::Subquery(q) = e {
        lemma_query_sound(db, env, cls, *q);
        let qi = query_info(db.schema, cls, *q)->Some_0;
        let card = if qi.one_row { Errs::Never } else { Errs::Only(SqlError::CardinalityViolation) };
        lemma_errs_join(qi.errs, card);
        if let Ok(rows) = eval_query(db, env, *q) {
            if rows.len() == 1 {
                assert(row_in(rows[0], qi.cols));
                assert(in_class(rows[0][0], qi.cols[0]));
            }
        }
    }
}

/// L3 soundness of the list analysis: errors allowed, values a row of the classes, domain when it fits.
pub proof fn lemma_exprs_sound(db: Database, env: Row, cls: Seq<VClass>, es: Seq<Expr>)
    requires db_wf(db), row_in(env, cls), exprs_info(db.schema, cls, es) is Some,
    ensures exprs_sound(db, env, es, exprs_info(db.schema, cls, es)->Some_0),
    decreases es, 0nat,
{
    let l = exprs_info(db.schema, cls, es)->Some_0;
    lemma_exprs_info_index(db.schema, cls, es);
    let rs = expr_results(db, env, es);
    lemma_expr_results_index(db, env, es);
    assert forall|i: int| 0 <= i < es.len() implies
        #[trigger] expr_sound(db, env, es[i], expr_info(db.schema, cls, es[i])->Some_0) by {
        lemma_expr_sound(db, env, cls, es[i]);
    }
    assert forall|i: int| 0 <= i < rs.len() implies errs_allow(#[trigger] rs[i], l.errs) by {
        assert(expr_sound(db, env, es[i], expr_info(db.schema, cls, es[i])->Some_0));
        lemma_errs_le_allow(rs[i], expr_info(db.schema, cls, es[i])->Some_0.errs, l.errs);
    }
    lemma_collect_allow(rs, l.errs);
    if let Ok(vs) = eval_exprs(db, env, es) {
        assert forall|i: int| 0 <= i < vs.len() implies in_class(#[trigger] vs[i], l.classes[i]) by {
            assert(rs[i] == Ok::<Val, SqlError>(vs[i]));
            assert(expr_sound(db, env, es[i], expr_info(db.schema, cls, es[i])->Some_0));
        }
    }
    if l.fits {
        assert forall|i: int| 0 <= i < es.len() implies #[trigger] fits_expr(db, env, es[i]) by {
            assert(expr_sound(db, env, es[i], expr_info(db.schema, cls, es[i])->Some_0));
        }
        lemma_fits_exprs_all(db, env, es);
    }
}

// ------------------------------------------------------------------------------------- conditions

/// L3 soundness of the condition analysis: errors allowed, domain when it fits.
pub proof fn lemma_pred_sound(db: Database, env: Row, cls: Seq<VClass>, p: Pred)
    requires db_wf(db), row_in(env, cls), pred_info(db.schema, cls, p) is Some,
    ensures pred_sound(db, env, p, pred_info(db.schema, cls, p)->Some_0),
    decreases p, 1nat,
{
    match p {
        Pred::Cmp { op, a, b } => {
            lemma_expr_sound(db, env, cls, a);
            lemma_expr_sound(db, env, cls, b);
            let x = expr_info(db.schema, cls, a)->Some_0;
            let y = expr_info(db.schema, cls, b)->Some_0;
            lemma_errs_join(x.errs, y.errs);
            if let (Ok(va), Ok(vb)) = (eval_expr(db, env, a), eval_expr(db, env, b)) {
                lemma_comparable(op, va, x.cls, vb, y.cls);
            }
        },
        Pred::And(a, b) | Pred::Or(a, b) => {
            lemma_pred_sound(db, env, cls, *a);
            lemma_pred_sound(db, env, cls, *b);
            let x = pred_info(db.schema, cls, *a)->Some_0;
            let y = pred_info(db.schema, cls, *b)->Some_0;
            lemma_errs_join(x.errs, y.errs);
        },
        Pred::Not(a) => lemma_pred_sound(db, env, cls, *a),
        Pred::IsNull(e) => lemma_expr_sound(db, env, cls, e),
        Pred::OfBool(e) => lemma_expr_sound(db, env, cls, e),
        Pred::Exists(q) => lemma_query_sound(db, env, cls, *q),
        Pred::AnyCmp { op, e, q } => {
            lemma_expr_sound(db, env, cls, e);
            lemma_query_sound(db, env, cls, *q);
            let x = expr_info(db.schema, cls, e)->Some_0;
            let qi = query_info(db.schema, cls, *q)->Some_0;
            lemma_errs_join(x.errs, qi.errs);
            if let (Ok(v), Ok(rows)) = (eval_expr(db, env, e), eval_query(db, env, *q)) {
                assert(qi.cols =~= seq![qi.cols[0]]);
                lemma_any_cmp_ok(op, v, x.cls, rows, qi.cols[0]);
            }
        },
    }
}

// ------------------------------------------------------------------------------------- aggregate arguments

/// L3 soundness of one aggregate's argument analysis.
pub proof fn lemma_agg_arg_sound(db: Database, env: Row, cls: Seq<VClass>, a: Agg)
    requires db_wf(db), row_in(env, cls), agg_arg_info(db.schema, cls, a) is Some,
    ensures agg_arg_sound(db, env, a, agg_arg_info(db.schema, cls, a)->Some_0),
    decreases a, 0nat,
{
    match a {
        Agg::CountStar => {},
        Agg::Count(e) => lemma_expr_sound(db, env, cls, e),
        Agg::Sum { kind, arg } => lemma_expr_sound(db, env, cls, arg),
        Agg::Min(e) => lemma_expr_sound(db, env, cls, e),
        Agg::Max(e) => lemma_expr_sound(db, env, cls, e),
        Agg::Avg { kind, arg } => lemma_expr_sound(db, env, cls, arg),
        Agg::DistinctAgg(inner) => lemma_agg_arg_sound(db, env, cls, *inner),
    }
}

/// L3 soundness of the argument analysis of a list of aggregates.
pub proof fn lemma_aggs_arg_sound(db: Database, env: Row, cls: Seq<VClass>, aggs: Seq<Agg>)
    requires db_wf(db), row_in(env, cls), aggs_arg_info(db.schema, cls, aggs) is Some,
    ensures aggs_arg_sound(db, env, aggs, aggs_arg_info(db.schema, cls, aggs)->Some_0),
    decreases aggs, 0nat,
{
    let l = aggs_arg_info(db.schema, cls, aggs)->Some_0;
    lemma_aggs_arg_info_index(db.schema, cls, aggs);
    let rs = agg_arg_results(db, env, aggs);
    lemma_agg_arg_results_index(db, env, aggs);
    lemma_agg_args(db, env, aggs);
    lemma_agg_arg_fs_index(db, env, aggs);
    assert forall|j: int| 0 <= j < aggs.len() implies
        #[trigger] agg_arg_sound(db, env, aggs[j], agg_arg_info(db.schema, cls, aggs[j])->Some_0) by {
        lemma_agg_arg_sound(db, env, cls, aggs[j]);
    }
    assert forall|j: int| 0 <= j < rs.len() implies errs_allow(#[trigger] rs[j], l.errs) by {
        assert(agg_arg_sound(db, env, aggs[j], agg_arg_info(db.schema, cls, aggs[j])->Some_0));
        lemma_errs_le_allow(rs[j], agg_arg_info(db.schema, cls, aggs[j])->Some_0.errs, l.errs);
    }
    lemma_collect_allow(rs, l.errs);
    if let Ok(vs) = agg_args(db, env, aggs) {
        assert forall|j: int| 0 <= j < vs.len() implies in_class(#[trigger] vs[j], l.classes[j]) by {
            assert(rs[j] == Ok::<Val, SqlError>(vs[j]));
            assert(agg_arg_sound(db, env, aggs[j], agg_arg_info(db.schema, cls, aggs[j])->Some_0));
        }
    }
    if l.fits {
        let fs = agg_arg_fs(db, env, aggs);
        assert forall|j: int| 0 <= j < fs.len() implies #[trigger] fs[j] by {
            assert(agg_arg_sound(db, env, aggs[j], agg_arg_info(db.schema, cls, aggs[j])->Some_0));
        }
        lemma_fits_each_all(rs, fs);
    }
}

/// The aggregate row of one group over argument rows in classes `cs`.
pub proof fn lemma_aggs_value_sound(aggs: Seq<Agg>, cs: Seq<VClass>, args: Seq<Row>)
    requires aggs_value_info(aggs, cs) is Some, rows_in(args, cs),
    ensures ({
        let l = aggs_value_info(aggs, cs)->Some_0;
        &&& errs_allow(agg_row(aggs, args), l.errs)
        &&& (agg_row(aggs, args) matches Ok(row) ==> row_in(row, l.classes))
        &&& (l.fits ==> fits_agg_row(aggs, args))
    }),
{
    let l = aggs_value_info(aggs, cs)->Some_0;
    lemma_aggs_value_info_index(aggs, cs);
    lemma_agg_row(aggs, args);
    let rs = agg_value_results(aggs, args);
    assert forall|j: int| 0 <= j < aggs.len() implies
        op_sound(#[trigger] agg_value(aggs[j], column(args, j)), agg_value_info(aggs[j], cs[j])->Some_0)
        && (agg_value_info(aggs[j], cs[j])->Some_0.fits ==> fits_agg_value(aggs[j], column(args, j))) by {
        assert forall|i: int| 0 <= i < column(args, j).len() implies in_class(#[trigger] column(args, j)[i], cs[j]) by {
            assert(row_in(args[i], cs));
        }
        lemma_agg_value(aggs[j], column(args, j), cs[j]);
    }
    assert forall|j: int| 0 <= j < rs.len() implies errs_allow(#[trigger] rs[j], l.errs) by {
        assert(rs[j] == agg_value(aggs[j], column(args, j)));
        lemma_errs_le_allow(rs[j], agg_value_info(aggs[j], cs[j])->Some_0.errs, l.errs);
    }
    lemma_collect_allow(rs, l.errs);
    if let Ok(row) = agg_row(aggs, args) {
        assert forall|j: int| 0 <= j < row.len() implies in_class(#[trigger] row[j], l.classes[j]) by {
            assert(rs[j] == Ok::<Val, SqlError>(row[j]));
            assert(rs[j] == agg_value(aggs[j], column(args, j)));
        }
    }
    if l.fits {
        let fs = agg_value_fs(aggs, args);
        assert forall|j: int| 0 <= j < fs.len() implies #[trigger] fs[j] by {
            assert(agg_value(aggs[j], column(args, j)) == rs[j]);
        }
        lemma_fits_each_all(rs, fs);
    }
}

// ------------------------------------------------------------------------------------- queries

/// L3 soundness of the query analysis (`query_sound`): errors allowed, rows in the column classes (at most one when `one_row`), domain when it fits.
pub proof fn lemma_query_sound(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires db_wf(db), row_in(ctx, cls), query_info(db.schema, cls, q) is Some,
    ensures query_sound(db, ctx, q, query_info(db.schema, cls, q)->Some_0),
    decreases q, 2nat,
{
    match q {
        Query::Table(_) => lemma_table_sound(db, ctx, cls, q),
        Query::Filter { .. } => lemma_filter_sound(db, ctx, cls, q),
        Query::Project { .. } => lemma_project_sound(db, ctx, cls, q),
        Query::Product { .. } => lemma_product_sound(db, ctx, cls, q),
        Query::LeftJoin { .. } => lemma_left_join_sound(db, ctx, cls, q),
        Query::Aggregate { .. } => lemma_aggregate_sound(db, ctx, cls, q),
        Query::GroupBy { .. } => lemma_group_by_sound(db, ctx, cls, q),
        Query::Distinct(_) => lemma_distinct_sound(db, ctx, cls, q),
    }
}

proof fn lemma_table_sound(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires q is Table, db_wf(db), row_in(ctx, cls), query_info(db.schema, cls, q) is Some,
    ensures query_sound(db, ctx, q, query_info(db.schema, cls, q)->Some_0),
    decreases q, 1nat,
{
    if let Query::Table(t) = q {
        lemma_table_rows_in(db, t as int);
    }
}

proof fn lemma_filter_sound(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires q is Filter, db_wf(db), row_in(ctx, cls), query_info(db.schema, cls, q) is Some,
    ensures query_sound(db, ctx, q, query_info(db.schema, cls, q)->Some_0),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_pred);
    hide(fits_pred);
    if let Query::Filter { pred, input } = q {
        let qi = query_info(db.schema, cls, q)->Some_0;
        lemma_query_sound(db, ctx, cls, *input);
        let i = query_info(db.schema, cls, *input)->Some_0;
        let p = pred_info(db.schema, cls + i.cols, pred)->Some_0;
        lemma_errs_join(i.errs, p.errs);
        lemma_eval_filter(db, ctx, pred, input);
        lemma_fits_filter(db, ctx, pred, input);
        if let Ok(rows) = eval_query(db, ctx, *input) {
            assert forall|k: int| 0 <= k < rows.len() implies #[trigger] pred_sound(db, ctx + rows[k], pred, p) by {
                assert(row_in(rows[k], i.cols));
                lemma_row_in_concat(ctx, cls, rows[k], i.cols);
                lemma_pred_sound(db, ctx + rows[k], cls + i.cols, pred);
            }
            let rs = filter_results(db, ctx, rows, pred);
            assert forall|k: int| 0 <= k < rs.len() implies errs_allow(#[trigger] rs[k], qi.errs) by {
                assert(pred_sound(db, ctx + rows[k], pred, p));
                lemma_errs_le_allow(rs[k], p.errs, qi.errs);
            }
            lemma_collect_allow(rs, qi.errs);
            if let Ok(truths) = collect(rs) {
                let kept = keep_true(rows, truths);
                lemma_keep_true_sub(rows, truths);
                assert forall|k: int| 0 <= k < kept.len() implies row_in(#[trigger] kept[k], qi.cols) by {
                    let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[k];
                    assert(row_in(rows[m], i.cols));
                }
            }
            if qi.fits {
                assert forall|k: int| 0 <= k < rows.len() && ok_before(rs, k)
                    implies #[trigger] fits_pred(db, ctx + rows[k], pred) by {
                    assert(pred_sound(db, ctx + rows[k], pred, p));
                }
            }
        }
    }
}

proof fn lemma_project_sound(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires q is Project, db_wf(db), row_in(ctx, cls), query_info(db.schema, cls, q) is Some,
    ensures query_sound(db, ctx, q, query_info(db.schema, cls, q)->Some_0),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_exprs);
    hide(fits_exprs);
    if let Query::Project { exprs, input } = q {
        let qi = query_info(db.schema, cls, q)->Some_0;
        lemma_query_sound(db, ctx, cls, *input);
        let i = query_info(db.schema, cls, *input)->Some_0;
        let l = exprs_info(db.schema, cls + i.cols, exprs)->Some_0;
        lemma_errs_join(i.errs, l.errs);
        lemma_eval_project(db, ctx, exprs, input);
        lemma_fits_project_unfold(db, ctx, exprs, input);
        if let Ok(rows) = eval_query(db, ctx, *input) {
            assert forall|k: int| 0 <= k < rows.len() implies #[trigger] exprs_sound(db, ctx + rows[k], exprs, l) by {
                assert(row_in(rows[k], i.cols));
                lemma_row_in_concat(ctx, cls, rows[k], i.cols);
                lemma_exprs_sound(db, ctx + rows[k], cls + i.cols, exprs);
            }
            let rs = project_results(db, ctx, rows, exprs);
            assert forall|k: int| 0 <= k < rs.len() implies errs_allow(#[trigger] rs[k], qi.errs) by {
                assert(exprs_sound(db, ctx + rows[k], exprs, l));
                lemma_errs_le_allow(rs[k], l.errs, qi.errs);
            }
            lemma_collect_allow(rs, qi.errs);
            if let Ok(out) = collect(rs) {
                assert forall|k: int| 0 <= k < out.len() implies row_in(#[trigger] out[k], qi.cols) by {
                    assert(rs[k] == Ok::<Row, SqlError>(out[k]));
                    assert(exprs_sound(db, ctx + rows[k], exprs, l));
                }
            }
            if qi.fits {
                lemma_project_fs_index(db, ctx, rows, exprs);
                let fs = project_fs(db, ctx, rows, exprs);
                assert forall|k: int| 0 <= k < fs.len() implies #[trigger] fs[k] by {
                    assert(exprs_sound(db, ctx + rows[k], exprs, l));
                }
                lemma_fits_each_all(rs, fs);
            }
        }
    }
}

proof fn lemma_product_sound(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires q is Product, db_wf(db), row_in(ctx, cls), query_info(db.schema, cls, q) is Some,
    ensures query_sound(db, ctx, q, query_info(db.schema, cls, q)->Some_0),
    decreases q, 1nat,
{
    if let Query::Product { left, right } = q {
        lemma_query_sound(db, ctx, cls, *left);
        lemma_query_sound(db, ctx, cls, *right);
        let l = query_info(db.schema, cls, *left)->Some_0;
        let r = query_info(db.schema, cls, *right)->Some_0;
        lemma_errs_join(l.errs, r.errs);
        if let (Ok(lr), Ok(rr)) = (eval_query(db, ctx, *left), eval_query(db, ctx, *right)) {
            let p = product_rows(lr, rr);
            lemma_product_rows_elems(lr, rr);
            assert forall|k: int| 0 <= k < p.len() implies row_in(#[trigger] p[k], l.cols + r.cols) by {
                assert(is_concat(p[k], lr, rr));
                let (i, j) = choose|i: int, j: int| 0 <= i < lr.len() && 0 <= j < rr.len() && p[k] == #[trigger] lr[i] + #[trigger] rr[j];
                assert(row_in(lr[i], l.cols) && row_in(rr[j], r.cols));
                lemma_row_in_concat(lr[i], l.cols, rr[j], r.cols);
            }
            if l.one_row && r.one_row {
                assert(lr.len() * rr.len() <= 1) by (nonlinear_arith) requires lr.len() <= 1, rr.len() <= 1;
            }
        }
    }
}

proof fn lemma_left_join_sound(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires q is LeftJoin, db_wf(db), row_in(ctx, cls), query_info(db.schema, cls, q) is Some,
    ensures query_sound(db, ctx, q, query_info(db.schema, cls, q)->Some_0),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_pred);
    hide(fits_pred);
    if let Query::LeftJoin { left, right, on } = q {
        let qi = query_info(db.schema, cls, q)->Some_0;
        lemma_query_sound(db, ctx, cls, *left);
        lemma_query_sound(db, ctx, cls, *right);
        let l = query_info(db.schema, cls, *left)->Some_0;
        let r = query_info(db.schema, cls, *right)->Some_0;
        let p = pred_info(db.schema, cls + l.cols + r.cols, on)->Some_0;
        lemma_errs_join3(l.errs, r.errs, p.errs);
        lemma_query_info_arity(db.schema, cls, *right);
        lemma_eval_left_join(db, ctx, left, right, on);
        lemma_fits_left_join(db, ctx, left, right, on);
        if let (Ok(lr), Ok(rr)) = (eval_query(db, ctx, *left), eval_query(db, ctx, *right)) {
            assert forall|i: int, j: int| 0 <= i < lr.len() && 0 <= j < rr.len() implies
                #[trigger] pred_sound(db, ctx + lr[i] + rr[j], on, p) by {
                assert(row_in(lr[i], l.cols) && row_in(rr[j], r.cols));
                lemma_row_in_concat(ctx, cls, lr[i], l.cols);
                lemma_row_in_concat(ctx + lr[i], cls + l.cols, rr[j], r.cols);
                lemma_pred_sound(db, ctx + lr[i] + rr[j], cls + l.cols + r.cols, on);
            }
            let outer = left_join_results(db, ctx, lr, rr, on);
            assert forall|i: int| 0 <= i < outer.len() implies errs_allow(#[trigger] outer[i], qi.errs) by {
                let inner = Seq::new(rr.len(), |j: int| eval_pred(db, ctx + lr[i] + rr[j], on));
                assert forall|j: int| 0 <= j < inner.len() implies errs_allow(#[trigger] inner[j], qi.errs) by {
                    assert(pred_sound(db, ctx + lr[i] + rr[j], on, p));
                    lemma_errs_le_allow(inner[j], p.errs, qi.errs);
                }
                lemma_collect_allow(inner, qi.errs);
                assert(outer[i] == collect(inner));
            }
            lemma_collect_allow(outer, qi.errs);
            if let Ok(truths) = collect(outer) {
                let n = query_arity(db.schema, *right);
                let out = left_join_rows(lr, rr, truths, n);
                lemma_left_join_rows_elems(lr, rr, truths, n);
                lemma_null_row_in(r.cols);
                assert forall|k: int| 0 <= k < out.len() implies row_in(#[trigger] out[k], qi.cols) by {
                    if is_concat(out[k], lr, rr) {
                        let (i, j) = choose|i: int, j: int| 0 <= i < lr.len() && 0 <= j < rr.len() && out[k] == #[trigger] lr[i] + #[trigger] rr[j];
                        assert(row_in(lr[i], l.cols) && row_in(rr[j], r.cols));
                        lemma_row_in_nullable(rr[j], r.cols);
                        lemma_row_in_concat(lr[i], l.cols, rr[j], nullable_classes(r.cols));
                    } else {
                        let i = choose|i: int| 0 <= i < lr.len() && out[k] == #[trigger] lr[i] + null_row(n);
                        assert(row_in(lr[i], l.cols));
                        lemma_row_in_concat(lr[i], l.cols, null_row(n), nullable_classes(r.cols));
                    }
                }
            }
            if qi.fits {
                assert forall|i: int| 0 <= i < lr.len() && ok_before(outer, i)
                    implies #[trigger] join_row_fits(db, ctx + lr[i], rr, on) by {
                    assert forall|j: int| 0 <= j < rr.len() && ok_before(join_results(db, ctx + lr[i], rr, on), j)
                        implies #[trigger] fits_pred(db, ctx + lr[i] + rr[j], on) by {
                        assert(pred_sound(db, ctx + lr[i] + rr[j], on, p));
                    }
                }
            }
        }
    }
}

proof fn lemma_aggregate_sound(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires q is Aggregate, db_wf(db), row_in(ctx, cls), query_info(db.schema, cls, q) is Some,
    ensures query_sound(db, ctx, q, query_info(db.schema, cls, q)->Some_0),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(agg_args);
    hide(fits_agg_args);
    if let Query::Aggregate { aggs, input } = q {
        let qi = query_info(db.schema, cls, q)->Some_0;
        lemma_query_sound(db, ctx, cls, *input);
        let i = query_info(db.schema, cls, *input)->Some_0;
        let a = aggs_arg_info(db.schema, cls + i.cols, aggs)->Some_0;
        let v = aggs_value_info(aggs, a.classes)->Some_0;
        lemma_errs_join3(i.errs, a.errs, v.errs);
        lemma_eval_aggregate(db, ctx, aggs, input);
        lemma_fits_aggregate_unfold(db, ctx, aggs, input);
        if let Ok(rows) = eval_query(db, ctx, *input) {
            assert forall|k: int| 0 <= k < rows.len() implies #[trigger] aggs_arg_sound(db, ctx + rows[k], aggs, a) by {
                assert(row_in(rows[k], i.cols));
                lemma_row_in_concat(ctx, cls, rows[k], i.cols);
                lemma_aggs_arg_sound(db, ctx + rows[k], cls + i.cols, aggs);
            }
            let rs = agg_args_results(db, ctx, rows, aggs);
            assert forall|k: int| 0 <= k < rs.len() implies errs_allow(#[trigger] rs[k], qi.errs) by {
                assert(aggs_arg_sound(db, ctx + rows[k], aggs, a));
                lemma_errs_le_allow(rs[k], a.errs, qi.errs);
            }
            lemma_collect_allow(rs, qi.errs);
            if let Ok(args) = collect(rs) {
                assert forall|k: int| 0 <= k < args.len() implies row_in(#[trigger] args[k], a.classes) by {
                    assert(rs[k] == Ok::<Row, SqlError>(args[k]));
                    assert(aggs_arg_sound(db, ctx + rows[k], aggs, a));
                }
                lemma_aggs_value_sound(aggs, a.classes, args);
                lemma_errs_le_allow(agg_row(aggs, args), v.errs, qi.errs);
            }
            if qi.fits {
                lemma_agg_args_fs_index(db, ctx, rows, aggs);
                let fs = agg_args_fs(db, ctx, rows, aggs);
                assert forall|k: int| 0 <= k < fs.len() implies #[trigger] fs[k] by {
                    assert(aggs_arg_sound(db, ctx + rows[k], aggs, a));
                }
                lemma_fits_each_all(rs, fs);
            }
        }
    }
}

proof fn lemma_group_by_sound(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires q is GroupBy, db_wf(db), row_in(ctx, cls), query_info(db.schema, cls, q) is Some,
    ensures query_sound(db, ctx, q, query_info(db.schema, cls, q)->Some_0),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_exprs);
    hide(fits_exprs);
    hide(agg_args);
    hide(fits_agg_args);
    hide(group_rows);
    if let Query::GroupBy { keys, aggs, input } = q {
        let qi = query_info(db.schema, cls, q)->Some_0;
        lemma_query_sound(db, ctx, cls, *input);
        let i = query_info(db.schema, cls, *input)->Some_0;
        let k = exprs_info(db.schema, cls + i.cols, keys)->Some_0;
        let a = aggs_arg_info(db.schema, cls + i.cols, aggs)->Some_0;
        let v = aggs_value_info(aggs, a.classes)->Some_0;
        lemma_errs_join3(i.errs, k.errs, a.errs);
        let e1 = errs_join3(i.errs, k.errs, a.errs)->Some_0;
        lemma_errs_join(e1, v.errs);
        lemma_errs_le_trans(k.errs, e1, qi.errs);
        lemma_errs_le_trans(a.errs, e1, qi.errs);
        lemma_eval_group_by(db, ctx, keys, aggs, input);
        lemma_fits_group_by(db, ctx, keys, aggs, input);
        if let Ok(rows) = eval_query(db, ctx, *input) {
            assert forall|m: int| 0 <= m < rows.len() implies
                #[trigger] exprs_sound(db, ctx + rows[m], keys, k) && aggs_arg_sound(db, ctx + rows[m], aggs, a) by {
                assert(row_in(rows[m], i.cols));
                lemma_row_in_concat(ctx, cls, rows[m], i.cols);
                lemma_exprs_sound(db, ctx + rows[m], cls + i.cols, keys);
                lemma_aggs_arg_sound(db, ctx + rows[m], cls + i.cols, aggs);
            }
            let rs = group_input_results(db, ctx, rows, keys, aggs);
            assert forall|m: int| 0 <= m < rs.len() implies errs_allow(#[trigger] rs[m], qi.errs) by {
                assert(exprs_sound(db, ctx + rows[m], keys, k));
                lemma_errs_le_allow(eval_exprs(db, ctx + rows[m], keys), k.errs, qi.errs);
                lemma_errs_le_allow(agg_args(db, ctx + rows[m], aggs), a.errs, qi.errs);
            }
            lemma_collect_allow(rs, qi.errs);
            if let Ok(prep) = collect(rs) {
                let ks = prep.map_values(|p: (Row, Row)| p.0);
                let args = prep.map_values(|p: (Row, Row)| p.1);
                assert forall|m: int| #![trigger prep[m]] 0 <= m < prep.len() implies
                    row_in(prep[m].0, k.classes) && row_in(prep[m].1, a.classes) by {
                    assert(rs[m] == Ok::<(Row, Row), SqlError>(prep[m]));
                    assert(exprs_sound(db, ctx + rows[m], keys, k));
                }
                let ds = distinct_rows(ks);
                lemma_distinct_rows_sub(ks);
                let gs = group_results(aggs, ks, args);
                assert forall|g: int| 0 <= g < gs.len() implies {
                    &&& errs_allow(#[trigger] gs[g], qi.errs)
                    &&& (gs[g] matches Ok(row) ==> row_in(row, qi.cols))
                    &&& (qi.fits ==> fits_agg_row(aggs, group_members(ks, args, ds[g])))
                } by {
                    let members = group_members(ks, args, ds[g]);
                    lemma_group_members_sub(ks, args, ds[g]);
                    assert forall|x: int| 0 <= x < members.len() implies row_in(#[trigger] members[x], a.classes) by {
                        let y = choose|y: int| 0 <= y < args.len() && args[y] == members[x];
                        assert(row_in(prep[y].1, a.classes));
                    }
                    lemma_aggs_value_sound(aggs, a.classes, members);
                    lemma_errs_le_allow(agg_row(aggs, members), v.errs, qi.errs);
                    let y = choose|y: int| 0 <= y < ks.len() && ks[y] == ds[g];
                    assert(row_in(prep[y].0, k.classes));
                    if let Ok(av) = agg_row(aggs, members) {
                        lemma_row_in_concat(ds[g], k.classes, av, v.classes);
                    }
                }
                lemma_collect_allow(gs, qi.errs);
                assert(group_rows(aggs, ks, args) == collect(gs)) by {
                    reveal(group_rows);
                    crate::bridge::collect::lemma_collect_pointwise::<Row>();
                }
                if let Ok(out) = collect(gs) {
                    assert forall|g: int| 0 <= g < out.len() implies row_in(#[trigger] out[g], qi.cols) by {
                        assert(gs[g] == Ok::<Row, SqlError>(out[g]));
                    }
                }
                if qi.fits {
                    let fs = groups_fs(aggs, ks, args);
                    assert forall|g: int| 0 <= g < fs.len() implies #[trigger] fs[g] by {
                        assert(fs[g] == fits_agg_row(aggs, group_members(ks, args, ds[g])));
                        assert(errs_allow(gs[g], qi.errs));
                    }
                    lemma_fits_each_all(gs, fs);
                }
            }
            if qi.fits {
                let fs = group_input_fs(db, ctx, rows, keys, aggs);
                assert forall|m: int| 0 <= m < fs.len() implies #[trigger] fs[m] by {
                    assert(exprs_sound(db, ctx + rows[m], keys, k));
                }
                lemma_fits_each_all(rs, fs);
            }
        }
    }
}

/// `distinct_rows` never has more rows than its input.
pub proof fn lemma_distinct_rows_len(rows: Seq<Row>)
    ensures distinct_rows(rows).len() <= rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_distinct_rows_len(rows.drop_last());
    }
}

proof fn lemma_distinct_sound(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires q is Distinct, db_wf(db), row_in(ctx, cls), query_info(db.schema, cls, q) is Some,
    ensures query_sound(db, ctx, q, query_info(db.schema, cls, q)->Some_0),
    decreases q, 1nat,
{
    if let Query::Distinct(input) = q {
        lemma_query_sound(db, ctx, cls, *input);
        let i = query_info(db.schema, cls, *input)->Some_0;
        if let Ok(rows) = eval_query(db, ctx, *input) {
            let d = distinct_rows(rows);
            lemma_distinct_rows_sub(rows);
            lemma_distinct_rows_len(rows);
            assert forall|g: int| 0 <= g < d.len() implies row_in(#[trigger] d[g], i.cols) by {
                let m = choose|m: int| 0 <= m < rows.len() && rows[m] == d[g];
                assert(row_in(rows[m], i.cols));
            }
        }
    }
}

// ------------------------------------------------------------------------------------- the three classes

/// L3 totality, expressions: no SQL error, inside the executable domain.
pub proof fn lemma_expr_total(db: Database, env: Row, cls: Seq<VClass>, e: Expr)
    requires db_wf(db), row_in(env, cls), expr_total(db.schema, cls, e),
    ensures eval_expr(db, env, e) is Ok, fits_expr(db, env, e),
{
    lemma_expr_sound(db, env, cls, e);
}

/// L3 totality, conditions.
pub proof fn lemma_pred_total(db: Database, env: Row, cls: Seq<VClass>, p: Pred)
    requires db_wf(db), row_in(env, cls), pred_total(db.schema, cls, p),
    ensures eval_pred(db, env, p) is Ok, fits_pred(db, env, p),
{
    lemma_pred_sound(db, env, cls, p);
}

/// L3 totality, queries.
pub proof fn lemma_query_total(db: Database, ctx: Row, cls: Seq<VClass>, q: Query)
    requires db_wf(db), row_in(ctx, cls), query_total(db.schema, cls, q),
    ensures eval_query(db, ctx, q) is Ok, fits_query(db, ctx, q),
{
    lemma_query_sound(db, ctx, cls, q);
}

/// L3 uniformity, expressions: a value or the one error `code`.
pub proof fn lemma_expr_uniform(db: Database, env: Row, cls: Seq<VClass>, e: Expr, code: SqlError)
    requires db_wf(db), row_in(env, cls), expr_uniform(db.schema, cls, e, code),
    ensures eval_expr(db, env, e) is Ok || eval_expr(db, env, e) == Err::<Val, SqlError>(code),
{
    lemma_expr_sound(db, env, cls, e);
}

/// L3 uniformity, conditions.
pub proof fn lemma_pred_uniform(db: Database, env: Row, cls: Seq<VClass>, p: Pred, code: SqlError)
    requires db_wf(db), row_in(env, cls), pred_uniform(db.schema, cls, p, code),
    ensures eval_pred(db, env, p) is Ok || eval_pred(db, env, p) == Err::<Truth, SqlError>(code),
{
    lemma_pred_sound(db, env, cls, p);
}

/// L3 uniformity, queries.
pub proof fn lemma_query_uniform(db: Database, ctx: Row, cls: Seq<VClass>, q: Query, code: SqlError)
    requires db_wf(db), row_in(ctx, cls), query_uniform(db.schema, cls, q, code),
    ensures eval_query(db, ctx, q) is Ok || eval_query(db, ctx, q) == Err::<Relation, SqlError>(code),
{
    lemma_query_sound(db, ctx, cls, q);
}

/// Two values of one exact class have one exact type: SQL "not distinct" is structural equality.
pub proof fn lemma_class_exact(v: Val, w: Val, c: VClass)
    requires in_class(v, c), in_class(w, c), class_exact(c),
    ensures same_exact_type(v, w), val_not_distinct(v, w) == (v == w),
{
    lemma_val_not_distinct_structural(v, w);
}

/// `classes_exact` by element.
pub proof fn lemma_classes_exact_index(cs: Seq<VClass>, i: int)
    requires classes_exact(cs), 0 <= i < cs.len(),
    ensures class_exact(cs[i]),
    decreases cs.len(),
{
    if i < cs.len() - 1 {
        lemma_classes_exact_index(cs.drop_last(), i);
        assert(cs.drop_last()[i] == cs[i]);
    }
}

/// Two rows of exact classes: SQL "not distinct" is structural equality.
pub proof fn lemma_rows_exact(r: Row, s: Row, cs: Seq<VClass>)
    requires row_in(r, cs), row_in(s, cs), classes_exact(cs),
    ensures row_not_distinct(r, s) == (r == s),
{
    assert forall|i: int| 0 <= i < r.len() implies same_exact_type(#[trigger] r[i], s[i]) by {
        lemma_classes_exact_index(cs, i);
        lemma_class_exact(r[i], s[i], cs[i]);
    }
    lemma_row_exact(r, s);
}

/// L3 scale-exactness, expressions: any two values (in any two environments of the classes) have one exact
/// type, so SQL "not distinct" is structural equality on them.
pub proof fn lemma_expr_exact(db: Database, env1: Row, env2: Row, cls: Seq<VClass>, e: Expr)
    requires db_wf(db), row_in(env1, cls), row_in(env2, cls), expr_exact(db.schema, cls, e),
        eval_expr(db, env1, e) is Ok, eval_expr(db, env2, e) is Ok,
    ensures ({
        let (v, w) = (eval_expr(db, env1, e)->Ok_0, eval_expr(db, env2, e)->Ok_0);
        same_exact_type(v, w) && val_not_distinct(v, w) == (v == w)
    }),
{
    lemma_expr_sound(db, env1, cls, e);
    lemma_expr_sound(db, env2, cls, e);
    let c = expr_info(db.schema, cls, e)->Some_0.cls;
    lemma_class_exact(eval_expr(db, env1, e)->Ok_0, eval_expr(db, env2, e)->Ok_0, c);
}

/// L3 scale-exactness, key lists: two key tuples are not distinct exactly when they are equal.
pub proof fn lemma_exprs_exact(db: Database, env1: Row, env2: Row, cls: Seq<VClass>, es: Seq<Expr>)
    requires db_wf(db), row_in(env1, cls), row_in(env2, cls), exprs_exact(db.schema, cls, es),
        eval_exprs(db, env1, es) is Ok, eval_exprs(db, env2, es) is Ok,
    ensures ({
        let (k1, k2) = (eval_exprs(db, env1, es)->Ok_0, eval_exprs(db, env2, es)->Ok_0);
        row_not_distinct(k1, k2) == (k1 == k2)
    }),
{
    lemma_exprs_sound(db, env1, cls, es);
    lemma_exprs_sound(db, env2, cls, es);
    let l = exprs_info(db.schema, cls, es)->Some_0;
    lemma_rows_exact(eval_exprs(db, env1, es)->Ok_0, eval_exprs(db, env2, es)->Ok_0, l.classes);
}

/// L3 scale-exactness, queries: two output rows are not distinct exactly when they are equal.
pub proof fn lemma_query_exact(db: Database, ctx: Row, cls: Seq<VClass>, q: Query, i: int, j: int)
    requires db_wf(db), row_in(ctx, cls), query_exact(db.schema, cls, q), eval_query(db, ctx, q) is Ok,
        0 <= i < eval_query(db, ctx, q)->Ok_0.len(), 0 <= j < eval_query(db, ctx, q)->Ok_0.len(),
    ensures ({
        let rows = eval_query(db, ctx, q)->Ok_0;
        row_not_distinct(rows[i], rows[j]) == (rows[i] == rows[j])
    }),
{
    lemma_query_sound(db, ctx, cls, q);
    let rows = eval_query(db, ctx, q)->Ok_0;
    let qi = query_info(db.schema, cls, q)->Some_0;
    lemma_rows_exact(rows[i], rows[j], qi.cols);
}

} // verus!
