//! Typed statement parameters: static typing sees a literal only through its static type (`type_lit`).
//!
//! `*_teq(a, b)` says that `a` and `b` are the same AST except for literals, and corresponding literals have the
//! same static type (`lit_teq`). The `lemma_*_teq` theorems show that such ASTs type alike, in every environment.
//! An emitted template `query_spec_at(ps)` differs between two bindings `ps`, `p0` only at the parameter
//! positions, so once `wf_ordered` is evaluated at one binding, `lemma_ordered_teq` gives it at every binding
//! whose literals have the declared types (the emitted `lemma_query_wf_at`). The list relations follow the typing's
//! own recursion (`drop_last` / `last`); `lemma_exprs_teq_intro` and `lemma_aggs_teq_intro` build them from
//! elementwise facts.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::ast::*;
use crate::spec::typing::*;

verus! {

/// Literals of the same static type (possibly different values).
pub open spec fn lit_teq(a: Literal, b: Literal) -> bool {
    type_lit(a) == type_lit(b)
}

pub open spec fn expr_teq(a: Expr, b: Expr) -> bool
    decreases a, 0nat,
{
    match a {
        Expr::Col(i) => b == Expr::Col(i),
        Expr::Lit(x) => b matches Expr::Lit(y) && lit_teq(x, y),
        Expr::Neg { kind, arg } => b matches Expr::Neg { kind: k, arg: y } && k == kind && expr_teq(*arg, *y),
        Expr::Arith { op, kind, a: x1, b: x2 } =>
            b matches Expr::Arith { op: o, kind: k, a: y1, b: y2 } && o == op && k == kind && expr_teq(*x1, *y1)
                && expr_teq(*x2, *y2),
        Expr::Cast { cast, arg } => b matches Expr::Cast { cast: c, arg: y } && c == cast && expr_teq(*arg, *y),
        Expr::AddInterval { arg, months, days, micros } =>
            b matches Expr::AddInterval { arg: y, months: m, days: d, micros: u } && m == months && d == days
                && u == micros && expr_teq(*arg, *y),
        Expr::Call { f, args } => b matches Expr::Call { f: g, args: ys } && g == f && exprs_teq(args, ys),
        Expr::If { cond, then_e, else_e } =>
            b matches Expr::If { cond: c, then_e: t, else_e: e } && pred_teq(*cond, *c) && expr_teq(*then_e, *t)
                && expr_teq(*else_e, *e),
        Expr::Subquery(q) => b matches Expr::Subquery(r) && query_teq(*q, *r),
    }
}

pub open spec fn exprs_teq(a: Seq<Expr>, b: Seq<Expr>) -> bool
    decreases a, 1nat,
{
    if a.len() == 0 {
        b.len() == 0
    } else {
        b.len() == a.len() && exprs_teq(a.drop_last(), b.drop_last()) && expr_teq(a.last(), b.last())
    }
}

pub open spec fn pred_teq(a: Pred, b: Pred) -> bool
    decreases a,
{
    match a {
        Pred::Cmp { op, a: x1, b: x2 } =>
            b matches Pred::Cmp { op: o, a: y1, b: y2 } && o == op && expr_teq(x1, y1) && expr_teq(x2, y2),
        Pred::And(x1, x2) => b matches Pred::And(y1, y2) && pred_teq(*x1, *y1) && pred_teq(*x2, *y2),
        Pred::Or(x1, x2) => b matches Pred::Or(y1, y2) && pred_teq(*x1, *y1) && pred_teq(*x2, *y2),
        Pred::Not(x) => b matches Pred::Not(y) && pred_teq(*x, *y),
        Pred::IsNull(x) => b matches Pred::IsNull(y) && expr_teq(x, y),
        Pred::OfBool(x) => b matches Pred::OfBool(y) && expr_teq(x, y),
        Pred::Exists(q) => b matches Pred::Exists(r) && query_teq(*q, *r),
        Pred::AnyCmp { op, e, q } =>
            b matches Pred::AnyCmp { op: o, e: y, q: r } && o == op && expr_teq(e, y) && query_teq(*q, *r),
    }
}

pub open spec fn agg_teq(a: Agg, b: Agg) -> bool
    decreases a, 0nat,
{
    match a {
        Agg::CountStar => b == Agg::CountStar,
        Agg::Count(x) => b matches Agg::Count(y) && expr_teq(x, y),
        Agg::Sum { kind, arg } => b matches Agg::Sum { kind: k, arg: y } && k == kind && expr_teq(arg, y),
        Agg::Min(x) => b matches Agg::Min(y) && expr_teq(x, y),
        Agg::Max(x) => b matches Agg::Max(y) && expr_teq(x, y),
        Agg::Avg { kind, arg } => b matches Agg::Avg { kind: k, arg: y } && k == kind && expr_teq(arg, y),
        Agg::DistinctAgg(x) => b matches Agg::DistinctAgg(y) && agg_teq(*x, *y),
    }
}

pub open spec fn aggs_teq(a: Seq<Agg>, b: Seq<Agg>) -> bool
    decreases a, 1nat,
{
    if a.len() == 0 {
        b.len() == 0
    } else {
        b.len() == a.len() && aggs_teq(a.drop_last(), b.drop_last()) && agg_teq(a.last(), b.last())
    }
}

pub open spec fn query_teq(a: Query, b: Query) -> bool
    decreases a,
{
    match a {
        Query::Table(t) => b == Query::Table(t),
        Query::Filter { pred, input } =>
            b matches Query::Filter { pred: p, input: i } && pred_teq(pred, p) && query_teq(*input, *i),
        Query::Project { exprs, input } =>
            b matches Query::Project { exprs: es, input: i } && exprs_teq(exprs, es) && query_teq(*input, *i),
        Query::Product { left, right } =>
            b matches Query::Product { left: l, right: r } && query_teq(*left, *l) && query_teq(*right, *r),
        Query::LeftJoin { left, right, on } =>
            b matches Query::LeftJoin { left: l, right: r, on: p } && query_teq(*left, *l) && query_teq(*right, *r)
                && pred_teq(on, p),
        Query::Aggregate { aggs, input } =>
            b matches Query::Aggregate { aggs: gs, input: i } && aggs_teq(aggs, gs) && query_teq(*input, *i),
        Query::GroupBy { keys, aggs, input } =>
            b matches Query::GroupBy { keys: ks, aggs: gs, input: i } && exprs_teq(keys, ks) && aggs_teq(aggs, gs)
                && query_teq(*input, *i),
        Query::Distinct(input) => b matches Query::Distinct(i) && query_teq(*input, *i),
    }
}

/// Statements: typing-equivalent bodies, identical ORDER BY keys, LIMIT and OFFSET.
pub open spec fn ordered_teq(a: OrderedQuery, b: OrderedQuery) -> bool {
    &&& query_teq(a.body, b.body)
    &&& a.keys == b.keys
    &&& a.limit == b.limit
    &&& a.offset == b.offset
}

// ------------------------------------------------------------------ typing-equivalent ASTs type alike
// One lemma per relation, following the typing's mutual recursion and measures.

pub proof fn lemma_expr_teq(schema: Schema, env: Seq<ColTy>, a: Expr, b: Expr)
    requires expr_teq(a, b),
    ensures type_expr(schema, env, a) == type_expr(schema, env, b),
    decreases a, 0nat,
{
    match a {
        Expr::Col(i) => {},
        Expr::Lit(x) => {},
        Expr::Neg { kind, arg } => {
            if let Expr::Neg { arg: y, .. } = b {
                lemma_expr_teq(schema, env, *arg, *y);
            }
        },
        Expr::Arith { op, kind, a: x1, b: x2 } => {
            if let Expr::Arith { a: y1, b: y2, .. } = b {
                lemma_expr_teq(schema, env, *x1, *y1);
                lemma_expr_teq(schema, env, *x2, *y2);
            }
        },
        Expr::Cast { cast, arg } => {
            if let Expr::Cast { arg: y, .. } = b {
                lemma_expr_teq(schema, env, *arg, *y);
            }
        },
        Expr::AddInterval { arg, months, days, micros } => {
            if let Expr::AddInterval { arg: y, .. } = b {
                lemma_expr_teq(schema, env, *arg, *y);
            }
        },
        Expr::Call { f, args } => {
            if let Expr::Call { args: ys, .. } = b {
                lemma_exprs_teq(schema, env, args, ys);
            }
        },
        Expr::If { cond, then_e, else_e } => {
            if let Expr::If { cond: c, then_e: t, else_e: e } = b {
                lemma_pred_teq(schema, env, *cond, *c);
                lemma_expr_teq(schema, env, *then_e, *t);
                lemma_expr_teq(schema, env, *else_e, *e);
            }
        },
        Expr::Subquery(q) => {
            if let Expr::Subquery(r) = b {
                lemma_query_teq(schema, env, *q, *r);
            }
        },
    }
}

pub proof fn lemma_exprs_teq(schema: Schema, env: Seq<ColTy>, a: Seq<Expr>, b: Seq<Expr>)
    requires exprs_teq(a, b),
    ensures type_exprs(schema, env, a) == type_exprs(schema, env, b),
    decreases a, 1nat,
{
    if a.len() > 0 {
        lemma_exprs_teq(schema, env, a.drop_last(), b.drop_last());
        lemma_expr_teq(schema, env, a.last(), b.last());
    }
}

pub proof fn lemma_pred_teq(schema: Schema, env: Seq<ColTy>, a: Pred, b: Pred)
    requires pred_teq(a, b),
    ensures type_pred(schema, env, a) == type_pred(schema, env, b),
    decreases a,
{
    match a {
        Pred::Cmp { op, a: x1, b: x2 } => {
            if let Pred::Cmp { a: y1, b: y2, .. } = b {
                lemma_expr_teq(schema, env, x1, y1);
                lemma_expr_teq(schema, env, x2, y2);
            }
        },
        Pred::And(x1, x2) => {
            if let Pred::And(y1, y2) = b {
                lemma_pred_teq(schema, env, *x1, *y1);
                lemma_pred_teq(schema, env, *x2, *y2);
            }
        },
        Pred::Or(x1, x2) => {
            if let Pred::Or(y1, y2) = b {
                lemma_pred_teq(schema, env, *x1, *y1);
                lemma_pred_teq(schema, env, *x2, *y2);
            }
        },
        Pred::Not(x) => {
            if let Pred::Not(y) = b {
                lemma_pred_teq(schema, env, *x, *y);
            }
        },
        Pred::IsNull(x) => {
            if let Pred::IsNull(y) = b {
                lemma_expr_teq(schema, env, x, y);
            }
        },
        Pred::OfBool(x) => {
            if let Pred::OfBool(y) = b {
                lemma_expr_teq(schema, env, x, y);
            }
        },
        Pred::Exists(q) => {
            if let Pred::Exists(r) = b {
                lemma_query_teq(schema, env, *q, *r);
            }
        },
        Pred::AnyCmp { op, e, q } => {
            if let Pred::AnyCmp { e: y, q: r, .. } = b {
                lemma_expr_teq(schema, env, e, y);
                lemma_query_teq(schema, env, *q, *r);
            }
        },
    }
}

pub proof fn lemma_agg_teq(schema: Schema, env: Seq<ColTy>, a: Agg, b: Agg)
    requires agg_teq(a, b),
    ensures type_agg(schema, env, a) == type_agg(schema, env, b),
    decreases a, 0nat,
{
    match a {
        Agg::CountStar => {},
        Agg::Count(x) => {
            if let Agg::Count(y) = b {
                lemma_expr_teq(schema, env, x, y);
            }
        },
        Agg::Sum { kind, arg } => {
            if let Agg::Sum { arg: y, .. } = b {
                lemma_expr_teq(schema, env, arg, y);
            }
        },
        Agg::Min(x) => {
            if let Agg::Min(y) = b {
                lemma_expr_teq(schema, env, x, y);
            }
        },
        Agg::Max(x) => {
            if let Agg::Max(y) = b {
                lemma_expr_teq(schema, env, x, y);
            }
        },
        Agg::Avg { kind, arg } => {
            if let Agg::Avg { arg: y, .. } = b {
                lemma_expr_teq(schema, env, arg, y);
            }
        },
        Agg::DistinctAgg(x) => {
            if let Agg::DistinctAgg(y) = b {
                lemma_agg_teq(schema, env, *x, *y);
                // `distinct_agg_ty` reads only the inner aggregate's constructor, which the relation preserves.
                assert(agg_teq(*x, *y));
            }
        },
    }
}

pub proof fn lemma_aggs_teq(schema: Schema, env: Seq<ColTy>, a: Seq<Agg>, b: Seq<Agg>)
    requires aggs_teq(a, b),
    ensures type_aggs(schema, env, a) == type_aggs(schema, env, b),
    decreases a, 1nat,
{
    if a.len() > 0 {
        lemma_aggs_teq(schema, env, a.drop_last(), b.drop_last());
        lemma_agg_teq(schema, env, a.last(), b.last());
    }
}

pub proof fn lemma_query_teq(schema: Schema, ctx: Seq<ColTy>, a: Query, b: Query)
    requires query_teq(a, b),
    ensures type_query(schema, ctx, a) == type_query(schema, ctx, b),
    decreases a,
{
    match a {
        Query::Table(t) => {},
        Query::Filter { pred, input } => {
            if let Query::Filter { pred: p, input: i } = b {
                lemma_query_teq(schema, ctx, *input, *i);
                if let Some(tys) = type_query(schema, ctx, *input) {
                    lemma_pred_teq(schema, ctx + tys, pred, p);
                }
            }
        },
        Query::Project { exprs, input } => {
            if let Query::Project { exprs: es, input: i } = b {
                lemma_query_teq(schema, ctx, *input, *i);
                if let Some(tys) = type_query(schema, ctx, *input) {
                    lemma_exprs_teq(schema, ctx + tys, exprs, es);
                }
            }
        },
        Query::Product { left, right } => {
            if let Query::Product { left: l, right: r } = b {
                lemma_query_teq(schema, ctx, *left, *l);
                lemma_query_teq(schema, ctx, *right, *r);
            }
        },
        Query::LeftJoin { left, right, on } => {
            if let Query::LeftJoin { left: l, right: r, on: p } = b {
                lemma_query_teq(schema, ctx, *left, *l);
                lemma_query_teq(schema, ctx, *right, *r);
                if let (Some(lt), Some(rt)) = (type_query(schema, ctx, *left), type_query(schema, ctx, *right)) {
                    lemma_pred_teq(schema, ctx + lt + rt, on, p);
                }
            }
        },
        Query::Aggregate { aggs, input } => {
            if let Query::Aggregate { aggs: gs, input: i } = b {
                lemma_query_teq(schema, ctx, *input, *i);
                if let Some(tys) = type_query(schema, ctx, *input) {
                    lemma_aggs_teq(schema, ctx + tys, aggs, gs);
                }
            }
        },
        Query::GroupBy { keys, aggs, input } => {
            if let Query::GroupBy { keys: ks, aggs: gs, input: i } = b {
                lemma_query_teq(schema, ctx, *input, *i);
                if let Some(tys) = type_query(schema, ctx, *input) {
                    lemma_exprs_teq(schema, ctx + tys, keys, ks);
                    lemma_aggs_teq(schema, ctx + tys, aggs, gs);
                }
            }
        },
        Query::Distinct(input) => {
            if let Query::Distinct(i) = b {
                lemma_query_teq(schema, ctx, *input, *i);
            }
        },
    }
}

/// A statement typing-equivalent to a checked statement is checked.
pub proof fn lemma_ordered_teq(schema: Schema, a: OrderedQuery, b: OrderedQuery)
    requires ordered_teq(a, b),
    ensures wf_ordered(schema, a) == wf_ordered(schema, b),
{
    lemma_query_teq(schema, Seq::empty(), a.body, b.body);
}

// ------------------------------------------------------------------ list relations from elementwise facts

/// `exprs_teq` from elementwise facts (e.g. two literal lists `seq![..]` of an emitted template).
pub proof fn lemma_exprs_teq_intro(a: Seq<Expr>, b: Seq<Expr>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> expr_teq(#[trigger] a[i], b[i]),
    ensures exprs_teq(a, b),
    decreases a.len(),
{
    if a.len() > 0 {
        let (x, y) = (a.drop_last(), b.drop_last());
        assert forall|i: int| 0 <= i < x.len() implies expr_teq(#[trigger] x[i], y[i]) by {
            assert(a[i] == x[i] && b[i] == y[i]);
        }
        lemma_exprs_teq_intro(x, y);
        assert(expr_teq(a[a.len() - 1], b[b.len() - 1]));
    }
}

/// `aggs_teq` from elementwise facts.
pub proof fn lemma_aggs_teq_intro(a: Seq<Agg>, b: Seq<Agg>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> agg_teq(#[trigger] a[i], b[i]),
    ensures aggs_teq(a, b),
    decreases a.len(),
{
    if a.len() > 0 {
        let (x, y) = (a.drop_last(), b.drop_last());
        assert forall|i: int| 0 <= i < x.len() implies agg_teq(#[trigger] x[i], y[i]) by {
            assert(a[i] == x[i] && b[i] == y[i]);
        }
        lemma_aggs_teq_intro(x, y);
        assert(agg_teq(a[a.len() - 1], b[b.len() - 1]));
    }
}

} // verus!
