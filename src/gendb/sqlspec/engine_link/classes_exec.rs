//! L3, executable checker: the analysis over the executable AST, proved equal to the spec checker of
//! `engine_link::classes` (engine toolkit; nothing here names a query, a table or a column).
//!
//! `expr_info_exec`, `exprs_info_exec`, `pred_info_exec`, `agg_arg_info_exec`, `aggs_arg_info_exec` and
//! `query_info_exec` mirror the spec analysis' mutual recursion over `exec::ast` (the views of
//! `exec::ast::view_*` and `exec::relational::schema::view_schema`). The three class checkers an engine's planner
//! calls at run time are at the end: totality (`*_total_exec`), uniformity (`*_uniform_exec`) and
//! scale-exactness (`*_exact_exec`), each `ensures r == <spec class>`; their meaning is
//! `engine_link::classes_sound`. Termination: `decreases` on the AST, as `exec::relational::check`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::exec::ast::*;
use crate::exec::relational::schema::*;
use crate::engine_link::classes::*;
use crate::engine_link::classes_exec_ops::*;

verus! {

/// Executable `expr_info` (proved equal).
pub fn expr_info_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, e: &EExpr) -> (r: Option<ExprInfo>)
    ensures r == expr_info(view_schema(schema@), env@, view_expr(*e)),
    decreases e, 0nat,
{
    if closed_expr_exec(e) {
        return closed_info_exec(e);
    }
    match e {
        EExpr::Col(i) => if *i < env.len() { Some(ExprInfo { cls: env[*i], errs: Errs::Never, fits: true }) } else { None },
        EExpr::Lit(_) => None,
        EExpr::Neg { kind, arg } => match expr_info_exec(schema, env, arg) {
            Some(a) => after1_exec(a, neg_op_exec(*kind, a.cls)),
            None => None,
        },
        EExpr::Arith { op, kind, a, b } => {
            let x = expr_info_exec(schema, env, a);
            let y = expr_info_exec(schema, env, b);
            match (x, y) {
                (Some(x), Some(y)) => after2_exec(x, y, arith_op_exec(*op, *kind, x.cls, y.cls)),
                _ => None,
            }
        },
        EExpr::Cast { cast, arg } => match expr_info_exec(schema, env, arg) {
            Some(a) => after1_exec(a, cast_op_exec(*cast, a.cls)),
            None => None,
        },
        EExpr::AddInterval { arg, months, days, micros } => match expr_info_exec(schema, env, arg) {
            Some(a) => after1_exec(a, interval_op_exec(*months, *days, *micros, a.cls)),
            None => None,
        },
        EExpr::Call { f, args } => match exprs_info_exec(schema, env, args) {
            Some(l) => after1_exec(
                ExprInfo { cls: VClass { kind: VKind::NoValue, nullable: false }, errs: l.errs, fits: l.fits },
                call_op_exec(*f, args, &l.classes),
            ),
            None => None,
        },
        EExpr::If { cond, then_e, else_e } => {
            let c = pred_info_exec(schema, env, cond);
            let t = expr_info_exec(schema, env, then_e);
            let f = expr_info_exec(schema, env, else_e);
            match (c, t, f) {
                (Some(c), Some(t), Some(f)) => if_info_exec(c, t, f),
                _ => None,
            }
        },
        EExpr::Subquery(q) => match query_info_exec(schema, env, q) {
            Some(qi) => subquery_info_exec(&qi),
            None => None,
        },
    }
}

/// An unclassified prefix leaves the whole list unclassified.
proof fn lemma_exprs_info_prefix_none(schema: Schema, env: Seq<VClass>, es: Seq<Expr>, k: int)
    requires 0 <= k <= es.len(), exprs_info(schema, env, es.take(k)) is None,
    ensures exprs_info(schema, env, es) is None,
    decreases es.len(),
{
    if k < es.len() {
        let d = es.drop_last();
        assert(d.take(k) =~= es.take(k));
        lemma_exprs_info_prefix_none(schema, env, d, k);
    } else {
        assert(es.take(k) =~= es);
    }
}

/// Executable `exprs_info` (proved equal).
pub fn exprs_info_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, es: &Vec<EExpr>) -> (r: Option<EListInfo>)
    ensures view_list_opt(r) == exprs_info(view_schema(schema@), env@, view_exprs(es@)),
    decreases es, 1nat,
{
    let ghost gs = view_schema(schema@);
    let ghost ge = view_exprs(es@);
    proof { lemma_view_exprs_index(es@); }
    let mut classes: Vec<VClass> = Vec::new();
    let mut errs = Errs::Never;
    let mut fits = true;
    let mut i: usize = 0;
    proof {
        assert(ge.take(0) =~= Seq::<Expr>::empty());
        assert(classes@ =~= Seq::<VClass>::empty());
    }
    while i < es.len()
        invariant
            i <= es.len(), gs == view_schema(schema@), ge == view_exprs(es@), ge.len() == es.len(),
            forall|j: int| 0 <= j < es.len() ==> #[trigger] ge[j] == view_expr(es@[j]),
            exprs_info(gs, env@, ge.take(i as int)) == Some(ListInfo { classes: classes@, errs, fits }),
        decreases es.len() - i,
    {
        proof {
            let t = ge.take(i as int + 1);
            assert(t.drop_last() =~= ge.take(i as int));
            assert(t.last() == view_expr(es@[i as int]));
        }
        let x = match expr_info_exec(schema, env, &es[i]) {
            Some(x) => x,
            None => {
                proof { lemma_exprs_info_prefix_none(gs, env@, ge, i as int + 1); }
                return None;
            },
        };
        match errs_join_exec(errs, x.errs) {
            Some(e) => {
                classes.push(x.cls);
                errs = e;
                fits = fits && x.fits;
            },
            None => {
                proof { lemma_exprs_info_prefix_none(gs, env@, ge, i as int + 1); }
                return None;
            },
        }
        i = i + 1;
    }
    proof { assert(ge.take(es.len() as int) =~= ge); }
    Some(EListInfo { classes, errs, fits })
}

/// Executable `pred_info` (proved equal).
pub fn pred_info_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, p: &EPred) -> (r: Option<PredInfo>)
    ensures r == pred_info(view_schema(schema@), env@, view_pred(*p)),
    decreases p, 0nat,
{
    match p {
        EPred::Cmp { op, a, b } => {
            let x = expr_info_exec(schema, env, a);
            let y = expr_info_exec(schema, env, b);
            match (x, y) {
                (Some(x), Some(y)) =>
                    if comparable_exec(x.cls.kind, y.cls.kind) { pred_after2_exec(x.errs, y.errs, x.fits && y.fits) } else { None },
                _ => None,
            }
        },
        EPred::And(a, b) | EPred::Or(a, b) => {
            let x = pred_info_exec(schema, env, a);
            let y = pred_info_exec(schema, env, b);
            match (x, y) {
                (Some(x), Some(y)) => pred_after2_exec(x.errs, y.errs, x.fits && y.fits),
                _ => None,
            }
        },
        EPred::Not(a) => pred_info_exec(schema, env, a),
        EPred::IsNull(e) => match expr_info_exec(schema, env, e) {
            Some(x) => Some(PredInfo { errs: x.errs, fits: x.fits }),
            None => None,
        },
        EPred::OfBool(e) => match expr_info_exec(schema, env, e) {
            Some(x) => match x.cls.kind {
                VKind::Bool | VKind::NoValue => Some(PredInfo { errs: x.errs, fits: x.fits }),
                _ => None,
            },
            None => None,
        },
        EPred::Exists(q) => match query_info_exec(schema, env, q) {
            Some(qi) => Some(PredInfo { errs: qi.errs, fits: qi.fits }),
            None => None,
        },
        EPred::AnyCmp { op, e, q } => {
            let x = expr_info_exec(schema, env, e);
            let qi = query_info_exec(schema, env, q);
            match (x, qi) {
                (Some(x), Some(qi)) =>
                    if qi.cols.len() == 1 && comparable_exec(x.cls.kind, qi.cols[0].kind) {
                        pred_after2_exec(x.errs, qi.errs, x.fits && qi.fits)
                    } else {
                        None
                    },
                _ => None,
            }
        },
    }
}

/// Executable `agg_arg_info` (proved equal).
pub fn agg_arg_info_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, a: &EAgg) -> (r: Option<ExprInfo>)
    ensures r == agg_arg_info(view_schema(schema@), env@, view_agg(*a)),
    decreases a, 0nat,
{
    match a {
        EAgg::CountStar => Some(null_info_exec()),
        EAgg::Count(e) => expr_info_exec(schema, env, e),
        EAgg::Sum { arg, .. } => expr_info_exec(schema, env, arg),
        EAgg::Min(e) => expr_info_exec(schema, env, e),
        EAgg::Max(e) => expr_info_exec(schema, env, e),
        EAgg::Avg { arg, .. } => expr_info_exec(schema, env, arg),
        EAgg::DistinctAgg(inner) => agg_arg_info_exec(schema, env, inner),
    }
}

/// An unclassified prefix leaves the whole list unclassified.
proof fn lemma_aggs_arg_info_prefix_none(schema: Schema, env: Seq<VClass>, aggs: Seq<Agg>, k: int)
    requires 0 <= k <= aggs.len(), aggs_arg_info(schema, env, aggs.take(k)) is None,
    ensures aggs_arg_info(schema, env, aggs) is None,
    decreases aggs.len(),
{
    if k < aggs.len() {
        let d = aggs.drop_last();
        assert(d.take(k) =~= aggs.take(k));
        lemma_aggs_arg_info_prefix_none(schema, env, d, k);
    } else {
        assert(aggs.take(k) =~= aggs);
    }
}

/// Executable `aggs_arg_info` (proved equal).
pub fn aggs_arg_info_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, aggs: &Vec<EAgg>) -> (r: Option<EListInfo>)
    ensures view_list_opt(r) == aggs_arg_info(view_schema(schema@), env@, view_aggs(aggs@)),
    decreases aggs, 1nat,
{
    let ghost gs = view_schema(schema@);
    let ghost ga = view_aggs(aggs@);
    proof { lemma_view_aggs_index(aggs@); }
    let mut classes: Vec<VClass> = Vec::new();
    let mut errs = Errs::Never;
    let mut fits = true;
    let mut i: usize = 0;
    proof {
        assert(ga.take(0) =~= Seq::<Agg>::empty());
        assert(classes@ =~= Seq::<VClass>::empty());
    }
    while i < aggs.len()
        invariant
            i <= aggs.len(), gs == view_schema(schema@), ga == view_aggs(aggs@), ga.len() == aggs.len(),
            forall|j: int| 0 <= j < aggs.len() ==> #[trigger] ga[j] == view_agg(aggs@[j]),
            aggs_arg_info(gs, env@, ga.take(i as int)) == Some(ListInfo { classes: classes@, errs, fits }),
        decreases aggs.len() - i,
    {
        proof {
            let t = ga.take(i as int + 1);
            assert(t.drop_last() =~= ga.take(i as int));
            assert(t.last() == view_agg(aggs@[i as int]));
        }
        let x = match agg_arg_info_exec(schema, env, &aggs[i]) {
            Some(x) => x,
            None => {
                proof { lemma_aggs_arg_info_prefix_none(gs, env@, ga, i as int + 1); }
                return None;
            },
        };
        match errs_join_exec(errs, x.errs) {
            Some(e) => {
                classes.push(x.cls);
                errs = e;
                fits = fits && x.fits;
            },
            None => {
                proof { lemma_aggs_arg_info_prefix_none(gs, env@, ga, i as int + 1); }
                return None;
            },
        }
        i = i + 1;
    }
    proof { assert(ga.take(aggs.len() as int) =~= ga); }
    Some(EListInfo { classes, errs, fits })
}

/// Executable `query_info` (proved equal).
pub fn query_info_exec(schema: &Vec<ETableSchema>, ctx: &Vec<VClass>, q: &EQuery) -> (r: Option<EQueryInfo>)
    ensures view_query_opt(r) == query_info(view_schema(schema@), ctx@, view_query(*q)),
    decreases q, 2nat,
{
    let ghost gs = view_schema(schema@);
    match q {
        EQuery::Table(t) => {
            if *t < schema.len() {
                proof { assert(gs[*t as int] == view_table_schema(schema@[*t as int])); }
                Some(EQueryInfo { cols: table_classes_exec(&schema[*t]), errs: Errs::Never, fits: true, one_row: false })
            } else {
                None
            }
        },
        EQuery::Product { left, right } => {
            let l = query_info_exec(schema, ctx, left);
            let r = query_info_exec(schema, ctx, right);
            match (l, r) {
                (Some(l), Some(r)) => match errs_join_exec(l.errs, r.errs) {
                    Some(e) => Some(EQueryInfo {
                        cols: concat_classes(&l.cols, &r.cols),
                        errs: e,
                        fits: l.fits && r.fits,
                        one_row: l.one_row && r.one_row,
                    }),
                    None => None,
                },
                _ => None,
            }
        },
        EQuery::Distinct(input) => query_info_exec(schema, ctx, input),
        EQuery::Filter { .. } | EQuery::Project { .. } => query_info_row_op_exec(schema, ctx, q),
        EQuery::LeftJoin { .. } => query_info_left_join_exec(schema, ctx, q),
        EQuery::Aggregate { .. } | EQuery::GroupBy { .. } => query_info_aggregation_exec(schema, ctx, q),
    }
}

/// `query_info` of a WHERE or a SELECT list.
fn query_info_row_op_exec(schema: &Vec<ETableSchema>, ctx: &Vec<VClass>, q: &EQuery) -> (r: Option<EQueryInfo>)
    requires q is Filter || q is Project,
    ensures view_query_opt(r) == query_info(view_schema(schema@), ctx@, view_query(*q)),
    decreases q, 1nat,
{
    match q {
        EQuery::Filter { pred, input } => {
            let i = match query_info_exec(schema, ctx, input) {
                Some(i) => i,
                None => return None,
            };
            let env = concat_classes(ctx, &i.cols);
            let p = match pred_info_exec(schema, &env, pred) {
                Some(p) => p,
                None => return None,
            };
            match errs_join_exec(i.errs, p.errs) {
                Some(e) => Some(EQueryInfo { cols: i.cols, errs: e, fits: i.fits && p.fits, one_row: i.one_row }),
                None => None,
            }
        },
        EQuery::Project { exprs, input } => {
            let i = match query_info_exec(schema, ctx, input) {
                Some(i) => i,
                None => return None,
            };
            let env = concat_classes(ctx, &i.cols);
            let l = match exprs_info_exec(schema, &env, exprs) {
                Some(l) => l,
                None => return None,
            };
            match errs_join_exec(i.errs, l.errs) {
                Some(e) => Some(EQueryInfo { cols: l.classes, errs: e, fits: i.fits && l.fits, one_row: i.one_row }),
                None => None,
            }
        },
        _ => None,
    }
}

/// `query_info` of a LEFT JOIN.
fn query_info_left_join_exec(schema: &Vec<ETableSchema>, ctx: &Vec<VClass>, q: &EQuery) -> (r: Option<EQueryInfo>)
    requires q is LeftJoin,
    ensures view_query_opt(r) == query_info(view_schema(schema@), ctx@, view_query(*q)),
    decreases q, 1nat,
{
    match q {
        EQuery::LeftJoin { left, right, on } => {
            let l = query_info_exec(schema, ctx, left);
            let r = query_info_exec(schema, ctx, right);
            match (l, r) {
                (Some(l), Some(r)) => {
                    let lc = concat_classes(ctx, &l.cols);
                    let env = concat_classes(&lc, &r.cols);
                    match pred_info_exec(schema, &env, on) {
                        Some(p) => match errs_join3_exec(l.errs, r.errs, p.errs) {
                            Some(e) => {
                                let n = r.cols.len();
                                proof { assert(r.cols@.len() == n); }
                                Some(EQueryInfo {
                                    cols: concat_classes(&l.cols, &nullable_classes_exec(&r.cols)),
                                    errs: e,
                                    fits: l.fits && r.fits && p.fits,
                                    one_row: false,
                                })
                            },
                            None => None,
                        },
                        None => None,
                    }
                },
                _ => None,
            }
        },
        _ => None,
    }
}

/// `query_info` of an aggregation (with or without GROUP BY).
fn query_info_aggregation_exec(schema: &Vec<ETableSchema>, ctx: &Vec<VClass>, q: &EQuery) -> (r: Option<EQueryInfo>)
    requires q is Aggregate || q is GroupBy,
    ensures view_query_opt(r) == query_info(view_schema(schema@), ctx@, view_query(*q)),
    decreases q, 1nat,
{
    match q {
        EQuery::Aggregate { aggs, input } => {
            let i = match query_info_exec(schema, ctx, input) {
                Some(i) => i,
                None => return None,
            };
            let env = concat_classes(ctx, &i.cols);
            let a = match aggs_arg_info_exec(schema, &env, aggs) {
                Some(a) => a,
                None => return None,
            };
            let v = match aggs_value_info_exec(aggs, &a.classes) {
                Some(v) => v,
                None => return None,
            };
            match errs_join3_exec(i.errs, a.errs, v.errs) {
                Some(e) => Some(EQueryInfo { cols: v.classes, errs: e, fits: i.fits && a.fits && v.fits, one_row: true }),
                None => None,
            }
        },
        EQuery::GroupBy { keys, aggs, input } => {
            let i = match query_info_exec(schema, ctx, input) {
                Some(i) => i,
                None => return None,
            };
            let env = concat_classes(ctx, &i.cols);
            let k = exprs_info_exec(schema, &env, keys);
            let a = aggs_arg_info_exec(schema, &env, aggs);
            match (k, a) {
                (Some(k), Some(a)) => match aggs_value_info_exec(aggs, &a.classes) {
                    Some(v) => match errs_join3_exec(i.errs, k.errs, a.errs) {
                        Some(e1) => match errs_join_exec(e1, v.errs) {
                            Some(e) => Some(EQueryInfo {
                                cols: concat_classes(&k.classes, &v.classes),
                                errs: e,
                                fits: i.fits && k.fits && a.fits && v.fits,
                                one_row: false,
                            }),
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                },
                _ => None,
            }
        },
        _ => None,
    }
}

// ------------------------------------------------------------------------------------- the three class checkers

/// The error set allows only `code` (or none).
pub fn errs_only_exec(e: Errs, code: SqlError) -> (r: bool)
    ensures r == errs_only(e, code),
{
    match e {
        Errs::Never => true,
        Errs::Only(c) => same_error(c, code),
    }
}

/// `classes_exact`.
pub fn classes_exact_exec(cs: &Vec<VClass>) -> (r: bool)
    ensures r == classes_exact(cs@),
{
    let mut i: usize = 0;
    proof { assert(cs@.take(0) =~= Seq::<VClass>::empty()); }
    while i < cs.len()
        invariant i <= cs.len(), classes_exact(cs@.take(i as int)),
        decreases cs.len() - i,
    {
        proof {
            let t = cs@.take(i as int + 1);
            assert(t.drop_last() =~= cs@.take(i as int));
            assert(t.last() == cs@[i as int]);
        }
        match cs[i].kind {
            VKind::NumAny => {
                proof { lemma_classes_exact_prefix(cs@, i as int + 1); }
                return false;
            },
            _ => {},
        }
        i = i + 1;
    }
    proof { assert(cs@.take(cs.len() as int) =~= cs@); }
    true
}

proof fn lemma_classes_exact_prefix(cs: Seq<VClass>, k: int)
    requires 0 <= k <= cs.len(), !classes_exact(cs.take(k)),
    ensures !classes_exact(cs),
    decreases cs.len(),
{
    if k < cs.len() {
        let d = cs.drop_last();
        assert(d.take(k) =~= cs.take(k));
        lemma_classes_exact_prefix(d, k);
    } else {
        assert(cs.take(k) =~= cs);
    }
}

/// Totality of an expression (L3).
pub fn expr_total_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, e: &EExpr) -> (r: bool)
    ensures r == expr_total(view_schema(schema@), env@, view_expr(*e)),
{
    match expr_info_exec(schema, env, e) {
        Some(i) => match i.errs { Errs::Never => i.fits, _ => false },
        None => false,
    }
}

/// Totality of a condition (L3): the check a planner makes before skipping or reordering its evaluation.
pub fn pred_total_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, p: &EPred) -> (r: bool)
    ensures r == pred_total(view_schema(schema@), env@, view_pred(*p)),
{
    match pred_info_exec(schema, env, p) {
        Some(i) => match i.errs { Errs::Never => i.fits, _ => false },
        None => false,
    }
}

/// Totality of a query (L3).
pub fn query_total_exec(schema: &Vec<ETableSchema>, ctx: &Vec<VClass>, q: &EQuery) -> (r: bool)
    ensures r == query_total(view_schema(schema@), ctx@, view_query(*q)),
{
    match query_info_exec(schema, ctx, q) {
        Some(i) => match i.errs { Errs::Never => i.fits, _ => false },
        None => false,
    }
}

/// Uniformity of an expression (L3).
pub fn expr_uniform_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, e: &EExpr, code: SqlError) -> (r: bool)
    ensures r == expr_uniform(view_schema(schema@), env@, view_expr(*e), code),
{
    match expr_info_exec(schema, env, e) {
        Some(i) => errs_only_exec(i.errs, code),
        None => false,
    }
}

/// Uniformity of a condition (L3).
pub fn pred_uniform_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, p: &EPred, code: SqlError) -> (r: bool)
    ensures r == pred_uniform(view_schema(schema@), env@, view_pred(*p), code),
{
    match pred_info_exec(schema, env, p) {
        Some(i) => errs_only_exec(i.errs, code),
        None => false,
    }
}

/// Uniformity of a query (L3).
pub fn query_uniform_exec(schema: &Vec<ETableSchema>, ctx: &Vec<VClass>, q: &EQuery, code: SqlError) -> (r: bool)
    ensures r == query_uniform(view_schema(schema@), ctx@, view_query(*q), code),
{
    match query_info_exec(schema, ctx, q) {
        Some(i) => errs_only_exec(i.errs, code),
        None => false,
    }
}

/// Scale-exactness of an expression (L3).
pub fn expr_exact_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, e: &EExpr) -> (r: bool)
    ensures r == expr_exact(view_schema(schema@), env@, view_expr(*e)),
{
    match expr_info_exec(schema, env, e) {
        Some(i) => match i.cls.kind { VKind::NumAny => false, _ => true },
        None => false,
    }
}

/// Scale-exactness of a key list (L3): GROUP BY keys whose groups do not depend on the row order.
pub fn exprs_exact_exec(schema: &Vec<ETableSchema>, env: &Vec<VClass>, es: &Vec<EExpr>) -> (r: bool)
    ensures r == exprs_exact(view_schema(schema@), env@, view_exprs(es@)),
{
    match exprs_info_exec(schema, env, es) {
        Some(l) => classes_exact_exec(&l.classes),
        None => false,
    }
}

/// Scale-exactness of a query's output (L3): DISTINCT whose result does not depend on the row order.
pub fn query_exact_exec(schema: &Vec<ETableSchema>, ctx: &Vec<VClass>, q: &EQuery) -> (r: bool)
    ensures r == query_exact(view_schema(schema@), ctx@, view_query(*q)),
{
    match query_info_exec(schema, ctx, q) {
        Some(i) => classes_exact_exec(&i.cols),
        None => false,
    }
}

} // verus!
