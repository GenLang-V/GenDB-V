//! The statement's body in normal form. Over the joined rows `X = xs(t)` (`nf`):
//! - the WHERE filter keeps the rows satisfying `qualx` (`lemma_where_eval`);
//! - GROUP BY ps_partkey gives one row `[key, SUM]` per group key with a qualifying row, in first-occurrence order
//!   (`lemma_group_eval`, inside `group_caps`);
//! - the HAVING subquery, evaluated behind any 2-value group row, is the one row `[T * $2]` (`T` the scalar SUM over
//!   all qualifying rows, `lemma_sub_eval`), so a group row passes HAVING exactly when `S * 10^10 > T * p`
//!   (`S` its SUM coefficient, `p` the coefficient of `$2` at scale 10; `lemma_having_row`);
//! - the body is the group rows that pass (`lemma_body`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::scalar::*;
use crate::spec::numeric::{abs, pow10, align, sign};
use crate::spec::relation::{collect, product_rows, keep_true, agg_row};
use crate::spec::order::denote_body;
use crate::spec::equality::row_not_distinct;
use crate::link::expr::{ival, fits_i128, lemma_compare_num, lemma_align_by, lemma_align_same, lemma_pred_cmp, int_cmp};
use crate::link::query::*;
use crate::link::join::{keep, lemma_keep_true_keep, lemma_keep_members};
use crate::bridge::collect::lemma_collect_all;
use crate::query::query_spec_at;
use super::nf::*;
use super::sqlrow::*;
use super::tables::Tabs;
use super::bind::tabs_of;

verus! {

/// The 16 positions of a joined row (the normal form reads joined rows whole).
pub open spec fn id16() -> Seq<nat> {
    Seq::new(16, |i: int| i as nat)
}

pub proof fn lemma_proj16(x: Row)
    requires x.len() == 16,
    ensures proj(x, id16()) == x,
{
    assert(proj(x, id16()) =~= x);
}

/// Projecting the joined rows on all 16 positions keeps them.
pub proof fn lemma_proj_xs(t: Tabs)
    requires tabs_typed(t),
    ensures proj_all(xs(t), id16()) == xs(t),
{
    lemma_xs_width(t);
    assert forall|i: int| 0 <= i < xs(t).len() implies #[trigger] proj_all(xs(t), id16())[i] == xs(t)[i] by {
        lemma_proj16(xs(t)[i]);
    }
    assert(proj_all(xs(t), id16()) =~= xs(t));
}

/// `FROM partsupp, supplier, nation` in any outer context.
pub proof fn lemma_prod_eval(db: Database, ctx: Row)
    requires db.tables.len() == 8,
    ensures eval_query(db, ctx, prod_q()) == Ok::<Relation, SqlError>(xs(tabs_of(db))),
{
    let l = Query::Product { left: Box::new(Query::Table(4)), right: Box::new(Query::Table(5)) };
    assert(eval_query(db, ctx, Query::Table(4)) == Ok::<Relation, SqlError>(db.tables[4]));
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
    assert(eval_query(db, ctx, Query::Table(6)) == Ok::<Relation, SqlError>(db.tables[6]));
    assert(eval_query(db, ctx, l) == Ok::<Relation, SqlError>(product_rows(db.tables[4], db.tables[5])));
}

/// One step of a WHERE over an input that evaluates to `rows`.
pub proof fn lemma_filter_unfold(db: Database, ctx: Row, pred: Pred, input: Query, rows: Relation)
    requires eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
    ensures
        eval_query(db, ctx, Query::Filter { pred, input: Box::new(input) })
            == match collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) {
                Err(err) => Err(err),
                Ok(truths) => Ok::<Relation, SqlError>(keep_true(rows, truths)),
            },
{
    crate::bridge::collect::lemma_collect_pointwise::<Truth>();
}

/// One step of an aggregate (no GROUP BY) over an input that evaluates to `rows`.
pub proof fn lemma_aggregate_step(db: Database, ctx: Row, aggs: Seq<Agg>, input: Query, rows: Relation)
    requires eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
    ensures
        eval_query(db, ctx, Query::Aggregate { aggs, input: Box::new(input) })
            == match collect(Seq::new(rows.len(), |i: int| agg_args(db, ctx + rows[i], aggs))) {
                Err(err) => Err(err),
                Ok(args) => match agg_row(aggs, args) {
                    Err(err) => Err(err),
                    Ok(row) => Ok::<Relation, SqlError>(seq![row]),
                },
            },
{
    hide(agg_row);
    crate::bridge::collect::lemma_collect_pointwise::<Row>();
}

/// The WHERE filter.
pub proof fn lemma_where_eval(db: Database, name: Seq<u8>)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)),
    ensures ({
        let x = xs(tabs_of(db));
        eval_query(db, Seq::empty(), where_q(Literal::Text(name)))
            == Ok::<Relation, SqlError>(keep_true(x, qual_truths(gq(name), proj_all(x, id16()))))
    }),
{
    let t = tabs_of(db);
    let x = xs(t);
    lemma_prod_eval(db, Seq::empty());
    lemma_xs_typed(t);
    assert forall|i: int| 0 <= i < x.len() implies
        eval_pred(db, #[trigger] x[i], where_at(0, Literal::Text(name)))
            == Ok::<Truth, SqlError>(truth_of((gq(name).qual)(proj(x[i], id16())))) by {
        assert(x_typed(x[i]));
        lemma_where_row(db, x[i], name);
        lemma_proj16(x[i]);
    }
    assert(pred_agrees(db, x, id16(), where_at(0, Literal::Text(name)), gq(name)));
    lemma_filter_rows(db, prod_q(), x, id16(), where_at(0, Literal::Text(name)), gq(name));
}

/// The SUM argument agrees with a normal form whose argument is `argx`.
proof fn lemma_args_agree(db: Database, name: Seq<u8>, g: QuerySpec)
    requires
        db.tables.len() == 8, tabs_typed(tabs_of(db)),
        g.aggs == seq![AggKind::Sum { scale: 2 }],
        forall|x: Row| #[trigger] (g.arg)(0, x) == argx(x),
    ensures args_agree(db, xs(tabs_of(db)), id16(), seq![sum_at(0)], g),
{
    let x = xs(tabs_of(db));
    lemma_xs_typed(tabs_of(db));
    assert forall|i: int| 0 <= i < x.len() && (g.qual)(proj(#[trigger] x[i], id16())) implies
        agg_args(db, x[i], seq![sum_at(0)]) == Ok::<Row, SqlError>(arg_vals(g, proj(x[i], id16()))) by {
        assert(x_typed(x[i]));
        lemma_proj16(x[i]);
        lemma_args_row(db, x[i], g);
    }
}

/// Group keys of qualifying rows are exact (one integer each).
proof fn lemma_keys_exact(t: Tabs, name: Seq<u8>)
    requires tabs_typed(t),
    ensures keys_exact(gq(name), proj_all(xs(t), id16())),
{
    let g = gq(name);
    lemma_proj_xs(t);
    lemma_xs_typed(t);
    let x = xs(t);
    assert forall|a: int, b: int| 0 <= a < x.len() && 0 <= b < x.len() && (g.qual)(x[a]) && (g.qual)(x[b]) implies
        (row_not_distinct(#[trigger] (g.key)(x[a]), #[trigger] (g.key)(x[b])) <==> (g.key)(x[a]) == (g.key)(x[b])) by {
        assert(x_typed(x[a]) && x_typed(x[b]));
        crate::link::query::lemma_row_exact((g.key)(x[a]), (g.key)(x[b]));
    }
}

/// The GROUP BY: one `key ++ [SUM]` row per group key with a qualifying row (first-occurrence order).
pub proof fn lemma_group_eval(db: Database, name: Seq<u8>)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), group_caps(gq(name), xs(tabs_of(db))),
    ensures ({
        let x = xs(tabs_of(db));
        eval_query(db, Seq::empty(), group_q(Literal::Text(name)))
            == Ok::<Relation, SqlError>(gkeys(gq(name), x).map_values(|k: Row| full_row(gq(name), x, k)))
    }),
{
    let t = tabs_of(db);
    let x = xs(t);
    let g = gq(name);
    lemma_where_eval(db, name);
    lemma_xs_typed(t);
    lemma_proj_xs(t);
    assert forall|i: int| 0 <= i < x.len() && (g.qual)(proj(#[trigger] x[i], id16())) implies
        eval_exprs(db, x[i], seq![Expr::Col(0)]) == Ok::<Row, SqlError>((g.key)(proj(x[i], id16()))) by {
        assert(x_typed(x[i]));
        lemma_proj16(x[i]);
        lemma_key_row(db, x[i]);
    }
    assert(keys_agree(db, x, id16(), seq![Expr::Col(0)], g));
    lemma_args_agree(db, name, g);
    assert(aggs_match(seq![sum_at(0)], g));
    lemma_keys_exact(t, name);
    lemma_group_query(db, x, id16(), where_q(Literal::Text(name)), seq![Expr::Col(0)], seq![sum_at(0)], g);
}

/// The scalar aggregate at the top level: the one row `[SUM]` (NULL without a qualifying row).
pub proof fn lemma_agg0_eval(db: Database, name: Seq<u8>)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), group_caps(gs(name), xs(tabs_of(db))),
    ensures
        eval_query(db, Seq::empty(), agg_0(Literal::Text(name)))
            == Ok::<Relation, SqlError>(seq![full_row(gs(name), xs(tabs_of(db)), Seq::empty())]),
{
    let t = tabs_of(db);
    let x = xs(t);
    let g = gs(name);
    lemma_where_eval(db, name);
    lemma_proj_xs(t);
    // The WHERE truths of the scalar normal form are those of the grouped one (same condition).
    assert(qual_truths(g, x) =~= qual_truths(gq(name), x));
    lemma_args_agree(db, name, g);
    assert(aggs_match(seq![sum_at(0)], g));
    assert(scalar_key(g));
    lemma_aggregate_query(db, x, id16(), where_q(Literal::Text(name)), seq![sum_at(0)], g);
}

/// The subquery's WHERE behind a 2-value row keeps the same rows as the top-level WHERE.
proof fn lemma_where_s_eval(db: Database, w: Row, lit: Literal)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), w.len() == 2,
    ensures
        eval_query(db, w, Query::Filter { pred: where_at(2, lit), input: Box::new(prod_q()) })
            == eval_query(db, Seq::empty(), where_q(lit)),
{
    hide(eval_pred);
    hide(eval_query);
    let x = xs(tabs_of(db));
    lemma_prod_eval(db, w);
    lemma_prod_eval(db, Seq::empty());
    lemma_xs_width(tabs_of(db));
    lemma_filter_unfold(db, w, where_at(2, lit), prod_q(), x);
    lemma_filter_unfold(db, Seq::empty(), where_at(0, lit), prod_q(), x);
    assert forall|i: int| 0 <= i < x.len() implies
        #[trigger] eval_pred(db, w + x[i], where_at(2, lit)) == eval_pred(db, Seq::<Val>::empty() + x[i], where_at(0, lit)) by {
        lemma_where_shift(db, w, x[i], lit);
        assert(Seq::<Val>::empty() + x[i] =~= x[i]);
    }
    crate::bridge::collect::lemma_collect_pointwise::<Truth>();
}

/// A SUM's value does not depend on its argument expression (only on the argument values).
proof fn lemma_agg_row_same(args: Seq<Row>)
    ensures crate::spec::relation::agg_row(seq![sum_at(2)], args) == crate::spec::relation::agg_row(seq![sum_at(0)], args),
{
    let vs = crate::spec::relation::column(args, 0);
    assert(crate::spec::relation::agg_value(sum_at(2), vs) == crate::spec::relation::agg_value(sum_at(0), vs));
    crate::bridge::collect::lemma_collect_pointwise::<Val>();
}

/// The subquery's aggregate behind a 2-value row is the top-level aggregate.
pub proof fn lemma_agg_s_eval(db: Database, w: Row, name: Seq<u8>)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), w.len() == 2,
    ensures eval_query(db, w, agg_s(Literal::Text(name))) == eval_query(db, Seq::empty(), agg_0(Literal::Text(name))),
{
    hide(eval_pred);
    hide(eval_query);
    hide(agg_args);
    let lit = Literal::Text(name);
    let t = tabs_of(db);
    let x = xs(t);
    lemma_where_s_eval(db, w, lit);
    lemma_where_eval(db, name);
    lemma_xs_width(t);
    let kept = keep_true(x, qual_truths(gq(name), proj_all(x, id16())));
    let f2 = Query::Filter { pred: where_at(2, lit), input: Box::new(prod_q()) };
    lemma_aggregate_step(db, w, seq![sum_at(2)], f2, kept);
    lemma_aggregate_step(db, Seq::empty(), seq![sum_at(0)], where_q(lit), kept);
    // Every kept row is a joined row (16 values).
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] kept[i]).len() == 16 by {
        crate::link::query::lemma_keep_true_member(x, qual_truths(gq(name), proj_all(x, id16())), i);
    }
    assert forall|i: int| 0 <= i < kept.len() implies
        #[trigger] agg_args(db, w + kept[i], seq![sum_at(2)]) == agg_args(db, Seq::<Val>::empty() + kept[i], seq![sum_at(0)]) by {
        lemma_args_shift(db, w, kept[i]);
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
    }
    crate::bridge::collect::lemma_collect_pointwise::<Row>();
    assert(eval_query(db, w, f2) == Ok::<Relation, SqlError>(kept));
    let c2 = collect(Seq::new(kept.len(), |i: int| agg_args(db, w + kept[i], seq![sum_at(2)])));
    let c0 = collect(Seq::new(kept.len(), |i: int| agg_args(db, Seq::<Val>::empty() + kept[i], seq![sum_at(0)])));
    assert(c2 == c0);
    assert(agg_s(lit) == Query::Aggregate { aggs: seq![sum_at(2)], input: Box::new(f2) });
    assert(agg_0(lit) == Query::Aggregate { aggs: seq![sum_at(0)], input: Box::new(where_q(lit)) });
    let r2 = match c2 { Err(err) => Err(err), Ok(args) => match agg_row(seq![sum_at(2)], args) { Err(err) => Err(err), Ok(row) => Ok::<Relation, SqlError>(seq![row]) } };
    let r0 = match c0 { Err(err) => Err(err), Ok(args) => match agg_row(seq![sum_at(0)], args) { Err(err) => Err(err), Ok(row) => Ok::<Relation, SqlError>(seq![row]) } };
    assert(eval_query(db, w, agg_s(lit)) == r2);
    assert(eval_query(db, Seq::empty(), agg_0(lit)) == r0);
    if c2 is Ok {
        lemma_agg_row_same(c2->Ok_0);
    }
}


/// One step of a projection over an input that evaluates to `rows`.
pub proof fn lemma_project_step(db: Database, ctx: Row, exprs: Seq<Expr>, input: Query, rows: Relation)
    requires eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
    ensures
        eval_query(db, ctx, Query::Project { exprs, input: Box::new(input) })
            == collect(Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], exprs))),
{
    crate::bridge::collect::lemma_collect_pointwise::<Row>();
}

/// A qualifying row of group `k` makes the group non-empty.
pub proof fn lemma_count_pos(g: QuerySpec, xs: Seq<Row>, m: int, k: Row)
    requires 0 <= m < xs.len(), hit(g, xs[m], k),
    ensures gcount(g, xs, k) > 0,
    decreases xs.len(),
{
    if m < xs.len() - 1 {
        assert(xs.drop_last()[m] == xs[m]);
        lemma_count_pos(g, xs.drop_last(), m, k);
    }
}

/// The value of `$2` as a literal.
pub open spec fn p_coeff(p: Literal) -> int {
    match p { Literal::Num { coeff, scale } => coeff, _ => 0 }
}

pub open spec fn p_ok(p: Literal) -> bool {
    &&& p is Num
    &&& p->Num_scale == 10
    &&& abs(p->Num_coeff) < pow10(38)
}

/// The scalar SUM coefficient `T` over all qualifying rows.
pub open spec fn tot(name: Seq<u8>, x: Seq<Row>) -> int {
    gsum(gs(name), x, Seq::empty(), 0)
}

/// The value of the HAVING subquery: NULL without a qualifying row, else `T * $2` at scale 12.
pub open spec fn sub_val(name: Seq<u8>, x: Seq<Row>, p: Literal) -> Val {
    if gcount(gs(name), x, Seq::empty()) == 0 { Val::Null } else { Val::Num { coeff: tot(name, x) * p_coeff(p), scale: 12 } }
}

/// `SUM(..) * $2` on the subquery's aggregate row.
proof fn lemma_mul_row(db: Database, env: Row, v: Val, p: Literal)
    requires
        env.len() == 3, env[2] == v, p_ok(p),
        v is Null || (v is Num && v->Num_scale == 2 && abs(v->Num_coeff) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff),
    ensures
        eval_expr(db, env, mul_e(p)) == Ok::<Val, SqlError>(
            if v is Null { Val::Null } else { Val::Num { coeff: v->Num_coeff * p_coeff(p), scale: 12 } }),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    let pc = p_coeff(p);
    assert(crate::spec::limits::numeric_int_digits_max() == 131072);
    assert(crate::spec::limits::numeric_dscale_max() == 16383);
    crate::link::query::lemma_digits_in_range(pc, 10, 38);
    assert(eval_expr(db, env, Expr::Lit(p)) == Ok::<Val, SqlError>(Val::Num { coeff: pc, scale: 10 }));
    assert(eval_expr(db, env, Expr::Col(2)) == Ok::<Val, SqlError>(v));
    if v is Num {
        assert(pow10(39) == 1000000000000000000000000000000000000000) by (compute);
        lemma_node_mul(db, env, Expr::Col(2), Expr::Lit(p), v->Num_coeff, 2, 39, pc, 10, 38);
    }
}

/// The subquery's aggregate row behind any 2-value row: `[SUM]` (NULL without a qualifying row).
proof fn lemma_sub_agg(db: Database, name: Seq<u8>, w: Row)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), w.len() == 2,
        group_caps(gs(name), xs(tabs_of(db))),
    ensures ({
        let x = xs(tabs_of(db));
        let e = Seq::<Val>::empty();
        eval_query(db, w, agg_s(Literal::Text(name)))
            == Ok::<Relation, SqlError>(seq![seq![agg_out(AggKind::Sum { scale: 2 }, gcount(gs(name), x, e), gsum(gs(name), x, e, 0))]])
    }),
{
    hide(eval_query);
    let x = xs(tabs_of(db));
    let e = Seq::<Val>::empty();
    lemma_agg_s_eval(db, w, name);
    lemma_agg0_eval(db, name);
    assert(full_row(gs(name), x, e) =~= seq![agg_out(AggKind::Sum { scale: 2 }, gcount(gs(name), x, e), gsum(gs(name), x, e, 0))]);
}

/// A projection of one expression over a one-row input.
proof fn lemma_project_one(db: Database, ctx: Row, ex: Expr, input: Query, r: Row, v: Val)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(seq![r]),
        eval_expr(db, ctx + r, ex) == Ok::<Val, SqlError>(v),
    ensures eval_query(db, ctx, Query::Project { exprs: seq![ex], input: Box::new(input) }) == Ok::<Relation, SqlError>(seq![seq![v]]),
{
    hide(eval_query);
    hide(eval_expr);
    lemma_project_step(db, ctx, seq![ex], input, seq![r]);
    let es = seq![ex];
    crate::spec::eval::lemma_expr_results_index(db, ctx + r, es);
    lemma_collect_all(crate::spec::eval::expr_results(db, ctx + r, es), seq![v]);
    let rs = Seq::new(1, |i: int| eval_exprs(db, ctx + seq![r][i], es));
    assert(rs[0] == eval_exprs(db, ctx + r, es));
    lemma_collect_all(rs, seq![seq![v]]);
}

/// The HAVING subquery behind any 2-value row: one row holding `sub_val`.
pub proof fn lemma_sub_eval(db: Database, name: Seq<u8>, p: Literal, w: Row)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), w.len() == 2, p_ok(p),
        group_caps(gs(name), xs(tabs_of(db))),
    ensures
        eval_query(db, w, sub_q(Literal::Text(name), p))
            == Ok::<Relation, SqlError>(seq![seq![sub_val(name, xs(tabs_of(db)), p)]]),
{
    hide(eval_query);
    hide(eval_expr);
    let x = xs(tabs_of(db));
    let g = gs(name);
    let e = Seq::<Val>::empty();
    lemma_sub_agg(db, name, w);
    let v = agg_out(AggKind::Sum { scale: 2 }, gcount(g, x, e), gsum(g, x, e, 0));
    if gcount(g, x, e) > 0 {
        crate::link::query::lemma_abs_bound(g, x, e, 0);
    }
    let env = w + seq![v];
    assert(env[2] == v);
    lemma_mul_row(db, env, v, p);
    lemma_project_one(db, w, mul_e(p), agg_s(Literal::Text(name)), seq![v], sub_val(name, x, p));
}

/// The HAVING condition holds on a group row: `S * 10^10 > T * $2`.
pub open spec fn passes(name: Seq<u8>, x: Seq<Row>, p: Literal, w: Row) -> bool {
    ival(w[1]) * 10000000000 > tot(name, x) * p_coeff(p)
}

/// The row of a group `k` (one key value): `k ++ [SUM]`, SUM non-NULL when the group is non-empty.
proof fn lemma_group_row(g: QuerySpec, x: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 2 }], k.len() == 1, gcount(g, x, k) > 0,
    ensures ({
        let w = full_row(g, x, k);
        &&& w.len() == 2
        &&& w[0] == k[0]
        &&& w[1] == (Val::Num { coeff: gsum(g, x, k, 0), scale: 2 })
    }),
{
    assert(full_row(g, x, k) =~= k + seq![Val::Num { coeff: gsum(g, x, k, 0), scale: 2 }]);
}

/// The value of the HAVING subquery expression on the row of a non-empty group.
proof fn lemma_subq_value(db: Database, name: Seq<u8>, p: Literal, w: Row)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), p_ok(p), w.len() == 2,
        group_caps(gs(name), xs(tabs_of(db))),
        gcount(gs(name), xs(tabs_of(db)), Seq::empty()) > 0,
    ensures
        eval_expr(db, w, Expr::Subquery(Box::new(sub_q(Literal::Text(name), p))))
            == Ok::<Val, SqlError>(Val::Num { coeff: tot(name, xs(tabs_of(db))) * p_coeff(p), scale: 12 }),
{
    hide(eval_query);
    hide(eval_expr);
    lemma_sub_eval(db, name, p, w);
    let v = sub_val(name, xs(tabs_of(db)), p);
    lemma_subquery_expr(db, w, sub_q(Literal::Text(name), p), v);
}

/// A scalar subquery evaluating to one one-value row is that value.
proof fn lemma_subquery_expr(db: Database, env: Row, q: Query, v: Val)
    requires eval_query(db, env, q) == Ok::<Relation, SqlError>(seq![seq![v]]),
    ensures eval_expr(db, env, Expr::Subquery(Box::new(q))) == Ok::<Val, SqlError>(v),
{
    hide(eval_pred);
    hide(eval_exprs);
    assert(subquery_value(seq![seq![v]]) == Ok::<Val, SqlError>(v));
}

/// The HAVING condition on the row of a non-empty group.
pub proof fn lemma_having_row(db: Database, name: Seq<u8>, p: Literal, k: Row)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), p_ok(p),
        group_caps(gs(name), xs(tabs_of(db))),
        k.len() == 1, gcount(gq(name), xs(tabs_of(db)), k) > 0,
    ensures ({
        let w = full_row(gq(name), xs(tabs_of(db)), k);
        &&& w.len() == 2
        &&& w[1] == (Val::Num { coeff: gsum(gq(name), xs(tabs_of(db)), k, 0), scale: 2 })
        &&& eval_pred(db, Seq::<Val>::empty() + w, having_p(Literal::Text(name), p))
            == Ok::<Truth, SqlError>(truth_of(passes(name, xs(tabs_of(db)), p, w)))
    }),
{
    hide(eval_query);
    hide(eval_expr);
    hide(full_row);
    let x = xs(tabs_of(db));
    let g = gq(name);
    let w = full_row(g, x, k);
    let e = Seq::<Val>::empty();
    lemma_group_row(g, x, k);
    assert(e + w =~= w);
    // The subquery's group is non-empty: a qualifying row of group `k` qualifies for it.
    crate::link::query::lemma_count_witness(g, x, k);
    let m = choose|m: int| 0 <= m < x.len() && #[trigger] hit(g, x[m], k);
    assert(hit(gs(name), x[m], e));
    lemma_count_pos(gs(name), x, m, e);
    lemma_subq_value(db, name, p, w);
    let s = gsum(g, x, k, 0);
    let tp = tot(name, x) * p_coeff(p);
    let va = Val::Num { coeff: s, scale: 2 };
    let vb = Val::Num { coeff: tp, scale: 12 };
    crate::link::expr::lemma_expr_col(db, w, 1);
    lemma_compare_num(s, 2, tp, 12);
    assert(pow10(10) == 10000000000) by (compute);
    lemma_align_by(s, 2, 12, 10000000000);
    lemma_align_same(tp, 12);
    lemma_pred_cmp(db, w, CmpOp::Gt, Expr::Col(1), Expr::Subquery(Box::new(sub_q(Literal::Text(name), p))), va, vb,
        s * 10000000000, tp);
}

/// The group rows of the outer query.
pub open spec fn grows(name: Seq<u8>, x: Seq<Row>) -> Seq<Row> {
    gkeys(gq(name), x).map_values(|k: Row| full_row(gq(name), x, k))
}

/// The statement's body: the group rows that pass HAVING.
pub proof fn lemma_body(db: Database, name: Seq<u8>, p: Literal)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), p_ok(p),
        group_caps(gs(name), xs(tabs_of(db))), group_caps(gq(name), xs(tabs_of(db))),
    ensures
        eval_query(db, Seq::empty(), body_q(Literal::Text(name), p))
            == Ok::<Relation, SqlError>(keep(grows(name, xs(tabs_of(db))), |w: Row| passes(name, xs(tabs_of(db)), p, w))),
{
    hide(eval_query);
    hide(eval_pred);
    let x = xs(tabs_of(db));
    let g = gq(name);
    let gr = grows(name, x);
    let f = |w: Row| passes(name, x, p, w);
    lemma_group_eval(db, name);
    lemma_filter_unfold(db, Seq::empty(), having_p(Literal::Text(name), p), group_q(Literal::Text(name)), gr);
    crate::link::query::lemma_gkeys(g, x);
    let truths = Seq::new(gr.len(), |i: int| truth_of(f(gr[i])));
    let rs = Seq::new(gr.len(), |i: int| eval_pred(db, Seq::<Val>::empty() + gr[i], having_p(Literal::Text(name), p)));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        let k = gkeys(g, x)[i];
        assert(gkeys(g, x).contains(k));
        crate::link::query::lemma_gkeys_witness(g, x, k);
        let m = choose|m: int| 0 <= m < x.len() && #[trigger] hit(g, x[m], k);
        lemma_having_row(db, name, p, k);
    }
    lemma_collect_all(rs, truths);
    lemma_keep_true_keep(gr, truths, f);
}

/// Public forms of two private steps (used by the capacity proofs).
pub proof fn lemma_where_s_eval_pub(db: Database, w: Row, lit: Literal)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), w.len() == 2,
    ensures
        eval_query(db, w, Query::Filter { pred: where_at(2, lit), input: Box::new(prod_q()) })
            == eval_query(db, Seq::empty(), where_q(lit)),
{
    lemma_where_s_eval(db, w, lit);
}

pub proof fn lemma_sub_agg_pub(db: Database, name: Seq<u8>, w: Row)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), w.len() == 2,
        group_caps(gs(name), xs(tabs_of(db))),
    ensures ({
        let x = xs(tabs_of(db));
        let e = Seq::<Val>::empty();
        eval_query(db, w, agg_s(Literal::Text(name)))
            == Ok::<Relation, SqlError>(seq![seq![agg_out(AggKind::Sum { scale: 2 }, gcount(gs(name), x, e), gsum(gs(name), x, e, 0))]])
    }),
{
    lemma_sub_agg(db, name, w);
}

pub proof fn lemma_keys_exact_pub(t: Tabs, name: Seq<u8>)
    requires tabs_typed(t),
    ensures keys_exact(gq(name), proj_all(xs(t), id16())),
{
    lemma_keys_exact(t, name);
}

pub proof fn lemma_group_row_pub(g: QuerySpec, x: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 2 }], k.len() == 1, gcount(g, x, k) > 0,
    ensures ({
        let w = full_row(g, x, k);
        &&& w.len() == 2
        &&& w[0] == k[0]
        &&& w[1] == (Val::Num { coeff: gsum(g, x, k, 0), scale: 2 })
    }),
{
    lemma_group_row(g, x, k);
}

} // verus!
