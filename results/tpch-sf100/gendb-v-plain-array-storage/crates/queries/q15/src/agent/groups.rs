//! `revenue0` and `SELECT MAX(total_revenue) FROM revenue0` over one database.
//!
//! With `L` the `lineitem` rows and `xs = proj_all(L, src_cols())` their projections, the GROUP BY evaluates under
//! every outer context to `grp_rows(g, xs)`: one row `[l_suppkey, SUM]` per group key, in first-occurrence order
//! (`lemma_group_at`). The subquery, evaluated under a 9-value row, is one row holding the largest group SUM at
//! scale 4, `max_sum(g, xs)` (`lemma_sub_at`). Both need the groups inside `i128` (`group_caps`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::aggs::minmax::max_value;
use crate::exec::relational::domain::{lemma_eval_aggregate, agg_args_results, lemma_agg_args};
use crate::link::query::*;
use crate::bridge::collect::lemma_collect_all;
use crate::agent::common::group_ctx::*;
use crate::agent::common::max_num::*;
use crate::agent::normal::*;

verus! {

/// Every `supplier` row has its 7 values, the key an integer.
pub open spec fn supp_rows_ok(srows: Seq<Row>) -> bool {
    forall|j: int| 0 <= j < srows.len() ==> (#[trigger] srows[j]).len() == 7 && srows[j][0] is Int
}

/// What the statement's meaning needs of one database: tables 0 and 5 are `L` and `S`, with well-formed rows.
pub open spec fn db_hyps(db: Database, lrows: Seq<Row>, srows: Seq<Row>) -> bool {
    &&& db.tables.len() == 8
    &&& db.tables[0] == lrows
    &&& db.tables[5] == srows
    &&& li_rows_ok(lrows)
    &&& supp_rows_ok(srows)
}

/// The projected `lineitem` rows the normal form reads.
pub open spec fn xs_of(lrows: Seq<Row>) -> Seq<Row> {
    proj_all(lrows, src_cols())
}

/// The GROUP BY's rows: `key ++ [SUM]` per group key, first-occurrence order.
pub open spec fn grp_rows(g: QuerySpec, xs: Seq<Row>) -> Seq<Row> {
    gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k))
}

/// The groups' SUM values, in group order.
pub open spec fn sum_vals(g: QuerySpec, xs: Seq<Row>) -> Seq<Val> {
    gkeys(g, xs).map_values(|k: Row| Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 })
}

/// The largest group SUM (coefficient at scale 4; 0 without groups).
pub open spec fn max_sum(g: QuerySpec, xs: Seq<Row>) -> int {
    coeff_max(sum_vals(g, xs))
}

/// A group key is the one-integer key of a qualifying row, with a non-zero count.
pub proof fn lemma_gkey_shape(lrows: Seq<Row>, b: QBounds, k: Row)
    requires li_rows_ok(lrows), gkeys(q_spec(b), xs_of(lrows)).contains(k),
    ensures k.len() == 1, k[0] is Int, gcount(q_spec(b), xs_of(lrows), k) > 0, k == seq![k[0]],
{
    let g = q_spec(b);
    let xs = xs_of(lrows);
    lemma_gkeys_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    assert(xs[m] == proj(lrows[m], src_cols()));
    lemma_proj_row(lrows[m]);
    assert(k == seq![xs[m][0]]);
}

/// Group row `i` is `[key, SUM]` with an integer key.
pub proof fn lemma_grp_row(lrows: Seq<Row>, b: QBounds, i: int)
    requires li_rows_ok(lrows), 0 <= i < gkeys(q_spec(b), xs_of(lrows)).len(),
    ensures ({
        let g = q_spec(b);
        let xs = xs_of(lrows);
        let k = gkeys(g, xs)[i];
        &&& grp_rows(g, xs)[i] == seq![k[0], Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 }]
        &&& grp_rows(g, xs)[i].len() == 2
        &&& k[0] is Int
        &&& grp_rows(g, xs)[i][1] == sum_vals(g, xs)[i]
    }),
{
    let g = q_spec(b);
    let xs = xs_of(lrows);
    let k = gkeys(g, xs)[i];
    assert(gkeys(g, xs).contains(k));
    lemma_gkey_shape(lrows, b, k);
    assert(agg_outs(g, xs, k) =~= seq![Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 }]);
    assert(full_row(g, xs, k) =~= seq![k[0], Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 }]);
}

/// `revenue0` under any outer context: the group rows.
pub proof fn lemma_group_at(db: Database, ctx: Row, lrows: Seq<Row>, srows: Seq<Row>, ps: Seq<Literal>, b: QBounds, t1: int)
    requires
        db_hyps(db, lrows, srows),
        bounds_ok(ps, b, t1),
        group_caps(q_spec(b), xs_of(lrows)),
    ensures eval_query(db, ctx, g_query(ctx.len(), ps[0])) == Ok::<Relation, SqlError>(grp_rows(q_spec(b), xs_of(lrows))),
{
    let g = q_spec(b);
    let o = ctx.len();
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(lrows));
    lemma_agree_at(db, ctx, lrows, ps, b, t1);
    lemma_filter_rows_at(db, ctx, Query::Table(0), lrows, src_cols(), p_date(o, ps[0]), g);
    lemma_aggs_match(o, b);
    lemma_keys_exact(lrows, b);
    lemma_group_query_at(db, ctx, lrows, src_cols(), g_input(o, ps[0]), g_keys(o), g_aggs(o), g);
}

/// The MAX argument of group row `r` under a 9-value context: its SUM.
pub proof fn lemma_max_arg(db: Database, ctx: Row, r: Row)
    requires ctx.len() == 9, r.len() == 2,
    ensures agg_args(db, ctx + r, seq![Agg::Max(Expr::Col(10))]) == Ok::<Row, SqlError>(seq![r[1]]),
{
    let env = ctx + r;
    let aggs = seq![Agg::Max(Expr::Col(10))];
    lemma_agg_args(db, env, aggs);
    lemma_agg_arg_results_index(db, env, aggs);
    assert(env[10] == r[1]);
    assert(agg_arg(db, env, aggs[0]) == Ok::<Val, SqlError>(r[1]));
    lemma_collect_all(agg_arg_results(db, env, aggs), seq![r[1]]);
}

/// The subquery under a 9-value context: one row with the largest group SUM.
pub proof fn lemma_sub_at(db: Database, ctx: Row, lrows: Seq<Row>, srows: Seq<Row>, ps: Seq<Literal>, b: QBounds, t1: int)
    requires
        db_hyps(db, lrows, srows),
        bounds_ok(ps, b, t1),
        group_caps(q_spec(b), xs_of(lrows)),
        ctx.len() == 9,
        gkeys(q_spec(b), xs_of(lrows)).len() > 0,
    ensures
        eval_query(db, ctx, sub_query(ps[0]))
            == Ok::<Relation, SqlError>(seq![seq![Val::Num { coeff: max_sum(q_spec(b), xs_of(lrows)), scale: 4 }]]),
        is_max_of(sum_vals(q_spec(b), xs_of(lrows)), max_sum(q_spec(b), xs_of(lrows))),
{
    hide(agg_args);
    let g = q_spec(b);
    let xs = xs_of(lrows);
    let rr = grp_rows(g, xs);
    let vs = sum_vals(g, xs);
    let aggs = seq![Agg::Max(Expr::Col(10))];
    lemma_group_at(db, ctx, lrows, srows, ps, b, t1);
    lemma_eval_aggregate(db, ctx, aggs, Box::new(g_query(9, ps[0])));
    // per group row, its argument row is `[SUM]`
    let args = rr.map_values(|r: Row| seq![r[1]]);
    let ars = agg_args_results(db, ctx, rr, aggs);
    assert forall|i: int| 0 <= i < ars.len() implies #[trigger] ars[i] == Ok::<Row, SqlError>(args[i]) by {
        lemma_grp_row(lrows, b, i);
        lemma_max_arg(db, ctx, rr[i]);
    }
    lemma_collect_all(ars, args);
    // the argument column is the groups' SUM values, all numeric at scale 4
    assert(column(args, 0) =~= vs) by {
        assert forall|i: int| 0 <= i < vs.len() implies #[trigger] column(args, 0)[i] == vs[i] by {
            lemma_grp_row(lrows, b, i);
        }
    }
    assert(all_num_at(vs, 4));
    lemma_max_value_num(vs, 4);
    let mv = Val::Num { coeff: max_sum(g, xs), scale: 4 };
    assert(agg_value(aggs[0], column(args, 0)) == Ok::<Val, SqlError>(mv));
    let avs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(args, j)));
    lemma_collect_all(avs, seq![mv]);
    assert(agg_row(aggs, args) == Ok::<Row, SqlError>(seq![mv]));
}

} // verus!
