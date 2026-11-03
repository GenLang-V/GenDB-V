//! The statement's meaning, part 3: the two outcomes other than rows.
//! - a group count beyond int8 makes the body the SQL error 22003 (`lemma_body_count_err`: every group's COUNT and
//!   SUM succeed or fail with that code, and the overflowing group fails);
//! - an AVG division outside the executable domain puts the body outside `fits_query` (`lemma_body_capacity`): the
//!   first customer row's condition evaluates the subquery, whose AVG value is outside `fits_avg_value`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::limits::*;
use crate::spec::fns::div::num_div_fits;
use crate::spec::aggs::avg::*;
use crate::query::query_spec_at;
use crate::link::expr::ival;
use crate::link::query::*;
use crate::link::capacity::*;
use crate::bridge::collect::{lemma_collect_all, lemma_collect_first_err};
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::exec::aggs::avg::fits_avg_value;
use super::model::*;
use super::sql::*;
use super::group::*;

verus! {

// ------------------------------------------------------------------------------------------------ count beyond int8

/// The body is the GROUP BY of the derived table's (key, arguments) sequence.
proof fn lemma_body_groups(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db), ps_ok(ps), group_caps(g2(ps), ctab(db)), avg_val(db, ps) is Null || avg_val(db, ps) is Num,
    ensures ({
        let x = prows(db, ps, avg_val(db, ps), ctab(db));
        &&& keys_exact(gp(), x)
        &&& denote_body(db, query_spec_at(ps)) == group_rows(group_aggs(), qkeys(gp(), x),
                qrows(gp(), x).map_values(|r: Row| arg_vals(gp(), r)))
    }),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let avg = avg_val(db, ps);
    let x = prows(db, ps, avg, ctab(db));
    let g = gp();
    lemma_statement(ps);
    lemma_project(db, ps);
    lemma_prows_shape(db, ps, avg);
    lemma_group_premises(db, x);
    lemma_proj2(x);
    lemma_table_rows(db, project_q(ps), x, cols2(), g);
    let kept = keep_true(x, qual_truths(g, x));
    lemma_kept_rows(g, x, cols2());
    lemma_prepared(db, x, kept, cols2(), group_keys(), group_aggs(), g);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols2())), arg_vals(g, proj(kept[i], cols2()))));
    let q = qrows(g, x);
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, x));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= q.map_values(|r: Row| arg_vals(g, r)));
    lemma_groupby_unfold(db, project_q(ps), group_keys(), group_aggs(), kept, prep);
}

/// A group's aggregate row succeeds or fails with 22003; it fails when its count is beyond int8.
proof fn lemma_group_row_err(xs: Seq<Row>, k: Row)
    ensures ({
        let r = agg_row(group_aggs(), members(gp(), xs, k));
        &&& r is Ok || r == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange)
        &&& gcount(gp(), xs, k) > int8_max() ==> r == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange)
    }),
{
    let g = gp();
    let aggs = group_aggs();
    let e = SqlError::NumericValueOutOfRange;
    let ms = members(g, xs, k);
    lemma_members_col(g, xs, k, 0);
    lemma_members_col(g, xs, k, 1);
    let c0 = column(ms, 0);
    let c1 = column(ms, 1);
    lemma_count_value(Agg::CountStar, c0);
    let vr = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(ms, j)));
    assert(vr[0] == agg_value(Agg::CountStar, c0));
    assert(vr[1] == agg_value(aggs[1], c1));
    // SUM: NULL without members, else the exact sum or its range error.
    assert(vr[1] is Ok || vr[1] == Err::<Val, SqlError>(e)) by {
        assert(all_of_kind(NumKind::Numeric, c1));
    }
    if vr[0] is Err {
        lemma_collect_first_err(vr, 0);
    } else if vr[1] is Err {
        lemma_collect_first_err(vr, 1);
    } else {
        lemma_collect_all(vr, Seq::new(2, |j: int| vr[j]->Ok_0));
    }
}

/// GROUP BY with COUNT(*) and SUM: when some group's count is beyond int8, the outcome is error 22003.
proof fn lemma_groups_count_err(xs: Seq<Row>, k0: Row)
    requires
        keys_exact(gp(), xs),
        gcount(gp(), xs, k0) > int8_max(),
    ensures
        group_rows(group_aggs(), qkeys(gp(), xs), qrows(gp(), xs).map_values(|x: Row| arg_vals(gp(), x)))
            == Err::<Seq<Row>, SqlError>(SqlError::NumericValueOutOfRange),
{
    let g = gp();
    let aggs = group_aggs();
    let e = SqlError::NumericValueOutOfRange;
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    lemma_gkeys(g, xs);
    let grs = Seq::new(ds.len(), |gi: int|
        match agg_row(aggs, group_members(ks, avs, ds[gi])) {
            Ok(a) => Ok(ds[gi] + a),
            Err(err) => Err(err),
        });
    assert forall|gi: int| 0 <= gi < grs.len() implies #[trigger] grs[gi] is Ok || grs[gi] == Err::<Row, SqlError>(e) by {
        assert(pool.contains(ds[gi]));
        lemma_group_members(g, xs, ds[gi], pool);
        lemma_group_row_err(xs, ds[gi]);
    }
    assert(ds.contains(k0));
    let g0 = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k0;
    assert(grs[g0] == Err::<Row, SqlError>(e)) by {
        assert(pool.contains(k0));
        lemma_group_members(g, xs, k0, pool);
        lemma_group_row_err(xs, k0);
    }
    lemma_collect_uniform_err(grs, e, g0);
}

/// A group count beyond int8 makes the body the SQL error 22003.
pub proof fn lemma_body_count_err(db: Database, ps: Seq<Literal>, k0: Row)
    requires
        db_ok(db), ps_ok(ps), group_caps(g2(ps), ctab(db)), avg_val(db, ps) is Null || avg_val(db, ps) is Num,
        gcount(gc(db, ps, avg_val(db, ps)), ctab(db), k0) > int8_max(),
    ensures
        denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let avg = avg_val(db, ps);
    lemma_body_groups(db, ps);
    lemma_transfer(db, ps, avg, ctab(db), k0, 0);
    lemma_groups_count_err(prows(db, ps, avg, ctab(db)), k0);
}

// ------------------------------------------------------------------------------------------------ capacity

/// The AVG subquery under an outer customer row is outside `fits_query` when its division is.
proof fn lemma_sub_capacity(db: Database, r: Row, ps: Seq<Literal>)
    requires
        db_ok(db), crow_ok(r), ps_ok(ps),
        gcount(g2(ps), ctab(db), Seq::empty()) > 0,
        !num_div_fits(gsum(g2(ps), ctab(db), Seq::empty(), 0), 2, gcount(g2(ps), ctab(db), Seq::empty()) as int, 0),
    ensures !fits_query(db, r, sub_q(ps)),
{
    let g = g2(ps);
    let rows = ctab(db);
    let cols = id8();
    let filt = Query::Filter { pred: sub_pred(ps), input: Box::new(Query::Table(2)) };
    let aggs = seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(13) }];
    assert(sub_q(ps) == Query::Aggregate { aggs, input: Box::new(filt) });
    if fits_query(db, r, filt) {
        assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] rows[i]).len() == 8 by {
            assert(crow_ok(rows[i]));
        }
        lemma_proj_id8(rows);
        lemma_sub_filter(db, r, ps);
        let kept = keep_true(rows, qual_truths(g, rows));
        lemma_kept_rows(g, rows, cols);
        let args = Seq::new(kept.len(), |i: int| arg_vals(g, proj(kept[i], cols)));
        let pre = agg_args_results(db, r, kept, aggs);
        assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<Row, SqlError>(args[i]) by {
            assert(rows.contains(kept[i]));
            let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
            assert(crow_ok(rows[m]));
            assert(proj(kept[i], cols) =~= kept[i]);
            lemma_sub_arg(db, r, kept[i], ps);
        }
        lemma_collect_all(pre, args);
        let q = qrows(g, rows);
        assert(args =~= q.map_values(|x: Row| arg_vals(g, x)));
        lemma_scalar_members(g, rows);
        lemma_members_col(g, rows, Seq::empty(), 0);
        let vs = column(args, 0);
        assert(!fits_avg_value(NumKind::Numeric, vs));
        let rs = agg_value_results(aggs, args);
        let fs = agg_value_fs(aggs, args);
        assert(!fs[0]);
        lemma_fits_each_violation(rs, fs, 0);
        assert(!fits_agg_row(aggs, args));
    } else {
        lemma_first_input(db, r, sub_q(ps));
    }
}

/// The WHERE condition of a customer row is outside `fits_pred` when the subquery's division is.
proof fn lemma_where_capacity(db: Database, r: Row, ps: Seq<Literal>)
    requires
        db_ok(db), crow_ok(r), ps_ok(ps),
        gcount(g2(ps), ctab(db), Seq::empty()) > 0,
        !num_div_fits(gsum(g2(ps), ctab(db), Seq::empty(), 0), 2, gcount(g2(ps), ctab(db), Seq::empty()) as int, 0),
    ensures !fits_pred(db, r, where_pred(ps)),
{
    lemma_sub_capacity(db, r, ps);
    lemma_eval_in_list(db, r, 4, cphone(r), ps);
    crate::link::expr::lemma_expr_col(db, r, 5);
    assert(!fits_expr(db, r, Expr::Subquery(Box::new(sub_q(ps)))));
    assert(!fits_pred(db, r, gt_sub(ps)));
    let a = Pred::And(Box::new(in_list(4, ps)), Box::new(gt_sub(ps)));
    assert(!fits_pred(db, r, a));
}

/// An AVG division outside the executable domain puts the body outside `fits_query`.
pub proof fn lemma_body_capacity(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db), ps_ok(ps),
        gcount(g2(ps), ctab(db), Seq::empty()) > 0,
        !num_div_fits(gsum(g2(ps), ctab(db), Seq::empty(), 0), 2, gcount(g2(ps), ctab(db), Seq::empty()) as int, 0),
    ensures !fits_query(db, Seq::empty(), query_spec_at(ps).body),
{
    let rows = ctab(db);
    let ctx = Seq::<Val>::empty();
    lemma_statement(ps);
    assert(rows.len() > 0) by {
        if rows.len() == 0 {
            assert(rows =~= Seq::<Row>::empty());
        }
    }
    assert forall|k: int| 0 <= k < rows.len() implies !#[trigger] fits_pred(db, ctx + rows[k], where_pred(ps)) by {
        assert(ctx + rows[k] =~= rows[k]);
        assert(crow_ok(rows[k]));
        lemma_where_capacity(db, rows[k], ps);
    }
    assert(eval_query(db, ctx, Query::Table(2)) == Ok::<Relation, SqlError>(rows));
    lemma_filter_capacity(db, ctx, where_pred(ps), Box::new(Query::Table(2)), rows, 0);
    lemma_first_input(db, ctx, project_q(ps));
    lemma_first_input(db, ctx, body_q(ps));
}

} // verus!
