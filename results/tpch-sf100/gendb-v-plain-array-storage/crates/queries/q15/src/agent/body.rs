//! The statement body over one database: `SELECT s_suppkey, s_name, s_address, s_phone, total_revenue FROM supplier,
//! revenue0 WHERE s_suppkey = supplier_no AND total_revenue = (SELECT MAX(total_revenue) FROM revenue0)`.
//!
//! - Rows (`lemma_body_ok`): inside `group_caps`, the body is `body_rows(S, R, m)`: the rows of `S x R` (supplier
//!   rows times group rows, left-major) whose key equals the group key and whose SUM is the largest one `m`
//!   (`cond_of`), each projected onto the five output positions.
//! - SQL error (`lemma_body_err`): when `$1 + INTERVAL '3' MONTH` fails and `lineitem` has a row, the body is that
//!   error (the GROUP BY's WHERE fails on the first row).
//! - Capacity (`lemma_body_capacity`): a group whose absolute SUM mass leaves `i128` puts the body outside the
//!   capacity domain (the GROUP BY on the product's right side).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::distinct_rows;
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::expr::*;
use crate::link::join::{keep, lemma_keep_true_keep, lemma_keep_members, lemma_product_index};
use crate::link::capacity::{lemma_group_by_capacity, lemma_first_input, lemma_second_input, lemma_filter_err,
    aggs_ok_inside, lemma_sum_inside_ok, lemma_num_mass_uniform};
use crate::bridge::collect::lemma_collect_all;
use crate::agent::common::group_ctx::*;
use crate::agent::common::max_num::*;
use crate::agent::normal::*;
use crate::agent::bounds::{q_end_val, lemma_q_end_eval};
use crate::agent::groups::*;

verus! {

/// The outer WHERE on a `supplier x revenue0` row (9 values) when the subquery's value is the SUM `m`.
pub open spec fn cond_of(m: int) -> spec_fn(Row) -> bool {
    |pr: Row| pr[0] == pr[7] && pr[8] == Val::Num { coeff: m, scale: 4 }
}

/// The body's rows: the qualifying rows of `S x R`, projected onto the output positions.
pub open spec fn body_rows(srows: Seq<Row>, rr: Seq<Row>, m: int) -> Seq<Row> {
    keep(product_rows(srows, rr), cond_of(m)).map_values(|pr: Row| select(pr, out_cols()))
}

/// The outer WHERE on one row `s ++ r` of the product (`s` a supplier row, `r` a group row).
pub proof fn lemma_outer_pred(db: Database, lrows: Seq<Row>, srows: Seq<Row>, ps: Seq<Literal>, b: QBounds, t1: int,
    s: Row, r: Row)
    requires
        db_hyps(db, lrows, srows),
        bounds_ok(ps, b, t1),
        group_caps(q_spec(b), xs_of(lrows)),
        gkeys(q_spec(b), xs_of(lrows)).len() > 0,
        s.len() == 7, s[0] is Int,
        r.len() == 2, r[0] is Int, r[1] is Num, r[1]->Num_scale == 4,
    ensures
        eval_pred(db, s + r, body_pred(ps[0])) == Ok::<Truth, SqlError>(truth_of(cond_of(max_sum(q_spec(b), xs_of(lrows)))(s + r))),
{
    let pr = s + r;
    let m = max_sum(q_spec(b), xs_of(lrows));
    let mv = Val::Num { coeff: m, scale: 4 };
    lemma_sub_at(db, pr, lrows, srows, ps, b, t1);
    assert(eval_expr(db, pr, Expr::Subquery(Box::new(sub_query(ps[0])))) == Ok::<Val, SqlError>(mv));
    let (a, k) = (s[0]->Int_0, r[0]->Int_0);
    assert(pr[0] == s[0] && pr[7] == r[0] && pr[8] == r[1]);
    assert(eval_expr(db, pr, Expr::Col(0)) == Ok::<Val, SqlError>(pr[0]));
    assert(eval_expr(db, pr, Expr::Col(7)) == Ok::<Val, SqlError>(pr[7]));
    assert(eval_expr(db, pr, Expr::Col(8)) == Ok::<Val, SqlError>(pr[8]));
    lemma_compare_int(a, k);
    lemma_pred_cmp(db, pr, CmpOp::Eq, Expr::Col(0), Expr::Col(7), pr[0], pr[7], a, k);
    let v = r[1]->Num_coeff;
    lemma_compare_same_scale(v, m, 4);
    lemma_pred_cmp(db, pr, CmpOp::Eq, Expr::Col(8), Expr::Subquery(Box::new(sub_query(ps[0]))), pr[8], mv, v, m);
    lemma_pred_and(db, pr,
        Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(7) },
        Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Subquery(Box::new(sub_query(ps[0]))) },
        a == k, v == m);
}

/// A position below `a * b` is `i * b + j` with `i < a`, `j < b`.
pub proof fn lemma_split_index(idx: int, a: int, b: int)
    requires 0 <= idx < a * b, b > 0,
    ensures
        0 <= idx / b < a,
        0 <= idx % b < b,
        idx == (idx / b) * b + idx % b,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(idx, b);
    vstd::arithmetic::div_mod::lemma_mod_bound(idx, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(idx, b);
    let i = idx / b;
    assert(i * b == b * i) by (nonlinear_arith);
    assert(i < a) by (nonlinear_arith) requires idx == b * i + idx % b, idx % b >= 0, idx < a * b, b > 0;
}

/// Product row `idx` of `S x R`: 9 values, and the outer WHERE on it is `cond_of(m)`.
pub proof fn lemma_product_row(db: Database, lrows: Seq<Row>, srows: Seq<Row>, ps: Seq<Literal>, b: QBounds, t1: int, idx: int)
    requires
        db_hyps(db, lrows, srows),
        bounds_ok(ps, b, t1),
        group_caps(q_spec(b), xs_of(lrows)),
        0 <= idx < product_rows(srows, grp_rows(q_spec(b), xs_of(lrows))).len(),
    ensures ({
        let p = product_rows(srows, grp_rows(q_spec(b), xs_of(lrows)));
        &&& p[idx].len() == 9
        &&& eval_pred(db, Seq::<Val>::empty() + p[idx], body_pred(ps[0]))
                == Ok::<Truth, SqlError>(truth_of(cond_of(max_sum(q_spec(b), xs_of(lrows)))(p[idx])))
    }),
{
    let rr = grp_rows(q_spec(b), xs_of(lrows));
    let p = product_rows(srows, rr);
    lemma_product_index(srows, rr);
    assert(rr.len() > 0) by {
        if rr.len() == 0 {
            assert(srows.len() * rr.len() == 0) by (nonlinear_arith) requires rr.len() == 0;
        }
    }
    lemma_split_index(idx, srows.len() as int, rr.len() as int);
    let (i, j) = (idx / rr.len() as int, idx % rr.len() as int);
    assert(p[i * rr.len() + j] == srows[i] + rr[j]);
    lemma_grp_row(lrows, b, j);
    assert(Seq::<Val>::empty() + p[idx] =~= p[idx]);
    lemma_outer_pred(db, lrows, srows, ps, b, t1, srows[i], rr[j]);
}

/// The outer WHERE keeps exactly the product rows satisfying `cond_of(m)`.
pub proof fn lemma_filter_ok(db: Database, lrows: Seq<Row>, srows: Seq<Row>, ps: Seq<Literal>, b: QBounds, t1: int)
    requires
        db_hyps(db, lrows, srows),
        bounds_ok(ps, b, t1),
        group_caps(q_spec(b), xs_of(lrows)),
    ensures ({
        let p = product_rows(srows, grp_rows(q_spec(b), xs_of(lrows)));
        let f = cond_of(max_sum(q_spec(b), xs_of(lrows)));
        &&& eval_query(db, Seq::empty(), body_filter(ps[0])) == Ok::<Relation, SqlError>(keep(p, f))
        &&& forall|i: int| 0 <= i < keep(p, f).len() ==> (#[trigger] keep(p, f)[i]).len() == 9
    }),
{
    hide(eval_pred);
    let g = q_spec(b);
    let xs = xs_of(lrows);
    let ctx = Seq::<Val>::empty();
    let rr = grp_rows(g, xs);
    let f = cond_of(max_sum(g, xs));
    let p = product_rows(srows, rr);
    let pred = body_pred(ps[0]);
    lemma_group_at(db, ctx, lrows, srows, ps, b, t1);
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(srows));
    assert(eval_query(db, ctx, body_product(ps[0])) == Ok::<Relation, SqlError>(p));
    let truths = Seq::new(p.len(), |i: int| truth_of(f(p[i])));
    let frs = filter_results(db, ctx, p, pred);
    assert forall|idx: int| 0 <= idx < p.len() implies #[trigger] frs[idx] == Ok::<Truth, SqlError>(truths[idx]) && p[idx].len() == 9 by {
        lemma_product_row(db, lrows, srows, ps, b, t1, idx);
    }
    lemma_eval_filter(db, ctx, pred, Box::new(body_product(ps[0])));
    lemma_collect_all(frs, truths);
    lemma_keep_true_keep(p, truths, f);
    lemma_keep_members(p, f);
    assert forall|i: int| 0 <= i < keep(p, f).len() implies (#[trigger] keep(p, f)[i]).len() == 9 by {
        assert(p.contains(keep(p, f)[i]));
        let idx = choose|idx: int| 0 <= idx < p.len() && p[idx] == keep(p, f)[i];
        assert(frs[idx] == Ok::<Truth, SqlError>(truths[idx]) && p[idx].len() == 9);
    }
}

/// Inside `group_caps`, the body is `body_rows` of the supplier rows, the group rows and the largest SUM.
pub proof fn lemma_body_ok(db: Database, lrows: Seq<Row>, srows: Seq<Row>, ps: Seq<Literal>, b: QBounds, t1: int)
    requires
        db_hyps(db, lrows, srows),
        bounds_ok(ps, b, t1),
        group_caps(q_spec(b), xs_of(lrows)),
    ensures
        eval_query(db, Seq::empty(), ast_body(ps[0]))
            == Ok::<Relation, SqlError>(body_rows(srows, grp_rows(q_spec(b), xs_of(lrows)), max_sum(q_spec(b), xs_of(lrows)))),
{
    hide(eval_query);
    let p = product_rows(srows, grp_rows(q_spec(b), xs_of(lrows)));
    let f = cond_of(max_sum(q_spec(b), xs_of(lrows)));
    lemma_filter_ok(db, lrows, srows, ps, b, t1);
    lemma_project_cols(db, body_filter(ps[0]), keep(p, f), out_cols(), 9);
}

// ------------------------------------------------------------------------------------------------ the SQL error

/// On a table row, the GROUP BY's WHERE fails with the error of `$1 + INTERVAL '3' MONTH`.
pub proof fn lemma_row_err(db: Database, r: Row, ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        li_row_ok(r),
        ps.len() == 1,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd)),
        q_end_val(pd) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, r, p_date(0, ps[0])) == Err::<Truth, SqlError>(e),
{
    let d = r[10]->Date_0;
    lemma_q_end_eval(db, r, ps[0], pd);
    assert(eval_expr(db, r, Expr::Col(10)) == Ok::<Val, SqlError>(r[10]));
    assert(eval_expr(db, r, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Date(pd)));
    lemma_compare_date(d, pd);
    lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(10), Expr::Lit(ps[0]), r[10], Val::Date(pd), d, pd);
    assert(eval_pred(db, r, p_lt(0, ps[0])) == Err::<Truth, SqlError>(e));
}

/// A failing `$1 + INTERVAL '3' MONTH` over a non-empty `lineitem`: the body is that error.
pub proof fn lemma_body_err(db: Database, lrows: Seq<Row>, srows: Seq<Row>, ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        db_hyps(db, lrows, srows),
        lrows.len() > 0,
        ps.len() == 1,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd)),
        q_end_val(pd) == Err::<Val, SqlError>(e),
    ensures eval_query(db, Seq::empty(), ast_body(ps[0])) == Err::<Relation, SqlError>(e),
{
    let ctx = Seq::<Val>::empty();
    let pred = p_date(0, ps[0]);
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(lrows));
    assert forall|k: int| 0 <= k < lrows.len() implies #[trigger] eval_pred(db, ctx + lrows[k], pred) == Err::<Truth, SqlError>(e) by {
        assert(ctx + lrows[k] =~= lrows[k]);
        lemma_row_err(db, lrows[k], ps, pd, e);
    }
    assert(eval_pred(db, ctx + lrows[0], pred) == Err::<Truth, SqlError>(e));
    lemma_filter_err(db, ctx, pred, Box::new(Query::Table(0)), lrows, e, 0);
    lemma_first_input(db, ctx, g_query(0, ps[0]));
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(srows));
    lemma_second_input(db, ctx, body_product(ps[0]), srows);
    lemma_first_input(db, ctx, body_filter(ps[0]));
    lemma_first_input(db, ctx, ast_body(ps[0]));
}

// ------------------------------------------------------------------------------------------------ capacity

/// The absolute mass of a group's argument column (at scale 4) is its `gabs`.
pub proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 4 }],
    ensures num_mass_at(column(members(g, xs, k), 0), 4) == gabs(g, xs, k, 0),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        lemma_members_mass(g, xi, k);
        let m = members(g, xs, k);
        let mi = members(g, xi, k);
        if hit(g, xs.last(), k) {
            let av = arg_vals(g, xs.last());
            assert(m == mi.push(av));
            assert(column(m, 0) =~= column(mi, 0).push(av[0]));
            assert(av[0] == Val::Num { coeff: (g.arg)(0, xs.last()), scale: 4 });
            assert(column(m, 0).drop_last() =~= column(mi, 0));
            assert(pow10(0) == 1) by (compute);
        } else {
            assert(m == mi);
        }
    } else {
        assert(column(members(g, xs, k), 0) =~= Seq::<Val>::empty());
    }
}

/// Every value of a group's argument column is numeric at scale 4.
pub proof fn lemma_members_scale(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 4 }],
    ensures forall|i: int| 0 <= i < column(members(g, xs, k), 0).len() ==>
        (#[trigger] column(members(g, xs, k), 0)[i]) is Num && column(members(g, xs, k), 0)[i]->Num_scale == 4,
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        lemma_members_scale(g, xi, k);
        let m = members(g, xs, k);
        let mi = members(g, xi, k);
        if hit(g, xs.last(), k) {
            let av = arg_vals(g, xs.last());
            assert(m == mi.push(av));
            assert(column(m, 0) =~= column(mi, 0).push(av[0]));
        } else {
            assert(m == mi);
        }
    }
}

/// A group `k` whose absolute SUM mass exceeds `i128::MAX` puts the body outside its capacity domain.
pub proof fn lemma_body_capacity(db: Database, lrows: Seq<Row>, srows: Seq<Row>, ps: Seq<Literal>, b: QBounds, t1: int, k: Row)
    requires
        db_hyps(db, lrows, srows),
        bounds_ok(ps, b, t1),
        gabs(q_spec(b), xs_of(lrows), k, 0) > i128_max(),
    ensures !fits_query(db, Seq::empty(), ast_body(ps[0])),
{
    let g = q_spec(b);
    let xs = xs_of(lrows);
    let cols = src_cols();
    let ctx = Seq::<Val>::empty();
    let keys = g_keys(0);
    let aggs = g_aggs(0);
    if gcount(g, xs, k) == 0 {
        lemma_zero_count(g, xs, k, 0);
    }
    lemma_gkeys(g, xs);
    // the WHERE's rows and the GROUP BY's prepared inputs
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(lrows));
    lemma_agree_at(db, ctx, lrows, ps, b, t1);
    lemma_filter_rows_at(db, ctx, Query::Table(0), lrows, cols, p_date(0, ps[0]), g);
    let kept = keep_true(lrows, qual_truths(g, xs));
    lemma_kept_rows(g, lrows, cols);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert(ks.len() == kept.len() && args.len() == kept.len());
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, ctx + kept[i], keys, aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(lrows.contains(kept[i]) && (g.qual)(proj(kept[i], cols)));
        let r = choose|r: int| 0 <= r < lrows.len() && lrows[r] == kept[i];
        assert(eval_exprs(db, ctx + lrows[r], keys) == Ok::<Row, SqlError>((g.key)(proj(lrows[r], cols))));
        assert(agg_args(db, ctx + lrows[r], aggs) == Ok::<Row, SqlError>(arg_vals(g, proj(lrows[r], cols))));
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
    }
    // the canonical groups are the normal form's
    let pool = key_pool(g, xs);
    lemma_keys_exact(lrows, b);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {}
    lemma_distinct_gkeys(g, xs, pool);
    assert(gkeys(g, xs).contains(k));
    let gi = choose|gi: int| 0 <= gi < gkeys(g, xs).len() && gkeys(g, xs)[gi] == k;
    assert(distinct_rows(ks)[gi] == k);
    assert(pool.contains(k)) by {
        assert(pool.contains(gkeys(g, xs)[gi]));
    }
    // group `k` is outside its capacity condition
    lemma_group_members(g, xs, k, pool);
    let vs = column(members(g, xs, k), 0);
    lemma_members_col(g, xs, k, 0);
    lemma_members_mass(g, xs, k);
    lemma_members_scale(g, xs, k);
    assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == 4) by {}
    lemma_num_mass_uniform(vs, 4);
    assert(vs.len() > 0);
    assert(vs[0] is Num);
    assert(num_max_scale(vs) == 4);
    assert(!fits_agg_value(aggs[0], column(group_members(ks, args, distinct_rows(ks)[gi]), 0)));
    // every group's SUM succeeds inside its condition
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(aggs, group_members(ks, args, distinct_rows(ks)[h])) by {
        let kh = gkeys(g, xs)[h];
        assert(pool.contains(kh));
        lemma_group_members(g, xs, kh, pool);
        lemma_members_col(g, xs, kh, 0);
        let vh = column(members(g, xs, kh), 0);
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(group_members(ks, args, distinct_rows(ks)[h]), j))
            implies agg_value(aggs[j], column(group_members(ks, args, distinct_rows(ks)[h]), j)) is Ok by {
            assert(j == 0);
            lemma_sum_inside_ok(NumKind::Numeric, e_rev(0), vh);
        }
    }
    lemma_group_by_capacity(db, ctx, keys, aggs, Box::new(g_input(0, ps[0])), kept, ks, args, gi, 0);
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(srows));
    lemma_second_input(db, ctx, body_product(ps[0]), srows);
    lemma_first_input(db, ctx, body_filter(ps[0]));
    lemma_first_input(db, ctx, ast_body(ps[0]));
}

} // verus!
