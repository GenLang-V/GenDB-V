//! The statement body of Q1 (`GROUP BY` over `WHERE` over `lineitem`) in terms of the normal form
//! (`agent::normal`): its rows when every group is inside the capacity domain (`lemma_body_ok`), `Capacity` from a
//! per-row overflow of the charge product (`lemma_body_row_capacity`) or from a group's SUM/AVG domain
//! (`lemma_body_group_capacity`), and the exact SQL error of a COUNT beyond int8 (`lemma_body_count_error`).
//!
//! Every lemma takes the table rows `rows = db.tables[0]` (all `table_row_ok`) and the parameter literal `p` with
//! its day number `pd`; `xs = proj_all(rows, src_cols())` are the projected rows the normal form reads.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::limits::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::num_div_fits;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::expr::{ival, i128_max};
use crate::link::capacity::*;
use crate::bridge::collect::lemma_collect_all;
use crate::agent::normal::*;

verus! {

/// Every row of the table is a well-formed `lineitem` row on the columns Q1 reads.
pub open spec fn rows_ok(rows: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> table_row_ok(#[trigger] rows[i])
}

/// The rows the WHERE keeps (the GROUP BY's input), under the normal form's condition.
pub open spec fn kept_rows(pd: int, rows: Seq<Row>) -> Seq<Row> {
    keep_true(rows, qual_truths(q1_spec(pd), proj_all(rows, src_cols())))
}

/// Hypotheses shared by the lemmas: the table, its well-formed rows and the parameter.
pub open spec fn body_hyps(db: Database, rows: Seq<Row>, p: Literal, pd: int) -> bool {
    &&& db.tables.len() > 0
    &&& rows == db.tables[0]
    &&& rows_ok(rows)
    &&& lit_val(p) == Ok::<Val, SqlError>(Val::Date(pd))
}

/// Projected source rows are well formed.
pub proof fn lemma_xs_ok(rows: Seq<Row>)
    requires rows_ok(rows),
    ensures
        proj_all(rows, src_cols()).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] proj_all(rows, src_cols())[i] == proj(rows[i], src_cols()),
        forall|i: int| 0 <= i < rows.len() ==> src_row_ok(#[trigger] proj_all(rows, src_cols())[i]),
{
    let xs = proj_all(rows, src_cols());
    assert forall|i: int| 0 <= i < rows.len() implies src_row_ok(#[trigger] xs[i]) by {
        assert(xs[i] == proj(rows[i], src_cols()));
        lemma_proj_row_ok(rows[i]);
    }
}

/// The WHERE of the body evaluates to the kept rows; the kept rows are table rows that qualify, and project to the
/// normal form's qualifying rows.
pub proof fn lemma_input(db: Database, rows: Seq<Row>, p: Literal, pd: int)
    requires body_hyps(db, rows, p, pd),
    ensures ({
        let g = q1_spec(pd);
        let xs = proj_all(rows, src_cols());
        let kept = kept_rows(pd, rows);
        &&& eval_query(db, Seq::empty(), ast_input(p)) == Ok::<Relation, SqlError>(kept)
        &&& kept.len() == qrows(g, xs).len()
        &&& forall|i: int| 0 <= i < kept.len() ==> rows.contains(#[trigger] kept[i]) && (g.qual)(proj(kept[i], src_cols()))
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] proj(kept[i], src_cols()) == qrows(g, xs)[i]
        &&& forall|i: int| 0 <= i < kept.len() ==> table_row_ok(#[trigger] kept[i])
    }),
{
    hide(eval_pred);
    let g = q1_spec(pd);
    let cols = src_cols();
    let xs = proj_all(rows, cols);
    let kept = kept_rows(pd, rows);
    assert(eval_query(db, Seq::empty(), Query::Table(0)) == Ok::<Relation, SqlError>(rows));
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], ast_pred(p)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols)))) by {
        lemma_pred_row(db, rows[i], p, pd);
    }
    assert(pred_agrees(db, rows, cols, ast_pred(p), g));
    lemma_filter_rows(db, Query::Table(0), rows, cols, ast_pred(p), g);
    lemma_kept_rows(g, rows, cols);
    assert(proj_all(kept, cols).len() == kept.len());
    assert forall|i: int| 0 <= i < kept.len() implies table_row_ok(#[trigger] kept[i]) by {
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(table_row_ok(rows[m]));
    }
}

/// Per-row agreement of the keys and aggregate arguments on every table row.
pub proof fn lemma_agree(db: Database, rows: Seq<Row>, pd: int)
    requires rows_ok(rows),
    ensures
        keys_agree(db, rows, src_cols(), ast_keys(), q1_spec(pd)),
        args_agree(db, rows, src_cols(), ast_aggs(), q1_spec(pd)),
{
    hide(eval_exprs);
    hide(agg_args);
    let g = q1_spec(pd);
    let cols = src_cols();
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        eval_exprs(db, rows[i], ast_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], cols))) by {
        lemma_keys_row(db, rows[i]);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        agg_args(db, rows[i], ast_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], cols))) by {
        lemma_args_row(db, rows[i], pd);
    }
}

/// Inside `group_caps` the body is the normal form's result rows.
pub proof fn lemma_body_ok(db: Database, rows: Seq<Row>, p: Literal, pd: int)
    requires
        body_hyps(db, rows, p, pd),
        group_caps(q1_spec(pd), proj_all(rows, src_cols())),
    ensures
        eval_query(db, Seq::empty(), ast_body(p)) == Ok::<Relation, SqlError>(result_rows(q1_spec(pd), proj_all(rows, src_cols()))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let g = q1_spec(pd);
    let cols = src_cols();
    let xs = proj_all(rows, cols);
    lemma_input(db, rows, p, pd);
    lemma_agree(db, rows, pd);
    lemma_aggs_match(pd);
    lemma_xs_ok(rows);
    lemma_keys_exact(pd, xs);
    lemma_group_query(db, rows, cols, ast_input(p), ast_keys(), ast_aggs(), g);
    let ks = gkeys(g, xs);
    let fulls = ks.map_values(|k: Row| full_row(g, xs, k));
    let outs = ks.map_values(|k: Row| out_row(g, xs, k));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] fulls[i] == outs[i] by {
        let k = ks[i];
        assert(ks.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
        assert(k == q1_key(xs[m]));
        assert(k.len() == 2);
        lemma_select_identity(full_row(g, xs, k), q1_outs());
    }
    assert(fulls =~= outs);
    assert(ast_body(p) == Query::GroupBy { keys: ast_keys(), aggs: ast_aggs(), input: Box::new(ast_input(p)) });
}

// ------------------------------------------------------------------------------------------------ capacity: one row

/// A table row that qualifies is one of the kept rows.
pub proof fn lemma_keep_true_has(rows: Seq<Row>, truths: Seq<Truth>, m: int)
    requires rows.len() == truths.len(), 0 <= m < rows.len(), truths[m] is True,
    ensures exists|i: int| 0 <= i < keep_true(rows, truths).len() && #[trigger] keep_true(rows, truths)[i] == rows[m],
    decreases rows.len(),
{
    let init = keep_true(rows.drop_last(), truths.drop_last());
    if m == rows.len() - 1 {
        assert(truths.last() is True);
        assert(keep_true(rows, truths) == init.push(rows.last()));
        assert(keep_true(rows, truths)[init.len() as int] == rows[m]);
    } else {
        lemma_keep_true_has(rows.drop_last(), truths.drop_last(), m);
        let i = choose|i: int| 0 <= i < init.len() && #[trigger] init[i] == rows.drop_last()[m];
        if truths.last() is True {
            assert(keep_true(rows, truths)[i] == init[i]);
        } else {
            assert(keep_true(rows, truths) == init);
        }
    }
}

/// The charge of a table row outside `i128` puts its aggregate arguments outside their domain.
pub proof fn lemma_row_args_outside(db: Database, r: Row, pd: int)
    requires
        table_row_ok(r),
        !crate::link::expr::fits_i128(charge(proj(r, src_cols()))),
    ensures !fits_agg_args(db, r, ast_aggs()),
{
    hide(agg_arg_results);
    hide(row_arg_vals);
    let x = proj(r, src_cols());
    let aggs = ast_aggs();
    lemma_args_row_pointwise(db, r);
    lemma_agg_args(db, r, aggs);
    lemma_agg_arg_fs_index(db, r, aggs);
    lemma_ast_aggs();
    let rs = agg_arg_results(db, r, aggs);
    let fs = agg_arg_fs(db, r, aggs);
    assert(ok_before(rs, 3)) by {
        assert forall|j: int| 0 <= j < 3 implies #[trigger] rs[j] is Ok by {}
    }
    lemma_eval_disc_price(db, r);
    lemma_eval_charge(db, r);
    assert(fs[3] == fits_agg_arg(db, r, aggs[3]));
    assert(fits_agg_arg(db, r, aggs[3]) == fits_expr(db, r, e_charge()));
    assert(charge(x) == disc_price(x) * (100 + ival(r[7])));
    assert(!arith_fits(ArithOp::Mul, NumKind::Numeric, Val::Num { coeff: disc_price(x), scale: 4 }, Val::Num { coeff: 100 + ival(r[7]), scale: 2 }));
    assert(!fits_expr(db, r, e_charge()));
    assert(!fs[3]);
}

/// A qualifying row whose charge overflows `i128` puts the statement outside the capacity domain.
pub proof fn lemma_body_row_capacity(db: Database, rows: Seq<Row>, p: Literal, pd: int, m: int)
    requires
        body_hyps(db, rows, p, pd),
        0 <= m < rows.len(),
        q1_qual(pd, proj(rows[m], src_cols())),
        !crate::link::expr::fits_i128(charge(proj(rows[m], src_cols()))),
    ensures !fits_query(db, Seq::empty(), ast_body(p)),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    hide(fits_exprs);
    hide(fits_agg_args);
    hide(group_input);
    hide(fits_group_input);
    let g = q1_spec(pd);
    let cols = src_cols();
    let xs = proj_all(rows, cols);
    let kept = kept_rows(pd, rows);
    let ctx = Seq::<Val>::empty();
    lemma_input(db, rows, p, pd);
    lemma_xs_ok(rows);
    let truths = qual_truths(g, xs);
    assert(truths[m] is True);
    lemma_keep_true_has(rows, truths, m);
    let i = choose|i: int| 0 <= i < kept.len() && #[trigger] kept[i] == rows[m];
    let keys = ast_keys();
    let aggs = ast_aggs();
    let rs = group_input_results(db, ctx, kept, keys, aggs);
    let fs = group_input_fs(db, ctx, kept, keys, aggs);
    assert forall|k: int| 0 <= k < fs.len() && #[trigger] fs[k] implies rs[k] is Ok by {
        lemma_group_input_results(db, ctx, kept, keys, aggs, k);
        assert(ctx + kept[k] =~= kept[k]);
        lemma_keys_row(db, kept[k]);
        lemma_args_row(db, kept[k], pd);
        lemma_group_input_unfold(db, kept[k], keys, aggs);
    }
    assert(!fs[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(fs[i] == fits_group_input(db, kept[i], keys, aggs));
        lemma_keys_row(db, kept[i]);
        lemma_row_args_outside(db, kept[i], pd);
        lemma_group_input_unfold(db, kept[i], keys, aggs);
    }
    lemma_fits_each_violation(rs, fs, i);
    lemma_fits_group_by(db, ctx, keys, aggs, Box::new(ast_input(p)));
}

// ------------------------------------------------------------------------------------------------ groups

/// The members of every group: their argument column `j` is numeric at the aggregate's scale, and its absolute
/// mass at that scale is `gabs`.
pub proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row, j: int, scale: nat)
    requires
        0 <= j < g.aggs.len(),
        g.aggs[j] == (AggKind::Sum { scale }) || g.aggs[j] == (AggKind::Avg { scale }),
    ensures ({
        let vs = column(members(g, xs, k), j);
        &&& forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i] matches Val::Num { coeff, scale: s } ==> s == scale)
        &&& forall|i: int| 0 <= i < vs.len() ==> #[trigger] vs[i] is Num
        &&& num_mass_at(vs, scale) == gabs(g, xs, k, j)
    }),
    decreases xs.len(),
{
    let vs = column(members(g, xs, k), j);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(g, xi, k, j, scale);
        let vsi = column(members(g, xi, k), j);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(arg_vals(g, x)[j]));
            assert(vs.drop_last() =~= vsi);
            assert(arg_vals(g, x)[j] == Val::Num { coeff: (g.arg)(j, x), scale });
            assert((scale - scale) as nat == 0nat);
            assert(pow10(0) == 1);
            assert(abs((g.arg)(j, x)) * pow10(0) == abs((g.arg)(j, x)));
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// The SUM/AVG capacity condition of a group's argument column is its `gabs` bound.
pub proof fn lemma_members_mass_fits(g: QuerySpec, xs: Seq<Row>, k: Row, j: int, scale: nat)
    requires
        0 <= j < g.aggs.len(),
        g.aggs[j] == (AggKind::Sum { scale }) || g.aggs[j] == (AggKind::Avg { scale }),
        gcount(g, xs, k) > 0,
    ensures sum_mass_fits(NumKind::Numeric, column(members(g, xs, k), j)) == (gabs(g, xs, k, j) <= i128_max()),
{
    let vs = column(members(g, xs, k), j);
    lemma_members_mass(g, xs, k, j, scale);
    lemma_members_col(g, xs, k, j);
    lemma_num_mass_uniform(vs, scale);
    assert(vs.len() > 0);
    assert(vs[0] is Num);
    assert(num_max_scale(vs) == scale);
}

/// Inside their capacity conditions every aggregate of a group with at most `int8_max` members succeeds.
pub proof fn lemma_aggs_ok_inside(pd: int, xs: Seq<Row>, k: Row)
    requires gcount(q1_spec(pd), xs, k) <= int8_max(),
    ensures aggs_ok_inside(ast_aggs(), members(q1_spec(pd), xs, k)),
{
    let g = q1_spec(pd);
    let m = members(g, xs, k);
    let aggs = ast_aggs();
    lemma_ast_aggs();
    assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(m, j))
        implies agg_value(aggs[j], column(m, j)) is Ok by {
        lemma_members_col(g, xs, k, j);
        let vs = column(m, j);
        if j == 0 {
            lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(4), vs);
        } else if j == 1 {
            lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(5), vs);
        } else if j == 2 {
            lemma_sum_inside_ok(NumKind::Numeric, e_disc_price(), vs);
        } else if j == 3 {
            lemma_sum_inside_ok(NumKind::Numeric, e_charge(), vs);
        } else if j == 4 {
            lemma_avg_inside_ok(NumKind::Numeric, Expr::Col(4), vs);
        } else if j == 5 {
            lemma_avg_inside_ok(NumKind::Numeric, Expr::Col(5), vs);
        } else if j == 6 {
            lemma_avg_inside_ok(NumKind::Numeric, Expr::Col(6), vs);
        } else {
            lemma_count_value(Agg::CountStar, vs);
        }
    }
}

/// The GROUP BY's prepared inputs and groups in normal-form terms: the keys and argument rows of the kept rows are
/// `qkeys` and the qualifying rows' `arg_vals`; their distinct keys are `gkeys`; every group's members are `members`.
pub proof fn lemma_groups_setup(db: Database, rows: Seq<Row>, p: Literal, pd: int)
    requires body_hyps(db, rows, p, pd),
    ensures ({
        let g = q1_spec(pd);
        let xs = proj_all(rows, src_cols());
        let kept = kept_rows(pd, rows);
        let ks = qkeys(g, xs);
        let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
        &&& ks.len() == kept.len()
        &&& args.len() == kept.len()
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], ast_keys(), ast_aggs())
                == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
        &&& distinct_rows(ks) == gkeys(g, xs)
        &&& forall|k: Row| #[trigger] gkeys(g, xs).contains(k) ==> group_members(ks, args, k) == members(g, xs, k)
    }),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_input);
    let g = q1_spec(pd);
    let cols = src_cols();
    let xs = proj_all(rows, cols);
    let kept = kept_rows(pd, rows);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    lemma_input(db, rows, p, pd);
    lemma_xs_ok(rows);
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], ast_keys(), ast_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        lemma_keys_row(db, kept[i]);
        lemma_args_row(db, kept[i], pd);
        lemma_group_input_unfold(db, kept[i], ast_keys(), ast_aggs());
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
    }
    lemma_keys_exact(pd, xs);
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    assert forall|k: Row| #[trigger] gkeys(g, xs).contains(k) implies group_members(ks, args, k) == members(g, xs, k) by {
        let i = choose|i: int| 0 <= i < gkeys(g, xs).len() && gkeys(g, xs)[i] == k;
        assert(pool.contains(gkeys(g, xs)[i]));
        lemma_group_members(g, xs, k, pool);
    }
}

/// A group (with at most `int8_max` rows in every group) whose aggregate `j` leaves its capacity condition puts the
/// statement outside the capacity domain: the absolute mass of SUM(disc_price) / SUM(charge) beyond `i128`
/// (j = 2, 3), or an AVG division outside its executable domain (j = 4, 5, 6).
pub proof fn lemma_body_group_capacity(db: Database, rows: Seq<Row>, p: Literal, pd: int, k: Row, j: int)
    requires
        body_hyps(db, rows, p, pd),
        forall|k2: Row| #[trigger] gcount(q1_spec(pd), proj_all(rows, src_cols()), k2) <= int8_max(),
        gcount(q1_spec(pd), proj_all(rows, src_cols()), k) > 0,
        2 <= j <= 6,
        (j == 2 || j == 3) ==> gabs(q1_spec(pd), proj_all(rows, src_cols()), k, j) > i128_max(),
        (4 <= j <= 6) ==> !num_div_fits(gsum(q1_spec(pd), proj_all(rows, src_cols()), k, j), 2,
            gcount(q1_spec(pd), proj_all(rows, src_cols()), k) as int, 0),
    ensures !fits_query(db, Seq::empty(), ast_body(p)),
{
    hide(eval_query);
    hide(group_input);
    let g = q1_spec(pd);
    let xs = proj_all(rows, src_cols());
    let kept = kept_rows(pd, rows);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let ctx = Seq::<Val>::empty();
    lemma_input(db, rows, p, pd);
    lemma_groups_setup(db, rows, p, pd);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] aggs_ok_inside(ast_aggs(), group_members(ks, args, ds[h])) by {
        assert(ds.contains(ds[h]));
        lemma_aggs_ok_inside(pd, xs, ds[h]);
    }
    let vs = column(members(g, xs, k), j);
    lemma_ast_aggs();
    lemma_members_col(g, xs, k, j);
    if j == 2 || j == 3 {
        let scale: nat = if j == 2 { 4 } else { 6 };
        lemma_members_mass_fits(g, xs, k, j, scale);
        assert(!fits_agg_value(ast_aggs()[j], vs));
    } else {
        assert(avg_sum(NumKind::Numeric, vs) == (gsum(g, xs, k, j), 2nat));
        assert(!fits_avg(NumKind::Numeric, vs));
        assert(!crate::exec::aggs::avg::fits_avg_value(NumKind::Numeric, vs));
        assert(!fits_agg_value(ast_aggs()[j], vs));
    }
    assert(group_members(ks, args, ds[gi]) == members(g, xs, k));
    lemma_group_by_capacity(db, ctx, ast_keys(), ast_aggs(), Box::new(ast_input(p)), kept, ks, args, gi, j);
}

/// Every aggregate value of a group is a value or the 22003 error (exact SUM/AVG of numeric arguments and the
/// COUNT only fail by the range checks).
pub proof fn lemma_agg_values_ok_or_range(pd: int, xs: Seq<Row>, k: Row, j: int)
    requires gcount(q1_spec(pd), xs, k) > 0, 0 <= j < 8,
    ensures ({
        let v = agg_value(ast_aggs()[j], column(members(q1_spec(pd), xs, k), j));
        v is Ok || v == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange)
    }),
{
    let g = q1_spec(pd);
    lemma_ast_aggs();
    lemma_members_col(g, xs, k, j);
    let vs = column(members(g, xs, k), j);
    if 4 <= j <= 6 {
        let s = avg_sum(NumKind::Numeric, vs);
        assert(count_non_null(vs) > 0);
        assert(count_non_null(vs) as int != 0);
    }
}

/// A group with more than `int8_max` rows makes the statement's meaning the error 22003 (COUNT beyond int8; every
/// other aggregate value is a value or the same error, so the group order does not matter).
pub proof fn lemma_body_count_error(db: Database, rows: Seq<Row>, p: Literal, pd: int, k: Row)
    requires
        body_hyps(db, rows, p, pd),
        gcount(q1_spec(pd), proj_all(rows, src_cols()), k) > int8_max(),
    ensures eval_query(db, Seq::empty(), ast_body(p)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_query);
    hide(group_input);
    let g = q1_spec(pd);
    let xs = proj_all(rows, src_cols());
    let kept = kept_rows(pd, rows);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let ctx = Seq::<Val>::empty();
    let e = SqlError::NumericValueOutOfRange;
    lemma_input(db, rows, p, pd);
    lemma_groups_setup(db, rows, p, pd);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    lemma_ast_aggs();
    assert forall|h: int, j: int| 0 <= h < ds.len() && 0 <= j < ast_aggs().len() implies
        #[trigger] agg_value(ast_aggs()[j], column(group_members(ks, args, ds[h]), j)) is Ok
            || agg_value(ast_aggs()[j], column(group_members(ks, args, ds[h]), j)) == Err::<Val, SqlError>(e) by {
        assert(ds.contains(ds[h]));
        lemma_agg_values_ok_or_range(pd, xs, ds[h], j);
    }
    lemma_members_col(g, xs, k, 7);
    lemma_count_value(Agg::CountStar, column(members(g, xs, k), 7));
    lemma_group_by_err(db, ctx, ast_keys(), ast_aggs(), Box::new(ast_input(p)), kept, ks, args, e, gi, 7);
}

} // verus!
