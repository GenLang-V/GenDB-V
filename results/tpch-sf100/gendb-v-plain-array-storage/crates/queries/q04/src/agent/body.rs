//! The statement body of Q4 (`GROUP BY` over `WHERE` over `orders`) in terms of the normal form (`agent::normal`):
//! its rows when every group count fits int8 (`lemma_body_ok`), the exact SQL error of a COUNT beyond int8
//! (`lemma_body_count_error`), and the error of the window's upper bound (`$1 + 3 months` outside the timestamp range)
//! on a non-empty `orders` table (`lemma_body_hi_err`).
//!
//! Every lemma takes the table rows `rows = db.tables[1]` (all `o_row_ok`), the lineitem view `l` of
//! `db.tables[0]`, and the parameter literal `p` with its day number `pd`; `xs = proj_all(rows, src_cols())`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::limits::int8_max;
use crate::spec::equality::distinct_rows;
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::capacity::*;
use crate::agent::cols::*;
use crate::agent::normal::*;

verus! {

/// Every row of the table is a well-formed `orders` row on the columns Q4 reads.
pub open spec fn rows_ok(rows: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> o_row_ok(#[trigger] rows[i])
}

/// Hypotheses shared by the lemmas: the tables, their rows and the parameter.
pub open spec fn body_hyps(db: Database, rows: Seq<Row>, l: LCols, p: Literal, pd: int) -> bool {
    &&& db.tables.len() > 1
    &&& rows == db.tables[1]
    &&& rows_ok(rows)
    &&& li_rows_ok(db.tables[0], l)
    &&& lit_val(p) == Ok::<Val, SqlError>(Val::Date(pd))
}

/// The rows the WHERE keeps (the GROUP BY's input), under the normal form's condition.
pub open spec fn kept_rows(l: LCols, pd: int, t1: int, rows: Seq<Row>) -> Seq<Row> {
    keep_true(rows, qual_truths(q4_spec(l, pd, t1), proj_all(rows, src_cols())))
}

/// Projected source rows: three values, the priority a text.
pub proof fn lemma_xs_ok(rows: Seq<Row>)
    requires rows_ok(rows),
    ensures
        proj_all(rows, src_cols()).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] proj_all(rows, src_cols())[i] == proj(rows[i], src_cols()),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] proj_all(rows, src_cols())[i]).len() == 3
            && proj_all(rows, src_cols())[i][2] is Text,
{
    let xs = proj_all(rows, src_cols());
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] xs[i]).len() == 3 && xs[i][2] is Text by {
        assert(xs[i] == proj(rows[i], src_cols()));
        assert(o_row_ok(rows[i]));
        assert(proj(rows[i], src_cols())[2] == rows[i][5]);
    }
}

/// The WHERE of the body evaluates to the kept rows; they are table rows that qualify, projecting to the normal form's
/// qualifying rows.
pub proof fn lemma_input(db: Database, rows: Seq<Row>, l: LCols, p: Literal, pd: int, t1: int)
    requires body_hyps(db, rows, l, p, pd), rows.len() > 0 ==> hi_res(pd) == Ok::<int, SqlError>(t1),
    ensures ({
        let g = q4_spec(l, pd, t1);
        let xs = proj_all(rows, src_cols());
        let kept = kept_rows(l, pd, t1, rows);
        &&& eval_query(db, Seq::empty(), ast_input(p)) == Ok::<Relation, SqlError>(kept)
        &&& kept.len() == qrows(g, xs).len()
        &&& forall|i: int| 0 <= i < kept.len() ==> rows.contains(#[trigger] kept[i]) && (g.qual)(proj(kept[i], src_cols()))
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] proj(kept[i], src_cols()) == qrows(g, xs)[i]
        &&& forall|i: int| 0 <= i < kept.len() ==> o_row_ok(#[trigger] kept[i])
    }),
{
    hide(eval_pred);
    let g = q4_spec(l, pd, t1);
    let cols = src_cols();
    let xs = proj_all(rows, cols);
    let kept = kept_rows(l, pd, t1, rows);
    assert(eval_query(db, Seq::empty(), Query::Table(1)) == Ok::<Relation, SqlError>(rows));
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], ast_pred(p)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols)))) by {
        lemma_pred_row(db, rows[i], p, pd, t1, l);
    }
    assert(pred_agrees(db, rows, cols, ast_pred(p), g));
    lemma_filter_rows(db, Query::Table(1), rows, cols, ast_pred(p), g);
    lemma_kept_rows(g, rows, cols);
    assert(proj_all(kept, cols).len() == kept.len());
    assert forall|i: int| 0 <= i < kept.len() implies o_row_ok(#[trigger] kept[i]) by {
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(o_row_ok(rows[m]));
    }
}

/// Per-row agreement of the keys and aggregate arguments on every table row.
pub proof fn lemma_agree(db: Database, rows: Seq<Row>, l: LCols, pd: int, t1: int)
    requires rows_ok(rows),
    ensures
        keys_agree(db, rows, src_cols(), ast_keys(), q4_spec(l, pd, t1)),
        args_agree(db, rows, src_cols(), ast_aggs(), q4_spec(l, pd, t1)),
{
    hide(eval_exprs);
    hide(agg_args);
    let g = q4_spec(l, pd, t1);
    let cols = src_cols();
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        eval_exprs(db, rows[i], ast_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], cols))) by {
        lemma_keys_row(db, rows[i]);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        agg_args(db, rows[i], ast_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], cols))) by {
        lemma_args_row(db, rows[i], l, pd, t1);
    }
}

/// Inside `group_caps` the body is the normal form's result rows.
pub proof fn lemma_body_ok(db: Database, rows: Seq<Row>, l: LCols, p: Literal, pd: int, t1: int)
    requires
        body_hyps(db, rows, l, p, pd),
        rows.len() > 0 ==> hi_res(pd) == Ok::<int, SqlError>(t1),
        group_caps(q4_spec(l, pd, t1), proj_all(rows, src_cols())),
    ensures
        eval_query(db, Seq::empty(), ast_body(p)) == Ok::<Relation, SqlError>(result_rows(q4_spec(l, pd, t1), proj_all(rows, src_cols()))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let g = q4_spec(l, pd, t1);
    let cols = src_cols();
    let xs = proj_all(rows, cols);
    lemma_input(db, rows, l, p, pd, t1);
    lemma_agree(db, rows, l, pd, t1);
    lemma_aggs_match(l, pd, t1);
    lemma_xs_ok(rows);
    lemma_keys_exact(l, pd, t1, xs);
    lemma_group_query(db, rows, cols, ast_input(p), ast_keys(), ast_aggs(), g);
    let ks = gkeys(g, xs);
    let fulls = ks.map_values(|k: Row| full_row(g, xs, k));
    let outs = ks.map_values(|k: Row| out_row(g, xs, k));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] fulls[i] == outs[i] by {
        let k = ks[i];
        assert(ks.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
        assert(k == q4_key(xs[m]));
        assert(k.len() == 1);
        let f = full_row(g, xs, k);
        assert(agg_outs(g, xs, k).len() == 1);
        lemma_select_identity(f, seq![0nat, 1nat]);
    }
    assert(fulls =~= outs);
    assert(ast_body(p) == Query::GroupBy { keys: ast_keys(), aggs: ast_aggs(), input: Box::new(ast_input(p)) });
}

/// The window's upper bound fails: on a non-empty table, the body's meaning is that error.
pub proof fn lemma_body_hi_err(db: Database, rows: Seq<Row>, l: LCols, p: Literal, pd: int, e: SqlError)
    requires
        body_hyps(db, rows, l, p, pd),
        hi_res(pd) == Err::<int, SqlError>(e),
        rows.len() > 0,
    ensures eval_query(db, Seq::empty(), ast_body(p)) == Err::<Relation, SqlError>(e),
{
    hide(eval_pred);
    let ctx = Seq::<Val>::empty();
    assert(eval_query(db, ctx, Query::Table(1)) == Ok::<Relation, SqlError>(rows));
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], ast_pred(p)) is Ok
        || eval_pred(db, ctx + rows[k], ast_pred(p)) == Err::<Truth, SqlError>(e) by {
        assert(ctx + rows[k] =~= rows[k]);
        lemma_pred_row_err(db, rows[k], p, pd, e);
    }
    assert(ctx + rows[0] =~= rows[0]);
    lemma_pred_row_err(db, rows[0], p, pd, e);
    lemma_filter_err(db, ctx, ast_pred(p), Box::new(Query::Table(1)), rows, e, 0);
    lemma_first_input(db, ctx, ast_body(p));
}

/// The GROUP BY's prepared inputs and groups in normal-form terms.
pub proof fn lemma_groups_setup(db: Database, rows: Seq<Row>, l: LCols, p: Literal, pd: int, t1: int)
    requires body_hyps(db, rows, l, p, pd), rows.len() > 0 ==> hi_res(pd) == Ok::<int, SqlError>(t1),
    ensures ({
        let g = q4_spec(l, pd, t1);
        let xs = proj_all(rows, src_cols());
        let kept = kept_rows(l, pd, t1, rows);
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
    let g = q4_spec(l, pd, t1);
    let cols = src_cols();
    let xs = proj_all(rows, cols);
    let kept = kept_rows(l, pd, t1, rows);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    lemma_input(db, rows, l, p, pd, t1);
    lemma_xs_ok(rows);
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], ast_keys(), ast_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        lemma_keys_row(db, kept[i]);
        lemma_args_row(db, kept[i], l, pd, t1);
        lemma_group_input_unfold(db, kept[i], ast_keys(), ast_aggs());
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
    }
    lemma_keys_exact(l, pd, t1, xs);
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

/// A group with more than int8 rows makes the statement's meaning the error 22003 (COUNT beyond int8; every other
/// group's COUNT is a value or the same error, so the group order does not matter).
pub proof fn lemma_body_count_error(db: Database, rows: Seq<Row>, l: LCols, p: Literal, pd: int, t1: int, k: Row)
    requires
        body_hyps(db, rows, l, p, pd),
        rows.len() > 0 ==> hi_res(pd) == Ok::<int, SqlError>(t1),
        gcount(q4_spec(l, pd, t1), proj_all(rows, src_cols()), k) > int8_max(),
    ensures eval_query(db, Seq::empty(), ast_body(p)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_query);
    hide(group_input);
    let g = q4_spec(l, pd, t1);
    let xs = proj_all(rows, src_cols());
    let kept = kept_rows(l, pd, t1, rows);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let ctx = Seq::<Val>::empty();
    let e = SqlError::NumericValueOutOfRange;
    lemma_input(db, rows, l, p, pd, t1);
    lemma_groups_setup(db, rows, l, p, pd, t1);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    assert forall|h: int, j: int| 0 <= h < ds.len() && 0 <= j < ast_aggs().len() implies
        #[trigger] agg_value(ast_aggs()[j], column(group_members(ks, args, ds[h]), j)) is Ok
            || agg_value(ast_aggs()[j], column(group_members(ks, args, ds[h]), j)) == Err::<Val, SqlError>(e) by {
        assert(ds.contains(ds[h]));
        lemma_members_col(g, xs, ds[h], j);
        lemma_count_value(Agg::CountStar, column(members(g, xs, ds[h]), j));
    }
    lemma_members_col(g, xs, k, 0);
    lemma_count_value(Agg::CountStar, column(members(g, xs, k), 0));
    assert(group_members(ks, args, ds[gi]) == members(g, xs, k));
    lemma_group_by_err(db, ctx, ast_keys(), ast_aggs(), Box::new(ast_input(p)), kept, ks, args, e, gi, 0);
}

} // verus!
