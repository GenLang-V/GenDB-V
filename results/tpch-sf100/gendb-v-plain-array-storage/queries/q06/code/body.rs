//! The statement body of Q6 (`Aggregate` over `WHERE` over `lineitem`) over one database: its one row inside the
//! capacity domain (`lemma_body_rows`), `Capacity` when the SUM's absolute mass leaves `i128`
//! (`lemma_body_capacity`), and the exact SQL error when `$1 + INTERVAL '1' YEAR` fails (`lemma_body_err`).
//!
//! Every lemma takes the table rows `rows = db.tables[0]` (all `table_row_ok`, `table_hyps`); `xs =
//! proj_all(rows, src_cols())` are the projected rows the normal form reads.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::datetime::*;
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::expr::*;
use crate::link::capacity::*;
use crate::agent::normal::*;
use crate::agent::source::rows_ok;

verus! {

/// The table and its well-formed rows.
pub open spec fn table_hyps(db: Database, rows: Seq<Row>) -> bool {
    &&& db.tables.len() > 0
    &&& rows == db.tables[0]
    &&& rows_ok(rows)
}

/// The rows the WHERE keeps under the normal form's condition.
pub open spec fn kept_rows(g: QuerySpec, rows: Seq<Row>) -> Seq<Row> {
    keep_true(rows, qual_truths(g, proj_all(rows, src_cols())))
}

/// The one output row: SUM at scale 4 (NULL without qualifying rows).
pub open spec fn sum_row(g: QuerySpec, xs: Seq<Row>) -> Row {
    seq![agg_out(AggKind::Sum { scale: 4 }, gcount(g, xs, Seq::<Val>::empty()), gsum(g, xs, Seq::<Val>::empty(), 0))]
}

/// The WHERE of the body evaluates to the kept rows.
pub proof fn lemma_input(db: Database, rows: Seq<Row>, ps: Seq<Literal>, g: QuerySpec)
    requires table_hyps(db, rows), pred_agrees(db, rows, src_cols(), ast_pred(ps), g),
    ensures eval_query(db, Seq::empty(), ast_input(ps)) == Ok::<Relation, SqlError>(kept_rows(g, rows)),
{
    assert(eval_query(db, Seq::empty(), Query::Table(0)) == Ok::<Relation, SqlError>(rows));
    lemma_filter_rows(db, Query::Table(0), rows, src_cols(), ast_pred(ps), g);
}

/// A scalar normal form has no rows under any key other than the empty one.
pub proof fn lemma_other_key(g: QuerySpec, xs: Seq<Row>, k: Row, j: int)
    requires scalar_key(g), k != Seq::<Val>::empty(),
    ensures gabs(g, xs, k, j) == 0, gcount(g, xs, k) == 0,
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_other_key(g, xs.drop_last(), k, j);
        assert((g.key)(xs.last()) == Seq::<Val>::empty());
    }
}

/// The SUM inside `i128` is the whole arithmetic domain of the normal form.
pub proof fn lemma_caps(b: QBounds, xs: Seq<Row>)
    requires gabs(q6_spec(b), xs, Seq::<Val>::empty(), 0) <= i128_max(),
    ensures group_caps(q6_spec(b), xs),
{
    let g = q6_spec(b);
    lemma_aggs_match(b);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        if k != Seq::<Val>::empty() {
            lemma_other_key(g, xs, k, j);
        } else {
            assert(j == 0);
        }
    }
}

/// Inside the SUM's capacity condition the body is the one row `sum_row` (also for an empty table).
pub proof fn lemma_body_rows(db: Database, rows: Seq<Row>, ps: Seq<Literal>, b: QBounds)
    requires
        table_hyps(db, rows),
        pred_agrees(db, rows, src_cols(), ast_pred(ps), q6_spec(b)),
        gabs(q6_spec(b), proj_all(rows, src_cols()), Seq::<Val>::empty(), 0) <= i128_max(),
    ensures
        eval_query(db, Seq::empty(), ast_body(ps)) == Ok::<Relation, SqlError>(seq![sum_row(q6_spec(b), proj_all(rows, src_cols()))]),
{
    hide(eval_query);
    hide(eval_pred);
    hide(agg_args);
    let g = q6_spec(b);
    let xs = proj_all(rows, src_cols());
    let e = Seq::<Val>::empty();
    lemma_input(db, rows, ps, g);
    lemma_args_agree(db, rows, b);
    lemma_aggs_match(b);
    lemma_caps(b, xs);
    lemma_aggregate_query(db, rows, src_cols(), ast_input(ps), ast_aggs(), g);
    assert(full_row(g, xs, e) =~= sum_row(g, xs));
}

// ------------------------------------------------------------------------------------------------ capacity

/// The members' argument column: numeric at scale 4, its absolute mass at that scale is `gabs`.
pub proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row, j: int, scale: nat)
    requires
        0 <= j < g.aggs.len(),
        g.aggs[j] == (AggKind::Sum { scale }),
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

/// The SUM capacity condition of the members' argument column is the `gabs` bound.
pub proof fn lemma_members_mass_fits(g: QuerySpec, xs: Seq<Row>, k: Row, j: int, scale: nat)
    requires
        0 <= j < g.aggs.len(),
        g.aggs[j] == (AggKind::Sum { scale }),
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

/// A SUM whose absolute mass leaves `i128` puts the statement outside the capacity domain.
pub proof fn lemma_body_capacity(db: Database, rows: Seq<Row>, ps: Seq<Literal>, b: QBounds)
    requires
        table_hyps(db, rows),
        pred_agrees(db, rows, src_cols(), ast_pred(ps), q6_spec(b)),
        gabs(q6_spec(b), proj_all(rows, src_cols()), Seq::<Val>::empty(), 0) > i128_max(),
    ensures !fits_query(db, Seq::empty(), ast_body(ps)),
{
    hide(eval_query);
    hide(eval_pred);
    hide(agg_args);
    let g = q6_spec(b);
    let cols = src_cols();
    let xs = proj_all(rows, cols);
    let e = Seq::<Val>::empty();
    let ctx = Seq::<Val>::empty();
    let kept = kept_rows(g, rows);
    let aggs = ast_aggs();
    lemma_input(db, rows, ps, g);
    lemma_args_agree(db, rows, b);
    lemma_kept_rows(g, rows, cols);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert(proj_all(kept, cols).len() == kept.len());
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] agg_args(db, ctx + kept[i], aggs) == Ok::<Row, SqlError>(args[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert((g.qual)(proj(rows[m], cols)));
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
    }
    lemma_aggs_match(b);
    lemma_scalar_members(g, xs);
    lemma_members_col(g, xs, e, 0);
    if gcount(g, xs, e) == 0 {
        lemma_zero_count(g, xs, e, 0);
    }
    lemma_members_mass_fits(g, xs, e, 0, 4);
    let vs = column(args, 0);
    assert(!fits_agg_value(aggs[0], vs));
    assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(args, j))
        implies agg_value(aggs[j], column(args, j)) is Ok by {
        lemma_sum_inside_ok(NumKind::Numeric, e_revenue(), column(args, j));
    }
    lemma_aggregate_capacity(db, ctx, aggs, Box::new(ast_input(ps)), kept, args, 0);
}

// ------------------------------------------------------------------------------------------------ the SQL error

/// `$1 + INTERVAL '1' YEAR` at the day `pd` (days since 2000-01-01): the timestamp of `date_to_ts` and
/// `ts_add_interval`, or their error.
pub open spec fn year_end_val(pd: int) -> Result<Val, SqlError> {
    match date_to_ts(pd) {
        Err(e) => Err(e),
        Ok(t0) => match ts_add_interval(t0, 12, 0, 0) {
            Ok(t) => Ok(Val::Ts(t)),
            Err(e) => Err(e),
        },
    }
}

/// The evaluator's value of `$1 + INTERVAL '1' YEAR` (it reads no column).
pub proof fn lemma_year_end_eval(db: Database, env: Row, p0: Literal, pd: int)
    requires lit_val(p0) == Ok::<Val, SqlError>(Val::Date(pd)),
    ensures eval_expr(db, env, e_year_end(p0)) == year_end_val(pd),
{
    hide(lit_val);
    hide(date_to_ts);
    hide(ts_add_interval);
    let cst = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p0)) };
    assert(eval_expr(db, env, Expr::Lit(p0)) == Ok::<Val, SqlError>(Val::Date(pd)));
    assert(eval_expr(db, env, cst) == cast(CastOp::DateToTimestamp, Val::Date(pd)));
}

/// On a table row, the WHERE condition fails with the error of `$1 + INTERVAL '1' YEAR`.
pub proof fn lemma_row_err(db: Database, r: Row, ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        table_row_ok(r),
        ps.len() == 3,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd)),
        year_end_val(pd) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, r, ast_pred(ps)) == Err::<Truth, SqlError>(e),
{
    let d = r[10]->Date_0;
    lemma_year_end_eval(db, r, ps[0], pd);
    assert(eval_expr(db, r, Expr::Col(10)) == Ok::<Val, SqlError>(r[10]));
    assert(eval_expr(db, r, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Date(pd)));
    lemma_compare_date(d, pd);
    lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(10), Expr::Lit(ps[0]), r[10], Val::Date(pd), d, pd);
    let lt = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(10), b: e_year_end(ps[0]) };
    assert(eval_pred(db, r, lt) == Err::<Truth, SqlError>(e));
    assert(eval_pred(db, r, ast_date_pred(ps[0])) == Err::<Truth, SqlError>(e));
    let dd = Pred::And(Box::new(ast_date_pred(ps[0])), Box::new(ast_disc_pred(ps[1])));
    assert(eval_pred(db, r, dd) == Err::<Truth, SqlError>(e));
}

/// A non-empty table and a failing `$1 + INTERVAL '1' YEAR`: the body is that error.
pub proof fn lemma_body_err(db: Database, rows: Seq<Row>, ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        table_hyps(db, rows),
        rows.len() > 0,
        ps.len() == 3,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd)),
        year_end_val(pd) == Err::<Val, SqlError>(e),
    ensures eval_query(db, Seq::empty(), ast_body(ps)) == Err::<Relation, SqlError>(e),
{
    let ctx = Seq::<Val>::empty();
    let pred = ast_pred(ps);
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(rows));
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], pred) == Err::<Truth, SqlError>(e) by {
        assert(ctx + rows[k] =~= rows[k]);
        lemma_row_err(db, rows[k], ps, pd, e);
    }
    assert(eval_pred(db, ctx + rows[0], pred) == Err::<Truth, SqlError>(e));
    lemma_filter_err(db, ctx, pred, Box::new(Query::Table(0)), rows, e, 0);
    lemma_first_input(db, ctx, ast_body(ps));
}

} // verus!
