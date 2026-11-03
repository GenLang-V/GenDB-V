//! The statement's outcomes from the stored totals.
//!
//! The statement is `Project [100.00 * s0 / s1] (Aggregate [s0, s1] (Filter pred (Product lineitem part)))`. The
//! aggregate row is `[s0, s1]` (`agg_row_of`): both NULL without a qualifying joined row; otherwise `s1` is the sum
//! of `l_extendedprice * (1 - l_discount)` at scale 4, and `s0` the sum of the CASE, whose ELSE branch is the
//! numeric `0` of scale 0, so `s0` has scale 4 when some promotion row qualifies and scale 0 otherwise.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::datetime::*;
use crate::spec::order::*;
use crate::link::expr::closed_db;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::{bound_db, capacity_domain};
use crate::query::*;
use crate::spec::relation::*;
use crate::link::join::{lemma_keep_members};
use crate::link::query::lemma_aggregate_unfold;
use crate::bridge::collect::lemma_collect_all;
use crate::exec::domain::fits_expr;
use crate::exec::relational::domain::{fits_query, project_fs, project_results};
use super::model::*;
use super::terms::*;
use super::kernel::*;
use super::general::*;
use super::sqlrow::*;
use super::bind::*;
use super::joinsum::*;
use super::aggsum::*;

verus! {

// ------------------------------------------------------------------------------------------------ the statement AST

/// `$1 + INTERVAL '1' MONTH` (node n45).
pub open spec fn hi_expr(ps: Seq<Literal>) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[0])) }),
        months: 1i32, days: 0i32, micros: 0i64,
    }
}

/// The exact window of a binding: `lo` the day of `$1`, `hi` the day whose midnight is `$1 + 1 month`.
pub open spec fn win_ok(ps: Seq<Literal>, lo: int, hi: int) -> bool {
    &&& param_domain(ps)
    &&& ps[0] matches Literal::Date { y, m, d } && lo == date_from_civil(y, m, d)
    &&& eval_expr(closed_db(), Seq::empty(), hi_expr(ps)) == Ok::<Val, SqlError>(Val::Ts(hi * usecs_per_day()))
}

/// `$1 + INTERVAL '1' MONTH` evaluates to the error `e`.
pub open spec fn hi_err(ps: Seq<Literal>, e: SqlError) -> bool {
    eval_expr(closed_db(), Seq::empty(), hi_expr(ps)) == Err::<Val, SqlError>(e)
}

/// The aggregate row `[s0, s1]` of the totals.
pub open spec fn agg_row_of(t: Tot) -> Row {
    if !t.any {
        seq![Val::Null, Val::Null]
    } else {
        seq![Val::Num { coeff: t.psum as int, scale: if t.pany { 4 } else { 0 } }, Val::Num { coeff: t.sum as int, scale: 4 }]
    }
}

/// The output expression `100.00 * Col(0) / Col(1)` (node n5).
pub open spec fn out_expr() -> Expr {
    Expr::Call {
        f: ScalarFn::DivNumeric,
        args: seq![
            Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Lit(Literal::Num { coeff: 10000, scale: 2 })), b: Box::new(Expr::Col(0)) },
            Expr::Col(1),
        ],
    }
}

/// `100.00 * s0`.
pub open spec fn mul_expr() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Lit(Literal::Num { coeff: 10000, scale: 2 })), b: Box::new(Expr::Col(0)) }
}

// ------------------------------------------------------------------------------------------------ the stored data

/// For a bound database: the shapes of the stored parts the scan relies on.
pub proof fn lemma_db_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        li_shape(sv.facts),
        pa_shape(sv.custpart),
{
    lemma_li_link(sv, db);
    lemma_pa_link(sv, db);
}

/// The rows of a bound database are typed.
pub proof fn lemma_bound_typed(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures rows_typed(db),
{
    lemma_rows_typed(db);
}

// ------------------------------------------------------------------------------------------------ the nodes

/// The argument rows of the kept rows, collected.
pub proof fn lemma_kept_args(db: Database, ks: Seq<Row>)
    requires
        rows_typed(db),
        forall|i: int| 0 <= i < ks.len() ==> prod_of(db).contains(#[trigger] ks[i]),
    ensures
        collect(Seq::new(ks.len(), |i: int| agg_args(db, Seq::<Val>::empty() + ks[i], aggs_q()))) == Ok::<Seq<Row>, SqlError>(args_of(ks)),
        forall|i: int| 0 <= i < ks.len() ==> #[trigger] agg_args(db, Seq::<Val>::empty() + ks[i], aggs_q()) == Ok::<Row, SqlError>(args_of(ks)[i]),
{
    hide(product_rows);
    hide(agg_args);
    hide(eval_expr);
    hide(eval_pred);
    hide(prow_typed);
    lemma_prod_typed(db);
    let rs = Seq::new(ks.len(), |i: int| agg_args(db, Seq::<Val>::empty() + ks[i], aggs_q()));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] agg_args(db, Seq::<Val>::empty() + ks[i], aggs_q()) == Ok::<Row, SqlError>(args_of(ks)[i]) by {
        assert(Seq::<Val>::empty() + ks[i] =~= ks[i]);
        let pr = prod_of(db);
        let m = choose|m: int| 0 <= m < pr.len() && pr[m] == ks[i];
        assert(prow_typed(pr[m]));
        lemma_row_args(db, ks[i]);
    }
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args_of(ks)[i]) by {}
    lemma_collect_all(rs, args_of(ks));
}

/// The aggregate node of a binding inside the window.
pub proof fn lemma_eval_agg(sv: StoresView, db: Database, ps: Seq<Literal>, w: Win, t: Tot)
    requires
        bound_db(sv, db),
        win_ok(ps, w.lo as int, w.hi as int),
        tot_ok(t, sv.facts, sv.custpart, w),
    ensures
        eval_query(db, Seq::empty(), agg_q(ps)) == Ok::<Relation, SqlError>(seq![agg_row_of(t)]),
{
    let (lo, hi) = (w.lo as int, w.hi as int);
    lemma_bound_typed(sv, db);
    lemma_eval_filter_q(db, ps, lo, hi);
    let ks = kept_of(db, lo, hi);
    lemma_keep_members(prod_of(db), qx(lo, hi));
    lemma_kept_args(db, ks);
    lemma_aggregate_unfold(db, filter_q(ps), aggs_q(), ks, args_of(ks));
    lemma_agg_row(sv, db, w, t);
}

/// A projection whose input rows' projected outcomes leave their domain is outside the capacity domain.
pub proof fn lemma_project_cap(db: Database, ctx: Row, exprs: Seq<Expr>, input: Query, rows: Seq<Row>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
        !crate::exec::relational::domain::fits_each(project_results(db, ctx, rows, exprs), project_fs(db, ctx, rows, exprs)),
    ensures
        !fits_query(db, ctx, Query::Project { exprs, input: Box::new(input) }),
{
    hide(eval_query);
}

/// One expression on one row: its value as a one-value row.
pub proof fn lemma_one_expr(db: Database, row: Row, e: Expr)
    ensures
        eval_exprs(db, row, seq![e]) == match eval_expr(db, row, e) {
            Ok(v) => Ok::<Row, SqlError>(seq![v]),
            Err(err) => Err::<Row, SqlError>(err),
        },
        crate::exec::domain::fits_exprs(db, row, seq![e]) == fits_expr(db, row, e),
{
    hide(eval_expr);
    hide(fits_expr);
    let exprs = seq![e];
    assert(exprs.drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_step(db, row, exprs);
    lemma_eval_exprs_empty(db, row);
    crate::exec::domain::lemma_fits_exprs_unfold(db, row, exprs);
    assert(crate::exec::domain::fits_exprs(db, row, Seq::<Expr>::empty()));
    if let Ok(v) = eval_expr(db, row, e) {
        assert(Seq::<Val>::empty().push(v) =~= seq![v]);
    }
}

/// `collect` of one outcome.
pub proof fn lemma_collect_one(r: Result<Row, SqlError>)
    ensures
        collect(seq![r]) == match r {
            Ok(v) => Ok::<Seq<Row>, SqlError>(seq![v]),
            Err(e) => Err::<Seq<Row>, SqlError>(e),
        },
{
    reveal_with_fuel(collect, 2);
    assert(seq![r].drop_last() =~= Seq::<Result<Row, SqlError>>::empty());
    if let Ok(v) = r {
        assert(Seq::<Row>::empty().push(v) =~= seq![v]);
    }
}

/// The projection over the one aggregate row: the output expression's outcome, or outside the capacity domain
/// with it.
pub proof fn lemma_eval_project(db: Database, ps: Seq<Literal>, row: Row)
    requires
        eval_query(db, Seq::empty(), agg_q(ps)) == Ok::<Relation, SqlError>(seq![row]),
    ensures
        denote_body(db, query_spec_at(ps)) == match eval_expr(db, row, out_expr()) {
            Ok(v) => Ok::<Relation, SqlError>(seq![seq![v]]),
            Err(e) => Err::<Relation, SqlError>(e),
        },
        !fits_expr(db, row, out_expr()) ==> !fits_query(db, Seq::empty(), query_spec_at(ps).body),
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_expr);
    hide(fits_expr);
    hide(eval_exprs);
    hide(crate::exec::domain::fits_exprs);
    hide(collect);
    lemma_ast(ps);
    let ctx = Seq::<Val>::empty();
    let exprs = seq![out_expr()];
    let rows = seq![row];
    assert(ctx + rows[0] =~= row);
    crate::exec::relational::domain::lemma_eval_project(db, ctx, exprs, Box::new(agg_q(ps)));
    let prs = project_results(db, ctx, rows, exprs);
    assert(prs =~= seq![eval_exprs(db, row, exprs)]);
    lemma_one_expr(db, row, out_expr());
    lemma_collect_one(eval_exprs(db, row, exprs));
    if !fits_expr(db, row, out_expr()) {
        let fs = project_fs(db, ctx, rows, exprs);
        crate::exec::relational::domain::lemma_project_fs_index(db, ctx, rows, exprs);
        assert(!fs[0]);
        crate::link::capacity::lemma_fits_each_violation(prs, fs, 0);
        lemma_project_cap(db, ctx, exprs, agg_q(ps), rows);
    }
}

// ------------------------------------------------------------------------------------------------ outcomes

/// The output expression on the aggregate row in a bound database is `eval_out` / `fits_out`.
pub proof fn lemma_out_any_db(db: Database, row: Row)
    requires row.len() == 2,
    ensures
        eval_expr(db, row, out_expr()) == eval_out(row),
        fits_expr(db, row, out_expr()) == fits_out(row),
{
    super::outexpr::lemma_out_eval_db(db, row);
    super::outexpr::lemma_out_eval_db(closed_db(), row);
}

/// Without a lineitem or a part row the statement's one row is NULL.
pub proof fn lemma_outcome_empty(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires
        bound_db(sv, db),
        param_domain(ps),
        n_li(sv.facts) == 0 || n_pa(sv.custpart) == 0,
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(seq![seq![Val::Null]])),
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_expr);
    hide(fits_expr);
    hide(product_rows);
    hide(agg_args);
    lemma_bound_typed(sv, db);
    lemma_li_link(sv, db);
    lemma_pa_link(sv, db);
    crate::link::join::lemma_product_index(db.tables[0], db.tables[3]);
    assert(prod_of(db).len() == 0) by (nonlinear_arith)
        requires prod_of(db).len() == db.tables[0].len() * db.tables[3].len(),
            db.tables[0].len() == 0 || db.tables[3].len() == 0;
    lemma_eval_filter_empty(db, ps);
    let ks = Seq::<Row>::empty();
    assert(args_of(ks) =~= Seq::<Row>::empty());
    assert(Seq::new(ks.len(), |i: int| agg_args(db, Seq::<Val>::empty() + ks[i], aggs_q())) =~= Seq::<Result<Row, SqlError>>::empty());
    lemma_aggregate_unfold(db, filter_q(ps), aggs_q(), ks, Seq::<Row>::empty());
    let row = seq![Val::Null, Val::Null];
    let rs = Seq::new(2, |j: int| agg_value(aggs_q()[j], column(Seq::<Row>::empty(), j)));
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(row[j]) by {
        assert(column(Seq::<Row>::empty(), j) =~= Seq::<Val>::empty());
    }
    lemma_collect_all(rs, row);
    lemma_eval_project(db, ps, row);
    lemma_out_any_db(db, row);
    super::outexpr::lemma_out_eval(row);
    assert(eval_out(row) == Ok::<Val, SqlError>(Val::Null));
    lemma_ast(ps);
    crate::link::outcome::lemma_outcome_rows(db, query_spec_at(ps), seq![seq![Val::Null]]);
}

/// `$1 + 1 month` outside the timestamp range on a non-empty product: the statement's meaning is that error.
pub proof fn lemma_outcome_hi_err(sv: StoresView, db: Database, ps: Seq<Literal>, e: SqlError)
    requires
        bound_db(sv, db),
        param_domain(ps),
        hi_err(ps, e),
        n_li(sv.facts) > 0,
        n_pa(sv.custpart) > 0,
    ensures
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)),
{
    hide(eval_pred);
    lemma_bound_typed(sv, db);
    lemma_li_link(sv, db);
    lemma_pa_link(sv, db);
    let pr = prod_of(db);
    let ctx = Seq::<Val>::empty();
    crate::link::join::lemma_product_index(db.tables[0], db.tables[3]);
    assert(pr.len() > 0) by (nonlinear_arith)
        requires pr.len() == db.tables[0].len() * db.tables[3].len(), db.tables[0].len() > 0, db.tables[3].len() > 0;
    lemma_eval_product_q(db);
    crate::link::join::lemma_keep_all(pr, |x: Row| true);
    lemma_prod_typed(db);
    assert forall|i: int| 0 <= i < pr.len() implies #[trigger] eval_pred(db, ctx + pr[i], pred_q(ps)) == Err::<Truth, SqlError>(e) by {
        assert(ctx + pr[i] =~= pr[i]);
        lemma_row_pred_err(db, pr[i], ps, e);
    }
    crate::link::capacity::lemma_filter_err(db, ctx, pred_q(ps), Box::new(product_q()), pr, e, 0);
    crate::link::capacity::lemma_first_input(db, ctx, agg_q(ps));
    lemma_ast(ps);
    crate::link::capacity::lemma_first_input(db, ctx, query_spec_at(ps).body);
    crate::link::outcome::lemma_outcome_err(db, query_spec_at(ps), e);
}

/// The absolute mass of the SUM beyond `i128`: outside the capacity domain.
pub proof fn lemma_outcome_mass(sv: StoresView, db: Database, ps: Seq<Literal>, w: Win)
    requires
        bound_db(sv, db),
        win_ok(ps, w.lo as int, w.hi as int),
        tot(sv.facts, sv.custpart, 4, w.lo as int, w.hi as int, 0, n_li(sv.facts)) > i128::MAX,
    ensures
        !capacity_domain(db, query_spec_at(ps)),
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_expr);
    hide(eval_pred);
    hide(product_rows);
    hide(agg_args);
    let (lo, hi) = (w.lo as int, w.hi as int);
    let ctx = Seq::<Val>::empty();
    lemma_bound_typed(sv, db);
    lemma_eval_filter_q(db, ps, lo, hi);
    let ks = kept_of(db, lo, hi);
    lemma_keep_members(prod_of(db), qx(lo, hi));
    lemma_kept_args(db, ks);
    lemma_columns(ks);
    lemma_agg_capacity(sv, db, w);
    crate::link::capacity::lemma_aggregate_capacity(db, ctx, aggs_q(), Box::new(filter_q(ps)), ks, args_of(ks), 1);
    lemma_ast(ps);
    crate::link::capacity::lemma_first_input(db, ctx, query_spec_at(ps).body);
}

/// The outcome of the output expression on the aggregate row is the statement's outcome: a value is the one row,
/// an error is the statement's error, and a domain failure is outside the capacity domain.
pub proof fn lemma_outcome_out(sv: StoresView, db: Database, ps: Seq<Literal>, w: Win, t: Tot)
    requires
        bound_db(sv, db),
        win_ok(ps, w.lo as int, w.hi as int),
        tot_ok(t, sv.facts, sv.custpart, w),
    ensures
        fits_out(agg_row_of(t)) && eval_out(agg_row_of(t)) is Ok
            ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(seq![seq![eval_out(agg_row_of(t))->Ok_0]])),
        fits_out(agg_row_of(t)) && eval_out(agg_row_of(t)) is Err
            ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(eval_out(agg_row_of(t))->Err_0)),
        !fits_out(agg_row_of(t)) ==> !capacity_domain(db, query_spec_at(ps)),
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_expr);
    hide(fits_expr);
    let row = agg_row_of(t);
    lemma_eval_agg(sv, db, ps, w, t);
    lemma_eval_project(db, ps, row);
    lemma_out_any_db(db, row);
    lemma_ast(ps);
    let oq = query_spec_at(ps);
    match eval_out(row) {
        Ok(v) => {
            crate::link::outcome::lemma_outcome_rows(db, oq, seq![seq![v]]);
        },
        Err(e) => {
            crate::link::outcome::lemma_outcome_err(db, oq, e);
        },
    }
}

/// The output expression's value on the aggregate row (it reads no table).
pub open spec fn eval_out(r: Row) -> Result<Val, SqlError> {
    eval_expr(closed_db(), r, out_expr())
}

/// The output expression's domain on the aggregate row.
pub open spec fn fits_out(r: Row) -> bool {
    crate::exec::domain::fits_expr(closed_db(), r, out_expr())
}

} // verus!
