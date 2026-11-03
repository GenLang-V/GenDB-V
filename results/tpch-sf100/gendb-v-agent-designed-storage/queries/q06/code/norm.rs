//! Normal form of the statement and its link to the SQL meaning.
//!
//! The statement is a scalar `SUM(l_extendedprice * l_discount)` over the lineitem rows that pass
//! `lo <= l_shipdate < hi`, `dlo <= l_discount <= dhi` and `l_quantity < qhi`, where, in exact units,
//! `lo` is the day number of `$1` (days since 2000-01-01), `hi` is the day whose midnight is `$1 + 1 year`,
//! `dlo`/`dhi` are the coefficients (scale 2) of `$2 - 0.01` / `$2 + 0.01`, and `qhi = $3 * 100` (scale 2).
//!
//! The normal form is a `link::query::QuerySpec` over rows of the four query columns
//! `[l_quantity, l_extendedprice, l_discount, l_shipdate]` (`cols4`). The executable scan reads these columns
//! from the storage `facts` in stored (clustered) order, as the rows `xs_parts(parts)`; `lemma_db_link` shows they
//! are a permutation of the database's rows projected on `cols4`, so every accumulator agrees.
//!
//! Outcome lemmas: `lemma_outcome_ok` (the one result row), `lemma_outcome_capacity` (the absolute mass of the
//! SUM exceeds `i128`), `lemma_outcome_err` (`$1 + 1 year` leaves the timestamp range on a non-empty table).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::int::*;
use crate::spec::typing::*;
use crate::spec::order::*;
use crate::spec::relation::*;
use crate::spec::types::*;
use crate::link::query::*;
use crate::link::expr::*;
use crate::link::join::{lemma_acc_sum_of, lemma_sum_of_perm};
use crate::link::source::lemma_proj_all_index;
use crate::link::capacity::{lemma_aggregate_capacity, aggs_ok_inside};
use crate::exec::relational::domain::*;
use crate::query::*;
use crate::schema::schema_spec;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::gendb_entry::{bound_db, capacity_domain};
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::declaration::*;
use crate::stores::li_bits::interface as LB;
use crate::stores::li_bits::declaration as LBD;

verus! {

// ------------------------------------------------------------------------------------------- the normal form

/// The empty group key of a scalar aggregate.
pub open spec fn ek() -> Row {
    Seq::<Val>::empty()
}

/// `10^15`: the exclusive bound of a numeric(15, 2) coefficient.
pub open spec fn p15() -> int {
    1_000_000_000_000_000
}

/// The WHERE condition over a row `x = [quantity, price, discount, shipdate]` (exact coefficients and days).
pub open spec fn row_qual(lo: int, hi: int, dlo: int, dhi: int, qhi: int, x: Row) -> bool {
    &&& lo <= ival(x[3]) && ival(x[3]) < hi
    &&& dlo <= ival(x[2]) && ival(x[2]) <= dhi
    &&& ival(x[0]) < qhi
}

/// The statement in normal form: scalar SUM (scale 4) of `price * discount` over the qualifying rows.
pub open spec fn qspec(lo: int, hi: int, dlo: int, dhi: int, qhi: int) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| row_qual(lo, hi, dlo, dhi, qhi, x),
        key: |x: Row| Seq::<Val>::empty(),
        arg: |j: int, x: Row| ival(x[1]) * ival(x[2]),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat],
        grouped: false,
    }
}

/// Table positions of the four query columns: l_quantity, l_extendedprice, l_discount, l_shipdate.
pub open spec fn cols4() -> Seq<nat> {
    seq![4nat, 5nat, 6nat, 10nat]
}

/// A row of the four query columns.
pub open spec fn li_row(q: int, p: int, d: int, s: int) -> Row {
    seq![Val::Num { coeff: q, scale: 2 }, Val::Num { coeff: p, scale: 2 }, Val::Num { coeff: d, scale: 2 }, Val::Date(s)]
}

// ------------------------------------------------------------------------------------------- the statement AST

/// `$1 + INTERVAL '1' YEAR` (node n12).
pub open spec fn hi_expr(ps: Seq<Literal>) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[0])) }),
        months: 12i32, days: 0i32, micros: 0i64,
    }
}

/// `$1 + INTERVAL '1' YEAR` has no column reference (so it is evaluated once, `lemma_expr_closed`).
pub proof fn lemma_hi_closed(ps: Seq<Literal>)
    ensures closed_expr(hi_expr(ps)),
{
    reveal_with_fuel(closed_expr, 3);
}

/// `$2 - 0.01` (n20) and `$2 + 0.01` (n27).
pub open spec fn disc_expr(ps: Seq<Literal>, op: ArithOp) -> Expr {
    Expr::Arith { op, kind: NumKind::Numeric, a: Box::new(Expr::Lit(ps[1])), b: Box::new(Expr::Lit(Literal::Num { coeff: 1, scale: 2 })) }
}

/// `$3` as numeric (n34).
pub open spec fn qty_expr(ps: Seq<Literal>) -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(ps[2])) }
}

pub open spec fn pred_date(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(10), b: Expr::Lit(ps[0]) }),
        Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(10), b: hi_expr(ps) }))
}

pub open spec fn pred_disc(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(6), b: disc_expr(ps, ArithOp::Sub) }),
        Box::new(Pred::Cmp { op: CmpOp::Le, a: Expr::Col(6), b: disc_expr(ps, ArithOp::Add) }))
}

pub open spec fn pred_qty(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: qty_expr(ps) }
}

/// The WHERE condition (n36).
pub open spec fn q6_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(Pred::And(Box::new(pred_date(ps)), Box::new(pred_disc(ps)))), Box::new(pred_qty(ps)))
}

/// The aggregate list `[SUM(l_extendedprice * l_discount)]`.
pub open spec fn q6_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(5)), b: Box::new(Expr::Col(6)) } }]
}

pub open spec fn q6_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q6_pred(ps), input: Box::new(Query::Table(0)) }
}

/// The statement AST is the Aggregate of the Filter above, with no ORDER BY, OFFSET or LIMIT.
pub proof fn lemma_q6_ast(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == (Query::Aggregate { aggs: q6_aggs(), input: Box::new(q6_filter(ps)) }),
        query_spec_at(ps).keys == Seq::<OrderKey>::empty(),
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
    assert(query_spec_at(ps).keys =~= Seq::<OrderKey>::empty());
}

// ------------------------------------------------------------------------------------------- parameters

/// The exact bounds of a binding: `lo` the day of `$1`, `hi` the day whose midnight is `$1 + 1 year`,
/// `dlo`/`dhi` the coefficients of `$2 -/+ 0.01`, `qhi` the coefficient of `$3` at scale 2.
pub open spec fn bounds_ok(ps: Seq<Literal>, lo: int, hi: int, dlo: int, dhi: int, qhi: int) -> bool {
    &&& param_domain(ps)
    &&& ps[0] matches Literal::Date { y, m, d } && lo == date_from_civil(y, m, d)
    &&& eval_expr(closed_db(), Seq::empty(), hi_expr(ps)) == Ok::<Val, SqlError>(Val::Ts(hi * usecs_per_day()))
    &&& ps[1] matches Literal::Num { coeff, scale } && dlo == coeff - 1 && dhi == coeff + 1
    &&& ps[2] matches Literal::Int { v, kind } && qhi == v * 100
}

/// `date + 12 months` of a date at midnight is a midnight: `ts_add_interval` keeps the time of day 0.
pub proof fn lemma_year_later_midnight(lo: int, t: int)
    requires ts_add_interval(lo * usecs_per_day(), 12, 0, 0) == Ok::<int, SqlError>(t),
    ensures t % usecs_per_day() == 0,
{
    let u = usecs_per_day();
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(lo, u);
    let t0 = lo * u;
    assert(t0 % u == 0);
    let day = t0 / u;
    let ymd = civil_from_date(day);
    let total = ymd.0 * 12 + (ymd.1 - 1) + 12;
    let y2 = total / 12;
    let m2 = total % 12 + 1;
    let d2 = if ymd.2 <= days_in_month(y2, m2) { ymd.2 } else { days_in_month(y2, m2) };
    let k = date_from_civil(y2, m2, d2);
    assert(ts_add_months(t0, 12) == ts_result(k * u + 0));
    assert(t == k * u);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(k, u);
}

/// `$1 + INTERVAL '1' YEAR` evaluates to the error `e`.
pub open spec fn eval_expr_hi_err(ps: Seq<Literal>, e: SqlError) -> bool {
    eval_expr(closed_db(), Seq::empty(), hi_expr(ps)) == Err::<Val, SqlError>(e)
}

/// The value of `$1 + INTERVAL '1' YEAR` from the day of `$1`.
pub proof fn lemma_hi_eval(ps: Seq<Literal>, lo: int)
    requires lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(lo)),
    ensures
        eval_expr(closed_db(), Seq::empty(), hi_expr(ps)) == match date_to_ts(lo) {
            Err(e) => Err::<Val, SqlError>(e),
            Ok(t0) => match ts_add_interval(t0, 12, 0, 0) {
                Ok(t1) => Ok::<Val, SqlError>(Val::Ts(t1)),
                Err(e) => Err::<Val, SqlError>(e),
            },
        },
{
    hide(lit_val);
    let cdb = closed_db();
    let env = Seq::<Val>::empty();
    let lit = Expr::Lit(ps[0]);
    let c = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(lit) };
    assert(eval_expr(cdb, env, lit) == Ok::<Val, SqlError>(Val::Date(lo)));
    assert(eval_expr(cdb, env, c) == cast(CastOp::DateToTimestamp, Val::Date(lo)));
}

/// The value of a literal of the binding.
pub proof fn lemma_param_lits(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps[0] matches Literal::Date { y, m, d } && lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(date_from_civil(y, m, d))),
        ps[1] matches Literal::Num { coeff, scale } && scale == 2 && abs(coeff) < p15()
            && lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Num { coeff, scale: 2 }),
        ps[2] matches Literal::Int { v, kind } && lit_val(ps[2]) == Ok::<Val, SqlError>(Val::Int(v)),
{
}

// ------------------------------------------------------------------------------------------- per-row evaluation

/// A numeric(15, 2) value.
pub open spec fn num2(v: Val) -> bool {
    v == Val::Num { coeff: ival(v), scale: 2 } && abs(ival(v)) < p15()
}

/// A date value.
pub open spec fn date_val(v: Val) -> bool {
    v == Val::Date(ival(v))
}

/// The typing facts the condition and the argument need of a lineitem row.
pub open spec fn row_typed(r: Row) -> bool {
    &&& r.len() == 16
    &&& num2(r[4]) && num2(r[5]) && num2(r[6]) && date_val(r[10])
}

pub proof fn lemma_pow10_values()
    ensures pow10(0) == 1, pow10(1) == 10, pow10(2) == 100, pow10(15) == p15(), pow10(16) == 10 * p15(),
        pow10(17) == 100 * p15(),
{
    assert(pow10(17) == 100 * p15()) by (compute);
    assert(pow10(16) == 10 * p15()) by (compute);
    assert(pow10(15) == p15()) by (compute);
    assert(pow10(2) == 100) by (compute);
    assert(pow10(1) == 10) by (compute);
}

/// `$2 -/+ 0.01` evaluates to the coefficient `$2 -/+ 1` at scale 2.
pub proof fn lemma_disc_bound(db: Database, env: Row, ps: Seq<Literal>, op: ArithOp)
    requires param_domain(ps), op is Add || op is Sub,
    ensures
        ps[1] matches Literal::Num { coeff, scale } && eval_expr(db, env, disc_expr(ps, op))
            == Ok::<Val, SqlError>(Val::Num { coeff: if op is Add { coeff + 1 } else { coeff - 1 }, scale: 2 }),
{
    lemma_param_lits(ps);
    lemma_pow10_values();
    let c = ps[1]->Num_coeff;
    let one = Literal::Num { coeff: 1, scale: 2 };
    assert(num_in_range(1, 2)) by (compute);
    assert(lit_val(one) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 2 }));
    lemma_node_add(db, env, op, Expr::Lit(ps[1]), Expr::Lit(one), c, 2, 16, 1, 2, 1, 2, 1, 1, 17);
}

/// A literal evaluates to its value.
pub proof fn lemma_eval_lit(db: Database, env: Row, l: Literal)
    ensures eval_expr(db, env, Expr::Lit(l)) == lit_val(l),
{
}

/// `$3` cast to numeric evaluates to the integer at scale 0.
pub proof fn lemma_eval_qty_expr(db: Database, env: Row, ps: Seq<Literal>, v: int)
    requires lit_val(ps[2]) == Ok::<Val, SqlError>(Val::Int(v)),
    ensures eval_expr(db, env, qty_expr(ps)) == Ok::<Val, SqlError>(Val::Num { coeff: v, scale: 0 }),
{
    hide(lit_val);
    assert(eval_expr(db, env, Expr::Lit(ps[2])) == Ok::<Val, SqlError>(Val::Int(v)));
}

/// `AND` with an erring left operand is that error.
pub proof fn lemma_and_err_left(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
{
}

/// `AND` with a succeeding left and an erring right operand is that error.
pub proof fn lemma_and_err_right(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) is Ok, eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
{
}

/// A comparison whose right operand errs (left succeeding) is that error.
pub proof fn lemma_cmp_err_right(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, e: SqlError)
    requires eval_expr(db, env, a) is Ok, eval_expr(db, env, b) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, env, Pred::Cmp { op, a, b }) == Err::<Truth, SqlError>(e),
{
}

/// `l_shipdate >= $1`.
pub proof fn lemma_pred_ship_lo(db: Database, r: Row, ps: Seq<Literal>, lo: int)
    requires
        r.len() == 16, date_val(r[10]),
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(lo)),
    ensures
        eval_pred(db, r, Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(10), b: Expr::Lit(ps[0]) })
            == Ok::<Truth, SqlError>(truth_of(lo <= ival(r[10]))),
{
    hide(eval_pred);
    hide(eval_expr);
    let s = ival(r[10]);
    lemma_expr_col(db, r, 10);
    lemma_eval_lit(db, r, ps[0]);
    lemma_compare_date(s, lo);
    lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(10), Expr::Lit(ps[0]), Val::Date(s), Val::Date(lo), s, lo);
}

/// `l_shipdate >= $1 AND l_shipdate < $1 + INTERVAL '1' YEAR`.
pub proof fn lemma_pred_date(db: Database, r: Row, ps: Seq<Literal>, lo: int, hi: int)
    requires
        r.len() == 16, date_val(r[10]),
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(lo)),
        eval_expr(closed_db(), Seq::empty(), hi_expr(ps)) == Ok::<Val, SqlError>(Val::Ts(hi * usecs_per_day())),
    ensures
        eval_pred(db, r, pred_date(ps)) == Ok::<Truth, SqlError>(truth_of(lo <= ival(r[10]) && ival(r[10]) < hi)),
{
    hide(eval_pred);
    hide(eval_expr);
    let s = ival(r[10]);
    lemma_pred_ship_lo(db, r, ps, lo);
    lemma_expr_col(db, r, 10);
    lemma_hi_closed(ps);
    lemma_expr_closed(db, r, hi_expr(ps));
    lemma_compare_date_midnight(s, hi);
    lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(10), hi_expr(ps), Val::Date(s), Val::Ts(hi * usecs_per_day()), s, hi);
    lemma_pred_and(db, r,
        Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(10), b: Expr::Lit(ps[0]) },
        Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(10), b: hi_expr(ps) }, lo <= s, s < hi);
}

/// `l_discount BETWEEN $2 - 0.01 AND $2 + 0.01`.
pub proof fn lemma_pred_disc(db: Database, r: Row, ps: Seq<Literal>, dlo: int, dhi: int)
    requires
        r.len() == 16, num2(r[6]),
        param_domain(ps),
        ps[1] matches Literal::Num { coeff, scale } && dlo == coeff - 1 && dhi == coeff + 1,
    ensures
        eval_pred(db, r, pred_disc(ps)) == Ok::<Truth, SqlError>(truth_of(dlo <= ival(r[6]) && ival(r[6]) <= dhi)),
{
    hide(eval_pred);
    hide(eval_expr);
    let d = ival(r[6]);
    let disc = Expr::Col(6);
    lemma_expr_col(db, r, 6);
    lemma_disc_bound(db, r, ps, ArithOp::Sub);
    lemma_disc_bound(db, r, ps, ArithOp::Add);
    lemma_compare_num(d, 2, dlo, 2);
    lemma_compare_num(d, 2, dhi, 2);
    lemma_align_same(d, 2);
    lemma_align_same(dlo, 2);
    lemma_align_same(dhi, 2);
    lemma_pred_cmp(db, r, CmpOp::Ge, disc, disc_expr(ps, ArithOp::Sub), Val::Num { coeff: d, scale: 2 }, Val::Num { coeff: dlo, scale: 2 }, d, dlo);
    lemma_pred_cmp(db, r, CmpOp::Le, disc, disc_expr(ps, ArithOp::Add), Val::Num { coeff: d, scale: 2 }, Val::Num { coeff: dhi, scale: 2 }, d, dhi);
    lemma_pred_and(db, r,
        Pred::Cmp { op: CmpOp::Ge, a: disc, b: disc_expr(ps, ArithOp::Sub) },
        Pred::Cmp { op: CmpOp::Le, a: disc, b: disc_expr(ps, ArithOp::Add) }, dlo <= d, d <= dhi);
}

/// `l_quantity < $3`.
pub proof fn lemma_pred_qty(db: Database, r: Row, ps: Seq<Literal>, qhi: int)
    requires
        r.len() == 16, num2(r[4]),
        param_domain(ps),
        ps[2] matches Literal::Int { v, kind } && qhi == v * 100,
    ensures
        eval_pred(db, r, pred_qty(ps)) == Ok::<Truth, SqlError>(truth_of(ival(r[4]) < qhi)),
{
    hide(eval_pred);
    hide(eval_expr);
    lemma_param_lits(ps);
    let q = ival(r[4]);
    let v = ps[2]->Int_v;
    lemma_expr_col(db, r, 4);
    lemma_eval_qty_expr(db, r, ps, v);
    lemma_compare_num(q, 2, v, 0);
    lemma_align_same(q, 2);
    lemma_pow10_values();
    lemma_align_by(v, 0, 2, 100);
    lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(4), qty_expr(ps), Val::Num { coeff: q, scale: 2 }, Val::Num { coeff: v, scale: 0 }, q, v * 100);
}

/// The WHERE condition on one typed row is the normal form's condition on its four query columns.
pub proof fn lemma_row_pred(db: Database, r: Row, ps: Seq<Literal>, lo: int, hi: int, dlo: int, dhi: int, qhi: int)
    requires
        bounds_ok(ps, lo, hi, dlo, dhi, qhi),
        row_typed(r),
    ensures
        eval_pred(db, r, q6_pred(ps)) == Ok::<Truth, SqlError>(truth_of(row_qual(lo, hi, dlo, dhi, qhi, proj(r, cols4())))),
{
    hide(eval_pred);
    hide(eval_expr);
    lemma_param_lits(ps);
    let (q, d, s) = (ival(r[4]), ival(r[6]), ival(r[10]));
    lemma_pred_date(db, r, ps, lo, hi);
    lemma_pred_disc(db, r, ps, dlo, dhi);
    lemma_pred_qty(db, r, ps, qhi);
    lemma_pred_and(db, r, pred_date(ps), pred_disc(ps), lo <= s && s < hi, dlo <= d && d <= dhi);
    lemma_pred_and(db, r, Pred::And(Box::new(pred_date(ps)), Box::new(pred_disc(ps))), pred_qty(ps),
        (lo <= s && s < hi) && (dlo <= d && d <= dhi), q < qhi);
    let x = proj(r, cols4());
    assert(x[0] == r[4] && x[1] == r[5] && x[2] == r[6] && x[3] == r[10]);
}

/// The SUM argument `l_extendedprice * l_discount` of a typed row: the product of the coefficients at scale 4.
pub proof fn lemma_row_product(db: Database, r: Row)
    requires row_typed(r),
    ensures
        agg_arg(db, r, q6_aggs()[0]) == Ok::<Val, SqlError>(Val::Num { coeff: ival(r[5]) * ival(r[6]), scale: 4 }),
{
    hide(eval_expr);
    lemma_pow10_values();
    lemma_expr_col(db, r, 5);
    lemma_expr_col(db, r, 6);
    lemma_node_mul(db, r, Expr::Col(5), Expr::Col(6), ival(r[5]), 2, 15, ival(r[6]), 2, 15);
    lemma_agg_arg_sum(db, r, NumKind::Numeric, Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(5)), b: Box::new(Expr::Col(6)) });
}

/// The four query columns of a row.
pub proof fn lemma_proj4(r: Row)
    ensures
        proj(r, cols4()).len() == 4,
        proj(r, cols4())[0] == r[4],
        proj(r, cols4())[1] == r[5],
        proj(r, cols4())[2] == r[6],
        proj(r, cols4())[3] == r[10],
{
}

/// The normal form's argument values of a row: `[price * discount]` at scale 4.
pub proof fn lemma_arg_vals(lo: int, hi: int, dlo: int, dhi: int, qhi: int, x: Row)
    ensures arg_vals(qspec(lo, hi, dlo, dhi, qhi), x) == seq![Val::Num { coeff: ival(x[1]) * ival(x[2]), scale: 4 }],
{
    let g = qspec(lo, hi, dlo, dhi, qhi);
    assert(g.aggs[0] == AggKind::Sum { scale: 4 });
    assert(arg_vals(g, x) =~= seq![Val::Num { coeff: ival(x[1]) * ival(x[2]), scale: 4 }]);
}

/// The aggregate argument of one typed row is the normal form's argument `price * discount` at scale 4.
pub proof fn lemma_row_args(db: Database, r: Row, lo: int, hi: int, dlo: int, dhi: int, qhi: int)
    requires row_typed(r),
    ensures
        agg_args(db, r, q6_aggs()) == Ok::<Row, SqlError>(arg_vals(qspec(lo, hi, dlo, dhi, qhi), proj(r, cols4()))),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(proj);
    hide(arg_vals);
    lemma_row_product(db, r);
    let prod = Val::Num { coeff: ival(r[5]) * ival(r[6]), scale: 4 };
    let rs = agg_arg_results(db, r, q6_aggs());
    lemma_agg_arg_results_index(db, r, q6_aggs());
    assert(rs[0] == Ok::<Val, SqlError>(prod));
    lemma_collect_all_ok(rs, seq![prod]);
    let x = proj(r, cols4());
    lemma_proj4(r);
    lemma_arg_vals(lo, hi, dlo, dhi, qhi, x);
}

// ------------------------------------------------------------------------------------------- the stored rows

/// Number of stored lineitem rows.
pub open spec fn n_rows(parts: Seq<PartView>) -> int {
    part_len(parts[LI_SHIPDATE_CODES as int]) as int
}

/// The row groups of lineitem.
pub open spec fn gsv(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[LI_GROUPS as int])
}

pub open spec fn qty_at(parts: Seq<PartView>, j: int) -> int {
    for_at(gsv(parts), parts[LI_QUANTITY_BASE as int], parts[LI_QUANTITY_CODES as int], j)
}

pub open spec fn price_at(parts: Seq<PartView>, j: int) -> int {
    for_at(gsv(parts), parts[LI_EXTENDEDPRICE_BASE as int], parts[LI_EXTENDEDPRICE_CODES as int], j)
}

pub open spec fn disc_at(parts: Seq<PartView>, j: int) -> int {
    for_at(gsv(parts), parts[LI_DISCOUNT_BASE as int], parts[LI_DISCOUNT_CODES as int], j)
}

pub open spec fn ship_at(parts: Seq<PartView>, j: int) -> int {
    for_at(gsv(parts), parts[LI_SHIPDATE_BASE as int], parts[LI_SHIPDATE_CODES as int], j)
}

/// The four query columns of every stored lineitem row, in stored order, decoded from the parts.
pub open spec fn xs_parts(parts: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_rows(parts) as nat, |j: int| li_row(qty_at(parts, j), price_at(parts, j), disc_at(parts, j), ship_at(parts, j)))
}

/// An I64 base or zone part with one entry per group.
pub open spec fn group_part_ok(parts: Seq<PartView>, k: int) -> bool {
    parts[k] is I64 && i64s(parts[k]).len() == gsv(parts).len() - 1
}

/// The facts of the parts the scan relies on (all consequences of `represents` and `db_wf`).
pub open spec fn shape_ok(parts: Seq<PartView>) -> bool {
    let n = n_rows(parts);
    &&& parts.len() == FACTS_PARTS
    &&& parts[LI_GROUPS as int] is U64
    &&& groups_wf(gsv(parts), n)
    &&& parts[LI_SHIPDATE_CODES as int] is U16
    &&& parts[LI_DISCOUNT_CODES as int] is U8 && part_len(parts[LI_DISCOUNT_CODES as int]) == n
    &&& parts[LI_QUANTITY_CODES as int] is U16 && part_len(parts[LI_QUANTITY_CODES as int]) == n
    &&& parts[LI_EXTENDEDPRICE_CODES as int] is U32 && part_len(parts[LI_EXTENDEDPRICE_CODES as int]) == n
    &&& group_part_ok(parts, LI_SHIPDATE_BASE as int)
    &&& group_part_ok(parts, LI_SHIPDATE_ZMAX as int)
    &&& group_part_ok(parts, LI_DISCOUNT_BASE as int)
    &&& group_part_ok(parts, LI_QUANTITY_BASE as int)
    &&& group_part_ok(parts, LI_EXTENDEDPRICE_BASE as int)
    &&& zone_max_ok(gsv(parts), parts[LI_SHIPDATE_BASE as int], parts[LI_SHIPDATE_CODES as int], i64s(parts[LI_SHIPDATE_ZMAX as int]))
    &&& forall|j: int| 0 <= j < n ==> abs(#[trigger] price_at(parts, j)) < p15()
    &&& forall|j: int| 0 <= j < n ==> abs(#[trigger] disc_at(parts, j)) < p15()
}

/// The columns 0..15 of lineitem that `facts` stores.
pub proof fn lemma_cols15()
    ensures
        stored_cols_t0().len() == 15,
        forall|k: int| 0 <= k < 15 ==> #[trigger] stored_cols_t0()[k] == k,
{
}

/// The lineitem rows of a bound database are typed (`row_typed`).
pub proof fn lemma_rows_typed(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[0].len() ==> row_typed(#[trigger] db.tables[0][i]),
{
    lemma_declared_schema();
    lemma_pow10_values();
    let num = Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false };
    assert(schema_spec()[0].columns[4] == num) by (compute);
    assert(schema_spec()[0].columns[5] == num) by (compute);
    assert(schema_spec()[0].columns[6] == num) by (compute);
    assert(schema_spec()[0].columns[10] == Column { ty: SqlType::Date, nullable: false }) by (compute);
    assert forall|i: int| 0 <= i < db.tables[0].len() implies row_typed(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, db.schema[0]));
        assert(value_in_column(r[4], num));
        assert(value_in_column(r[5], num));
        assert(value_in_column(r[6], num));
        assert(value_in_column(r[10], Column { ty: SqlType::Date, nullable: false }));
    }
}

/// The facts of `represents` about the lineitem parts that the scan reads.
pub proof fn lemma_li_facts(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires represents(parts, rels),
    ensures ({
        let tp = parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int);
        let n = rels[0].len() as int;
        let srows = lineitem_rows(tp, rels[0]);
        &&& parts.len() == FACTS_PARTS
        &&& table_layout_ok(tp, n)
        &&& is_perm(lineitem_map(tp, n), n)
        &&& tp[LI_QUANTITY_CODES as int] is U16
        &&& num_col_at(tp, LI_GROUPS as int, LI_QUANTITY_CODES as int, LI_QUANTITY_BASE as int, srows, 4, 2)
        &&& tp[LI_EXTENDEDPRICE_CODES as int] is U32
        &&& num_col_at(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, srows, 5, 2)
        &&& tp[LI_DISCOUNT_CODES as int] is U8
        &&& num_col_at(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, srows, 6, 2)
        &&& tp[LI_SHIPDATE_CODES as int] is U16
        &&& date_col_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, srows, 10)
        &&& zone_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, LI_SHIPDATE_ZMAX as int)
    }),
{
}

/// The query columns of one stored row.
pub proof fn lemma_stored_row_cols(parts: Seq<PartView>, srows: Seq<Row>, j: int)
    requires
        parts.len() == FACTS_PARTS,
        0 <= j < srows.len(),
        ({
            let tp = parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int);
            &&& num_col_at(tp, LI_GROUPS as int, LI_QUANTITY_CODES as int, LI_QUANTITY_BASE as int, srows, 4, 2)
            &&& num_col_at(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, srows, 5, 2)
            &&& num_col_at(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, srows, 6, 2)
            &&& date_col_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, srows, 10)
        }),
    ensures
        srows[j][4] == (Val::Num { coeff: qty_at(parts, j), scale: 2 }),
        srows[j][5] == (Val::Num { coeff: price_at(parts, j), scale: 2 }),
        srows[j][6] == (Val::Num { coeff: disc_at(parts, j), scale: 2 }),
        srows[j][10] == Val::Date(ship_at(parts, j)),
{
    let tp = parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int);
    assert(tp[LI_GROUPS as int] == parts[LI_GROUPS as int]);
    assert(tp[LI_QUANTITY_CODES as int] == parts[LI_QUANTITY_CODES as int]);
    assert(tp[LI_QUANTITY_BASE as int] == parts[LI_QUANTITY_BASE as int]);
    assert(tp[LI_EXTENDEDPRICE_CODES as int] == parts[LI_EXTENDEDPRICE_CODES as int]);
    assert(tp[LI_EXTENDEDPRICE_BASE as int] == parts[LI_EXTENDEDPRICE_BASE as int]);
    assert(tp[LI_DISCOUNT_CODES as int] == parts[LI_DISCOUNT_CODES as int]);
    assert(tp[LI_DISCOUNT_BASE as int] == parts[LI_DISCOUNT_BASE as int]);
    assert(tp[LI_SHIPDATE_CODES as int] == parts[LI_SHIPDATE_CODES as int]);
    assert(tp[LI_SHIPDATE_BASE as int] == parts[LI_SHIPDATE_BASE as int]);
}

/// The shape facts of the parts, from `represents`.
pub proof fn lemma_shape_parts(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires represents(parts, rels),
    ensures
        n_rows(parts) == rels[0].len(),
        parts.len() == FACTS_PARTS,
        parts[LI_GROUPS as int] is U64,
        groups_wf(gsv(parts), n_rows(parts)),
        parts[LI_SHIPDATE_CODES as int] is U16,
        parts[LI_DISCOUNT_CODES as int] is U8 && part_len(parts[LI_DISCOUNT_CODES as int]) == n_rows(parts),
        parts[LI_QUANTITY_CODES as int] is U16 && part_len(parts[LI_QUANTITY_CODES as int]) == n_rows(parts),
        parts[LI_EXTENDEDPRICE_CODES as int] is U32 && part_len(parts[LI_EXTENDEDPRICE_CODES as int]) == n_rows(parts),
        group_part_ok(parts, LI_SHIPDATE_BASE as int),
        group_part_ok(parts, LI_SHIPDATE_ZMAX as int),
        group_part_ok(parts, LI_DISCOUNT_BASE as int),
        group_part_ok(parts, LI_QUANTITY_BASE as int),
        group_part_ok(parts, LI_EXTENDEDPRICE_BASE as int),
        zone_max_ok(gsv(parts), parts[LI_SHIPDATE_BASE as int], parts[LI_SHIPDATE_CODES as int], i64s(parts[LI_SHIPDATE_ZMAX as int])),
{
    hide(represents);
    lemma_li_facts(parts, rels);
    let tp = parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int);
    let n = rels[0].len() as int;
    assert forall|k: int| 0 <= k < 48 implies #[trigger] tp[k] == parts[k] by {}
    let bs = u64s(tp[LI_LAYOUT as int])[1] as int;
    lemma_uniform_groups(tp[LI_GROUPS as int], n, bs);
    assert(gsv(parts) == gs_at(tp, LI_GROUPS as int));
    assert(tp[LI_SHIPDATE_CODES as int] == parts[LI_SHIPDATE_CODES as int]);
    assert(n_rows(parts) == n);
    assert(tp[LI_SHIPDATE_ZMAX as int] == parts[LI_SHIPDATE_ZMAX as int]);
    assert(tp[LI_SHIPDATE_BASE as int] == parts[LI_SHIPDATE_BASE as int]);
    assert(tp[LI_DISCOUNT_BASE as int] == parts[LI_DISCOUNT_BASE as int]);
    assert(tp[LI_QUANTITY_BASE as int] == parts[LI_QUANTITY_BASE as int]);
    assert(tp[LI_EXTENDEDPRICE_BASE as int] == parts[LI_EXTENDEDPRICE_BASE as int]);
    assert(tp[LI_DISCOUNT_CODES as int] == parts[LI_DISCOUNT_CODES as int]);
    assert(tp[LI_QUANTITY_CODES as int] == parts[LI_QUANTITY_CODES as int]);
    assert(tp[LI_EXTENDEDPRICE_CODES as int] == parts[LI_EXTENDEDPRICE_CODES as int]);
}

/// One stored row's query columns are its database row's query columns.
pub proof fn lemma_xs_at(parts: Seq<PartView>, rel: Seq<Row>, map: Seq<int>, j: int)
    requires
        parts.len() == FACTS_PARTS,
        n_rows(parts) == rel.len(),
        map.len() == rel.len(),
        0 <= j < rel.len(),
        0 <= map[j] < rel.len(),
        ({
            let tp = parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int);
            let srows = stored_rows(proj_all(rel, stored_cols_t0()), map);
            &&& num_col_at(tp, LI_GROUPS as int, LI_QUANTITY_CODES as int, LI_QUANTITY_BASE as int, srows, 4, 2)
            &&& num_col_at(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, srows, 5, 2)
            &&& num_col_at(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, srows, 6, 2)
            &&& date_col_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, srows, 10)
        }),
    ensures
        xs_parts(parts)[j] == proj_all(rel, cols4())[map[j]],
{
    hide(num_col_at);
    hide(date_col_at);
    let i = map[j];
    let rel15 = proj_all(rel, stored_cols_t0());
    let srows = stored_rows(rel15, map);
    lemma_cols15();
    lemma_proj_all_index(rel, stored_cols_t0());
    lemma_proj_all_index(rel, cols4());
    assert(srows[j] == rel15[i]);
    assert(rel15[i] == proj(rel[i], stored_cols_t0()));
    reveal(num_col_at);
    reveal(date_col_at);
    lemma_stored_row_cols(parts, srows, j);
    assert(srows[j][4] == rel[i][4]);
    assert(srows[j][5] == rel[i][5]);
    assert(srows[j][6] == rel[i][6]);
    assert(srows[j][10] == rel[i][10]);
    lemma_proj4(rel[i]);
    assert(xs_parts(parts)[j] =~= proj_all(rel, cols4())[i]);
}

/// The facts parts the query reads: the parts storage `li_bits` inherits from `facts` (its first 75 parts).
pub open spec fn lbf(sv: StoresView) -> Seq<PartView> {
    LB::facts_parts(sv.li_bits)
}

/// For a bound database: facts' `represents` holds for the inherited parts of `li_bits`, and the bitmaps mean
/// what `li_bits` states.
pub proof fn lemma_lb_facts(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        represents(lbf(sv), stored_relations(db)),
        LB::bits_ok(sv.li_bits),
        sv.li_bits.len() == LB::LI_BITS_PARTS,
{
    hide(represents);
    hide(LB::bits_ok);
    assert(stored_ok(sv, db));
    assert(LB::represents(sv.li_bits, LBD::stored_relations(db)));
    assert(LBD::stored_relations(db) =~= stored_relations(db));
}

/// Under the row map, the stored rows' query columns are the database rows' query columns.
pub proof fn lemma_xs_map(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures ({
        let parts = lbf(sv);
        let tp = parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int);
        let n = db.tables[0].len() as int;
        let map = lineitem_map(tp, n);
        &&& n_rows(parts) == n
        &&& is_perm(map, n)
        &&& xs_parts(parts) == stored_rows(proj_all(db.tables[0], cols4()), map)
    }),
{
    hide(represents);
    hide(lineitem_ok);
    hide(orders_ok);
    hide(lineitem_cols_ok);
    hide(db_wf);
    hide(proj);
    hide(xs_parts);
    hide(num_col_at);
    hide(date_col_at);
    hide(table_layout_ok);
    hide(zone_at);
    let parts = lbf(sv);
    let rels = stored_relations(db);
    let rel = db.tables[0];
    let tp = parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int);
    lemma_lb_facts(sv, db);
    lemma_li_facts(parts, rels);
    lemma_proj_all_index(rel, stored_cols_t0());
    let n = rel.len() as int;
    assert(rels[0].len() == n);
    assert(n_rows(parts) == n) by {
        reveal(represents);
        reveal(lineitem_ok);
        reveal(lineitem_cols_ok);
        reveal(date_col_at);
        assert(tp[LI_SHIPDATE_CODES as int] == parts[LI_SHIPDATE_CODES as int]);
    }
    let map = lineitem_map(tp, n);
    assert(is_perm(map, n));
    assert(lineitem_rows(tp, rels[0]) == stored_rows(proj_all(rel, stored_cols_t0()), map));
    let xs = xs_parts(parts);
    let xd = proj_all(rel, cols4());
    assert forall|j: int| 0 <= j < n implies #[trigger] xs[j] == xd[map[j]] by {
        lemma_xs_at(parts, rel, map, j);
    }
    lemma_proj_all_index(rel, cols4());
    assert(xs.len() == n) by {
        reveal(xs_parts);
    }
    assert(xs =~= stored_rows(xd, map));
}

/// For a bound database: the parts have the shape the scan relies on, and the stored rows `xs_parts` are a
/// permutation of the database's lineitem rows projected on the four query columns.
pub proof fn lemma_db_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        shape_ok(lbf(sv)),
        xs_parts(lbf(sv)).len() == db.tables[0].len(),
        xs_parts(lbf(sv)).to_multiset() == proj_all(db.tables[0], cols4()).to_multiset(),
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[0].len() ==> row_typed(#[trigger] db.tables[0][i]),
{
    hide(represents);
    hide(proj);
    hide(xs_parts);
    let parts = lbf(sv);
    let rel = db.tables[0];
    let n = rel.len() as int;
    let tp = parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int);
    lemma_rows_typed(db);
    lemma_lb_facts(sv, db);
    lemma_shape_parts(parts, stored_relations(db));
    lemma_xs_map(sv, db);
    let map = lineitem_map(tp, n);
    let xs = xs_parts(parts);
    let xd = proj_all(rel, cols4());
    lemma_proj_all_index(rel, cols4());
    lemma_stored_rows_multiset(xd, map);
    // value bounds of price and discount (numeric(15, 2))
    assert forall|j: int| 0 <= j < n implies abs(#[trigger] price_at(parts, j)) < p15() && abs(disc_at(parts, j)) < p15() by {
        let i = map[j];
        assert(xs[j] == xd[i]);
        assert(row_typed(rel[i]));
        lemma_proj4(rel[i]);
        reveal(xs_parts);
        assert(xs[j][1] == rel[i][5]);
        assert(xs[j][2] == rel[i][6]);
    }
    assert forall|j: int| 0 <= j < n implies abs(#[trigger] disc_at(parts, j)) < p15() by {
        assert(abs(price_at(parts, j)) < p15());
    }
    reveal(xs_parts);
}

// ------------------------------------------------------------------------------------------- accumulators

/// The accumulators of a permutation agree.
pub proof fn lemma_acc_perm(g: QuerySpec, a: Seq<Row>, b: Seq<Row>, k: Row)
    requires a.to_multiset() == b.to_multiset(),
    ensures
        gcount(g, a, k) == gcount(g, b, k),
        gsum(g, a, k, 0) == gsum(g, b, k, 0),
        gabs(g, a, k, 0) == gabs(g, b, k, 0),
{
    lemma_acc_sum_of(g, a, k, 0);
    lemma_acc_sum_of(g, b, k, 0);
    lemma_sum_of_perm(a, b, crate::link::join::count_term(g, k));
    lemma_sum_of_perm(a, b, crate::link::join::sum_term(g, k, 0));
    lemma_sum_of_perm(a, b, crate::link::join::abs_term(g, k, 0));
}

/// A key other than the scalar key has no member.
pub proof fn lemma_other_key(g: QuerySpec, rows: Seq<Row>, k: Row)
    requires scalar_key(g), k != ek(),
    ensures gcount(g, rows, k) == 0, gsum(g, rows, k, 0) == 0, gabs(g, rows, k, 0) == 0,
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_other_key(g, rows.drop_last(), k);
        assert((g.key)(rows.last()) == ek());
    }
}

/// The normal form's per-row agreement with the statement over the lineitem rows of a bound database.
pub proof fn lemma_agreement(sv: StoresView, db: Database, ps: Seq<Literal>, lo: int, hi: int, dlo: int, dhi: int, qhi: int)
    requires
        bound_db(sv, db),
        bounds_ok(ps, lo, hi, dlo, dhi, qhi) || db.tables[0].len() == 0,
    ensures ({
        let g = qspec(lo, hi, dlo, dhi, qhi);
        let rel = db.tables[0];
        &&& eval_query(db, Seq::empty(), Query::Table(0)) == Ok::<Relation, SqlError>(rel)
        &&& pred_agrees(db, rel, cols4(), q6_pred(ps), g)
        &&& args_agree(db, rel, cols4(), q6_aggs(), g)
        &&& aggs_match(q6_aggs(), g)
        &&& scalar_key(g)
    }),
{
    let g = qspec(lo, hi, dlo, dhi, qhi);
    let rel = db.tables[0];
    lemma_db_link(sv, db);
    assert forall|i: int| 0 <= i < rel.len() implies
        eval_pred(db, #[trigger] rel[i], q6_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rel[i], cols4())))) by {
        lemma_row_pred(db, rel[i], ps, lo, hi, dlo, dhi, qhi);
    }
    assert forall|i: int| 0 <= i < rel.len() && (g.qual)(proj(#[trigger] rel[i], cols4())) implies
        agg_args(db, rel[i], q6_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rel[i], cols4()))) by {
        lemma_row_args(db, rel[i], lo, hi, dlo, dhi, qhi);
    }
    assert(agg_matches(q6_aggs()[0], g.aggs[0]));
}

// ------------------------------------------------------------------------------------------- outcomes

/// The one result value: NULL without a qualifying row, else the exact sum at scale 4.
pub open spec fn result_val(sum: int, cnt: int) -> Val {
    if cnt == 0 { Val::Null } else { Val::Num { coeff: sum, scale: 4 } }
}

/// Inside the capacity domain, the statement's allowed output is the one row `[result_val(sum, cnt)]` of the
/// stored rows' accumulators.
pub proof fn lemma_outcome_ok(sv: StoresView, db: Database, ps: Seq<Literal>, lo: int, hi: int, dlo: int, dhi: int, qhi: int,
    sum: int, cnt: int)
    requires
        bound_db(sv, db),
        bounds_ok(ps, lo, hi, dlo, dhi, qhi) || n_rows(lbf(sv)) == 0,
        gsum(qspec(lo, hi, dlo, dhi, qhi), xs_parts(lbf(sv)), ek(), 0) == sum,
        gcount(qspec(lo, hi, dlo, dhi, qhi), xs_parts(lbf(sv)), ek()) == cnt,
        gabs(qspec(lo, hi, dlo, dhi, qhi), xs_parts(lbf(sv)), ek(), 0) <= i128_max(),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(seq![seq![result_val(sum, cnt)]])),
{
    let g = qspec(lo, hi, dlo, dhi, qhi);
    let rel = db.tables[0];
    let xd = proj_all(rel, cols4());
    let oq = query_spec_at(ps);
    lemma_db_link(sv, db);
    lemma_agreement(sv, db, ps, lo, hi, dlo, dhi, qhi);
    lemma_acc_perm(g, xs_parts(lbf(sv)), xd, ek());
    // group_caps: only the scalar key has members
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xd, k, j) <= i128_max() by {
        if k != ek() {
            lemma_other_key(g, xd, k);
        }
    }
    assert(group_caps(g, xd));
    lemma_filter_rows(db, Query::Table(0), rel, cols4(), q6_pred(ps), g);
    lemma_aggregate_query(db, rel, cols4(), q6_filter(ps), q6_aggs(), g);
    lemma_q6_ast(ps);
    let r = full_row(g, xd, ek());
    assert(agg_outs(g, xd, ek()) =~= seq![result_val(sum, cnt)]);
    assert(r =~= seq![result_val(sum, cnt)]);
    assert(denote_body(db, oq) == Ok::<Relation, SqlError>(seq![r]));
    lemma_select_identity(r, g.outs);
    assert(out_row(g, xd, ek()) == r);
    assert(result_rows(g, xd) == seq![r]);
    lemma_scalar_result(g, oq.keys, oq.offset, oq.limit, xd, r);
    lemma_slice_all(seq![r]);
    lemma_ordered_link(db, oq, g, xd, seq![r]);
}

/// One more SUM argument value at scale 4: mass, kind and maximal scale.
pub proof fn lemma_mass_push(vs: Seq<Val>, c: int)
    requires
        all_of_kind(NumKind::Numeric, vs),
        vs.len() == 0 || num_max_scale(vs) == 4,
    ensures ({
        let ws = vs.push(Val::Num { coeff: c, scale: 4 });
        &&& num_mass_at(ws, 4) == num_mass_at(vs, 4) + abs(c)
        &&& all_of_kind(NumKind::Numeric, ws)
        &&& num_max_scale(ws) == 4
    }),
{
    let ws = vs.push(Val::Num { coeff: c, scale: 4 });
    assert(ws.drop_last() =~= vs);
    assert(ws.last() == Val::Num { coeff: c, scale: 4 });
    assert(pow10(0) == 1);
    assert(((4 - 4) as nat) == 0nat);
    assert(abs(c) * pow10(0) == abs(c));
    if vs.len() == 0 {
        assert(num_max_scale(vs) == 0);
    }
}

/// The absolute mass of the SUM's argument values at scale 4 is `gabs`.
pub proof fn lemma_members_mass(lo: int, hi: int, dlo: int, dhi: int, qhi: int, xs: Seq<Row>)
    ensures ({
        let g = qspec(lo, hi, dlo, dhi, qhi);
        let vs = column(members(g, xs, ek()), 0);
        &&& num_mass_at(vs, 4) == gabs(g, xs, ek(), 0)
        &&& all_of_kind(NumKind::Numeric, vs)
        &&& vs.len() == 0 || num_max_scale(vs) == 4
    }),
    decreases xs.len(),
{
    let g = qspec(lo, hi, dlo, dhi, qhi);
    let vs = column(members(g, xs, ek()), 0);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(lo, hi, dlo, dhi, qhi, xi);
        let mi = members(g, xi, ek());
        let vsi = column(mi, 0);
        assert((g.key)(x) == ek());
        if hit(g, x, ek()) {
            lemma_arg_vals(lo, hi, dlo, dhi, qhi, x);
            let c = ival(x[1]) * ival(x[2]);
            assert(members(g, xs, ek()) == mi.push(arg_vals(g, x)));
            assert(vs =~= vsi.push(Val::Num { coeff: c, scale: 4 }));
            assert((g.arg)(0, x) == c);
            lemma_mass_push(vsi, c);
        } else {
            assert(members(g, xs, ek()) == mi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// Beyond the capacity domain: the absolute mass of the SUM exceeds `i128`.
pub proof fn lemma_outcome_capacity(sv: StoresView, db: Database, ps: Seq<Literal>, lo: int, hi: int, dlo: int, dhi: int, qhi: int)
    requires
        bound_db(sv, db),
        bounds_ok(ps, lo, hi, dlo, dhi, qhi),
        gabs(qspec(lo, hi, dlo, dhi, qhi), xs_parts(lbf(sv)), ek(), 0) > i128_max(),
    ensures
        !capacity_domain(db, query_spec_at(ps)),
{
    let g = qspec(lo, hi, dlo, dhi, qhi);
    let rel = db.tables[0];
    let xd = proj_all(rel, cols4());
    let ctx = Seq::<Val>::empty();
    lemma_db_link(sv, db);
    lemma_agreement(sv, db, ps, lo, hi, dlo, dhi, qhi);
    lemma_acc_perm(g, xs_parts(lbf(sv)), xd, ek());
    lemma_filter_rows(db, Query::Table(0), rel, cols4(), q6_pred(ps), g);
    let kept = keep_true(rel, qual_truths(g, xd));
    lemma_kept_rows(g, rel, cols4());
    let args = Seq::new(kept.len(), |i: int| arg_vals(g, proj(kept[i], cols4())));
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] agg_args(db, ctx + kept[i], q6_aggs()) == Ok::<Row, SqlError>(args[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rel.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rel.len() && rel[m] == kept[i];
        assert((g.qual)(proj(rel[m], cols4())));
    }
    assert(args =~= qrows(g, xd).map_values(|x: Row| arg_vals(g, x)));
    lemma_scalar_members(g, xd);
    lemma_members_mass(lo, hi, dlo, dhi, qhi, xd);
    let vs = column(args, 0);
    assert(vs == column(members(g, xd, ek()), 0));
    assert(vs.len() != 0) by {
        if vs.len() == 0 {
            assert(num_mass_at(vs, 4) == 0);
        }
    }
    assert(!fits_agg_value(q6_aggs()[0], vs));
    assert(aggs_ok_inside(q6_aggs(), args));
    lemma_aggregate_capacity(db, ctx, q6_aggs(), Box::new(q6_filter(ps)), kept, args, 0);
    lemma_q6_ast(ps);
}

/// The WHERE condition errs on a typed row when `$1 + 1 year` errs.
pub proof fn lemma_row_pred_err(db: Database, r: Row, ps: Seq<Literal>, e: SqlError)
    requires
        param_domain(ps),
        eval_expr(closed_db(), Seq::empty(), hi_expr(ps)) == Err::<Val, SqlError>(e),
        row_typed(r),
    ensures
        eval_pred(db, r, q6_pred(ps)) == Err::<Truth, SqlError>(e),
{
    hide(eval_pred);
    hide(eval_expr);
    lemma_param_lits(ps);
    let lo = date_from_civil(ps[0]->Date_y, ps[0]->Date_m, ps[0]->Date_d);
    lemma_pred_ship_lo(db, r, ps, lo);
    lemma_expr_col(db, r, 10);
    lemma_hi_closed(ps);
    lemma_expr_closed(db, r, hi_expr(ps));
    lemma_cmp_err_right(db, r, CmpOp::Lt, Expr::Col(10), hi_expr(ps), e);
    lemma_and_err_right(db, r,
        Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(10), b: Expr::Lit(ps[0]) },
        Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(10), b: hi_expr(ps) }, e);
    lemma_and_err_left(db, r, pred_date(ps), pred_disc(ps), e);
    lemma_and_err_left(db, r, Pred::And(Box::new(pred_date(ps)), Box::new(pred_disc(ps))), pred_qty(ps), e);
}

/// `$1 + 1 year` outside the timestamp range on a non-empty table: the statement's meaning is that error.
pub proof fn lemma_outcome_err(sv: StoresView, db: Database, ps: Seq<Literal>, e: SqlError)
    requires
        bound_db(sv, db),
        param_domain(ps),
        eval_expr(closed_db(), Seq::empty(), hi_expr(ps)) == Err::<Val, SqlError>(e),
        n_rows(lbf(sv)) > 0,
    ensures
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)),
{
    hide(eval_pred);
    let rel = db.tables[0];
    let ctx = Seq::<Val>::empty();
    lemma_db_link(sv, db);
    assert forall|i: int| 0 <= i < rel.len() implies #[trigger] eval_pred(db, ctx + rel[i], q6_pred(ps)) == Err::<Truth, SqlError>(e) by {
        assert(ctx + rel[i] =~= rel[i]);
        lemma_row_pred_err(db, rel[i], ps, e);
    }
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(rel));
    crate::link::capacity::lemma_filter_err(db, ctx, q6_pred(ps), Box::new(Query::Table(0)), rel, e, 0);
    lemma_q6_ast(ps);
    crate::link::capacity::lemma_first_input(db, ctx, query_spec_at(ps).body);
}

} // verus!
