//! TPC-H Q6 in the accumulator normal form of `link::query` (`QuerySpec`, scalar mode), the statement's AST, and the
//! per-row agreement of the AST with the normal form.
//!
//! The FROM relation is `lineitem`; the normal form reads its projection onto `src_cols()` = (quantity,
//! extendedprice, discount, shipdate), positions 0..4 of a projected row `x`. The WHERE condition is
//! `plo <= x[3] < phi && dlo <= x[2] <= dhi && x[0] < qlim` (`QBounds`: days since 2000-01-01 and scale-2
//! coefficients); the one aggregate sums `price * discount` at scale 4. The bounds come from the parameters
//! (`bounds_ok`): `plo` is `$1`, `phi` the first day not before `$1 + INTERVAL '1' YEAR` (a timestamp `t1`),
//! `dlo/dhi` are `$2 -/+ 0.01`, `qlim` is `100 * $3`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::datetime::*;
use crate::spec::typing::*;
use crate::link::query::*;
use crate::link::expr::*;
use crate::bridge::collect::lemma_collect_all;

verus! {

// ------------------------------------------------------------------------------------------------ the normal form

/// Table columns of `lineitem` the normal form reads, in projected order.
pub open spec fn src_cols() -> Seq<nat> {
    seq![4nat, 5nat, 6nat, 10nat]
}

/// The WHERE bounds: shipdate in `[plo, phi)` (days since 2000-01-01), discount coefficient in `[dlo, dhi]`,
/// quantity coefficient below `qlim`.
pub struct QBounds {
    pub plo: int,
    pub phi: int,
    pub dlo: int,
    pub dhi: int,
    pub qlim: int,
}

/// WHERE on a projected row.
pub open spec fn q6_qual(b: QBounds, x: Row) -> bool {
    &&& x[3] is Date
    &&& b.plo <= x[3]->Date_0
    &&& x[3]->Date_0 < b.phi
    &&& b.dlo <= ival(x[2])
    &&& ival(x[2]) <= b.dhi
    &&& ival(x[0]) < b.qlim
}

/// Coefficient of `l_extendedprice * l_discount` (scale 4).
pub open spec fn q6_arg(x: Row) -> int {
    ival(x[1]) * ival(x[2])
}

/// The normal form of Q6 under the bounds `b`.
pub open spec fn q6_spec(b: QBounds) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q6_qual(b, x),
        key: |x: Row| Seq::<Val>::empty(),
        arg: |j: int, x: Row| q6_arg(x),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat],
        grouped: false,
    }
}

// ------------------------------------------------------------------------------------------------ source rows

/// A numeric(15,2) value of a well-formed database.
pub open spec fn num15_2(v: Val) -> bool {
    v is Num && v->Num_scale == 2 && -1_000_000_000_000_000 < v->Num_coeff < 1_000_000_000_000_000
}

/// A `lineitem` row as a well-formed database holds it, on the columns Q6 reads.
pub open spec fn table_row_ok(r: Row) -> bool {
    &&& r.len() == 16
    &&& r[4] is Num && r[4]->Num_scale == 2
    &&& num15_2(r[5])
    &&& num15_2(r[6])
    &&& r[10] is Date
}

/// The projection of a table row.
pub proof fn lemma_proj_row(r: Row)
    requires r.len() == 16,
    ensures proj(r, src_cols()) == seq![r[4], r[5], r[6], r[10]],
{
    assert(proj(r, src_cols()) =~= seq![r[4], r[5], r[6], r[10]]);
}

// ------------------------------------------------------------------------------------------------ the statement's AST

/// `$1 + INTERVAL '1' YEAR` (a timestamp).
pub open spec fn e_year_end(p0: Literal) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p0)) }),
        months: 12i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `$2 - 0.01` (`op` Sub) or `$2 + 0.01` (`op` Add).
pub open spec fn e_disc_bound(op: ArithOp, p1: Literal) -> Expr {
    Expr::Arith {
        op,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Lit(p1)),
        b: Box::new(Expr::Lit(Literal::Num { coeff: 1, scale: 2 })),
    }
}

/// `l_shipdate >= $1 AND l_shipdate < $1 + INTERVAL '1' YEAR`.
pub open spec fn ast_date_pred(p0: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(10), b: Expr::Lit(p0) }),
        Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(10), b: e_year_end(p0) }),
    )
}

/// `l_discount BETWEEN $2 - 0.01 AND $2 + 0.01`.
pub open spec fn ast_disc_pred(p1: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(6), b: e_disc_bound(ArithOp::Sub, p1) }),
        Box::new(Pred::Cmp { op: CmpOp::Le, a: Expr::Col(6), b: e_disc_bound(ArithOp::Add, p1) }),
    )
}

/// `l_quantity < $3` (the integer cast to numeric).
pub open spec fn ast_qty_pred(p2: Literal) -> Pred {
    Pred::Cmp {
        op: CmpOp::Lt,
        a: Expr::Col(4),
        b: Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(p2)) },
    }
}

/// The WHERE condition.
pub open spec fn ast_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(Box::new(ast_date_pred(ps[0])), Box::new(ast_disc_pred(ps[1])))),
        Box::new(ast_qty_pred(ps[2])),
    )
}

/// `l_extendedprice * l_discount`.
pub open spec fn e_revenue() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(5)), b: Box::new(Expr::Col(6)) }
}

pub open spec fn ast_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: e_revenue() }]
}

pub open spec fn ast_input(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: ast_pred(ps), input: Box::new(Query::Table(0)) }
}

pub open spec fn ast_body(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: ast_aggs(), input: Box::new(ast_input(ps)) }
}

/// The emitted statement is this AST.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        crate::query::query_spec_at(ps).body == ast_body(ps),
        crate::query::query_spec_at(ps).keys.len() == 0,
        crate::query::query_spec_at(ps).limit is None,
        crate::query::query_spec_at(ps).offset == 0,
{
}

/// The aggregate AST matches the normal form's kind.
pub proof fn lemma_aggs_match(b: QBounds)
    ensures aggs_match(ast_aggs(), q6_spec(b)), scalar_key(q6_spec(b)),
{
    let g = q6_spec(b);
    assert forall|j: int| 0 <= j < ast_aggs().len() implies agg_matches(#[trigger] ast_aggs()[j], g.aggs[j]) by {}
}

// ------------------------------------------------------------------------------------------------ the parameters

/// `pow10` at the exponents the per-row arithmetic uses.
pub proof fn lemma_pow10_small()
    ensures
        pow10(0) == 1,
        pow10(1) == 10,
        pow10(2) == 100,
        pow10(15) == 1_000_000_000_000_000,
{
    assert(pow10(0) == 1) by (compute);
    assert(pow10(1) == 10) by (compute);
    assert(pow10(2) == 100) by (compute);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
}

/// `$1 + INTERVAL '1' YEAR` evaluates to the timestamp `t1` (it reads no column).
#[verifier::opaque]
pub open spec fn year_end_is(p0: Literal, t1: int) -> bool {
    forall|db: Database, env: Row| #[trigger] eval_expr(db, env, e_year_end(p0)) == Ok::<Val, SqlError>(Val::Ts(t1))
}

/// What the WHERE bounds are at the parameters `ps`: `t1` is the timestamp `$1 + INTERVAL '1' YEAR`.
pub open spec fn bounds_ok(ps: Seq<Literal>, b: QBounds, t1: int) -> bool {
    &&& ps.len() == 3
    &&& lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(b.plo))
    &&& year_end_is(ps[0], t1)
    &&& (b.phi - 1) * usecs_per_day() < t1
    &&& t1 <= b.phi * usecs_per_day()
    &&& ps[1] is Num
    &&& ps[1]->Num_scale == 2
    &&& -1_000_000_000_000_000 < ps[1]->Num_coeff < 1_000_000_000_000_000
    &&& b.dlo == ps[1]->Num_coeff - 1
    &&& b.dhi == ps[1]->Num_coeff + 1
    &&& ps[2] is Int
    &&& ps[2]->Int_kind == IntKind::Int4
    &&& int_in_range(IntKind::Int4, ps[2]->Int_v)
    &&& b.qlim == 100 * ps[2]->Int_v
}

// ------------------------------------------------------------------------------------------------ per-row agreement

/// The date conjunct on a table row.
pub proof fn lemma_date_pred_row(db: Database, r: Row, ps: Seq<Literal>, b: QBounds, t1: int)
    requires table_row_ok(r), bounds_ok(ps, b, t1),
    ensures ({
        let d = r[10]->Date_0;
        eval_pred(db, r, ast_date_pred(ps[0])) == Ok::<Truth, SqlError>(truth_of(b.plo <= d && d < b.phi))
    }),
{
    let d = r[10]->Date_0;
    let u = usecs_per_day();
    assert(eval_expr(db, r, Expr::Col(10)) == Ok::<Val, SqlError>(r[10]));
    assert(eval_expr(db, r, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Date(b.plo)));
    lemma_compare_date(d, b.plo);
    lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(10), Expr::Lit(ps[0]), r[10], Val::Date(b.plo), d, b.plo);
    assert(eval_expr(db, r, e_year_end(ps[0])) == Ok::<Val, SqlError>(Val::Ts(t1))) by {
        reveal(year_end_is);
    }
    assert(compare(Val::Date(d), Val::Ts(t1)) == Some(sign(d * u - t1)));
    lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(10), e_year_end(ps[0]), r[10], Val::Ts(t1), d * u, t1);
    // `d * u < t1` exactly when `d < phi`: `t1` lies in `((phi - 1) * u, phi * u]`.
    assert((d * u < t1) == (d < b.phi)) by (nonlinear_arith)
        requires u == 86_400_000_000, (b.phi - 1) * u < t1, t1 <= b.phi * u;
    lemma_pred_and(db, r,
        Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(10), b: Expr::Lit(ps[0]) },
        Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(10), b: e_year_end(ps[0]) },
        d >= b.plo, d * u < t1);
}

/// `$2 -/+ 0.01` evaluates to the coefficient `p1 -/+ 1` at scale 2.
pub proof fn lemma_disc_bound(db: Database, env: Row, op: ArithOp, p1: Literal)
    requires
        !(op is Mul),
        p1 is Num,
        p1->Num_scale == 2,
        -1_000_000_000_000_000 < p1->Num_coeff < 1_000_000_000_000_000,
    ensures
        eval_expr(db, env, e_disc_bound(op, p1)) == Ok::<Val, SqlError>(Val::Num {
            coeff: if op is Add { p1->Num_coeff + 1 } else { p1->Num_coeff - 1 },
            scale: 2,
        }),
{
    lemma_pow10_small();
    let c = p1->Num_coeff;
    let one = Literal::Num { coeff: 1, scale: 2 };
    lemma_digits_in_range(c, 2, 15);
    lemma_digits_in_range(1, 2, 1);
    assert(eval_expr(db, env, Expr::Lit(p1)) == Ok::<Val, SqlError>(Val::Num { coeff: c, scale: 2 }));
    assert(eval_expr(db, env, Expr::Lit(one)) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 2 }));
    assert(max_nat(2, 2) == 2);
    lemma_node_add(db, env, op, Expr::Lit(p1), Expr::Lit(one), c, 2, 15, 1, 2, 1, 2, 1, 1, 16);
}

/// The discount conjunct on a table row.
pub proof fn lemma_disc_pred_row(db: Database, r: Row, ps: Seq<Literal>, b: QBounds, t1: int)
    requires table_row_ok(r), bounds_ok(ps, b, t1),
    ensures ({
        let x = r[6]->Num_coeff;
        eval_pred(db, r, ast_disc_pred(ps[1])) == Ok::<Truth, SqlError>(truth_of(b.dlo <= x && x <= b.dhi))
    }),
{
    let x = r[6]->Num_coeff;
    assert(eval_expr(db, r, Expr::Col(6)) == Ok::<Val, SqlError>(r[6]));
    lemma_disc_bound(db, r, ArithOp::Sub, ps[1]);
    lemma_disc_bound(db, r, ArithOp::Add, ps[1]);
    lemma_compare_num(x, 2, b.dlo, 2);
    lemma_compare_num(x, 2, b.dhi, 2);
    lemma_align_same(x, 2);
    lemma_align_same(b.dlo, 2);
    lemma_align_same(b.dhi, 2);
    assert(max_nat(2, 2) == 2);
    lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(6), e_disc_bound(ArithOp::Sub, ps[1]), r[6],
        Val::Num { coeff: b.dlo, scale: 2 }, x, b.dlo);
    lemma_pred_cmp(db, r, CmpOp::Le, Expr::Col(6), e_disc_bound(ArithOp::Add, ps[1]), r[6],
        Val::Num { coeff: b.dhi, scale: 2 }, x, b.dhi);
    lemma_pred_and(db, r,
        Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(6), b: e_disc_bound(ArithOp::Sub, ps[1]) },
        Pred::Cmp { op: CmpOp::Le, a: Expr::Col(6), b: e_disc_bound(ArithOp::Add, ps[1]) },
        x >= b.dlo, x <= b.dhi);
}

/// The integer literal `$3`.
pub proof fn lemma_int_lit(p2: Literal)
    requires p2 is Int, p2->Int_kind == IntKind::Int4, int_in_range(IntKind::Int4, p2->Int_v),
    ensures lit_val(p2) == Ok::<Val, SqlError>(Val::Int(p2->Int_v)),
{
}

/// `$3::numeric` evaluates to the integer at scale 0.
pub proof fn lemma_qty_bound(db: Database, env: Row, p2: Literal)
    requires p2 is Int, p2->Int_kind == IntKind::Int4, int_in_range(IntKind::Int4, p2->Int_v),
    ensures
        eval_expr(db, env, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(p2)) })
            == Ok::<Val, SqlError>(Val::Num { coeff: p2->Int_v, scale: 0 }),
{
    hide(lit_val);
    lemma_int_lit(p2);
    assert(eval_expr(db, env, Expr::Lit(p2)) == Ok::<Val, SqlError>(Val::Int(p2->Int_v)));
}

/// A scale-2 coefficient against an integer at scale 0: the order of `q` and `100 * v`.
pub proof fn lemma_compare_qty(q: int, v: int)
    ensures compare(Val::Num { coeff: q, scale: 2 }, Val::Num { coeff: v, scale: 0 }) == Some(sign(q - v * 100)),
{
    assert(pow10(2) == 100) by (compute);
    lemma_compare_num(q, 2, v, 0);
    assert(max_nat(2, 0) == 2);
    lemma_align_same(q, 2);
    lemma_align_by(v, 0, 2, 100);
}

/// The quantity conjunct on a table row.
pub proof fn lemma_qty_pred_row(db: Database, r: Row, ps: Seq<Literal>, b: QBounds, t1: int)
    requires table_row_ok(r), bounds_ok(ps, b, t1),
    ensures ({
        let q = r[4]->Num_coeff;
        eval_pred(db, r, ast_qty_pred(ps[2])) == Ok::<Truth, SqlError>(truth_of(q < b.qlim))
    }),
{
    let q = r[4]->Num_coeff;
    let v = ps[2]->Int_v;
    let cst = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(ps[2])) };
    assert(eval_expr(db, r, Expr::Col(4)) == Ok::<Val, SqlError>(r[4]));
    lemma_qty_bound(db, r, ps[2]);
    lemma_compare_qty(q, v);
    lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(4), cst, r[4], Val::Num { coeff: v, scale: 0 }, q, v * 100);
}

/// The WHERE condition on one table row is the normal form's condition.
pub proof fn lemma_pred_row(db: Database, r: Row, ps: Seq<Literal>, b: QBounds, t1: int)
    requires table_row_ok(r), bounds_ok(ps, b, t1),
    ensures eval_pred(db, r, ast_pred(ps)) == Ok::<Truth, SqlError>(truth_of(q6_qual(b, proj(r, src_cols())))),
{
    let d = r[10]->Date_0;
    let x = r[6]->Num_coeff;
    let q = r[4]->Num_coeff;
    lemma_date_pred_row(db, r, ps, b, t1);
    lemma_disc_pred_row(db, r, ps, b, t1);
    lemma_qty_pred_row(db, r, ps, b, t1);
    lemma_pred_and(db, r, ast_date_pred(ps[0]), ast_disc_pred(ps[1]), b.plo <= d && d < b.phi, b.dlo <= x && x <= b.dhi);
    lemma_pred_and(db, r, Pred::And(Box::new(ast_date_pred(ps[0])), Box::new(ast_disc_pred(ps[1]))), ast_qty_pred(ps[2]),
        (b.plo <= d && d < b.phi) && (b.dlo <= x && x <= b.dhi), q < b.qlim);
    lemma_proj_row(r);
}

/// The WHERE condition agrees with the normal form on every row of a table of well-formed rows.
pub proof fn lemma_pred_agrees(db: Database, rows: Seq<Row>, ps: Seq<Literal>, b: QBounds, t1: int)
    requires
        forall|i: int| 0 <= i < rows.len() ==> table_row_ok(#[trigger] rows[i]),
        bounds_ok(ps, b, t1),
    ensures pred_agrees(db, rows, src_cols(), ast_pred(ps), q6_spec(b)),
{
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], ast_pred(ps)) == Ok::<Truth, SqlError>(truth_of((q6_spec(b).qual)(proj(rows[i], src_cols())))) by {
        lemma_pred_row(db, rows[i], ps, b, t1);
    }
}

/// `l_extendedprice * l_discount` on one table row: the exact product at scale 4.
pub proof fn lemma_eval_revenue(db: Database, r: Row)
    requires table_row_ok(r),
    ensures
        eval_expr(db, r, e_revenue()) == Ok::<Val, SqlError>(Val::Num { coeff: q6_arg(proj(r, src_cols())), scale: 4 }),
{
    lemma_proj_row(r);
    lemma_pow10_small();
    assert(eval_expr(db, r, Expr::Col(5)) == Ok::<Val, SqlError>(r[5]));
    assert(eval_expr(db, r, Expr::Col(6)) == Ok::<Val, SqlError>(r[6]));
    lemma_node_mul(db, r, Expr::Col(5), Expr::Col(6), r[5]->Num_coeff, 2, 15, r[6]->Num_coeff, 2, 15);
}

/// The aggregate arguments on one table row are the normal form's argument values.
pub proof fn lemma_args_row(db: Database, r: Row, b: QBounds)
    requires table_row_ok(r),
    ensures agg_args(db, r, ast_aggs()) == Ok::<Row, SqlError>(arg_vals(q6_spec(b), proj(r, src_cols()))),
{
    hide(eval_expr);
    hide(agg_arg);
    let aggs = ast_aggs();
    let x = proj(r, src_cols());
    let vals = arg_vals(q6_spec(b), x);
    lemma_agg_arg_results_index(db, r, aggs);
    let rs = agg_arg_results(db, r, aggs);
    lemma_agg_arg_sum(db, r, NumKind::Numeric, e_revenue());
    lemma_eval_revenue(db, r);
    assert(vals.len() == 1);
    assert(rs[0] == Ok::<Val, SqlError>(vals[0]));
    lemma_collect_all(rs, vals);
    crate::exec::relational::domain::lemma_agg_args(db, r, aggs);
}

/// The aggregate arguments agree with the normal form on every row of a table of well-formed rows.
pub proof fn lemma_args_agree(db: Database, rows: Seq<Row>, b: QBounds)
    requires forall|i: int| 0 <= i < rows.len() ==> table_row_ok(#[trigger] rows[i]),
    ensures args_agree(db, rows, src_cols(), ast_aggs(), q6_spec(b)),
{
    assert forall|i: int| 0 <= i < rows.len() && (q6_spec(b).qual)(proj(#[trigger] rows[i], src_cols())) implies
        agg_args(db, rows[i], ast_aggs()) == Ok::<Row, SqlError>(arg_vals(q6_spec(b), proj(rows[i], src_cols()))) by {
        lemma_args_row(db, rows[i], b);
    }
}

} // verus!
