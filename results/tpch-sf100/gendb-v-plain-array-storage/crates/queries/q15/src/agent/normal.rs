//! TPC-H Q15's statement in pieces, its GROUP BY in the accumulator normal form of `link::query`, and the per-row
//! agreement of the AST with the normal form.
//!
//! The GROUP BY (`revenue0`) groups the `lineitem` rows shipped in `[$1, $1 + 3 months)` by `l_suppkey` and sums
//! `l_extendedprice * (1 - l_discount)` at scale 4. It occurs twice: as the right input of `supplier x revenue0`
//! (outer context empty) and inside the scalar subquery `SELECT MAX(total_revenue) FROM revenue0`, which is
//! evaluated under the 9-value row of `supplier x revenue0`, so its column references are shifted by 9. The pieces
//! below take that shift `o` as a parameter (`g_query(o, p0)`).
//!
//! The normal form reads a `lineitem` row through its projection onto `src_cols()` = (suppkey, extendedprice,
//! discount, shipdate): positions 0..4 of a projected row `x`. Its condition is `plo <= x[3] < phi` on days since
//! 2000-01-01 (`QBounds`), its key `[x[0]]`, its one aggregate the coefficient `price * (100 - discount)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::datetime::*;
use crate::spec::equality::row_not_distinct;
use crate::link::query::*;
use crate::link::expr::*;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::same_exact_type;
use crate::agent::common::group_ctx::*;

verus! {

// ------------------------------------------------------------------------------------------------ the normal form

/// Table columns of `lineitem` the normal form reads, in projected order.
pub open spec fn src_cols() -> Seq<nat> {
    seq![2nat, 5nat, 6nat, 10nat]
}

/// The shipdate window `[plo, phi)` in days since 2000-01-01.
pub struct QBounds {
    pub plo: int,
    pub phi: int,
}

/// WHERE on a projected row.
pub open spec fn q_qual(b: QBounds, x: Row) -> bool {
    &&& x[3] is Date
    &&& b.plo <= x[3]->Date_0
    &&& x[3]->Date_0 < b.phi
}

/// Coefficient of `l_extendedprice * (1 - l_discount)` (scale 4) of a projected row.
pub open spec fn rev_of(x: Row) -> int {
    ival(x[1]) * (100 - ival(x[2]))
}

/// The GROUP BY in normal form: key `l_suppkey`, one SUM at scale 4.
pub open spec fn q_spec(b: QBounds) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q_qual(b, x),
        key: |x: Row| seq![x[0]],
        arg: |j: int, x: Row| rev_of(x),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

// ------------------------------------------------------------------------------------------------ source rows

/// A numeric(15,2) value of a well-formed database.
pub open spec fn num15_2(v: Val) -> bool {
    v is Num && v->Num_scale == 2 && -1_000_000_000_000_000 < v->Num_coeff < 1_000_000_000_000_000
}

/// A `lineitem` row as a well-formed database holds it, on the columns the statement reads.
pub open spec fn li_row_ok(r: Row) -> bool {
    &&& r.len() == 16
    &&& r[2] is Int
    &&& num15_2(r[5])
    &&& num15_2(r[6])
    &&& r[10] is Date
}

/// Every row of the relation is a well-formed `lineitem` row.
pub open spec fn li_rows_ok(rows: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> li_row_ok(#[trigger] rows[i])
}

/// The projection of a table row.
pub proof fn lemma_proj_row(r: Row)
    requires r.len() == 16,
    ensures proj(r, src_cols()) == seq![r[2], r[5], r[6], r[10]],
{
    assert(proj(r, src_cols()) =~= seq![r[2], r[5], r[6], r[10]]);
}

// ------------------------------------------------------------------------------------------------ the statement's AST

/// `1::numeric` (the cast of the integer literal 1).
pub open spec fn e_one() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }
}

/// `l_extendedprice * (1 - l_discount)` with the `lineitem` columns at offset `o`.
pub open spec fn e_rev(o: nat) -> Expr {
    Expr::Arith {
        op: ArithOp::Mul,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Col(o + 5)),
        b: Box::new(Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(e_one()), b: Box::new(Expr::Col(o + 6)) }),
    }
}

/// `$1 + INTERVAL '3' MONTH` (a timestamp).
pub open spec fn e_q_end(p0: Literal) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p0)) }),
        months: 3i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `l_shipdate >= $1`.
pub open spec fn p_ge(o: nat, p0: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(o + 10), b: Expr::Lit(p0) }
}

/// `l_shipdate < $1 + INTERVAL '3' MONTH`.
pub open spec fn p_lt(o: nat, p0: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(o + 10), b: e_q_end(p0) }
}

/// The WHERE of `revenue0`.
pub open spec fn p_date(o: nat, p0: Literal) -> Pred {
    Pred::And(Box::new(p_ge(o, p0)), Box::new(p_lt(o, p0)))
}

pub open spec fn g_keys(o: nat) -> Seq<Expr> {
    seq![Expr::Col(o + 2)]
}

pub open spec fn g_aggs(o: nat) -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: e_rev(o) }]
}

pub open spec fn g_input(o: nat, p0: Literal) -> Query {
    Query::Filter { pred: p_date(o, p0), input: Box::new(Query::Table(0)) }
}

/// `revenue0`: `SELECT l_suppkey, SUM(..) FROM lineitem WHERE .. GROUP BY l_suppkey`.
pub open spec fn g_query(o: nat, p0: Literal) -> Query {
    Query::GroupBy { keys: g_keys(o), aggs: g_aggs(o), input: Box::new(g_input(o, p0)) }
}

/// `SELECT MAX(total_revenue) FROM revenue0` (under the 9-value row of `supplier x revenue0`).
pub open spec fn sub_query(p0: Literal) -> Query {
    Query::Aggregate { aggs: seq![Agg::Max(Expr::Col(10))], input: Box::new(g_query(9, p0)) }
}

/// `s_suppkey = supplier_no AND total_revenue = (SELECT MAX ..)`.
pub open spec fn body_pred(p0: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(7) }),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Subquery(Box::new(sub_query(p0))) }),
    )
}

pub open spec fn body_product(p0: Literal) -> Query {
    Query::Product { left: Box::new(Query::Table(5)), right: Box::new(g_query(0, p0)) }
}

pub open spec fn body_filter(p0: Literal) -> Query {
    Query::Filter { pred: body_pred(p0), input: Box::new(body_product(p0)) }
}

/// Output positions of a `supplier x revenue0` row: `s_suppkey, s_name, s_address, s_phone, total_revenue`.
pub open spec fn out_cols() -> Seq<nat> {
    seq![0nat, 1nat, 2nat, 4nat, 8nat]
}

pub open spec fn ast_body(p0: Literal) -> Query {
    Query::Project { exprs: col_exprs(out_cols()), input: Box::new(body_filter(p0)) }
}

/// `ORDER BY s_suppkey`.
pub open spec fn ast_order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The emitted statement is this AST.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        crate::query::query_spec_at(ps).body == ast_body(ps[0]),
        crate::query::query_spec_at(ps).keys == ast_order_keys(),
        crate::query::query_spec_at(ps).limit is None,
        crate::query::query_spec_at(ps).offset == 0,
{
    assert(col_exprs(out_cols()) =~= seq![Expr::Col(0), Expr::Col(1), Expr::Col(2), Expr::Col(4), Expr::Col(8)]);
    assert(g_keys(9) =~= seq![Expr::Col(11)]);
    assert(g_keys(0) =~= seq![Expr::Col(2)]);
}

/// The aggregate AST matches the normal form's kind.
pub proof fn lemma_aggs_match(o: nat, b: QBounds)
    ensures aggs_match(g_aggs(o), q_spec(b)),
{
    let g = q_spec(b);
    assert forall|j: int| 0 <= j < g_aggs(o).len() implies agg_matches(#[trigger] g_aggs(o)[j], g.aggs[j]) by {}
}

// ------------------------------------------------------------------------------------------------ the parameter

/// `pow10` at the exponents the per-row arithmetic uses.
pub proof fn lemma_pow10_small()
    ensures
        pow10(0) == 1,
        pow10(1) == 10,
        pow10(2) == 100,
        pow10(15) == 1_000_000_000_000_000,
        pow10(16) == 10_000_000_000_000_000,
{
    assert(pow10(0) == 1) by (compute);
    assert(pow10(1) == 10) by (compute);
    assert(pow10(2) == 100) by (compute);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert(pow10(16) == 10_000_000_000_000_000) by (compute);
}

/// `$1 + INTERVAL '3' MONTH` evaluates to the timestamp `t1` (it reads no column).
#[verifier::opaque]
pub open spec fn q_end_is(p0: Literal, t1: int) -> bool {
    forall|db: Database, env: Row| #[trigger] eval_expr(db, env, e_q_end(p0)) == Ok::<Val, SqlError>(Val::Ts(t1))
}

/// What the window is at the parameters `ps`: `$1` is the day `plo`, `t1` the timestamp `$1 + INTERVAL '3' MONTH`,
/// and `phi` the first day whose midnight is not before `t1`.
pub open spec fn bounds_ok(ps: Seq<Literal>, b: QBounds, t1: int) -> bool {
    &&& ps.len() == 1
    &&& lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(b.plo))
    &&& q_end_is(ps[0], t1)
    &&& (b.phi - 1) * usecs_per_day() < t1
    &&& t1 <= b.phi * usecs_per_day()
}

// ------------------------------------------------------------------------------------------------ per-row agreement
// Every lemma takes the environment `ctx ++ r` of a `lineitem` row `r` under an outer context of `|ctx|` values;
// the AST pieces read `r` at offset `|ctx|`.

/// A column of the row inside the environment.
pub proof fn lemma_env_col(ctx: Row, r: Row, j: int)
    requires 0 <= j < r.len(),
    ensures (ctx + r)[ctx.len() + j] == r[j], (ctx + r).len() == ctx.len() + r.len(),
{
}

/// The date condition on a table row.
pub proof fn lemma_date_pred_row(db: Database, ctx: Row, r: Row, ps: Seq<Literal>, b: QBounds, t1: int)
    requires li_row_ok(r), bounds_ok(ps, b, t1),
    ensures
        eval_pred(db, ctx + r, p_date(ctx.len(), ps[0])) == Ok::<Truth, SqlError>(truth_of(q_qual(b, proj(r, src_cols())))),
{
    let env = ctx + r;
    let o = ctx.len();
    let d = r[10]->Date_0;
    let u = usecs_per_day();
    lemma_env_col(ctx, r, 10);
    lemma_proj_row(r);
    assert(eval_expr(db, env, Expr::Col(o + 10)) == Ok::<Val, SqlError>(r[10]));
    assert(eval_expr(db, env, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Date(b.plo)));
    lemma_compare_date(d, b.plo);
    lemma_pred_cmp(db, env, CmpOp::Ge, Expr::Col(o + 10), Expr::Lit(ps[0]), r[10], Val::Date(b.plo), d, b.plo);
    assert(eval_expr(db, env, e_q_end(ps[0])) == Ok::<Val, SqlError>(Val::Ts(t1))) by {
        reveal(q_end_is);
    }
    assert(compare(Val::Date(d), Val::Ts(t1)) == Some(sign(d * u - t1)));
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(o + 10), e_q_end(ps[0]), r[10], Val::Ts(t1), d * u, t1);
    // `d * u < t1` exactly when `d < phi`: `t1` lies in `((phi - 1) * u, phi * u]`.
    assert((d * u < t1) == (d < b.phi)) by (nonlinear_arith)
        requires u == 86_400_000_000, (b.phi - 1) * u < t1, t1 <= b.phi * u;
    lemma_pred_and(db, env, p_ge(o, ps[0]), p_lt(o, ps[0]), d >= b.plo, d * u < t1);
}

/// The GROUP BY key on a table row is the normal form's key.
pub proof fn lemma_keys_row(db: Database, ctx: Row, r: Row, b: QBounds)
    requires li_row_ok(r),
    ensures eval_exprs(db, ctx + r, g_keys(ctx.len())) == Ok::<Row, SqlError>(((q_spec(b)).key)(proj(r, src_cols()))),
{
    let o = ctx.len();
    let idxs = seq![(o + 2) as nat];
    lemma_env_col(ctx, r, 2);
    lemma_proj_row(r);
    assert(col_exprs(idxs) =~= g_keys(o));
    lemma_eval_cols(db, ctx + r, idxs);
    assert(select(ctx + r, idxs) =~= seq![r[2]]);
}

/// `1::numeric` is `Num { 1, 0 }`.
pub proof fn lemma_eval_one(db: Database, env: Row)
    ensures eval_expr(db, env, e_one()) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }),
{
    let l = Literal::Int { v: 1, kind: IntKind::Int4 };
    assert(int_in_range(IntKind::Int4, 1));
    assert(lit_val(l) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, env, Expr::Lit(l)) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(cast(CastOp::IntToNumeric, Val::Int(1)) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
}

/// `1 - c` of a numeric(15,2) value at position `i` of the environment: scale 2, coefficient `100 - c`, below
/// `10^16`.
pub proof fn lemma_one_minus_col(db: Database, env: Row, i: nat)
    requires i < env.len(), num15_2(env[i as int]),
    ensures ({
        let c = env[i as int]->Num_coeff;
        &&& eval_expr(db, env, Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(e_one()), b: Box::new(Expr::Col(i)) })
                == Ok::<Val, SqlError>(Val::Num { coeff: 100 - c, scale: 2 })
        &&& abs(100 - c) < pow10(16)
    }),
{
    lemma_eval_one(db, env);
    lemma_pow10_small();
    let c = env[i as int]->Num_coeff;
    assert(eval_expr(db, env, Expr::Col(i)) == Ok::<Val, SqlError>(env[i as int]));
    assert(max_nat(0, 2) == 2);
    lemma_node_add(db, env, ArithOp::Sub, e_one(), Expr::Col(i), 1, 0, 1, c, 2, 15, 2, 100, 1, 16);
}

/// `l_extendedprice * (1 - l_discount)` on a table row: the exact product at scale 4, below `10^31`.
pub proof fn lemma_eval_rev(db: Database, ctx: Row, r: Row)
    requires li_row_ok(r),
    ensures
        eval_expr(db, ctx + r, e_rev(ctx.len())) == Ok::<Val, SqlError>(Val::Num { coeff: rev_of(proj(r, src_cols())), scale: 4 }),
        abs(rev_of(proj(r, src_cols()))) < pow10(31),
{
    let env = ctx + r;
    let o = ctx.len();
    lemma_env_col(ctx, r, 5);
    lemma_env_col(ctx, r, 6);
    lemma_proj_row(r);
    lemma_pow10_small();
    lemma_one_minus_col(db, env, (o + 6) as nat);
    let p = r[5]->Num_coeff;
    let d = r[6]->Num_coeff;
    assert(eval_expr(db, env, Expr::Col(o + 5)) == Ok::<Val, SqlError>(r[5]));
    let sub = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(e_one()), b: Box::new(Expr::Col(o + 6)) };
    lemma_node_mul(db, env, Expr::Col(o + 5), sub, p, 2, 15, 100 - d, 2, 16);
}

/// The aggregate arguments on a table row are the normal form's argument values.
pub proof fn lemma_args_row(db: Database, ctx: Row, r: Row, b: QBounds)
    requires li_row_ok(r),
    ensures agg_args(db, ctx + r, g_aggs(ctx.len())) == Ok::<Row, SqlError>(arg_vals(q_spec(b), proj(r, src_cols()))),
{
    hide(eval_expr);
    hide(agg_arg);
    let env = ctx + r;
    let aggs = g_aggs(ctx.len());
    let vals = arg_vals(q_spec(b), proj(r, src_cols()));
    lemma_agg_arg_results_index(db, env, aggs);
    let rs = agg_arg_results(db, env, aggs);
    lemma_agg_arg_sum(db, env, NumKind::Numeric, e_rev(ctx.len()));
    lemma_eval_rev(db, ctx, r);
    assert(vals.len() == 1);
    assert(rs[0] == Ok::<Val, SqlError>(vals[0]));
    lemma_collect_all(rs, vals);
    crate::exec::relational::domain::lemma_agg_args(db, env, aggs);
}

/// The WHERE, key and arguments agree with the normal form on every row of a relation of table rows, under any
/// outer context.
pub proof fn lemma_agree_at(db: Database, ctx: Row, rows: Seq<Row>, ps: Seq<Literal>, b: QBounds, t1: int)
    requires li_rows_ok(rows), bounds_ok(ps, b, t1),
    ensures
        pred_agrees_at(db, ctx, rows, src_cols(), p_date(ctx.len(), ps[0]), q_spec(b)),
        keys_agree_at(db, ctx, rows, src_cols(), g_keys(ctx.len()), q_spec(b)),
        args_agree_at(db, ctx, rows, src_cols(), g_aggs(ctx.len()), q_spec(b)),
{
    let g = q_spec(b);
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, ctx + #[trigger] rows[i], p_date(ctx.len(), ps[0])) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], src_cols())))) by {
        lemma_date_pred_row(db, ctx, rows[i], ps, b, t1);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], src_cols())) implies
        eval_exprs(db, ctx + rows[i], g_keys(ctx.len())) == Ok::<Row, SqlError>((g.key)(proj(rows[i], src_cols()))) by {
        lemma_keys_row(db, ctx, rows[i], b);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], src_cols())) implies
        agg_args(db, ctx + rows[i], g_aggs(ctx.len())) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], src_cols()))) by {
        lemma_args_row(db, ctx, rows[i], b);
    }
}

/// The keys of the projected rows are one-integer rows: SQL "not distinct" is equality.
pub proof fn lemma_keys_exact(rows: Seq<Row>, b: QBounds)
    requires li_rows_ok(rows),
    ensures keys_exact(q_spec(b), proj_all(rows, src_cols())),
{
    let g = q_spec(b);
    let xs = proj_all(rows, src_cols());
    assert forall|a: int, c: int| 0 <= a < xs.len() && 0 <= c < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[c]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[c])) <==> (g.key)(xs[a]) == (g.key)(xs[c])) by {
        lemma_proj_row(rows[a]);
        lemma_proj_row(rows[c]);
        let ka = (g.key)(xs[a]);
        let kc = (g.key)(xs[c]);
        assert(ka[0] is Int && kc[0] is Int);
        assert forall|i: int| 0 <= i < ka.len() implies same_exact_type(#[trigger] ka[i], kc[i]) by {}
        lemma_row_exact(ka, kc);
    }
}

} // verus!
