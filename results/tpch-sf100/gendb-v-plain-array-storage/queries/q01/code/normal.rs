//! TPC-H Q1 in the accumulator normal form of `link::query` (`QuerySpec`), and the per-row agreement of the
//! statement's AST with it.
//!
//! The FROM relation is `lineitem`; the normal form reads its projection onto `src_cols()` =
//! (quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate), positions 0..7 of a projected
//! row `x`. The group key is `(x[4], x[5])`; the WHERE condition is `x[6] <= pd` (days since 2000-01-01).
//! Aggregate `j` sums the exact argument coefficient `q1_arg(j, x)`:
//!   0 SUM(qty) scale 2, 1 SUM(price) scale 2, 2 SUM(price*(1-disc)) scale 4,
//!   3 SUM(price*(1-disc)*(1+tax)) scale 6, 4 AVG(qty), 5 AVG(price), 6 AVG(disc) (scale 2), 7 COUNT(*).
//! Every numeric(15,2) value of a well-formed database has a coefficient below `10^15` in absolute value
//! (`coeff_bound`), so the per-row arithmetic stays far inside PostgreSQL's numeric format.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::datetime::*;
use crate::link::query::*;
use crate::link::expr::{ival, lemma_compare_date, lemma_expr_col};
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::same_exact_type;
use crate::spec::equality::row_not_distinct;

verus! {

// ------------------------------------------------------------------------------------------------ the normal form

/// Table columns of `lineitem` the normal form reads, in projected order.
pub open spec fn src_cols() -> Seq<nat> {
    seq![4nat, 5nat, 6nat, 7nat, 8nat, 9nat, 10nat]
}

/// Exclusive bound of the absolute coefficient of a numeric(15,2) value: `10^15`.
pub open spec fn coeff_bound() -> int {
    1_000_000_000_000_000
}

/// WHERE `l_shipdate <= pd` on a projected row.
pub open spec fn q1_qual(pd: int, x: Row) -> bool {
    match x[6] {
        Val::Date(d) => d <= pd,
        _ => false,
    }
}

/// GROUP BY key `(l_returnflag, l_linestatus)` of a projected row.
pub open spec fn q1_key(x: Row) -> Row {
    seq![x[4], x[5]]
}

/// Coefficient of `l_extendedprice * (1 - l_discount)` (scale 4).
pub open spec fn disc_price(x: Row) -> int {
    ival(x[1]) * (100 - ival(x[2]))
}

/// Coefficient of `l_extendedprice * (1 - l_discount) * (1 + l_tax)` (scale 6).
pub open spec fn charge(x: Row) -> int {
    disc_price(x) * (100 + ival(x[3]))
}

/// Argument coefficient of aggregate `j` on a projected row.
pub open spec fn q1_arg(j: int, x: Row) -> int {
    if j == 0 || j == 4 {
        ival(x[0])
    } else if j == 1 || j == 5 {
        ival(x[1])
    } else if j == 2 {
        disc_price(x)
    } else if j == 3 {
        charge(x)
    } else if j == 6 {
        ival(x[2])
    } else {
        0
    }
}

pub open spec fn q1_aggs() -> Seq<AggKind> {
    seq![
        AggKind::Sum { scale: 2 },
        AggKind::Sum { scale: 2 },
        AggKind::Sum { scale: 4 },
        AggKind::Sum { scale: 6 },
        AggKind::Avg { scale: 2 },
        AggKind::Avg { scale: 2 },
        AggKind::Avg { scale: 2 },
        AggKind::Count
    ]
}

/// Output columns: the key, then every aggregate (`key ++ aggregates` unchanged).
pub open spec fn q1_outs() -> Seq<nat> {
    seq![0nat, 1nat, 2nat, 3nat, 4nat, 5nat, 6nat, 7nat, 8nat, 9nat]
}

/// The normal form of Q1 at the parameter date `pd` (days since 2000-01-01).
pub open spec fn q1_spec(pd: int) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q1_qual(pd, x),
        key: |x: Row| q1_key(x),
        arg: |j: int, x: Row| q1_arg(j, x),
        aggs: q1_aggs(),
        outs: q1_outs(),
        grouped: true,
    }
}

// ------------------------------------------------------------------------------------------------ source rows

/// A numeric(15,2) value of a well-formed database.
pub open spec fn num15_2(v: Val) -> bool {
    v is Num && v->Num_scale == 2 && -coeff_bound() < v->Num_coeff < coeff_bound()
}

/// A `lineitem` row as a well-formed database holds it, on the columns Q1 reads.
pub open spec fn table_row_ok(r: Row) -> bool {
    &&& r.len() == 16
    &&& num15_2(r[4])
    &&& num15_2(r[5])
    &&& num15_2(r[6])
    &&& num15_2(r[7])
    &&& r[8] is Text
    &&& r[9] is Text
    &&& r[10] is Date
}

/// The same facts on a projected row (positions 0..7).
pub open spec fn src_row_ok(x: Row) -> bool {
    &&& x.len() == 7
    &&& num15_2(x[0])
    &&& num15_2(x[1])
    &&& num15_2(x[2])
    &&& num15_2(x[3])
    &&& x[4] is Text
    &&& x[5] is Text
    &&& x[6] is Date
}

pub proof fn lemma_proj_row_ok(r: Row)
    requires table_row_ok(r),
    ensures
        src_row_ok(proj(r, src_cols())),
        proj(r, src_cols()) == seq![r[4], r[5], r[6], r[7], r[8], r[9], r[10]],
{
    let x = proj(r, src_cols());
    assert(x =~= seq![r[4], r[5], r[6], r[7], r[8], r[9], r[10]]);
}

// ------------------------------------------------------------------------------------------------ the statement's AST

/// `1::numeric` (the cast of the integer literal 1).
pub open spec fn e_one() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn e_disc_price() -> Expr {
    Expr::Arith {
        op: ArithOp::Mul,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Col(5)),
        b: Box::new(Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(e_one()), b: Box::new(Expr::Col(6)) }),
    }
}

/// `1 + l_tax`.
pub open spec fn e_one_plus_tax() -> Expr {
    Expr::Arith { op: ArithOp::Add, kind: NumKind::Numeric, a: Box::new(e_one()), b: Box::new(Expr::Col(7)) }
}

/// `l_extendedprice * (1 - l_discount) * (1 + l_tax)`.
pub open spec fn e_charge() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(e_disc_price()), b: Box::new(e_one_plus_tax()) }
}

pub open spec fn ast_keys() -> Seq<Expr> {
    seq![Expr::Col(8), Expr::Col(9)]
}

pub open spec fn ast_aggs() -> Seq<Agg> {
    seq![
        Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(4) },
        Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(5) },
        Agg::Sum { kind: NumKind::Numeric, arg: e_disc_price() },
        Agg::Sum { kind: NumKind::Numeric, arg: e_charge() },
        Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(4) },
        Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(5) },
        Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(6) },
        Agg::CountStar
    ]
}

/// WHERE `l_shipdate <= $1`.
pub open spec fn ast_pred(p: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Le, a: Expr::Col(10), b: Expr::Lit(p) }
}

pub open spec fn ast_input(p: Literal) -> Query {
    Query::Filter { pred: ast_pred(p), input: Box::new(Query::Table(0)) }
}

pub open spec fn ast_body(p: Literal) -> Query {
    Query::GroupBy { keys: ast_keys(), aggs: ast_aggs(), input: Box::new(ast_input(p)) }
}

pub open spec fn ast_order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }, OrderKey { col: 1, desc: false, nulls_first: false }]
}

/// The emitted statement is this AST.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        crate::query::query_spec_at(ps).body == ast_body(ps[0]),
        crate::query::query_spec_at(ps).keys == ast_order_keys(),
        crate::query::query_spec_at(ps).limit is None,
        crate::query::query_spec_at(ps).offset == 0,
{
}

/// The aggregate ASTs match the normal form's kinds.
pub proof fn lemma_aggs_match(pd: int)
    ensures aggs_match(ast_aggs(), q1_spec(pd)),
{
    let g = q1_spec(pd);
    assert forall|j: int| 0 <= j < ast_aggs().len() implies agg_matches(#[trigger] ast_aggs()[j], g.aggs[j]) by {
        if j == 0 {} else if j == 1 {} else if j == 2 {} else if j == 3 {} else if j == 4 {} else if j == 5 {} else if j == 6 {} else {}
    }
}

// ------------------------------------------------------------------------------------------------ per-row agreement

/// The WHERE condition on one table row is the normal form's condition.
pub proof fn lemma_pred_row(db: Database, r: Row, p: Literal, pd: int)
    requires
        table_row_ok(r),
        lit_val(p) == Ok::<Val, SqlError>(Val::Date(pd)),
    ensures
        eval_pred(db, r, ast_pred(p)) == Ok::<Truth, SqlError>(truth_of(q1_qual(pd, proj(r, src_cols())))),
{
    lemma_proj_row_ok(r);
    let d = r[10]->Date_0;
    lemma_compare_date(d, pd);
    assert(eval_expr(db, r, Expr::Col(10)) == Ok::<Val, SqlError>(Val::Date(d)));
    assert(eval_expr(db, r, Expr::Lit(p)) == Ok::<Val, SqlError>(Val::Date(pd)));
    assert(cmp_truth(CmpOp::Le, Val::Date(d), Val::Date(pd)) == Ok::<Truth, SqlError>(truth_of(d <= pd)));
    assert(q1_qual(pd, proj(r, src_cols())) == (d <= pd));
}

/// The GROUP BY key expressions on one table row are the normal form's key.
pub proof fn lemma_keys_row(db: Database, r: Row)
    requires table_row_ok(r),
    ensures eval_exprs(db, r, ast_keys()) == Ok::<Row, SqlError>(q1_key(proj(r, src_cols()))),
{
    lemma_proj_row_ok(r);
    let ks = ast_keys();
    assert(ks =~= col_exprs(seq![8nat, 9nat]));
    lemma_eval_cols(db, r, seq![8nat, 9nat]);
    assert(select(r, seq![8nat, 9nat]) =~= q1_key(proj(r, src_cols())));
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

/// `pow10` at the small exponents the per-row arithmetic uses.
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

/// `1 - c` and `1 + c` of a numeric(15,2) column value: scale 2, coefficient `100 - c` / `100 + c`, below `10^16`.
pub proof fn lemma_one_op_col(db: Database, env: Row, op: ArithOp, i: nat)
    requires
        !(op is Mul),
        i < env.len(),
        num15_2(env[i as int]),
    ensures ({
        let c = env[i as int]->Num_coeff;
        let v = if op is Add { 100 + c } else { 100 - c };
        &&& eval_expr(db, env, Expr::Arith { op, kind: NumKind::Numeric, a: Box::new(e_one()), b: Box::new(Expr::Col(i)) })
                == Ok::<Val, SqlError>(Val::Num { coeff: v, scale: 2 })
        &&& abs(v) < pow10(16)
    }),
{
    lemma_eval_one(db, env);
    lemma_pow10_small();
    let c = env[i as int]->Num_coeff;
    assert(eval_expr(db, env, Expr::Col(i)) == Ok::<Val, SqlError>(env[i as int]));
    assert(max_nat(0, 2) == 2);
    lemma_node_add(db, env, op, e_one(), Expr::Col(i), 1, 0, 1, c, 2, 15, 2, 100, 1, 16);
}

/// `l_extendedprice * (1 - l_discount)` on one table row.
pub proof fn lemma_eval_disc_price(db: Database, r: Row)
    requires table_row_ok(r),
    ensures
        eval_expr(db, r, e_disc_price()) == Ok::<Val, SqlError>(Val::Num { coeff: disc_price(proj(r, src_cols())), scale: 4 }),
        abs(disc_price(proj(r, src_cols()))) < pow10(31),
{
    lemma_proj_row_ok(r);
    lemma_pow10_small();
    lemma_one_op_col(db, r, ArithOp::Sub, 6);
    let e = r[5]->Num_coeff;
    let d = r[6]->Num_coeff;
    assert(eval_expr(db, r, Expr::Col(5)) == Ok::<Val, SqlError>(r[5]));
    let sub = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(e_one()), b: Box::new(Expr::Col(6)) };
    lemma_node_mul(db, r, Expr::Col(5), sub, e, 2, 15, 100 - d, 2, 16);
}

/// The charge on one table row (its value; and its machine-domain condition `fits_i128` of the last product).
pub proof fn lemma_eval_charge(db: Database, r: Row)
    requires table_row_ok(r),
    ensures
        eval_expr(db, r, e_charge()) == Ok::<Val, SqlError>(Val::Num { coeff: charge(proj(r, src_cols())), scale: 6 }),
        eval_expr(db, r, e_one_plus_tax()) == Ok::<Val, SqlError>(Val::Num { coeff: 100 + ival(r[7]), scale: 2 }),
{
    lemma_proj_row_ok(r);
    lemma_pow10_small();
    lemma_eval_disc_price(db, r);
    lemma_one_op_col(db, r, ArithOp::Add, 7);
    let x = proj(r, src_cols());
    let t = r[7]->Num_coeff;
    lemma_node_mul(db, r, e_disc_price(), e_one_plus_tax(), disc_price(x), 4, 31, 100 + t, 2, 16);
}

/// The argument values of the aggregates on a projected source row (COUNT(*) has none; NULL stands in).
pub open spec fn row_arg_vals(x: Row) -> Row {
    seq![
        x[0], x[1],
        Val::Num { coeff: disc_price(x), scale: 4 },
        Val::Num { coeff: charge(x), scale: 6 },
        x[0], x[1], x[2], Val::Null
    ]
}

/// The normal form's argument values of a projected source row are `row_arg_vals`.
pub proof fn lemma_arg_vals(pd: int, x: Row)
    requires src_row_ok(x),
    ensures arg_vals(q1_spec(pd), x) == row_arg_vals(x),
{
    let v = arg_vals(q1_spec(pd), x);
    let w = row_arg_vals(x);
    assert(v.len() == 8);
    assert forall|j: int| 0 <= j < 8 implies #[trigger] v[j] == w[j] by {
        if j == 0 {} else if j == 1 {} else if j == 2 {} else if j == 3 {} else if j == 4 {} else if j == 5 {} else if j == 6 {} else {}
    }
    assert(v =~= w);
}

/// The ASTs of the aggregates, one by one.
pub proof fn lemma_ast_aggs()
    ensures
        ast_aggs().len() == 8,
        ast_aggs()[0] == (Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(4) }),
        ast_aggs()[1] == (Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(5) }),
        ast_aggs()[2] == (Agg::Sum { kind: NumKind::Numeric, arg: e_disc_price() }),
        ast_aggs()[3] == (Agg::Sum { kind: NumKind::Numeric, arg: e_charge() }),
        ast_aggs()[4] == (Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(4) }),
        ast_aggs()[5] == (Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(5) }),
        ast_aggs()[6] == (Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(6) }),
        ast_aggs()[7] == Agg::CountStar,
{
}

/// The argument value of each aggregate AST on one table row.
pub proof fn lemma_agg_arg_row(db: Database, r: Row, j: int)
    requires table_row_ok(r), 0 <= j < 8,
    ensures agg_arg(db, r, ast_aggs()[j]) == Ok::<Val, SqlError>(row_arg_vals(proj(r, src_cols()))[j]),
{
    hide(eval_expr);
    hide(agg_arg);
    lemma_proj_row_ok(r);
    lemma_ast_aggs();
    let x = proj(r, src_cols());
    let w = row_arg_vals(x);
    if j == 0 {
        lemma_agg_arg_sum(db, r, NumKind::Numeric, Expr::Col(4));
        lemma_expr_col(db, r, 4);
    } else if j == 1 {
        lemma_agg_arg_sum(db, r, NumKind::Numeric, Expr::Col(5));
        lemma_expr_col(db, r, 5);
    } else if j == 2 {
        lemma_agg_arg_sum(db, r, NumKind::Numeric, e_disc_price());
        lemma_eval_disc_price(db, r);
    } else if j == 3 {
        lemma_agg_arg_sum(db, r, NumKind::Numeric, e_charge());
        lemma_eval_charge(db, r);
    } else if j == 4 {
        lemma_agg_arg_avg(db, r, NumKind::Numeric, Expr::Col(4));
        lemma_expr_col(db, r, 4);
    } else if j == 5 {
        lemma_agg_arg_avg(db, r, NumKind::Numeric, Expr::Col(5));
        lemma_expr_col(db, r, 5);
    } else if j == 6 {
        lemma_agg_arg_avg(db, r, NumKind::Numeric, Expr::Col(6));
        lemma_expr_col(db, r, 6);
    } else {
        lemma_agg_arg_count(db, r);
    }
}

/// Per aggregate: the argument outcome on one table row is `row_arg_vals`.
pub proof fn lemma_args_row_pointwise(db: Database, r: Row)
    requires table_row_ok(r),
    ensures
        agg_arg_results(db, r, ast_aggs()).len() == 8,
        forall|j: int| 0 <= j < 8 ==>
            #[trigger] agg_arg_results(db, r, ast_aggs())[j] == Ok::<Val, SqlError>(row_arg_vals(proj(r, src_cols()))[j]),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(row_arg_vals);
    hide(proj);
    hide(src_cols);
    hide(ast_aggs);
    let aggs = ast_aggs();
    lemma_agg_arg_results_index(db, r, aggs);
    assert(aggs.len() == 8) by { reveal(ast_aggs); }
    assert forall|j: int| 0 <= j < 8 implies
        #[trigger] agg_arg_results(db, r, aggs)[j] == Ok::<Val, SqlError>(row_arg_vals(proj(r, src_cols()))[j]) by {
        lemma_agg_arg_row(db, r, j);
    }
}

/// The aggregate arguments on one table row are the normal form's argument values.
pub proof fn lemma_args_row(db: Database, r: Row, pd: int)
    requires table_row_ok(r),
    ensures agg_args(db, r, ast_aggs()) == Ok::<Row, SqlError>(arg_vals(q1_spec(pd), proj(r, src_cols()))),
{
    hide(agg_args);
    hide(collect);
    hide(arg_vals);
    hide(agg_arg_results);
    hide(row_arg_vals);
    hide(proj);
    hide(src_cols);
    hide(ast_aggs);
    let x = proj(r, src_cols());
    assert(src_row_ok(x)) by {
        reveal(proj);
        reveal(src_cols);
        lemma_proj_row_ok(r);
    }
    lemma_arg_vals(pd, x);
    let rs = agg_arg_results(db, r, ast_aggs());
    let vals = row_arg_vals(x);
    lemma_args_row_pointwise(db, r);
    assert(vals.len() == 8) by { reveal(row_arg_vals); }
    lemma_collect_all(rs, vals);
    crate::exec::relational::domain::lemma_agg_args(db, r, ast_aggs());
}

/// On projected source rows, SQL "not distinct" of the keys is structural equality (text keys).
pub proof fn lemma_keys_exact(pd: int, xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> src_row_ok(#[trigger] xs[i]),
    ensures keys_exact(q1_spec(pd), xs),
{
    let g = q1_spec(pd);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let ka = (g.key)(xs[a]);
        let kb = (g.key)(xs[b]);
        assert(src_row_ok(xs[a]) && src_row_ok(xs[b]));
        assert forall|i: int| 0 <= i < ka.len() implies same_exact_type(#[trigger] ka[i], kb[i]) by {}
        lemma_row_exact(ka, kb);
    }
}

} // verus!
