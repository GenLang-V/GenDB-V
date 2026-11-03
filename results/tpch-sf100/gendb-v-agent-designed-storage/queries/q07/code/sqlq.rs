//! Q7's statement pieces and their meaning on one joined row.
//!
//! The FROM list is the left-deep product supplier x lineitem x orders x customer x nation n1 x nation n2; a
//! joined row `x` has 48 columns: supplier 0..7, lineitem 7..23, orders 23..32, customer 32..40, n1 40..44,
//! n2 44..48. On a row whose referenced positions carry values of their declared types (`x_typed`):
//! - the WHERE condition evaluates without error to the truth of `jq(ps, x)` (`lemma_where_row`);
//! - the SELECT list evaluates to `px(x)`: `[n1.n_name, n2.n_name, EXTRACT(YEAR FROM l_shipdate),
//!   l_extendedprice * (1 - l_discount)]`, the last as the scale-4 coefficient `price * (100 - discount)`
//!   (`lemma_proj_row`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::limits::*;
use crate::spec::datetime::*;
use crate::spec::fns::extract::extract_field;
use crate::spec::relation::*;
use crate::spec::fns::apply_fn;
use crate::link::expr::*;
use crate::link::query::{lemma_node_mul, lemma_node_add};
use crate::bridge::collect::lemma_collect_all;
use crate::query::{query_spec_at, param_typed};
use super::dates::*;

verus! {

// ------------------------------------------------------------------------------------------------ statement pieces

/// `Col(a) = Col(b)`.
pub open spec fn eqp(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

/// The five join conditions, as the statement nests them.
pub open spec fn join_pred() -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::And(
                Box::new(Pred::And(Box::new(eqp(0, 9)), Box::new(eqp(23, 7)))),
                Box::new(eqp(32, 24)),
            )),
            Box::new(eqp(3, 40)),
        )),
        Box::new(eqp(35, 44)),
    )
}

/// `Col(c) = <literal>`.
pub open spec fn txtp(c: nat, l: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c), b: Expr::Lit(l) }
}

/// `(n1.n_name = $1 AND n2.n_name = $2) OR (n1.n_name = $2 AND n2.n_name = $1)`.
pub open spec fn names_pred(ps: Seq<Literal>) -> Pred {
    Pred::Or(
        Box::new(Pred::And(Box::new(txtp(41, ps[0])), Box::new(txtp(45, ps[1])))),
        Box::new(Pred::And(Box::new(txtp(41, ps[1])), Box::new(txtp(45, ps[0])))),
    )
}

/// `l_shipdate BETWEEN DATE '1995-01-01' AND DATE '1996-12-31'`.
pub open spec fn date_pred() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(17), b: Expr::Lit(Literal::Date { y: 1995, m: 1, d: 1 }) }),
        Box::new(Pred::Cmp { op: CmpOp::Le, a: Expr::Col(17), b: Expr::Lit(Literal::Date { y: 1996, m: 12, d: 31 }) }),
    )
}

/// The WHERE condition.
pub open spec fn where_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(Pred::And(Box::new(join_pred()), Box::new(names_pred(ps)))), Box::new(date_pred()))
}

/// `1 - l_discount`.
pub open spec fn one_minus_disc() -> Expr {
    Expr::Arith {
        op: ArithOp::Sub,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }),
        b: Box::new(Expr::Col(13)),
    }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn vol_expr() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(12)), b: Box::new(one_minus_disc()) }
}

/// `EXTRACT(YEAR FROM l_shipdate)`.
pub open spec fn year_expr() -> Expr {
    Expr::Call { f: ScalarFn::ExtractYear, args: seq![Expr::Col(17)] }
}

/// The inner SELECT list.
pub open spec fn proj_exprs() -> Seq<Expr> {
    seq![Expr::Col(41), Expr::Col(45), year_expr(), vol_expr()]
}

/// The FROM list: supplier, lineitem, orders, customer, nation, nation.
pub open spec fn prod_q() -> Query {
    Query::Product {
        left: Box::new(Query::Product {
            left: Box::new(Query::Product {
                left: Box::new(Query::Product {
                    left: Box::new(Query::Product { left: Box::new(Query::Table(5)), right: Box::new(Query::Table(0)) }),
                    right: Box::new(Query::Table(1)),
                }),
                right: Box::new(Query::Table(2)),
            }),
            right: Box::new(Query::Table(6)),
        }),
        right: Box::new(Query::Table(6)),
    }
}

/// `FROM .. WHERE ..`.
pub open spec fn filter_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(ps), input: Box::new(prod_q()) }
}

/// The derived table `shipping`.
pub open spec fn shipping_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: proj_exprs(), input: Box::new(filter_q(ps)) }
}

/// The GROUP BY keys.
pub open spec fn group_keys() -> Seq<Expr> {
    seq![Expr::Col(0), Expr::Col(1), Expr::Col(2)]
}

/// `SUM(volume)`.
pub open spec fn group_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(3) }]
}

/// The ORDER BY keys: supp_nation, cust_nation, l_year, ascending.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![
        OrderKey { col: 0, desc: false, nulls_first: false },
        OrderKey { col: 1, desc: false, nulls_first: false },
        OrderKey { col: 2, desc: false, nulls_first: false },
    ]
}

/// The statement, piece by piece.
pub proof fn lemma_statement(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == (Query::GroupBy { keys: group_keys(), aggs: group_aggs(), input: Box::new(shipping_q(ps)) }),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
}

// ------------------------------------------------------------------------------------------------ one joined row

/// The text of a text literal (empty otherwise).
pub open spec fn ltext(l: Literal) -> Seq<u8> {
    match l {
        Literal::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// Both parameters are text literals.
pub open spec fn texts(ps: Seq<Literal>) -> bool {
    &&& ps.len() == 2
    &&& ps[0] is Text
    &&& ps[1] is Text
}

pub proof fn lemma_texts(ps: Seq<Literal>)
    requires param_typed(ps),
    ensures texts(ps),
{
}

/// The names of the two nations are `($1, $2)` or `($2, $1)`.
pub open spec fn names_ok(ps: Seq<Literal>, a: Val, b: Val) -> bool {
    ||| (a == Val::Text(ltext(ps[0])) && b == Val::Text(ltext(ps[1])))
    ||| (a == Val::Text(ltext(ps[1])) && b == Val::Text(ltext(ps[0])))
}

/// A date inside the shipping window.
pub open spec fn date_in(v: Val) -> bool {
    &&& v is Date
    &&& win_lo() <= v->Date_0 <= win_hi()
}

/// The WHERE condition on a joined row, two-valued.
pub open spec fn jq(ps: Seq<Literal>, x: Row) -> bool {
    &&& x[0] == x[9]
    &&& x[23] == x[7]
    &&& x[32] == x[24]
    &&& x[3] == x[40]
    &&& x[35] == x[44]
    &&& names_ok(ps, x[41], x[45])
    &&& date_in(x[17])
}

/// Coefficient of a numeric value (0 otherwise).
pub open spec fn ncoef(v: Val) -> int {
    match v {
        Val::Num { coeff, .. } => coeff,
        _ => 0,
    }
}

/// Day of a date value (0 otherwise).
pub open spec fn dday(v: Val) -> int {
    match v {
        Val::Date(d) => d,
        _ => 0,
    }
}

/// `EXTRACT(YEAR ..)` of a day.
#[verifier::opaque]
pub open spec fn year_of(d: int) -> int {
    extract_field(ScalarFn::ExtractYear, civil_from_date(d))
}

/// The scale-4 coefficient of `price * (1 - discount)` from the scale-2 coefficients.
#[verifier::opaque]
pub open spec fn vol_of(price: int, disc: int) -> int {
    price * (100 - disc)
}

/// The SELECT list's values on a joined row.
pub open spec fn px(x: Row) -> Row {
    seq![
        x[41],
        x[45],
        Val::Num { coeff: year_of(dday(x[17])), scale: 0 },
        Val::Num { coeff: vol_of(ncoef(x[12]), ncoef(x[13])), scale: 4 },
    ]
}

/// A numeric(15, 2) value.
pub open spec fn num152(v: Val) -> bool {
    &&& v is Num
    &&& v->Num_scale == 2
    &&& abs(v->Num_coeff) < pow10(15)
}

/// The positions the statement reads carry values of their declared types.
pub open spec fn x_typed(x: Row) -> bool {
    &&& x.len() == 48
    &&& x[0] is Int && x[9] is Int
    &&& x[23] is Int && x[7] is Int
    &&& x[32] is Int && x[24] is Int
    &&& x[3] is Int && x[40] is Int
    &&& x[35] is Int && x[44] is Int
    &&& x[41] is Text && x[45] is Text
    &&& x[17] is Date
    &&& num152(x[12]) && num152(x[13])
}

/// One equality of two integer columns.
proof fn lemma_eq_row(db: Database, x: Row, a: nat, b: nat)
    requires a < x.len(), b < x.len(), x[a as int] is Int, x[b as int] is Int,
    ensures eval_pred(db, x, eqp(a, b)) == Ok::<Truth, SqlError>(truth_of(x[a as int] == x[b as int])),
{
    let (va, vb) = (x[a as int], x[b as int]);
    lemma_expr_col(db, x, a);
    lemma_expr_col(db, x, b);
    lemma_compare_int(va->Int_0, vb->Int_0);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(a), Expr::Col(b), va, vb, va->Int_0, vb->Int_0);
}

/// The join conditions.
proof fn lemma_join_row(db: Database, x: Row)
    requires x_typed(x),
    ensures eval_pred(db, x, join_pred()) == Ok::<Truth, SqlError>(truth_of(
        x[0] == x[9] && x[23] == x[7] && x[32] == x[24] && x[3] == x[40] && x[35] == x[44])),
{
    hide(eval_pred);
    lemma_eq_row(db, x, 0, 9);
    lemma_eq_row(db, x, 23, 7);
    lemma_eq_row(db, x, 32, 24);
    lemma_eq_row(db, x, 3, 40);
    lemma_eq_row(db, x, 35, 44);
    let p1 = Pred::And(Box::new(eqp(0, 9)), Box::new(eqp(23, 7)));
    lemma_pred_and(db, x, eqp(0, 9), eqp(23, 7), x[0] == x[9], x[23] == x[7]);
    let p2 = Pred::And(Box::new(p1), Box::new(eqp(32, 24)));
    lemma_pred_and(db, x, p1, eqp(32, 24), x[0] == x[9] && x[23] == x[7], x[32] == x[24]);
    let p3 = Pred::And(Box::new(p2), Box::new(eqp(3, 40)));
    lemma_pred_and(db, x, p2, eqp(3, 40), x[0] == x[9] && x[23] == x[7] && x[32] == x[24], x[3] == x[40]);
    lemma_pred_and(db, x, p3, eqp(35, 44), x[0] == x[9] && x[23] == x[7] && x[32] == x[24] && x[3] == x[40], x[35] == x[44]);
}

/// One text column against a text parameter.
proof fn lemma_txt_row(db: Database, x: Row, c: nat, l: Literal)
    requires c < x.len(), x[c as int] is Text, l is Text,
    ensures eval_pred(db, x, txtp(c, l)) == Ok::<Truth, SqlError>(truth_of(x[c as int] == Val::Text(ltext(l)))),
{
    let a = x[c as int]->Text_0;
    lemma_expr_col(db, x, c);
    lemma_expr_text(db, x, ltext(l));
    assert(Expr::Lit(l) == Expr::Lit(Literal::Text(ltext(l))));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(c), Expr::Lit(l), a, ltext(l));
}

/// The nation-name condition.
proof fn lemma_names_row(db: Database, ps: Seq<Literal>, x: Row)
    requires x_typed(x), texts(ps),
    ensures eval_pred(db, x, names_pred(ps)) == Ok::<Truth, SqlError>(truth_of(names_ok(ps, x[41], x[45]))),
{
    hide(eval_pred);
    let (t0, t1) = (Val::Text(ltext(ps[0])), Val::Text(ltext(ps[1])));
    lemma_txt_row(db, x, 41, ps[0]);
    lemma_txt_row(db, x, 45, ps[1]);
    lemma_txt_row(db, x, 41, ps[1]);
    lemma_txt_row(db, x, 45, ps[0]);
    lemma_pred_and(db, x, txtp(41, ps[0]), txtp(45, ps[1]), x[41] == t0, x[45] == t1);
    lemma_pred_and(db, x, txtp(41, ps[1]), txtp(45, ps[0]), x[41] == t1, x[45] == t0);
    lemma_pred_or(db, x,
        Pred::And(Box::new(txtp(41, ps[0])), Box::new(txtp(45, ps[1]))),
        Pred::And(Box::new(txtp(41, ps[1])), Box::new(txtp(45, ps[0]))),
        x[41] == t0 && x[45] == t1, x[41] == t1 && x[45] == t0);
}

/// The shipping-date window.
proof fn lemma_date_row(db: Database, x: Row)
    requires x_typed(x),
    ensures eval_pred(db, x, date_pred()) == Ok::<Truth, SqlError>(truth_of(date_in(x[17]))),
{
    hide(eval_pred);
    let d = x[17]->Date_0;
    let l1 = Literal::Date { y: 1995, m: 1, d: 1 };
    let l2 = Literal::Date { y: 1996, m: 12, d: 31 };
    lemma_window_lits();
    lemma_expr_col(db, x, 17);
    lemma_compare_date(d, win_lo());
    lemma_compare_date(d, win_hi());
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(17), Expr::Lit(l1), x[17], Val::Date(win_lo()), d, win_lo());
    lemma_pred_cmp(db, x, CmpOp::Le, Expr::Col(17), Expr::Lit(l2), x[17], Val::Date(win_hi()), d, win_hi());
    lemma_pred_and(db, x,
        Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(17), b: Expr::Lit(l1) },
        Pred::Cmp { op: CmpOp::Le, a: Expr::Col(17), b: Expr::Lit(l2) },
        d >= win_lo(), d <= win_hi());
}

/// The WHERE condition on a typed joined row is `jq`, without error.
pub proof fn lemma_where_row(db: Database, ps: Seq<Literal>, x: Row)
    requires x_typed(x), texts(ps),
    ensures eval_pred(db, x, where_pred(ps)) == Ok::<Truth, SqlError>(truth_of(jq(ps, x))),
{
    hide(eval_pred);
    lemma_join_row(db, x);
    lemma_names_row(db, ps, x);
    lemma_date_row(db, x);
    let jb = x[0] == x[9] && x[23] == x[7] && x[32] == x[24] && x[3] == x[40] && x[35] == x[44];
    lemma_pred_and(db, x, join_pred(), names_pred(ps), jb, names_ok(ps, x[41], x[45]));
    lemma_pred_and(db, x, Pred::And(Box::new(join_pred()), Box::new(names_pred(ps))), date_pred(),
        jb && names_ok(ps, x[41], x[45]), date_in(x[17]));
}

/// `EXTRACT(YEAR FROM l_shipdate)` on a typed row.
proof fn lemma_year_expr(db: Database, x: Row)
    requires x_typed(x),
    ensures eval_expr(db, x, year_expr()) == Ok::<Val, SqlError>(Val::Num { coeff: year_of(dday(x[17])), scale: 0 }),
{
    reveal(year_of);
    lemma_expr_col(db, x, 17);
    let args = seq![Expr::Col(17)];
    crate::spec::eval::lemma_eval_exprs_step(db, x, args);
    assert(args.drop_last() =~= Seq::<Expr>::empty());
    crate::spec::eval::lemma_eval_exprs_empty(db, x);
    assert(seq![x[17]] =~= Seq::<Val>::empty().push(x[17]));
}

/// The literal `1` cast to numeric.
pub open spec fn one_expr() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }
}

proof fn lemma_one_expr(db: Database, x: Row)
    ensures eval_expr(db, x, one_expr()) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }),
{
    let lit = Literal::Int { v: 1, kind: IntKind::Int4 };
    assert(int_in_range(IntKind::Int4, 1));
    assert(lit_val(lit) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, x, Expr::Lit(lit)) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(cast(CastOp::IntToNumeric, Val::Int(1)) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
}

proof fn lemma_small_pow10()
    ensures pow10(0) == 1, pow10(1) == 10, pow10(2) == 100, pow10(15) <= pow10(16),
{
    reveal_with_fuel(pow10, 3);
    lemma_pow10_monotone(15, 16);
}

/// `l_extendedprice * (1 - l_discount)` on a typed row.
proof fn lemma_vol_expr(db: Database, x: Row)
    requires x_typed(x),
    ensures eval_expr(db, x, vol_expr()) == Ok::<Val, SqlError>(Val::Num { coeff: vol_of(ncoef(x[12]), ncoef(x[13])), scale: 4 }),
{
    hide(eval_expr);
    hide(pow10);
    let (p, d) = (ncoef(x[12]), ncoef(x[13]));
    lemma_one_expr(db, x);
    lemma_expr_col(db, x, 12);
    lemma_expr_col(db, x, 13);
    lemma_small_pow10();
    assert(one_minus_disc() == Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(one_expr()), b: Box::new(Expr::Col(13)) });
    lemma_node_add(db, x, ArithOp::Sub, one_expr(), Expr::Col(13), 1, 0, 1, d, 2, 15, 2, 100, 1, 16);
    assert(1 * 100 - d * 1 == 100 - d);
    lemma_node_mul(db, x, Expr::Col(12), one_minus_disc(), p, 2, 15, 100 - d, 2, 16);
    reveal(vol_of);
}

/// The SELECT list on a typed row is `px(x)`, without error (one `eval_exprs` step per expression).
pub proof fn lemma_proj_row(db: Database, x: Row)
    requires x_typed(x),
    ensures eval_exprs(db, x, proj_exprs()) == Ok::<Row, SqlError>(px(x)),
{
    hide(eval_expr);
    hide(eval_exprs);
    hide(eval_query);
    hide(eval_pred);
    hide(apply_fn);
    hide(civil_from_date);
    let e4 = proj_exprs();
    let e3 = e4.drop_last();
    let e2 = e3.drop_last();
    let e1 = e2.drop_last();
    let e0 = e1.drop_last();
    assert(e0 =~= Seq::<Expr>::empty());
    assert(e1.last() == Expr::Col(41) && e2.last() == Expr::Col(45) && e3.last() == year_expr() && e4.last() == vol_expr());
    lemma_expr_col(db, x, 41);
    lemma_expr_col(db, x, 45);
    lemma_year_expr(db, x);
    lemma_vol_expr(db, x);
    crate::spec::eval::lemma_eval_exprs_empty(db, x);
    crate::spec::eval::lemma_eval_exprs_step(db, x, e1);
    crate::spec::eval::lemma_eval_exprs_step(db, x, e2);
    crate::spec::eval::lemma_eval_exprs_step(db, x, e3);
    crate::spec::eval::lemma_eval_exprs_step(db, x, e4);
    let v = px(x);
    assert(Seq::<Val>::empty().push(v[0]).push(v[1]).push(v[2]).push(v[3]) =~= v);
}

} // verus!
