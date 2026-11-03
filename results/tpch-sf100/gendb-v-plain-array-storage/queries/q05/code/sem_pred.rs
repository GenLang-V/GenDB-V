//! The WHERE condition on one FROM row: when the timestamp `$2 + INTERVAL '1' YEAR` exists (`hi_res` is `Ok(t)`),
//! the condition is the two-valued `q5_qual` of the row (`lemma_where_row`), which on `row6` is `qual6` over the
//! stored columns (`lemma_qual_row6`); otherwise every row's condition is that timestamp's SQL error.
//!
//! Dates: a stored order date `od` (days since 1970-01-01) is the SQL date `od - 10957` (days since 2000-01-01);
//! the parameter `$2` is the day `pd` (`date_from_civil`), and the timestamp bound `t` is in microseconds.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::sign;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::datetime::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::link::expr::{lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and, lemma_compare_int, lemma_compare_date,
    lemma_expr_col, lemma_expr_text, text_cmp, int_cmp};
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_from::*;

verus! {

/// The timestamp `$2 + INTERVAL '1' YEAR` of the parameter day `pd`, or the SQL error of computing it.
pub open spec fn hi_res(pd: int) -> Result<int, SqlError> {
    match date_to_ts(pd) {
        Err(e) => Err(e),
        Ok(t0) => ts_add_interval(t0, 12, 0, 0),
    }
}

/// The SQL date value `v` lies in `[$2, $2 + 1 year)`: on or after day `pd` and before timestamp `t`.
pub open spec fn date_val_in(v: Val, pd: int, t: int) -> bool {
    match v {
        Val::Date(dd) => dd >= pd && dd * usecs_per_day() < t,
        _ => false,
    }
}

/// The stored order date `od` lies in `[$2, $2 + 1 year)`.
pub open spec fn date_in(od: i32, pd: int, t: int) -> bool {
    date_val_in(date32_val(od), pd, t)
}

/// The WHERE as a two-valued condition on a FROM row (positions of `sem_ast`).
pub open spec fn q5_qual(rp: Seq<u8>, pd: int, t: int, x: Row) -> bool {
    &&& x[0] == x[9]
    &&& x[17] == x[8]
    &&& x[19] == x[33]
    &&& x[3] == x[36]
    &&& x[36] == x[40]
    &&& x[42] == x[44]
    &&& x[45] == Val::Text(rp)
    &&& date_val_in(x[12], pd, t)
}

/// The WHERE over the stored columns of the index tuple `(i, j, c, d, e, f)`.
pub open spec fn qual6(sv: StoresView, rp: Seq<u8>, pd: int, t: int, i: int, j: int, c: int, d: int, e: int, f: int) -> bool {
    &&& c_ck(sv)[i] == o_ck(sv)[j]
    &&& l_ok(sv)[c] == o_ok(sv)[j]
    &&& l_sk(sv)[c] == s_sk(sv)[d]
    &&& c_nk(sv)[i] == s_nk(sv)[d]
    &&& s_nk(sv)[d] == n_nk(sv)[e]
    &&& n_rk(sv)[e] == r_rk(sv)[f]
    &&& r_name(sv, f) == rp
    &&& date_in(o_date(sv)[j], pd, t)
}

/// The parameters as the proofs use them: `$1` is the text `rp`, `$2` the day `pd`.
pub open spec fn params_are(ps: Seq<Literal>, rp: Seq<u8>, pd: int) -> bool {
    &&& ps.len() == 2
    &&& ps[0] == Literal::Text(rp)
    &&& lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Date(pd))
}

/// `q5_qual` of a FROM row is `qual6` of its index tuple.
pub proof fn lemma_qual_row6(sv: StoresView, rp: Seq<u8>, pd: int, t: int, i: int, j: int, c: int, d: int, e: int, f: int)
    requires stores_wf(sv), in6(sv, i, j, c, d, e, f),
    ensures q5_qual(rp, pd, t, row6(sv, i, j, c, d, e, f)) == qual6(sv, rp, pd, t, i, j, c, d, e, f),
{
    lemma_row6(sv, i, j, c, d, e, f);
}

/// `$2 + INTERVAL '1' YEAR` evaluates to `hi_res` (a closed expression: the same in every row).
pub proof fn lemma_hi_expr(db: Database, x: Row, ps: Seq<Literal>, rp: Seq<u8>, pd: int)
    requires params_are(ps, rp, pd),
    ensures
        eval_expr(db, x, hi_expr(ps)) == match hi_res(pd) {
            Ok(t) => Ok::<Val, SqlError>(Val::Ts(t)),
            Err(e) => Err::<Val, SqlError>(e),
        },
{
    let lit = Expr::Lit(ps[1]);
    let cst = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(lit) };
    assert(eval_expr(db, x, lit) == Ok::<Val, SqlError>(Val::Date(pd)));
    assert(eval_expr(db, x, cst) == cast(CastOp::DateToTimestamp, Val::Date(pd)));
    match date_to_ts(pd) {
        Err(e) => {
            assert(eval_expr(db, x, cst) == Err::<Val, SqlError>(e));
        },
        Ok(t0) => {
            assert(eval_expr(db, x, cst) == Ok::<Val, SqlError>(Val::Ts(t0)));
            assert(eval_expr(db, x, hi_expr(ps)) == add_interval(Val::Ts(t0), 12i32, 0i32, 0i64));
        },
    }
}

/// `col a = col b` over two integer values.
proof fn lemma_eq_ints(db: Database, x: Row, a: nat, b: nat, va: int, vb: int)
    requires a < x.len(), b < x.len(), x[a as int] == Val::Int(va), x[b as int] == Val::Int(vb),
    ensures eval_pred(db, x, eq_cols(a, b)) == Ok::<Truth, SqlError>(truth_of(va == vb)),
{
    lemma_expr_col(db, x, a);
    lemma_expr_col(db, x, b);
    lemma_compare_int(va, vb);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(a), Expr::Col(b), Val::Int(va), Val::Int(vb), va, vb);
}

/// The join and region conditions on a FROM row.
proof fn lemma_join_conds(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int,
    i: int, j: int, c: int, d: int, e: int, f: int)
    requires stores_wf(sv), in6(sv, i, j, c, d, e, f), params_are(ps, rp, pd),
    ensures ({
        let x = row6(sv, i, j, c, d, e, f);
        eval_pred(db, x, join_conds(ps)) == Ok::<Truth, SqlError>(truth_of(
            x[0] == x[9] && x[17] == x[8] && x[19] == x[33] && x[3] == x[36] && x[36] == x[40] && x[42] == x[44]
            && x[45] == Val::Text(rp)))
    }),
{
    let x = row6(sv, i, j, c, d, e, f);
    lemma_row6(sv, i, j, c, d, e, f);
    let (cck, cnk_, ook, ock) = (c_ck(sv)[i] as int, c_nk(sv)[i] as int, o_ok(sv)[j] as int, o_ck(sv)[j] as int);
    let (lok, lsk) = (l_ok(sv)[c] as int, l_sk(sv)[c] as int);
    let (ssk, snk) = (s_sk(sv)[d] as int, s_nk(sv)[d] as int);
    let (nnk, nrk, rrk) = (n_nk(sv)[e] as int, n_rk(sv)[e] as int, r_rk(sv)[f] as int);
    lemma_eq_ints(db, x, 0, 9, cck, ock);
    lemma_eq_ints(db, x, 17, 8, lok, ook);
    lemma_eq_ints(db, x, 19, 33, lsk, ssk);
    lemma_eq_ints(db, x, 3, 36, cnk_, snk);
    lemma_eq_ints(db, x, 36, 40, snk, nnk);
    lemma_eq_ints(db, x, 42, 44, nrk, rrk);
    lemma_expr_col(db, x, 45);
    lemma_expr_text(db, x, rp);
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(45), Expr::Lit(Literal::Text(rp)), r_name(sv, f), rp);
    let p1 = and(eq_cols(0, 9), eq_cols(17, 8));
    let p2 = and(p1, eq_cols(19, 33));
    let p3 = and(p2, eq_cols(3, 36));
    let p4 = and(p3, eq_cols(36, 40));
    let p5 = and(p4, eq_cols(42, 44));
    let pr = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(45), b: Expr::Lit(ps[0]) };
    lemma_pred_and(db, x, eq_cols(0, 9), eq_cols(17, 8), cck == ock, lok == ook);
    let b1 = cck == ock && lok == ook;
    lemma_pred_and(db, x, p1, eq_cols(19, 33), b1, lsk == ssk);
    let b2 = b1 && lsk == ssk;
    lemma_pred_and(db, x, p2, eq_cols(3, 36), b2, cnk_ == snk);
    let b3 = b2 && cnk_ == snk;
    lemma_pred_and(db, x, p3, eq_cols(36, 40), b3, snk == nnk);
    let b4 = b3 && snk == nnk;
    lemma_pred_and(db, x, p4, eq_cols(42, 44), b4, nrk == rrk);
    let b5 = b4 && nrk == rrk;
    lemma_pred_and(db, x, p5, pr, b5, r_name(sv, f) == rp);
    assert(join_conds(ps) == and(p5, pr));
}

/// `o_orderdate >= $2` on a FROM row.
proof fn lemma_date_ge(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int,
    i: int, j: int, c: int, d: int, e: int, f: int)
    requires stores_wf(sv), in6(sv, i, j, c, d, e, f), params_are(ps, rp, pd),
    ensures ({
        let dd = o_date(sv)[j] as int - 10957;
        eval_pred(db, row6(sv, i, j, c, d, e, f), date_ge(ps)) == Ok::<Truth, SqlError>(truth_of(dd >= pd))
    }),
{
    let x = row6(sv, i, j, c, d, e, f);
    lemma_row6(sv, i, j, c, d, e, f);
    let dd = o_date(sv)[j] as int - 10957;
    lemma_expr_col(db, x, 12);
    assert(eval_expr(db, x, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Date(pd)));
    lemma_compare_date(dd, pd);
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(12), Expr::Lit(ps[1]), Val::Date(dd), Val::Date(pd), dd, pd);
}

/// `o_orderdate < $2 + INTERVAL '1' YEAR` on a FROM row, when the bound is the timestamp `t`.
proof fn lemma_date_lt(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, t: int,
    i: int, j: int, c: int, d: int, e: int, f: int)
    requires stores_wf(sv), in6(sv, i, j, c, d, e, f), params_are(ps, rp, pd), hi_res(pd) == Ok::<int, SqlError>(t),
    ensures ({
        let dd = o_date(sv)[j] as int - 10957;
        eval_pred(db, row6(sv, i, j, c, d, e, f), date_lt(ps)) == Ok::<Truth, SqlError>(truth_of(dd * usecs_per_day() < t))
    }),
{
    let x = row6(sv, i, j, c, d, e, f);
    lemma_row6(sv, i, j, c, d, e, f);
    let dd = o_date(sv)[j] as int - 10957;
    lemma_expr_col(db, x, 12);
    lemma_hi_expr(db, x, ps, rp, pd);
    assert(compare(Val::Date(dd), Val::Ts(t)) == Some(sign(date_as_usecs(dd) - t)));
    lemma_pred_cmp(db, x, CmpOp::Lt, Expr::Col(12), hi_expr(ps), Val::Date(dd), Val::Ts(t), date_as_usecs(dd), t);
}

/// An error of the right operand after a value of the left is the conjunction's error.
proof fn lemma_and_err_right(db: Database, env: Row, p: Pred, q: Pred, t: Truth, err: SqlError)
    requires eval_pred(db, env, p) == Ok::<Truth, SqlError>(t), eval_pred(db, env, q) == Err::<Truth, SqlError>(err),
    ensures eval_pred(db, env, and(p, q)) == Err::<Truth, SqlError>(err),
{
}

/// Without the timestamp bound, `o_orderdate < $2 + INTERVAL '1' YEAR` is the bound's error.
proof fn lemma_date_lt_err(db: Database, x: Row, ps: Seq<Literal>, rp: Seq<u8>, pd: int, err: SqlError)
    requires x.len() == 47, params_are(ps, rp, pd), hi_res(pd) == Err::<int, SqlError>(err),
    ensures eval_pred(db, x, date_lt(ps)) == Err::<Truth, SqlError>(err),
{
    lemma_expr_col(db, x, 12);
    lemma_hi_expr(db, x, ps, rp, pd);
}

/// The WHERE on a FROM row: the two-valued `q5_qual` when the timestamp bound exists, its error otherwise.
pub proof fn lemma_where_row(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int,
    i: int, j: int, c: int, d: int, e: int, f: int)
    requires stores_wf(sv), in6(sv, i, j, c, d, e, f), params_are(ps, rp, pd),
    ensures
        hi_res(pd) matches Ok(t) ==> eval_pred(db, row6(sv, i, j, c, d, e, f), where_pred(ps))
            == Ok::<Truth, SqlError>(truth_of(q5_qual(rp, pd, t, row6(sv, i, j, c, d, e, f)))),
        hi_res(pd) matches Err(err) ==> eval_pred(db, row6(sv, i, j, c, d, e, f), where_pred(ps)) == Err::<Truth, SqlError>(err),
{
    hide(eval_pred);
    hide(join_conds);
    hide(date_ge);
    hide(date_lt);
    hide(row6);
    let x = row6(sv, i, j, c, d, e, f);
    lemma_row6(sv, i, j, c, d, e, f);
    lemma_join_conds(db, sv, ps, rp, pd, i, j, c, d, e, f);
    lemma_date_ge(db, sv, ps, rp, pd, i, j, c, d, e, f);
    let dd = o_date(sv)[j] as int - 10957;
    let bj = x[0] == x[9] && x[17] == x[8] && x[19] == x[33] && x[3] == x[36] && x[36] == x[40] && x[42] == x[44]
        && x[45] == Val::Text(rp);
    let left = and(join_conds(ps), date_ge(ps));
    lemma_pred_and(db, x, join_conds(ps), date_ge(ps), bj, dd >= pd);
    assert(where_pred(ps) == and(left, date_lt(ps)));
    match hi_res(pd) {
        Ok(t) => {
            lemma_date_lt(db, sv, ps, rp, pd, t, i, j, c, d, e, f);
            lemma_pred_and(db, x, left, date_lt(ps), bj && dd >= pd, dd * usecs_per_day() < t);
            assert(x[12] == Val::Date(dd));
            assert(date_val_in(x[12], pd, t) == (dd >= pd && dd * usecs_per_day() < t));
        },
        Err(err) => {
            lemma_date_lt_err(db, x, ps, rp, pd, err);
            lemma_and_err_right(db, x, left, date_lt(ps), truth_of(bj && dd >= pd), err);
        },
    }
}

} // verus!
