//! The output expression `100.00 * Col(0) / Col(1)` (`answer::out_expr`) on a two-value row: its value and its
//! executable domain, one operator at a time, so the answer can be computed with the verified operators
//! (`exec::scalar::arith_exec`, `exec::fns::div::exec_div`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::fns::apply_fn;
use crate::spec::fns::div::{apply_div, fits_div};
use crate::exec::domain::{fits_expr, fits_exprs, arith_fits, lemma_fits_exprs_unfold};
use crate::exec::relational::domain::fits_pred;
use crate::spec::fns::fits_fn;
use crate::link::expr::closed_db;
use super::answer::*;

verus! {

/// `100.00` as a value.
pub open spec fn hundred() -> Val {
    Val::Num { coeff: 10000, scale: 2 }
}

/// The literal `100.00` evaluates to its value.
pub proof fn lemma_lit_hundred(db: Database, env: Row)
    ensures eval_expr(db, env, Expr::Lit(Literal::Num { coeff: 10000, scale: 2 })) == Ok::<Val, SqlError>(hundred()),
{
    assert(crate::spec::numeric::num_in_range(10000, 2)) by (compute);
    assert(2 <= crate::spec::limits::numeric_dscale_max()) by (compute);
}

/// A list of two expressions: values left to right, stopping at the first error, and its domain.
pub proof fn lemma_eval_pair(db: Database, env: Row, e0: Expr, e1: Expr)
    ensures
        eval_exprs(db, env, seq![e0, e1]) == match eval_expr(db, env, e0) {
            Err(e) => Err(e),
            Ok(v0) => match eval_expr(db, env, e1) {
                Err(e) => Err(e),
                Ok(v1) => Ok::<Row, SqlError>(seq![v0, v1]),
            },
        },
        fits_exprs(db, env, seq![e0, e1]) == (fits_expr(db, env, e0) && (eval_expr(db, env, e0) is Ok ==> fits_expr(db, env, e1))),
{
    let es = seq![e0, e1];
    let e1s = seq![e0];
    assert(es.drop_last() =~= e1s);
    assert(e1s.drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_step(db, env, es);
    lemma_eval_exprs_step(db, env, e1s);
    lemma_eval_exprs_empty(db, env);
    lemma_fits_exprs_unfold(db, env, es);
    lemma_fits_exprs_unfold(db, env, e1s);
    assert(fits_exprs(db, env, Seq::<Expr>::empty()));
    if let Ok(v0) = eval_expr(db, env, e0) {
        assert(Seq::<Val>::empty().push(v0) =~= seq![v0]);
        if let Ok(v1) = eval_expr(db, env, e1) {
            assert(seq![v0].push(v1) =~= seq![v0, v1]);
        }
    }
}

/// `100.00 * Col(0)` on a two-value row.
pub proof fn lemma_mul_eval(db: Database, env: Row)
    requires env.len() == 2,
    ensures
        eval_expr(db, env, mul_expr()) == arith(ArithOp::Mul, NumKind::Numeric, hundred(), env[0]),
        fits_expr(db, env, mul_expr()) == arith_fits(ArithOp::Mul, NumKind::Numeric, hundred(), env[0]),
{
    let lit = Expr::Lit(Literal::Num { coeff: 10000, scale: 2 });
    lemma_lit_hundred(db, env);
    assert(eval_expr(db, env, Expr::Col(0)) == Ok::<Val, SqlError>(env[0]));
    assert(fits_expr(db, env, lit));
    assert(fits_expr(db, env, Expr::Col(0)));
}

/// The output expression's value on a two-value row: the product, then the quotient.
pub open spec fn out_formula(env: Row) -> Result<Val, SqlError> {
    match arith(ArithOp::Mul, NumKind::Numeric, hundred(), env[0]) {
        Err(e) => Err::<Val, SqlError>(e),
        Ok(m) => apply_div(ScalarFn::DivNumeric, seq![m, env[1]]),
    }
}

/// The output expression's domain on a two-value row.
pub open spec fn out_fits_formula(env: Row) -> bool {
    arith_fits(ArithOp::Mul, NumKind::Numeric, hundred(), env[0])
        && (arith(ArithOp::Mul, NumKind::Numeric, hundred(), env[0]) matches Ok(m)
            ==> fits_div(ScalarFn::DivNumeric, seq![m, env[1]]))
}

/// The output expression on a two-value row, in the closed database.
pub proof fn lemma_out_eval(env: Row)
    requires env.len() == 2,
    ensures
        eval_out(env) == match arith(ArithOp::Mul, NumKind::Numeric, hundred(), env[0]) {
            Err(e) => Err::<Val, SqlError>(e),
            Ok(m) => apply_div(ScalarFn::DivNumeric, seq![m, env[1]]),
        },
        fits_out(env) == (arith_fits(ArithOp::Mul, NumKind::Numeric, hundred(), env[0])
            && (arith(ArithOp::Mul, NumKind::Numeric, hundred(), env[0]) matches Ok(m)
                ==> fits_div(ScalarFn::DivNumeric, seq![m, env[1]]))),
{
    lemma_out_eval_db(closed_db(), env);
}

/// The output expression on a two-value row, in any database (it reads no table).
pub proof fn lemma_out_eval_db(db: Database, env: Row)
    requires env.len() == 2,
    ensures
        eval_expr(db, env, out_expr()) == out_formula(env),
        fits_expr(db, env, out_expr()) == out_fits_formula(env),
{
    lemma_mul_eval(db, env);
    lemma_eval_pair(db, env, mul_expr(), Expr::Col(1));
    assert(eval_expr(db, env, Expr::Col(1)) == Ok::<Val, SqlError>(env[1]));
    assert(fits_expr(db, env, Expr::Col(1)));
    assert(out_expr() == Expr::Call { f: ScalarFn::DivNumeric, args: seq![mul_expr(), Expr::Col(1)] });
}

} // verus!
