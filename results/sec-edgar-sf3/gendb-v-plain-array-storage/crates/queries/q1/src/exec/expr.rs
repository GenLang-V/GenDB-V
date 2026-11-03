//! Executable scalar expression evaluator, mirroring `spec::eval`: literals (`lit_exec`), expressions
//! (`exec_expr`), expression lists (`exec_exprs`) and scalar subqueries (`subquery_value_exec`). The
//! postcondition of `exec_expr` is the compositional bridge for every expression AST (any depth): a result
//! equals the denotation and the domain predicate holds; `Capacity` means the domain predicate fails.
//!
//! `exec_expr` / `exec_exprs` are part of the recursion of `exec::relational::eval` (subqueries, CASE
//! conditions). Termination measures: `exec_expr_if` (e, 0) < `exec_expr_node` (e, 1) < `exec_expr` (e, 2);
//! `exec_exprs` (es, 1).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::domain::*;
use crate::exec::datetime::*;
use crate::exec::scalar::*;
use crate::exec::fns::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::eval::*;

verus! {

/// `spec::limits::numeric_dscale_max`: the largest numeric display scale PostgreSQL accepts (also the static check's
/// bound, `exec::relational::check`).
pub const NUMERIC_DSCALE_MAX: u32 = 16383;

/// `spec::eval::lit_val` (never leaves the executable domain: exec literals are representable by construction).
/// A literal outside its type's range is `TypeError`: the typing rules refuse it before evaluation.
pub fn lit_exec(l: &ELiteral) -> (r: Result<EVal, SqlError>)
    ensures
        view_result(r) == lit_val(view_lit(*l)),
        r matches Ok(v) ==> val_ts_ok(v@),
{
    match l {
        ELiteral::Null { .. } => Ok(EVal::Null),
        ELiteral::Bool(b) => Ok(EVal::Bool(*b)),
        ELiteral::Int { v, kind } =>
            if int_in_range_exec(*kind, *v as i128) { Ok(EVal::Int(*v)) } else { Err(SqlError::TypeError) },
        ELiteral::Num { coeff, scale } => {
            proof {
                lemma_num_in_range_small(*coeff as int, *scale as nat);
            }
            if *scale <= NUMERIC_DSCALE_MAX {
                Ok(EVal::Num { coeff: *coeff, scale: *scale })
            } else {
                Err(SqlError::TypeError)
            }
        },
        ELiteral::Date { y, m, d } => {
            let (y, m, d) = (*y as i64, *m as i64, *d as i64);
            let valid_ymd = 1 <= m && m <= 12 && 1 <= d && d <= days_in_month_exec(y, m);
            if !valid_ymd {
                return Err(SqlError::TypeError);
            }
            let day = date_from_civil_exec(y, m, d);
            if date_valid_exec(day) { Ok(EVal::Date(day as i32)) } else { Err(SqlError::TypeError) }
        },
        ELiteral::Text(b) => Ok(EVal::Text(b.clone())),
    }
}

/// `spec::eval::eval_expr` under `env`.
pub fn exec_expr(db: &EDatabase, env: &Vec<EVal>, e: &EExpr) -> (r: Outcome<EVal>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(env@)),
    ensures
        match r {
            Ok(res) => fits_expr(db@, view_row(env@), view_expr(*e))
                && view_result(res) == eval_expr(db@, view_row(env@), view_expr(*e))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_expr(db@, view_row(env@), view_expr(*e)),
        },
    decreases e, 2nat,
{
    let ghost genv = view_row(env@);
    match e {
        EExpr::Col(i) => {
            if *i < env.len() {
                let v = clone_val(&env[*i]);
                assert(genv[*i as int] == env@[*i as int]@);
                Ok(Ok(v))
            } else {
                Ok(Err(SqlError::TypeError))
            }
        },
        EExpr::Lit(l) => Ok(lit_exec(l)),
        EExpr::Neg { kind, arg } => {
            let v = match exec_expr(db, env, arg) {
                Err(c) => return Err(c),
                Ok(Err(err)) => return Ok(Err(err)),
                Ok(Ok(v)) => v,
            };
            neg_exec(*kind, &v)
        },
        EExpr::Arith { op, kind, a, b } => {
            let va = match exec_expr(db, env, a) {
                Err(c) => return Err(c),
                Ok(Err(err)) => return Ok(Err(err)),
                Ok(Ok(v)) => v,
            };
            let vb = match exec_expr(db, env, b) {
                Err(c) => return Err(c),
                Ok(Err(err)) => return Ok(Err(err)),
                Ok(Ok(v)) => v,
            };
            arith_exec(*op, *kind, &va, &vb)
        },
        EExpr::Cast { cast, arg } => {
            let v = match exec_expr(db, env, arg) {
                Err(c) => return Err(c),
                Ok(Err(err)) => return Ok(Err(err)),
                Ok(Ok(v)) => v,
            };
            Ok(cast_exec(*cast, &v))
        },
        EExpr::AddInterval { arg, months, days, micros } => {
            let v = match exec_expr(db, env, arg) {
                Err(c) => return Err(c),
                Ok(Err(err)) => return Ok(Err(err)),
                Ok(Ok(v)) => v,
            };
            Ok(add_interval_exec(&v, *months, *days, *micros))
        },
        EExpr::Call { .. } | EExpr::If { .. } | EExpr::Subquery(_) => exec_expr_node(db, env, e),
    }
}

/// `exec_expr` on `Call`, `If` and `Subquery`: their own function so that these unfoldings (leaf functions,
/// lazy CASE, subqueries) are a separate Verus query from the core operators.
pub fn exec_expr_node(db: &EDatabase, env: &Vec<EVal>, e: &EExpr) -> (r: Outcome<EVal>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(env@)),
        e is Call || e is If || e is Subquery,
    ensures
        match r {
            Ok(res) => fits_expr(db@, view_row(env@), view_expr(*e))
                && view_result(res) == eval_expr(db@, view_row(env@), view_expr(*e))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_expr(db@, view_row(env@), view_expr(*e)),
        },
    decreases e, 1nat,
{
    match e {
        EExpr::Call { f, args } => {
            let vs = match exec_exprs(db, env, args) {
                Err(c) => return Err(c),
                Ok(Err(err)) => return Ok(Err(err)),
                Ok(Ok(vs)) => vs,
            };
            exec_fn(*f, &vs)
        },
        EExpr::If { .. } => exec_expr_if(db, env, e),
        EExpr::Subquery(q) => {
            let rows = match exec_query(db, env, q) {
                Err(c) => return Err(c),
                Ok(Err(err)) => return Ok(Err(err)),
                Ok(Ok(rows)) => rows,
            };
            Ok(subquery_value_exec(&rows))
        },
        _ => unreached(),
    }
}

/// `exec_expr` on `Expr::If` (lazy: only the taken branch is evaluated). Its own function so that the CASE
/// unfolding is a separate Verus query.
pub fn exec_expr_if(db: &EDatabase, env: &Vec<EVal>, e: &EExpr) -> (r: Outcome<EVal>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(env@)),
        e is If,
    ensures
        match r {
            Ok(res) => fits_expr(db@, view_row(env@), view_expr(*e))
                && view_result(res) == eval_expr(db@, view_row(env@), view_expr(*e))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_expr(db@, view_row(env@), view_expr(*e)),
        },
    decreases e, 0nat,
{
    match e {
        EExpr::If { cond, then_e, else_e } => {
            let t = match exec_pred(db, env, cond) {
                Err(c) => return Err(c),
                Ok(Err(err)) => return Ok(Err(err)),
                Ok(Ok(t)) => t,
            };
            match t {
                Truth::True => exec_expr(db, env, then_e),
                _ => exec_expr(db, env, else_e),
            }
        },
        _ => unreached(),
    }
}

/// `spec::eval::subquery_value` (0 rows NULL, 1 row its column, more rows 21000).
pub fn subquery_value_exec(rows: &Vec<ERow>) -> (r: Result<EVal, SqlError>)
    requires rows_ts_ok(view_rows(rows@)),
    ensures
        view_result(r) == subquery_value(view_rows(rows@)),
        r matches Ok(v) ==> val_ts_ok(v@),
{
    let ghost g = view_rows(rows@);
    if rows.len() == 0 {
        Ok(EVal::Null)
    } else if rows.len() == 1 {
        proof {
            assert(g[0] == view_row(rows@[0]@));
            assert(row_ts_ok(g[0]));
        }
        if rows[0].len() > 0 {
            let v = clone_val(&rows[0][0]);
            proof { assert(g[0][0] == rows@[0]@[0]@); }
            Ok(v)
        } else {
            Err(SqlError::TypeError)
        }
    } else {
        Err(SqlError::CardinalityViolation)
    }
}

/// `spec::eval::eval_exprs` (left to right, first SQL error).
pub fn exec_exprs(db: &EDatabase, env: &Vec<EVal>, es: &Vec<EExpr>) -> (r: Outcome<Vec<EVal>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(env@)),
    ensures
        match r {
            Ok(Ok(vs)) => fits_exprs(db@, view_row(env@), view_exprs(es@))
                && eval_exprs(db@, view_row(env@), view_exprs(es@)) == Ok::<Row, SqlError>(view_row(vs@))
                && row_ts_ok(view_row(vs@)),
            Ok(Err(err)) => fits_exprs(db@, view_row(env@), view_exprs(es@))
                && eval_exprs(db@, view_row(env@), view_exprs(es@)) == Err::<Row, SqlError>(err),
            Err(_) => !fits_exprs(db@, view_row(env@), view_exprs(es@)),
        },
    decreases es, 1nat,
{
    let ghost genv = view_row(env@);
    let ghost ges = view_exprs(es@);
    let mut out: Vec<EVal> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(ges.take(0) =~= Seq::<Expr>::empty());
        assert(view_row(out@) =~= Seq::<Val>::empty());
        lemma_eval_exprs_empty(db@, genv);
    }
    while i < es.len()
        invariant
            i <= es.len(),
            ges.len() == es.len(),
            ges == view_exprs(es@),
            genv == view_row(env@),
            row_ts_ok(genv), db_ts_ok(db@),
            fits_exprs(db@, genv, ges.take(i as int)),
            eval_exprs(db@, genv, ges.take(i as int)) == Ok::<Row, SqlError>(view_row(out@)),
            row_ts_ok(view_row(out@)),
        decreases es.len() - i,
    {
        let ghost vs = view_row(out@);
        proof {
            assert(ges[i as int] == view_expr(es@[i as int]));
        }
        match exec_expr(db, env, &es[i]) {
            Err(c) => {
                proof {
                    lemma_exprs_step_fails(db@, genv, ges, i as int, vs);
                }
                return Err(c);
            },
            Ok(Err(err)) => {
                proof {
                    lemma_exprs_step(db@, genv, ges, i as int, vs);
                    lemma_exprs_err_extends(db@, genv, ges, i as int + 1);
                }
                return Ok(Err(err));
            },
            Ok(Ok(v)) => {
                proof {
                    lemma_exprs_step(db@, genv, ges, i as int, vs);
                }
                out.push(v);
                proof {
                    assert(view_row(out@) =~= vs.push(v@));
                }
            },
        }
        i = i + 1;
    }
    proof {
        assert(ges.take(es.len() as int) =~= ges);
    }
    Ok(Ok(out))
}

} // verus!
