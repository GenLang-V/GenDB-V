//! The finite executable domain: which exact intermediates of an evaluation must fit the machine
//! representation. These are spec predicates over spec values; each executable operator returns `Capacity`
//! exactly when its predicate is false, and the semantic result whenever it is true. They never change a SQL
//! meaning: the spec operators are exact and unbounded.
//!
//! Intermediates that can leave the representation, by operator:
//! - numeric `+`/`-`: the power of ten `10^(s - si)` aligning each operand to the result scale `s`, each aligned
//!   coefficient, and the result coefficient must fit `i128` (`num_addsub_fits`);
//! - numeric `*`: the product coefficient must fit `i128` and the result scale `u32` (`num_arith_fits`);
//! - numeric unary minus: the negated coefficient must fit `i128`; only `-(-2^127)` fails (`neg_fits`);
//! - scalar functions: `spec::fns::fits_fn` (only numeric division can fail, `spec::fns::div::num_div_fits`);
//! - SUM/AVG and queries: `exec::relational::domain` (`sum_mass_fits`, `fits_pred`, `fits_query`) and
//!   `exec::aggs::avg::fits_avg_value`.
//! Everything else never needs `Capacity`: int4/int8 arithmetic is computed in `i128`, which holds every exact
//! result of two `i64` operands; dates and timestamps have representations covering PostgreSQL's whole range;
//! comparisons are exact without overflow.
//!
//! The file also holds the timestamp representation invariant (`val_ts_ok`, `row_ts_ok`) that every evaluator
//! requires of its environment and ensures of its results.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::fns::*;
use crate::exec::relational::domain::*;

verus! {

/// `x` fits the machine coefficient type `i128`.
pub open spec fn fits_i128(x: int) -> bool {
    i128::MIN as int <= x <= i128::MAX as int
}

/// Domain of numeric `+`/`-` (see the module comment).
pub open spec fn num_addsub_fits(op: ArithOp, c1: int, s1: nat, c2: int, s2: nat) -> bool {
    let s = max_nat(s1, s2);
    &&& fits_i128(pow10((s - s1) as nat))
    &&& fits_i128(align(c1, s1, s))
    &&& fits_i128(pow10((s - s2) as nat))
    &&& fits_i128(align(c2, s2, s))
    &&& fits_i128(num_arith(op, c1, s1, c2, s2).0)
}

/// Domain of numeric `+`, `-`, `*` (`exec::numeric::num_arith_exec`).
pub open spec fn num_arith_fits(op: ArithOp, c1: int, s1: nat, c2: int, s2: nat) -> bool {
    match op {
        ArithOp::Mul => fits_i128(c1 * c2) && s1 + s2 <= u32::MAX as nat,
        _ => num_addsub_fits(op, c1, s1, c2, s2),
    }
}

/// Domain of `spec::scalar::arith` (only numeric operands can leave it).
pub open spec fn arith_fits(op: ArithOp, kind: NumKind, a: Val, b: Val) -> bool {
    match (kind, a, b) {
        (NumKind::Numeric, Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 }) =>
            num_arith_fits(op, c1, s1, c2, s2),
        _ => true,
    }
}

/// Domain of `spec::scalar::neg` (only a numeric coefficient of `-2^127` can leave it).
pub open spec fn neg_fits(kind: NumKind, a: Val) -> bool {
    match (kind, a) {
        (NumKind::Numeric, Val::Num { coeff, scale }) => fits_i128(-coeff),
        _ => true,
    }
}

/// Domain of `spec::eval::eval_expr`: the intermediates the canonical evaluation actually computes (children
/// left to right, stopping at the first SQL error) fit the representation. Mutually recursive with
/// `exec::relational::domain::{fits_pred, fits_query}` (subqueries, CASE conditions).
pub open spec fn fits_expr(db: Database, env: Row, e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Col(_) => true,
        Expr::Lit(_) => true,
        Expr::Neg { kind, arg } => fits_expr(db, env, *arg) && match eval_expr(db, env, *arg) {
            Ok(v) => neg_fits(kind, v),
            Err(_) => true,
        },
        Expr::Arith { op, kind, a, b } => fits_expr(db, env, *a) && match eval_expr(db, env, *a) {
            Err(_) => true,
            Ok(va) => fits_expr(db, env, *b) && match eval_expr(db, env, *b) {
                Err(_) => true,
                Ok(vb) => arith_fits(op, kind, va, vb),
            },
        },
        Expr::Cast { cast, arg } => fits_expr(db, env, *arg),
        Expr::AddInterval { arg, months, days, micros } => fits_expr(db, env, *arg),
        Expr::Call { f, args } => fits_exprs(db, env, args) && match eval_exprs(db, env, args) {
            Err(_) => true,
            Ok(vs) => fits_fn(f, vs),
        },
        // Lazy: the condition, then only the taken branch.
        Expr::If { cond, then_e, else_e } => fits_pred(db, env, *cond) && match eval_pred(db, env, *cond) {
            Err(_) => true,
            Ok(Truth::True) => fits_expr(db, env, *then_e),
            Ok(_) => fits_expr(db, env, *else_e),
        },
        Expr::Subquery(q) => fits_query(db, env, *q),
    }
}

/// Domain of `eval_exprs` (left to right, stopping at the first SQL error).
pub open spec fn fits_exprs(db: Database, env: Row, es: Seq<Expr>) -> bool
    decreases es, 0nat,
{
    if es.len() == 0 {
        true
    } else {
        fits_exprs(db, env, es.drop_last()) && match eval_exprs(db, env, es.drop_last()) {
            Err(_) => true,
            Ok(_) => fits_expr(db, env, es.last()),
        }
    }
}

/// One level of `fits_exprs` (stated once, so the list lemmas below can keep the recursive definitions hidden).
pub proof fn lemma_fits_exprs_unfold(db: Database, env: Row, es: Seq<Expr>)
    requires es.len() > 0,
    ensures
        fits_exprs(db, env, es) == (fits_exprs(db, env, es.drop_last())
            && (eval_exprs(db, env, es.drop_last()) is Ok ==> fits_expr(db, env, es.last()))),
{
}

/// A domain failure in a prefix is a failure of the whole list.
pub proof fn lemma_fits_exprs_monotone(db: Database, env: Row, es: Seq<Expr>, n: int)
    requires 0 <= n <= es.len(), fits_exprs(db, env, es),
    ensures fits_exprs(db, env, es.take(n)),
    decreases es.len(),
{
    hide(fits_exprs);
    hide(eval_exprs);
    hide(fits_expr);
    hide(eval_expr);
    if n < es.len() {
        let d = es.drop_last();
        assert(d.take(n) =~= es.take(n));
        lemma_fits_exprs_unfold(db, env, es);
        lemma_fits_exprs_monotone(db, env, d, n);
    } else {
        assert(es.take(n) =~= es);
    }
}

/// One more expression of a list evaluated: the prefix facts extend (`r` = outcome of `es[n]`).
pub proof fn lemma_exprs_step(db: Database, env: Row, es: Seq<Expr>, n: int, vs: Row)
    requires
        0 <= n < es.len(),
        fits_exprs(db, env, es.take(n)),
        eval_exprs(db, env, es.take(n)) == Ok::<Row, SqlError>(vs),
        fits_expr(db, env, es[n]),
    ensures
        fits_exprs(db, env, es.take(n + 1)),
        eval_exprs(db, env, es.take(n + 1)) == match eval_expr(db, env, es[n]) {
            Err(e) => Err(e),
            Ok(v) => Ok::<Row, SqlError>(vs.push(v)),
        },
{
    hide(fits_exprs);
    hide(eval_exprs);
    hide(fits_expr);
    hide(eval_expr);
    let next = es.take(n + 1);
    assert(next.drop_last() =~= es.take(n));
    assert(next.last() == es[n]);
    lemma_eval_exprs_step(db, env, next);
    lemma_fits_exprs_unfold(db, env, next);
}

/// A domain failure of `es[n]` after a successful prefix fails the whole list.
pub proof fn lemma_exprs_step_fails(db: Database, env: Row, es: Seq<Expr>, n: int, vs: Row)
    requires
        0 <= n < es.len(),
        eval_exprs(db, env, es.take(n)) == Ok::<Row, SqlError>(vs),
        !fits_expr(db, env, es[n]),
    ensures
        !fits_exprs(db, env, es),
{
    hide(fits_exprs);
    hide(eval_exprs);
    hide(fits_expr);
    hide(eval_expr);
    let next = es.take(n + 1);
    assert(next.drop_last() =~= es.take(n));
    assert(next.last() == es[n]);
    if fits_exprs(db, env, es) {
        lemma_fits_exprs_monotone(db, env, es, n + 1);
        lemma_fits_exprs_unfold(db, env, next);
    }
}

/// A SQL error in a prefix is the outcome (and the domain predicate) of the whole list.
pub proof fn lemma_exprs_err_extends(db: Database, env: Row, es: Seq<Expr>, n: int)
    requires
        0 < n <= es.len(),
        fits_exprs(db, env, es.take(n)),
        eval_exprs(db, env, es.take(n)) is Err,
    ensures
        fits_exprs(db, env, es),
        eval_exprs(db, env, es) == eval_exprs(db, env, es.take(n)),
    decreases es.len(),
{
    hide(fits_exprs);
    hide(eval_exprs);
    hide(fits_expr);
    hide(eval_expr);
    if n == es.len() {
        assert(es.take(n) =~= es);
    } else {
        let d = es.drop_last();
        assert(d.take(n) =~= es.take(n));
        lemma_exprs_err_extends(db, env, d, n);
        lemma_eval_exprs_step(db, env, es);
        lemma_fits_exprs_unfold(db, env, es);
    }
}

// ---- Timestamp representation invariant ----

/// Representation invariant carried by environments: every timestamp value is inside PostgreSQL's range
/// (true for `db_wf` inputs and preserved by every operator).
pub open spec fn val_ts_ok(v: Val) -> bool {
    v matches Val::Ts(t) ==> crate::spec::datetime::ts_valid(t)
}

/// Every value of the row satisfies `val_ts_ok`.
pub open spec fn row_ts_ok(r: Row) -> bool {
    forall|i: int| 0 <= i < r.len() ==> val_ts_ok(#[trigger] r[i])
}

} // verus!
