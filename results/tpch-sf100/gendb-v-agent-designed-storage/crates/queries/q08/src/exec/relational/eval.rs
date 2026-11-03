//! The recursive evaluator of conditions and queries, mirroring `spec::eval`: `exec_pred` and `exec_query`.
//! Postconditions are the compositional bridge for every predicate/query AST of any depth and arity: a result
//! equals the denotation and the domain predicate holds; `Capacity` means the domain predicate
//! (`exec::relational::domain`) fails. Both contracts are named once (`pred_outcome_ok`, `query_outcome_ok`).
//!
//! Each function only dispatches: `exec_pred` to `exec_pred_{scalar,logic,sub}` by constructor group, and
//! `exec_query` to one `exec_query_<constructor>` helper per constructor, which evaluates the inputs and applies the
//! row operator of `exec::relational::{ops, group}`. Each constructor's unfolding and lemmas are thus proved in
//! their own, bounded Verus query.
//!
//! Termination: lexicographic (AST node, rank): the `exec_pred_<group>` helpers (p, 0) < `exec_pred` (p, 1) <
//! `exec_left_join_row` / `exec_filter` (node, 2) < `exec_left_join` (on, 3); the `exec_query_<constructor>`
//! helpers (q, 2) < `exec_query` (q, 3); with `exec_expr` and its helpers (e, 0 to 2; see `exec::expr`),
//! `exec_exprs` (es, 1), `exec_project` (exprs, 2), `exec_agg_arg` (a), `exec_agg_args` (aggs, 1),
//! `exec_aggregate` (aggs, 2) and `exec_group_by` (q, 1) in the same recursion. Every call either descends into a
//! strict sub-AST or stays on the same node with a smaller rank.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::domain::*;
use crate::exec::scalar::*;
use crate::exec::expr::*;
use crate::exec::equality::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::domain::*;
use crate::exec::relational::ops::*;
use crate::exec::relational::group::*;

verus! {

// ------------------------------------------------------------------ conditions

/// Contract of evaluating condition `p` under environment `env`: a truth value or SQL error equal to
/// `spec::eval::eval_pred` inside the domain, `Capacity` exactly outside it.
pub open spec fn pred_outcome_ok(db: Database, env: Row, p: Pred, r: Outcome<Truth>) -> bool {
    match r {
        Ok(res) => fits_pred(db, env, p) && res == eval_pred(db, env, p),
        Err(_) => !fits_pred(db, env, p),
    }
}

/// `spec::eval::eval_pred` under environment `env`.
pub fn exec_pred(db: &EDatabase, env: &ERow, p: &EPred) -> (r: Outcome<Truth>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(env@)),
    ensures pred_outcome_ok(db@, view_row(env@), view_pred(*p), r),
    decreases p, 1nat,
{
    match p {
        EPred::Cmp { .. } | EPred::IsNull(_) | EPred::OfBool(_) => exec_pred_scalar(db, env, p),
        EPred::And(..) | EPred::Or(..) | EPred::Not(_) => exec_pred_logic(db, env, p),
        EPred::Exists(_) | EPred::AnyCmp { .. } => exec_pred_sub(db, env, p),
    }
}

/// `exec_pred` on `Cmp`, `IsNull` and `OfBool` (scalar operands).
fn exec_pred_scalar(db: &EDatabase, env: &ERow, p: &EPred) -> (r: Outcome<Truth>)
    requires
        p is Cmp || p is IsNull || p is OfBool,
        db_ts_ok(db@),
        row_ts_ok(view_row(env@)),
    ensures pred_outcome_ok(db@, view_row(env@), view_pred(*p), r),
    decreases p, 0nat,
{
    match p {
        EPred::Cmp { op, a, b } => {
            let va = match exec_expr(db, env, a) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(v)) => v,
            };
            let vb = match exec_expr(db, env, b) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(v)) => v,
            };
            Ok(cmp_truth_exec(*op, &va, &vb))
        },
        EPred::IsNull(e) => {
            let v = match exec_expr(db, env, e) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(v)) => v,
            };
            Ok(Ok(truth_of_exec(matches!(v, EVal::Null))))
        },
        EPred::OfBool(e) => {
            let v = match exec_expr(db, env, e) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(v)) => v,
            };
            Ok(truth_of_val_exec(&v))
        },
        _ => unreached(),
    }
}

/// `exec_pred` on `And`, `Or` and `Not` (sub-predicates).
fn exec_pred_logic(db: &EDatabase, env: &ERow, p: &EPred) -> (r: Outcome<Truth>)
    requires
        p is And || p is Or || p is Not,
        db_ts_ok(db@),
        row_ts_ok(view_row(env@)),
    ensures pred_outcome_ok(db@, view_row(env@), view_pred(*p), r),
    decreases p, 0nat,
{
    match p {
        EPred::And(a, b) => {
            let ta = match exec_pred(db, env, a) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(t)) => t,
            };
            let tb = match exec_pred(db, env, b) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(t)) => t,
            };
            Ok(Ok(truth_and_exec(ta, tb)))
        },
        EPred::Or(a, b) => {
            let ta = match exec_pred(db, env, a) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(t)) => t,
            };
            let tb = match exec_pred(db, env, b) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(t)) => t,
            };
            Ok(Ok(truth_or_exec(ta, tb)))
        },
        EPred::Not(a) => {
            let t = match exec_pred(db, env, a) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(t)) => t,
            };
            Ok(Ok(truth_not_exec(t)))
        },
        _ => unreached(),
    }
}

/// `exec_pred` on `Exists` and `AnyCmp` (subqueries).
fn exec_pred_sub(db: &EDatabase, env: &ERow, p: &EPred) -> (r: Outcome<Truth>)
    requires
        p is Exists || p is AnyCmp,
        db_ts_ok(db@),
        row_ts_ok(view_row(env@)),
    ensures pred_outcome_ok(db@, view_row(env@), view_pred(*p), r),
    decreases p, 0nat,
{
    match p {
        EPred::Exists(q) => {
            let rows = match exec_query(db, env, q) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            Ok(Ok(truth_of_exec(rows.len() > 0)))
        },
        EPred::AnyCmp { op, e, q } => {
            let v = match exec_expr(db, env, e) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(v)) => v,
            };
            let rows = match exec_query(db, env, q) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            Ok(any_cmp_truth_exec(*op, &v, &rows))
        },
        _ => unreached(),
    }
}

/// `spec::eval::any_cmp_truth` (Kleene OR over the rows in order; first error).
pub fn any_cmp_truth_exec(op: CmpOp, v: &EVal, rows: &Vec<ERow>) -> (r: Result<Truth, SqlError>)
    ensures r == any_cmp_truth(op, v@, view_rows(rows@)),
{
    let ghost g = view_rows(rows@);
    let mut acc = Truth::False;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<Row>::empty()); }
    while i < rows.len()
        invariant
            i <= rows.len(), g == view_rows(rows@),
            any_cmp_truth(op, v@, g.take(i as int)) == Ok::<Truth, SqlError>(acc),
        decreases rows.len() - i,
    {
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == g[i as int]);
            assert(g[i as int] == view_row(rows@[i as int]@));
        }
        if rows[i].len() == 0 {
            proof { lemma_any_cmp_err_extends(op, v@, g, i as int + 1); }
            return Err(SqlError::TypeError);
        }
        proof { assert(g[i as int][0] == rows@[i as int]@[0]@); }
        match cmp_truth_exec(op, v, &rows[i][0]) {
            Err(e) => {
                proof { lemma_any_cmp_err_extends(op, v@, g, i as int + 1); }
                return Err(e);
            },
            Ok(u) => { acc = truth_or_exec(acc, u); },
        }
        i = i + 1;
    }
    proof { assert(g.take(rows.len() as int) =~= g); }
    Ok(acc)
}

/// An error in a prefix of the rows is the outcome of `any_cmp_truth` on all of them.
proof fn lemma_any_cmp_err_extends(op: CmpOp, v: Val, rows: Seq<Row>, n: int)
    requires 0 < n <= rows.len(), any_cmp_truth(op, v, rows.take(n)) is Err,
    ensures any_cmp_truth(op, v, rows) == any_cmp_truth(op, v, rows.take(n)),
    decreases rows.len(),
{
    if n == rows.len() {
        assert(rows.take(n) =~= rows);
    } else {
        let d = rows.drop_last();
        assert(d.take(n) =~= rows.take(n));
        lemma_any_cmp_err_extends(op, v, d, n);
    }
}

// ------------------------------------------------------------------ queries

/// Contract of evaluating query `q` under outer context `ctx`: rows or a SQL error equal to
/// `spec::eval::eval_query` inside the domain (rows meeting the timestamp invariant), `Capacity` exactly outside it.
pub open spec fn query_outcome_ok(db: Database, ctx: Row, q: Query, r: Outcome<Vec<ERow>>) -> bool {
    match r {
        Ok(res) => fits_query(db, ctx, q) && rel_outcome_ok(res, eval_query(db, ctx, q)),
        Err(_) => !fits_query(db, ctx, q),
    }
}

/// `spec::eval::eval_query` under outer context `ctx`. Every helper has this exact postcondition for its
/// constructor, so the dispatcher needs neither definition (`eval_query`/`fits_query` are hidden here).
pub fn exec_query(db: &EDatabase, ctx: &ERow, q: &EQuery) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
    ensures query_outcome_ok(db@, view_row(ctx@), view_query(*q), r),
    decreases q, 3nat,
{
    hide(eval_query);
    hide(fits_query);
    match q {
        EQuery::Table(_) => exec_query_table(db, ctx, q),
        EQuery::Filter { .. } => exec_query_filter(db, ctx, q),
        EQuery::Project { .. } => exec_query_project(db, ctx, q),
        EQuery::Product { .. } => exec_query_product(db, ctx, q),
        EQuery::LeftJoin { .. } => exec_query_left_join(db, ctx, q),
        EQuery::Aggregate { .. } => exec_query_aggregate(db, ctx, q),
        EQuery::GroupBy { .. } => exec_query_group_by(db, ctx, q),
        EQuery::Distinct(_) => exec_query_distinct(db, ctx, q),
    }
}

/// `exec_query` on `Query::Table`.
fn exec_query_table(db: &EDatabase, ctx: &ERow, q: &EQuery) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        q is Table,
    ensures query_outcome_ok(db@, view_row(ctx@), view_query(*q), r),
{
    match q {
        EQuery::Table(t) => Ok(exec_table(db, *t)),
        _ => unreached(),
    }
}

/// `exec_query` on `Query::Filter`.
fn exec_query_filter(db: &EDatabase, ctx: &ERow, q: &EQuery) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        q is Filter,
    ensures query_outcome_ok(db@, view_row(ctx@), view_query(*q), r),
    decreases q, 2nat,
{
    let ghost gc = view_row(ctx@);
    match q {
        EQuery::Filter { pred, input } => {
            proof {
                lemma_eval_filter(db@, gc, view_pred(*pred), Box::new(view_query(**input)));
                lemma_fits_filter(db@, gc, view_pred(*pred), Box::new(view_query(**input)));
            }
            let rows = match exec_query(db, ctx, input) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            exec_filter(db, ctx, pred, &rows)
        },
        _ => unreached(),
    }
}

/// `exec_query` on `Query::Project`.
fn exec_query_project(db: &EDatabase, ctx: &ERow, q: &EQuery) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        q is Project,
    ensures query_outcome_ok(db@, view_row(ctx@), view_query(*q), r),
    decreases q, 2nat,
{
    let ghost gc = view_row(ctx@);
    match q {
        EQuery::Project { exprs, input } => {
            proof { lemma_eval_project(db@, gc, view_exprs(exprs@), Box::new(view_query(**input))); }
            let rows = match exec_query(db, ctx, input) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            exec_project(db, ctx, exprs, &rows)
        },
        _ => unreached(),
    }
}

/// `exec_query` on `Query::Product`.
fn exec_query_product(db: &EDatabase, ctx: &ERow, q: &EQuery) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        q is Product,
    ensures query_outcome_ok(db@, view_row(ctx@), view_query(*q), r),
    decreases q, 2nat,
{
    match q {
        EQuery::Product { left, right } => {
            let l = match exec_query(db, ctx, left) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            let r = match exec_query(db, ctx, right) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            Ok(Ok(product_rows_exec(&l, &r)))
        },
        _ => unreached(),
    }
}

/// `exec_query` on `Query::LeftJoin`. The padding width (the right input's static arity) is computed first:
/// `Capacity` when it exceeds `usize`, before either input is evaluated.
fn exec_query_left_join(db: &EDatabase, ctx: &ERow, q: &EQuery) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        q is LeftJoin,
    ensures query_outcome_ok(db@, view_row(ctx@), view_query(*q), r),
    decreases q, 2nat,
{
    let ghost gc = view_row(ctx@);
    match q {
        EQuery::LeftJoin { left, right, on } => {
            proof {
                lemma_eval_left_join(db@, gc, Box::new(view_query(**left)), Box::new(view_query(**right)), view_pred(*on));
                lemma_fits_left_join(db@, gc, Box::new(view_query(**left)), Box::new(view_query(**right)), view_pred(*on));
            }
            let right_arity = match query_arity_exec(&db.schema, right) {
                None => return Err(Capacity),
                Some(n) => n,
            };
            let l = match exec_query(db, ctx, left) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            let r = match exec_query(db, ctx, right) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            exec_left_join(db, ctx, on, &l, &r, right_arity)
        },
        _ => unreached(),
    }
}

/// `exec_query` on `Query::Aggregate`.
fn exec_query_aggregate(db: &EDatabase, ctx: &ERow, q: &EQuery) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        q is Aggregate,
    ensures query_outcome_ok(db@, view_row(ctx@), view_query(*q), r),
    decreases q, 2nat,
{
    let ghost gc = view_row(ctx@);
    match q {
        EQuery::Aggregate { aggs, input } => {
            proof { lemma_eval_aggregate(db@, gc, view_aggs(aggs@), Box::new(view_query(**input))); }
            let rows = match exec_query(db, ctx, input) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            exec_aggregate(db, ctx, aggs, &rows)
        },
        _ => unreached(),
    }
}

/// `exec_query` on `Query::GroupBy`.
fn exec_query_group_by(db: &EDatabase, ctx: &ERow, q: &EQuery) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        q is GroupBy,
    ensures query_outcome_ok(db@, view_row(ctx@), view_query(*q), r),
    decreases q, 2nat,
{
    let ghost gc = view_row(ctx@);
    match q {
        EQuery::GroupBy { keys, aggs, input } => {
            proof {
                lemma_eval_group_by(db@, gc, view_exprs(keys@), view_aggs(aggs@), Box::new(view_query(**input)));
                lemma_fits_group_by(db@, gc, view_exprs(keys@), view_aggs(aggs@), Box::new(view_query(**input)));
            }
            let rows = match exec_query(db, ctx, input) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            exec_group_by(db, ctx, q, &rows)
        },
        _ => unreached(),
    }
}

/// `exec_query` on `Query::Distinct`: `spec::eval::distinct_query_rows`, the first row of each not-distinct class.
fn exec_query_distinct(db: &EDatabase, ctx: &ERow, q: &EQuery) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        q is Distinct,
    ensures query_outcome_ok(db@, view_row(ctx@), view_query(*q), r),
    decreases q, 2nat,
{
    match q {
        EQuery::Distinct(input) => {
            let rows = match exec_query(db, ctx, input) {
                Err(c) => return Err(c),
                Ok(Err(e)) => return Ok(Err(e)),
                Ok(Ok(rows)) => rows,
            };
            Ok(Ok(distinct_rows_exec(&rows)))
        },
        _ => unreached(),
    }
}

} // verus!
