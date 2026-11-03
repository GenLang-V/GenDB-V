//! L6, decorrelation (engine toolkit; nothing here names a query, a table or a column).
//!
//! A subquery inside a condition sees the outer environment `ctx ++ outer row` as its context (hazard H4). These
//! rules replace per-row evaluation by one evaluation, a semi- or anti-join, or a grouped lookup, under explicit
//! side conditions:
//! - EXISTS / NOT EXISTS (`lemma_exists_semi`, `lemma_semi_join`, `lemma_anti_join`): when the inner query has
//!   one value for every outer row (L2: it reads no position of the outer row) and the correlated condition
//!   never errs on any (outer, inner) pair (H1: a semi-join skips non-matching pairs), the filter keeps the outer
//!   rows with (without) a matching inner row.
//! - IN / NOT IN (`lemma_in_semi`, `lemma_in_semi_join`, `lemma_not_in_anti_join`): with a non-NULL left value
//!   and non-NULL subquery values (NOT NULL columns), `IN` is never `Unknown`, so NOT IN is the complement of IN;
//!   on values of one exact type the match is equality (`lemma_in_exact`), a hash-set probe.
//! - Equality-correlated scalar aggregate (`lemma_aggregate_lookup`, `lemma_lookup_group`): the aggregate over
//!   the inner rows whose key matches the outer key `k` (not distinct from it) is the aggregate row of the group of
//!   `k` in a GROUP BY of the inner rows on that key (the same member sequence, so no H2 condition), and the
//!   aggregate of no rows when `k` has no group.
//! - Uncorrelated scalar subquery (`lemma_subquery_once`, `lemma_cmp_hoisted`, with `engine_link::ops::
//!   lemma_filter_all_err`): one outcome for every environment of one length, so it is evaluated once; an error
//!   is raised only if some row reaches it.
//! Helpers for the conditions these rules take: `lemma_pred_and_keeps` (conjunctions), `lemma_eq_exact`
//! (equality of exact values), `lemma_eq_key` (a correlation key column).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::bridge::collect::*;
use crate::bridge::equality::*;
use crate::link::join::{keep, lemma_keep_keep, lemma_keep_members};
use crate::link::exists::lemma_exists_filter;
use crate::engine_link::ops::*;
use crate::engine_link::locality::*;
use crate::engine_link::congruence::lemma_group_members_keep;

verus! {

// ------------------------------------------------------------------------------------- condition helpers

/// A conjunction of two error-free conditions is error-free, and `True` exactly when both are.
pub proof fn lemma_pred_and_keeps(db: Database, env: Row, a: Pred, b: Pred)
    requires eval_pred(db, env, a) is Ok, eval_pred(db, env, b) is Ok,
    ensures
        eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) is Ok,
        (eval_pred(db, env, Pred::And(Box::new(a), Box::new(b)))->Ok_0 is True)
            == ((eval_pred(db, env, a)->Ok_0 is True) && (eval_pred(db, env, b)->Ok_0 is True)),
{
}

/// Equality of two non-NULL values of one exact type is two-valued structural equality.
pub proof fn lemma_eq_exact(db: Database, env: Row, a: Expr, b: Expr, va: Val, vb: Val)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(vb),
        !(va is Null), !(vb is Null), same_exact_type(va, vb),
    ensures eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a, b }) == Ok::<Truth, SqlError>(truth_of(va == vb)),
{
    lemma_val_not_distinct_structural(va, vb);
}

// ------------------------------------------------------------------------------------- EXISTS / NOT EXISTS

/// Some inner row matches outer row `o` (the condition is `True` on `ctx + o + inner row`).
pub open spec fn matches_any(db: Database, ctx: Row, o: Row, irows: Seq<Row>, p: Pred) -> bool {
    exists|j: int| 0 <= j < irows.len() && #[trigger] eval_pred(db, ctx + o + irows[j], p) == Ok::<Truth, SqlError>(Truth::True)
}

/// The correlated condition never errs on any (outer, inner) pair (H1 for a semi-join, which skips pairs).
pub open spec fn pairs_total(db: Database, ctx: Row, orows: Seq<Row>, irows: Seq<Row>, p: Pred) -> bool {
    forall|i: int, j: int| 0 <= i < orows.len() && 0 <= j < irows.len() ==> #[trigger] eval_pred(db, ctx + orows[i] + irows[j], p) is Ok
}

/// The outer rows with a matching inner row.
pub open spec fn semi_keeps(db: Database, ctx: Row, irows: Seq<Row>, p: Pred) -> spec_fn(Row) -> bool {
    |o: Row| matches_any(db, ctx, o, irows, p)
}

/// The outer rows without a matching inner row.
pub open spec fn anti_keeps(db: Database, ctx: Row, irows: Seq<Row>, p: Pred) -> spec_fn(Row) -> bool {
    |o: Row| !matches_any(db, ctx, o, irows, p)
}

/// The EXISTS condition `EXISTS (SELECT .. FROM inner WHERE p)`.
pub open spec fn exists_pred(p: Pred, inner: Query) -> Pred {
    Pred::Exists(Box::new(Query::Filter { pred: p, input: Box::new(inner) }))
}

/// L6, EXISTS for one outer row: whether some inner row matches, when the inner query evaluates to `irows` in
/// the outer row's environment and the condition never errs on its pairs.
pub proof fn lemma_exists_semi(db: Database, ctx: Row, o: Row, inner: Query, irows: Seq<Row>, p: Pred)
    requires
        eval_query(db, ctx + o, inner) == Ok::<Relation, SqlError>(irows),
        forall|j: int| 0 <= j < irows.len() ==> #[trigger] eval_pred(db, ctx + o + irows[j], p) is Ok,
    ensures
        eval_pred(db, ctx + o, exists_pred(p, inner)) == Ok::<Truth, SqlError>(truth_of(matches_any(db, ctx, o, irows, p))),
{
    lemma_exists_filter(db, ctx + o, p, Box::new(inner), irows);
}

/// L6, semi-join: a WHERE EXISTS over outer rows keeps exactly the outer rows with a matching inner row, when the
/// inner query has the one value `irows` for every outer row (L2: `lemma_query_ctx_free`) and the condition never
/// errs on any pair.
pub proof fn lemma_semi_join(db: Database, ctx: Row, orows: Seq<Row>, inner: Query, irows: Seq<Row>, p: Pred)
    requires
        forall|i: int| 0 <= i < orows.len() ==> eval_query(db, ctx + #[trigger] orows[i], inner) == Ok::<Relation, SqlError>(irows),
        pairs_total(db, ctx, orows, irows, p),
    ensures
        filter_op(db, ctx, orows, exists_pred(p, inner)) == Ok::<Relation, SqlError>(keep(orows, semi_keeps(db, ctx, irows, p))),
{
    assert forall|i: int| 0 <= i < orows.len() implies {
        &&& #[trigger] eval_pred(db, ctx + orows[i], exists_pred(p, inner)) is Ok
        &&& (eval_pred(db, ctx + orows[i], exists_pred(p, inner))->Ok_0 is True) == semi_keeps(db, ctx, irows, p)(orows[i])
    } by {
        assert forall|j: int| 0 <= j < irows.len() implies #[trigger] eval_pred(db, ctx + orows[i] + irows[j], p) is Ok by {}
        lemma_exists_semi(db, ctx, orows[i], inner, irows, p);
    }
    lemma_filter_keeps(db, ctx, orows, exists_pred(p, inner), semi_keeps(db, ctx, irows, p));
}

/// L6, anti-join: WHERE NOT EXISTS keeps exactly the outer rows without a matching inner row.
pub proof fn lemma_anti_join(db: Database, ctx: Row, orows: Seq<Row>, inner: Query, irows: Seq<Row>, p: Pred)
    requires
        forall|i: int| 0 <= i < orows.len() ==> eval_query(db, ctx + #[trigger] orows[i], inner) == Ok::<Relation, SqlError>(irows),
        pairs_total(db, ctx, orows, irows, p),
    ensures
        filter_op(db, ctx, orows, Pred::Not(Box::new(exists_pred(p, inner))))
            == Ok::<Relation, SqlError>(keep(orows, anti_keeps(db, ctx, irows, p))),
{
    let np = Pred::Not(Box::new(exists_pred(p, inner)));
    assert forall|i: int| 0 <= i < orows.len() implies {
        &&& #[trigger] eval_pred(db, ctx + orows[i], np) is Ok
        &&& (eval_pred(db, ctx + orows[i], np)->Ok_0 is True) == anti_keeps(db, ctx, irows, p)(orows[i])
    } by {
        assert forall|j: int| 0 <= j < irows.len() implies #[trigger] eval_pred(db, ctx + orows[i] + irows[j], p) is Ok by {}
        lemma_exists_semi(db, ctx, orows[i], inner, irows, p);
    }
    lemma_filter_keeps(db, ctx, orows, np, anti_keeps(db, ctx, irows, p));
}

// ------------------------------------------------------------------------------------- IN / NOT IN

/// Some single-column row compares equal to `v` (SQL equality, `compare == 0`).
pub open spec fn in_match(v: Val, rows: Seq<Row>) -> bool {
    exists|j: int| 0 <= j < rows.len() && #[trigger] compare(v, rows[j][0]) == Some(0int)
}

/// Every row has a first column that is not NULL and is comparable with `v`.
pub open spec fn in_rows_ok(v: Val, rows: Seq<Row>) -> bool {
    forall|j: int| 0 <= j < rows.len() ==> (#[trigger] rows[j]).len() >= 1 && !(rows[j][0] is Null) && compare(v, rows[j][0]) is Some
}

/// `v = ANY (rows)` of a non-NULL value over non-NULL comparable values: two-valued membership.
pub proof fn lemma_any_eq_two_valued(v: Val, rows: Seq<Row>)
    requires !(v is Null), in_rows_ok(v, rows),
    ensures any_cmp_truth(CmpOp::Eq, v, rows) == Ok::<Truth, SqlError>(truth_of(in_match(v, rows))),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|j: int| 0 <= j < d.len() implies (#[trigger] d[j]).len() >= 1 && !(d[j][0] is Null) && compare(v, d[j][0]) is Some by {
            assert(d[j] == rows[j]);
        }
        lemma_any_eq_two_valued(v, d);
        let last = rows[rows.len() - 1];
        assert(rows.last() == last);
        if in_match(v, rows) && !(compare(v, last[0]) == Some(0int)) {
            let j = choose|j: int| 0 <= j < rows.len() && #[trigger] compare(v, rows[j][0]) == Some(0int);
            assert(d[j] == rows[j]);
        }
        if in_match(v, d) {
            let j = choose|j: int| 0 <= j < d.len() && #[trigger] compare(v, d[j][0]) == Some(0int);
            assert(rows[j] == d[j]);
        }
        if compare(v, last[0]) == Some(0int) {
            assert(compare(v, rows[rows.len() - 1][0]) == Some(0int));
        }
    }
}

/// L6, IN for one environment: with a non-NULL left value and a subquery of non-NULL comparable values, `IN` is
/// two-valued membership and `NOT IN` its complement.
pub proof fn lemma_in_semi(db: Database, env: Row, e: Expr, q: Query, v: Val, rows: Seq<Row>)
    requires
        eval_expr(db, env, e) == Ok::<Val, SqlError>(v),
        !(v is Null),
        eval_query(db, env, q) == Ok::<Relation, SqlError>(rows),
        in_rows_ok(v, rows),
    ensures
        eval_pred(db, env, Pred::AnyCmp { op: CmpOp::Eq, e, q: Box::new(q) }) == Ok::<Truth, SqlError>(truth_of(in_match(v, rows))),
        eval_pred(db, env, Pred::Not(Box::new(Pred::AnyCmp { op: CmpOp::Eq, e, q: Box::new(q) })))
            == Ok::<Truth, SqlError>(truth_of(!in_match(v, rows))),
{
    lemma_any_eq_two_valued(v, rows);
}

/// On values of one exact type, SQL equality membership is equality membership (a hash-set probe).
pub proof fn lemma_in_exact(v: Val, rows: Seq<Row>)
    requires
        !(v is Null), in_rows_ok(v, rows),
        forall|j: int| 0 <= j < rows.len() ==> same_exact_type(v, #[trigger] rows[j][0]),
    ensures in_match(v, rows) == exists|j: int| 0 <= j < rows.len() && #[trigger] rows[j][0] == v,
{
    if in_match(v, rows) {
        let j = choose|j: int| 0 <= j < rows.len() && #[trigger] compare(v, rows[j][0]) == Some(0int);
        lemma_val_not_distinct_structural(v, rows[j][0]);
    }
    if exists|j: int| 0 <= j < rows.len() && #[trigger] rows[j][0] == v {
        let j = choose|j: int| 0 <= j < rows.len() && #[trigger] rows[j][0] == v;
        lemma_val_not_distinct_refl(v);
        lemma_val_not_distinct_structural(v, rows[j][0]);
        assert(compare(v, rows[j][0]) == Some(0int));
    }
}

/// The outer rows whose left value is a member.
pub open spec fn in_keeps(db: Database, ctx: Row, e: Expr, rows: Seq<Row>) -> spec_fn(Row) -> bool {
    |o: Row| in_match(eval_expr(db, ctx + o, e)->Ok_0, rows)
}

/// The outer rows whose left value is not a member.
pub open spec fn not_in_keeps(db: Database, ctx: Row, e: Expr, rows: Seq<Row>) -> spec_fn(Row) -> bool {
    |o: Row| !in_match(eval_expr(db, ctx + o, e)->Ok_0, rows)
}

/// For every outer row: the left value is a non-NULL value, the subquery has the one value `rows`, and its
/// values are non-NULL and comparable with the left value.
pub open spec fn in_side_ok(db: Database, ctx: Row, orows: Seq<Row>, e: Expr, q: Query, rows: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < orows.len() ==> {
        &&& #[trigger] eval_expr(db, ctx + orows[i], e) is Ok
        &&& !(eval_expr(db, ctx + orows[i], e)->Ok_0 is Null)
        &&& eval_query(db, ctx + orows[i], q) == Ok::<Relation, SqlError>(rows)
        &&& in_rows_ok(eval_expr(db, ctx + orows[i], e)->Ok_0, rows)
    }
}

/// L6, IN semi-join: WHERE `e IN (q)` keeps exactly the outer rows whose value is a member of the subquery's one
/// value `rows`.
pub proof fn lemma_in_semi_join(db: Database, ctx: Row, orows: Seq<Row>, e: Expr, q: Query, rows: Seq<Row>)
    requires in_side_ok(db, ctx, orows, e, q, rows),
    ensures
        filter_op(db, ctx, orows, Pred::AnyCmp { op: CmpOp::Eq, e, q: Box::new(q) })
            == Ok::<Relation, SqlError>(keep(orows, in_keeps(db, ctx, e, rows))),
{
    let p = Pred::AnyCmp { op: CmpOp::Eq, e, q: Box::new(q) };
    assert forall|i: int| 0 <= i < orows.len() implies {
        &&& #[trigger] eval_pred(db, ctx + orows[i], p) is Ok
        &&& (eval_pred(db, ctx + orows[i], p)->Ok_0 is True) == in_keeps(db, ctx, e, rows)(orows[i])
    } by {
        assert(eval_expr(db, ctx + orows[i], e) is Ok);
        lemma_in_semi(db, ctx + orows[i], e, q, eval_expr(db, ctx + orows[i], e)->Ok_0, rows);
    }
    lemma_filter_keeps(db, ctx, orows, p, in_keeps(db, ctx, e, rows));
}

/// L6, NOT IN anti-join: WHERE `e NOT IN (q)` keeps exactly the outer rows whose value is not a member.
pub proof fn lemma_not_in_anti_join(db: Database, ctx: Row, orows: Seq<Row>, e: Expr, q: Query, rows: Seq<Row>)
    requires in_side_ok(db, ctx, orows, e, q, rows),
    ensures
        filter_op(db, ctx, orows, Pred::Not(Box::new(Pred::AnyCmp { op: CmpOp::Eq, e, q: Box::new(q) })))
            == Ok::<Relation, SqlError>(keep(orows, not_in_keeps(db, ctx, e, rows))),
{
    let p = Pred::Not(Box::new(Pred::AnyCmp { op: CmpOp::Eq, e, q: Box::new(q) }));
    assert forall|i: int| 0 <= i < orows.len() implies {
        &&& #[trigger] eval_pred(db, ctx + orows[i], p) is Ok
        &&& (eval_pred(db, ctx + orows[i], p)->Ok_0 is True) == not_in_keeps(db, ctx, e, rows)(orows[i])
    } by {
        assert(eval_expr(db, ctx + orows[i], e) is Ok);
        lemma_in_semi(db, ctx + orows[i], e, q, eval_expr(db, ctx + orows[i], e)->Ok_0, rows);
    }
    lemma_filter_keeps(db, ctx, orows, p, not_in_keeps(db, ctx, e, rows));
}

// ------------------------------------------------------------------------------------- grouped lookup

/// One key column of an equality correlation: `a = b` with a non-NULL outer value `vb` never errs and is `True`
/// exactly when the one-column keys are not distinct (a NULL inner value gives `Unknown`, and is distinct from
/// `vb`). The premise of `lemma_aggregate_lookup` for one key column; conjunctions combine with
/// `lemma_pred_and_keeps`.
pub proof fn lemma_eq_key(db: Database, env: Row, a: Expr, b: Expr, va: Val, vb: Val)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(vb),
        !(vb is Null),
        va is Null || compare(va, vb) is Some,
    ensures
        eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a, b }) is Ok,
        (eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a, b })->Ok_0 is True) == row_not_distinct(seq![va], seq![vb]),
{
    assert(seq![va][0] == va && seq![vb][0] == vb);
    assert(row_not_distinct(seq![va], seq![vb]) == val_not_distinct(va, vb));
}

/// Every key has a representative in `distinct_rows` it is not distinct from.
pub proof fn lemma_distinct_rows_covers(ks: Seq<Row>, i: int) -> (g: int)
    requires 0 <= i < ks.len(),
    ensures 0 <= g < distinct_rows(ks).len(), row_not_distinct(distinct_rows(ks)[g], ks[i]),
    decreases ks.len(),
{
    let d = distinct_rows(ks.drop_last());
    if i < ks.len() - 1 {
        let g = lemma_distinct_rows_covers(ks.drop_last(), i);
        assert(ks.drop_last()[i] == ks[i]);
        assert(distinct_rows(ks)[g] == d[g]);
        g
    } else {
        let x = ks.last();
        if has_not_distinct(d, x) {
            let g = lemma_has_not_distinct_witness(d, x);
            assert(distinct_rows(ks)[g] == d[g]);
            g
        } else {
            lemma_row_not_distinct_refl(x);
            d.len() as int
        }
    }
}

proof fn lemma_has_not_distinct_witness(d: Seq<Row>, x: Row) -> (g: int)
    requires has_not_distinct(d, x),
    ensures 0 <= g < d.len(), row_not_distinct(d[g], x),
    decreases d.len(),
{
    if row_not_distinct(d.last(), x) {
        d.len() - 1
    } else {
        let g = lemma_has_not_distinct_witness(d.drop_last(), x);
        assert(d.drop_last()[g] == d[g]);
        g
    }
}

/// Members of keys not distinct from `k` and from `rep` (with `rep` not distinct from `k`) are the same.
proof fn lemma_group_members_same(ks: Seq<Row>, args: Seq<Row>, k: Row, rep: Row)
    requires row_not_distinct(rep, k),
    ensures group_members(ks, args, k) == group_members(ks, args, rep),
    decreases ks.len(),
{
    if ks.len() > 0 && args.len() > 0 {
        lemma_group_members_same(ks.drop_last(), args.drop_last(), k, rep);
        let x = ks.last();
        lemma_row_not_distinct_symm(rep, k);
        if row_not_distinct(x, k) {
            lemma_row_not_distinct_trans(x, k, rep);
        }
        if row_not_distinct(x, rep) {
            lemma_row_not_distinct_trans(x, rep, k);
        }
    }
}

/// Members of a key not distinct from any key are none.
proof fn lemma_group_members_none(ks: Seq<Row>, args: Seq<Row>, k: Row)
    requires forall|i: int| 0 <= i < ks.len() ==> !row_not_distinct(#[trigger] ks[i], k),
    ensures group_members(ks, args, k) == Seq::<Row>::empty(),
    decreases ks.len(),
{
    if ks.len() > 0 && args.len() > 0 {
        assert forall|i: int| 0 <= i < ks.drop_last().len() implies !row_not_distinct(#[trigger] ks.drop_last()[i], k) by {
            assert(ks.drop_last()[i] == ks[i]);
        }
        lemma_group_members_none(ks.drop_last(), args.drop_last(), k);
        assert(!row_not_distinct(ks[ks.len() - 1], k));
    }
}

/// The group of key `k` in a GROUP BY: when some group representative is not distinct from `k`, `k`'s members are
/// that group's members; otherwise `k` has no members.
pub proof fn lemma_lookup_group(ks: Seq<Row>, args: Seq<Row>, k: Row)
    ensures
        forall|g: int| 0 <= g < distinct_rows(ks).len() && row_not_distinct(#[trigger] distinct_rows(ks)[g], k)
            ==> group_members(ks, args, k) == group_members(ks, args, distinct_rows(ks)[g]),
        (forall|g: int| 0 <= g < distinct_rows(ks).len() ==> !row_not_distinct(#[trigger] distinct_rows(ks)[g], k))
            ==> group_members(ks, args, k) == Seq::<Row>::empty(),
{
    let d = distinct_rows(ks);
    assert forall|g: int| 0 <= g < d.len() && row_not_distinct(#[trigger] d[g], k)
        implies group_members(ks, args, k) == group_members(ks, args, d[g]) by {
        lemma_group_members_same(ks, args, k, d[g]);
    }
    if forall|g: int| 0 <= g < d.len() ==> !row_not_distinct(#[trigger] d[g], k) {
        assert forall|i: int| 0 <= i < ks.len() implies !row_not_distinct(#[trigger] ks[i], k) by {
            let g = lemma_distinct_rows_covers(ks, i);
            if row_not_distinct(ks[i], k) {
                lemma_row_not_distinct_trans(d[g], ks[i], k);
            }
        }
        lemma_group_members_none(ks, args, k);
    }
}

/// The inner rows that match key `k`: their residual condition holds and their key is not distinct from `k`.
pub open spec fn key_keeps(resid: spec_fn(Row) -> bool, keyf: spec_fn(Row) -> Row, k: Row) -> spec_fn(Row) -> bool {
    |r: Row| resid(r) && row_not_distinct(keyf(r), k)
}

/// L6, equality-correlated scalar aggregate: an Aggregate over the inner rows that the correlated condition keeps
/// (residual `resid` and key `keyf` not distinct from the outer key `k`) is the aggregate row of `k`'s members
/// in a GROUP BY on `keyf` of the inner rows the residual keeps (`lemma_lookup_group` finds the group).
pub proof fn lemma_aggregate_lookup(db: Database, env: Row, aggs: Seq<Agg>, p: Pred, inner: Query, irows: Seq<Row>,
    resid: spec_fn(Row) -> bool, keyf: spec_fn(Row) -> Row, argf: spec_fn(Row) -> Row, k: Row)
    requires
        eval_query(db, env, inner) == Ok::<Relation, SqlError>(irows),
        pred_keeps(db, env, irows, p, key_keeps(resid, keyf, k)),
        forall|i: int| 0 <= i < irows.len() && #[trigger] key_keeps(resid, keyf, k)(irows[i])
            ==> agg_args(db, env + irows[i], aggs) == Ok::<Row, SqlError>(argf(irows[i])),
    ensures ({
        let kept = keep(irows, resid);
        eval_query(db, env, Query::Aggregate { aggs, input: Box::new(Query::Filter { pred: p, input: Box::new(inner) }) })
            == match agg_row(aggs, group_members(kept.map_values(keyf), kept.map_values(argf), k)) {
                Ok(row) => Ok::<Relation, SqlError>(seq![row]),
                Err(e) => Err::<Relation, SqlError>(e),
            }
    }),
{
    let kk = key_keeps(resid, keyf, k);
    let fq = Query::Filter { pred: p, input: Box::new(inner) };
    lemma_eval_op(db, env, fq);
    lemma_filter_keeps(db, env, irows, p, kk);
    let rows = keep(irows, kk);
    lemma_eval_op(db, env, Query::Aggregate { aggs, input: Box::new(fq) });
    lemma_keep_members(irows, kk);
    let rs = agg_args_results(db, env, rows, aggs);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(rows.map_values(argf)[i]) by {
        assert(irows.contains(rows[i]) && kk(rows[i]));
        let j = choose|j: int| 0 <= j < irows.len() && irows[j] == rows[i];
        assert(kk(irows[j]));
    }
    lemma_collect_all(rs, rows.map_values(argf));
    let kept = keep(irows, resid);
    let pk = |r: Row| row_not_distinct(keyf(r), k);
    lemma_keep_keep(irows, resid, pk);
    crate::link::join::lemma_keep_ext(irows, |x: Row| resid(x) && pk(x), kk);
    lemma_group_members_keep(kept, keyf, argf, k);
}

// ------------------------------------------------------------------------------------- evaluate once

/// L6, uncorrelated scalar subquery: a subquery that reads no position of its environment has one outcome (and
/// one domain) in every environment of one length, so it is evaluated once.
pub proof fn lemma_subquery_once(db: Database, env1: Row, env2: Row, q: Query)
    requires env1.len() == env2.len(), query_reads(q, ctx_free(env1.len())),
    ensures
        eval_expr(db, env1, Expr::Subquery(Box::new(q))) == eval_expr(db, env2, Expr::Subquery(Box::new(q))),
        fits_expr(db, env1, Expr::Subquery(Box::new(q))) == fits_expr(db, env2, Expr::Subquery(Box::new(q))),
{
    lemma_query_ctx_free(db, env1, env2, q);
}

/// L6, a hoisted operand: a comparison whose right operand has the outcome `c` (evaluated once: a closed
/// expression, `link::expr::lemma_expr_closed`, or an uncorrelated subquery, `lemma_subquery_once`). An error of
/// `c` is the comparison's outcome whenever the left operand succeeds, so a filter over rows that all reach it
/// raises it exactly when there is a row (`engine_link::ops::lemma_filter_all_err`).
pub proof fn lemma_cmp_hoisted(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, c: Result<Val, SqlError>)
    requires eval_expr(db, env, b) == c,
    ensures
        eval_pred(db, env, Pred::Cmp { op, a, b }) == match eval_expr(db, env, a) {
            Err(e) => Err(e),
            Ok(va) => match c {
                Err(e) => Err::<Truth, SqlError>(e),
                Ok(vb) => cmp_truth(op, va, vb),
            },
        },
{
}

} // verus!
