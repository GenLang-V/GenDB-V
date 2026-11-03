//! Example: a correlated AVG on a key is a lookup in one GROUP BY (TPC-H Q17 style).
//!
//! Per outer row: `(SELECT AVG(inner.qty) FROM inner WHERE inner.key = outer.key)`. The planner rule: evaluate
//! `SELECT key, AVG(qty) FROM inner GROUP BY key` once (here in the empty context), then look up each outer row's
//! key; a key without a group gives the AVG of no rows (NULL). Proof route: L6 (`lemma_aggregate_lookup`,
//! `lemma_lookup_group`), with the key equality two-valued on int8 keys (`lemma_eq_exact`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::exec::relational::domain::*;
use crate::bridge::equality::*;
use crate::link::join::{keep, lemma_keep_all};
use crate::link::expr::lemma_expr_col;
use crate::link::query::{lemma_agg_arg_avg};
use crate::engine_link::ops::*;
use crate::engine_link::congruence::{group_key, group_args, lemma_group_by_op_values};
use crate::engine_link::decorrelate::*;
use crate::engine_pins::schema::*;

verus! {

/// AVG(inner.qty) in the environment `outer row ++ inner row` (inner.qty at 3 + 3).
pub open spec fn corr_aggs() -> Seq<Agg> {
    seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(6) }]
}

/// `inner.key = outer.key`.
pub open spec fn key_eq() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(0) }
}

/// The correlated subquery's body, evaluated in the environment of one outer row.
pub open spec fn correlated_avg() -> Query {
    Query::Aggregate { aggs: corr_aggs(), input: Box::new(Query::Filter { pred: key_eq(), input: Box::new(Query::Table(1)) }) }
}

/// AVG(inner.qty) over inner rows alone.
pub open spec fn group_aggs() -> Seq<Agg> {
    seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(3) }]
}

pub open spec fn group_keys() -> Seq<Expr> {
    seq![Expr::Col(0)]
}

/// `SELECT key, AVG(qty) FROM inner GROUP BY key`, evaluated once.
pub open spec fn grouped_avg() -> Query {
    Query::GroupBy { keys: group_keys(), aggs: group_aggs(), input: Box::new(Query::Table(1)) }
}

pub open spec fn inner_key() -> spec_fn(Row) -> Row {
    |r: Row| seq![r[0]]
}

pub open spec fn inner_qty() -> spec_fn(Row) -> Row {
    |r: Row| seq![r[3]]
}

pub open spec fn always() -> spec_fn(Row) -> bool {
    |r: Row| true
}

/// Two one-column int keys are not distinct exactly when equal.
proof fn lemma_int_key(a: Val, b: Val)
    requires a is Int, b is Int,
    ensures row_not_distinct(seq![a], seq![b]) == (a == b),
{
    lemma_val_not_distinct_structural(a, b);
    assert(seq![a][0] == a && seq![b][0] == b);
}

/// Per outer row `o`: the correlated AVG is the aggregate of the members of `o`'s key in the grouping of the inner
/// rows by key (the group whose representative has that key, if there is one; no rows otherwise), and the GROUP
/// BY evaluated once has exactly those groups.
pub proof fn example_correlated_avg_lookup(db: Database, o: Row)
    requires example_db(db), o.len() == 3, o[0] is Int,
    ensures ({
        let irows = db.tables[1];
        let (ks, args) = (irows.map_values(inner_key()), irows.map_values(inner_qty()));
        let k = seq![o[0]];
        &&& eval_query(db, o, correlated_avg()) == match agg_row(corr_aggs(), group_members(ks, args, k)) {
                Ok(row) => Ok::<Relation, SqlError>(seq![row]),
                Err(e) => Err::<Relation, SqlError>(e),
            }
        &&& eval_query(db, Seq::empty(), grouped_avg()) == group_rows(group_aggs(), ks, args)
        &&& forall|g: int| 0 <= g < distinct_rows(ks).len() && row_not_distinct(#[trigger] distinct_rows(ks)[g], k)
                ==> group_members(ks, args, k) == group_members(ks, args, distinct_rows(ks)[g])
        &&& (forall|g: int| 0 <= g < distinct_rows(ks).len() ==> !row_not_distinct(#[trigger] distinct_rows(ks)[g], k))
                ==> group_members(ks, args, k) == Seq::<Row>::empty()
        &&& forall|m: Seq<Row>| #[trigger] agg_row(corr_aggs(), m) == agg_row(group_aggs(), m)
    }),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    hide(eval_exprs);
    hide(agg_args);
    hide(agg_arg);
    lemma_example_rows(db);
    let irows = db.tables[1];
    let k = seq![o[0]];
    let kk = key_keeps(always(), inner_key(), k);
    // The correlated condition keeps the inner rows with the outer key.
    assert forall|i: int| 0 <= i < irows.len() implies {
        &&& #[trigger] eval_pred(db, o + irows[i], key_eq()) is Ok
        &&& (eval_pred(db, o + irows[i], key_eq())->Ok_0 is True) == kk(irows[i])
    } by {
        let r = irows[i];
        let env = o + r;
        assert(env[3] == r[0] && env[0] == o[0]);
        lemma_expr_col(db, env, 3);
        lemma_expr_col(db, env, 0);
        lemma_eq_exact(db, env, Expr::Col(3), Expr::Col(0), r[0], o[0]);
        lemma_int_key(r[0], o[0]);
    }
    assert forall|i: int| 0 <= i < irows.len() && #[trigger] kk(irows[i])
        implies agg_args(db, o + irows[i], corr_aggs()) == Ok::<Row, SqlError>(inner_qty()(irows[i])) by {
        let r = irows[i];
        let env = o + r;
        assert(env[6] == r[3]);
        lemma_expr_col(db, env, 6);
        lemma_agg_arg_avg(db, env, NumKind::Numeric, Expr::Col(6));
        lemma_one_arg(db, env, corr_aggs(), r[3]);
    }
    lemma_eval_op(db, o, Query::Table(1));
    lemma_aggregate_lookup(db, o, corr_aggs(), key_eq(), Query::Table(1), irows, always(), inner_key(), inner_qty(), k);
    lemma_keep_all(irows, always());
    // The GROUP BY, evaluated once in the empty context.
    let ctx = Seq::<Val>::empty();
    let gs = group_input_results(db, ctx, irows, group_keys(), group_aggs());
    let prep = Seq::new(irows.len(), |j: int| (inner_key()(irows[j]), inner_qty()(irows[j])));
    assert forall|i: int| 0 <= i < gs.len() implies #[trigger] gs[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        let r = irows[i];
        assert(ctx + r =~= r);
        lemma_group_input_results(db, ctx, irows, group_keys(), group_aggs(), i);
        lemma_key_col0(db, r);
        lemma_expr_col(db, r, 3);
        lemma_agg_arg_avg(db, r, NumKind::Numeric, Expr::Col(3));
        lemma_one_arg(db, r, group_aggs(), r[3]);
    }
    crate::bridge::collect::lemma_collect_all(gs, prep);
    lemma_group_by_op_values(db, ctx, irows, group_keys(), group_aggs());
    assert forall|i: int| 0 <= i < irows.len() implies #[trigger] group_input(db, ctx + irows[i], group_keys(), group_aggs())
        == Ok::<(Row, Row), SqlError>(prep[i]) by {
        lemma_group_input_results(db, ctx, irows, group_keys(), group_aggs(), i);
    }
    assert(irows.map_values(group_key(db, ctx, group_keys(), group_aggs())) =~= irows.map_values(inner_key()));
    assert(irows.map_values(group_args(db, ctx, group_keys(), group_aggs())) =~= irows.map_values(inner_qty()));
    lemma_eval_op(db, ctx, Query::Table(1));
    lemma_eval_op(db, ctx, grouped_avg());
    // The lookup.
    lemma_lookup_group(irows.map_values(inner_key()), irows.map_values(inner_qty()), k);
    assert forall|m: Seq<Row>| #[trigger] agg_row(corr_aggs(), m) == agg_row(group_aggs(), m) by {
        lemma_agg_row(corr_aggs(), m);
        lemma_agg_row(group_aggs(), m);
        assert(agg_value_results(corr_aggs(), m) =~= agg_value_results(group_aggs(), m));
    }
}

/// One aggregate whose argument evaluates to `v`: its argument row is `[v]`.
proof fn lemma_one_arg(db: Database, env: Row, aggs: Seq<Agg>, v: Val)
    requires aggs.len() == 1, agg_arg(db, env, aggs[0]) == Ok::<Val, SqlError>(v),
    ensures agg_args(db, env, aggs) == Ok::<Row, SqlError>(seq![v]),
{
    hide(agg_arg);
    lemma_agg_args(db, env, aggs);
    lemma_agg_arg_results_index(db, env, aggs);
    crate::bridge::collect::lemma_collect_all(agg_arg_results(db, env, aggs), seq![v]);
}

/// The key list `[Col(0)]` of a row.
proof fn lemma_key_col0(db: Database, r: Row)
    requires r.len() > 0,
    ensures eval_exprs(db, r, group_keys()) == Ok::<Row, SqlError>(seq![r[0]]),
{
    hide(eval_expr);
    lemma_expr_col(db, r, 0);
    crate::spec::eval::lemma_eval_exprs_step(db, r, group_keys());
    assert(group_keys().drop_last() =~= Seq::<Expr>::empty());
    crate::spec::eval::lemma_eval_exprs_empty(db, r);
    assert(Seq::<Val>::empty().push(r[0]) =~= seq![r[0]]);
}

} // verus!
