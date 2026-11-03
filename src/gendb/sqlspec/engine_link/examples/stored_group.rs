//! Example: GROUP BY over a storage's reordered copy of a table.
//!
//! A storage keeps table 1's rows in another order, with a row map `p` (`stored[i] == table[p[i]]`). The engine
//! groups the stored rows directly: `SELECT key, SUM(qty), COUNT(*) FROM inner GROUP BY key`. Proof route: the
//! row map is a permutation witness (`lemma_perm_bag`); the GROUP BY congruence (L4, `lemma_group_by_bag`) needs
//! group inputs without errors, exact keys (int8) and group values whose only error is 22003 (L3,
//! `aggs_value_info` by `compute`, `lemma_aggs_value_sound`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::exec::relational::domain::*;
use crate::bridge::equality::lemma_val_not_distinct_structural;
use crate::bridge::relation::lemma_group_members_sub;
use crate::link::expr::lemma_expr_col;
use crate::link::query::{lemma_agg_arg_sum, lemma_agg_arg_count};
use crate::engine_link::bag::*;
use crate::engine_link::ops::*;
use crate::engine_link::classes::*;
use crate::engine_link::classes_sound::lemma_aggs_value_sound;
use crate::engine_link::order_free::*;
use crate::engine_link::congruence::*;
use crate::engine_pins::schema::*;

verus! {

pub open spec fn sum_count() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(3) }, Agg::CountStar]
}

pub open spec fn by_key() -> Seq<Expr> {
    seq![Expr::Col(0)]
}

pub open spec fn grouped() -> Query {
    Query::GroupBy { keys: by_key(), aggs: sum_count(), input: Box::new(Query::Table(1)) }
}

/// Classes of the aggregate arguments of an inner row: its qty, and COUNT(*)'s NULL stand-in.
pub open spec fn arg_classes() -> Seq<VClass> {
    seq![
        VClass { kind: VKind::Num { scale: 2, digits: Some(15) }, nullable: false },
        VClass { kind: VKind::NoValue, nullable: true },
    ]
}

/// The group input of an inner row: its key, and its qty with the NULL stand-in.
proof fn lemma_input(db: Database, r: Row)
    requires r.len() == 4, r[0] is Int,
    ensures group_input(db, Seq::<Val>::empty() + r, by_key(), sum_count())
        == Ok::<(Row, Row), SqlError>((seq![r[0]], seq![r[3], Val::Null])),
{
    hide(eval_expr);
    hide(eval_exprs);
    hide(agg_args);
    hide(agg_arg);
    let env = Seq::<Val>::empty() + r;
    assert(env =~= r);
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 3);
    crate::spec::eval::lemma_eval_exprs_step(db, env, by_key());
    assert(by_key().drop_last() =~= Seq::<Expr>::empty());
    crate::spec::eval::lemma_eval_exprs_empty(db, env);
    assert(Seq::<Val>::empty().push(r[0]) =~= seq![r[0]]);
    lemma_agg_arg_sum(db, env, NumKind::Numeric, Expr::Col(3));
    lemma_agg_arg_count(db, env);
    lemma_agg_args(db, env, sum_count());
    lemma_agg_arg_results_index(db, env, sum_count());
    crate::bridge::collect::lemma_collect_all(agg_arg_results(db, env, sum_count()), seq![r[3], Val::Null]);
}

/// Grouping the stored rows is bag-equal to the SQL result.
pub proof fn example_group_by_stored_perm(db: Database, stored: Seq<Row>, p: Seq<int>)
    requires example_db(db), perm_of(p, db.tables[1], stored),
    ensures bag_eq(group_by_op(db, Seq::empty(), stored, by_key(), sum_count()), eval_query(db, Seq::empty(), grouped())),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    lemma_example_rows(db);
    let rows = db.tables[1];
    let ctx = Seq::<Val>::empty();
    lemma_perm_bag(p, rows, stored);
    // Every group input succeeds: uniform for any code.
    let gs = group_input_results(db, ctx, rows, by_key(), sum_count());
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] group_input(db, ctx + rows[i], by_key(), sum_count())
        == Ok::<(Row, Row), SqlError>((seq![rows[i][0]], seq![rows[i][3], Val::Null])) by {
        lemma_input(db, rows[i]);
    }
    assert forall|i: int| 0 <= i < gs.len() implies #[trigger] gs[i] is Ok
        || gs[i] == Err::<(Row, Row), SqlError>(SqlError::NumericValueOutOfRange) by {
        lemma_group_input_results(db, ctx, rows, by_key(), sum_count(), i);
    }
    // H2 and the group values: exact int8 keys, SUM and COUNT order-free, group errors only 22003 (L3).
    let kf = group_key(db, ctx, by_key(), sum_count());
    let af = group_args(db, ctx, by_key(), sum_count());
    let ks = rows.map_values(kf);
    let args = rows.map_values(af);
    assert forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && row_not_distinct(#[trigger] ks[i], #[trigger] ks[j])
        implies ks[i] == ks[j] by {
        assert(ks[i] == seq![rows[i][0]] && ks[j] == seq![rows[j][0]]);
        assert(ks[i][0] == rows[i][0] && ks[j][0] == rows[j][0]);
        lemma_val_not_distinct_structural(rows[i][0], rows[j][0]);
        assert(ks[i] =~= ks[j]);
    }
    assert(aggs_value_info(sum_count(), arg_classes()) is Some
        && aggs_value_info(sum_count(), arg_classes())->Some_0.errs == Errs::Only(SqlError::NumericValueOutOfRange)) by (compute_only);
    assert forall|i: int| 0 <= i < rows.len() implies {
        let m = group_members(ks, args, #[trigger] ks[i]);
        aggs_order_free(sum_count(), m)
            && (agg_row(sum_count(), m) is Ok || agg_row(sum_count(), m) == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange))
    } by {
        let m = group_members(ks, args, ks[i]);
        assert forall|j: int| 0 <= j < sum_count().len() implies #[trigger] agg_order_free(sum_count()[j], column(m, j)) by {}
        lemma_group_members_sub(ks, args, ks[i]);
        assert forall|x: int| 0 <= x < m.len() implies row_in(#[trigger] m[x], arg_classes()) by {
            let y = choose|y: int| 0 <= y < args.len() && args[y] == m[x];
            assert(args[y] == seq![rows[y][3], Val::Null]);
            assert(row_in(rows[y], inner_classes()));
            assert(in_class(rows[y][3], inner_classes()[3]));
        }
        lemma_aggs_value_sound(sum_count(), arg_classes(), m);
    }
    lemma_group_by_bag(db, ctx, rows, stored, by_key(), sum_count(), SqlError::NumericValueOutOfRange,
        SqlError::NumericValueOutOfRange);
    lemma_eval_op(db, ctx, grouped());
    lemma_eval_op(db, ctx, Query::Table(1));
}

} // verus!
