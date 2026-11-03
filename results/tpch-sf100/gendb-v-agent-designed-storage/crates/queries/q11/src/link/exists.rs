//! EXISTS rules (optional author toolkit; nothing here names a query).
//!
//! `EXISTS (SELECT .. FROM input WHERE pred)` is `Pred::Exists(Filter { pred, input })`; a correlated condition reads
//! the outer environment `env` (outer columns first, then the input row: `env + rows[i]`). When every condition
//! evaluation succeeds, its value is whether some input row satisfies the condition (`lemma_exists_filter`;
//! `lemma_exists_filter_table` for a base table, `link::join` for a product of tables). When a condition fails,
//! the first failure in row order is the outcome (`link::capacity::lemma_filter_err` for a uniform code).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::bridge::collect::*;
use crate::exec::relational::domain::{filter_results, lemma_eval_filter};

verus! {

/// `keep_true` keeps some row exactly when some truth value is `True`.
pub proof fn lemma_keep_true_nonempty(rows: Seq<Row>, truths: Seq<Truth>)
    requires rows.len() == truths.len(),
    ensures (keep_true(rows, truths).len() > 0) == (exists|i: int| 0 <= i < truths.len() && #[trigger] truths[i] is True),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (r0, t0) = (rows.drop_last(), truths.drop_last());
        lemma_keep_true_nonempty(r0, t0);
        if exists|i: int| 0 <= i < truths.len() && #[trigger] truths[i] is True {
            let i = choose|i: int| 0 <= i < truths.len() && #[trigger] truths[i] is True;
            if i < truths.len() - 1 {
                assert(t0[i] == truths[i]);
            }
        }
        if exists|i: int| 0 <= i < t0.len() && #[trigger] t0[i] is True {
            let i = choose|i: int| 0 <= i < t0.len() && #[trigger] t0[i] is True;
            assert(truths[i] == t0[i]);
        }
    }
}

/// EXISTS over a filtered input whose rows' conditions all succeed: true exactly when some row's condition is
/// `True` (correlated or not).
pub proof fn lemma_exists_filter(db: Database, env: Row, pred: Pred, input: Box<Query>, rows: Relation)
    requires
        eval_query(db, env, *input) == Ok::<Relation, SqlError>(rows),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] eval_pred(db, env + rows[i], pred) is Ok,
    ensures
        eval_pred(db, env, Pred::Exists(Box::new(Query::Filter { pred, input })))
            == Ok::<Truth, SqlError>(truth_of(exists|i: int| 0 <= i < rows.len()
                && #[trigger] eval_pred(db, env + rows[i], pred) == Ok::<Truth, SqlError>(Truth::True))),
{
    lemma_eval_filter(db, env, pred, input);
    let rs = filter_results(db, env, rows, pred);
    let truths = Seq::new(rows.len(), |i: int| eval_pred(db, env + rows[i], pred)->Ok_0);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {}
    lemma_collect_all(rs, truths);
    lemma_keep_true_nonempty(rows, truths);
    let w = exists|i: int| 0 <= i < rows.len() && #[trigger] eval_pred(db, env + rows[i], pred) == Ok::<Truth, SqlError>(Truth::True);
    if w {
        let i = choose|i: int| 0 <= i < rows.len() && #[trigger] eval_pred(db, env + rows[i], pred) == Ok::<Truth, SqlError>(Truth::True);
        assert(truths[i] is True);
    }
    if exists|i: int| 0 <= i < truths.len() && #[trigger] truths[i] is True {
        let i = choose|i: int| 0 <= i < truths.len() && #[trigger] truths[i] is True;
        assert(eval_pred(db, env + rows[i], pred) == Ok::<Truth, SqlError>(Truth::True));
    }
}

/// EXISTS over a filtered base table `t`.
pub proof fn lemma_exists_filter_table(db: Database, env: Row, pred: Pred, t: nat)
    requires
        t < db.tables.len(),
        forall|i: int| 0 <= i < db.tables[t as int].len() ==> #[trigger] eval_pred(db, env + db.tables[t as int][i], pred) is Ok,
    ensures
        eval_pred(db, env, Pred::Exists(Box::new(Query::Filter { pred, input: Box::new(Query::Table(t)) })))
            == Ok::<Truth, SqlError>(truth_of(exists|i: int| 0 <= i < db.tables[t as int].len()
                && #[trigger] eval_pred(db, env + db.tables[t as int][i], pred) == Ok::<Truth, SqlError>(Truth::True))),
{
    lemma_exists_filter(db, env, pred, Box::new(Query::Table(t)), db.tables[t as int]);
}

} // verus!
