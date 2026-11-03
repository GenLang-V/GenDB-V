//! Example: EXISTS correlated on a key is a hash semi-join (TPC-H Q4 style).
//!
//! `SELECT * FROM outer WHERE EXISTS (SELECT * FROM inner WHERE inner.key = outer.key AND inner.a < inner.b)`.
//! The planner rule: build the set of keys of the inner rows with `a < b` once, then keep the outer rows whose key
//! is in it. Proof route: L3 (the correlated condition is total on every (outer, inner) pair, decided by
//! `by (compute)`), L6 (`lemma_semi_join`; the inner table is the same for every outer row), and the meaning of
//! the condition on the pair (`lemma_eq_exact` for the key).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::bridge::equality::same_exact_type;
use crate::link::join::{keep, lemma_keep_ext};
use crate::link::expr::{lemma_expr_col, lemma_compare_date, lemma_pred_cmp, lemma_pred_and, int_cmp};
use crate::engine_link::ops::*;
use crate::engine_link::classes::*;
use crate::engine_link::classes_values::lemma_row_in_concat;
use crate::engine_link::classes_sound::lemma_pred_total;
use crate::engine_link::decorrelate::*;
use crate::engine_pins::schema::*;

verus! {

/// `inner.key = outer.key AND inner.a < inner.b` in the environment `outer row ++ inner row` (outer: 3 columns).
pub open spec fn corr_pred() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(0) }),
        Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: Expr::Col(5) }),
    )
}

pub open spec fn exists_query() -> Query {
    Query::Filter { pred: exists_pred(corr_pred(), Query::Table(1)), input: Box::new(Query::Table(0)) }
}

/// The hash semi-join: some inner row has the outer row's key and `a < b`.
pub open spec fn key_with_ordered_pair(inner: Seq<Row>) -> spec_fn(Row) -> bool {
    |o: Row| exists|j: int| 0 <= j < inner.len() && #[trigger] inner[j][0] == o[0] && day_of(inner[j][1]) < day_of(inner[j][2])
}

/// The correlated condition on one (outer, inner) pair.
proof fn lemma_corr_truth(db: Database, o: Row, i: Row)
    requires
        o.len() == 3 && o[0] is Int,
        i.len() == 4 && i[0] is Int && i[1] is Date && i[2] is Date,
    ensures
        eval_pred(db, Seq::<Val>::empty() + o + i, corr_pred())
            == Ok::<Truth, SqlError>(truth_of(i[0] == o[0] && day_of(i[1]) < day_of(i[2]))),
{
    hide(eval_pred);
    hide(eval_expr);
    let env = Seq::<Val>::empty() + o + i;
    assert(env.len() == 7);
    assert(env[0] == o[0] && env[3] == i[0] && env[4] == i[1] && env[5] == i[2]);
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 3);
    lemma_expr_col(db, env, 4);
    lemma_expr_col(db, env, 5);
    lemma_eq_exact(db, env, Expr::Col(3), Expr::Col(0), i[0], o[0]);
    let (x, y) = (day_of(i[1]), day_of(i[2]));
    lemma_compare_date(x, y);
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(4), Expr::Col(5), i[1], i[2], x, y);
    assert(int_cmp(CmpOp::Lt, x, y) == (x < y));
    lemma_pred_and(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(0) },
        Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: Expr::Col(5) }, i[0] == o[0], x < y);
}

/// The EXISTS query keeps exactly the outer rows whose key has an inner row with `a < b`.
pub proof fn example_exists_semi_join(db: Database)
    requires example_db(db),
    ensures
        eval_query(db, Seq::empty(), exists_query())
            == Ok::<Relation, SqlError>(keep(db.tables[0], key_with_ordered_pair(db.tables[1]))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    lemma_example_rows(db);
    let (orows, irows) = (db.tables[0], db.tables[1]);
    let ctx = Seq::<Val>::empty();
    // L3: the correlated condition is total on every pair of rows of the two tables' classes.
    assert(pred_total(example_schema(), outer_classes() + inner_classes(), corr_pred())) by (compute_only);
    assert forall|i: int, j: int| 0 <= i < orows.len() && 0 <= j < irows.len()
        implies #[trigger] eval_pred(db, ctx + orows[i] + irows[j], corr_pred()) is Ok by {
        assert(ctx + orows[i] =~= orows[i]);
        assert(row_in(orows[i], outer_classes()) && row_in(irows[j], inner_classes()));
        lemma_row_in_concat(orows[i], outer_classes(), irows[j], inner_classes());
        lemma_pred_total(db, orows[i] + irows[j], outer_classes() + inner_classes(), corr_pred());
    }
    // L2 (here direct): the inner table is the same for every outer row.
    assert forall|i: int| 0 <= i < orows.len() implies eval_query(db, ctx + #[trigger] orows[i], Query::Table(1))
        == Ok::<Relation, SqlError>(irows) by {
        lemma_eval_op(db, ctx + orows[i], Query::Table(1));
    }
    lemma_eval_op(db, ctx, exists_query());
    lemma_eval_op(db, ctx, Query::Table(0));
    lemma_semi_join(db, ctx, orows, Query::Table(1), irows, corr_pred());
    // The semi-join's match is the key-and-order test.
    assert forall|i: int| 0 <= i < orows.len() implies #[trigger] semi_keeps(db, ctx, irows, corr_pred())(orows[i])
        == key_with_ordered_pair(irows)(orows[i]) by {
        let o = orows[i];
        if semi_keeps(db, ctx, irows, corr_pred())(o) {
            let j = choose|j: int| 0 <= j < irows.len()
                && #[trigger] eval_pred(db, ctx + o + irows[j], corr_pred()) == Ok::<Truth, SqlError>(Truth::True);
            lemma_corr_truth(db, o, irows[j]);
        }
        if key_with_ordered_pair(irows)(o) {
            let j = choose|j: int| 0 <= j < irows.len() && #[trigger] irows[j][0] == o[0]
                && day_of(irows[j][1]) < day_of(irows[j][2]);
            lemma_corr_truth(db, o, irows[j]);
        }
    }
    lemma_keep_ext(orows, semi_keeps(db, ctx, irows, corr_pred()), key_with_ordered_pair(irows));
}

} // verus!
