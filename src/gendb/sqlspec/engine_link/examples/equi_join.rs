//! Example: an equality condition over a product is a hash join (the inner join of two tables on a key).
//!
//! `SELECT * FROM outer, inner WHERE outer.key = inner.key`. The planner rule: probe a hash table of the inner rows
//! by key with every outer row; the rows come out outer row by outer row, each with its matching inner rows in
//! inner order. Proof route: the condition is two-valued on every joined row (int8 keys, `lemma_eq_exact`), then
//! `lemma_filter_keeps` and `lemma_keep_product`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::link::join::{keep, lemma_keep_ext};
use crate::link::expr::lemma_expr_col;
use crate::engine_link::bag::flat_by;
use crate::engine_link::ops::*;
use crate::engine_link::congruence::{join_block, lemma_keep_product};
use crate::engine_link::decorrelate::lemma_eq_exact;
use crate::engine_pins::schema::*;

verus! {

pub open spec fn join_query() -> Query {
    Query::Filter {
        pred: Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(3) },
        input: Box::new(Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(1)) }),
    }
}

/// The joined row's outer key equals its inner key.
pub open spec fn keys_equal() -> spec_fn(Row) -> bool {
    |x: Row| x[0] == x[3]
}

/// The inner rows with the key of outer row `o` (one hash bucket), joined to `o`.
pub open spec fn bucket(inner: Seq<Row>, o: Row) -> Seq<Row> {
    keep(inner, |y: Row| y[0] == o[0]).map_values(|y: Row| o + y)
}

/// The equi-join is, outer row by outer row, that row's bucket.
pub proof fn example_equi_join(db: Database)
    requires example_db(db),
    ensures
        eval_query(db, Seq::empty(), join_query()) == Ok::<Relation, SqlError>(flat_by(db.tables[0], join_block(db.tables[1], keys_equal()))),
        forall|i: int| 0 <= i < db.tables[0].len() ==> #[trigger] join_block(db.tables[1], keys_equal())(db.tables[0][i])
            == bucket(db.tables[1], db.tables[0][i]),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    lemma_example_rows(db);
    let (orows, irows) = (db.tables[0], db.tables[1]);
    let ctx = Seq::<Val>::empty();
    let p = product_rows(orows, irows);
    let pred = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(3) };
    lemma_product_rows_elems(orows, irows);
    assert forall|k: int| 0 <= k < p.len() implies {
        &&& #[trigger] eval_pred(db, ctx + p[k], pred) is Ok
        &&& (eval_pred(db, ctx + p[k], pred)->Ok_0 is True) == keys_equal()(p[k])
    } by {
        assert(is_concat(p[k], orows, irows));
        let (i, j) = choose|i: int, j: int| 0 <= i < orows.len() && 0 <= j < irows.len() && p[k] == #[trigger] orows[i] + #[trigger] irows[j];
        let x = p[k];
        assert(ctx + x =~= x);
        assert(x[0] == orows[i][0] && x[3] == irows[j][0]);
        lemma_expr_col(db, x, 0);
        lemma_expr_col(db, x, 3);
        lemma_eq_exact(db, x, Expr::Col(0), Expr::Col(3), x[0], x[3]);
    }
    lemma_eval_op(db, ctx, join_query());
    lemma_eval_op(db, ctx, Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(1)) });
    lemma_eval_op(db, ctx, Query::Table(0));
    lemma_eval_op(db, ctx, Query::Table(1));
    lemma_filter_keeps(db, ctx, p, pred, keys_equal());
    lemma_keep_product(orows, irows, keys_equal());
    assert forall|i: int| 0 <= i < orows.len() implies #[trigger] join_block(irows, keys_equal())(orows[i]) == bucket(irows, orows[i]) by {
        let o = orows[i];
        assert forall|j: int| 0 <= j < irows.len() implies #[trigger] keys_equal()(o + irows[j]) == (irows[j][0] == o[0]) by {
            assert((o + irows[j])[0] == o[0] && (o + irows[j])[3] == irows[j][0]);
        }
        lemma_keep_ext(irows, |y: Row| keys_equal()(o + y), |y: Row| y[0] == o[0]);
    }
}

} // verus!
