//! Example: a condition on one input is pushed below a hash join (L5 pushdown, equi-join).
//!
//! `SELECT * FROM outer, inner WHERE outer.key = inner.key AND inner.a <= inner.b`. The planner rule: filter the inner
//! rows on their own by `a <= b` (the conjunct rewritten for inner rows: columns 4, 5 of the joined row are columns
//! 1, 2 of an inner row), then hash-join the outer rows with the kept inner rows. Proof route: the key equality and
//! the date comparison never err (int8 keys, NOT NULL dates), then `joins::lemma_equi_join_right_filter`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::link::join::keep;
use crate::link::expr::{lemma_expr_col, lemma_compare_date, lemma_pred_cmp};
use crate::engine_link::ops::*;
use crate::engine_link::locality::*;
use crate::engine_link::colmap::width_of;
use crate::engine_link::remap::*;
use crate::engine_link::joins::*;
use crate::engine_pins::schema::*;

verus! {

/// `inner.a <= inner.b` in the joined row (outer has 3 columns).
pub open spec fn dates_in_order() -> Pred {
    Pred::Cmp { op: CmpOp::Le, a: Expr::Col(4), b: Expr::Col(5) }
}

pub open spec fn pushdown_query() -> Query {
    Query::Filter {
        pred: Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(3) }),
            Box::new(dates_in_order()),
        ),
        input: Box::new(Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(1)) }),
    }
}

/// The pushed-down condition on an inner row alone.
pub open spec fn inner_dates_in_order() -> Pred {
    Pred::Cmp { op: CmpOp::Le, a: Expr::Col(1), b: Expr::Col(2) }
}

/// The conjunct rewritten for inner rows is `a <= b` on columns 1 and 2.
pub proof fn lemma_pushed_condition()
    ensures right_pred(dates_in_order(), 0, 3, 4) == inner_dates_in_order(),
{
    let m = right_map(0, 3, 4);
    assert(m[4] == 1 && m[5] == 2);
    assert(remap_expr(Expr::Col(4), m, 4) == Expr::Col(1));
    assert(remap_expr(Expr::Col(5), m, 4) == Expr::Col(2));
}

/// The join with the inner rows filtered first: the hash join of the outer rows with the inner rows whose `a` is
/// not after their `b`.
pub proof fn example_pushdown(db: Database)
    requires example_db(db),
    ensures
        eval_query(db, Seq::empty(), pushdown_query())
            == Ok::<Relation, SqlError>(equi_join(db.tables[0], keep(db.tables[1], side_keeps(db, Seq::empty(), inner_dates_in_order())), 0, 0)),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    lemma_example_rows(db);
    let (orows, irows) = (db.tables[0], db.tables[1]);
    let ctx = Seq::<Val>::empty();
    let q = dates_in_order();
    lemma_pushed_condition();
    // the key equality never errs: int8 against int8
    assert(width_of(orows, 3) && width_of(irows, 4));
    assert(keys_comparable(orows, irows, 0, 0)) by {
        assert forall|k: int, l: int| 0 <= k < orows.len() && 0 <= l < irows.len() implies
            #[trigger] orows[k][0] is Null || #[trigger] irows[l][0] is Null || compare(orows[k][0], irows[l][0]) is Some by {
            assert(orows[k][0] is Int && irows[l][0] is Int);
        }
    }
    // the date condition reads inner columns only and never errs on an inner row
    assert(right_conjunct(db, ctx, irows, q, 3, 4)) by {
        let m = right_map(0, 3, 4);
        let r = remap_reads(m, 4);
        assert(m[4] == 1 && m[5] == 2);
        assert(col_read_ok(4, r) && col_read_ok(5, r));
        assert(expr_reads(Expr::Col(4), r) && expr_reads(Expr::Col(5), r));
        assert(pred_reads(q, r));
        assert forall|l: int| 0 <= l < irows.len() implies #[trigger] eval_pred(db, ctx + irows[l], right_pred(q, 0, 3, 4)) is Ok by {
            let y = irows[l];
            assert(ctx + y =~= y);
            lemma_expr_col(db, y, 1);
            lemma_expr_col(db, y, 2);
            if let (Val::Date(d1), Val::Date(d2)) = (y[1], y[2]) {
                lemma_compare_date(d1, d2);
                lemma_pred_cmp(db, y, CmpOp::Le, Expr::Col(1), Expr::Col(2), y[1], y[2], d1, d2);
            }
        }
    }
    let pred = Pred::And(Box::new(equi_pred(0, 3, 0, 0)), Box::new(q));
    assert(pushdown_query() == Query::Filter {
        pred,
        input: Box::new(Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(1)) }),
    });
    lemma_equi_join_right_filter(db, ctx, orows, irows, 3, 4, 0, 0, q);
    lemma_eval_op(db, ctx, pushdown_query());
    lemma_eval_op(db, ctx, Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(1)) });
    lemma_eval_op(db, ctx, Query::Table(0));
    lemma_eval_op(db, ctx, Query::Table(1));
}

} // verus!
