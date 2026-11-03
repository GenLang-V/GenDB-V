//! Example: a three-input join tree reordered by the planner, with its column bookkeeping in one column map (L5).
//!
//! `SELECT * FROM outer o1, inner i, outer o2 WHERE o1.key = i.key AND i.key = o2.key`. Canonical rows are
//! `o1 ++ i ++ o2` (widths 3, 4, 3). The planner joins the two outer inputs first and the inner one last, so its
//! rows are `o1 ++ o2 ++ i`; the column map `reorder_map()` (`[0, 1, 2, 6, 7, 8, 9, 3, 4, 5]`) views a physical row
//! as the canonical one, and the condition is evaluated on physical rows rewritten through it
//! (`physical_condition()`: `o1.key = i.key` is columns 0 and 6, `i.key = o2.key` columns 6 and 3).
//!
//! Proof route (each step a toolkit lemma): association (`link::join::lemma_product_assoc`), commutation of the
//! inner and outer inputs as bags (`colmap::lemma_product_swap`), the side-by-side view (`colmap::lemma_product_map`),
//! then `joins::lemma_filter_reordered`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::link::join::{keep, lemma_product_assoc};
use crate::link::expr::{lemma_expr_col, lemma_pred_and};
use crate::engine_link::ops::*;
use crate::engine_link::congruence::lemma_product_bag;
use crate::engine_link::colmap::*;
use crate::engine_link::remap::*;
use crate::engine_link::joins::*;
use crate::engine_link::decorrelate::lemma_eq_exact;
use crate::engine_pins::schema::*;

verus! {

pub open spec fn key_chain() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(3) }),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(7) }),
    )
}

pub open spec fn three_way_query() -> Query {
    Query::Filter {
        pred: key_chain(),
        input: Box::new(Query::Product {
            left: Box::new(Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(1)) }),
            right: Box::new(Query::Table(0)),
        }),
    }
}

/// The view of a physical row `o1 ++ o2 ++ i` as the canonical `o1 ++ i ++ o2`.
pub open spec fn reorder_map() -> ColMap {
    beside(id_map(3), 3, swap_map(4, 3))
}

/// The physical rows: the two outer inputs joined first, then the inner input.
pub open spec fn physical_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(db.tables[0], db.tables[0]), db.tables[1])
}

/// The condition on physical rows.
pub open spec fn physical_condition() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(6) }),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(6), b: Expr::Col(3) }),
    )
}

/// The canonical condition rewritten through the column map is `physical_condition()`.
pub proof fn lemma_physical_condition()
    ensures remap_pred(key_chain(), ctx_map(0, reorder_map()), 10) == physical_condition(),
{
    let m = ctx_map(0, reorder_map());
    let sw = swap_map(4, 3);
    assert(sw[0] == 3 && sw[4] == 0);
    assert(reorder_map()[0] == 0 && reorder_map()[3] == 6 && reorder_map()[7] == 3);
    assert(m.len() == 10 && m[0] == 0 && m[3] == 6 && m[7] == 3);
    assert(remap_expr(Expr::Col(0), m, 10) == Expr::Col(0));
    assert(remap_expr(Expr::Col(3), m, 10) == Expr::Col(6));
    assert(remap_expr(Expr::Col(7), m, 10) == Expr::Col(3));
    let (c1, c2) = (Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(3) }, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(7) });
    assert(remap_pred(c1, m, 10) == Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(6) });
    assert(remap_pred(c2, m, 10) == Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(6), b: Expr::Col(3) });
}

/// The canonical rows are, as a bag, the physical rows viewed through the column map.
pub proof fn lemma_reordered_rows(db: Database)
    requires example_db(db),
    ensures
        width_of(physical_rows(db), 10),
        map_into(reorder_map(), 10),
        product_rows(product_rows(db.tables[0], db.tables[1]), db.tables[0]).to_multiset()
            == map_rows(reorder_map(), physical_rows(db)).to_multiset(),
{
    lemma_example_rows(db);
    let (o, i) = (db.tables[0], db.tables[1]);
    let sw = swap_map(4, 3);
    assert(width_of(o, 3) && width_of(i, 4));
    // o ++ (i ++ o): the inner input and the second outer input commute as bags
    lemma_product_assoc(o, i, o);
    lemma_product_swap(i, o, 4, 3);
    lemma_product_bag(o, o, product_rows(i, o), map_rows(sw, product_rows(o, i)));
    // o ++ view(o ++ i) is the side-by-side view of o ++ (o ++ i)
    lemma_id_map(o, 3);
    lemma_product_width(o, i, 3, 4);
    lemma_product_map(o, product_rows(o, i), id_map(3), 3, sw, 7);
    lemma_beside_into(id_map(3), 3, sw, 7);
    // o ++ (o ++ i) is (o ++ o) ++ i
    lemma_product_assoc(o, o, i);
    lemma_product_width(o, o, 3, 3);
    lemma_product_width(product_rows(o, o), i, 6, 4);
}

/// The physical condition never errs on a physical row: every key it compares is an int8.
pub proof fn lemma_physical_total(db: Database, k: int)
    requires example_db(db), 0 <= k < physical_rows(db).len(),
    ensures eval_pred(db, physical_rows(db)[k], physical_condition()) is Ok,
{
    hide(eval_pred);
    hide(eval_expr);
    lemma_example_rows(db);
    let (o, i) = (db.tables[0], db.tables[1]);
    assert(width_of(o, 3) && width_of(i, 4));
    lemma_product_width(o, o, 3, 3);
    let (k1, l) = lemma_product_row(product_rows(o, o), i, 6, k);
    let (a1, a2) = lemma_product_row(o, o, 3, k1);
    let y = physical_rows(db)[k];
    assert(y[0] == o[a1][0] && y[3] == o[a2][0] && y[6] == i[l][0]);
    assert(y[0] is Int && y[3] is Int && y[6] is Int);
    lemma_expr_col(db, y, 0);
    lemma_expr_col(db, y, 3);
    lemma_expr_col(db, y, 6);
    lemma_eq_exact(db, y, Expr::Col(0), Expr::Col(6), y[0], y[6]);
    lemma_eq_exact(db, y, Expr::Col(6), Expr::Col(3), y[6], y[3]);
    lemma_pred_and(db, y, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(6) },
        Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(6), b: Expr::Col(3) }, y[0] == y[6], y[6] == y[3]);
}

/// The planner's rows answer the statement: as a bag, the canonical result is the physical rows kept by the
/// rewritten condition and viewed through the column map.
pub proof fn example_join_reorder(db: Database)
    requires example_db(db),
    ensures
        eval_query(db, Seq::empty(), three_way_query()) is Ok,
        eval_query(db, Seq::empty(), three_way_query())->Ok_0.to_multiset()
            == map_rows(reorder_map(), keep(physical_rows(db), side_keeps(db, Seq::empty(), physical_condition()))).to_multiset(),
{
    hide(eval_query);
    hide(eval_pred);
    hide(remap_pred);
    hide(physical_rows);
    let (o, i) = (db.tables[0], db.tables[1]);
    let ctx = Seq::<Val>::empty();
    let ys = physical_rows(db);
    let s = product_rows(product_rows(o, i), o);
    lemma_reordered_rows(db);
    lemma_physical_condition();
    assert(ctx_map(ctx.len(), reorder_map()) == ctx_map(0, reorder_map()));
    assert forall|k: int| 0 <= k < ys.len() implies
        #[trigger] eval_pred(db, ctx + ys[k], remap_pred(key_chain(), ctx_map(ctx.len(), reorder_map()), ctx.len() + 10)) is Ok by {
        lemma_physical_total(db, k);
        assert(ctx + ys[k] =~= ys[k]);
    }
    lemma_filter_reordered(db, ctx, s, ys, reorder_map(), 10, key_chain());
    let inner_product = Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(1)) };
    lemma_eval_op(db, ctx, three_way_query());
    lemma_eval_op(db, ctx, Query::Product { left: Box::new(inner_product), right: Box::new(Query::Table(0)) });
    lemma_eval_op(db, ctx, inner_product);
    lemma_eval_op(db, ctx, Query::Table(0));
    lemma_eval_op(db, ctx, Query::Table(1));
    lemma_example_rows(db);
}

} // verus!
