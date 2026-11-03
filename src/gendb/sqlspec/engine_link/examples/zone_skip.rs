//! Example: hoisted closed bounds and zone skipping (TPC-H Q4/Q6/Q12 style ranges).
//!
//! `SELECT * FROM outer WHERE day >= DATE '1994-01-01' AND day < DATE '1994-01-01' + INTERVAL '1' YEAR`. The
//! planner rule: evaluate the closed bounds once (`link::expr::lemma_expr_closed`), then scan the table zone by
//! zone (blocks of rows with stored day bounds) and skip every zone the range cannot meet. Proof route: the
//! condition is two-valued on every row once the bounds are values (`lemma_cmp_hoisted`), then
//! `lemma_filter_keeps`, `lemma_keep_flat_by`, `lemma_flat_by_ext`. When a hoisted bound raises instead
//! (`example_hoisted_error`), the filter raises it exactly when the table has a row (`lemma_filter_all_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::datetime::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::link::expr::{closed_expr, closed_db, lemma_expr_closed, lemma_expr_col, lemma_compare_date, lemma_pred_and};
use crate::link::join::{keep, lemma_keep_none};
use crate::engine_link::bag::*;
use crate::engine_link::ops::*;
use crate::engine_link::decorrelate::lemma_cmp_hoisted;
use crate::engine_pins::schema::*;

verus! {

pub open spec fn lo_bound() -> Expr {
    Expr::Lit(Literal::Date { y: 1994, m: 1, d: 1 })
}

pub open spec fn hi_bound() -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(lo_bound()) }),
        months: 12,
        days: 0,
        micros: 0,
    }
}

pub open spec fn range_pred() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(1), b: lo_bound() }),
        Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(1), b: hi_bound() }),
    )
}

pub open spec fn range_query() -> Query {
    Query::Filter { pred: range_pred(), input: Box::new(Query::Table(0)) }
}

/// 1994-01-01 as a day count since 2000-01-01.
pub open spec fn lo_day() -> int { -2191 }

/// 1995-01-01 00:00 as microseconds since 2000-01-01 00:00.
pub open spec fn hi_ts() -> int { -157766400000000 }

/// The hoisted bounds, evaluated once.
pub proof fn lemma_bounds()
    ensures
        closed_expr(lo_bound()), closed_expr(hi_bound()),
        eval_expr(closed_db(), Seq::empty(), lo_bound()) == Ok::<Val, SqlError>(Val::Date(lo_day())),
        eval_expr(closed_db(), Seq::empty(), hi_bound()) == Ok::<Val, SqlError>(Val::Ts(hi_ts())),
{
    hide(eval_expr);
    assert(closed_expr(lo_bound()) && closed_expr(hi_bound())) by (compute_only);
    assert(eval_expr(closed_db(), Seq::empty(), lo_bound()) == Ok::<Val, SqlError>(Val::Date(lo_day()))) by (compute_only);
    assert(eval_expr(closed_db(), Seq::empty(), hi_bound()) == Ok::<Val, SqlError>(Val::Ts(hi_ts()))) by (compute_only);
}

/// The rows the range keeps.
pub open spec fn in_range() -> spec_fn(Row) -> bool {
    |r: Row| lo_day() <= day_of(r[1]) && day_of(r[1]) * usecs_per_day() < hi_ts()
}

/// A zone of rows with stored bounds on their day.
pub struct Zone {
    pub lo: int,
    pub hi: int,
}

/// Every row of the block is an outer row whose day lies in the zone's bounds.
pub open spec fn zone_holds(block: Seq<Row>, z: Zone) -> bool {
    forall|i: int| 0 <= i < block.len() ==> (#[trigger] block[i])[1] is Date && z.lo <= day_of(block[i][1]) <= z.hi
}

/// A zone the range cannot meet.
pub open spec fn zone_skipped(z: Zone) -> bool {
    z.hi < lo_day() || z.lo * usecs_per_day() >= hi_ts()
}

pub open spec fn zone_block() -> spec_fn((Seq<Row>, Zone)) -> Seq<Row> {
    |p: (Seq<Row>, Zone)| p.0
}

/// The zone scan: skipped zones contribute nothing, the others their rows in range.
pub open spec fn zone_scan() -> spec_fn((Seq<Row>, Zone)) -> Seq<Row> {
    |p: (Seq<Row>, Zone)| if zone_skipped(p.1) { Seq::<Row>::empty() } else { keep(p.0, in_range()) }
}

/// The range condition on one outer row.
proof fn lemma_range_truth(db: Database, r: Row)
    requires r.len() == 3, r[1] is Date,
    ensures eval_pred(db, Seq::<Val>::empty() + r, range_pred()) == Ok::<Truth, SqlError>(truth_of(in_range()(r))),
{
    hide(eval_pred);
    hide(eval_expr);
    let env = Seq::<Val>::empty() + r;
    assert(env =~= r);
    let d = day_of(r[1]);
    lemma_bounds();
    lemma_expr_col(db, env, 1);
    lemma_expr_closed(db, env, lo_bound());
    lemma_expr_closed(db, env, hi_bound());
    lemma_cmp_hoisted(db, env, CmpOp::Ge, Expr::Col(1), lo_bound(), Ok::<Val, SqlError>(Val::Date(lo_day())));
    lemma_cmp_hoisted(db, env, CmpOp::Lt, Expr::Col(1), hi_bound(), Ok::<Val, SqlError>(Val::Ts(hi_ts())));
    lemma_compare_date(d, lo_day());
    assert(date_as_usecs(d) == d * usecs_per_day());
    let ge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(1), b: lo_bound() };
    let lt = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(1), b: hi_bound() };
    assert(eval_pred(db, env, ge) == Ok::<Truth, SqlError>(truth_of(lo_day() <= d)));
    assert(eval_pred(db, env, lt) == Ok::<Truth, SqlError>(truth_of(d * usecs_per_day() < hi_ts())));
    lemma_pred_and(db, env, ge, lt, lo_day() <= d, d * usecs_per_day() < hi_ts());
}

/// The range filter is the zone scan, for any division of the table into zones whose bounds hold.
pub proof fn example_zone_skip(db: Database, zs: Seq<(Seq<Row>, Zone)>)
    requires
        example_db(db),
        db.tables[0] == flat_by(zs, zone_block()),
        forall|b: int| 0 <= b < zs.len() ==> zone_holds((#[trigger] zs[b]).0, zs[b].1),
    ensures eval_query(db, Seq::empty(), range_query()) == Ok::<Relation, SqlError>(flat_by(zs, zone_scan())),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    lemma_example_rows(db);
    let rows = db.tables[0];
    let ctx = Seq::<Val>::empty();
    assert forall|i: int| 0 <= i < rows.len() implies {
        &&& #[trigger] eval_pred(db, ctx + rows[i], range_pred()) is Ok
        &&& (eval_pred(db, ctx + rows[i], range_pred())->Ok_0 is True) == in_range()(rows[i])
    } by {
        lemma_range_truth(db, rows[i]);
    }
    lemma_eval_op(db, ctx, range_query());
    lemma_eval_op(db, ctx, Query::Table(0));
    lemma_filter_keeps(db, ctx, rows, range_pred(), in_range());
    lemma_keep_flat_by(zs, zone_block(), in_range());
    assert forall|b: int| 0 <= b < zs.len() implies #[trigger] kept_block(zone_block(), in_range())(zs[b]) == zone_scan()(zs[b]) by {
        let (block, z) = (zs[b].0, zs[b].1);
        assert(zone_holds(block, z));
        if zone_skipped(z) {
            assert forall|i: int| 0 <= i < block.len() implies !in_range()(#[trigger] block[i]) by {
                let d = day_of(block[i][1]);
                assert(z.lo <= d <= z.hi);
                if z.lo * usecs_per_day() >= hi_ts() {
                    assert(d * usecs_per_day() >= z.lo * usecs_per_day()) by (nonlinear_arith)
                        requires d >= z.lo, usecs_per_day() > 0;
                }
            }
            lemma_keep_none(block, in_range());
        }
    }
    lemma_flat_by_ext(zs, kept_block(zone_block(), in_range()), zone_scan());
}

/// `DATE '5000000-01-01'` as a timestamp: a valid date beyond the timestamp range.
pub open spec fn far_bound() -> Expr {
    Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(Literal::Date { y: 5000000, m: 1, d: 1 })) }
}

pub open spec fn far_query() -> Query {
    Query::Filter { pred: Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(1), b: far_bound() }, input: Box::new(Query::Table(0)) }
}

/// A hoisted bound that raises (22008) is raised only if a row reaches it: an empty table gives no row and no
/// error.
pub proof fn example_hoisted_error(db: Database)
    requires example_db(db),
    ensures
        eval_query(db, Seq::empty(), far_query()) == if db.tables[0].len() == 0 {
            Ok::<Relation, SqlError>(Seq::empty())
        } else {
            Err::<Relation, SqlError>(SqlError::DatetimeFieldOverflow)
        },
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    lemma_example_rows(db);
    assert(eval_expr(closed_db(), Seq::empty(), far_bound()) == Err::<Val, SqlError>(SqlError::DatetimeFieldOverflow)) by (compute_only);
    assert(closed_expr(far_bound())) by (compute_only);
    let rows = db.tables[0];
    let ctx = Seq::<Val>::empty();
    let pred = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(1), b: far_bound() };
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] eval_pred(db, ctx + rows[i], pred)
        == Err::<Truth, SqlError>(SqlError::DatetimeFieldOverflow) by {
        let env = ctx + rows[i];
        assert(env =~= rows[i]);
        lemma_expr_col(db, env, 1);
        lemma_expr_closed(db, env, far_bound());
        lemma_cmp_hoisted(db, env, CmpOp::Lt, Expr::Col(1), far_bound(), Err::<Val, SqlError>(SqlError::DatetimeFieldOverflow));
    }
    lemma_eval_op(db, ctx, far_query());
    lemma_eval_op(db, ctx, Query::Table(0));
    lemma_filter_all_err(db, ctx, rows, pred, SqlError::DatetimeFieldOverflow);
}

} // verus!
