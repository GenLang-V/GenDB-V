//! L4, bag congruence (engine toolkit; nothing here names a query, a table or a column).
//!
//! Every relational operator maps inputs with equal multisets to outcomes that are bag-equal
//! (`engine_link::bag::bag_eq`: the same SQL error, or rows with equal multisets), under the hazard conditions of
//! the lemma groups:
//! - H1, errors: the per-row outcomes the operator collects in row order (conditions, projections, ON
//!   conditions, aggregate arguments, group inputs, group values) are `uniform` (`engine_link::ops`): values or
//!   one error code. Without that the first error depends on the row order.
//! - H2, representatives: GROUP BY keys and DISTINCT rows exact (`engine_link::order_free::rows_exact`), MIN, MAX
//!   and DISTINCT aggregates order-free (`agg_order_free`).
//! Products need nothing. Operator forms (on evaluated children, `engine_link::ops`): `lemma_filter_bag`,
//! `lemma_project_bag`, `lemma_product_bag`, `lemma_left_join_bag`, `lemma_distinct_bag`, `lemma_aggregate_bag`,
//! `lemma_group_by_bag`. Node forms (replace a child by a bag-equal one, under the condition on the original
//! child's rows): `lemma_*_child_bag`. L3 establishes the conditions statically (`lemma_rows_uniform_pred` and
//! its siblings at the end).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::spec::typing::db_wf;
use crate::exec::relational::domain::*;
use crate::bridge::collect::*;
use crate::link::join::keep;
use crate::engine_link::bag::*;
use crate::engine_link::ops::*;
use crate::engine_link::order_free::*;
use crate::engine_link::classes::*;
use crate::engine_link::classes_values::*;
use crate::engine_link::classes_sound::*;

verus! {

// ------------------------------------------------------------------------------------- per-row outcome sequences

/// A per-row outcome sequence whose element `i` is `f(rows[i])`.
pub open spec fn by_row<T>(rows: Seq<Row>, f: spec_fn(Row) -> Result<T, SqlError>) -> Seq<Result<T, SqlError>> {
    rows.map_values(f)
}

/// Uniformity of a per-row outcome function transfers to an equal multiset of rows; the first-error
/// collections then agree on success, and on the error.
pub proof fn lemma_by_row_bag<T>(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> Result<T, SqlError>, e: SqlError)
    requires a.to_multiset() == b.to_multiset(), uniform(by_row(a, f), e),
    ensures
        uniform(by_row(b, f), e),
        (collect(by_row(a, f)) is Ok) == (collect(by_row(b, f)) is Ok),
        collect(by_row(a, f)) is Err ==> collect(by_row(a, f)) == Err::<Seq<T>, SqlError>(e)
            && collect(by_row(b, f)) == Err::<Seq<T>, SqlError>(e),
{
    let (ra, rb) = (by_row(a, f), by_row(b, f));
    assert forall|i: int| 0 <= i < rb.len() implies #[trigger] rb[i] is Ok || rb[i] == Err::<T, SqlError>(e) by {
        let j = lemma_bag_contains(a, b, i);
        assert(ra[j] == rb[i]);
    }
    lemma_collect_uniform(ra, e);
    lemma_collect_uniform(rb, e);
    if collect(ra) is Ok && !(collect(rb) is Ok) {
        let i = choose|i: int| 0 <= i < rb.len() && !(#[trigger] rb[i] is Ok);
        let j = lemma_bag_contains(a, b, i);
        assert(ra[j] == rb[i]);
    }
    if collect(rb) is Ok && !(collect(ra) is Ok) {
        let i = choose|i: int| 0 <= i < ra.len() && !(#[trigger] ra[i] is Ok);
        let j = lemma_bag_contains(b, a, i);
        assert(rb[j] == ra[i]);
    }
}

/// An all-`Ok` collection is the values of the per-row function.
pub proof fn lemma_by_row_values<T>(a: Seq<Row>, f: spec_fn(Row) -> Result<T, SqlError>)
    requires collect(by_row(a, f)) is Ok,
    ensures collect(by_row(a, f))->Ok_0 == a.map_values(|r: Row| f(r)->Ok_0),
{
    let ra = by_row(a, f);
    lemma_collect_ok(ra);
    let vs = collect(ra)->Ok_0;
    assert forall|i: int| 0 <= i < vs.len() implies #[trigger] vs[i] == f(a[i])->Ok_0 by {
        assert(ra[i] == Ok::<T, SqlError>(vs[i]));
    }
    assert(vs =~= a.map_values(|r: Row| f(r)->Ok_0));
}

// ------------------------------------------------------------------------------------- WHERE, SELECT, DISTINCT

/// The condition outcome of one row (environment `ctx + r`).
pub open spec fn pred_at(db: Database, ctx: Row, pred: Pred) -> spec_fn(Row) -> Result<Truth, SqlError> {
    |r: Row| eval_pred(db, ctx + r, pred)
}

/// L4, WHERE: bag-equal inputs give bag-equal outcomes when the condition's errors are uniform.
pub proof fn lemma_filter_bag(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, pred: Pred, e: SqlError)
    requires a.to_multiset() == b.to_multiset(), uniform(filter_results(db, ctx, a, pred), e),
    ensures bag_eq(filter_op(db, ctx, a, pred), filter_op(db, ctx, b, pred)),
{
    let f = pred_at(db, ctx, pred);
    assert(filter_results(db, ctx, a, pred) =~= by_row(a, f));
    assert(filter_results(db, ctx, b, pred) =~= by_row(b, f));
    lemma_by_row_bag(a, b, f, e);
    if collect(by_row(a, f)) is Ok {
        let keepf = |r: Row| eval_pred(db, ctx + r, pred) == Ok::<Truth, SqlError>(Truth::True);
        lemma_collect_ok(by_row(a, f));
        lemma_collect_ok(by_row(b, f));
        let (ta, tb) = (collect(by_row(a, f))->Ok_0, collect(by_row(b, f))->Ok_0);
        assert forall|i: int| 0 <= i < a.len() implies (#[trigger] ta[i] is True) == keepf(a[i]) by {
            assert(by_row(a, f)[i] == Ok::<Truth, SqlError>(ta[i]));
        }
        assert forall|i: int| 0 <= i < b.len() implies (#[trigger] tb[i] is True) == keepf(b[i]) by {
            assert(by_row(b, f)[i] == Ok::<Truth, SqlError>(tb[i]));
        }
        lemma_keep_true_as_keep(a, ta, keepf);
        lemma_keep_true_as_keep(b, tb, keepf);
        lemma_keep_bag(a, b, keepf);
    }
}

/// The SELECT list outcome of one row.
pub open spec fn exprs_at(db: Database, ctx: Row, exprs: Seq<Expr>) -> spec_fn(Row) -> Result<Row, SqlError> {
    |r: Row| eval_exprs(db, ctx + r, exprs)
}

/// L4, SELECT: bag-equal inputs give bag-equal outcomes when the expressions' errors are uniform.
pub proof fn lemma_project_bag(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, exprs: Seq<Expr>, e: SqlError)
    requires a.to_multiset() == b.to_multiset(), uniform(project_results(db, ctx, a, exprs), e),
    ensures bag_eq(project_op(db, ctx, a, exprs), project_op(db, ctx, b, exprs)),
{
    let f = exprs_at(db, ctx, exprs);
    assert(project_results(db, ctx, a, exprs) =~= by_row(a, f));
    assert(project_results(db, ctx, b, exprs) =~= by_row(b, f));
    lemma_by_row_bag(a, b, f, e);
    if collect(by_row(a, f)) is Ok {
        lemma_by_row_values(a, f);
        lemma_by_row_values(b, f);
        lemma_map_bag(a, b, |r: Row| f(r)->Ok_0);
    }
}

/// L4, SELECT DISTINCT: bag-equal exact inputs give bag-equal outputs.
pub proof fn lemma_distinct_bag(a: Seq<Row>, b: Seq<Row>)
    requires a.to_multiset() == b.to_multiset(), rows_exact(a),
    ensures distinct_rows(a).to_multiset() == distinct_rows(b).to_multiset(),
{
    lemma_distinct_rows_bag(a, b);
}

// ------------------------------------------------------------------------------------- products and LEFT JOIN

/// The block of one left row of a product: that row joined with every right row.
pub open spec fn product_block(b: Seq<Row>) -> spec_fn(Row) -> Seq<Row> {
    |x: Row| b.map_values(|y: Row| x + y)
}

/// The left-major product is the concatenation of the left rows' blocks.
pub proof fn lemma_product_blocks(a: Seq<Row>, b: Seq<Row>)
    ensures product_rows(a, b) == flat_by(a, product_block(b)),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_product_blocks(a.drop_last(), b);
        assert(b.map_values(|r: Row| a.last() + r) =~= product_block(b)(a.last()));
    }
}

/// The matching right rows of left row `x` under a condition on joined rows, joined to `x` (one block of an
/// equi-join or any join evaluated left row by left row).
pub open spec fn join_block(b: Seq<Row>, f: spec_fn(Row) -> bool) -> spec_fn(Row) -> Seq<Row> {
    |x: Row| keep(b, |y: Row| f(x + y)).map_values(|y: Row| x + y)
}

/// A two-valued condition over a left-major product is, left row by left row, the right rows it keeps for that
/// left row: the order in which a hash or index join probes the left input emits its rows.
pub proof fn lemma_keep_product(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> bool)
    ensures keep(product_rows(a, b), f) == flat_by(a, join_block(b, f)),
{
    lemma_product_blocks(a, b);
    lemma_keep_flat_by(a, product_block(b), f);
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] kept_block(product_block(b), f)(a[i]) == join_block(b, f)(a[i]) by {
        let x = a[i];
        let m = |y: Row| x + y;
        crate::link::join::lemma_keep_map(b, m, f);
        assert(product_block(b)(x) =~= b.map_values(m));
        crate::link::join::lemma_keep_ext(b, |y: Row| f(m(y)), |y: Row| f(x + y));
        let kb = keep(b, |y: Row| f(x + y));
        assert(kb.map_values(m) =~= kb.map_values(|y: Row| x + y));
    }
    lemma_flat_by_ext(a, kept_block(product_block(b), f), join_block(b, f));
}

/// L4, product: bag-equal inputs give bag-equal products.
pub proof fn lemma_product_bag(a: Seq<Row>, a2: Seq<Row>, b: Seq<Row>, b2: Seq<Row>)
    requires a.to_multiset() == a2.to_multiset(), b.to_multiset() == b2.to_multiset(),
    ensures product_rows(a, b).to_multiset() == product_rows(a2, b2).to_multiset(),
{
    lemma_product_blocks(a, b);
    lemma_product_blocks(a2, b);
    lemma_product_blocks(a2, b2);
    lemma_flat_by_bag(a, a2, product_block(b));
    assert forall|i: int| 0 <= i < a2.len() implies
        (#[trigger] product_block(b)(a2[i])).to_multiset() == product_block(b2)(a2[i]).to_multiset() by {
        let x = a2[i];
        lemma_map_bag(b, b2, |y: Row| x + y);
        assert(product_block(b)(x) =~= b.map_values(|y: Row| x + y));
        assert(product_block(b2)(x) =~= b2.map_values(|y: Row| x + y));
    }
    lemma_flat_by_blocks(a2, product_block(b), product_block(b2));
}

/// The ON outcomes of left row `x` against the right rows `r` (first error in right-row order).
pub open spec fn on_truths(db: Database, ctx: Row, r: Seq<Row>, on: Pred) -> spec_fn(Row) -> Result<Seq<Truth>, SqlError> {
    |x: Row| collect(join_results(db, ctx + x, r, on))
}

/// The rows of one left row of a LEFT JOIN, all ON outcomes values.
pub open spec fn left_join_block(db: Database, ctx: Row, r: Seq<Row>, on: Pred, n: nat) -> spec_fn(Row) -> Seq<Row> {
    |x: Row| left_join_one(x, r, on_truths(db, ctx, r, on)(x)->Ok_0, n)
}

/// LEFT JOIN rows are the concatenation of the left rows' blocks, when the truths are the left rows' ON outcomes.
pub proof fn lemma_left_join_blocks(db: Database, ctx: Row, l: Seq<Row>, r: Seq<Row>, on: Pred, n: nat, truths: Seq<Seq<Truth>>)
    requires
        truths.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> on_truths(db, ctx, r, on)(l[i]) == Ok::<Seq<Truth>, SqlError>(#[trigger] truths[i]),
    ensures left_join_rows(l, r, truths, n) == flat_by(l, left_join_block(db, ctx, r, on, n)),
    decreases l.len(),
{
    if l.len() > 0 {
        let (li, ti) = (l.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < li.len() implies on_truths(db, ctx, r, on)(li[i]) == Ok::<Seq<Truth>, SqlError>(#[trigger] ti[i]) by {
            assert(li[i] == l[i] && ti[i] == truths[i]);
        }
        lemma_left_join_blocks(db, ctx, li, r, on, n, ti);
        assert(on_truths(db, ctx, r, on)(l[l.len() - 1]) == Ok::<Seq<Truth>, SqlError>(truths[truths.len() - 1]));
    }
}

/// The right rows kept for left row `x` (ON condition `True`).
pub open spec fn on_keeps(db: Database, ctx: Row, on: Pred, x: Row) -> spec_fn(Row) -> bool {
    |y: Row| eval_pred(db, ctx + x + y, on) == Ok::<Truth, SqlError>(Truth::True)
}

/// One left row's block over bag-equal right inputs (all ON outcomes values).
proof fn lemma_left_join_block_bag(db: Database, ctx: Row, x: Row, r: Seq<Row>, r2: Seq<Row>, on: Pred, n: nat)
    requires
        r.to_multiset() == r2.to_multiset(),
        on_truths(db, ctx, r, on)(x) is Ok,
        on_truths(db, ctx, r2, on)(x) is Ok,
    ensures left_join_block(db, ctx, r, on, n)(x).to_multiset() == left_join_block(db, ctx, r2, on, n)(x).to_multiset(),
{
    let f = on_keeps(db, ctx, on, x);
    let (t, t2) = (on_truths(db, ctx, r, on)(x)->Ok_0, on_truths(db, ctx, r2, on)(x)->Ok_0);
    let (j, j2) = (join_results(db, ctx + x, r, on), join_results(db, ctx + x, r2, on));
    lemma_collect_ok(j);
    lemma_collect_ok(j2);
    assert forall|k: int| 0 <= k < r.len() implies (#[trigger] t[k] is True) == f(r[k]) by {
        assert(j[k] == Ok::<Truth, SqlError>(t[k]));
    }
    assert forall|k: int| 0 <= k < r2.len() implies (#[trigger] t2[k] is True) == f(r2[k]) by {
        assert(j2[k] == Ok::<Truth, SqlError>(t2[k]));
    }
    lemma_keep_true_as_keep(r, t, f);
    lemma_keep_true_as_keep(r2, t2, f);
    lemma_keep_bag(r, r2, f);
    keep(r, f).to_multiset_ensures();
    keep(r2, f).to_multiset_ensures();
    lemma_map_bag(keep(r, f), keep(r2, f), |y: Row| x + y);
}

/// Every ON outcome over left rows `l` and right rows `r` is a value or the one error `e`.
pub open spec fn on_uniform(db: Database, ctx: Row, l: Seq<Row>, r: Seq<Row>, on: Pred, e: SqlError) -> bool {
    forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < r.len() ==>
        #[trigger] eval_pred(db, ctx + l[i] + r[j], on) is Ok || eval_pred(db, ctx + l[i] + r[j], on) == Err::<Truth, SqlError>(e)
}

/// The ON outcomes of left row `x` against `r`: uniform, and `Ok` exactly when every one is a value.
proof fn lemma_on_truths(db: Database, ctx: Row, x: Row, r: Seq<Row>, on: Pred, e: SqlError)
    requires forall|j: int| 0 <= j < r.len() ==> #[trigger] eval_pred(db, ctx + x + r[j], on) is Ok
        || eval_pred(db, ctx + x + r[j], on) == Err::<Truth, SqlError>(e),
    ensures
        (on_truths(db, ctx, r, on)(x) is Ok) == (forall|j: int| 0 <= j < r.len() ==> #[trigger] eval_pred(db, ctx + x + r[j], on) is Ok),
        on_truths(db, ctx, r, on)(x) is Ok || on_truths(db, ctx, r, on)(x) == Err::<Seq<Truth>, SqlError>(e),
{
    let j = join_results(db, ctx + x, r, on);
    assert forall|k: int| 0 <= k < j.len() implies #[trigger] j[k] is Ok || j[k] == Err::<Truth, SqlError>(e) by {
        assert(j[k] == eval_pred(db, ctx + x + r[k], on));
    }
    lemma_collect_uniform(j, e);
    if collect(j) is Ok {
        assert forall|k: int| 0 <= k < r.len() implies #[trigger] eval_pred(db, ctx + x + r[k], on) is Ok by {
            assert(j[k] == eval_pred(db, ctx + x + r[k], on));
        }
    }
    if forall|k: int| 0 <= k < r.len() ==> #[trigger] eval_pred(db, ctx + x + r[k], on) is Ok {
        assert forall|k: int| 0 <= k < j.len() implies #[trigger] j[k] is Ok by {
            assert(j[k] == eval_pred(db, ctx + x + r[k], on));
        }
    }
}

/// L4, LEFT JOIN: bag-equal inputs give bag-equal outcomes when the ON outcomes' errors are uniform.
pub proof fn lemma_left_join_bag(db: Database, ctx: Row, l: Seq<Row>, l2: Seq<Row>, r: Seq<Row>, r2: Seq<Row>, on: Pred,
    n: nat, e: SqlError)
    requires
        l.to_multiset() == l2.to_multiset(),
        r.to_multiset() == r2.to_multiset(),
        on_uniform(db, ctx, l, r, on, e),
    ensures bag_eq(left_join_op(db, ctx, l, r, on, n), left_join_op(db, ctx, l2, r2, on, n)),
{
    // Every pair of (l2, r2) rows is a pair of (l, r) rows: uniformity carries over.
    assert forall|i: int, j: int| 0 <= i < l2.len() && 0 <= j < r2.len() implies
        #[trigger] eval_pred(db, ctx + l2[i] + r2[j], on) is Ok || eval_pred(db, ctx + l2[i] + r2[j], on) == Err::<Truth, SqlError>(e) by {
        let x = lemma_bag_contains(l, l2, i);
        let y = lemma_bag_contains(r, r2, j);
        assert(eval_pred(db, ctx + l[x] + r[y], on) is Ok || eval_pred(db, ctx + l[x] + r[y], on) == Err::<Truth, SqlError>(e));
    }
    // Per left row: the outcome over `r` is the outcome over `r2` (same pairs).
    let f = on_truths(db, ctx, r, on);
    let f2 = on_truths(db, ctx, r2, on);
    assert forall|i: int| #![trigger l[i]] 0 <= i < l.len() implies
        (f(l[i]) is Ok || f(l[i]) == Err::<Seq<Truth>, SqlError>(e)) && (f(l[i]) is Ok) == (f2(l[i]) is Ok)
        && (f2(l[i]) is Ok || f2(l[i]) == Err::<Seq<Truth>, SqlError>(e)) by {
        let x = l[i];
        assert forall|j: int| 0 <= j < r.len() implies #[trigger] eval_pred(db, ctx + x + r[j], on) is Ok
            || eval_pred(db, ctx + x + r[j], on) == Err::<Truth, SqlError>(e) by {}
        lemma_on_truths(db, ctx, x, r, on, e);
        let k = lemma_bag_contains(l2, l, i);
        assert forall|j: int| 0 <= j < r2.len() implies #[trigger] eval_pred(db, ctx + x + r2[j], on) is Ok
            || eval_pred(db, ctx + x + r2[j], on) == Err::<Truth, SqlError>(e) by {
            assert(l2[k] == x);
        }
        lemma_on_truths(db, ctx, x, r2, on, e);
        if (f(x) is Ok) != (f2(x) is Ok) {
            if f(x) is Ok {
                let j = choose|j: int| 0 <= j < r2.len() && !(#[trigger] eval_pred(db, ctx + x + r2[j], on) is Ok);
                let y = lemma_bag_contains(r, r2, j);
            } else {
                let j = choose|j: int| 0 <= j < r.len() && !(#[trigger] eval_pred(db, ctx + x + r[j], on) is Ok);
                let y = lemma_bag_contains(r2, r, j);
            }
        }
    }
    let (oa, ob) = (left_join_results(db, ctx, l, r, on), left_join_results(db, ctx, l2, r2, on));
    assert(oa =~= by_row(l, f)) by {
        assert forall|i: int| 0 <= i < l.len() implies oa[i] == #[trigger] by_row(l, f)[i] by {
            crate::bridge::collect::lemma_collect_pointwise::<Truth>();
            assert(Seq::new(r.len(), |j: int| eval_pred(db, ctx + l[i] + r[j], on)) =~= join_results(db, ctx + l[i], r, on));
        }
    }
    assert(ob =~= by_row(l2, f2)) by {
        assert forall|i: int| 0 <= i < l2.len() implies ob[i] == #[trigger] by_row(l2, f2)[i] by {
            crate::bridge::collect::lemma_collect_pointwise::<Truth>();
            assert(Seq::new(r2.len(), |j: int| eval_pred(db, ctx + l2[i] + r2[j], on)) =~= join_results(db, ctx + l2[i], r2, on));
        }
    }
    assert forall|i: int| 0 <= i < by_row(l, f).len() implies #[trigger] by_row(l, f)[i] is Ok
        || by_row(l, f)[i] == Err::<Seq<Truth>, SqlError>(e) by {
        assert((f(l[i]) is Ok || f(l[i]) == Err::<Seq<Truth>, SqlError>(e)));
    }
    lemma_by_row_bag(l, l2, f, e);
    // `f` and `f2` agree on success for every left row; so the l2-collections of `f` and `f2` agree too.
    assert forall|i: int| 0 <= i < l2.len() implies (#[trigger] f(l2[i]) is Ok) == (f2(l2[i]) is Ok)
        && (f2(l2[i]) is Ok || f2(l2[i]) == Err::<Seq<Truth>, SqlError>(e)) by {
        let k = lemma_bag_contains(l, l2, i);
        assert((f(l[k]) is Ok) == (f2(l[k]) is Ok));
    }
    let (cf, cf2) = (by_row(l2, f), by_row(l2, f2));
    assert forall|i: int| 0 <= i < cf2.len() implies #[trigger] cf2[i] is Ok || cf2[i] == Err::<Seq<Truth>, SqlError>(e) by {
        assert(cf2[i] == f2(l2[i]));
        assert((f(l2[i]) is Ok) == (f2(l2[i]) is Ok));
    }
    lemma_collect_uniform(cf, e);
    lemma_collect_uniform(cf2, e);
    if collect(cf) is Ok && !(collect(cf2) is Ok) {
        let i = choose|i: int| 0 <= i < cf2.len() && !(#[trigger] cf2[i] is Ok);
        assert(cf[i] is Ok);
    }
    if collect(cf2) is Ok && !(collect(cf) is Ok) {
        let i = choose|i: int| 0 <= i < cf.len() && !(#[trigger] cf[i] is Ok);
        assert(cf2[i] is Ok);
    }
    if collect(by_row(l, f)) is Ok {
        lemma_collect_ok(by_row(l, f));
        lemma_collect_ok(cf2);
        let (ta, tb) = (collect(by_row(l, f))->Ok_0, collect(cf2)->Ok_0);
        assert forall|i: int| 0 <= i < l.len() implies f(l[i]) == Ok::<Seq<Truth>, SqlError>(#[trigger] ta[i]) by {
            assert(by_row(l, f)[i] == Ok::<Seq<Truth>, SqlError>(ta[i]));
        }
        assert forall|i: int| 0 <= i < l2.len() implies f2(l2[i]) == Ok::<Seq<Truth>, SqlError>(#[trigger] tb[i]) by {
            assert(cf2[i] == Ok::<Seq<Truth>, SqlError>(tb[i]));
        }
        lemma_left_join_blocks(db, ctx, l, r, on, n, ta);
        lemma_left_join_blocks(db, ctx, l2, r2, on, n, tb);
        let (g, g2) = (left_join_block(db, ctx, r, on, n), left_join_block(db, ctx, r2, on, n));
        lemma_flat_by_bag(l, l2, g);
        assert forall|i: int| 0 <= i < l2.len() implies (#[trigger] g(l2[i])).to_multiset() == g2(l2[i]).to_multiset() by {
            assert(cf[i] is Ok);
            lemma_left_join_block_bag(db, ctx, l2[i], r, r2, on, n);
        }
        lemma_flat_by_blocks(l2, g, g2);
    }
}

// ------------------------------------------------------------------------------------- aggregation

/// The aggregate arguments of one row.
pub open spec fn args_at(db: Database, ctx: Row, aggs: Seq<Agg>) -> spec_fn(Row) -> Result<Row, SqlError> {
    |r: Row| agg_args(db, ctx + r, aggs)
}

/// L4, aggregation without GROUP BY: bag-equal inputs give the same outcome when the arguments' errors are
/// uniform and the aggregates are order-free over the argument rows.
pub proof fn lemma_aggregate_bag(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, aggs: Seq<Agg>, e: SqlError)
    requires
        a.to_multiset() == b.to_multiset(),
        uniform(agg_args_results(db, ctx, a, aggs), e),
        collect(agg_args_results(db, ctx, a, aggs)) matches Ok(args) ==> aggs_order_free(aggs, args),
    ensures aggregate_op(db, ctx, a, aggs) == aggregate_op(db, ctx, b, aggs),
{
    let f = args_at(db, ctx, aggs);
    assert(agg_args_results(db, ctx, a, aggs) =~= by_row(a, f));
    assert(agg_args_results(db, ctx, b, aggs) =~= by_row(b, f));
    lemma_by_row_bag(a, b, f, e);
    if collect(by_row(a, f)) is Ok {
        lemma_by_row_values(a, f);
        lemma_by_row_values(b, f);
        lemma_map_bag(a, b, |r: Row| f(r)->Ok_0);
        lemma_agg_row_bag(aggs, collect(by_row(a, f))->Ok_0, collect(by_row(b, f))->Ok_0);
    }
}

/// The key of a row of a GROUP BY whose input succeeded (`spec::eval::group_input`).
pub open spec fn group_key(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>) -> spec_fn(Row) -> Row {
    |r: Row| group_input(db, ctx + r, keys, aggs)->Ok_0.0
}

/// The aggregate arguments of a row of a GROUP BY whose input succeeded.
pub open spec fn group_args(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>) -> spec_fn(Row) -> Row {
    |r: Row| group_input(db, ctx + r, keys, aggs)->Ok_0.1
}

/// The group input of one row.
pub open spec fn group_at(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>) -> spec_fn(Row) -> Result<(Row, Row), SqlError> {
    |r: Row| group_input(db, ctx + r, keys, aggs)
}

/// H2 and the group-level part of H1 for a GROUP BY over `rows` whose inputs all succeed: exact keys, and in every
/// group order-free aggregates whose row is a value or the one error `e`.
pub open spec fn groups_order_free(db: Database, ctx: Row, rows: Seq<Row>, keys: Seq<Expr>, aggs: Seq<Agg>, e: SqlError) -> bool {
    let ks = rows.map_values(group_key(db, ctx, keys, aggs));
    let args = rows.map_values(group_args(db, ctx, keys, aggs));
    &&& rows_exact(ks)
    &&& forall|i: int| 0 <= i < rows.len() ==> {
        let m = group_members(ks, args, #[trigger] ks[i]);
        aggs_order_free(aggs, m) && (agg_row(aggs, m) is Ok || agg_row(aggs, m) == Err::<Row, SqlError>(e))
    }
}

/// The members of a group, as kept rows: the arguments of the rows whose key is not distinct from `k`.
pub proof fn lemma_group_members_keep(rows: Seq<Row>, kf: spec_fn(Row) -> Row, af: spec_fn(Row) -> Row, k: Row)
    ensures group_members(rows.map_values(kf), rows.map_values(af), k)
        == keep(rows, |r: Row| row_not_distinct(kf(r), k)).map_values(af),
    decreases rows.len(),
{
    let p = |r: Row| row_not_distinct(kf(r), k);
    if rows.len() > 0 {
        let d = rows.drop_last();
        lemma_group_members_keep(d, kf, af, k);
        assert(rows.map_values(kf).drop_last() =~= d.map_values(kf));
        assert(rows.map_values(af).drop_last() =~= d.map_values(af));
        if p(rows.last()) {
            assert(keep(rows, p).map_values(af) =~= keep(d, p).map_values(af).push(af(rows.last())));
        }
    } else {
        assert(rows.map_values(kf) =~= Seq::<Row>::empty());
        assert(keep(rows, p).map_values(af) =~= Seq::<Row>::empty());
    }
}

/// The outcome of the group with key `k`.
pub open spec fn group_outcome(aggs: Seq<Agg>, ks: Seq<Row>, args: Seq<Row>) -> spec_fn(Row) -> Result<Row, SqlError> {
    |k: Row| match agg_row(aggs, group_members(ks, args, k)) {
        Ok(a) => Ok(k + a),
        Err(e) => Err(e),
    }
}

/// The groups of two inputs with equal multisets agree on a key whose group is order-free.
proof fn lemma_group_outcome_bag(aggs: Seq<Agg>, a: Seq<Row>, b: Seq<Row>, kf: spec_fn(Row) -> Row, af: spec_fn(Row) -> Row, k: Row)
    requires
        a.to_multiset() == b.to_multiset(),
        aggs_order_free(aggs, group_members(a.map_values(kf), a.map_values(af), k)),
    ensures
        group_outcome(aggs, a.map_values(kf), a.map_values(af))(k) == group_outcome(aggs, b.map_values(kf), b.map_values(af))(k),
{
    let p = |r: Row| row_not_distinct(kf(r), k);
    lemma_group_members_keep(a, kf, af, k);
    lemma_group_members_keep(b, kf, af, k);
    lemma_keep_bag(a, b, p);
    lemma_map_bag(keep(a, p), keep(b, p), af);
    lemma_agg_row_bag(aggs, group_members(a.map_values(kf), a.map_values(af), k), group_members(b.map_values(kf), b.map_values(af), k));
}

/// GROUP BY over evaluated keys and arguments of bag-equal inputs: bag-equal outcomes, given exact keys and
/// order-free groups with uniform errors.
pub proof fn lemma_group_rows_bag(aggs: Seq<Agg>, a: Seq<Row>, b: Seq<Row>, kf: spec_fn(Row) -> Row, af: spec_fn(Row) -> Row,
    e2: SqlError)
    requires
        a.to_multiset() == b.to_multiset(),
        rows_exact(a.map_values(kf)),
        forall|i: int| 0 <= i < a.len() ==> {
            let m = group_members(a.map_values(kf), a.map_values(af), #[trigger] a.map_values(kf)[i]);
            aggs_order_free(aggs, m) && (agg_row(aggs, m) is Ok || agg_row(aggs, m) == Err::<Row, SqlError>(e2))
        },
    ensures
        bag_eq(group_rows(aggs, a.map_values(kf), a.map_values(af)), group_rows(aggs, b.map_values(kf), b.map_values(af))),
{
    hide(agg_row);
    hide(group_members);
    let (ka, aa) = (a.map_values(kf), a.map_values(af));
    let (kb, ab) = (b.map_values(kf), b.map_values(af));
    lemma_map_bag(a, b, kf);
    lemma_distinct_rows_bag(ka, kb);
    lemma_distinct_rows_exact(ka);
    lemma_rows_exact_bag(ka, kb);
    lemma_distinct_rows_exact(kb);
    let (oa, ob) = (group_outcome(aggs, ka, aa), group_outcome(aggs, kb, ab));
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] oa(ka[i]) == ob(ka[i])
        && (oa(ka[i]) is Ok || oa(ka[i]) == Err::<Row, SqlError>(e2)) by {
        lemma_group_outcome_bag(aggs, a, b, kf, af, ka[i]);
    }
    let (ra, rb) = (group_results(aggs, ka, aa), group_results(aggs, kb, ab));
    let (da, db) = (distinct_rows(ka), distinct_rows(kb));
    assert(ra =~= da.map_values(oa));
    assert(rb =~= db.map_values(ob));
    assert forall|i: int| 0 <= i < db.len() implies #[trigger] db.map_values(ob)[i] == db.map_values(oa)[i] by {
        assert(db.contains(db[i]));
        assert(kb.contains(db[i]));
        let j = choose|j: int| 0 <= j < kb.len() && kb[j] == db[i];
        let x = lemma_bag_contains(ka, kb, j);
    }
    assert(rb =~= db.map_values(oa));
    lemma_map_bag(da, db, oa);
    assert forall|i: int| 0 <= i < ra.len() implies #[trigger] ra[i] is Ok || ra[i] == Err::<Row, SqlError>(e2) by {
        assert(da.contains(da[i]));
        assert(ka.contains(da[i]));
        let j = choose|j: int| 0 <= j < ka.len() && ka[j] == da[i];
    }
    assert forall|i: int| 0 <= i < rb.len() implies #[trigger] rb[i] is Ok || rb[i] == Err::<Row, SqlError>(e2) by {
        let j = lemma_bag_contains(ra, rb, i);
    }
    lemma_collect_uniform(ra, e2);
    lemma_collect_uniform(rb, e2);
    if collect(ra) is Ok && !(collect(rb) is Ok) {
        let i = choose|i: int| 0 <= i < rb.len() && !(#[trigger] rb[i] is Ok);
        let j = lemma_bag_contains(ra, rb, i);
    }
    if collect(rb) is Ok && !(collect(ra) is Ok) {
        let i = choose|i: int| 0 <= i < ra.len() && !(#[trigger] ra[i] is Ok);
        let j = lemma_bag_contains(rb, ra, i);
    }
    assert(group_rows(aggs, ka, aa) == collect(ra)) by {
        crate::bridge::collect::lemma_collect_pointwise::<Row>();
    }
    assert(group_rows(aggs, kb, ab) == collect(rb)) by {
        crate::bridge::collect::lemma_collect_pointwise::<Row>();
    }
    if collect(ra) is Ok {
        lemma_collect_ok(ra);
        lemma_collect_ok(rb);
        let (va, vb) = (collect(ra)->Ok_0, collect(rb)->Ok_0);
        assert(va =~= ra.map_values(|x: Result<Row, SqlError>| x->Ok_0));
        assert(vb =~= rb.map_values(|x: Result<Row, SqlError>| x->Ok_0));
        lemma_map_bag(ra, rb, |x: Result<Row, SqlError>| x->Ok_0);
    }
}

/// The per-row GROUP BY inputs as a per-row function.
pub proof fn lemma_group_input_by_row(db: Database, ctx: Row, a: Seq<Row>, keys: Seq<Expr>, aggs: Seq<Agg>)
    ensures group_input_results(db, ctx, a, keys, aggs) == by_row(a, group_at(db, ctx, keys, aggs)),
{
    hide(eval_exprs);
    hide(agg_args);
    let (rs, bs) = (group_input_results(db, ctx, a, keys, aggs), by_row(a, group_at(db, ctx, keys, aggs)));
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] rs[i] == bs[i] by {
        lemma_group_input_results(db, ctx, a, keys, aggs, i);
    }
    assert(rs =~= bs);
}

/// A GROUP BY whose every group input succeeds is `group_rows` of the rows' keys and arguments.
pub proof fn lemma_group_by_op_values(db: Database, ctx: Row, a: Seq<Row>, keys: Seq<Expr>, aggs: Seq<Agg>)
    requires collect(group_input_results(db, ctx, a, keys, aggs)) is Ok,
    ensures group_by_op(db, ctx, a, keys, aggs) == group_rows(aggs, a.map_values(group_key(db, ctx, keys, aggs)),
        a.map_values(group_args(db, ctx, keys, aggs))),
{
    hide(group_rows);
    hide(group_input);
    hide(eval_exprs);
    hide(agg_args);
    let g = group_at(db, ctx, keys, aggs);
    lemma_group_input_by_row(db, ctx, a, keys, aggs);
    lemma_by_row_values(a, g);
    let pa = collect(by_row(a, g))->Ok_0;
    assert(pa.map_values(|p: (Row, Row)| p.0) =~= a.map_values(group_key(db, ctx, keys, aggs)));
    assert(pa.map_values(|p: (Row, Row)| p.1) =~= a.map_values(group_args(db, ctx, keys, aggs)));
}

/// L4, GROUP BY: bag-equal inputs give bag-equal outcomes when the group inputs' errors are uniform (`e`), the
/// keys exact and every group order-free with uniform errors (`e2`).
pub proof fn lemma_group_by_bag(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, keys: Seq<Expr>, aggs: Seq<Agg>,
    e: SqlError, e2: SqlError)
    requires
        a.to_multiset() == b.to_multiset(),
        uniform(group_input_results(db, ctx, a, keys, aggs), e),
        collect(group_input_results(db, ctx, a, keys, aggs)) is Ok ==> groups_order_free(db, ctx, a, keys, aggs, e2),
    ensures bag_eq(group_by_op(db, ctx, a, keys, aggs), group_by_op(db, ctx, b, keys, aggs)),
{
    hide(group_rows);
    hide(group_input);
    hide(group_by_op);
    hide(eval_exprs);
    hide(agg_args);
    let g = group_at(db, ctx, keys, aggs);
    lemma_group_input_by_row(db, ctx, a, keys, aggs);
    lemma_group_input_by_row(db, ctx, b, keys, aggs);
    lemma_by_row_bag(a, b, g, e);
    if collect(by_row(a, g)) is Ok {
        lemma_group_by_op_values(db, ctx, a, keys, aggs);
        lemma_group_by_op_values(db, ctx, b, keys, aggs);
        lemma_group_rows_bag(aggs, a, b, group_key(db, ctx, keys, aggs), group_args(db, ctx, keys, aggs), e2);
    } else {
        reveal(group_by_op);
    }
}

// ------------------------------------------------------------------------------------- node forms

/// L4, node form of WHERE: a bag-equal input keeps the outcome bag-equal, when the condition's errors are
/// uniform on the original input's rows.
pub proof fn lemma_filter_child_bag(db: Database, ctx: Row, pred: Pred, in1: Query, in2: Query, e: SqlError)
    requires
        bag_eq(eval_query(db, ctx, in1), eval_query(db, ctx, in2)),
        eval_query(db, ctx, in1) matches Ok(rows) ==> uniform(filter_results(db, ctx, rows, pred), e),
    ensures
        bag_eq(eval_query(db, ctx, Query::Filter { pred, input: Box::new(in1) }),
            eval_query(db, ctx, Query::Filter { pred, input: Box::new(in2) })),
{
    lemma_eval_op(db, ctx, Query::Filter { pred, input: Box::new(in1) });
    lemma_eval_op(db, ctx, Query::Filter { pred, input: Box::new(in2) });
    if let (Ok(a), Ok(b)) = (eval_query(db, ctx, in1), eval_query(db, ctx, in2)) {
        lemma_filter_bag(db, ctx, a, b, pred, e);
    }
}

/// L4, node form of SELECT.
pub proof fn lemma_project_child_bag(db: Database, ctx: Row, exprs: Seq<Expr>, in1: Query, in2: Query, e: SqlError)
    requires
        bag_eq(eval_query(db, ctx, in1), eval_query(db, ctx, in2)),
        eval_query(db, ctx, in1) matches Ok(rows) ==> uniform(project_results(db, ctx, rows, exprs), e),
    ensures
        bag_eq(eval_query(db, ctx, Query::Project { exprs, input: Box::new(in1) }),
            eval_query(db, ctx, Query::Project { exprs, input: Box::new(in2) })),
{
    lemma_eval_op(db, ctx, Query::Project { exprs, input: Box::new(in1) });
    lemma_eval_op(db, ctx, Query::Project { exprs, input: Box::new(in2) });
    if let (Ok(a), Ok(b)) = (eval_query(db, ctx, in1), eval_query(db, ctx, in2)) {
        lemma_project_bag(db, ctx, a, b, exprs, e);
    }
}

/// L4, node form of a product (both inputs replaced).
pub proof fn lemma_product_child_bag(db: Database, ctx: Row, l1: Query, l2: Query, r1: Query, r2: Query)
    requires
        bag_eq(eval_query(db, ctx, l1), eval_query(db, ctx, l2)),
        bag_eq(eval_query(db, ctx, r1), eval_query(db, ctx, r2)),
    ensures
        bag_eq(eval_query(db, ctx, Query::Product { left: Box::new(l1), right: Box::new(r1) }),
            eval_query(db, ctx, Query::Product { left: Box::new(l2), right: Box::new(r2) })),
{
    if let (Ok(a), Ok(a2), Ok(b), Ok(b2)) = (eval_query(db, ctx, l1), eval_query(db, ctx, l2), eval_query(db, ctx, r1),
        eval_query(db, ctx, r2)) {
        lemma_product_bag(a, a2, b, b2);
    }
}

/// L4, node form of a LEFT JOIN (both inputs replaced; the right inputs of one static arity).
pub proof fn lemma_left_join_child_bag(db: Database, ctx: Row, l1: Query, l2: Query, r1: Query, r2: Query, on: Pred, e: SqlError)
    requires
        bag_eq(eval_query(db, ctx, l1), eval_query(db, ctx, l2)),
        bag_eq(eval_query(db, ctx, r1), eval_query(db, ctx, r2)),
        query_arity(db.schema, r1) == query_arity(db.schema, r2),
        (eval_query(db, ctx, l1), eval_query(db, ctx, r1)) matches (Ok(l), Ok(r)) ==> on_uniform(db, ctx, l, r, on, e),
    ensures
        bag_eq(eval_query(db, ctx, Query::LeftJoin { left: Box::new(l1), right: Box::new(r1), on }),
            eval_query(db, ctx, Query::LeftJoin { left: Box::new(l2), right: Box::new(r2), on })),
{
    lemma_eval_op(db, ctx, Query::LeftJoin { left: Box::new(l1), right: Box::new(r1), on });
    lemma_eval_op(db, ctx, Query::LeftJoin { left: Box::new(l2), right: Box::new(r2), on });
    if let (Ok(a), Ok(a2), Ok(b), Ok(b2)) = (eval_query(db, ctx, l1), eval_query(db, ctx, l2), eval_query(db, ctx, r1),
        eval_query(db, ctx, r2)) {
        lemma_left_join_bag(db, ctx, a, a2, b, b2, on, query_arity(db.schema, r1), e);
    }
}

/// L4, node form of aggregation without GROUP BY: the same outcome.
pub proof fn lemma_aggregate_child_bag(db: Database, ctx: Row, aggs: Seq<Agg>, in1: Query, in2: Query, e: SqlError)
    requires
        bag_eq(eval_query(db, ctx, in1), eval_query(db, ctx, in2)),
        eval_query(db, ctx, in1) matches Ok(rows) ==> {
            &&& uniform(agg_args_results(db, ctx, rows, aggs), e)
            &&& collect(agg_args_results(db, ctx, rows, aggs)) matches Ok(args) ==> aggs_order_free(aggs, args)
        },
    ensures
        eval_query(db, ctx, Query::Aggregate { aggs, input: Box::new(in1) })
            == eval_query(db, ctx, Query::Aggregate { aggs, input: Box::new(in2) }),
{
    lemma_eval_op(db, ctx, Query::Aggregate { aggs, input: Box::new(in1) });
    lemma_eval_op(db, ctx, Query::Aggregate { aggs, input: Box::new(in2) });
    if let (Ok(a), Ok(b)) = (eval_query(db, ctx, in1), eval_query(db, ctx, in2)) {
        lemma_aggregate_bag(db, ctx, a, b, aggs, e);
    }
}

/// L4, node form of GROUP BY.
pub proof fn lemma_group_by_child_bag(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, in1: Query, in2: Query,
    e: SqlError, e2: SqlError)
    requires
        bag_eq(eval_query(db, ctx, in1), eval_query(db, ctx, in2)),
        eval_query(db, ctx, in1) matches Ok(rows) ==> {
            &&& uniform(group_input_results(db, ctx, rows, keys, aggs), e)
            &&& collect(group_input_results(db, ctx, rows, keys, aggs)) is Ok ==> groups_order_free(db, ctx, rows, keys, aggs, e2)
        },
    ensures
        bag_eq(eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(in1) }),
            eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(in2) })),
{
    lemma_eval_op(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(in1) });
    lemma_eval_op(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(in2) });
    if let (Ok(a), Ok(b)) = (eval_query(db, ctx, in1), eval_query(db, ctx, in2)) {
        lemma_group_by_bag(db, ctx, a, b, keys, aggs, e, e2);
    }
}

/// L4, node form of SELECT DISTINCT.
pub proof fn lemma_distinct_child_bag(db: Database, ctx: Row, in1: Query, in2: Query)
    requires
        bag_eq(eval_query(db, ctx, in1), eval_query(db, ctx, in2)),
        eval_query(db, ctx, in1) matches Ok(rows) ==> rows_exact(rows),
    ensures
        bag_eq(eval_query(db, ctx, Query::Distinct(Box::new(in1))), eval_query(db, ctx, Query::Distinct(Box::new(in2)))),
{
    if let (Ok(a), Ok(b)) = (eval_query(db, ctx, in1), eval_query(db, ctx, in2)) {
        lemma_distinct_rows_bag(a, b);
    }
}

// ------------------------------------------------------------------------------------- conditions from L3

/// L3 to L4: a condition the analysis finds uniform for `code` (context classes `cls`, input column classes
/// `rcls`) is uniform on every row of the input.
pub proof fn lemma_filter_uniform_class(db: Database, ctx: Row, cls: Seq<VClass>, rows: Seq<Row>, rcls: Seq<VClass>,
    pred: Pred, code: SqlError)
    requires db_wf(db), row_in(ctx, cls), rows_in(rows, rcls), pred_uniform(db.schema, cls + rcls, pred, code),
    ensures uniform(filter_results(db, ctx, rows, pred), code),
{
    let rs = filter_results(db, ctx, rows, pred);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] is Ok || rs[i] == Err::<Truth, SqlError>(code) by {
        assert(row_in(rows[i], rcls));
        lemma_row_in_concat(ctx, cls, rows[i], rcls);
        lemma_pred_uniform(db, ctx + rows[i], cls + rcls, pred, code);
    }
}

/// L3 to L4: SELECT expressions the analysis finds uniform for `code` are uniform on every row of the input.
pub proof fn lemma_project_uniform_class(db: Database, ctx: Row, cls: Seq<VClass>, rows: Seq<Row>, rcls: Seq<VClass>,
    exprs: Seq<Expr>, code: SqlError)
    requires
        db_wf(db), row_in(ctx, cls), rows_in(rows, rcls),
        exprs_info(db.schema, cls + rcls, exprs) matches Some(l) && errs_only(l.errs, code),
    ensures uniform(project_results(db, ctx, rows, exprs), code),
{
    let rs = project_results(db, ctx, rows, exprs);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] is Ok || rs[i] == Err::<Row, SqlError>(code) by {
        assert(row_in(rows[i], rcls));
        lemma_row_in_concat(ctx, cls, rows[i], rcls);
        lemma_exprs_sound(db, ctx + rows[i], cls + rcls, exprs);
    }
}

/// L3 to L4 (H2): values of an exact class that is not boolean make every aggregate order-free.
pub proof fn lemma_order_free_class(a: Agg, vs: Seq<Val>, c: VClass)
    requires vals_in(vs, c), class_exact(c), !(c.kind is Bool),
    ensures agg_order_free(a, vs),
    decreases a,
{
    assert forall|i: int, j: int| 0 <= i < vs.len() && 0 <= j < vs.len() && val_not_distinct(#[trigger] vs[i], #[trigger] vs[j])
        implies vs[i] == vs[j] by {
        lemma_class_exact(vs[i], vs[j], c);
    }
    assert forall|i: int, j: int| 0 <= i < vs.len() && 0 <= j < vs.len() && !(vs[i] is Null) && !(vs[j] is Null)
        implies crate::bridge::typing::val_family(#[trigger] vs[i]) == crate::bridge::typing::val_family(#[trigger] vs[j]) by {
        assert(in_class(vs[i], c) && in_class(vs[j], c));
    }
    assert forall|i: int| 0 <= i < vs.len() implies !(#[trigger] vs[i] is Bool) by {
        assert(in_class(vs[i], c));
    }
    if let Agg::DistinctAgg(inner) = a {
        lemma_order_free_class(*inner, vs, c);
    }
}

} // verus!
