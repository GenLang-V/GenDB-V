//! L4 (hazard H2): which operator results do not depend on the order of their input (engine toolkit; nothing
//! here names a query, a table or a column).
//!
//! - Deduplication: on exact rows (values (`vals_exact`) or rows (`rows_exact`) that are SQL "not distinct" only
//!   when equal), `distinct_rows` / `distinct_vals` keep one copy of every element, so inputs with equal
//!   multisets give outputs with equal multisets (`lemma_distinct_rows_bag`, `lemma_distinct_vals_bag`). Without
//!   exactness the first occurrence's representative (for example `1.0` against `1.00`) depends on the order.
//! - Aggregate values: COUNT, SUM and AVG depend only on the multiset of their arguments (exact arithmetic).
//!   MIN and MAX need exact arguments of one comparison family (`vals_ordered`; the first of equal values is
//!   kept), DISTINCT aggregates exact arguments: `agg_order_free`. Then `lemma_agg_value_bag` and
//!   `lemma_agg_row_bag`.
//!
//! These are the H2 side conditions of the GROUP BY, aggregate and DISTINCT congruences (`engine_link::congruence`);
//! the L3 exactness class (`engine_link::classes`) establishes them statically.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::aggs::avg::*;
use crate::spec::aggs::minmax::*;
use crate::exec::relational::domain::*;
use crate::exec::relational::aggregate::{num_sum_at, lemma_num_sum_at};
use crate::bridge::typing::val_family;
use crate::bridge::order::{lemma_compare_antisym, lemma_compare_trans};
use crate::bridge::equality::*;
use crate::link::query::{lemma_nodup_same_multiset, lemma_has_nd_contains};
use crate::link::expr::lemma_align_same;
use crate::engine_link::bag::*;

verus! {

// ------------------------------------------------------------------------------------- exactness

/// Rows that are SQL "not distinct" only when equal.
pub open spec fn rows_exact(rows: Seq<Row>) -> bool {
    forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && row_not_distinct(#[trigger] rows[i], #[trigger] rows[j])
        ==> rows[i] == rows[j]
}

/// Values that are SQL "not distinct" only when equal.
pub open spec fn vals_exact(vs: Seq<Val>) -> bool {
    forall|i: int, j: int| 0 <= i < vs.len() && 0 <= j < vs.len() && val_not_distinct(#[trigger] vs[i], #[trigger] vs[j])
        ==> vs[i] == vs[j]
}

/// No boolean value, and all non-NULL values of one comparison family (MIN and MAX never raise).
pub open spec fn vals_ordered(vs: Seq<Val>) -> bool {
    &&& forall|i: int| 0 <= i < vs.len() ==> !(#[trigger] vs[i] is Bool)
    &&& forall|i: int, j: int| 0 <= i < vs.len() && 0 <= j < vs.len() && !(vs[i] is Null) && !(vs[j] is Null)
        ==> val_family(#[trigger] vs[i]) == val_family(#[trigger] vs[j])
}

/// The value of aggregate `a` does not depend on the order of its argument values `vs` (H2).
pub open spec fn agg_order_free(a: Agg, vs: Seq<Val>) -> bool
    decreases a,
{
    match a {
        Agg::Min(_) | Agg::Max(_) => vals_exact(vs) && vals_ordered(vs),
        Agg::DistinctAgg(inner) => vals_exact(vs) && agg_order_free(*inner, vs),
        _ => true,
    }
}

/// Every aggregate is order-free over its argument column of `args`.
pub open spec fn aggs_order_free(aggs: Seq<Agg>, args: Seq<Row>) -> bool {
    forall|j: int| 0 <= j < aggs.len() ==> #[trigger] agg_order_free(aggs[j], column(args, j))
}

/// Order-freedom holds of any sub-collection of the values.
pub proof fn lemma_order_free_subset(a: Agg, vs: Seq<Val>, ws: Seq<Val>)
    requires agg_order_free(a, vs), forall|j: int| 0 <= j < ws.len() ==> vs.contains(#[trigger] ws[j]),
    ensures agg_order_free(a, ws),
    decreases a,
{
    assert forall|i: int, j: int| 0 <= i < ws.len() && 0 <= j < ws.len() && val_not_distinct(#[trigger] ws[i], #[trigger] ws[j])
        && vals_exact(vs) implies ws[i] == ws[j] by {
        let (x, y) = (choose|x: int| 0 <= x < vs.len() && vs[x] == ws[i], choose|y: int| 0 <= y < vs.len() && vs[y] == ws[j]);
        assert(vs.contains(ws[i]) && vs.contains(ws[j]));
    }
    assert forall|i: int| 0 <= i < ws.len() && vals_ordered(vs) implies !(#[trigger] ws[i] is Bool) by {
        assert(vs.contains(ws[i]));
    }
    assert forall|i: int, j: int| 0 <= i < ws.len() && 0 <= j < ws.len() && !(ws[i] is Null) && !(ws[j] is Null)
        && vals_ordered(vs) implies val_family(#[trigger] ws[i]) == val_family(#[trigger] ws[j]) by {
        assert(vs.contains(ws[i]) && vs.contains(ws[j]));
        let x = choose|x: int| 0 <= x < vs.len() && vs[x] == ws[i];
        let y = choose|y: int| 0 <= y < vs.len() && vs[y] == ws[j];
    }
    if let Agg::DistinctAgg(inner) = a {
        lemma_order_free_subset(*inner, vs, ws);
    }
}

/// Exactness transfers to an equal multiset.
pub proof fn lemma_rows_exact_bag(a: Seq<Row>, b: Seq<Row>)
    requires a.to_multiset() == b.to_multiset(), rows_exact(a),
    ensures rows_exact(b),
{
    assert forall|i: int, j: int| 0 <= i < b.len() && 0 <= j < b.len() && row_not_distinct(#[trigger] b[i], #[trigger] b[j])
        implies b[i] == b[j] by {
        let x = lemma_bag_contains(a, b, i);
        let y = lemma_bag_contains(a, b, j);
    }
}

/// Order-freedom transfers to an equal multiset.
pub proof fn lemma_order_free_bag(a: Agg, vs: Seq<Val>, ws: Seq<Val>)
    requires vs.to_multiset() == ws.to_multiset(), agg_order_free(a, vs),
    ensures agg_order_free(a, ws),
{
    assert forall|j: int| 0 <= j < ws.len() implies vs.contains(#[trigger] ws[j]) by {
        let x = lemma_bag_contains(vs, ws, j);
    }
    lemma_order_free_subset(a, vs, ws);
}

// ------------------------------------------------------------------------------------- deduplication

/// On exact rows `distinct_rows` keeps exactly one copy of every row.
pub proof fn lemma_distinct_rows_exact(rows: Seq<Row>)
    requires rows_exact(rows),
    ensures
        distinct_rows(rows).no_duplicates(),
        forall|x: Row| #[trigger] distinct_rows(rows).contains(x) <==> rows.contains(x),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        assert forall|i: int, j: int| 0 <= i < init.len() && 0 <= j < init.len() && row_not_distinct(#[trigger] init[i], #[trigger] init[j])
            implies init[i] == init[j] by {
            assert(init[i] == rows[i] && init[j] == rows[j]);
        }
        lemma_distinct_rows_exact(init);
        let d = distinct_rows(init);
        let x = rows.last();
        assert forall|a: Row, b: Row| rows.contains(a) && rows.contains(b) implies (#[trigger] row_not_distinct(a, b) <==> a == b) by {
            let i = choose|i: int| 0 <= i < rows.len() && rows[i] == a;
            let j = choose|j: int| 0 <= j < rows.len() && rows[j] == b;
            if a == b {
                lemma_row_not_distinct_refl(a);
            }
        }
        assert forall|i: int| 0 <= i < d.len() implies rows.contains(#[trigger] d[i]) by {
            assert(d.contains(d[i]));
            assert(init.contains(d[i]));
            let j = choose|j: int| 0 <= j < init.len() && init[j] == d[i];
            assert(rows[j] == init[j]);
        }
        assert(rows[rows.len() - 1] == x);
        lemma_has_nd_contains(d, x, rows);
        assert forall|y: Row| #[trigger] distinct_rows(rows).contains(y) <==> rows.contains(y) by {
            if rows.contains(y) && y != x {
                let j = choose|j: int| 0 <= j < rows.len() && rows[j] == y;
                assert(init[j] == y);
                assert(init.contains(y));
            }
            if init.contains(y) {
                let j = choose|j: int| 0 <= j < init.len() && init[j] == y;
                assert(rows[j] == y);
            }
            if distinct_rows(rows).contains(y) && !d.contains(y) {
                let k = choose|k: int| 0 <= k < distinct_rows(rows).len() && distinct_rows(rows)[k] == y;
                assert(y == x);
            }
            if d.contains(y) {
                let k = choose|k: int| 0 <= k < d.len() && d[k] == y;
                if !has_not_distinct(d, x) {
                    assert(distinct_rows(rows)[k] == y);
                }
            }
            if y == x && !has_not_distinct(d, x) {
                assert(distinct_rows(rows)[d.len() as int] == x);
            }
        }
        if !has_not_distinct(d, x) {
            assert forall|i: int, j: int| 0 <= i < distinct_rows(rows).len() && 0 <= j < distinct_rows(rows).len() && i != j
                implies distinct_rows(rows)[i] != distinct_rows(rows)[j] by {
                if j == d.len() {
                    assert(d.contains(d[i]));
                } else if i == d.len() {
                    assert(d.contains(d[j]));
                }
            }
        }
    }
}

/// On exact rows, inputs with equal multisets have deduplications with equal multisets.
pub proof fn lemma_distinct_rows_bag(a: Seq<Row>, b: Seq<Row>)
    requires a.to_multiset() == b.to_multiset(), rows_exact(a),
    ensures distinct_rows(a).to_multiset() == distinct_rows(b).to_multiset(),
{
    lemma_rows_exact_bag(a, b);
    lemma_distinct_rows_exact(a);
    lemma_distinct_rows_exact(b);
    a.to_multiset_ensures();
    b.to_multiset_ensures();
    assert forall|x: Row| distinct_rows(a).contains(x) <==> distinct_rows(b).contains(x) by {
        if a.contains(x) {
            assert(a.to_multiset().count(x) > 0);
            assert(b.to_multiset().count(x) > 0);
        }
        if b.contains(x) {
            assert(b.to_multiset().count(x) > 0);
            assert(a.to_multiset().count(x) > 0);
        }
    }
    lemma_nodup_same_multiset(distinct_rows(a), distinct_rows(b));
}

/// `has_val_not_distinct` over exact values is `contains`.
proof fn lemma_has_val_nd_contains(d: Seq<Val>, v: Val, pool: Seq<Val>)
    requires
        forall|i: int| 0 <= i < d.len() ==> pool.contains(#[trigger] d[i]),
        pool.contains(v),
        forall|a: Val, b: Val| pool.contains(a) && pool.contains(b) ==> (#[trigger] val_not_distinct(a, b) <==> a == b),
    ensures has_val_not_distinct(d, v) <==> d.contains(v),
    decreases d.len(),
{
    if d.len() > 0 {
        let di = d.drop_last();
        assert forall|i: int| 0 <= i < di.len() implies pool.contains(#[trigger] di[i]) by {
            assert(di[i] == d[i]);
        }
        lemma_has_val_nd_contains(di, v, pool);
        assert(pool.contains(d[d.len() - 1]));
        if di.contains(v) {
            let i = choose|i: int| 0 <= i < di.len() && di[i] == v;
            assert(d[i] == v);
        }
        if d.contains(v) && d.last() != v {
            let i = choose|i: int| 0 <= i < d.len() && d[i] == v;
            assert(di[i] == v);
        }
    }
}

/// On exact values `distinct_vals` keeps exactly one copy of every non-NULL value.
pub proof fn lemma_distinct_vals_exact(vs: Seq<Val>)
    requires vals_exact(vs),
    ensures
        distinct_vals(vs).no_duplicates(),
        forall|x: Val| #[trigger] distinct_vals(vs).contains(x) <==> (vs.contains(x) && !(x is Null)),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let init = vs.drop_last();
        assert forall|i: int, j: int| 0 <= i < init.len() && 0 <= j < init.len() && val_not_distinct(#[trigger] init[i], #[trigger] init[j])
            implies init[i] == init[j] by {
            assert(init[i] == vs[i] && init[j] == vs[j]);
        }
        lemma_distinct_vals_exact(init);
        let d = distinct_vals(init);
        let x = vs.last();
        assert forall|a: Val, b: Val| vs.contains(a) && vs.contains(b) implies (#[trigger] val_not_distinct(a, b) <==> a == b) by {
            let i = choose|i: int| 0 <= i < vs.len() && vs[i] == a;
            let j = choose|j: int| 0 <= j < vs.len() && vs[j] == b;
            if a == b {
                lemma_val_not_distinct_refl(a);
            }
        }
        assert forall|i: int| 0 <= i < d.len() implies vs.contains(#[trigger] d[i]) by {
            assert(d.contains(d[i]));
            assert(init.contains(d[i]));
            let j = choose|j: int| 0 <= j < init.len() && init[j] == d[i];
            assert(vs[j] == init[j]);
        }
        assert(vs[vs.len() - 1] == x);
        lemma_has_val_nd_contains(d, x, vs);
        let r = distinct_vals(vs);
        let added = !(x is Null) && !has_val_not_distinct(d, x);
        assert forall|y: Val| #[trigger] r.contains(y) <==> (vs.contains(y) && !(y is Null)) by {
            if vs.contains(y) && y != x {
                let j = choose|j: int| 0 <= j < vs.len() && vs[j] == y;
                assert(init[j] == y);
                assert(init.contains(y));
            }
            if init.contains(y) {
                let j = choose|j: int| 0 <= j < init.len() && init[j] == y;
                assert(vs[j] == y);
            }
            if r.contains(y) && !d.contains(y) {
                let k = choose|k: int| 0 <= k < r.len() && r[k] == y;
                assert(y == x);
            }
            if d.contains(y) {
                let k = choose|k: int| 0 <= k < d.len() && d[k] == y;
                if added {
                    assert(r[k] == y);
                }
            }
            if y == x && added {
                assert(r[d.len() as int] == x);
            }
        }
        if added {
            assert forall|i: int, j: int| 0 <= i < r.len() && 0 <= j < r.len() && i != j implies r[i] != r[j] by {
                if j == d.len() {
                    assert(d.contains(d[i]));
                } else if i == d.len() {
                    assert(d.contains(d[j]));
                }
            }
        }
    }
}

/// On exact values, equal multisets have DISTINCT-aggregate inputs with equal multisets.
pub proof fn lemma_distinct_vals_bag(vs: Seq<Val>, ws: Seq<Val>)
    requires vs.to_multiset() == ws.to_multiset(), vals_exact(vs),
    ensures distinct_vals(vs).to_multiset() == distinct_vals(ws).to_multiset(),
{
    assert forall|i: int, j: int| 0 <= i < ws.len() && 0 <= j < ws.len() && val_not_distinct(#[trigger] ws[i], #[trigger] ws[j])
        implies ws[i] == ws[j] by {
        let x = lemma_bag_contains(vs, ws, i);
        let y = lemma_bag_contains(vs, ws, j);
    }
    lemma_distinct_vals_exact(vs);
    lemma_distinct_vals_exact(ws);
    vs.to_multiset_ensures();
    ws.to_multiset_ensures();
    assert forall|x: Val| distinct_vals(vs).contains(x) <==> distinct_vals(ws).contains(x) by {
        if vs.contains(x) {
            assert(vs.to_multiset().count(x) > 0);
            assert(ws.to_multiset().count(x) > 0);
        }
        if ws.contains(x) {
            assert(ws.to_multiset().count(x) > 0);
            assert(vs.to_multiset().count(x) > 0);
        }
    }
    lemma_nodup_same_multiset(distinct_vals(vs), distinct_vals(ws));
}

// ------------------------------------------------------------------------------------- sums and counts

pub open spec fn non_null_term() -> spec_fn(Val) -> int {
    |v: Val| if v is Null { 0int } else { 1int }
}

pub open spec fn int_term() -> spec_fn(Val) -> int {
    |v: Val| match v { Val::Int(x) => x, _ => 0int }
}

pub open spec fn num_term(t: nat) -> spec_fn(Val) -> int {
    |v: Val| match v { Val::Num { coeff, scale } => align(coeff, scale, t), _ => 0int }
}

pub open spec fn kind_ok(kind: NumKind, v: Val) -> bool {
    match v {
        Val::Null => true,
        Val::Int(_) => !(kind is Numeric),
        Val::Num { .. } => kind is Numeric,
        _ => false,
    }
}

proof fn lemma_count_sum(vs: Seq<Val>)
    ensures count_non_null(vs) as int == sum_by(vs, non_null_term()),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_count_sum(vs.drop_last());
    }
}

proof fn lemma_int_sum_by(vs: Seq<Val>)
    ensures int_sum(vs) == sum_by(vs, int_term()),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_int_sum_by(vs.drop_last());
    }
}

proof fn lemma_num_sum_at_by(vs: Seq<Val>, t: nat)
    ensures num_sum_at(vs, t) == sum_by(vs, num_term(t)),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_num_sum_at_by(vs.drop_last(), t);
    }
}

proof fn lemma_all_of_kind_elems(kind: NumKind, vs: Seq<Val>)
    ensures all_of_kind(kind, vs) == forall|i: int| 0 <= i < vs.len() ==> kind_ok(kind, #[trigger] vs[i]),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        lemma_all_of_kind_elems(kind, d);
        if forall|i: int| 0 <= i < vs.len() ==> kind_ok(kind, #[trigger] vs[i]) {
            assert forall|i: int| 0 <= i < d.len() implies kind_ok(kind, #[trigger] d[i]) by {
                assert(d[i] == vs[i]);
            }
            assert(kind_ok(kind, vs[vs.len() - 1]));
        }
        if all_of_kind(kind, vs) {
            assert forall|i: int| 0 <= i < vs.len() implies kind_ok(kind, #[trigger] vs[i]) by {
                if i < d.len() {
                    assert(d[i] == vs[i]);
                }
            }
        }
    }
}

proof fn lemma_all_of_kind_bag(kind: NumKind, vs: Seq<Val>, ws: Seq<Val>)
    requires vs.to_multiset() == ws.to_multiset(),
    ensures all_of_kind(kind, vs) == all_of_kind(kind, ws),
{
    lemma_all_of_kind_elems(kind, vs);
    lemma_all_of_kind_elems(kind, ws);
    if all_of_kind(kind, vs) {
        assert forall|i: int| 0 <= i < ws.len() implies kind_ok(kind, #[trigger] ws[i]) by {
            let j = lemma_bag_contains(vs, ws, i);
        }
    }
    if all_of_kind(kind, ws) {
        assert forall|i: int| 0 <= i < vs.len() implies kind_ok(kind, #[trigger] vs[i]) by {
            let j = lemma_bag_contains(ws, vs, i);
        }
    }
}

/// The result scale of `num_sum`: at least every numeric's scale, and either 0 or one of them.
proof fn lemma_num_max_scale_char(vs: Seq<Val>)
    ensures
        forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale <= num_max_scale(vs)),
        num_max_scale(vs) == 0 || exists|i: int| 0 <= i < vs.len() && (#[trigger] vs[i] matches Val::Num { coeff, scale } && scale == num_max_scale(vs)),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        lemma_num_max_scale_char(d);
        assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale <= num_max_scale(vs)) by {
            if i < d.len() {
                assert(d[i] == vs[i]);
            }
        }
        if num_max_scale(vs) != 0 {
            if num_max_scale(vs) == num_max_scale(d) {
                let i = choose|i: int| 0 <= i < d.len() && (#[trigger] d[i] matches Val::Num { coeff, scale } && scale == num_max_scale(d));
                assert(vs[i] == d[i]);
            } else {
                assert(vs[vs.len() - 1] == vs.last());
            }
        }
    }
}

proof fn lemma_num_max_scale_bag(vs: Seq<Val>, ws: Seq<Val>)
    requires vs.to_multiset() == ws.to_multiset(),
    ensures num_max_scale(vs) == num_max_scale(ws),
{
    lemma_num_max_scale_char(vs);
    lemma_num_max_scale_char(ws);
    if num_max_scale(ws) != 0 {
        let i = choose|i: int| 0 <= i < ws.len() && (#[trigger] ws[i] matches Val::Num { coeff, scale } && scale == num_max_scale(ws));
        let j = lemma_bag_contains(vs, ws, i);
        assert(vs[j] matches Val::Num { coeff, scale } && scale <= num_max_scale(vs));
    }
    if num_max_scale(vs) != 0 {
        let i = choose|i: int| 0 <= i < vs.len() && (#[trigger] vs[i] matches Val::Num { coeff, scale } && scale == num_max_scale(vs));
        let j = lemma_bag_contains(ws, vs, i);
        assert(ws[j] matches Val::Num { coeff, scale } && scale <= num_max_scale(ws));
    }
}

/// The exact numeric sum depends only on the multiset of values.
pub proof fn lemma_num_sum_bag(vs: Seq<Val>, ws: Seq<Val>)
    requires vs.to_multiset() == ws.to_multiset(),
    ensures num_sum(vs) == num_sum(ws),
{
    lemma_num_max_scale_bag(vs, ws);
    let t = num_max_scale(vs);
    lemma_num_sum_at(vs, t);
    lemma_num_sum_at(ws, t);
    lemma_align_same(num_sum(vs).0, t);
    lemma_align_same(num_sum(ws).0, t);
    lemma_num_sum_at_by(vs, t);
    lemma_num_sum_at_by(ws, t);
    lemma_sum_by_bag(vs, ws, num_term(t));
}

// ------------------------------------------------------------------------------------- MIN and MAX

/// `v` is not after `m` in the extremum's order (at most `m` for MAX, at least for MIN).
pub open spec fn extreme_le(max: bool, v: Val, m: Val) -> bool {
    match compare(v, m) {
        Some(c) => if max { c <= 0 } else { c >= 0 },
        None => false,
    }
}

/// `m` is an extremum of the non-NULL values of `vs`.
pub open spec fn is_extreme(max: bool, vs: Seq<Val>, m: Val) -> bool {
    &&& !(m is Null)
    &&& vs.contains(m)
    &&& forall|i: int| 0 <= i < vs.len() && !(vs[i] is Null) ==> extreme_le(max, #[trigger] vs[i], m)
}

pub open spec fn all_null(vs: Seq<Val>) -> bool {
    forall|i: int| 0 <= i < vs.len() ==> #[trigger] vs[i] is Null
}

/// On ordered values the running extremum never raises and is NULL exactly when every value is, otherwise an
/// extremum of the values.
pub proof fn lemma_extremum_char(max: bool, vs: Seq<Val>)
    requires vals_ordered(vs),
    ensures
        extremum(max, vs) is Ok,
        (extremum(max, vs)->Ok_0 is Null) == all_null(vs),
        !(extremum(max, vs)->Ok_0 is Null) ==> is_extreme(max, vs, extremum(max, vs)->Ok_0),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        let n = vs.len() - 1;
        assert(vs[n] == vs.last());
        assert forall|i: int| 0 <= i < d.len() implies d[i] == #[trigger] vs[i] by {}
        assert(vals_ordered(d));
        lemma_extremum_char(max, d);
        let acc = extremum(max, d)->Ok_0;
        let v = vs.last();
        if v is Null {
            if !(acc is Null) {
                assert(d.contains(acc));
                let k = choose|k: int| 0 <= k < d.len() && d[k] == acc;
                assert(vs[k] == acc);
            }
        } else if acc is Null {
            lemma_compare_antisym(v, v);
            assert(vs[n] == v);
            assert forall|i: int| 0 <= i < vs.len() && !(vs[i] is Null) implies extreme_le(max, #[trigger] vs[i], v) by {
                if i < n {
                    assert(d[i] == vs[i]);
                }
            }
        } else {
            assert(d.contains(acc));
            let k = choose|k: int| 0 <= k < d.len() && d[k] == acc;
            assert(vs[k] == acc);
            lemma_compare_antisym(v, acc);
            let c = compare(v, acc)->0;
            if extremum_better(max, c) {
                assert forall|i: int| 0 <= i < vs.len() && !(vs[i] is Null) implies extreme_le(max, #[trigger] vs[i], v) by {
                    if i < n {
                        assert(d[i] == vs[i]);
                        assert(extreme_le(max, vs[i], acc));
                        lemma_compare_antisym(vs[i], acc);
                        lemma_compare_antisym(vs[i], v);
                        if max {
                            lemma_compare_trans(vs[i], acc, v);
                        } else {
                            lemma_compare_antisym(acc, vs[i]);
                            lemma_compare_antisym(v, vs[i]);
                            lemma_compare_trans(v, acc, vs[i]);
                        }
                    } else {
                        lemma_compare_antisym(v, v);
                    }
                }
            } else {
                assert forall|i: int| 0 <= i < vs.len() && !(vs[i] is Null) implies extreme_le(max, #[trigger] vs[i], acc) by {
                    if i < n {
                        assert(d[i] == vs[i]);
                    }
                }
            }
        }
        if all_null(vs) {
            assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] is Null by {}
        }
        if !all_null(vs) && v is Null {
            let i = choose|i: int| 0 <= i < vs.len() && !(#[trigger] vs[i] is Null);
            assert(d[i] == vs[i]);
        }
    }
}

/// On exact ordered values with one multiset, MIN and MAX agree.
pub proof fn lemma_extremum_bag(max: bool, vs: Seq<Val>, ws: Seq<Val>)
    requires vs.to_multiset() == ws.to_multiset(), vals_exact(vs), vals_ordered(vs),
    ensures extremum(max, vs) == extremum(max, ws),
{
    lemma_order_free_bag(Agg::Min(crate::spec::ast::Expr::Col(0)), vs, ws);
    lemma_extremum_char(max, vs);
    lemma_extremum_char(max, ws);
    let (m1, m2) = (extremum(max, vs)->Ok_0, extremum(max, ws)->Ok_0);
    if all_null(vs) != all_null(ws) {
        if all_null(vs) {
            let i = choose|i: int| 0 <= i < ws.len() && !(#[trigger] ws[i] is Null);
            let j = lemma_bag_contains(vs, ws, i);
        } else {
            let i = choose|i: int| 0 <= i < vs.len() && !(#[trigger] vs[i] is Null);
            let j = lemma_bag_contains(ws, vs, i);
        }
    }
    if !all_null(vs) && !all_null(ws) {
        let i1 = choose|i: int| 0 <= i < vs.len() && vs[i] == m1;
        let i2 = choose|i: int| 0 <= i < ws.len() && ws[i] == m2;
        let j1 = lemma_bag_contains(ws, vs, i1);
        let j2 = lemma_bag_contains(vs, ws, i2);
        assert(extreme_le(max, ws[j1], m2));
        assert(extreme_le(max, vs[j2], m1));
        lemma_compare_antisym(m1, m2);
        assert(val_not_distinct(m1, m2));
        assert(vs[i1] == m1 && vs[j2] == m2);
    }
}

// ------------------------------------------------------------------------------------- aggregate values

/// L4 (H2): an order-free aggregate has the same value over equal multisets of arguments.
pub proof fn lemma_agg_value_bag(a: Agg, vs: Seq<Val>, ws: Seq<Val>)
    requires vs.to_multiset() == ws.to_multiset(), agg_order_free(a, vs),
    ensures agg_value(a, vs) == agg_value(a, ws),
    decreases a,
{
    vs.to_multiset_ensures();
    ws.to_multiset_ensures();
    lemma_count_sum(vs);
    lemma_count_sum(ws);
    lemma_sum_by_bag(vs, ws, non_null_term());
    match a {
        Agg::CountStar => {},
        Agg::Count(_) => {},
        Agg::Sum { kind, arg } => {
            lemma_all_of_kind_bag(kind, vs, ws);
            lemma_int_sum_by(vs);
            lemma_int_sum_by(ws);
            lemma_sum_by_bag(vs, ws, int_term());
            lemma_num_sum_bag(vs, ws);
        },
        Agg::Avg { kind, arg } => {
            lemma_all_of_kind_bag(kind, vs, ws);
            lemma_int_sum_by(vs);
            lemma_int_sum_by(ws);
            lemma_sum_by_bag(vs, ws, int_term());
            lemma_num_sum_bag(vs, ws);
        },
        Agg::Min(_) => lemma_extremum_bag(false, vs, ws),
        Agg::Max(_) => lemma_extremum_bag(true, vs, ws),
        Agg::DistinctAgg(inner) => {
            lemma_distinct_vals_bag(vs, ws);
            lemma_distinct_vals_sub_contains(vs);
            lemma_order_free_subset(*inner, vs, distinct_vals(vs));
            lemma_agg_value_bag(*inner, distinct_vals(vs), distinct_vals(ws));
        },
    }
}

/// Every value of `distinct_vals(vs)` is a value of `vs`.
proof fn lemma_distinct_vals_sub_contains(vs: Seq<Val>)
    ensures forall|j: int| 0 <= j < distinct_vals(vs).len() ==> vs.contains(#[trigger] distinct_vals(vs)[j]),
{
    crate::bridge::relation::lemma_distinct_vals_sub(vs);
}

/// L4 (H2): the aggregate row of a group is the same over equal multisets of argument rows, when every
/// aggregate is order-free.
pub proof fn lemma_agg_row_bag(aggs: Seq<Agg>, args: Seq<Row>, args2: Seq<Row>)
    requires args.to_multiset() == args2.to_multiset(), aggs_order_free(aggs, args),
    ensures agg_row(aggs, args) == agg_row(aggs, args2),
{
    lemma_agg_row(aggs, args);
    lemma_agg_row(aggs, args2);
    let (r1, r2) = (agg_value_results(aggs, args), agg_value_results(aggs, args2));
    assert forall|j: int| 0 <= j < aggs.len() implies #[trigger] r1[j] == r2[j] by {
        lemma_map_bag(args, args2, |r: Row| r[j]);
        assert(column(args, j) =~= args.map_values(|r: Row| r[j]));
        assert(column(args2, j) =~= args2.map_values(|r: Row| r[j]));
        assert(agg_order_free(aggs[j], column(args, j)));
        lemma_agg_value_bag(aggs[j], column(args, j), column(args2, j));
    }
    assert(r1 =~= r2);
}

} // verus!
