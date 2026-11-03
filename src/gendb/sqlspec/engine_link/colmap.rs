//! L5 column maps: one type for the column bookkeeping of reordered and pruned plans (engine toolkit; nothing here
//! names a query, a table or a column).
//!
//! A physical plan may hold its rows' columns in another order than the canonical denotation (a join tree the
//! planner reordered) or hold only some of them (pruning). A `ColMap` `m` says how: the physical row `y` stands for
//! the canonical row `map_row(m, y)`, whose position `k` is `y[m[k]]` (`link::query::proj`). The same map rewrites
//! the column references of a condition so that it can be evaluated on physical rows (`engine_link::remap`).
//!
//! Row level (this module):
//! - `id_map(w)`: rows of width `w` are their own view;
//! - `map_then(m1, m2)`: viewing through `m1` and then through `m2` is one view (`lemma_map_then`);
//! - `beside(m1, w1, m2)`: a concatenated physical row viewed part by part; products of viewed inputs
//!   (`lemma_product_map`);
//! - `swap_map(wa, wb)`: the product of `b` and `a` viewed by the swap is the product of `a` and `b` as a bag
//!   (`lemma_product_swap`, join commutation); association needs no map (`link::join::lemma_product_assoc`);
//! - conditions through a view (`lemma_keep_through_map`) and bag equality through a view (`lemma_map_rows_bag`).
//!
//! A join-tree reordering is proved by composing these steps (`engine_pins::join_reorder` shows a three-input one).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::*;
use crate::link::query::{proj, proj_all};
use crate::link::source::{compose_cols, lemma_proj_all_compose};
use crate::link::join::{keep, shift, lemma_keep_map, lemma_keep_ext, lemma_proj_concat, lemma_proj_product};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::engine_link::bag::{lemma_concat_bag, lemma_map_bag};

verus! {

// ------------------------------------------------------------------------------------- the type and its views

/// Physical row `y` stands for the canonical row whose position `k` is `y[m[k]]`.
pub type ColMap = Seq<nat>;

/// The canonical row a physical row stands for.
pub open spec fn map_row(m: ColMap, y: Row) -> Row {
    proj(y, m)
}

/// `map_row` of every physical row, in order.
pub open spec fn map_rows(m: ColMap, ys: Seq<Row>) -> Seq<Row> {
    proj_all(ys, m)
}

/// Every entry of `m` is a position of rows of width `w`.
pub open spec fn map_into(m: ColMap, w: nat) -> bool {
    forall|k: int| 0 <= k < m.len() ==> #[trigger] m[k] < w
}

/// Every row has `w` columns.
pub open spec fn width_of(rows: Seq<Row>, w: nat) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == w
}

/// Positions and values of a viewed row.
pub proof fn lemma_map_row_index(m: ColMap, y: Row)
    ensures
        map_row(m, y).len() == m.len(),
        forall|k: int| 0 <= k < m.len() ==> #[trigger] map_row(m, y)[k] == y[m[k] as int],
{
}

/// Length and rows of viewed rows, by index; their width is the map's length.
pub proof fn lemma_map_rows_index(m: ColMap, ys: Seq<Row>)
    ensures
        map_rows(m, ys).len() == ys.len(),
        forall|i: int| 0 <= i < ys.len() ==> #[trigger] map_rows(m, ys)[i] == map_row(m, ys[i]),
        width_of(map_rows(m, ys), m.len()),
{
}

// ------------------------------------------------------------------------------------- identity and composition

/// The identity view of rows of width `w`.
pub open spec fn id_map(w: nat) -> ColMap {
    Seq::new(w, |k: int| k as nat)
}

/// A row viewed by the identity of its width is itself.
pub proof fn lemma_id_map_row(y: Row)
    ensures map_into(id_map(y.len()), y.len()), map_row(id_map(y.len()), y) == y,
{
    assert(map_row(id_map(y.len()), y) =~= y);
}

/// Rows of width `w` viewed by the identity are themselves.
pub proof fn lemma_id_map(ys: Seq<Row>, w: nat)
    requires width_of(ys, w),
    ensures map_into(id_map(w), w), map_rows(id_map(w), ys) == ys,
{
    assert forall|i: int| 0 <= i < ys.len() implies #[trigger] map_rows(id_map(w), ys)[i] == ys[i] by {
        lemma_id_map_row(ys[i]);
    }
    assert(map_rows(id_map(w), ys) =~= ys);
}

/// View through `m1`, then through `m2` (positions of `m2` address the rows `m1` yields).
pub open spec fn map_then(m1: ColMap, m2: ColMap) -> ColMap {
    compose_cols(m1, m2)
}

/// Two views in a row are one view.
pub proof fn lemma_map_then(m1: ColMap, m2: ColMap, ys: Seq<Row>)
    requires map_into(m2, m1.len()),
    ensures
        map_rows(m2, map_rows(m1, ys)) == map_rows(map_then(m1, m2), ys),
        forall|i: int| 0 <= i < ys.len() ==> #[trigger] map_row(m2, map_row(m1, ys[i])) == map_row(map_then(m1, m2), ys[i]),
{
    lemma_proj_all_compose(ys, m1, m2);
    assert forall|i: int| 0 <= i < ys.len() implies #[trigger] map_row(m2, map_row(m1, ys[i])) == map_row(map_then(m1, m2), ys[i]) by {
        assert(map_rows(m2, map_rows(m1, ys))[i] == map_rows(map_then(m1, m2), ys)[i]);
    }
}

/// A composed view stays inside the physical rows.
pub proof fn lemma_map_then_into(m1: ColMap, m2: ColMap, w: nat)
    requires map_into(m1, w), map_into(m2, m1.len()),
    ensures map_into(map_then(m1, m2), w),
{
    assert forall|k: int| 0 <= k < map_then(m1, m2).len() implies #[trigger] map_then(m1, m2)[k] < w by {
        assert(m2[k] < m1.len());
    }
}

// ------------------------------------------------------------------------------------- side by side: products

/// A concatenated physical row `y1 ++ y2` (`|y1| = w1`) viewed by `m1` on its first part and `m2` on its second.
pub open spec fn beside(m1: ColMap, w1: nat, m2: ColMap) -> ColMap {
    m1 + shift(m2, w1)
}

/// The side-by-side view of a concatenated row is the concatenation of the views.
pub proof fn lemma_beside_row(m1: ColMap, m2: ColMap, y1: Row, y2: Row)
    requires map_into(m1, y1.len()), map_into(m2, y2.len()),
    ensures map_row(beside(m1, y1.len(), m2), y1 + y2) == map_row(m1, y1) + map_row(m2, y2),
{
    lemma_proj_concat(y1, y2, m1, m2);
}

/// The side-by-side view stays inside the concatenated rows.
pub proof fn lemma_beside_into(m1: ColMap, w1: nat, m2: ColMap, w2: nat)
    requires map_into(m1, w1), map_into(m2, w2),
    ensures map_into(beside(m1, w1, m2), w1 + w2), beside(m1, w1, m2).len() == m1.len() + m2.len(),
{
    let b = beside(m1, w1, m2);
    assert forall|k: int| 0 <= k < b.len() implies #[trigger] b[k] < w1 + w2 by {
        if k >= m1.len() {
            assert(b[k] == m2[k - m1.len()] + w1);
        }
    }
}

/// A product of rows of widths `wa` and `wb` has rows of width `wa + wb`.
pub proof fn lemma_product_width(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires width_of(a, wa), width_of(b, wb),
    ensures width_of(product_rows(a, b), wa + wb),
{
    lemma_product_rows_elems(a, b);
    let p = product_rows(a, b);
    assert forall|k: int| 0 <= k < p.len() implies (#[trigger] p[k]).len() == wa + wb by {
        assert(is_concat(p[k], a, b));
        let (i, j) = choose|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && p[k] == #[trigger] a[i] + #[trigger] b[j];
        assert(a[i].len() == wa && b[j].len() == wb);
    }
}

/// The product of viewed inputs is the viewed product (`link::join::lemma_proj_product`).
pub proof fn lemma_product_map(a: Seq<Row>, b: Seq<Row>, m1: ColMap, wa: nat, m2: ColMap, wb: nat)
    requires width_of(a, wa), width_of(b, wb), map_into(m1, wa), map_into(m2, wb),
    ensures map_rows(beside(m1, wa, m2), product_rows(a, b)) == product_rows(map_rows(m1, a), map_rows(m2, b)),
{
    lemma_proj_product(a, b, m1, m2, wa, wb);
}

// ------------------------------------------------------------------------------------- the swap: commutation

/// The view of `x ++ y` (`|x| = wa`, `|y| = wb`) in the swapped physical row `y ++ x`.
pub open spec fn swap_map(wa: nat, wb: nat) -> ColMap {
    Seq::new(wa + wb, |k: int| if k < wa { (k + wb) as nat } else { (k - wa) as nat })
}

/// The swap view of a swapped row is the row in canonical order.
pub proof fn lemma_swap_row(x: Row, y: Row)
    ensures
        map_into(swap_map(x.len(), y.len()), y.len() + x.len()),
        map_row(swap_map(x.len(), y.len()), y + x) == x + y,
{
    assert(map_row(swap_map(x.len(), y.len()), y + x) =~= x + y);
}

/// Every row of `b` with `x` appended: the product of `b` and the one row `x`.
proof fn lemma_product_single_right(b: Seq<Row>, x: Row)
    ensures product_rows(b, seq![x]) == b.map_values(|y: Row| y + x),
    decreases b.len(),
{
    if b.len() > 0 {
        let bi = b.drop_last();
        lemma_product_single_right(bi, x);
        assert(seq![x].map_values(|r: Row| b.last() + r) =~= seq![b.last() + x]);
        assert(b.map_values(|y: Row| y + x) =~= bi.map_values(|y: Row| y + x).push(b.last() + x));
    } else {
        assert(b.map_values(|y: Row| y + x) =~= Seq::<Row>::empty());
    }
}

/// As bags, a product distributes over a concatenated right input.
proof fn lemma_product_right_concat_bag(b: Seq<Row>, c1: Seq<Row>, c2: Seq<Row>)
    ensures
        product_rows(b, c1 + c2).to_multiset() == product_rows(b, c1).to_multiset().add(product_rows(b, c2).to_multiset()),
    decreases b.len(),
{
    if b.len() == 0 {
        let e = Seq::<Row>::empty();
        lemma_concat_bag(e, e);
        assert(e + e =~= e);
    } else {
        let bi = b.drop_last();
        let y = b.last();
        lemma_product_right_concat_bag(bi, c1, c2);
        let (m1, m2) = (c1.map_values(|r: Row| y + r), c2.map_values(|r: Row| y + r));
        assert((c1 + c2).map_values(|r: Row| y + r) =~= m1 + m2);
        lemma_concat_bag(product_rows(bi, c1 + c2), m1 + m2);
        lemma_concat_bag(m1, m2);
        lemma_concat_bag(product_rows(bi, c1), m1);
        lemma_concat_bag(product_rows(bi, c2), m2);
        let (p1, p2) = (product_rows(bi, c1).to_multiset(), product_rows(bi, c2).to_multiset());
        let (q1, q2) = (m1.to_multiset(), m2.to_multiset());
        assert(p1.add(p2).add(q1.add(q2)) =~= p1.add(q1).add(p2.add(q2)));
    }
}

/// Join commutation: as bags, the product of `a` and `b` is the product of `b` and `a` viewed by the swap.
pub proof fn lemma_product_swap(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires width_of(a, wa), width_of(b, wb),
    ensures
        map_into(swap_map(wa, wb), wb + wa),
        product_rows(a, b).to_multiset() == map_rows(swap_map(wa, wb), product_rows(b, a)).to_multiset(),
    decreases a.len(),
{
    let s = swap_map(wa, wb);
    assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] < wb + wa by {}
    if a.len() == 0 {
        assert(a =~= Seq::<Row>::empty());
        lemma_product_empty_right(b);
        assert(map_rows(s, product_rows(b, a)) =~= Seq::<Row>::empty());
    } else {
        let ai = a.drop_last();
        let x = a.last();
        assert(width_of(ai, wa)) by {
            assert forall|i: int| 0 <= i < ai.len() implies (#[trigger] ai[i]).len() == wa by {
                assert(ai[i] == a[i]);
            }
        }
        assert(x.len() == wa) by {
            assert(a[a.len() - 1] == x);
        }
        lemma_product_swap(ai, b, wa, wb);
        // canonical side: the rows of `ai`, then `x` with every row of `b`
        let left = b.map_values(|y: Row| x + y);
        assert(product_rows(a, b) == product_rows(ai, b) + b.map_values(|r: Row| a.last() + r));
        assert(b.map_values(|r: Row| a.last() + r) =~= left);
        lemma_concat_bag(product_rows(ai, b), left);
        // physical side: `b` with the rows of `ai`, plus `b` with `x`
        assert(a =~= ai + seq![x]);
        lemma_product_right_concat_bag(b, ai, seq![x]);
        lemma_product_single_right(b, x);
        let right = b.map_values(|y: Row| y + x);
        assert(map_rows(s, right) =~= left) by {
            assert forall|j: int| 0 <= j < b.len() implies #[trigger] map_rows(s, right)[j] == left[j] by {
                lemma_swap_row(x, b[j]);
            }
        }
        // the view distributes over the bag sum
        lemma_map_rows_bag_add(s, product_rows(b, a), product_rows(b, ai), right);
    }
}

/// The product with an empty right input is empty.
proof fn lemma_product_empty_right(b: Seq<Row>)
    ensures product_rows(b, Seq::<Row>::empty()) == Seq::<Row>::empty(),
    decreases b.len(),
{
    if b.len() > 0 {
        lemma_product_empty_right(b.drop_last());
        assert(Seq::<Row>::empty().map_values(|r: Row| b.last() + r) =~= Seq::<Row>::empty());
        assert(Seq::<Row>::empty() + Seq::<Row>::empty() =~= Seq::<Row>::empty());
    }
}

/// A view of rows whose bag is the sum of two bags is the sum of the viewed bags.
proof fn lemma_map_rows_bag_add(m: ColMap, s: Seq<Row>, s1: Seq<Row>, s2: Seq<Row>)
    requires s.to_multiset() == s1.to_multiset().add(s2.to_multiset()),
    ensures map_rows(m, s).to_multiset() == map_rows(m, s1).to_multiset().add(map_rows(m, s2).to_multiset()),
{
    let v = |r: Row| proj(r, m);
    lemma_concat_bag(s1, s2);
    lemma_map_bag(s, s1 + s2, v);
    assert(map_rows(m, s) =~= s.map_values(v));
    assert(map_rows(m, s1 + s2) =~= (s1 + s2).map_values(v));
    assert(map_rows(m, s1 + s2) =~= map_rows(m, s1) + map_rows(m, s2));
    lemma_concat_bag(map_rows(m, s1), map_rows(m, s2));
}

// ------------------------------------------------------------------------------------- conditions and bags

/// A condition on viewed rows is the condition on the view, kept on the physical rows and then viewed.
pub proof fn lemma_keep_through_map(m: ColMap, ys: Seq<Row>, f: spec_fn(Row) -> bool)
    ensures keep(map_rows(m, ys), f) == map_rows(m, keep(ys, |y: Row| f(map_row(m, y)))),
{
    let v = |r: Row| proj(r, m);
    lemma_keep_map(ys, v, f);
    lemma_keep_ext(ys, |y: Row| f(v(y)), |y: Row| f(map_row(m, y)));
    assert(map_rows(m, ys) =~= ys.map_values(v));
    let kept = keep(ys, |y: Row| f(map_row(m, y)));
    assert(map_rows(m, kept) =~= kept.map_values(v));
}

/// Bag-equal physical rows have bag-equal views.
pub proof fn lemma_map_rows_bag(m: ColMap, s: Seq<Row>, t: Seq<Row>)
    requires s.to_multiset() == t.to_multiset(),
    ensures map_rows(m, s).to_multiset() == map_rows(m, t).to_multiset(),
{
    let v = |r: Row| proj(r, m);
    lemma_map_bag(s, t, v);
    assert(map_rows(m, s) =~= s.map_values(v));
    assert(map_rows(m, t) =~= t.map_values(v));
}

} // verus!
