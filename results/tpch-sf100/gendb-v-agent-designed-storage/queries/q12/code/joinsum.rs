//! Q12's group sums over the join `orders x lineitem` are the scan model's per-line counts.
//!
//! The normal form (`sql::q12_g`) ranges over the product `xs = orel x lrel` of the stored relations. Its group sum of
//! ship-mode entry `d` and aggregate `a` (0: high, 1: low priority) is a sum of per-row terms (`link::join`):
//! exchanged to right-major order it is, per lineitem row `y`, the sum over the orders rows `x` of the term of
//! `x ++ y` (`lemma_sum_of_product_swap`). Both relations are permutations of the stored rows (`bind::lrows`,
//! `bind::orows`), so both sums may run in storage order. For stored lineitem row `j` the term of stored orders row
//! `p` is 1 exactly when the line qualifies, has mode `d`, `p` holds the line's order key and its priority belongs
//! to `a` (`lemma_pair_term`); with o_orderkey distinct at most one `p` matches, `rpos(l_orderkey)`, so the inner sum
//! is `model::lval` (`lemma_inner`), and the outer sum is `model::cnt` over every stored lineitem row
//! (`lemma_gsum_cnt`).
//!
//! Every qualifying row adds 1 to exactly one of the two sums, so a group's count is the sum of its two sums
//! (`lemma_count_sums`); a non-empty group is some ship-mode entry's group (`lemma_keys_complete`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::*;
use crate::spec::relation::*;
use crate::link::query::*;
use crate::link::join::*;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::stores::facts::declaration::*;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use super::model::*;
use super::sql::*;
use super::bind::*;

verus! {

// ------------------------------------------------------------------------------------------------ definitions

/// Ship-mode dictionary entry `d` as a group key.
pub open spec fn key_d(mo: Seq<u64>, my: Seq<u8>, d: int) -> Row {
    seq![Val::Text(text_of(mo, my, d))]
}

/// The scan window `w` decides the bound parameters `prm` on dictionary entries: the receipt-date window is
/// `prm`'s, a ship-mode entry is selected exactly when its text is `$1` or `$2`, and a priority entry is high
/// exactly when its text is `'1-URGENT'` or `'2-HIGH'`.
pub open spec fn win_matches(w: Win, prm: Prm, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>) -> bool {
    &&& w.lo as int == prm.lo
    &&& w.hi as int == prm.hi
    &&& forall|e: int| 0 <= e < mo.len() - 1 ==>
            ((e == w.s0 || e == w.s1) <==> (#[trigger] text_of(mo, my, e) == prm.p0 || text_of(mo, my, e) == prm.p1))
    &&& forall|e: int| 0 <= e < po.len() - 1 ==>
            (phigh(w, e) <==> (#[trigger] text_of(po, py, e) == urgent() || text_of(po, py, e) == high2()))
}

/// The stored rows `o` (orders) and `l` (lineitem) decode as the model's columns (`bind::lemma_orders_cols`,
/// `bind::lemma_lineitem_cols`), with their stored widths 7 and 15.
pub open spec fn rows_model(c: Cols, o: Seq<Row>, l: Seq<Row>, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>) -> bool {
    &&& o.len() == c.n_o
    &&& l.len() == c.n_l
    &&& forall|p: int| 0 <= p < c.n_o ==> {
        &&& (#[trigger] o[p]).len() == 7
        &&& o[p][0] == Val::Int(okey(c, p))
        &&& 0 <= oprio(c, p) < po.len() - 1
        &&& o[p][5] == Val::Text(text_of(po, py, oprio(c, p)))
    }
    &&& forall|j: int| 0 <= j < c.n_l ==> {
        &&& (#[trigger] l[j]).len() == 15
        &&& l[j][0] == Val::Int(lkey(c, j))
        &&& l[j][10] == Val::Date(lship(c, j))
        &&& l[j][11] == Val::Date(lcmt(c, j))
        &&& l[j][12] == Val::Date(lrcp(c, j))
        &&& 0 <= lmode(c, j) < mo.len() - 1
        &&& l[j][14] == Val::Text(text_of(mo, my, lmode(c, j)))
    }
}

/// The term of stored orders row `p` and stored lineitem row `j` in the model.
pub open spec fn pair_val(c: Cols, w: Win, a: int, d: int, p: int, j: int) -> int {
    if lqual(c, w, j) && lmode(c, j) == d && okey(c, p) == lkey(c, j) && agg_takes(w, a, oprio(c, p)) { 1 } else { 0 }
}

/// The per-row term of aggregate `a` of group `k` (`link::join::sum_term`) for the Q12 normal form.
pub open spec fn q12_term(prm: Prm, k: Row, a: int) -> spec_fn(Row) -> int {
    sum_term(q12_g(prm), k, a)
}

/// The inner sum of the right-major product: over the rows `xs` (orders), the term of `x ++ y`.
pub open spec fn inner_sum(xs: Seq<Row>, f: spec_fn(Row) -> int, y: Row) -> int {
    sum_of(xs, |x: Row| f(x + y))
}

// ------------------------------------------------------------------------------------------------ one pair

/// Positions of a joined stored row `o ++ l` (7 + 15 columns).
proof fn lemma_joined_at(o: Row, l: Row)
    requires o.len() == 7, l.len() == 15,
    ensures ({
        let x = o + l;
        &&& x[0] == o[0]
        &&& x[5] == o[5]
        &&& x[7] == l[0]
        &&& x[17] == l[10]
        &&& x[18] == l[11]
        &&& x[19] == l[12]
        &&& x[21] == l[14]
    }),
{
}

/// The WHERE condition of the normal form on stored rows `p`, `j`.
proof fn lemma_pair_qual(c: Cols, w: Win, prm: Prm, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>,
    o: Seq<Row>, l: Seq<Row>, p: int, j: int)
    requires
        rows_model(c, o, l, po, py, mo, my),
        win_matches(w, prm, po, py, mo, my),
        0 <= p < c.n_o,
        0 <= j < c.n_l,
    ensures
        q12_qual(prm, o[p] + l[j]) == (lqual(c, w, j) && okey(c, p) == lkey(c, j)),
{
    let x = o[p] + l[j];
    lemma_joined_at(o[p], l[j]);
    let e = lmode(c, j);
    assert(text_of(mo, my, e) == prm.p0 || text_of(mo, my, e) == prm.p1 <==> (e == w.s0 || e == w.s1));
    assert((x[21] == Val::Text(prm.p0)) == (text_of(mo, my, e) == prm.p0));
    assert((x[21] == Val::Text(prm.p1)) == (text_of(mo, my, e) == prm.p1));
    assert((x[0] == x[7]) == (okey(c, p) == lkey(c, j)));
    assert(day_of(x[17]) == lship(c, j));
    assert(day_of(x[18]) == lcmt(c, j));
    assert(day_of(x[19]) == lrcp(c, j));
}

/// The GROUP BY key of the normal form on stored rows `p`, `j` is entry `d`'s key exactly when the line has mode `d`.
proof fn lemma_pair_key(c: Cols, prm: Prm, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>,
    o: Seq<Row>, l: Seq<Row>, d: int, p: int, j: int)
    requires
        rows_model(c, o, l, po, py, mo, my),
        dict_ok(mo, my),
        0 <= d < mo.len() - 1,
        0 <= p < c.n_o,
        0 <= j < c.n_l,
    ensures
        ((q12_g(prm).key)(o[p] + l[j]) == key_d(mo, my, d)) == (lmode(c, j) == d),
{
    let x = o[p] + l[j];
    lemma_joined_at(o[p], l[j]);
    let e = lmode(c, j);
    if e == d {
        assert(seq![x[21]] =~= key_d(mo, my, d));
    } else {
        lemma_dict_distinct(mo, my, mo.len() - 1, e, d);
        assert(seq![x[21]][0] != key_d(mo, my, d)[0]);
    }
}

/// The SUM argument of aggregate `a` on stored rows `p`, `j` is 1 exactly when the order's priority belongs to `a`.
proof fn lemma_pair_arg(c: Cols, w: Win, prm: Prm, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>,
    o: Seq<Row>, l: Seq<Row>, a: int, p: int, j: int)
    requires
        rows_model(c, o, l, po, py, mo, my),
        win_matches(w, prm, po, py, mo, my),
        a == 0 || a == 1,
        0 <= p < c.n_o,
        0 <= j < c.n_l,
    ensures
        (q12_g(prm).arg)(a, o[p] + l[j]) == if agg_takes(w, a, oprio(c, p)) { 1int } else { 0int },
{
    let x = o[p] + l[j];
    lemma_joined_at(o[p], l[j]);
    let e = oprio(c, p);
    assert(phigh(w, e) <==> (text_of(po, py, e) == urgent() || text_of(po, py, e) == high2()));
    assert(prio_high(x[5]) == phigh(w, e));
}

/// The normal form's term of aggregate `a` of entry `d`'s group on the joined stored rows `p`, `j`.
pub proof fn lemma_pair_term(c: Cols, w: Win, prm: Prm, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>,
    o: Seq<Row>, l: Seq<Row>, a: int, d: int, p: int, j: int)
    requires
        rows_model(c, o, l, po, py, mo, my),
        win_matches(w, prm, po, py, mo, my),
        dict_ok(mo, my),
        a == 0 || a == 1,
        0 <= d < mo.len() - 1,
        0 <= p < c.n_o,
        0 <= j < c.n_l,
    ensures
        q12_term(prm, key_d(mo, my, d), a)(o[p] + l[j]) == pair_val(c, w, a, d, p, j),
{
    lemma_pair_qual(c, w, prm, po, py, mo, my, o, l, p, j);
    lemma_pair_key(c, prm, po, py, mo, my, o, l, d, p, j);
    lemma_pair_arg(c, w, prm, po, py, mo, my, o, l, a, p, j);
}

// ------------------------------------------------------------------------------------------------ inner sums

/// Over the stored orders rows, the terms with lineitem row `j` sum to the model's `lval`: only the row of the
/// line's order key (`rpos`) can contribute.
pub proof fn lemma_inner(c: Cols, w: Win, prm: Prm, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>,
    o: Seq<Row>, l: Seq<Row>, a: int, d: int, j: int)
    requires
        rows_model(c, o, l, po, py, mo, my),
        win_matches(w, prm, po, py, mo, my),
        dict_ok(mo, my),
        keys_distinct(c),
        a == 0 || a == 1,
        0 <= d < mo.len() - 1,
        0 <= j < c.n_l,
    ensures
        inner_sum(o, q12_term(prm, key_d(mo, my, d), a), l[j]) == lval(c, w, a, d, j),
{
    let f = q12_term(prm, key_d(mo, my, d), a);
    let y = l[j];
    let h = |x: Row| f(x + y);
    let k = lkey(c, j);
    let r = rpos(c, k);
    lemma_rpos_bound(c, k);
    assert forall|p: int| 0 <= p < c.n_o implies #[trigger] h(o[p]) == pair_val(c, w, a, d, p, j) by {
        lemma_pair_term(c, w, prm, po, py, mo, my, o, l, a, d, p, j);
    }
    if r < c.n_o {
        // Every other row holds another key.
        let rest = o.remove(r);
        assert forall|i: int| 0 <= i < rest.len() implies h(#[trigger] rest[i]) == 0 by {
            let p = if i < r { i } else { i + 1 };
            assert(rest[i] == o[p]);
            assert(okey(c, p) != okey(c, r));
        }
        lemma_sum_of_zero(rest, h);
        lemma_sum_of_remove(o, r, h);
    } else {
        assert forall|i: int| 0 <= i < o.len() implies h(#[trigger] o[i]) == 0 by {
            if okey(c, i) == k {
                lemma_rpos_first(c, k, i);
            }
        }
        lemma_sum_of_zero(o, h);
    }
}

// ------------------------------------------------------------------------------------------------ outer sums

/// Over the first `n` stored lineitem rows, the inner sums add up to the model's count.
proof fn lemma_outer_prefix(c: Cols, w: Win, prm: Prm, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>,
    o: Seq<Row>, l: Seq<Row>, a: int, d: int, n: int)
    requires
        rows_model(c, o, l, po, py, mo, my),
        win_matches(w, prm, po, py, mo, my),
        dict_ok(mo, my),
        keys_distinct(c),
        a == 0 || a == 1,
        0 <= d < mo.len() - 1,
        0 <= n <= c.n_l,
    ensures
        sum_of(l.subrange(0, n), |y: Row| inner_sum(o, q12_term(prm, key_d(mo, my, d), a), y)) == cnt(c, w, a, d, 0, n),
    decreases n,
{
    let f = q12_term(prm, key_d(mo, my, d), a);
    let fy = |y: Row| inner_sum(o, f, y);
    if n > 0 {
        lemma_outer_prefix(c, w, prm, po, py, mo, my, o, l, a, d, n - 1);
        let s = l.subrange(0, n);
        assert(s.drop_last() =~= l.subrange(0, n - 1));
        assert(s.last() == l[n - 1]);
        lemma_inner(c, w, prm, po, py, mo, my, o, l, a, d, n - 1);
    }
}

/// The normal form's group sum of entry `d` and aggregate `a` over the product of the stored relations is the
/// model's count over every stored lineitem row.
pub proof fn lemma_gsum_cnt(db: Database, parts: Seq<PartView>, c: Cols, w: Win, prm: Prm, po: Seq<u64>, py: Seq<u8>,
    mo: Seq<u64>, my: Seq<u8>, a: int, d: int)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        dicts_from_parts(parts, po, py, mo, my),
        win_matches(w, prm, po, py, mo, my),
        keys_distinct(c),
        a == 0 || a == 1,
        0 <= d < mo.len() - 1,
    ensures
        gsum(q12_g(prm), xs_of(db), key_d(mo, my, d), a) == cnt(c, w, a, d, 0, c.n_l as int),
{
    let g = q12_g(prm);
    let kd = key_d(mo, my, d);
    let f = q12_term(prm, kd, a);
    let (orel, lrel) = (orel_of(db), lrel_of(db));
    let (o, l) = (orows(parts, db), lrows(parts, db));
    lemma_rows_model(db, parts, c, po, py, mo, my);
    // Sum of terms over the product, in right-major order.
    lemma_acc_sum_of(g, xs_of(db), kd, a);
    lemma_sum_of_product_swap(orel, lrel, f);
    let fy0 = |y: Row| sum_of(orel, |x: Row| f(x + y));
    let fy1 = |y: Row| inner_sum(orel, f, y);
    let fy = |y: Row| inner_sum(o, f, y);
    assert forall|i: int| 0 <= i < lrel.len() implies fy0(#[trigger] lrel[i]) == fy1(lrel[i]) by {}
    lemma_sum_of_ext(lrel, fy0, fy1);
    // Both relations in storage order.
    lemma_rows_multiset(db, parts);
    lemma_sum_of_perm(lrel, l, fy1);
    assert forall|i: int| 0 <= i < l.len() implies fy1(#[trigger] l[i]) == fy(l[i]) by {
        lemma_sum_of_perm(orel, o, |x: Row| f(x + l[i]));
    }
    lemma_sum_of_ext(l, fy1, fy);
    lemma_outer_prefix(c, w, prm, po, py, mo, my, o, l, a, d, c.n_l as int);
    assert(l.subrange(0, c.n_l as int) =~= l);
}

/// The stored rows of a bound database decode as the model (`rows_model`).
pub proof fn lemma_rows_model(db: Database, parts: Seq<PartView>, c: Cols, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>,
    my: Seq<u8>)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        dicts_from_parts(parts, po, py, mo, my),
    ensures
        rows_model(c, orows(parts, db), lrows(parts, db), po, py, mo, my),
        dict_ok(po, py),
        dict_ok(mo, my),
{
    lemma_orders_cols(db, parts, c, po, py);
    lemma_lineitem_cols(db, parts, c, mo, my);
    lemma_row_widths(db, parts);
}

/// Stored orders rows have 7 columns, stored lineitem rows 15.
pub proof fn lemma_row_widths(db: Database, parts: Seq<PartView>)
    requires bound(db, parts),
    ensures
        forall|i: int| 0 <= i < orel_of(db).len() ==> (#[trigger] orel_of(db)[i]).len() == 7,
        forall|i: int| 0 <= i < lrel_of(db).len() ==> (#[trigger] lrel_of(db)[i]).len() == 15,
        forall|p: int| 0 <= p < orows(parts, db).len() ==> (#[trigger] orows(parts, db)[p]).len() == 7,
        forall|j: int| 0 <= j < lrows(parts, db).len() ==> (#[trigger] lrows(parts, db)[j]).len() == 15,
{
    lemma_stored_relations(db);
    lemma_row_maps(db, parts);
    let (orel, lrel) = (orel_of(db), lrel_of(db));
    assert(stored_columns_t1().len() == 7 && stored_columns_t0().len() == 15);
    assert forall|i: int| 0 <= i < orel.len() implies (#[trigger] orel[i]).len() == 7 by {}
    assert forall|i: int| 0 <= i < lrel.len() implies (#[trigger] lrel[i]).len() == 15 by {}
    let omap = orders_map(otp(parts), orel.len() as int);
    let lmap = lineitem_map(ltp(parts), lrel.len() as int);
    assert forall|p: int| 0 <= p < orows(parts, db).len() implies (#[trigger] orows(parts, db)[p]).len() == 7 by {
        assert(orows(parts, db)[p] == orel[omap[p]]);
    }
    assert forall|j: int| 0 <= j < lrows(parts, db).len() implies (#[trigger] lrows(parts, db)[j]).len() == 15 by {
        assert(lrows(parts, db)[j] == lrel[lmap[j]]);
    }
}

// ------------------------------------------------------------------------------------------------ counts and keys

/// Every qualifying row adds 1 to exactly one of the two sums: a group's count is the sum of its sums, and each
/// sum lies in `[0, count]`.
pub proof fn lemma_count_sums(prm: Prm, rows: Seq<Row>, k: Row)
    ensures
        gcount(q12_g(prm), rows, k) == gsum(q12_g(prm), rows, k, 0) + gsum(q12_g(prm), rows, k, 1),
        0 <= gsum(q12_g(prm), rows, k, 0),
        0 <= gsum(q12_g(prm), rows, k, 1),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_count_sums(prm, rows.drop_last(), k);
        let x = rows.last();
        assert(q12_arg(0, x) + q12_arg(1, x) == 1);
    }
}

/// A non-empty group of the normal form over the product is some ship-mode entry's group.
pub proof fn lemma_keys_complete(db: Database, parts: Seq<PartView>, c: Cols, po: Seq<u64>, py: Seq<u8>,
    mo: Seq<u64>, my: Seq<u8>, prm: Prm, kr: Row)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        dicts_from_parts(parts, po, py, mo, my),
        gcount(q12_g(prm), xs_of(db), kr) > 0,
    ensures
        exists|d: int| 0 <= d < mo.len() - 1 && kr == key_d(mo, my, d),
{
    let g = q12_g(prm);
    let xs = xs_of(db);
    let (orel, lrel) = (orel_of(db), lrel_of(db));
    let l = lrows(parts, db);
    lemma_rows_model(db, parts, c, po, py, mo, my);
    lemma_row_widths(db, parts);
    lemma_row_maps(db, parts);
    lemma_count_witness(g, xs, kr);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], kr);
    lemma_product_rows_elems(orel, lrel);
    assert(is_concat(xs[m], orel, lrel));
    let (i, j) = choose|i: int, j: int| 0 <= i < orel.len() && 0 <= j < lrel.len() && xs[m] == #[trigger] orel[i] + #[trigger] lrel[j];
    let lmap = lineitem_map(ltp(parts), lrel.len() as int);
    assert(covered(lmap, j));
    let jj = choose|jj: int| 0 <= jj < lmap.len() && lmap[jj] == j;
    assert(l[jj] == lrel[j]);
    let d = lmode(c, jj);
    assert(xs[m][21] == lrel[j][14]);
    assert(kr =~= key_d(mo, my, d));
}

} // verus!
