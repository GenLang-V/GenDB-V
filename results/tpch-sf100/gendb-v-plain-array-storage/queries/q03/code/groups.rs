//! The groups of the normal form are the qualifying orders.
//!
//! A group key `k` of the normal form is reached through joined rows `C[a] ++ O[b] ++ L[i]`. By the primary keys
//! (`keys_unique`), the key of a qualifying order `j0` (`order_key`) is reached only through `b == j0` and the one
//! customer `a0` of `j0`, so the group's count, sum and absolute mass over the whole product are the per-order
//! quantities over the lineitem rows that hit `j0` (`lemma_order_group`). Conversely every non-empty group is the
//! key of a qualifying order with a hitting lineitem (`lemma_group_is_order`).
//!
//! The sums over the product are taken in nested form (`link::join::lemma_sum_of_product`): customers outermost,
//! then orders, then lineitems; all customer and order terms but one are zero (`lemma_sum_single`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::relation::product_rows;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::param_domain;
use crate::link::query::*;
use crate::link::join::{sum_of, count_term, sum_term, abs_term, lemma_acc_sum_of, lemma_sum_of_zero, lemma_sum_of_map,
    lemma_sum_of_remove, lemma_sum_of_product};
use crate::link::source::lemma_proj_all_index;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::*;

verus! {

// ------------------------------------------------------------------------------------------------ sums

/// A sum with one possibly non-zero term.
pub proof fn lemma_sum_single(s: Seq<Row>, f: spec_fn(Row) -> int, i0: int)
    requires 0 <= i0 < s.len(), forall|t: int| 0 <= t < s.len() && t != i0 ==> f(#[trigger] s[t]) == 0,
    ensures sum_of(s, f) == f(s[i0]),
{
    lemma_sum_of_remove(s, i0, f);
    let r = s.remove(i0);
    assert forall|t: int| 0 <= t < r.len() implies f(#[trigger] r[t]) == 0 by {
        if t < i0 {
            assert(r[t] == s[t]);
        } else {
            assert(r[t] == s[t + 1]);
        }
    }
    lemma_sum_of_zero(r, f);
}

/// `Σ_{i < n} t(i)`.
pub open spec fn isum(t: spec_fn(int) -> int, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { isum(t, n - 1) + t(n - 1) }
}

/// A sum over a sequence whose element `i` contributes `t(i)`.
pub proof fn lemma_sum_index(s: Seq<Row>, h: spec_fn(Row) -> int, t: spec_fn(int) -> int)
    requires forall|i: int| 0 <= i < s.len() ==> h(#[trigger] s[i]) == t(i),
    ensures sum_of(s, h) == isum(t, s.len() as int),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies h(#[trigger] d[i]) == t(i) by {
            assert(d[i] == s[i]);
        }
        lemma_sum_index(d, h, t);
        assert(s.last() == s[s.len() - 1]);
    }
}

/// The per-order quantities as index sums.
pub proof fn lemma_order_isum(sv: StoresView, seg: Seq<u8>, dl: int, j: int, n: int)
    requires 0 <= n,
    ensures
        order_count(sv, seg, dl, j, 0, n) == isum(|i: int| if line_hit(sv, seg, dl, i, j) { 1int } else { 0int }, n),
        order_sum(sv, seg, dl, j, 0, n) == isum(|i: int| if line_hit(sv, seg, dl, i, j) { line_value(sv, i) } else { 0int }, n),
        order_abs(sv, seg, dl, j, 0, n) == isum(|i: int| if line_hit(sv, seg, dl, i, j) { abs(line_value(sv, i)) } else { 0int }, n),
    decreases n,
{
    if n > 0 {
        lemma_order_isum(sv, seg, dl, j, n - 1);
    }
}

// ------------------------------------------------------------------------------------------------ hits of one order

/// The customer row of a qualifying order (it exists by `cust_ok`).
pub open spec fn cust_row(sv: StoresView, seg: Seq<u8>, key: int) -> int {
    choose|r: int| 0 <= r < n_c(sv) && ck(sv)[r] as int == key && #[trigger] cseg(sv, r) == seg
}

/// A joined row hits the group of qualifying order `j0` exactly through `j0`'s customer and `j0` itself, by a
/// lineitem row that hits `j0`.
pub proof fn lemma_hit_order(sv: StoresView, db: Database, ps: Seq<Literal>, j0: int, a: int, b: int, i: int)
    requires
        bound_db(sv, db), param_domain(ps),
        0 <= j0 < n_o(sv), order_ok(sv, seg_of(ps), dl_of(ps), j0),
        0 <= a < n_c(sv), 0 <= b < n_o(sv), 0 <= i < n_l(sv),
    ensures
        hit(q3_spec(ps), proj(joined(db, a, b, i), q3_cols()), order_key(sv, j0))
            == (a == cust_row(sv, seg_of(ps), oc(sv)[j0] as int) && b == j0 && line_hit(sv, seg_of(ps), dl_of(ps), i, j0)),
        line_hit(sv, seg_of(ps), dl_of(ps), i, j0) ==> (q3_spec(ps).arg)(0, proj(joined(db, a, b, i), q3_cols())) == line_value(sv, i),
{
    let (seg, dl) = (seg_of(ps), dl_of(ps));
    let g = q3_spec(ps);
    let x = proj(joined(db, a, b, i), q3_cols());
    let a0 = cust_row(sv, seg, oc(sv)[j0] as int);
    lemma_joined_normal_form(sv, db, ps, a, b, i);
    lemma_keys_unique(sv, db);
    lemma_parts_shape(sv, db);
    let k0 = order_key(sv, j0);
    if hit(g, x, k0) {
        assert((g.key)(x)[0] == k0[0]);
        assert(lk(sv)[i] == ok(sv)[j0]);
        assert(ok(sv)[b] == ok(sv)[j0]);
        assert(b == j0);
        assert(ck(sv)[a] == ck(sv)[a0]);
        assert(a == a0);
    }
    if a == a0 && b == j0 && line_hit(sv, seg, dl, i, j0) {
        assert((g.key)(x) =~= k0);
    }
}

/// Count, sum and absolute mass of the group of qualifying order `j0` over the whole product, for one of the three
/// per-row contributions `f` (`w` of the hitting lineitem row, 0 elsewhere).
pub proof fn lemma_order_group_sum(sv: StoresView, db: Database, ps: Seq<Literal>, j0: int, f: spec_fn(Row) -> int,
    w: spec_fn(int) -> int)
    requires
        bound_db(sv, db), param_domain(ps),
        0 <= j0 < n_o(sv), order_ok(sv, seg_of(ps), dl_of(ps), j0),
        forall|a: int, b: int, i: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) ==>
            #[trigger] f(proj(joined(db, a, b, i), q3_cols()))
                == if a == cust_row(sv, seg_of(ps), oc(sv)[j0] as int) && b == j0 && line_hit(sv, seg_of(ps), dl_of(ps), i, j0) { w(i) } else { 0 },
    ensures
        sum_of(q3_xs(db), f) == isum(|i: int| if line_hit(sv, seg_of(ps), dl_of(ps), i, j0) { w(i) } else { 0int }, n_l(sv)),
{
    let (seg, dl) = (seg_of(ps), dl_of(ps));
    lemma_parts_shape(sv, db);
    let (c, o, l) = (db.tables[2], db.tables[1], db.tables[0]);
    let cols = q3_cols();
    let a0 = cust_row(sv, seg, oc(sv)[j0] as int);
    let rows = q3_rows(db);
    let m = |r: Row| proj(r, cols);
    assert(q3_xs(db) =~= rows.map_values(m));
    lemma_sum_of_map(rows, m, f);
    let ff = |r: Row| f(m(r));
    let co = product_rows(c, o);
    lemma_sum_of_product(co, l, ff);
    let gg = |x: Row| sum_of(l, |y: Row| ff(x + y));
    lemma_sum_of_product(c, o, gg);
    let pp = |x: Row| sum_of(o, |y: Row| gg(x + y));
    // every customer but a0 contributes nothing
    assert forall|t: int| 0 <= t < c.len() && t != a0 implies pp(#[trigger] c[t]) == 0 by {
        let qq = |y: Row| gg(c[t] + y);
        assert forall|u: int| 0 <= u < o.len() implies qq(#[trigger] o[u]) == 0 by {
            let hh = |y: Row| ff(c[t] + o[u] + y);
            assert forall|v: int| 0 <= v < l.len() implies hh(#[trigger] l[v]) == 0 by {
                assert(f(proj(joined(db, t, u, v), cols)) == 0);
            }
            lemma_sum_of_zero(l, hh);
        }
        lemma_sum_of_zero(o, qq);
    }
    lemma_sum_single(c, pp, a0);
    // of a0's terms, only j0 contributes
    let qq0 = |y: Row| gg(c[a0] + y);
    assert forall|u: int| 0 <= u < o.len() && u != j0 implies qq0(#[trigger] o[u]) == 0 by {
        let hh = |y: Row| ff(c[a0] + o[u] + y);
        assert forall|v: int| 0 <= v < l.len() implies hh(#[trigger] l[v]) == 0 by {
            assert(f(proj(joined(db, a0, u, v), cols)) == 0);
        }
        lemma_sum_of_zero(l, hh);
    }
    lemma_sum_single(o, qq0, j0);
    let h0 = |y: Row| ff(c[a0] + o[j0] + y);
    let t0 = |i: int| if line_hit(sv, seg, dl, i, j0) { w(i) } else { 0int };
    assert forall|v: int| 0 <= v < l.len() implies h0(#[trigger] l[v]) == t0(v) by {
        assert(f(proj(joined(db, a0, j0, v), cols)) == t0(v));
    }
    lemma_sum_index(l, h0, t0);
}

/// The group of a qualifying order: its count, sum and absolute mass over the product are the order's.
pub proof fn lemma_order_group(sv: StoresView, db: Database, ps: Seq<Literal>, j0: int)
    requires
        bound_db(sv, db), param_domain(ps),
        0 <= j0 < n_o(sv), order_ok(sv, seg_of(ps), dl_of(ps), j0),
    ensures ({
        let (g, xs, k, seg, dl) = (q3_spec(ps), q3_xs(db), order_key(sv, j0), seg_of(ps), dl_of(ps));
        &&& gcount(g, xs, k) == order_count(sv, seg, dl, j0, 0, n_l(sv))
        &&& gsum(g, xs, k, 0) == order_sum(sv, seg, dl, j0, 0, n_l(sv))
        &&& gabs(g, xs, k, 0) == order_abs(sv, seg, dl, j0, 0, n_l(sv))
    }),
{
    let (g, xs, k, seg, dl) = (q3_spec(ps), q3_xs(db), order_key(sv, j0), seg_of(ps), dl_of(ps));
    lemma_acc_sum_of(g, xs, k, 0);
    lemma_order_isum(sv, seg, dl, j0, n_l(sv));
    let a0 = cust_row(sv, seg, oc(sv)[j0] as int);
    assert forall|a: int, b: int, i: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) implies
        #[trigger] count_term(g, k)(proj(joined(db, a, b, i), q3_cols()))
            == if a == a0 && b == j0 && line_hit(sv, seg, dl, i, j0) { 1int } else { 0int } by {
        lemma_hit_order(sv, db, ps, j0, a, b, i);
    }
    lemma_order_group_sum(sv, db, ps, j0, count_term(g, k), |i: int| 1int);
    assert forall|a: int, b: int, i: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) implies
        #[trigger] sum_term(g, k, 0)(proj(joined(db, a, b, i), q3_cols()))
            == if a == a0 && b == j0 && line_hit(sv, seg, dl, i, j0) { line_value(sv, i) } else { 0int } by {
        lemma_hit_order(sv, db, ps, j0, a, b, i);
    }
    lemma_order_group_sum(sv, db, ps, j0, sum_term(g, k, 0), |i: int| line_value(sv, i));
    assert forall|a: int, b: int, i: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) implies
        #[trigger] abs_term(g, k, 0)(proj(joined(db, a, b, i), q3_cols()))
            == if a == a0 && b == j0 && line_hit(sv, seg, dl, i, j0) { abs(line_value(sv, i)) } else { 0int } by {
        lemma_hit_order(sv, db, ps, j0, a, b, i);
    }
    lemma_order_group_sum(sv, db, ps, j0, abs_term(g, k, 0), |i: int| abs(line_value(sv, i)));
    let tc = |i: int| if line_hit(sv, seg, dl, i, j0) { 1int } else { 0int };
    let tc2 = |i: int| if line_hit(sv, seg, dl, i, j0) { (|i: int| 1int)(i) } else { 0int };
    assert(tc =~= tc2);
    let ts = |i: int| if line_hit(sv, seg, dl, i, j0) { line_value(sv, i) } else { 0int };
    let ts2 = |i: int| if line_hit(sv, seg, dl, i, j0) { (|i: int| line_value(sv, i))(i) } else { 0int };
    assert(ts =~= ts2);
    let ta = |i: int| if line_hit(sv, seg, dl, i, j0) { abs(line_value(sv, i)) } else { 0int };
    let ta2 = |i: int| if line_hit(sv, seg, dl, i, j0) { (|i: int| abs(line_value(sv, i)))(i) } else { 0int };
    assert(ta =~= ta2);
}

/// Every non-empty group is the key of a qualifying order hit by some lineitem row.
pub proof fn lemma_group_is_order(sv: StoresView, db: Database, ps: Seq<Literal>, k: Row) -> (j: int)
    requires bound_db(sv, db), param_domain(ps), gcount(q3_spec(ps), q3_xs(db), k) > 0,
    ensures
        0 <= j < n_o(sv),
        order_ok(sv, seg_of(ps), dl_of(ps), j),
        k == order_key(sv, j),
        order_count(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv)) > 0,
{
    let (g, xs, seg, dl) = (q3_spec(ps), q3_xs(db), seg_of(ps), dl_of(ps));
    lemma_count_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    lemma_proj_all_index(q3_rows(db), q3_cols());
    let (a, b, i) = lemma_joined_witness(sv, db, m);
    lemma_joined_normal_form(sv, db, ps, a, b, i);
    assert(cseg(sv, a) == seg && ck(sv)[a] as int == oc(sv)[b] as int);
    assert(cust_ok(sv, seg, oc(sv)[b] as int));
    assert(order_ok(sv, seg, dl, b));
    assert(k =~= order_key(sv, b));
    lemma_order_group(sv, db, ps, b);
    b
}

} // verus!
