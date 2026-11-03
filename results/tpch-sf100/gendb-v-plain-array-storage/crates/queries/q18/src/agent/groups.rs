//! The groups of the normal form are the qualifying orders.
//!
//! An orders row `j` qualifies (`ord_ok`) when its key is in the subquery's result and some customer row has its
//! customer key. A group key `k` of the normal form is reached through joined rows `C[a] ++ O[b] ++ L[i]`. By the
//! primary keys (`keys_unique`), the key of a qualifying order `j0` (`order_key`) is reached only through `b == j0`
//! and the one customer `a0` of `j0`, so the group's count, sum and absolute mass over the whole product are the
//! per-key quantities of `j0`'s order key over the lineitem rows (`lemma_order_group`). Conversely every non-empty
//! group is the key of a qualifying order (`lemma_group_is_order`).
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
use crate::link::expr::i128_max;
use crate::link::join::{sum_of, count_term, sum_term, abs_term, lemma_acc_sum_of, lemma_sum_of_zero, lemma_sum_of_map,
    lemma_sum_of_remove, lemma_sum_of_product};
use crate::link::source::lemma_proj_all_index;
use crate::agent::tables::*;
use crate::agent::common::keysum::*;
use crate::agent::lookup::has_key;
use crate::agent::subquery::*;
use crate::agent::denotation::*;

verus! {

// ------------------------------------------------------------------------------------------------ qualifying orders

/// Orders row `j` qualifies: its key is in the subquery's result and its customer exists.
pub open spec fn ord_ok(sv: StoresView, ps: Seq<Literal>, j: int) -> bool {
    &&& in_sub(sv, ps, ok(sv)[j] as int)
    &&& has_key(ck(sv), oc(sv)[j])
}

/// The customer row of orders row `j` (some row with its customer key; unique by the primary key).
pub open spec fn cust_of(sv: StoresView, j: int) -> int {
    choose|a: int| 0 <= a < ck(sv).len() && ck(sv)[a] == oc(sv)[j]
}

/// The group key of orders row `j`: `(c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice)`.
pub open spec fn order_key(sv: StoresView, j: int) -> Row {
    let a = cust_of(sv, j);
    seq![Val::Text(cname(sv, a)), Val::Int(ck(sv)[a] as int), Val::Int(ok(sv)[j] as int), date32_val(od(sv)[j]),
        Val::Num { coeff: otp(sv)[j] as int, scale: 2 }]
}

/// The quantity sum of orders row `j`'s key over all lineitem rows.
pub open spec fn order_sum(sv: StoresView, j: int) -> int {
    ksum(lk(sv), lq(sv), ok(sv)[j], 0, n_l(sv))
}

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

/// The per-key quantities as index sums, and the absolute sum's bound.
pub proof fn lemma_key_isum(sv: StoresView, v: i64, n: int)
    requires 0 <= n <= n_l(sv), lq(sv).len() == n_l(sv), forall|i: int| 0 <= i < n_l(sv) ==> num15(#[trigger] lq(sv)[i]),
    ensures
        kcount(lk(sv), v, 0, n) == isum(|i: int| if lk(sv)[i] == v { 1int } else { 0int }, n),
        ksum(lk(sv), lq(sv), v, 0, n) == isum(|i: int| if lk(sv)[i] == v { lq(sv)[i] as int } else { 0int }, n),
        0 <= isum(|i: int| if lk(sv)[i] == v { abs(lq(sv)[i] as int) } else { 0int }, n) <= n * 1_000_000_000_000_000,
    decreases n,
{
    if n > 0 {
        lemma_key_isum(sv, v, n - 1);
        assert(num15(lq(sv)[n - 1]));
    }
}

// ------------------------------------------------------------------------------------------------ hits of one order

/// A joined row hits the group of qualifying order `j0` exactly through `j0`'s customer and `j0` itself, by a
/// lineitem row of `j0`'s key.
pub proof fn lemma_hit_order(sv: StoresView, db: Database, ps: Seq<Literal>, j0: int, a: int, b: int, i: int)
    requires
        bound_db(sv, db),
        0 <= j0 < n_o(sv), ord_ok(sv, ps, j0),
        0 <= a < n_c(sv), 0 <= b < n_o(sv), 0 <= i < n_l(sv),
    ensures
        hit(q_spec(sv, ps), proj(joined(db, a, b, i), q_cols()), order_key(sv, j0))
            == (a == cust_of(sv, j0) && b == j0 && lk(sv)[i] == ok(sv)[j0]),
        (q_spec(sv, ps).arg)(0, proj(joined(db, a, b, i), q_cols())) == lq(sv)[i] as int,
{
    let g = q_spec(sv, ps);
    let x = proj(joined(db, a, b, i), q_cols());
    lemma_parts_shape(sv, db);
    let a0 = cust_of(sv, j0);
    assert(has_key(ck(sv), oc(sv)[j0]));
    let aw = choose|aw: int| 0 <= aw < ck(sv).len() && ck(sv)[aw] == oc(sv)[j0];
    assert(0 <= a0 < n_c(sv) && ck(sv)[a0] == oc(sv)[j0]);
    lemma_joined_normal_form(sv, db, ps, a, b, i);
    lemma_keys_unique(sv, db);
    let k0 = order_key(sv, j0);
    if hit(g, x, k0) {
        assert((g.key)(x)[2] == k0[2]);
        assert(ok(sv)[b] == ok(sv)[j0]);
        assert(b == j0);
        assert((g.key)(x)[1] == k0[1]);
        assert(ck(sv)[a] == ck(sv)[a0]);
        assert(a == a0);
    }
    if a == a0 && b == j0 && lk(sv)[i] == ok(sv)[j0] {
        assert((g.key)(x) =~= k0);
    }
}

/// One of the three per-row contributions `f` of the group of qualifying order `j0` (`t(i)` for the joined rows of
/// `j0`'s customer, `j0` and lineitem row `i`, 0 elsewhere) summed over the whole product.
pub proof fn lemma_order_group_sum(sv: StoresView, db: Database, ps: Seq<Literal>, j0: int, f: spec_fn(Row) -> int,
    t0: spec_fn(int) -> int)
    requires
        bound_db(sv, db),
        0 <= j0 < n_o(sv), ord_ok(sv, ps, j0),
        forall|a: int, b: int, i: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) ==>
            #[trigger] f(proj(joined(db, a, b, i), q_cols()))
                == if a == cust_of(sv, j0) && b == j0 { t0(i) } else { 0 },
    ensures
        sum_of(q_xs(db), f) == isum(t0, n_l(sv)),
{
    lemma_parts_shape(sv, db);
    let (c, o, l) = (db.tables[2], db.tables[1], db.tables[0]);
    let cols = q_cols();
    let a0 = cust_of(sv, j0);
    assert(has_key(ck(sv), oc(sv)[j0]));
    let aw = choose|aw: int| 0 <= aw < ck(sv).len() && ck(sv)[aw] == oc(sv)[j0];
    assert(0 <= a0 < n_c(sv));
    let rows = q_rows(db);
    let m = |r: Row| proj(r, cols);
    assert(q_xs(db) =~= rows.map_values(m));
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
    assert forall|v: int| 0 <= v < l.len() implies h0(#[trigger] l[v]) == t0(v) by {
        assert(f(proj(joined(db, a0, j0, v), cols)) == t0(v));
    }
    lemma_sum_index(l, h0, t0);
}

/// The group of a qualifying order: its count and sum over the product are its key's lineitem count and quantity
/// sum; its absolute mass is at most `n_l * 10^15`.
pub proof fn lemma_order_group(sv: StoresView, db: Database, ps: Seq<Literal>, j0: int)
    requires
        bound_db(sv, db),
        0 <= j0 < n_o(sv), ord_ok(sv, ps, j0),
    ensures ({
        let (g, xs, k, v) = (q_spec(sv, ps), q_xs(db), order_key(sv, j0), ok(sv)[j0]);
        &&& gcount(g, xs, k) == kcount(lk(sv), v, 0, n_l(sv))
        &&& gsum(g, xs, k, 0) == ksum(lk(sv), lq(sv), v, 0, n_l(sv))
        &&& gabs(g, xs, k, 0) <= n_l(sv) * 1_000_000_000_000_000
    }),
{
    let (g, xs, k, v) = (q_spec(sv, ps), q_xs(db), order_key(sv, j0), ok(sv)[j0]);
    lemma_cols_facts(sv, db);
    lemma_acc_sum_of(g, xs, k, 0);
    lemma_key_isum(sv, v, n_l(sv));
    let a0 = cust_of(sv, j0);
    let tc = |i: int| if lk(sv)[i] == v { 1int } else { 0int };
    let ts = |i: int| if lk(sv)[i] == v { lq(sv)[i] as int } else { 0int };
    let ta = |i: int| if lk(sv)[i] == v { abs(lq(sv)[i] as int) } else { 0int };
    assert forall|a: int, b: int, i: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) implies {
        &&& #[trigger] count_term(g, k)(proj(joined(db, a, b, i), q_cols())) == if a == a0 && b == j0 { tc(i) } else { 0int }
        &&& sum_term(g, k, 0)(proj(joined(db, a, b, i), q_cols())) == if a == a0 && b == j0 { ts(i) } else { 0int }
        &&& abs_term(g, k, 0)(proj(joined(db, a, b, i), q_cols())) == if a == a0 && b == j0 { ta(i) } else { 0int }
    } by {
        lemma_hit_order(sv, db, ps, j0, a, b, i);
    }
    assert forall|a: int, b: int, i: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) implies
        #[trigger] sum_term(g, k, 0)(proj(joined(db, a, b, i), q_cols())) == if a == a0 && b == j0 { ts(i) } else { 0int } by {
        lemma_hit_order(sv, db, ps, j0, a, b, i);
    }
    assert forall|a: int, b: int, i: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) implies
        #[trigger] abs_term(g, k, 0)(proj(joined(db, a, b, i), q_cols())) == if a == a0 && b == j0 { ta(i) } else { 0int } by {
        lemma_hit_order(sv, db, ps, j0, a, b, i);
    }
    lemma_order_group_sum(sv, db, ps, j0, count_term(g, k), tc);
    lemma_order_group_sum(sv, db, ps, j0, sum_term(g, k, 0), ts);
    lemma_order_group_sum(sv, db, ps, j0, abs_term(g, k, 0), ta);
}

/// Every non-empty group is the key of a qualifying order.
pub proof fn lemma_group_is_order(sv: StoresView, db: Database, ps: Seq<Literal>, k: Row) -> (j: int)
    requires bound_db(sv, db), gcount(q_spec(sv, ps), q_xs(db), k) > 0,
    ensures
        0 <= j < n_o(sv),
        ord_ok(sv, ps, j),
        k == order_key(sv, j),
{
    let (g, xs) = (q_spec(sv, ps), q_xs(db));
    lemma_count_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    lemma_proj_all_index(q_rows(db), q_cols());
    let (a, b, i) = lemma_joined_witness(sv, db, m);
    lemma_joined_normal_form(sv, db, ps, a, b, i);
    lemma_parts_shape(sv, db);
    lemma_keys_unique(sv, db);
    assert(ck(sv)[a] == oc(sv)[b]);
    assert(has_key(ck(sv), oc(sv)[b]));
    assert(ord_ok(sv, ps, b));
    let a0 = cust_of(sv, b);
    assert(0 <= a0 < n_c(sv) && ck(sv)[a0] == oc(sv)[b]);
    assert(a0 == a);
    assert(k =~= order_key(sv, b));
    b
}

/// The SUM capacity of the statement: every group's absolute mass fits `i128` (the lineitem table has at most
/// `usize::MAX` rows).
pub proof fn lemma_caps(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), small(sv),
    ensures group_caps(q_spec(sv, ps), q_xs(db)),
{
    let (g, xs) = (q_spec(sv, ps), q_xs(db));
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 0);
        if gcount(g, xs, k) == 0 {
            lemma_zero_count(g, xs, k, 0);
        } else {
            let jj = lemma_group_is_order(sv, db, ps, k);
            lemma_order_group(sv, db, ps, jj);
            let n = n_l(sv);
            assert(n * 1_000_000_000_000_000 <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff) by (nonlinear_arith)
                requires 0 <= n <= usize::MAX;
        }
    }
}

} // verus!
