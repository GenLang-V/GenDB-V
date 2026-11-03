//! The groups of the normal form are the customers (`lemma_cust_group`, `lemma_group_is_cust`).
//!
//! A group key of the normal form is reached through joined rows `C[a] ++ O[b] ++ L[i] ++ N[n]`. By the primary
//! keys (`cols::keys_unique`), the key `ckey(a0)` of a customer whose nation exists is reached only through `a == a0`
//! and `n == nat_row(a0)`, by an order `b` that `a0` collects (`cmatch`) and a lineitem row `i` that hits `b`'s key
//! (`lhit`) (`lemma_hit_cust`). So the group's count, sum and absolute mass over the whole product are the
//! customer's totals `ctcnt`, `ctot`, `ctabs` (`lemma_cust_group`). Conversely every non-empty group is the key of
//! such a customer (`lemma_group_is_cust`).
//!
//! The sums over the product are taken in nested form (`link::join::lemma_sum_of_product`, customers outermost, then
//! orders, lineitems and nations) and written as index sums `isum`; all customer and nation terms but one are zero.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::relation::product_rows;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::param_domain;
use crate::link::query::*;
use crate::link::join::{sum_of, count_term, sum_term, abs_term, lemma_acc_sum_of, lemma_sum_of_zero, lemma_sum_of_map,
    lemma_sum_of_product};
use crate::link::source::lemma_proj_all_index;
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::denot::*;

verus! {

// ------------------------------------------------------------------------------------------------ index sums

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

/// Index sums of pointwise equal terms are equal.
pub proof fn lemma_isum_ext(t: spec_fn(int) -> int, u: spec_fn(int) -> int, n: int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] t(i) == u(i),
    ensures isum(t, n) == isum(u, n),
    decreases n,
{
    if n > 0 {
        lemma_isum_ext(t, u, n - 1);
    }
}

/// An index sum of zero terms is zero.
pub proof fn lemma_isum_zero(t: spec_fn(int) -> int, n: int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] t(i) == 0,
    ensures isum(t, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_isum_zero(t, n - 1);
    }
}

/// An index sum with one possibly non-zero term.
pub proof fn lemma_isum_single(t: spec_fn(int) -> int, n: int, i0: int)
    requires 0 <= i0 < n, forall|i: int| 0 <= i < n && i != i0 ==> #[trigger] t(i) == 0,
    ensures isum(t, n) == t(i0),
    decreases n,
{
    if n - 1 == i0 {
        lemma_isum_zero(t, n - 1);
    } else {
        lemma_isum_single(t, n - 1, i0);
    }
}

// ------------------------------------------------------------------------------------------------ per-key, per-customer terms

/// Term `i` of a key's sum with weight `wv`: `wv(i)` when lineitem row `i` hits key `k`.
pub open spec fn tk(sv: StoresView, k: int, wv: spec_fn(int) -> int) -> spec_fn(int) -> int {
    |i: int| if lhit(sv, k, i) { wv(i) } else { 0 }
}

/// Term `b` of a customer's sum with weight `wv`: the key sum of order `b` when customer `a0` collects it.
pub open spec fn tc(sv: StoresView, dlo: int, dhi: int, a0: int, wv: spec_fn(int) -> int) -> spec_fn(int) -> int {
    |b: int| if cmatch(sv, dlo, dhi, a0, b) { isum(tk(sv, ok(sv)[b] as int, wv), n_l(sv)) } else { 0 }
}

pub open spec fn w_one() -> spec_fn(int) -> int { |i: int| 1int }
pub open spec fn w_val(sv: StoresView) -> spec_fn(int) -> int { |i: int| lval(sv, i) }
pub open spec fn w_abs(sv: StoresView) -> spec_fn(int) -> int { |i: int| abs(lval(sv, i)) }

/// The per-key quantities as index sums.
pub proof fn lemma_k_isum(sv: StoresView, k: int, n: int)
    requires 0 <= n,
    ensures
        kcnt(sv, k, 0, n) == isum(tk(sv, k, w_one()), n),
        ksum(sv, k, 0, n) == isum(tk(sv, k, w_val(sv)), n),
        kabs(sv, k, 0, n) == isum(tk(sv, k, w_abs(sv)), n),
    decreases n,
{
    if n > 0 {
        lemma_k_isum(sv, k, n - 1);
    }
}

/// The per-customer quantities as index sums.
pub proof fn lemma_c_isum(sv: StoresView, dlo: int, dhi: int, a: int, n: int)
    requires 0 <= n,
    ensures
        ccnt(sv, dlo, dhi, a, 0, n) == isum(tc(sv, dlo, dhi, a, w_one()), n),
        csum(sv, dlo, dhi, a, 0, n) == isum(tc(sv, dlo, dhi, a, w_val(sv)), n),
        cabs(sv, dlo, dhi, a, 0, n) == isum(tc(sv, dlo, dhi, a, w_abs(sv)), n),
    decreases n,
{
    if n > 0 {
        lemma_c_isum(sv, dlo, dhi, a, n - 1);
        let b = n - 1;
        if cmatch(sv, dlo, dhi, a, b) {
            lemma_k_isum(sv, ok(sv)[b] as int, n_l(sv));
        }
    }
}

// ------------------------------------------------------------------------------------------------ hits of one customer

/// A joined row hits the group of customer `a0` (whose nation exists) exactly through `a0`, its nation row, an
/// order that `a0` collects and a lineitem row that hits that order's key.
pub proof fn lemma_hit_cust(sv: StoresView, db: Database, pd: int, t1: int, dlo: int, dhi: int, a0: int, w: JRow)
    requires
        bound_db(sv, db), win_of(dlo, dhi, pd, t1),
        0 <= a0 < n_c(sv), natok(sv, a0), jrow_ok(sv, w),
    ensures
        hit(q_spec(pd, t1), proj(joined(db, w.a, w.b, w.i, w.n), q_cols()), ckey(sv, a0))
            == (w.a == a0 && w.n == nat_row(sv, a0) && cmatch(sv, dlo, dhi, a0, w.b) && lhit(sv, ok(sv)[w.b] as int, w.i)),
        (q_spec(pd, t1).arg)(0, proj(joined(db, w.a, w.b, w.i, w.n), q_cols())) == lval(sv, w.i),
{
    let g = q_spec(pd, t1);
    let x = proj(joined(db, w.a, w.b, w.i, w.n), q_cols());
    let n0 = nat_row(sv, a0);
    lemma_joined_normal_form(sv, db, pd, t1, dlo, dhi, w);
    lemma_keys_unique(sv, db);
    lemma_parts_shape(sv, db);
    lemma_nat_row(sv, a0);
    let k0 = ckey(sv, a0);
    if hit(g, x, k0) {
        assert(jkey(sv, w)[0] == k0[0]);
        assert(ck(sv)[w.a] == ck(sv)[a0]);
        assert(w.a == a0);
        assert(nk(sv)[w.n] == nk(sv)[n0]);
        assert(w.n == n0);
    }
    if w.a == a0 && w.n == n0 && cmatch(sv, dlo, dhi, a0, w.b) && lhit(sv, ok(sv)[w.b] as int, w.i) {
        assert(jkey(sv, w) =~= k0);
    }
}

/// Count, sum and absolute mass of the group of customer `a0` over the whole product, for a per-row contribution `f`
/// (`wv` of the hitting lineitem row, 0 elsewhere).
pub proof fn lemma_cust_group_sum(sv: StoresView, db: Database, dlo: int, dhi: int, a0: int, f: spec_fn(Row) -> int,
    wv: spec_fn(int) -> int)
    requires
        bound_db(sv, db), 0 <= a0 < n_c(sv), natok(sv, a0),
        forall|a: int, b: int, i: int, n: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) && 0 <= n < n_n(sv) ==>
            #[trigger] f(proj(joined(db, a, b, i, n), q_cols()))
                == if a == a0 && n == nat_row(sv, a0) && cmatch(sv, dlo, dhi, a0, b) && lhit(sv, ok(sv)[b] as int, i) { wv(i) } else { 0 },
    ensures
        sum_of(q_xs(db), f) == isum(tc(sv, dlo, dhi, a0, wv), n_o(sv)),
{
    lemma_parts_shape(sv, db);
    lemma_nat_row(sv, a0);
    reveal(joined);
    let (c, o, l, nn) = (db.tables[2], db.tables[1], db.tables[0], db.tables[6]);
    let n0 = nat_row(sv, a0);
    let cols = q_cols();
    let rows = q_rows(db);
    let m = |r: Row| proj(r, cols);
    assert(q_xs(db) =~= rows.map_values(m));
    lemma_sum_of_map(rows, m, f);
    let ff = |r: Row| f(m(r));
    let p1 = product_rows(c, o);
    let p2 = product_rows(p1, l);
    lemma_sum_of_product(p2, nn, ff);
    let g3 = |x: Row| sum_of(nn, |y: Row| ff(x + y));
    lemma_sum_of_product(p1, l, g3);
    let g2 = |x: Row| sum_of(l, |y: Row| g3(x + y));
    lemma_sum_of_product(c, o, g2);
    let g1 = |x: Row| sum_of(o, |y: Row| g2(x + y));
    // every customer but a0 contributes nothing
    assert forall|t: int| 0 <= t < c.len() && t != a0 implies g1(#[trigger] c[t]) == 0 by {
        let q1 = |y: Row| g2(c[t] + y);
        assert forall|u: int| 0 <= u < o.len() implies q1(#[trigger] o[u]) == 0 by {
            let q2 = |y: Row| g3(c[t] + o[u] + y);
            assert forall|v: int| 0 <= v < l.len() implies q2(#[trigger] l[v]) == 0 by {
                let q3 = |y: Row| ff(c[t] + o[u] + l[v] + y);
                assert forall|z: int| 0 <= z < nn.len() implies q3(#[trigger] nn[z]) == 0 by {
                    assert(f(proj(joined(db, t, u, v, z), cols)) == 0);
                }
                lemma_sum_of_zero(nn, q3);
            }
            lemma_sum_of_zero(l, q2);
        }
        lemma_sum_of_zero(o, q1);
    }
    let tg1 = |t: int| g1(c[t]);
    assert forall|t: int| 0 <= t < c.len() implies g1(#[trigger] c[t]) == tg1(t) by {}
    lemma_sum_index(c, g1, tg1);
    assert forall|t: int| 0 <= t < c.len() && t != a0 implies #[trigger] tg1(t) == 0 by {
        assert(g1(c[t]) == 0);
    }
    lemma_isum_single(tg1, c.len() as int, a0);
    // a0's orders
    let q1 = |y: Row| g2(c[a0] + y);
    let tcw = tc(sv, dlo, dhi, a0, wv);
    assert forall|u: int| 0 <= u < o.len() implies q1(#[trigger] o[u]) == tcw(u) by {
        let q2 = |y: Row| g3(c[a0] + o[u] + y);
        let tku = tk(sv, ok(sv)[u] as int, wv);
        let tq2 = |v: int| if cmatch(sv, dlo, dhi, a0, u) { tku(v) } else { 0 };
        assert forall|v: int| 0 <= v < l.len() implies q2(#[trigger] l[v]) == tq2(v) by {
            let q3 = |y: Row| ff(c[a0] + o[u] + l[v] + y);
            let tq3 = |z: int| f(proj(joined(db, a0, u, v, z), cols));
            assert forall|z: int| 0 <= z < nn.len() implies q3(#[trigger] nn[z]) == tq3(z) by {}
            lemma_sum_index(nn, q3, tq3);
            assert forall|z: int| 0 <= z < nn.len() && z != n0 implies #[trigger] tq3(z) == 0 by {}
            lemma_isum_single(tq3, nn.len() as int, n0);
        }
        lemma_sum_index(l, q2, tq2);
        if cmatch(sv, dlo, dhi, a0, u) {
            lemma_isum_ext(tq2, tku, l.len() as int);
        } else {
            assert forall|v: int| 0 <= v < l.len() implies #[trigger] tq2(v) == 0 by {}
            lemma_isum_zero(tq2, l.len() as int);
        }
    }
    lemma_sum_index(o, q1, tcw);
}

/// The group of customer `a0` (whose nation exists): its count, sum and absolute mass over the product are the
/// customer's totals.
pub proof fn lemma_cust_group(sv: StoresView, db: Database, pd: int, t1: int, dlo: int, dhi: int, a0: int)
    requires bound_db(sv, db), win_of(dlo, dhi, pd, t1), 0 <= a0 < n_c(sv), natok(sv, a0),
    ensures ({
        let (g, xs, k) = (q_spec(pd, t1), q_xs(db), ckey(sv, a0));
        &&& gcount(g, xs, k) == ctcnt(sv, dlo, dhi, a0)
        &&& gsum(g, xs, k, 0) == ctot(sv, dlo, dhi, a0)
        &&& gabs(g, xs, k, 0) == ctabs(sv, dlo, dhi, a0)
    }),
{
    let (g, xs, k) = (q_spec(pd, t1), q_xs(db), ckey(sv, a0));
    lemma_acc_sum_of(g, xs, k, 0);
    lemma_c_isum(sv, dlo, dhi, a0, n_o(sv));
    let n0 = nat_row(sv, a0);
    assert forall|a: int, b: int, i: int, n: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) && 0 <= n < n_n(sv) implies
        #[trigger] count_term(g, k)(proj(joined(db, a, b, i, n), q_cols()))
            == if a == a0 && n == n0 && cmatch(sv, dlo, dhi, a0, b) && lhit(sv, ok(sv)[b] as int, i) { w_one()(i) } else { 0 } by {
        lemma_hit_cust(sv, db, pd, t1, dlo, dhi, a0, JRow { a, b, i, n });
    }
    lemma_cust_group_sum(sv, db, dlo, dhi, a0, count_term(g, k), w_one());
    assert forall|a: int, b: int, i: int, n: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) && 0 <= n < n_n(sv) implies
        #[trigger] sum_term(g, k, 0)(proj(joined(db, a, b, i, n), q_cols()))
            == if a == a0 && n == n0 && cmatch(sv, dlo, dhi, a0, b) && lhit(sv, ok(sv)[b] as int, i) { w_val(sv)(i) } else { 0 } by {
        lemma_hit_cust(sv, db, pd, t1, dlo, dhi, a0, JRow { a, b, i, n });
    }
    lemma_cust_group_sum(sv, db, dlo, dhi, a0, sum_term(g, k, 0), w_val(sv));
    assert forall|a: int, b: int, i: int, n: int| 0 <= a < n_c(sv) && 0 <= b < n_o(sv) && 0 <= i < n_l(sv) && 0 <= n < n_n(sv) implies
        #[trigger] abs_term(g, k, 0)(proj(joined(db, a, b, i, n), q_cols()))
            == if a == a0 && n == n0 && cmatch(sv, dlo, dhi, a0, b) && lhit(sv, ok(sv)[b] as int, i) { w_abs(sv)(i) } else { 0 } by {
        lemma_hit_cust(sv, db, pd, t1, dlo, dhi, a0, JRow { a, b, i, n });
    }
    lemma_cust_group_sum(sv, db, dlo, dhi, a0, abs_term(g, k, 0), w_abs(sv));
}

/// Every non-empty group is the key of a customer whose nation exists and that some lineitem row reaches.
pub proof fn lemma_group_is_cust(sv: StoresView, db: Database, pd: int, t1: int, dlo: int, dhi: int, k: Row) -> (a0: int)
    requires bound_db(sv, db), win_of(dlo, dhi, pd, t1), gcount(q_spec(pd, t1), q_xs(db), k) > 0,
    ensures is_group(sv, dlo, dhi, a0), k == ckey(sv, a0),
{
    let (g, xs) = (q_spec(pd, t1), q_xs(db));
    lemma_count_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    lemma_proj_all_index(q_rows(db), q_cols());
    let w = lemma_joined_witness(sv, db, m);
    lemma_joined_normal_form(sv, db, pd, t1, dlo, dhi, w);
    let a0 = w.a;
    assert(nk(sv)[w.n] == cnk(sv)[a0]);
    assert(natok(sv, a0));
    lemma_nat_row(sv, a0);
    lemma_keys_unique(sv, db);
    assert(nat_row(sv, a0) == w.n);
    assert(k =~= ckey(sv, a0));
    lemma_cust_group(sv, db, pd, t1, dlo, dhi, a0);
    a0
}

} // verus!
