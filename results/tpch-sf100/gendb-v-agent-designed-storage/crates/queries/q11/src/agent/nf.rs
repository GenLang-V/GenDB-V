//! The Q11 normal form over the three tables (`tables::Tabs`).
//!
//! The FROM relation is the left-major product `xs(t) = partsupp x supplier x nation`; its rows are
//! `ps[k] ++ s[j] ++ n[q]` (16 values). The WHERE condition is `qualx` (ps_suppkey = s_suppkey, s_nationkey =
//! n_nationkey, n_name = $1), the GROUP BY key is `[ps_partkey]` and the aggregate argument is
//! `ps_supplycost * ps_availqty` as a coefficient of scale 2 (`argx`). `gq` is that normal form grouped by
//! ps_partkey (the outer query), `gs` the same rows as one scalar group (the HAVING subquery).
//!
//! With the declared primary keys of supplier and nation (`keys_unique`), every partsupp row joins at most one
//! (supplier, nation) pair, so every accumulator over `xs(t)` is the same sum over the partsupp rows alone, each
//! row counted when its supplier is in a nation named `$1` (`rq`): `lemma_xsum`, `lemma_accs`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::{abs, pow10};
use crate::spec::relation::product_rows;
use crate::link::expr::ival;
use crate::link::query::{QuerySpec, AggKind, gsum, gcount, gabs, hit, group_caps};
use crate::link::join::{sum_of, lemma_sum_of_product, lemma_sum_of_ext, lemma_acc_sum_of, sum_term, count_term, abs_term};
use super::tables::Tabs;

verus! {

// ------------------------------------------------------------------------------------------------ table rows

/// A partsupp row: ps_partkey, ps_suppkey, ps_availqty (bigint), ps_supplycost (numeric(15,2)).
pub open spec fn ps_typed(r: Row) -> bool {
    &&& r.len() == 5
    &&& r[0] is Int && r[1] is Int && r[2] is Int
    &&& r[3] is Num && r[3]->scale == 2
    &&& i64::MIN <= ival(r[0]) <= i64::MAX
    &&& i64::MIN <= ival(r[2]) <= i64::MAX
    &&& abs(ival(r[3])) < pow10(15)
}

/// A supplier row: s_suppkey and s_nationkey (bigint).
pub open spec fn s_typed(r: Row) -> bool {
    r.len() == 7 && r[0] is Int && r[3] is Int
}

/// A nation row: n_nationkey (bigint), n_name (text).
pub open spec fn n_typed(r: Row) -> bool {
    r.len() == 4 && r[0] is Int && r[1] is Text
}

pub open spec fn tabs_typed(t: Tabs) -> bool {
    &&& forall|k: int| 0 <= k < t.ps.len() ==> #[trigger] ps_typed(t.ps[k])
    &&& forall|j: int| 0 <= j < t.s.len() ==> #[trigger] s_typed(t.s[j])
    &&& forall|q: int| 0 <= q < t.n.len() ==> #[trigger] n_typed(t.n[q])
}

/// The declared primary keys of supplier and nation: two rows with one key are one row.
pub open spec fn keys_unique(t: Tabs) -> bool {
    &&& forall|i: int, j: int| 0 <= i < t.s.len() && 0 <= j < t.s.len() && #[trigger] t.s[i][0] == #[trigger] t.s[j][0] ==> i == j
    &&& forall|i: int, j: int| 0 <= i < t.n.len() && 0 <= j < t.n.len() && #[trigger] t.n[i][0] == #[trigger] t.n[j][0] ==> i == j
}

// ------------------------------------------------------------------------------------------------ the FROM rows

/// The FROM relation `partsupp x supplier x nation` (left-major).
pub open spec fn xs(t: Tabs) -> Seq<Row> {
    product_rows(product_rows(t.ps, t.s), t.n)
}

/// The WHERE condition on a joined row (ps_suppkey = s_suppkey, s_nationkey = n_nationkey, n_name = `name`).
pub open spec fn qualx(name: Seq<u8>, x: Row) -> bool {
    &&& x[1] == x[5]
    &&& x[8] == x[12]
    &&& x[13] == Val::Text(name)
}

/// The aggregate argument `ps_supplycost * ps_availqty` as a coefficient of scale 2.
pub open spec fn argx(x: Row) -> int {
    ival(x[3]) * ival(x[2])
}

/// The outer query in normal form: grouped by `[ps_partkey]`, one SUM, output `ps_partkey, value`.
pub open spec fn gq(name: Seq<u8>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| qualx(name, x),
        key: |x: Row| seq![x[0]],
        arg: |j: int, x: Row| argx(x),
        aggs: seq![AggKind::Sum { scale: 2 }],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

/// The subquery's aggregate in normal form: the same rows as one scalar group.
pub open spec fn gs(name: Seq<u8>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| qualx(name, x),
        key: |x: Row| Seq::<Val>::empty(),
        arg: |j: int, x: Row| argx(x),
        aggs: seq![AggKind::Sum { scale: 2 }],
        outs: seq![0nat],
        grouped: false,
    }
}

// ------------------------------------------------------------------------------------------------ partsupp rows

/// Nation key value `v` belongs to a nation named `name`.
pub open spec fn nq(t: Tabs, name: Seq<u8>, v: Val) -> bool {
    exists|q: int| 0 <= q < t.n.len() && #[trigger] t.n[q][0] == v && t.n[q][1] == Val::Text(name)
}

/// Supplier key value `v` belongs to a supplier in a nation named `name`.
pub open spec fn sq(t: Tabs, name: Seq<u8>, v: Val) -> bool {
    exists|j: int| 0 <= j < t.s.len() && #[trigger] t.s[j][0] == v && nq(t, name, t.s[j][3])
}

/// The partsupp row `a` qualifies: its supplier is in a nation named `name`.
pub open spec fn rq(t: Tabs, name: Seq<u8>, a: Row) -> bool {
    sq(t, name, a[1])
}

/// `ps_supplycost * ps_availqty` of a partsupp row (coefficient of scale 2).
pub open spec fn pval(a: Row) -> int {
    ival(a[3]) * ival(a[2])
}

/// Per-row term over partsupp: `h(a)` on qualifying rows, else 0.
pub open spec fn on_rq(t: Tabs, name: Seq<u8>, h: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |a: Row| if rq(t, name, a) { h(a) } else { 0int }
}

/// Per-row term over the FROM rows: `h(x)` on rows satisfying the WHERE condition, else 0.
pub open spec fn on_qx(name: Seq<u8>, h: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if qualx(name, x) { h(x) } else { 0int }
}

/// `h` reads only the partsupp part (the first 5 values) of a joined row.
pub open spec fn ps_local(h: spec_fn(Row) -> int) -> bool {
    forall|a: Row, y: Row| a.len() == 5 ==> #[trigger] h(a + y) == h(a)
}

// ------------------------------------------------------------------------------------------------ sum lemmas

/// A sum whose terms are `w` on the rows satisfying `p` (at most one row) and 0 elsewhere is `w` when some row
/// satisfies `p`, else 0.
pub proof fn lemma_sum_unique(rows: Seq<Row>, p: spec_fn(Row) -> bool, w: int)
    requires forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && p(#[trigger] rows[i]) && p(#[trigger] rows[j]) ==> i == j,
    ensures
        sum_of(rows, |r: Row| if p(r) { w } else { 0int })
            == if exists|i: int| 0 <= i < rows.len() && #[trigger] p(rows[i]) { w } else { 0int },
    decreases rows.len(),
{
    let f = |r: Row| if p(r) { w } else { 0int };
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int, j: int| 0 <= i < ri.len() && 0 <= j < ri.len() && p(#[trigger] ri[i]) && p(#[trigger] ri[j]) implies i == j by {
            assert(ri[i] == rows[i] && ri[j] == rows[j]);
        }
        lemma_sum_unique(ri, p, w);
        let n = rows.len() - 1;
        if p(rows[n]) {
            // No earlier row satisfies `p`.
            assert(!exists|i: int| 0 <= i < ri.len() && #[trigger] p(ri[i])) by {
                if exists|i: int| 0 <= i < ri.len() && #[trigger] p(ri[i]) {
                    let i = choose|i: int| 0 <= i < ri.len() && #[trigger] p(ri[i]);
                    assert(ri[i] == rows[i]);
                }
            }
            assert(p(rows[n]));
        } else {
            if exists|i: int| 0 <= i < ri.len() && #[trigger] p(ri[i]) {
                let i = choose|i: int| 0 <= i < ri.len() && #[trigger] p(ri[i]);
                assert(ri[i] == rows[i]);
            }
            if exists|i: int| 0 <= i < rows.len() && #[trigger] p(rows[i]) {
                let i = choose|i: int| 0 <= i < rows.len() && #[trigger] p(rows[i]);
                assert(i < n);
                assert(ri[i] == rows[i]);
            }
        }
    }
}

/// Pointwise `f <= h` gives `sum_of(f) <= sum_of(h)`.
pub proof fn lemma_sum_mono(rows: Seq<Row>, f: spec_fn(Row) -> int, h: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) <= h(rows[i]),
    ensures sum_of(rows, f) <= sum_of(rows, h),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies f(#[trigger] ri[i]) <= h(ri[i]) by {
            assert(ri[i] == rows[i]);
        }
        lemma_sum_mono(ri, f, h);
        assert(f(rows[rows.len() - 1]) <= h(rows[rows.len() - 1]));
    }
}

/// Nonnegative terms give a nonnegative sum.
pub proof fn lemma_sum_nonneg(rows: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) >= 0,
    ensures sum_of(rows, f) >= 0,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies f(#[trigger] ri[i]) >= 0 by {
            assert(ri[i] == rows[i]);
        }
        lemma_sum_nonneg(ri, f);
        assert(f(rows[rows.len() - 1]) >= 0);
    }
}

// ------------------------------------------------------------------------------------------------ product to partsupp

/// For one partsupp row `a` and one supplier row `b`: the nation rows joined to `a ++ b` contribute `h(a)` once
/// when `a` joins `b` and `b`'s nation is named `name`, else nothing.
proof fn lemma_nation_sum(t: Tabs, name: Seq<u8>, h: spec_fn(Row) -> int, a: Row, b: Row)
    requires tabs_typed(t), keys_unique(t), ps_local(h), a.len() == 5, b.len() == 7,
    ensures
        sum_of(t.n, |c: Row| on_qx(name, h)((a + b) + c))
            == if a[1] == b[0] && nq(t, name, b[3]) { h(a) } else { 0int },
{
    let w = h(a);
    let p = |c: Row| a[1] == b[0] && b[3] == c[0] && c[1] == Val::Text(name);
    let f1 = |c: Row| on_qx(name, h)((a + b) + c);
    let f2 = |c: Row| if p(c) { w } else { 0int };
    assert forall|q: int| 0 <= q < t.n.len() implies f1(#[trigger] t.n[q]) == f2(t.n[q]) by {
        let c = t.n[q];
        assert(n_typed(c));
        let x = (a + b) + c;
        assert(x =~= a + (b + c));
        assert(h(a + (b + c)) == h(a));
        assert(x[1] == a[1] && x[5] == b[0] && x[8] == b[3] && x[12] == c[0] && x[13] == c[1]);
    }
    lemma_sum_of_ext(t.n, f1, f2);
    assert forall|i: int, j: int| 0 <= i < t.n.len() && 0 <= j < t.n.len() && p(#[trigger] t.n[i]) && p(#[trigger] t.n[j]) implies i == j by {
        assert(t.n[i][0] == t.n[j][0]);
    }
    lemma_sum_unique(t.n, p, w);
    if a[1] == b[0] && nq(t, name, b[3]) {
        let q = choose|q: int| 0 <= q < t.n.len() && #[trigger] t.n[q][0] == b[3] && t.n[q][1] == Val::Text(name);
        assert(p(t.n[q]));
    } else {
        if exists|i: int| 0 <= i < t.n.len() && #[trigger] p(t.n[i]) {
            let i = choose|i: int| 0 <= i < t.n.len() && #[trigger] p(t.n[i]);
            assert(t.n[i][0] == b[3]);
        }
    }
}

/// For one partsupp row `a`: the (supplier, nation) pairs joined to `a` contribute `h(a)` once when `a`
/// qualifies, else nothing.
proof fn lemma_ps_row_sum(t: Tabs, name: Seq<u8>, h: spec_fn(Row) -> int, a: Row)
    requires tabs_typed(t), keys_unique(t), ps_local(h), a.len() == 5,
    ensures
        sum_of(t.s, |b: Row| sum_of(t.n, |c: Row| on_qx(name, h)((a + b) + c))) == on_rq(t, name, h)(a),
{
    let w = h(a);
    let p = |b: Row| a[1] == b[0] && nq(t, name, b[3]);
    let f1 = |b: Row| sum_of(t.n, |c: Row| on_qx(name, h)((a + b) + c));
    let f2 = |b: Row| if p(b) { w } else { 0int };
    assert forall|j: int| 0 <= j < t.s.len() implies f1(#[trigger] t.s[j]) == f2(t.s[j]) by {
        assert(s_typed(t.s[j]));
        lemma_nation_sum(t, name, h, a, t.s[j]);
    }
    lemma_sum_of_ext(t.s, f1, f2);
    assert forall|i: int, j: int| 0 <= i < t.s.len() && 0 <= j < t.s.len() && p(#[trigger] t.s[i]) && p(#[trigger] t.s[j]) implies i == j by {
        assert(t.s[i][0] == t.s[j][0]);
    }
    lemma_sum_unique(t.s, p, w);
    if rq(t, name, a) {
        let j = choose|j: int| 0 <= j < t.s.len() && #[trigger] t.s[j][0] == a[1] && nq(t, name, t.s[j][3]);
        assert(p(t.s[j]));
    } else {
        if exists|i: int| 0 <= i < t.s.len() && #[trigger] p(t.s[i]) {
            let i = choose|i: int| 0 <= i < t.s.len() && #[trigger] p(t.s[i]);
            assert(t.s[i][0] == a[1]);
        }
    }
}

/// A sum over the FROM rows of a term reading only the partsupp part, on rows satisfying the WHERE condition, is
/// the same term summed over the qualifying partsupp rows.
pub proof fn lemma_xsum(t: Tabs, name: Seq<u8>, h: spec_fn(Row) -> int)
    requires tabs_typed(t), keys_unique(t), ps_local(h),
    ensures sum_of(xs(t), on_qx(name, h)) == sum_of(t.ps, on_rq(t, name, h)),
{
    let f = on_qx(name, h);
    let f2 = |y: Row| sum_of(t.n, |c: Row| f(y + c));
    lemma_sum_of_product(product_rows(t.ps, t.s), t.n, f);
    lemma_sum_of_product(t.ps, t.s, f2);
    let f3 = |a: Row| sum_of(t.s, |b: Row| f2(a + b));
    assert forall|k: int| 0 <= k < t.ps.len() implies f3(#[trigger] t.ps[k]) == on_rq(t, name, h)(t.ps[k]) by {
        let a = t.ps[k];
        assert(ps_typed(a));
        lemma_ps_row_sum(t, name, h, a);
        let g1 = |b: Row| f2(a + b);
        let g2 = |b: Row| sum_of(t.n, |c: Row| on_qx(name, h)((a + b) + c));
        assert forall|j: int| 0 <= j < t.s.len() implies g1(#[trigger] t.s[j]) == g2(t.s[j]) by {
            let b = t.s[j];
            let e1 = |c: Row| f((a + b) + c);
            let e2 = |c: Row| on_qx(name, h)((a + b) + c);
            assert forall|q: int| 0 <= q < t.n.len() implies e1(#[trigger] t.n[q]) == e2(t.n[q]) by {}
            lemma_sum_of_ext(t.n, e1, e2);
        }
        lemma_sum_of_ext(t.s, g1, g2);
    }
    lemma_sum_of_ext(t.ps, f3, on_rq(t, name, h));
}

// ------------------------------------------------------------------------------------------------ the accumulators

/// The value of group key `k` on a partsupp row (`h` of `lemma_xsum` for gsum).
pub open spec fn key_val(k: Row) -> spec_fn(Row) -> int {
    |a: Row| if seq![a[0]] == k { pval(a) } else { 0int }
}

pub open spec fn key_one(k: Row) -> spec_fn(Row) -> int {
    |a: Row| if seq![a[0]] == k { 1int } else { 0int }
}

pub open spec fn key_abs(k: Row) -> spec_fn(Row) -> int {
    |a: Row| if seq![a[0]] == k { abs(pval(a)) } else { 0int }
}

pub open spec fn all_val() -> spec_fn(Row) -> int {
    |a: Row| pval(a)
}

pub open spec fn all_one() -> spec_fn(Row) -> int {
    |a: Row| 1int
}

pub open spec fn all_abs() -> spec_fn(Row) -> int {
    |a: Row| abs(pval(a))
}

/// The accumulators of the grouped and the scalar normal form are sums over the qualifying partsupp rows.
pub proof fn lemma_accs(t: Tabs, name: Seq<u8>, k: Row)
    requires tabs_typed(t), keys_unique(t),
    ensures
        gsum(gq(name), xs(t), k, 0) == sum_of(t.ps, on_rq(t, name, key_val(k))),
        gcount(gq(name), xs(t), k) == sum_of(t.ps, on_rq(t, name, key_one(k))),
        gabs(gq(name), xs(t), k, 0) == sum_of(t.ps, on_rq(t, name, key_abs(k))),
        gsum(gs(name), xs(t), Seq::<Val>::empty(), 0) == sum_of(t.ps, on_rq(t, name, all_val())),
        gcount(gs(name), xs(t), Seq::<Val>::empty()) == sum_of(t.ps, on_rq(t, name, all_one())),
        gabs(gs(name), xs(t), Seq::<Val>::empty(), 0) == sum_of(t.ps, on_rq(t, name, all_abs())),
{
    let g = gq(name);
    let g2 = gs(name);
    let e = Seq::<Val>::empty();
    let x = xs(t);
    lemma_acc_sum_of(g, x, k, 0);
    lemma_acc_sum_of(g2, x, e, 0);
    // Each accumulator term is `on_qx` of a term reading only the partsupp part.
    assert forall|a: Row, y: Row| a.len() == 5 implies #[trigger] key_val(k)(a + y) == key_val(k)(a) by {
        assert((a + y)[0] == a[0] && (a + y)[2] == a[2] && (a + y)[3] == a[3]);
    }
    assert forall|a: Row, y: Row| a.len() == 5 implies #[trigger] key_one(k)(a + y) == key_one(k)(a) by {
        assert((a + y)[0] == a[0]);
    }
    assert forall|a: Row, y: Row| a.len() == 5 implies #[trigger] key_abs(k)(a + y) == key_abs(k)(a) by {
        assert((a + y)[0] == a[0] && (a + y)[2] == a[2] && (a + y)[3] == a[3]);
    }
    assert forall|a: Row, y: Row| a.len() == 5 implies #[trigger] all_val()(a + y) == all_val()(a) by {
        assert((a + y)[2] == a[2] && (a + y)[3] == a[3]);
    }
    assert forall|a: Row, y: Row| a.len() == 5 implies #[trigger] all_abs()(a + y) == all_abs()(a) by {
        assert((a + y)[2] == a[2] && (a + y)[3] == a[3]);
    }
    assert(ps_local(all_one()));
    lemma_sum_of_ext(x, sum_term(g, k, 0), on_qx(name, key_val(k)));
    lemma_sum_of_ext(x, count_term(g, k), on_qx(name, key_one(k)));
    lemma_sum_of_ext(x, abs_term(g, k, 0), on_qx(name, key_abs(k)));
    lemma_sum_of_ext(x, sum_term(g2, e, 0), on_qx(name, all_val()));
    lemma_sum_of_ext(x, count_term(g2, e), on_qx(name, all_one()));
    lemma_sum_of_ext(x, abs_term(g2, e, 0), on_qx(name, all_abs()));
    lemma_xsum(t, name, key_val(k));
    lemma_xsum(t, name, key_one(k));
    lemma_xsum(t, name, key_abs(k));
    lemma_xsum(t, name, all_val());
    lemma_xsum(t, name, all_one());
    lemma_xsum(t, name, all_abs());
}

/// The mass of the scalar group bounds every group's mass, so it gives `group_caps` of both normal forms.
pub proof fn lemma_caps(t: Tabs, name: Seq<u8>)
    requires sum_of(xs(t), abs_term(gs(name), Seq::<Val>::empty(), 0)) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
    ensures group_caps(gq(name), xs(t)), group_caps(gs(name), xs(t)),
{
    let g = gq(name);
    let g2 = gs(name);
    let e = Seq::<Val>::empty();
    let x = xs(t);
    lemma_acc_sum_of(g2, x, e, 0);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, x, k, j) <= crate::link::expr::i128_max() by {
        assert(j == 0);
        lemma_acc_sum_of(g, x, k, 0);
        assert forall|i: int| 0 <= i < x.len() implies abs_term(g, k, 0)(#[trigger] x[i]) <= abs_term(g2, e, 0)(x[i]) by {}
        lemma_sum_mono(x, abs_term(g, k, 0), abs_term(g2, e, 0));
    }
    assert forall|k: Row, j: int| 0 <= j < g2.aggs.len() && !(g2.aggs[j] is Count) implies #[trigger] gabs(g2, x, k, j) <= crate::link::expr::i128_max() by {
        assert(j == 0);
        lemma_acc_sum_of(g2, x, k, 0);
        assert forall|i: int| 0 <= i < x.len() implies abs_term(g2, k, 0)(#[trigger] x[i]) <= abs_term(g2, e, 0)(x[i]) by {}
        lemma_sum_mono(x, abs_term(g2, k, 0), abs_term(g2, e, 0));
    }
}

} // verus!
