//! From the selected customers to the fixed claim's row outcome (`lemma_answer`).
//!
//! The executable code establishes, over the stored columns only: every group's absolute mass fits `i128`
//! (`groups_capped`) and `sel` is a sorted top-20 of the groups by revenue (`top_ok`). The groups are the customers
//! `a` with `is_group(a)`, listed once each in row order by `all_groups`; customer `a`'s output row is
//! `cust_row(a, ctot(a))`. For every database bound to the parts this is an allowed output of the statement: the
//! body is the normal form's result rows (`denot::lemma_denotation`, inside `group_caps`), whose multiset is the
//! groups' rows (`agent::groups`), and a sorted top-n is a slice of a sorted permutation (`common::topk_spec`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::numeric::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::expr::{i128_max, lemma_compare_num, lemma_align_same};
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok};
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::denot::*;
use crate::agent::groups::*;
use crate::agent::common::topk_spec::lemma_topk_slice;

verus! {

// ------------------------------------------------------------------------------------------------ the groups

/// The customers among rows `0..n` that are groups, in row order.
pub open spec fn glist(sv: StoresView, dlo: int, dhi: int, n: int) -> Seq<int>
    decreases n,
{
    if n <= 0 { Seq::empty() } else {
        let d = glist(sv, dlo, dhi, n - 1);
        if is_group(sv, dlo, dhi, n - 1) { d.push(n - 1) } else { d }
    }
}

/// All groups of the statement.
pub open spec fn all_groups(sv: StoresView, dlo: int, dhi: int) -> Seq<int> { glist(sv, dlo, dhi, n_c(sv)) }

pub proof fn lemma_glist(sv: StoresView, dlo: int, dhi: int, n: int)
    requires 0 <= n,
    ensures
        glist(sv, dlo, dhi, n).no_duplicates(),
        forall|x: int| #[trigger] glist(sv, dlo, dhi, n).contains(x) <==> 0 <= x < n && is_group(sv, dlo, dhi, x),
    decreases n,
{
    if n > 0 {
        lemma_glist(sv, dlo, dhi, n - 1);
        let d = glist(sv, dlo, dhi, n - 1);
        if is_group(sv, dlo, dhi, n - 1) {
            let e = d.push(n - 1);
            assert forall|x: int| #[trigger] e.contains(x) <==> 0 <= x < n && is_group(sv, dlo, dhi, x) by {
                if e.contains(x) {
                    let t = choose|t: int| 0 <= t < e.len() && e[t] == x;
                    if t < d.len() { assert(d[t] == x); assert(d.contains(x)); }
                }
                if 0 <= x < n && is_group(sv, dlo, dhi, x) {
                    if x < n - 1 {
                        assert(d.contains(x));
                        let t = choose|t: int| 0 <= t < d.len() && d[t] == x;
                        assert(e[t] == x);
                    } else {
                        assert(e[d.len() as int] == x);
                    }
                }
            }
            assert forall|a: int, b: int| 0 <= a < e.len() && 0 <= b < e.len() && a != b implies e[a] != e[b] by {
                if a < d.len() && b < d.len() {
                } else if a < d.len() {
                    assert(d.contains(d[a]));
                } else if b < d.len() {
                    assert(d.contains(d[b]));
                }
            }
        }
    }
}

/// Every group's absolute SUM mass fits `i128`.
pub open spec fn groups_capped(sv: StoresView, dlo: int, dhi: int) -> bool {
    forall|a: int| #[trigger] is_group(sv, dlo, dhi, a) ==> ctabs(sv, dlo, dhi, a) <= i128_max()
}

/// `sel` is a sorted top-20 of the groups by revenue: `min(20, #groups)` distinct groups, revenue not increasing,
/// and no other group with more revenue than the last selected one.
pub open spec fn top_ok(sv: StoresView, dlo: int, dhi: int, sel: Seq<int>) -> bool {
    &&& sel.no_duplicates()
    &&& forall|t: int| 0 <= t < sel.len() ==> is_group(sv, dlo, dhi, #[trigger] sel[t])
    &&& sel.len() == if all_groups(sv, dlo, dhi).len() <= 20 { all_groups(sv, dlo, dhi).len() as int } else { 20 }
    &&& forall|i: int, j: int| 0 <= i < j < sel.len() ==> ctot(sv, dlo, dhi, #[trigger] sel[i]) >= ctot(sv, dlo, dhi, #[trigger] sel[j])
    &&& sel.len() > 0 ==> forall|a: int| #[trigger] is_group(sv, dlo, dhi, a) && !sel.contains(a)
            ==> ctot(sv, dlo, dhi, sel.last()) >= ctot(sv, dlo, dhi, a)
}

/// The output row of group `a`.
pub open spec fn grow(sv: StoresView, dlo: int, dhi: int, a: int) -> Row { cust_row(sv, a, ctot(sv, dlo, dhi, a)) }

// ------------------------------------------------------------------------------------------------ rows and order

/// The ORDER BY comparison of two customer rows: by revenue, descending.
pub proof fn lemma_row_cmp(sv: StoresView, a: int, s1: int, b: int, s2: int)
    ensures
        (keys_cmp(q_order_keys(), cust_row(sv, a, s1), cust_row(sv, b, s2)) <= 0) == (s1 >= s2),
        keys_ok(q_order_keys(), seq![1int], cust_row(sv, a, s1)),
{
    let keys = q_order_keys();
    let (r1, r2) = (cust_row(sv, a, s1), cust_row(sv, b, s2));
    lemma_compare_num(s1, 4, s2, 4);
    lemma_align_same(s1, 4);
    lemma_align_same(s2, 4);
    assert(max_nat(4, 4) == 4);
    assert(keys.drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(Seq::<OrderKey>::empty(), r1, r2) == 0);
    assert(keys_cmp(keys.drop_first(), r1, r2) == 0);
    assert(key_cmp(keys[0], r1, r2) == -sign(s1 - s2));
    assert(keys_cmp(keys, r1, r2) == key_cmp(keys[0], r1, r2));
    assert(key_ok(keys[0], seq![1int][0], r1));
}

/// Output rows of different customers differ (their first column is the unique customer key).
pub proof fn lemma_grow_injective(sv: StoresView, db: Database, dlo: int, dhi: int, a: int, b: int)
    requires bound_db(sv, db), 0 <= a < n_c(sv), 0 <= b < n_c(sv), grow(sv, dlo, dhi, a) == grow(sv, dlo, dhi, b),
    ensures a == b,
{
    lemma_keys_unique(sv, db);
    assert(grow(sv, dlo, dhi, a)[0] == grow(sv, dlo, dhi, b)[0]);
}

/// The SUM capacity condition of the statement holds when every group's absolute mass fits.
pub proof fn lemma_caps(sv: StoresView, db: Database, pd: int, t1: int, dlo: int, dhi: int)
    requires bound_db(sv, db), win_of(dlo, dhi, pd, t1), groups_capped(sv, dlo, dhi),
    ensures group_caps(q_spec(pd, t1), q_xs(db)),
{
    let (g, xs) = (q_spec(pd, t1), q_xs(db));
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 0);
        if gcount(g, xs, k) == 0 {
            lemma_zero_count(g, xs, k, 0);
        } else {
            let a0 = lemma_group_is_cust(sv, db, pd, t1, dlo, dhi, k);
            lemma_cust_group(sv, db, pd, t1, dlo, dhi, a0);
        }
    }
}

/// The normal form's output row of group `a`'s key is the group row.
pub proof fn lemma_out_row(sv: StoresView, db: Database, pd: int, t1: int, dlo: int, dhi: int, a: int)
    requires bound_db(sv, db), win_of(dlo, dhi, pd, t1), is_group(sv, dlo, dhi, a),
    ensures out_row(q_spec(pd, t1), q_xs(db), ckey(sv, a)) == grow(sv, dlo, dhi, a),
{
    let (g, xs, k) = (q_spec(pd, t1), q_xs(db), ckey(sv, a));
    lemma_cust_group(sv, db, pd, t1, dlo, dhi, a);
    let full = full_row(g, xs, k);
    assert(agg_outs(g, xs, k)[0] == (Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 }));
    assert(full.len() == 8);
    assert(full[0] == k[0] && full[1] == k[1] && full[2] == k[2] && full[3] == k[3] && full[4] == k[4] && full[5] == k[5]
        && full[6] == k[6] && full[7] == agg_outs(g, xs, k)[0]);
    assert(out_row(g, xs, k) =~= grow(sv, dlo, dhi, a));
}

/// The rows of all groups and the normal form's result rows are the same multiset.
pub proof fn lemma_rows_multiset(sv: StoresView, db: Database, pd: int, t1: int, dlo: int, dhi: int)
    requires bound_db(sv, db), win_of(dlo, dhi, pd, t1),
    ensures
        all_groups(sv, dlo, dhi).map_values(|a: int| grow(sv, dlo, dhi, a)).no_duplicates(),
        all_groups(sv, dlo, dhi).map_values(|a: int| grow(sv, dlo, dhi, a)).to_multiset()
            == result_rows(q_spec(pd, t1), q_xs(db)).to_multiset(),
{
    let (g, xs) = (q_spec(pd, t1), q_xs(db));
    let groups = all_groups(sv, dlo, dhi);
    lemma_glist(sv, dlo, dhi, n_c(sv));
    let all = groups.map_values(|a: int| grow(sv, dlo, dhi, a));
    let gk = gkeys(g, xs);
    let res = result_rows(g, xs);
    lemma_gkeys(g, xs);
    assert forall|a: int, b: int| 0 <= a < all.len() && 0 <= b < all.len() && a != b implies all[a] != all[b] by {
        assert(groups.contains(groups[a]) && groups.contains(groups[b]));
        if all[a] == all[b] {
            lemma_grow_injective(sv, db, dlo, dhi, groups[a], groups[b]);
        }
    }
    assert forall|a: int, b: int| 0 <= a < res.len() && 0 <= b < res.len() && a != b implies res[a] != res[b] by {
        if res[a] == res[b] {
            let (ka, kb) = (gk[a], gk[b]);
            assert(gk.contains(ka) && gk.contains(kb));
            let ja = lemma_group_is_cust(sv, db, pd, t1, dlo, dhi, ka);
            let jb = lemma_group_is_cust(sv, db, pd, t1, dlo, dhi, kb);
            lemma_out_row(sv, db, pd, t1, dlo, dhi, ja);
            lemma_out_row(sv, db, pd, t1, dlo, dhi, jb);
            lemma_grow_injective(sv, db, dlo, dhi, ja, jb);
        }
    }
    assert forall|x: Row| #[trigger] all.contains(x) <==> res.contains(x) by {
        if all.contains(x) {
            let t = choose|t: int| 0 <= t < all.len() && all[t] == x;
            let a = groups[t];
            assert(groups.contains(a));
            lemma_cust_group(sv, db, pd, t1, dlo, dhi, a);
            assert(gk.contains(ckey(sv, a)));
            let u = choose|u: int| 0 <= u < gk.len() && gk[u] == ckey(sv, a);
            lemma_out_row(sv, db, pd, t1, dlo, dhi, a);
            assert(res[u] == x);
        }
        if res.contains(x) {
            let u = choose|u: int| 0 <= u < res.len() && res[u] == x;
            assert(gk.contains(gk[u]));
            let a = lemma_group_is_cust(sv, db, pd, t1, dlo, dhi, gk[u]);
            lemma_out_row(sv, db, pd, t1, dlo, dhi, a);
            assert(groups.contains(a));
            let t = choose|t: int| 0 <= t < groups.len() && groups[t] == a;
            assert(all[t] == x);
        }
    }
    lemma_nodup_same_multiset(all, res);
}

/// The answer: under the column-level facts, the selected rows are an allowed output of the statement on every
/// database bound to the parts.
pub proof fn lemma_answer(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int, dlo: int, dhi: int, sel: Seq<int>)
    requires
        bound_db(sv, db), param_domain(ps), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1), win_of(dlo, dhi, pd_of(ps), t1),
        groups_capped(sv, dlo, dhi),
        top_ok(sv, dlo, dhi, sel),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(sel.map_values(|a: int| grow(sv, dlo, dhi, a)))),
{
    let pd = pd_of(ps);
    let (g, xs) = (q_spec(pd, t1), q_xs(db));
    let keys = q_order_keys();
    let fams = seq![1int];
    let groups = all_groups(sv, dlo, dhi);
    lemma_glist(sv, dlo, dhi, n_c(sv));
    let all = groups.map_values(|a: int| grow(sv, dlo, dhi, a));
    let out = sel.map_values(|a: int| grow(sv, dlo, dhi, a));
    lemma_caps(sv, db, pd, t1, dlo, dhi);
    lemma_denotation(sv, db, ps, t1, dlo, dhi);
    lemma_query_shape(ps);
    lemma_rows_multiset(sv, db, pd, t1, dlo, dhi);
    assert(all_keys_ok(keys, fams, all)) by {
        assert forall|i: int| 0 <= i < all.len() implies keys_ok(keys, fams, #[trigger] all[i]) by {
            lemma_row_cmp(sv, groups[i], ctot(sv, dlo, dhi, groups[i]), groups[i], ctot(sv, dlo, dhi, groups[i]));
        }
    }
    assert forall|i: int| 0 <= i < out.len() implies all.contains(#[trigger] out[i]) by {
        assert(groups.contains(sel[i]));
        let t = choose|t: int| 0 <= t < groups.len() && groups[t] == sel[i];
        assert(all[t] == out[i]);
    }
    assert(out.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < out.len() && 0 <= b < out.len() && a != b implies out[a] != out[b] by {
            if out[a] == out[b] {
                assert(is_group(sv, dlo, dhi, sel[a]) && is_group(sv, dlo, dhi, sel[b]));
                lemma_grow_injective(sv, db, dlo, dhi, sel[a], sel[b]);
            }
        }
    }
    assert(sorted_by(keys, out)) by {
        assert forall|i: int, j: int| 0 <= i < j < out.len() implies keys_cmp(keys, #[trigger] out[i], #[trigger] out[j]) <= 0 by {
            assert(ctot(sv, dlo, dhi, sel[i]) >= ctot(sv, dlo, dhi, sel[j]));
            lemma_row_cmp(sv, sel[i], ctot(sv, dlo, dhi, sel[i]), sel[j], ctot(sv, dlo, dhi, sel[j]));
        }
    }
    if out.len() > 0 {
        assert forall|x: Row| #[trigger] all.contains(x) && !out.contains(x) implies keys_cmp(keys, out.last(), x) <= 0 by {
            let t = choose|t: int| 0 <= t < all.len() && all[t] == x;
            let a = groups[t];
            assert(groups.contains(a));
            if sel.contains(a) {
                let u = choose|u: int| 0 <= u < sel.len() && sel[u] == a;
                assert(out[u] == x);
            }
            assert(out.last() == grow(sv, dlo, dhi, sel.last()));
            lemma_row_cmp(sv, sel.last(), ctot(sv, dlo, dhi, sel.last()), a, ctot(sv, dlo, dhi, a));
        }
    }
    lemma_topk_slice(keys, fams, all, out, 20);
    let p = choose|p: Seq<Row>| #![trigger sorted_by(keys, p)]
        p.to_multiset() == all.to_multiset() && sorted_by(keys, p) && out == slice_rows(p, 0, Some(20nat));
    assert(p.to_multiset() == result_rows(g, xs).to_multiset());
    assert(sorted_by(query_spec_at(ps).keys, p));
}

} // verus!
