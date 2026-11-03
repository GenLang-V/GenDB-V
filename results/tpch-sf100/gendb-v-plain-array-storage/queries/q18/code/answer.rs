//! From the qualifying orders and the selected rows to the fixed claim (`lemma_answer`).
//!
//! The executable code establishes, over the stored columns only: `groups` lists every qualifying order exactly
//! once (`groups_complete`) and `sel` is a sorted top-100 of the groups' output rows (`top_rows_ok`). For every
//! database bound to the parts this is an allowed output of the statement: the body is the normal form's result
//! rows (`lemma_denotation`, inside the SUM capacity `lemma_caps`), whose multiset is the groups' rows
//! (`lemma_rows_multiset`), and a sorted top-n is a slice of a sorted permutation (`common::topk_spec`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::expr::lemma_compare_num;
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok};
use crate::agent::tables::*;
use crate::agent::common::keysum::*;
use crate::agent::subquery::*;
use crate::agent::denotation::*;
use crate::agent::groups::*;
use crate::agent::common::topk_spec::lemma_topk_slice;

verus! {

/// The output row of orders row `j`'s group: `c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice, sum_qty`.
pub open spec fn group_row(sv: StoresView, j: int) -> Row {
    order_key(sv, j).push(Val::Num { coeff: order_sum(sv, j), scale: 2 })
}

/// `groups` lists, without repetition, exactly the qualifying orders.
pub open spec fn groups_complete(sv: StoresView, ps: Seq<Literal>, groups: Seq<int>) -> bool {
    &&& groups.no_duplicates()
    &&& forall|t: int| 0 <= t < groups.len() ==> 0 <= #[trigger] groups[t] < n_o(sv) && ord_ok(sv, ps, groups[t])
    &&& forall|j: int| 0 <= j < n_o(sv) && #[trigger] ord_ok(sv, ps, j) ==> groups.contains(j)
}

/// The order of two output rows on the ORDER BY keys: total price descending, then date ascending.
pub open spec fn row_cmp(p1: int, d1: int, p2: int, d2: int) -> int {
    if p1 > p2 { -1 } else if p1 < p2 { 1 } else if d1 < d2 { -1 } else if d1 > d2 { 1 } else { 0 }
}

/// `sel` is a sorted top-100 of the groups' rows: `min(100, |groups|)` distinct groups, sorted by the ORDER BY
/// keys, and no other group sorting strictly before the last selected one.
pub open spec fn top_rows_ok(sv: StoresView, groups: Seq<int>, sel: Seq<int>) -> bool {
    let rows = sel.map_values(|j: int| group_row(sv, j));
    &&& sel.no_duplicates()
    &&& forall|t: int| 0 <= t < sel.len() ==> groups.contains(#[trigger] sel[t])
    &&& sel.len() == if groups.len() <= 100 { groups.len() as int } else { 100 }
    &&& sorted_by(q_order_keys(), rows)
    &&& sel.len() > 0 ==> forall|j: int| #[trigger] groups.contains(j) && !sel.contains(j)
            ==> keys_cmp(q_order_keys(), rows.last(), group_row(sv, j)) <= 0
}

/// The ORDER BY comparison of two group rows is `row_cmp` of their prices and stored dates.
pub proof fn lemma_group_row_cmp(sv: StoresView, j1: int, j2: int)
    ensures keys_cmp(q_order_keys(), group_row(sv, j1), group_row(sv, j2))
        == row_cmp(otp(sv)[j1] as int, od(sv)[j1] as int, otp(sv)[j2] as int, od(sv)[j2] as int),
{
    let keys = q_order_keys();
    let (r1, r2) = (group_row(sv, j1), group_row(sv, j2));
    let (p1, p2) = (otp(sv)[j1] as int, otp(sv)[j2] as int);
    let (d1, d2) = (od(sv)[j1] as int, od(sv)[j2] as int);
    assert(r1[4] == Val::Num { coeff: p1, scale: 2 } && r2[4] == Val::Num { coeff: p2, scale: 2 });
    assert(r1[3] == Val::Date(d1 - 10957) && r2[3] == Val::Date(d2 - 10957));
    lemma_compare_num(p1, 2, p2, 2);
    assert(pow10(0) == 1) by (compute);
    assert(align(p1, 2, 2) == p1 && align(p2, 2, 2) == p2);
    let c0 = key_cmp(keys[0], r1, r2);
    assert(c0 == -sign(p1 - p2));
    let c1 = key_cmp(keys[1], r1, r2);
    assert(c1 == sign((d1 - 10957) - (d2 - 10957)));
    let k1 = keys.drop_first();
    assert(k1 =~= seq![keys[1]]);
    assert(k1.drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(k1.drop_first(), r1, r2) == 0);
    assert(keys_cmp(k1, r1, r2) == c1);
}

/// Output rows of different orders differ (their third column is the unique order key).
pub proof fn lemma_group_row_injective(sv: StoresView, db: Database, a: int, b: int)
    requires bound_db(sv, db), 0 <= a < n_o(sv), 0 <= b < n_o(sv), group_row(sv, a) == group_row(sv, b),
    ensures a == b,
{
    lemma_keys_unique(sv, db);
    lemma_parts_shape(sv, db);
    assert(group_row(sv, a)[2] == order_key(sv, a)[2]);
    assert(group_row(sv, b)[2] == order_key(sv, b)[2]);
    assert(Val::Int(ok(sv)[a] as int) == Val::Int(ok(sv)[b] as int));
    assert(ok(sv)[a] == ok(sv)[b]);
}

/// The group rows have the ORDER BY key families (numeric, date).
pub proof fn lemma_group_row_keys(sv: StoresView, j: int)
    ensures keys_ok(q_order_keys(), seq![1int, 2int], group_row(sv, j)),
{
    let keys = q_order_keys();
    let fams = seq![1int, 2int];
    let r = group_row(sv, j);
    assert(key_ok(keys[0], fams[0], r));
    assert(key_ok(keys[1], fams[1], r));
}

/// The normal form's output row of order `j`'s key is the group row.
pub proof fn lemma_out_row(sv: StoresView, db: Database, ps: Seq<Literal>, j: int)
    requires bound_db(sv, db), 0 <= j < n_o(sv), ord_ok(sv, ps, j),
    ensures out_row(q_spec(sv, ps), q_xs(db), order_key(sv, j)) == group_row(sv, j),
{
    let (g, xs, k) = (q_spec(sv, ps), q_xs(db), order_key(sv, j));
    lemma_order_group(sv, db, ps, j);
    let full = full_row(g, xs, k);
    assert(agg_outs(g, xs, k) =~= seq![Val::Num { coeff: gsum(g, xs, k, 0), scale: 2 }]);
    assert(full =~= group_row(sv, j));
    assert forall|m: int| 0 <= m < g.outs.len() implies #[trigger] g.outs[m] == m by {
        if m == 0 {} else if m == 1 {} else if m == 2 {} else if m == 3 {} else if m == 4 {} else {}
    }
    lemma_select_identity(full, g.outs);
}

/// The rows of all groups and the normal form's result rows are the same multiset.
pub proof fn lemma_rows_multiset(sv: StoresView, db: Database, ps: Seq<Literal>, groups: Seq<int>)
    requires bound_db(sv, db), groups_complete(sv, ps, groups),
    ensures
        groups.map_values(|j: int| group_row(sv, j)).no_duplicates(),
        groups.map_values(|j: int| group_row(sv, j)).to_multiset() == result_rows(q_spec(sv, ps), q_xs(db)).to_multiset(),
{
    let (g, xs) = (q_spec(sv, ps), q_xs(db));
    let all = groups.map_values(|j: int| group_row(sv, j));
    let gk = gkeys(g, xs);
    let res = result_rows(g, xs);
    lemma_gkeys(g, xs);
    assert forall|a: int, b: int| 0 <= a < all.len() && 0 <= b < all.len() && a != b implies all[a] != all[b] by {
        if all[a] == all[b] {
            lemma_group_row_injective(sv, db, groups[a], groups[b]);
        }
    }
    assert forall|a: int, b: int| 0 <= a < res.len() && 0 <= b < res.len() && a != b implies res[a] != res[b] by {
        if res[a] == res[b] {
            let (ka, kb) = (gk[a], gk[b]);
            assert(gk.contains(ka) && gk.contains(kb));
            let ja = lemma_group_is_order(sv, db, ps, ka);
            let jb = lemma_group_is_order(sv, db, ps, kb);
            lemma_out_row(sv, db, ps, ja);
            lemma_out_row(sv, db, ps, jb);
            lemma_group_row_injective(sv, db, ja, jb);
        }
    }
    assert forall|x: Row| #[trigger] all.contains(x) <==> res.contains(x) by {
        if all.contains(x) {
            let t = choose|t: int| 0 <= t < all.len() && all[t] == x;
            let j = groups[t];
            lemma_order_group(sv, db, ps, j);
            assert(kcount(lk(sv), ok(sv)[j], 0, n_l(sv)) > 0);
            assert(gk.contains(order_key(sv, j)));
            let u = choose|u: int| 0 <= u < gk.len() && gk[u] == order_key(sv, j);
            lemma_out_row(sv, db, ps, j);
            assert(res[u] == x);
        }
        if res.contains(x) {
            let u = choose|u: int| 0 <= u < res.len() && res[u] == x;
            assert(gk.contains(gk[u]));
            let j = lemma_group_is_order(sv, db, ps, gk[u]);
            lemma_out_row(sv, db, ps, j);
            assert(groups.contains(j));
            let t = choose|t: int| 0 <= t < groups.len() && groups[t] == j;
            assert(all[t] == x);
        }
    }
    lemma_nodup_same_multiset(all, res);
}

/// The answer: the selected rows are an allowed output of the statement on every database bound to the parts.
pub proof fn lemma_answer(sv: StoresView, db: Database, ps: Seq<Literal>, groups: Seq<int>, sel: Seq<int>)
    requires
        bound_db(sv, db), small(sv), param_domain(ps),
        groups_complete(sv, ps, groups),
        top_rows_ok(sv, groups, sel),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(sel.map_values(|j: int| group_row(sv, j)))),
{
    let (g, xs) = (q_spec(sv, ps), q_xs(db));
    let keys = q_order_keys();
    let fams = seq![1int, 2int];
    let all = groups.map_values(|j: int| group_row(sv, j));
    let out = sel.map_values(|j: int| group_row(sv, j));
    lemma_caps(sv, db, ps);
    lemma_denotation(sv, db, ps);
    lemma_query_shape(ps);
    lemma_rows_multiset(sv, db, ps, groups);
    assert(all_keys_ok(keys, fams, all)) by {
        assert forall|i: int| 0 <= i < all.len() implies keys_ok(keys, fams, #[trigger] all[i]) by {
            lemma_group_row_keys(sv, groups[i]);
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
                assert(groups.contains(sel[a]) && groups.contains(sel[b]));
                let ta = choose|t: int| 0 <= t < groups.len() && groups[t] == sel[a];
                let tb = choose|t: int| 0 <= t < groups.len() && groups[t] == sel[b];
                lemma_group_row_injective(sv, db, sel[a], sel[b]);
            }
        }
    }
    if out.len() > 0 {
        assert forall|x: Row| #[trigger] all.contains(x) && !out.contains(x) implies keys_cmp(keys, out.last(), x) <= 0 by {
            let t = choose|t: int| 0 <= t < all.len() && all[t] == x;
            let j = groups[t];
            assert(groups.contains(j));
            if sel.contains(j) {
                let u = choose|u: int| 0 <= u < sel.len() && sel[u] == j;
                assert(out[u] == x);
            }
        }
    }
    lemma_topk_slice(keys, fams, all, out, 100);
    let p = choose|p: Seq<Row>| #![trigger sorted_by(keys, p)]
        p.to_multiset() == all.to_multiset() && sorted_by(keys, p) && out == slice_rows(p, 0, Some(100nat));
    assert(p.to_multiset() == result_rows(g, xs).to_multiset());
    assert(sorted_by(query_spec_at(ps).keys, p));
}

} // verus!
