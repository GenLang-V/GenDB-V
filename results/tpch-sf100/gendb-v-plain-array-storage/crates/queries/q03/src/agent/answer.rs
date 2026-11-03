//! From the computed groups and the selected rows to the fixed claim (`lemma_answer`).
//!
//! The executable code establishes, over the stored columns only: `groups` lists every qualifying order hit by some
//! lineitem row exactly once (`groups_complete`), each group's absolute mass fits `i128` (`groups_capped`), and
//! `sel` is a sorted top-10 of the groups' output rows (`top_rows_ok`). For every database bound to the parts this
//! is an allowed output of the statement: the body is the normal form's result rows (`lemma_denotation`, inside
//! `group_caps`), whose multiset is the groups' rows (`agent::groups`), and a sorted top-n is a slice of a sorted
//! permutation (`common::topk_spec`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok, key_val};
use crate::bridge::typing::val_family;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::*;
use crate::agent::groups::*;
use crate::agent::common::topk_spec::lemma_topk_slice;

verus! {

/// The output row of order `j`'s group.
pub open spec fn group_row(sv: StoresView, ps: Seq<Literal>, j: int) -> Row {
    order_row(sv, j, order_sum(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv)))
}

/// `groups` lists, without repetition, exactly the qualifying orders that some lineitem row hits.
pub open spec fn groups_complete(sv: StoresView, ps: Seq<Literal>, groups: Seq<int>) -> bool {
    &&& groups.no_duplicates()
    &&& forall|t: int| 0 <= t < groups.len() ==> {
            &&& 0 <= #[trigger] groups[t] < n_o(sv)
            &&& order_ok(sv, seg_of(ps), dl_of(ps), groups[t])
            &&& order_count(sv, seg_of(ps), dl_of(ps), groups[t], 0, n_l(sv)) > 0
        }
    &&& forall|j: int| 0 <= j < n_o(sv) && order_ok(sv, seg_of(ps), dl_of(ps), j)
            && #[trigger] order_count(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv)) > 0 ==> groups.contains(j)
}

/// Every group's absolute mass fits `i128` (the SUM capacity condition of the statement).
pub open spec fn groups_capped(sv: StoresView, ps: Seq<Literal>, groups: Seq<int>) -> bool {
    forall|t: int| 0 <= t < groups.len() ==> #[trigger] order_abs(sv, seg_of(ps), dl_of(ps), groups[t], 0, n_l(sv)) <= i128_max()
}

/// `sel` is a sorted top-10 of the groups' rows: `min(10, |groups|)` distinct groups, sorted by the ORDER BY keys,
/// and no other group sorting strictly before the last selected one.
pub open spec fn top_rows_ok(sv: StoresView, ps: Seq<Literal>, groups: Seq<int>, sel: Seq<int>) -> bool {
    let rows = sel.map_values(|j: int| group_row(sv, ps, j));
    &&& sel.no_duplicates()
    &&& forall|t: int| 0 <= t < sel.len() ==> groups.contains(#[trigger] sel[t])
    &&& sel.len() == if groups.len() <= 10 { groups.len() as int } else { 10 }
    &&& sorted_by(q3_order_keys(), rows)
    &&& sel.len() > 0 ==> forall|j: int| #[trigger] groups.contains(j) && !sel.contains(j)
            ==> keys_cmp(q3_order_keys(), rows.last(), group_row(sv, ps, j)) <= 0
}

/// Output rows of different orders differ (their first column is the unique order key).
pub proof fn lemma_group_row_injective(sv: StoresView, db: Database, ps: Seq<Literal>, a: int, b: int)
    requires bound_db(sv, db), 0 <= a < n_o(sv), 0 <= b < n_o(sv), group_row(sv, ps, a) == group_row(sv, ps, b),
    ensures a == b,
{
    lemma_keys_unique(sv, db);
    assert(group_row(sv, ps, a)[0] == group_row(sv, ps, b)[0]);
}

/// The group rows have the ORDER BY key families (numeric revenue, date).
pub proof fn lemma_group_row_keys(sv: StoresView, ps: Seq<Literal>, j: int)
    ensures keys_ok(q3_order_keys(), seq![1int, 2int], group_row(sv, ps, j)),
{
    let keys = q3_order_keys();
    let fams = seq![1int, 2int];
    let r = group_row(sv, ps, j);
    assert(key_ok(keys[0], fams[0], r));
    assert(key_ok(keys[1], fams[1], r));
}

/// The SUM capacity condition of the statement holds when every group's absolute mass fits.
pub proof fn lemma_caps(sv: StoresView, db: Database, ps: Seq<Literal>, groups: Seq<int>)
    requires bound_db(sv, db), param_domain(ps), groups_complete(sv, ps, groups), groups_capped(sv, ps, groups),
    ensures group_caps(q3_spec(ps), q3_xs(db)),
{
    let (g, xs) = (q3_spec(ps), q3_xs(db));
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 0);
        if gcount(g, xs, k) == 0 {
            lemma_zero_count(g, xs, k, 0);
        } else {
            let jj = lemma_group_is_order(sv, db, ps, k);
            lemma_order_group(sv, db, ps, jj);
            let t = choose|t: int| 0 <= t < groups.len() && groups[t] == jj;
            assert(order_abs(sv, seg_of(ps), dl_of(ps), groups[t], 0, n_l(sv)) <= i128_max());
        }
    }
}

/// The normal form's output row of order `j`'s key is the group row.
pub proof fn lemma_out_row(sv: StoresView, db: Database, ps: Seq<Literal>, j: int)
    requires
        bound_db(sv, db), param_domain(ps), 0 <= j < n_o(sv),
        order_ok(sv, seg_of(ps), dl_of(ps), j),
        order_count(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv)) > 0,
    ensures out_row(q3_spec(ps), q3_xs(db), order_key(sv, j)) == group_row(sv, ps, j),
{
    let (g, xs, k) = (q3_spec(ps), q3_xs(db), order_key(sv, j));
    lemma_order_group(sv, db, ps, j);
    let full = full_row(g, xs, k);
    assert(agg_outs(g, xs, k)[0] == (Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 }));
    assert(full[0] == k[0] && full[1] == k[1] && full[2] == k[2] && full[3] == agg_outs(g, xs, k)[0]);
    assert(out_row(g, xs, k) =~= group_row(sv, ps, j));
}

/// The rows of all groups and the normal form's result rows are the same multiset.
pub proof fn lemma_rows_multiset(sv: StoresView, db: Database, ps: Seq<Literal>, groups: Seq<int>)
    requires bound_db(sv, db), param_domain(ps), groups_complete(sv, ps, groups),
    ensures
        groups.map_values(|j: int| group_row(sv, ps, j)).no_duplicates(),
        groups.map_values(|j: int| group_row(sv, ps, j)).to_multiset() == result_rows(q3_spec(ps), q3_xs(db)).to_multiset(),
{
    let (g, xs) = (q3_spec(ps), q3_xs(db));
    let all = groups.map_values(|j: int| group_row(sv, ps, j));
    let gk = gkeys(g, xs);
    let res = result_rows(g, xs);
    lemma_gkeys(g, xs);
    // the group rows have no duplicates
    assert forall|a: int, b: int| 0 <= a < all.len() && 0 <= b < all.len() && a != b implies all[a] != all[b] by {
        if all[a] == all[b] {
            lemma_group_row_injective(sv, db, ps, groups[a], groups[b]);
        }
    }
    // the result rows: one per group key, the key is the row's 1st, 3rd and 4th value
    assert forall|a: int, b: int| 0 <= a < res.len() && 0 <= b < res.len() && a != b implies res[a] != res[b] by {
        if res[a] == res[b] {
            let (ka, kb) = (gk[a], gk[b]);
            assert(gk.contains(ka) && gk.contains(kb));
            let ja = lemma_group_is_order(sv, db, ps, ka);
            let jb = lemma_group_is_order(sv, db, ps, kb);
            lemma_out_row(sv, db, ps, ja);
            lemma_out_row(sv, db, ps, jb);
            lemma_group_row_injective(sv, db, ps, ja, jb);
        }
    }
    assert forall|x: Row| #[trigger] all.contains(x) <==> res.contains(x) by {
        if all.contains(x) {
            let t = choose|t: int| 0 <= t < all.len() && all[t] == x;
            let j = groups[t];
            lemma_order_group(sv, db, ps, j);
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

/// The answer: under the three column-level facts, the selected rows are an allowed output of the statement on
/// every database bound to the parts.
pub proof fn lemma_answer(sv: StoresView, db: Database, ps: Seq<Literal>, groups: Seq<int>, sel: Seq<int>)
    requires
        bound_db(sv, db), param_domain(ps),
        groups_complete(sv, ps, groups),
        groups_capped(sv, ps, groups),
        top_rows_ok(sv, ps, groups, sel),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(sel.map_values(|j: int| group_row(sv, ps, j)))),
{
    let (g, xs) = (q3_spec(ps), q3_xs(db));
    let keys = q3_order_keys();
    let fams = seq![1int, 2int];
    let all = groups.map_values(|j: int| group_row(sv, ps, j));
    let out = sel.map_values(|j: int| group_row(sv, ps, j));
    lemma_caps(sv, db, ps, groups);
    lemma_denotation(sv, db, ps);
    lemma_query_shape(ps);
    lemma_rows_multiset(sv, db, ps, groups);
    assert(all_keys_ok(keys, fams, all)) by {
        assert forall|i: int| 0 <= i < all.len() implies keys_ok(keys, fams, #[trigger] all[i]) by {
            lemma_group_row_keys(sv, ps, groups[i]);
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
                lemma_group_row_injective(sv, db, ps, sel[a], sel[b]);
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
    lemma_topk_slice(keys, fams, all, out, 10);
    let p = choose|p: Seq<Row>| #![trigger sorted_by(keys, p)]
        p.to_multiset() == all.to_multiset() && sorted_by(keys, p) && out == slice_rows(p, 0, Some(10nat));
    assert(p.to_multiset() == result_rows(g, xs).to_multiset());
    assert(sorted_by(query_spec_at(ps).keys, p));
}

} // verus!
