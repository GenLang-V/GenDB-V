//! From the per-group sums to the fixed claim (`lemma_answer`).
//!
//! The executable code establishes, over the stored columns only, the four groups' sums (`lines::lsum`, groups
//! 0..4 with keys `grp_key`) and outputs the non-empty groups in the order `out_grp` (`$1` first when `$1 <= $2`
//! in byte order). A key's accumulators are the sums of the groups with that key (`lemma_ksum_groups`); when
//! `$1 == $2` the groups 2 and 3 are empty (their tags would need a nation named `$2` but not `$1`,
//! `lemma_same_params`), so every non-empty group's key is its own (`lemma_out_group`). With the denotation
//! (`denotation::lemma_denotation`) and the product collapse (`groups::lemma_group_sums`) the output rows are a
//! sorted permutation of the statement's rows.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::scalar::compare;
use crate::spec::numeric::*;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::expr::{i128_max, lemma_compare_num};
use crate::link::outcome::{lemma_outcome_sorted, lemma_slice_whole};
use crate::bridge::order::lemma_lex_cmp_antisym;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::*;
use crate::agent::lines::*;
use crate::agent::groups::*;

verus! {

// ------------------------------------------------------------------------------------------------ keys and groups

/// The accumulators of key `k` as sums of the groups with that key.
pub open spec fn sum4(sv: StoresView, ps: Seq<Literal>, k: Row, w: int, n: int) -> int {
    (if grp_key(ps, 0) == k { lsum(sv, ps, 0, w, 0, n) } else { 0 })
        + (if grp_key(ps, 1) == k { lsum(sv, ps, 1, w, 0, n) } else { 0 })
        + (if grp_key(ps, 2) == k { lsum(sv, ps, 2, w, 0, n) } else { 0 })
        + (if grp_key(ps, 3) == k { lsum(sv, ps, 3, w, 0, n) } else { 0 })
}

/// Every row's group is one of 0..4.
proof fn lemma_grp_range(sv: StoresView, ps: Seq<Literal>, l: int)
    ensures 0 <= line_grp(sv, ps, l) < 4,
{
}

/// A key's sum is the sum of its groups' sums.
pub proof fn lemma_ksum_groups(sv: StoresView, ps: Seq<Literal>, k: Row, w: int, n: int)
    requires n >= 0,
    ensures ksum(sv, ps, k, w, n) == sum4(sv, ps, k, w, n),
    decreases n,
{
    if n > 0 {
        lemma_ksum_groups(sv, ps, k, w, n - 1);
        lemma_grp_range(sv, ps, n - 1);
    }
}

/// With `$1 == $2` every tag is 0 or 3, so a qualifying row is in group 0 or 1.
pub proof fn lemma_same_params(sv: StoresView, ps: Seq<Literal>, g: int, w: int, lo: int, hi: int)
    requires p1_of(ps) == p2_of(ps), 2 <= g,
    ensures lsum(sv, ps, g, w, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_same_params(sv, ps, g, w, lo, hi - 1);
        let l = hi - 1;
        let st = supp_tag(sv, ps, l_supp(sv, l));
        let ct = cust_tag(sv, ps, l_cust(sv, l));
        assert(st == 0 || st == 3);
        assert(ct == 0 || ct == 3);
    }
}

/// Counts and absolute sums of the groups are non-negative.
proof fn lemma_groups_nonneg(sv: StoresView, ps: Seq<Literal>, n: int)
    ensures
        forall|g: int| #[trigger] lsum(sv, ps, g, 0, 0, n) >= 0,
        forall|g: int| #[trigger] lsum(sv, ps, g, 2, 0, n) >= 0,
{
    assert forall|g: int| #[trigger] lsum(sv, ps, g, 0, 0, n) >= 0 by {
        lemma_lsum_bounds(sv, ps, g, 0, n);
    }
    assert forall|g: int| #[trigger] lsum(sv, ps, g, 2, 0, n) >= 0 by {
        lemma_lsum_bounds(sv, ps, g, 0, n);
    }
}

/// Two different groups with one key exist only when `$1 == $2`, and then one of them is 2 or 3.
proof fn lemma_key_collision(ps: Seq<Literal>, g: int, h: int)
    requires 0 <= g < 4, 0 <= h < 4, g != h, grp_key(ps, g) == grp_key(ps, h),
    ensures p1_of(ps) == p2_of(ps), g >= 2 || h >= 2,
{
    assert(grp_key(ps, g)[2] == grp_key(ps, h)[2]);
    assert(grp_key(ps, g)[0] == grp_key(ps, h)[0]);
    assert(grp_key(ps, g)[1] == grp_key(ps, h)[1]);
}

/// A non-empty group's key collects exactly that group's sums.
pub proof fn lemma_out_group(sv: StoresView, ps: Seq<Literal>, g: int, w: int, n: int)
    requires 0 <= g < 4, n >= 0, lsum(sv, ps, g, 0, 0, n) > 0,
    ensures ksum(sv, ps, grp_key(ps, g), w, n) == lsum(sv, ps, g, w, 0, n),
{
    lemma_ksum_groups(sv, ps, grp_key(ps, g), w, n);
    assert forall|h: int| 0 <= h < 4 && h != g && grp_key(ps, h) == grp_key(ps, g) implies
        #[trigger] lsum(sv, ps, h, w, 0, n) == 0 by {
        lemma_key_collision(ps, g, h);
        if g >= 2 {
            lemma_same_params(sv, ps, g, 0, 0, n);
        }
        lemma_same_params(sv, ps, h, w, 0, n);
    }
}

/// A key with a non-zero count is a non-empty group's key.
pub proof fn lemma_key_group(sv: StoresView, ps: Seq<Literal>, k: Row, n: int) -> (g: int)
    requires n >= 0, ksum(sv, ps, k, 0, n) > 0,
    ensures 0 <= g < 4, grp_key(ps, g) == k, lsum(sv, ps, g, 0, 0, n) > 0,
{
    lemma_ksum_groups(sv, ps, k, 0, n);
    lemma_groups_nonneg(sv, ps, n);
    if grp_key(ps, 0) == k && lsum(sv, ps, 0, 0, 0, n) > 0 { 0 }
    else if grp_key(ps, 1) == k && lsum(sv, ps, 1, 0, 0, n) > 0 { 1 }
    else if grp_key(ps, 2) == k && lsum(sv, ps, 2, 0, 0, n) > 0 { 2 }
    else { 3 }
}

/// Every key's absolute sum is within `i128` when every group's is.
proof fn lemma_key_caps(sv: StoresView, ps: Seq<Literal>, k: Row, n: int)
    requires n >= 0, forall|g: int| 0 <= g < 4 ==> #[trigger] lsum(sv, ps, g, 2, 0, n) <= i128_max(),
    ensures ksum(sv, ps, k, 2, n) <= i128_max(),
{
    lemma_ksum_groups(sv, ps, k, 2, n);
    lemma_groups_nonneg(sv, ps, n);
    if p1_of(ps) == p2_of(ps) {
        lemma_same_params(sv, ps, 2, 2, 0, n);
        lemma_same_params(sv, ps, 3, 2, 0, n);
        assert(grp_key(ps, 0) != grp_key(ps, 1)) by { assert(grp_key(ps, 0)[2] != grp_key(ps, 1)[2]); }
    } else {
        assert forall|g: int, h: int| 0 <= g < h < 4 implies grp_key(ps, g) != grp_key(ps, h) by {
            if grp_key(ps, g) == grp_key(ps, h) { lemma_key_collision(ps, g, h); }
        }
    }
}

// ------------------------------------------------------------------------------------------------ output order

/// The group output at position `q`: groups 0..4 when `$1 <= $2`, else 2, 3, 0, 1.
pub open spec fn out_grp(ps: Seq<Literal>, q: int) -> int {
    if lex_cmp(p1_of(ps), p2_of(ps)) <= 0 { q } else { if q < 2 { q + 2 } else { q - 2 } }
}

/// The output row of group `g` with volume sum `s`.
pub open spec fn grp_row(ps: Seq<Literal>, g: int, s: int) -> Row {
    grp_key(ps, g).push(Val::Num { coeff: s, scale: 4 })
}

/// The ORDER BY comparison of two output rows: by the first name, the second name, then the year.
proof fn lemma_keys_cmp(r1: Row, r2: Row)
    requires
        r1.len() == 4, r2.len() == 4, r1[0] is Text, r1[1] is Text, r2[0] is Text, r2[1] is Text,
        r1[2] is Num, r2[2] is Num,
    ensures ({
        let c0 = lex_cmp(r1[0]->Text_0, r2[0]->Text_0);
        let c1 = lex_cmp(r1[1]->Text_0, r2[1]->Text_0);
        let c2 = match compare(r1[2], r2[2]) { Some(c) => c, None => 0 };
        keys_cmp(q7_order_keys(), r1, r2) == if c0 != 0 { c0 } else if c1 != 0 { c1 } else { c2 }
    }),
{
    let keys = q7_order_keys();
    let k1 = keys.drop_first();
    let k2 = k1.drop_first();
    let k3 = k2.drop_first();
    assert(k1 =~= seq![keys[1], keys[2]]);
    assert(k2 =~= seq![keys[2]]);
    assert(k3 =~= Seq::<OrderKey>::empty());
    let c0 = lex_cmp(r1[0]->Text_0, r2[0]->Text_0);
    let c1 = lex_cmp(r1[1]->Text_0, r2[1]->Text_0);
    let c2 = match compare(r1[2], r2[2]) { Some(c) => c, None => 0 };
    assert(key_cmp(keys[0], r1, r2) == c0);
    assert(key_cmp(k1[0], r1, r2) == c1);
    assert(key_cmp(k2[0], r1, r2) == c2);
    assert(keys_cmp(k3, r1, r2) == 0);
    assert(keys_cmp(k2, r1, r2) == c2);
    assert(keys_cmp(k1, r1, r2) == if c1 != 0 { c1 } else { c2 });
}

/// Output rows at positions `a < b` are in ORDER BY order (for `$1 == $2` only groups 0 and 1 are output).
pub proof fn lemma_order_pair(ps: Seq<Literal>, a: int, b: int, s1: int, s2: int)
    requires 0 <= a < b < 4, p1_of(ps) == p2_of(ps) ==> b < 2,
    ensures keys_cmp(q7_order_keys(), grp_row(ps, out_grp(ps, a), s1), grp_row(ps, out_grp(ps, b), s2)) <= 0,
{
    let (p1, p2) = (p1_of(ps), p2_of(ps));
    let (g, h) = (out_grp(ps, a), out_grp(ps, b));
    let (r1, r2) = (grp_row(ps, g, s1), grp_row(ps, h, s2));
    lemma_keys_cmp(r1, r2);
    lemma_lex_cmp_antisym(p1, p2);
    lemma_lex_cmp_zero(p1, p1);
    lemma_lex_cmp_zero(p2, p2);
    lemma_lex_cmp_zero(p1, p2);
    lemma_compare_num(r1[2]->Num_coeff, 0, r2[2]->Num_coeff, 0);
    assert(pow10(0) == 1);
    assert(align(r1[2]->Num_coeff, 0, 0) == r1[2]->Num_coeff);
    assert(align(r2[2]->Num_coeff, 0, 0) == r2[2]->Num_coeff);
    assert(max_nat(0, 0) == 0);
}

// ------------------------------------------------------------------------------------------------ the answer

/// The output: positions `sel` (increasing) of the non-empty groups; within `i128` per group.
pub open spec fn sel_ok(sv: StoresView, ps: Seq<Literal>, sel: Seq<int>) -> bool {
    &&& forall|i: int| 0 <= i < sel.len() ==> 0 <= #[trigger] sel[i] < 4
    &&& forall|i: int, j: int| 0 <= i < j < sel.len() ==> #[trigger] sel[i] < #[trigger] sel[j]
    &&& forall|i: int| 0 <= i < sel.len() ==> lsum(sv, ps, out_grp(ps, #[trigger] sel[i]), 0, 0, n_l(sv)) > 0
    &&& forall|q: int| 0 <= q < 4 && lsum(sv, ps, out_grp(ps, q), 0, 0, n_l(sv)) > 0 ==> #[trigger] sel.contains(q)
    &&& forall|g: int| 0 <= g < 4 ==> #[trigger] lsum(sv, ps, g, 2, 0, n_l(sv)) <= i128_max()
}

/// The output rows of the selected positions.
pub open spec fn answer_rows(sv: StoresView, ps: Seq<Literal>, sel: Seq<int>) -> Seq<Row> {
    sel.map_values(|q: int| grp_row(ps, out_grp(ps, q), lsum(sv, ps, out_grp(ps, q), 1, 0, n_l(sv))))
}

/// The statement's GROUP BY row of a non-empty group's key is the group's output row.
proof fn lemma_out_row(sv: StoresView, db: Database, ps: Seq<Literal>, g: int)
    requires bound_db(sv, db), param_domain(ps), 0 <= g < 4, lsum(sv, ps, g, 0, 0, n_l(sv)) > 0,
    ensures
        out_row(g2(), sel_rows(db, ps), grp_key(ps, g)) == grp_row(ps, g, lsum(sv, ps, g, 1, 0, n_l(sv))),
        gcount(g2(), sel_rows(db, ps), grp_key(ps, g)) > 0,
{
    let (gg, xs, k) = (g2(), sel_rows(db, ps), grp_key(ps, g));
    lemma_parts_shape(sv, db);
    lemma_group_sums(sv, db, ps, k);
    lemma_out_group(sv, ps, g, 0, n_l(sv));
    lemma_out_group(sv, ps, g, 1, n_l(sv));
    let full = full_row(gg, xs, k);
    assert(agg_outs(gg, xs, k) =~= seq![Val::Num { coeff: lsum(sv, ps, g, 1, 0, n_l(sv)), scale: 4 }]);
    assert(full =~= grp_row(ps, g, lsum(sv, ps, g, 1, 0, n_l(sv))));
    lemma_select_identity(full, gg.outs);
}

/// `group_caps` of the statement's GROUP BY.
proof fn lemma_caps(sv: StoresView, db: Database, ps: Seq<Literal>, sel: Seq<int>)
    requires bound_db(sv, db), param_domain(ps), sel_ok(sv, ps, sel),
    ensures group_caps(g2(), sel_rows(db, ps)),
{
    let (g, xs) = (g2(), sel_rows(db, ps));
    lemma_parts_shape(sv, db);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 0);
        lemma_group_sums(sv, db, ps, k);
        lemma_key_caps(sv, ps, k, n_l(sv));
    }
}

/// `out_grp` is a permutation of 0..4.
proof fn lemma_out_grp(ps: Seq<Literal>, g: int) -> (q: int)
    requires 0 <= g < 4,
    ensures 0 <= q < 4, out_grp(ps, q) == g,
{
    if lex_cmp(p1_of(ps), p2_of(ps)) <= 0 { g } else { if g < 2 { g + 2 } else { g - 2 } }
}

/// With `$1 == $2` only groups 0 and 1 are output.
proof fn lemma_sel_same(sv: StoresView, ps: Seq<Literal>, sel: Seq<int>)
    requires sel_ok(sv, ps, sel),
    ensures forall|i: int| 0 <= i < sel.len() && p1_of(ps) == p2_of(ps) ==> #[trigger] sel[i] < 2,
{
    assert forall|i: int| 0 <= i < sel.len() && p1_of(ps) == p2_of(ps) implies #[trigger] sel[i] < 2 by {
        if sel[i] >= 2 {
            assert(out_grp(ps, sel[i]) == sel[i]) by { lemma_lex_cmp_zero(p1_of(ps), p2_of(ps)); }
            lemma_same_params(sv, ps, out_grp(ps, sel[i]), 0, 0, n_l(sv));
        }
    }
}

/// The output rows are sorted by the ORDER BY keys.
proof fn lemma_answer_sorted(sv: StoresView, ps: Seq<Literal>, sel: Seq<int>)
    requires sel_ok(sv, ps, sel),
    ensures sorted_by(q7_order_keys(), answer_rows(sv, ps, sel)),
{
    let n = n_l(sv);
    let out = answer_rows(sv, ps, sel);
    lemma_sel_same(sv, ps, sel);
    assert forall|i: int, j: int| 0 <= i < j < out.len() implies keys_cmp(q7_order_keys(), #[trigger] out[i], #[trigger] out[j]) <= 0 by {
        lemma_order_pair(ps, sel[i], sel[j], lsum(sv, ps, out_grp(ps, sel[i]), 1, 0, n), lsum(sv, ps, out_grp(ps, sel[j]), 1, 0, n));
    }
}

/// The output rows are pairwise different (different non-empty groups have different keys).
proof fn lemma_answer_nodup(sv: StoresView, ps: Seq<Literal>, sel: Seq<int>)
    requires sel_ok(sv, ps, sel),
    ensures answer_rows(sv, ps, sel).no_duplicates(),
{
    let n = n_l(sv);
    let out = answer_rows(sv, ps, sel);
    assert forall|i: int, j: int| 0 <= i < out.len() && 0 <= j < out.len() && i != j implies out[i] != out[j] by {
        let (g, h) = (out_grp(ps, sel[i]), out_grp(ps, sel[j]));
        if out[i] == out[j] {
            assert(out[i].drop_last() =~= grp_key(ps, g));
            assert(out[j].drop_last() =~= grp_key(ps, h));
            if i < j { assert(sel[i] < sel[j]); } else { assert(sel[j] < sel[i]); }
            assert(g != h) by {
                if lex_cmp(p1_of(ps), p2_of(ps)) <= 0 {} else {}
            }
            lemma_key_collision(ps, g, h);
            if g >= 2 { lemma_same_params(sv, ps, g, 0, 0, n); }
            if h >= 2 { lemma_same_params(sv, ps, h, 0, 0, n); }
        }
    }
}

/// The statement's rows are pairwise different (one per key).
proof fn lemma_result_nodup(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures result_rows(g2(), sel_rows(db, ps)).no_duplicates(),
{
    let (gg, xs) = (g2(), sel_rows(db, ps));
    let n = n_l(sv);
    let res = result_rows(gg, xs);
    let gk = gkeys(gg, xs);
    lemma_parts_shape(sv, db);
    lemma_gkeys(gg, xs);
    assert forall|i: int, j: int| 0 <= i < res.len() && 0 <= j < res.len() && i != j implies res[i] != res[j] by {
        assert(gk.contains(gk[i]) && gk.contains(gk[j]));
        lemma_group_sums(sv, db, ps, gk[i]);
        lemma_group_sums(sv, db, ps, gk[j]);
        let g = lemma_key_group(sv, ps, gk[i], n);
        let h = lemma_key_group(sv, ps, gk[j], n);
        lemma_out_row(sv, db, ps, g);
        lemma_out_row(sv, db, ps, h);
        if res[i] == res[j] {
            assert(res[i].drop_last() =~= gk[i]);
            assert(res[j].drop_last() =~= gk[j]);
        }
    }
}

/// An output row is a row of the statement.
proof fn lemma_answer_in_result(sv: StoresView, db: Database, ps: Seq<Literal>, sel: Seq<int>, i: int)
    requires bound_db(sv, db), param_domain(ps), sel_ok(sv, ps, sel), 0 <= i < sel.len(),
    ensures result_rows(g2(), sel_rows(db, ps)).contains(answer_rows(sv, ps, sel)[i]),
{
    let (gg, xs) = (g2(), sel_rows(db, ps));
    let gk = gkeys(gg, xs);
    lemma_gkeys(gg, xs);
    let g = out_grp(ps, sel[i]);
    lemma_out_row(sv, db, ps, g);
    assert(gk.contains(grp_key(ps, g)));
    let t = choose|t: int| 0 <= t < gk.len() && gk[t] == grp_key(ps, g);
    assert(result_rows(gg, xs)[t] == answer_rows(sv, ps, sel)[i]);
}

/// A row of the statement is an output row.
proof fn lemma_result_in_answer(sv: StoresView, db: Database, ps: Seq<Literal>, sel: Seq<int>, t: int)
    requires bound_db(sv, db), param_domain(ps), sel_ok(sv, ps, sel), 0 <= t < result_rows(g2(), sel_rows(db, ps)).len(),
    ensures answer_rows(sv, ps, sel).contains(result_rows(g2(), sel_rows(db, ps))[t]),
{
    let (gg, xs) = (g2(), sel_rows(db, ps));
    let gk = gkeys(gg, xs);
    let n = n_l(sv);
    lemma_parts_shape(sv, db);
    lemma_gkeys(gg, xs);
    assert(gk.contains(gk[t]));
    lemma_group_sums(sv, db, ps, gk[t]);
    let g = lemma_key_group(sv, ps, gk[t], n);
    lemma_out_row(sv, db, ps, g);
    let q = lemma_out_grp(ps, g);
    assert(sel.contains(q));
    let i = choose|i: int| 0 <= i < sel.len() && sel[i] == q;
    assert(answer_rows(sv, ps, sel)[i] == result_rows(gg, xs)[t]);
}

/// Under the column-level facts, the output rows are an allowed output of the statement on every bound database.
pub proof fn lemma_answer(sv: StoresView, db: Database, ps: Seq<Literal>, sel: Seq<int>)
    requires bound_db(sv, db), param_domain(ps), sel_ok(sv, ps, sel),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(answer_rows(sv, ps, sel))),
{
    let (gg, xs) = (g2(), sel_rows(db, ps));
    let out = answer_rows(sv, ps, sel);
    let res = result_rows(gg, xs);
    lemma_caps(sv, db, ps, sel);
    lemma_denotation(sv, db, ps);
    lemma_query_shape(ps);
    lemma_answer_sorted(sv, ps, sel);
    lemma_answer_nodup(sv, ps, sel);
    lemma_result_nodup(sv, db, ps);
    assert forall|x: Row| #[trigger] out.contains(x) <==> res.contains(x) by {
        if out.contains(x) {
            let i = choose|i: int| 0 <= i < out.len() && out[i] == x;
            lemma_answer_in_result(sv, db, ps, sel, i);
        }
        if res.contains(x) {
            let t = choose|t: int| 0 <= t < res.len() && res[t] == x;
            lemma_result_in_answer(sv, db, ps, sel, t);
        }
    }
    lemma_nodup_same_multiset(out, res);
    lemma_outcome_sorted(db, query_spec_at(ps), res, out);
    lemma_slice_whole(out);
}

} // verus!
