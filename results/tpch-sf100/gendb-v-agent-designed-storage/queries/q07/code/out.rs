//! The answer rows: one row `[supp_nation, cust_nation, l_year, revenue]` per non-empty group, in ORDER BY order
//! (`ord_of`: the pair whose first name is smaller bytewise first, years ascending; only pair 0 when
//! `$1 == $2`), built from the scan's per-group totals (`build_rows`) and proved an allowed output of the statement
//! (`lemma_out`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::numeric::*;
use crate::spec::order::*;
use crate::spec::text::lex_cmp;
use crate::spec::limits::*;
use crate::link::query::*;
use crate::exec::value::{EVal, view_row};
use crate::query::query_spec_at;
use super::sqlq::*;
use super::reduce::*;
use super::body::*;
use super::model::*;
use super::line::*;
use super::answer::*;
use super::kernel::i128_max;

verus! {

/// The groups in output order.
pub open spec fn ord_of(ps: Seq<Literal>) -> Seq<int> {
    if ltext(ps[0]) == ltext(ps[1]) {
        seq![0int, 1]
    } else if lex_cmp(ltext(ps[0]), ltext(ps[1])) < 0 {
        seq![0int, 1, 2, 3]
    } else {
        seq![2int, 3, 0, 1]
    }
}

/// The output row of group `gi` with revenue coefficient `s` (scale 4).
pub open spec fn rowof(ps: Seq<Literal>, gi: int, s: int) -> Row {
    krow(ps, gi).push(Val::Num { coeff: s, scale: 4 })
}

// ------------------------------------------------------------------------------------------------ order of the groups

proof fn lemma_year_cmp()
    ensures num_cmp(1995, 0, 1996, 0) < 0,
{
    assert(num_cmp(1995, 0, 1996, 0) == -1) by (compute);
}

proof fn lemma_text_eq(a: Seq<u8>)
    ensures lex_cmp(a, a) == 0,
{
    crate::bridge::equality::lemma_lex_cmp_zero(a, a);
}

/// Rows of the same pair, year 1995 then 1996.
proof fn lemma_cmp_years(ps: Seq<Literal>, gi: int, s1: int, s2: int)
    requires gi == 0 || gi == 2,
    ensures keys_cmp(order_keys(), rowof(ps, gi, s1), rowof(ps, gi + 1, s2)) < 0,
{
    let (r1, r2) = (rowof(ps, gi, s1), rowof(ps, gi + 1, s2));
    lemma_text_eq(ltext(ps[0]));
    lemma_text_eq(ltext(ps[1]));
    lemma_year_cmp();
    assert(r1[0] == r2[0] && r1[1] == r2[1]);
    assert(r1[2] == Val::Num { coeff: 1995, scale: 0 } && r2[2] == Val::Num { coeff: 1996, scale: 0 });
    let ks = order_keys();
    assert(ks.drop_first() =~= seq![ks[1], ks[2]]);
    assert(ks.drop_first().drop_first() =~= seq![ks[2]]);
    assert(ks.drop_first().drop_first().drop_first() =~= Seq::<OrderKey>::empty());
    assert(key_cmp(ks[0], r1, r2) == 0);
    assert(key_cmp(ks[1], r1, r2) == 0);
    assert(key_cmp(ks[2], r1, r2) < 0);
    reveal_with_fuel(keys_cmp, 4);
}

/// Rows of different pairs: the pair with the smaller first name comes first.
proof fn lemma_cmp_pairs(ps: Seq<Literal>, ga: int, gb: int, s1: int, s2: int)
    requires
        0 <= ga < 4, 0 <= gb < 4,
        (ga < 2) != (gb < 2),
        lex_cmp(krow(ps, ga)[0]->Text_0, krow(ps, gb)[0]->Text_0) < 0,
    ensures keys_cmp(order_keys(), rowof(ps, ga, s1), rowof(ps, gb, s2)) < 0,
{
    let (r1, r2) = (rowof(ps, ga, s1), rowof(ps, gb, s2));
    assert(r1[0] == krow(ps, ga)[0] && r2[0] == krow(ps, gb)[0]);
}

/// Consecutive positions of `ord_of` are in ORDER BY order, for any revenues.
proof fn lemma_ord_sorted(ps: Seq<Literal>, a: int, b: int, s1: int, s2: int)
    requires texts(ps), 0 <= a < b < ord_of(ps).len(),
    ensures keys_cmp(order_keys(), rowof(ps, ord_of(ps)[a], s1), rowof(ps, ord_of(ps)[b], s2)) < 0,
{
    let (t0, t1) = (ltext(ps[0]), ltext(ps[1]));
    let o = ord_of(ps);
    let (ga, gb) = (o[a], o[b]);
    crate::bridge::order::lemma_lex_cmp_antisym(t0, t1);
    crate::bridge::equality::lemma_lex_cmp_zero(t0, t1);
    if (ga < 2) == (gb < 2) {
        assert(gb == ga + 1 && (ga == 0 || ga == 2));
        lemma_cmp_years(ps, ga, s1, s2);
    } else {
        lemma_cmp_pairs(ps, ga, gb, s1, s2);
    }
}

/// Distinct positions of `ord_of` hold distinct key rows.
proof fn lemma_ord_injective(ps: Seq<Literal>, a: int, b: int)
    requires texts(ps), 0 <= a < ord_of(ps).len(), 0 <= b < ord_of(ps).len(), a != b,
    ensures krow(ps, ord_of(ps)[a]) != krow(ps, ord_of(ps)[b]),
{
    let o = ord_of(ps);
    let (ka, kb) = (krow(ps, o[a]), krow(ps, o[b]));
    if (o[a] < 2) == (o[b] < 2) {
        assert(ka[2] != kb[2]);
    } else {
        assert(ka[0] != kb[0]);
    }
}

// ------------------------------------------------------------------------------------------------ group totals

/// A group no line falls in has zero count, sum and mass.
proof fn lemma_r_absent(c: Cols, x: Ctx, gi: int, a: int, b: int)
    requires forall|j: int| a <= j < b ==> #[trigger] l_grp(c, x, j) != gi,
    ensures rcnt(c, x, gi, a, b) == 0, rsum(c, x, gi, a, b) == 0, rmass(c, x, gi, a, b) == 0,
    decreases b - a,
{
    if a < b {
        lemma_r_absent(c, x, gi, a, b - 1);
    }
}

/// A group without lines has zero sum and mass.
proof fn lemma_r_zero(c: Cols, x: Ctx, gi: int, a: int, b: int)
    requires rcnt(c, x, gi, a, b) == 0, a <= b,
    ensures rsum(c, x, gi, a, b) == 0, rmass(c, x, gi, a, b) == 0,
    decreases b - a,
{
    if a < b {
        lemma_r_bounds(c, x, gi, a, b - 1);
        lemma_r_zero(c, x, gi, a, b - 1);
    }
}

/// The scan's totals of the four groups over all lines.
pub open spec fn totals_ok(c: Cols, x: Ctx, tc: Seq<int>, ts: Seq<int>, tm: Seq<int>) -> bool {
    &&& tc.len() == 4 && ts.len() == 4 && tm.len() == 4
    &&& forall|gi: int| 0 <= gi < 4 ==> #[trigger] tc[gi] == rcnt(c, x, gi, 0, c.n_l as int)
    &&& forall|gi: int| 0 <= gi < 4 ==> #[trigger] ts[gi] == rsum(c, x, gi, 0, c.n_l as int)
    &&& forall|gi: int| 0 <= gi < 4 ==> #[trigger] tm[gi] == rmass(c, x, gi, 0, c.n_l as int)
}

/// When `$1 == $2`, groups 2 and 3 are empty; every group without lines has zero sum and mass.
proof fn lemma_totals(c: Cols, x: Ctx, tc: Seq<int>, ts: Seq<int>, tm: Seq<int>)
    requires totals_ok(c, x, tc, ts, tm),
    ensures
        x.same ==> tc[2] == 0 && tc[3] == 0,
        forall|gi: int| 0 <= gi < 4 && tc[gi] == 0 ==> #[trigger] ts[gi] == 0 && tm[gi] == 0,
        forall|gi: int| 0 <= gi < 4 ==> 0 <= #[trigger] tc[gi] && 0 <= tm[gi],
{
    let n = c.n_l as int;
    if x.same {
        assert forall|j: int| 0 <= j < n implies #[trigger] l_grp(c, x, j) != 2 by {}
        assert forall|j: int| 0 <= j < n implies #[trigger] l_grp(c, x, j) != 3 by {}
        lemma_r_absent(c, x, 2, 0, n);
        lemma_r_absent(c, x, 3, 0, n);
    }
    assert forall|gi: int| 0 <= gi < 4 && tc[gi] == 0 implies #[trigger] ts[gi] == 0 && tm[gi] == 0 by {
        lemma_r_zero(c, x, gi, 0, n);
    }
    assert forall|gi: int| 0 <= gi < 4 implies 0 <= #[trigger] tc[gi] && 0 <= tm[gi] by {
        lemma_r_bounds(c, x, gi, 0, n);
    }
}

/// The key rows of the four groups: distinct, except that pairs coincide when `$1 == $2`.
proof fn lemma_krows(ps: Seq<Literal>)
    requires texts(ps),
    ensures
        forall|a: int, b: int| 0 <= a < 4 && 0 <= b < 4 && a % 2 != b % 2 ==> krow(ps, a) != krow(ps, b),
        ltext(ps[0]) != ltext(ps[1]) ==> forall|a: int, b: int| 0 <= a < 4 && 0 <= b < 4 && a != b ==> krow(ps, a) != krow(ps, b),
        ltext(ps[0]) == ltext(ps[1]) ==> krow(ps, 0) == krow(ps, 2) && krow(ps, 1) == krow(ps, 3),
{
    assert forall|a: int, b: int| 0 <= a < 4 && 0 <= b < 4 && a % 2 != b % 2 implies krow(ps, a) != krow(ps, b) by {
        assert(krow(ps, a)[2] != krow(ps, b)[2]);
    }
    if ltext(ps[0]) != ltext(ps[1]) {
        assert forall|a: int, b: int| 0 <= a < 4 && 0 <= b < 4 && a != b implies krow(ps, a) != krow(ps, b) by {
            if a % 2 == b % 2 {
                assert(krow(ps, a)[0] != krow(ps, b)[0]);
            } else {
                assert(krow(ps, a)[2] != krow(ps, b)[2]);
            }
        }
    } else {
        assert(krow(ps, 0) =~= krow(ps, 2));
        assert(krow(ps, 1) =~= krow(ps, 3));
    }
}

/// Group `gi` is listed by `ord_of`.
pub open spec fn in_ord(ps: Seq<Literal>, gi: int) -> bool {
    exists|p: int| 0 <= p < ord_of(ps).len() && #[trigger] ord_of(ps)[p] == gi
}

/// The groups listed by `ord_of` are exactly the groups that can hold lines.
proof fn lemma_ord_groups(ps: Seq<Literal>)
    requires texts(ps),
    ensures
        forall|p: int| 0 <= p < ord_of(ps).len() ==> 0 <= #[trigger] ord_of(ps)[p] < 4,
        forall|gi: int| 0 <= gi < 4 && (ltext(ps[0]) != ltext(ps[1]) || gi < 2) ==> #[trigger] in_ord(ps, gi),
{
    let o = ord_of(ps);
    assert forall|gi: int| 0 <= gi < 4 && (ltext(ps[0]) != ltext(ps[1]) || gi < 2) implies #[trigger] in_ord(ps, gi) by {
        if ltext(ps[0]) == ltext(ps[1]) {
            assert(o[gi] == gi);
        } else if lex_cmp(ltext(ps[0]), ltext(ps[1])) < 0 {
            assert(o[gi] == gi);
        } else {
            let p = if gi < 2 { gi + 2 } else { gi - 2 };
            assert(o[p] == gi);
        }
    }
}

// ------------------------------------------------------------------------------------------------ the answer

/// The output rows hold, in `ord_of` order, the non-empty groups (positions `pos`).
pub open spec fn out_ok(ps: Seq<Literal>, tc: Seq<int>, ts: Seq<int>, pos: Seq<int>, out: Seq<Row>) -> bool {
    &&& out.len() == pos.len()
    &&& forall|i: int, j: int| 0 <= i < j < pos.len() ==> #[trigger] pos[i] < #[trigger] pos[j]
    &&& forall|i: int| 0 <= i < pos.len() ==> 0 <= #[trigger] pos[i] < ord_of(ps).len()
    &&& forall|i: int| 0 <= i < pos.len() ==> #[trigger] tc[ord_of(ps)[pos[i]]] > 0
    &&& forall|i: int| 0 <= i < pos.len() ==> #[trigger] out[i] == rowof(ps, ord_of(ps)[pos[i]], ts[ord_of(ps)[pos[i]]])
    &&& forall|p: int| 0 <= p < ord_of(ps).len() && #[trigger] tc[ord_of(ps)[p]] > 0 ==> pos.contains(p)
}

/// Which groups share a key row: none when `$1 != $2`; groups `gi` and `gi + 2` when `$1 == $2`, the latter empty.
proof fn lemma_key_match(c: Cols, x: Ctx, ps: Seq<Literal>, tc: Seq<int>, ts: Seq<int>, tm: Seq<int>, k: Row)
    requires
        texts(ps),
        x.same == (ltext(ps[0]) == ltext(ps[1])),
        totals_ok(c, x, tc, ts, tm),
    ensures ({
        let n = c.n_l as int;
        let (a0, a1, a2, a3) = (krow(ps, 0) == k, krow(ps, 1) == k, krow(ps, 2) == k, krow(ps, 3) == k);
        &&& kcnt(c, x, ps, k, n) == (if a0 { tc[0] } else { 0 }) + (if a1 { tc[1] } else { 0 }) + (if a2 { tc[2] } else { 0 }) + (if a3 { tc[3] } else { 0 })
        &&& ksum(c, x, ps, k, n) == (if a0 { ts[0] } else { 0 }) + (if a1 { ts[1] } else { 0 }) + (if a2 { ts[2] } else { 0 }) + (if a3 { ts[3] } else { 0 })
        &&& kmass(c, x, ps, k, n) == (if a0 { tm[0] } else { 0 }) + (if a1 { tm[1] } else { 0 }) + (if a2 { tm[2] } else { 0 }) + (if a3 { tm[3] } else { 0 })
        &&& !(a0 && a1) && !(a2 && a3) && !(a0 && a3) && !(a1 && a2)
        &&& !x.same ==> !(a0 && a2) && !(a1 && a3)
        &&& x.same ==> tc[2] == 0 && tc[3] == 0 && ts[2] == 0 && ts[3] == 0 && tm[2] == 0 && tm[3] == 0
        &&& 0 <= tc[0] && 0 <= tc[1] && 0 <= tc[2] && 0 <= tc[3]
        &&& 0 <= tm[0] && 0 <= tm[1] && 0 <= tm[2] && 0 <= tm[3]
        &&& (tc[0] == 0 ==> ts[0] == 0 && tm[0] == 0) && (tc[1] == 0 ==> ts[1] == 0 && tm[1] == 0)
    }),
{
    let n = c.n_l as int;
    lemma_totals(c, x, tc, ts, tm);
    lemma_krows(ps);
    assert(tc[0] == rcnt(c, x, 0, 0, n) && tc[1] == rcnt(c, x, 1, 0, n) && tc[2] == rcnt(c, x, 2, 0, n) && tc[3] == rcnt(c, x, 3, 0, n));
    assert(ts[0] == rsum(c, x, 0, 0, n) && ts[1] == rsum(c, x, 1, 0, n) && ts[2] == rsum(c, x, 2, 0, n) && ts[3] == rsum(c, x, 3, 0, n));
    assert(tm[0] == rmass(c, x, 0, 0, n) && tm[1] == rmass(c, x, 1, 0, n) && tm[2] == rmass(c, x, 2, 0, n) && tm[3] == rmass(c, x, 3, 0, n));
    assert(krow(ps, 0) != krow(ps, 1) && krow(ps, 2) != krow(ps, 3) && krow(ps, 0) != krow(ps, 3) && krow(ps, 1) != krow(ps, 2));
    if !x.same {
        assert(krow(ps, 0) != krow(ps, 2) && krow(ps, 1) != krow(ps, 3));
    } else {
        assert(ts[2] == 0 && tm[2] == 0 && ts[3] == 0 && tm[3] == 0);
    }
    assert(tc[0] == 0 ==> ts[0] == 0 && tm[0] == 0);
    assert(tc[1] == 0 ==> ts[1] == 0 && tm[1] == 0);
}

/// SUM capacity: every key's mass is at most one group's mass.
proof fn lemma_caps(db: Database, c: Cols, x: Ctx, ps: Seq<Literal>, lm: Seq<int>, om: Seq<int>,
    tc: Seq<int>, ts: Seq<int>, tm: Seq<int>)
    requires
        chain_ok(db, c, x, ps, lm, om),
        totals_ok(c, x, tc, ts, tm),
        forall|gi: int| 0 <= gi < 4 ==> #[trigger] tm[gi] <= i128_max(),
    ensures group_caps(g7(), ship(db, ps)),
{
    let g = g7();
    let sh = ship(db, ps);
    let n = c.n_l as int;
    lemma_totals(c, x, tc, ts, tm);
    lemma_krows(ps);
    assert(tm[0] <= i128_max() && tm[1] <= i128_max() && tm[2] <= i128_max() && tm[3] <= i128_max());
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, sh, k, j) <= i128_max() by {
        assert(j == 0);
        lemma_group_sums(db, c, x, ps, lm, om, k);
        lemma_key_match(c, x, ps, tc, ts, tm, k);
    }
}

/// The key rows of the output are distinct, and they are exactly the keys of the non-empty groups.
proof fn lemma_out_keys(db: Database, c: Cols, x: Ctx, ps: Seq<Literal>, lm: Seq<int>, om: Seq<int>,
    tc: Seq<int>, ts: Seq<int>, tm: Seq<int>, pos: Seq<int>, out: Seq<Row>)
    requires
        chain_ok(db, c, x, ps, lm, om),
        totals_ok(c, x, tc, ts, tm),
        out_ok(ps, tc, ts, pos, out),
    ensures ({
        let ks = pos.map_values(|p: int| krow(ps, ord_of(ps)[p]));
        &&& ks.no_duplicates()
        &&& forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g7(), ship(db, ps), k) > 0
    }),
{
    let g = g7();
    let sh = ship(db, ps);
    let n = c.n_l as int;
    let o = ord_of(ps);
    lemma_totals(c, x, tc, ts, tm);
    lemma_krows(ps);
    lemma_ord_groups(ps);
    let ks = pos.map_values(|p: int| krow(ps, o[p]));
    assert forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j implies ks[i] != ks[j] by {
        if i < j {
            assert(pos[i] < pos[j]);
        } else {
            assert(pos[j] < pos[i]);
        }
        lemma_ord_injective(ps, pos[i], pos[j]);
    }
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, sh, k) > 0 by {
        lemma_group_sums(db, c, x, ps, lm, om, k);
        lemma_key_match(c, x, ps, tc, ts, tm, k);
        if ks.contains(k) {
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
            assert(tc[o[pos[i]]] > 0);
        }
        if gcount(g, sh, k) > 0 {
            let gi: int = if krow(ps, 0) == k && tc[0] > 0 { 0 } else if krow(ps, 1) == k && tc[1] > 0 { 1 }
                else if krow(ps, 2) == k && tc[2] > 0 { 2 } else { 3 };
            assert(krow(ps, gi) == k && tc[gi] > 0);
            assert(in_ord(ps, gi));
            let p = choose|p: int| 0 <= p < o.len() && #[trigger] o[p] == gi;
            assert(pos.contains(p));
            let i = choose|i: int| 0 <= i < pos.len() && pos[i] == p;
            assert(ks[i] == k);
        }
    }
}

/// Each output row is its group's full row.
proof fn lemma_out_rows(db: Database, c: Cols, x: Ctx, ps: Seq<Literal>, lm: Seq<int>, om: Seq<int>,
    tc: Seq<int>, ts: Seq<int>, tm: Seq<int>, pos: Seq<int>, out: Seq<Row>)
    requires
        chain_ok(db, c, x, ps, lm, om),
        totals_ok(c, x, tc, ts, tm),
        out_ok(ps, tc, ts, pos, out),
    ensures ({
        let ks = pos.map_values(|p: int| krow(ps, ord_of(ps)[p]));
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == out_row(g7(), ship(db, ps), ks[i])
    }),
{
    let g = g7();
    let sh = ship(db, ps);
    let o = ord_of(ps);
    lemma_totals(c, x, tc, ts, tm);
    lemma_krows(ps);
    lemma_ord_groups(ps);
    let ks = pos.map_values(|p: int| krow(ps, o[p]));
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == out_row(g, sh, ks[i]) by {
        let gi = o[pos[i]];
        let k = ks[i];
        lemma_group_sums(db, c, x, ps, lm, om, k);
        lemma_key_match(c, x, ps, tc, ts, tm, k);
        assert(k == krow(ps, gi));
        assert(tc[gi] > 0);
        assert(x.same ==> gi < 2);
        assert(gcount(g, sh, k) > 0);
        assert(gsum(g, sh, k, 0) == ts[gi]);
        assert(agg_outs(g, sh, k) =~= seq![Val::Num { coeff: ts[gi], scale: 4 }]);
        assert(full_row(g, sh, k) =~= rowof(ps, gi, ts[gi]));
        lemma_select_identity(full_row(g, sh, k), g.outs);
    }
}

/// The non-empty groups' rows in `ord_of` order are an allowed output of the statement.
pub proof fn lemma_out(db: Database, c: Cols, x: Ctx, ps: Seq<Literal>, lm: Seq<int>, om: Seq<int>,
    tc: Seq<int>, ts: Seq<int>, tm: Seq<int>, pos: Seq<int>, out: Seq<Row>)
    requires
        chain_ok(db, c, x, ps, lm, om),
        totals_ok(c, x, tc, ts, tm),
        forall|gi: int| 0 <= gi < 4 ==> #[trigger] tm[gi] <= i128_max(),
        out_ok(ps, tc, ts, pos, out),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let g = g7();
    let sh = ship(db, ps);
    let o = ord_of(ps);
    lemma_statement(ps);
    lemma_caps(db, c, x, ps, lm, om, tc, ts, tm);
    lemma_body(db, ps);
    lemma_out_keys(db, c, x, ps, lm, om, tc, ts, tm, pos, out);
    lemma_out_rows(db, c, x, ps, lm, om, tc, ts, tm, pos, out);
    let ks = pos.map_values(|p: int| krow(ps, o[p]));
    assert(sorted_by(order_keys(), out)) by {
        assert forall|i: int, j: int| 0 <= i < j < out.len() implies keys_cmp(order_keys(), #[trigger] out[i], #[trigger] out[j]) <= 0 by {
            assert(pos[i] < pos[j]);
            lemma_ord_sorted(ps, pos[i], pos[j], ts[o[pos[i]]], ts[o[pos[j]]]);
        }
    }
    lemma_result_from_keys(g, order_keys(), 0, None, sh, ks, out);
    lemma_slice_all(out);
    lemma_ordered_link(db, query_spec_at(ps), g, sh, out);
}

} // verus!
