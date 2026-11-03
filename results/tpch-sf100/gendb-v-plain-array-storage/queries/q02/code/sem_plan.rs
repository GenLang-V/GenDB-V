//! The plan's normal form: the statement's kept rows are determined by their partsupp row.
//!
//! A partsupp row `c` is a *hit* when some qualifying part has its part key and some supplier of the region has its
//! supplier key (`hit`); it is a *candidate* when it is a hit and its supply cost is the least among the hits with
//! its part key (`lemma_cand_iff`). Each candidate has exactly one kept FROM row (`cand_row`, unique by the primary
//! keys), and the kept rows are, as a bag, the candidates' rows (`lemma_kept_bag`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::relation::*;
use crate::link::join::keep;
use crate::link::expr::{ival, tval};
use crate::link::query::lemma_nodup_same_multiset;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_sub::*;
use crate::agent::sem_outer::*;
use crate::agent::common::relations::*;

verus! {

/// Some qualifying part has key `k`.
pub open spec fn qual_key(sv: StoresView, v: int, pat: Seq<u8>, k: int) -> bool {
    exists|a: int| 0 <= a < part_n(sv) && #[trigger] p_keys(sv)[a] == k && part_ok(sv, v, pat, a)
}

/// Some supplier of the region has the supplier key of partsupp row `c`.
pub open spec fn reg_supp(sv: StoresView, rp: Seq<u8>, c: int) -> bool {
    exists|b: int| 0 <= b < supp_n(sv) && #[trigger] s_keys(sv)[b] == ps_skeys(sv)[c] && supp_in_reg(sv, rp, b)
}

/// Partsupp row `c` is a hit.
pub open spec fn hit(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, c: int) -> bool {
    qual_key(sv, v, pat, ps_pkeys(sv)[c] as int) && reg_supp(sv, rp, c)
}

/// The supply cost of `c` is at most that of every hit with its part key.
pub open spec fn least_cost(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, c: int) -> bool {
    forall|c2: int| 0 <= c2 < ps_n(sv) && #[trigger] hit(sv, v, pat, rp, c2) && ps_pkeys(sv)[c2] == ps_pkeys(sv)[c]
        ==> ps_costs(sv)[c] <= ps_costs(sv)[c2]
}

/// Partsupp row `c` has a kept FROM row.
pub open spec fn cand(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, c: int) -> bool {
    exists|a: int, b: int, d: int, e: int| #[trigger] in5(sv, a, b, c, d, e)
        && (outer_keep(sv, v, pat, rp))(row5(sv, a, b, c, d, e))
}

/// The kept row of candidate `c`: part, supplier, nation and region rows.
pub open spec fn cand_tuple(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, c: int) -> (int, int, int, int) {
    choose|a: int, b: int, d: int, e: int| #[trigger] in5(sv, a, b, c, d, e) && (outer_keep(sv, v, pat, rp))(row5(sv, a, b, c, d, e))
}

pub open spec fn cand_row(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, c: int) -> Row {
    let t = cand_tuple(sv, v, pat, rp, c);
    row5(sv, t.0, t.1, c, t.2, t.3)
}

/// `outer_keep` on a FROM row, in terms of the stored columns.
pub proof fn lemma_keep_row5(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, a: int, b: int, c: int, d: int, e: int)
    requires stores_wf(sv), in5(sv, a, b, c, d, e),
    ensures
        (outer_keep(sv, v, pat, rp))(row5(sv, a, b, c, d, e)) == (
            p_keys(sv)[a] == ps_pkeys(sv)[c] && s_keys(sv)[b] == ps_skeys(sv)[c] && part_ok(sv, v, pat, a)
            && s_nks(sv)[b] == n_keys(sv)[d] && n_rks(sv)[d] == r_keys(sv)[e] && r_name(sv, e) == rp
            && is_min_cost(sv, rp, p_keys(sv)[a] as int, ps_costs(sv)[c] as int)),
{
    lemma_row5(sv, a, b, c, d, e);
}

/// A candidate is a hit whose cost is the least among the hits with its part key, and conversely.
pub proof fn lemma_cand_iff(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, c: int)
    requires stores_wf(sv), 0 <= c < ps_n(sv),
    ensures cand(sv, v, pat, rp, c) == (hit(sv, v, pat, rp, c) && least_cost(sv, v, pat, rp, c)),
{
    let k = ps_pkeys(sv)[c] as int;
    let w = ps_costs(sv)[c] as int;
    if cand(sv, v, pat, rp, c) {
        let (a, b, d, e) = choose|a: int, b: int, d: int, e: int| #[trigger] in5(sv, a, b, c, d, e)
            && (outer_keep(sv, v, pat, rp))(row5(sv, a, b, c, d, e));
        lemma_keep_row5(sv, v, pat, rp, a, b, c, d, e);
        assert(supp_in_reg(sv, rp, b));
        assert(reg_supp(sv, rp, c));
        assert(qual_key(sv, v, pat, k));
        assert forall|c2: int| 0 <= c2 < ps_n(sv) && #[trigger] hit(sv, v, pat, rp, c2) && ps_pkeys(sv)[c2] == ps_pkeys(sv)[c]
            implies ps_costs(sv)[c] <= ps_costs(sv)[c2] by {
            assert(sub_ok(sv, rp, k, c2));
        }
    }
    if hit(sv, v, pat, rp, c) && least_cost(sv, v, pat, rp, c) {
        let a = choose|a: int| 0 <= a < part_n(sv) && #[trigger] p_keys(sv)[a] == k && part_ok(sv, v, pat, a);
        let b = choose|b: int| 0 <= b < supp_n(sv) && #[trigger] s_keys(sv)[b] == ps_skeys(sv)[c] && supp_in_reg(sv, rp, b);
        let (d, e) = choose|d: int, e: int| 0 <= d < nat_n(sv) && 0 <= e < reg_n(sv)
            && #[trigger] n_keys(sv)[d] == s_nks(sv)[b] && n_rks(sv)[d] == #[trigger] r_keys(sv)[e] && r_name(sv, e) == rp;
        assert(sub_ok(sv, rp, k, c));
        assert forall|c2: int| 0 <= c2 < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c2) implies w <= ps_costs(sv)[c2] by {
            assert(qual_key(sv, v, pat, ps_pkeys(sv)[c2] as int));
            assert(reg_supp(sv, rp, c2));
            assert(hit(sv, v, pat, rp, c2));
        }
        assert(is_min_cost(sv, rp, k, w));
        lemma_keep_row5(sv, v, pat, rp, a, b, c, d, e);
        assert(in5(sv, a, b, c, d, e));
    }
}

/// A kept FROM row is determined by its partsupp row (primary keys of part, supplier, nation, region).
pub proof fn lemma_tuple_unique(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>,
    a: int, b: int, c: int, d: int, e: int, a2: int, b2: int, d2: int, e2: int)
    requires
        stores_wf(sv), keys_ok(sv),
        in5(sv, a, b, c, d, e), in5(sv, a2, b2, c, d2, e2),
        (outer_keep(sv, v, pat, rp))(row5(sv, a, b, c, d, e)),
        (outer_keep(sv, v, pat, rp))(row5(sv, a2, b2, c, d2, e2)),
    ensures a == a2, b == b2, d == d2, e == e2,
{
    lemma_keep_row5(sv, v, pat, rp, a, b, c, d, e);
    lemma_keep_row5(sv, v, pat, rp, a2, b2, c, d2, e2);
    assert(p_keys(sv)[a] == p_keys(sv)[a2]);
    assert(s_keys(sv)[b] == s_keys(sv)[b2]);
    assert(n_keys(sv)[d] == n_keys(sv)[d2]);
    assert(r_keys(sv)[e] == r_keys(sv)[e2]);
}

/// A candidate's kept row is its tuple's row, and any kept row of `c` is that row.
pub proof fn lemma_cand_row(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, c: int)
    requires stores_wf(sv), keys_ok(sv), cand(sv, v, pat, rp, c),
    ensures
        ({ let t = cand_tuple(sv, v, pat, rp, c);
            in5(sv, t.0, t.1, c, t.2, t.3) && (outer_keep(sv, v, pat, rp))(row5(sv, t.0, t.1, c, t.2, t.3)) }),
        forall|a: int, b: int, d: int, e: int| #[trigger] in5(sv, a, b, c, d, e) && (outer_keep(sv, v, pat, rp))(row5(sv, a, b, c, d, e))
            ==> cand_tuple(sv, v, pat, rp, c) == (a, b, d, e),
{
    let t = cand_tuple(sv, v, pat, rp, c);
    assert forall|a: int, b: int, d: int, e: int| #[trigger] in5(sv, a, b, c, d, e) && (outer_keep(sv, v, pat, rp))(row5(sv, a, b, c, d, e))
        implies cand_tuple(sv, v, pat, rp, c) == (a, b, d, e) by {
        lemma_tuple_unique(sv, v, pat, rp, t.0, t.1, c, t.2, t.3, a, b, d, e);
    }
}

/// The candidates' rows of an increasing list of exactly the candidates.
pub open spec fn cand_rows(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, cs: Seq<int>) -> Seq<Row> {
    cs.map_values(|c: int| cand_row(sv, v, pat, rp, c))
}

/// `cs` lists every candidate exactly once, in increasing order.
pub open spec fn lists_cands(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, cs: Seq<int>) -> bool {
    &&& forall|i: int| 0 <= i < cs.len() ==> 0 <= #[trigger] cs[i] < ps_n(sv) && cand(sv, v, pat, rp, cs[i])
    &&& forall|i: int, j: int| 0 <= i < j < cs.len() ==> cs[i] < cs[j]
    &&& forall|c: int| 0 <= c < ps_n(sv) && #[trigger] cand(sv, v, pat, rp, c) ==> exists|i: int| 0 <= i < cs.len() && cs[i] == c
}

/// The kept rows are, as a bag, the candidates' rows.
pub proof fn lemma_kept_bag(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, cs: Seq<int>)
    requires stores_wf(sv), keys_ok(sv), lists_cands(sv, v, pat, rp, cs),
    ensures keep(from5(sv), outer_keep(sv, v, pat, rp)).to_multiset() == cand_rows(sv, v, pat, rp, cs).to_multiset(),
{
    hide(outer_keep);
    let f = outer_keep(sv, v, pat, rp);
    let kept = keep(from5(sv), f);
    let g = cand_rows(sv, v, pat, rp, cs);
    lemma_from5_nodup(sv);
    lemma_keep_nodup(from5(sv), f);
    // The candidates' rows differ: their partsupp rows differ in the partsupp key.
    assert(g.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < g.len() && 0 <= j < g.len() && i != j implies g[i] != g[j] by {
            let (ci, cj) = (cs[i], cs[j]);
            if i < j { assert(ci < cj); } else { assert(cj < ci); }
            lemma_cand_row(sv, v, pat, rp, ci);
            lemma_cand_row(sv, v, pat, rp, cj);
            let ti = cand_tuple(sv, v, pat, rp, ci);
            let tj = cand_tuple(sv, v, pat, rp, cj);
            lemma_row5(sv, ti.0, ti.1, ci, ti.2, ti.3);
            lemma_row5(sv, tj.0, tj.1, cj, tj.2, tj.3);
            assert(g[i][16] == Val::Int(ps_pkeys(sv)[ci] as int) && g[i][17] == Val::Int(ps_skeys(sv)[ci] as int));
            assert(g[j][16] == Val::Int(ps_pkeys(sv)[cj] as int) && g[j][17] == Val::Int(ps_skeys(sv)[cj] as int));
            assert(ps_pkeys(sv)[ci] != ps_pkeys(sv)[cj] || ps_skeys(sv)[ci] != ps_skeys(sv)[cj]);
        }
    }
    assert forall|x: Row| kept.contains(x) <==> g.contains(x) by {
        lemma_keep_contains(from5(sv), f, x);
        lemma_from5_contains(sv, x);
        if kept.contains(x) {
            let (a, b, c, d, e) = choose|a: int, b: int, c: int, d: int, e: int| in5(sv, a, b, c, d, e) && x == #[trigger] row5(sv, a, b, c, d, e);
            assert(cand(sv, v, pat, rp, c));
            let i = choose|i: int| 0 <= i < cs.len() && cs[i] == c;
            lemma_cand_row(sv, v, pat, rp, c);
            assert(g[i] == x);
        }
        if g.contains(x) {
            let i = choose|i: int| 0 <= i < g.len() && g[i] == x;
            let c = cs[i];
            lemma_cand_row(sv, v, pat, rp, c);
            let t = cand_tuple(sv, v, pat, rp, c);
            assert(from5(sv).contains(x));
        }
    }
    lemma_nodup_same_multiset(kept, g);
}

} // verus!
