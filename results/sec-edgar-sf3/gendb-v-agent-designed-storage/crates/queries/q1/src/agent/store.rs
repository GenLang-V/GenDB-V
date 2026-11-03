//! From the stored layout of `pre` to the canonical groups of Q0.
//!
//! `ys` lists the projected rows (`canon::qcols`) in stored order. Row `i` of sub-run `s` is
//! `[adsh of s, line[i], stmt of group sg[s], rfile of group sg[s]]` (`yrow`); a group code `g` with non-NULL stmt
//! (`live`) has key `key_of(g)`, and distinct live codes have distinct keys (`lemma_key_injective`). `ys` is a
//! permutation of the canonical `xs` (`lemma_ys_perm`), so for every live group `g` the canonical count, line sum
//! and distinct adsh values are those of its sub-runs (`lemma_group_of_code`): `runs::run_rows`, `runs::run_vals`
//! and one adsh per sub-run (`adsh_runs`, distinct because each (adsh, group) pair is one sub-run). The canonical
//! group keys are exactly the keys of the live codes with rows (`lemma_gkeys_codes`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::layout::PartView;
use crate::stores::pre::interface::*;
use crate::stores::pre::interface::common::cols::*;
use crate::stores::pre::interface::common::runs::*;
use crate::stores::pre::interface::common::perm::*;
use crate::stores::pre::interface::common::text::*;
use crate::stores::pre::declaration::*;
use crate::link::query::*;
use crate::link::source::*;
use crate::link::join::{sum_of, count_term, sum_term, lemma_acc_sum_of, lemma_sum_of_append, lemma_sum_of_perm};
use super::canon::*;
use super::runs::*;

verus! {

pub open spec fn st_of(p: Seq<PartView>) -> Seq<u64> { u64s(p, P_SUB_START) }
pub open spec fn sg_of(p: Seq<PartView>) -> Seq<u64> { u64s(p, P_SUB_GROUP) }
pub open spec fn ln_of(p: Seq<PartView>) -> Seq<i32> { i32_part(p[P_LINE as int]) }

/// Group code `g` has a non-NULL stmt.
pub open spec fn live_of(p: Seq<PartView>, g: int) -> bool {
    u64s(p, P_GROUP_STMT)[g] != 0
}

/// The GROUP BY key `[stmt, rfile]` of group code `g`.
pub open spec fn key_of(p: Seq<PartView>, g: int) -> Row {
    seq![group_stmt_of(p, g), Val::Text(group_rfile_of(p, g))]
}

/// The projected row stored at position `i` of sub-run `s`.
pub open spec fn yrow(p: Seq<PartView>, s: int, i: int) -> Row {
    let g = sg_of(p)[s] as int;
    seq![Val::Text(sub_adsh_of(p, s)), Val::Int(ln_of(p)[i] as int), group_stmt_of(p, g), Val::Text(group_rfile_of(p, g))]
}

/// The projected rows in stored order.
pub open spec fn ys_of(p: Seq<PartView>, rels: Seq<Seq<Row>>) -> Seq<Row> {
    Seq::new(row_count(p) as nat, |i: int| proj(stored_row(p, rels, i), qcols()))
}

/// The layout facts the kernel needs follow from the storage layout.
pub proof fn lemma_layout_facts(p: Seq<PartView>)
    requires pre_layout_ok(p),
    ensures
        starts_ok(st_of(p), sub_count(p)),
        st_of(p)[0] == 0,
        st_of(p)[sub_count(p)] == row_count(p),
        sg_of(p).len() == sub_count(p),
        ln_of(p).len() == row_count(p),
        forall|s: int| 0 <= s < sub_count(p) ==> #[trigger] sg_of(p)[s] < group_count(p),
        u64s(p, P_GROUP_RFILE).len() == group_count(p),
        row_count(p) <= u64::MAX,
{
    lemma_permutation_facts(u64s(p, P_ORIG), row_count(p) as nat);
    assert forall|s: int| 0 <= s < sub_count(p) implies #[trigger] sg_of(p)[s] < group_count(p) by {
        assert(u64s(p, P_SUB_ADSH)[s] < adsh_count(p));
    }
}

/// Stored row `i` of sub-run `s` projects to `yrow(p, s, i)`.
pub proof fn lemma_ys_row(p: Seq<PartView>, rels: Seq<Seq<Row>>, s: int, i: int)
    requires represents(p, rels), 0 <= s < sub_count(p), st_of(p)[s] <= i < st_of(p)[s + 1],
    ensures 0 <= i < row_count(p), ys_of(p, rels)[i] == yrow(p, s, i),
{
    lemma_layout_facts(p);
    if s + 1 < sub_count(p) {
        assert(st_of(p)[s + 1] < st_of(p)[sub_count(p)]);
    }
    let row = stored_row(p, rels, i);
    assert(stored_cols_ok(p, row, i));
    assert(sub_cols_ok(p, row, s));
    assert(proj(row, qcols()) =~= yrow(p, s, i));
}

/// The stored-order rows are a permutation of the canonical rows, position `orig[i]` holding stored row `i`.
pub proof fn lemma_ys_perm(p: Seq<PartView>, db: Database)
    requires represents(p, stored_relations(db)),
    ensures ({
        let ys = ys_of(p, stored_relations(db));
        let xs = xs_of(db);
        &&& xs.len() == row_count(p)
        &&& ys.len() == row_count(p)
        &&& xs.to_multiset() == ys.to_multiset()
        &&& forall|i: int| 0 <= i < row_count(p) ==> 0 <= #[trigger] u64s(p, P_ORIG)[i] < row_count(p)
                && xs[u64s(p, P_ORIG)[i] as int] == ys[i]
    }),
{
    let rels = stored_relations(db);
    let n = row_count(p);
    let t = db.tables[3];
    let r = rels[0];
    let ys = ys_of(p, rels);
    let xs = xs_of(db);
    let f = |row: Row| proj(row, qcols());
    let sr = Seq::new(n as nat, |i: int| stored_row(p, rels, i));
    lemma_stored_rows_multiset(p, rels);
    lemma_map_multiset(sr, r, f);
    assert(sr.map_values(f) =~= ys);
    assert forall|k: int| 0 <= k < qcols().len() implies #[trigger] qcols()[k] < stored_cols_t0().len() by {}
    lemma_proj_all_compose(t, stored_cols_t0(), qcols());
    assert(compose_cols(stored_cols_t0(), qcols()) =~= qcols());
    assert(r.map_values(f) =~= proj_all(r, qcols()));
    assert(proj_all(r, qcols()) == xs);
    lemma_permutation_facts(u64s(p, P_ORIG), n as nat);
    assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] u64s(p, P_ORIG)[i] < n
        && xs[u64s(p, P_ORIG)[i] as int] == ys[i] by {
        let j = u64s(p, P_ORIG)[i] as int;
        assert(proj_all(r, qcols())[j] == proj(r[j], qcols()));
    }
}

/// Distinct live group codes have distinct keys.
pub proof fn lemma_key_injective(p: Seq<PartView>, g1: int, g2: int)
    requires
        pre_layout_ok(p),
        0 <= g1 < group_count(p), 0 <= g2 < group_count(p),
        live_of(p, g1), live_of(p, g2),
        key_of(p, g1) == key_of(p, g2),
    ensures g1 == g2,
{
    let gs = u64s(p, P_GROUP_STMT);
    let gr = u64s(p, P_GROUP_RFILE);
    assert(key_of(p, g1)[0] == key_of(p, g2)[0]);
    assert(key_of(p, g1)[1] == key_of(p, g2)[1]);
    lemma_dict_codes(u64_part(p[P_STMT_OFF as int]), u8_part(p[P_STMT_OFF + 1]), stmt_count(p), gs[g1] - 1, gs[g2] - 1);
    lemma_dict_codes(u64_part(p[P_RFILE_OFF as int]), u8_part(p[P_RFILE_OFF + 1]), rfile_count(p), gr[g1] as int, gr[g2] as int);
    assert(gs[g1] == gs[g2] && gr[g1] == gr[g2]);
    if g1 < g2 {
        assert(pair_lt(gs[g1], gr[g1], gs[g2], gr[g2]));
    } else if g2 < g1 {
        assert(pair_lt(gs[g2], gr[g2], gs[g1], gr[g1]));
    }
}

/// Two sub-runs of one group belong to different filings.
pub proof fn lemma_adsh_distinct(p: Seq<PartView>, s1: int, s2: int)
    requires pre_layout_ok(p), 0 <= s1 < s2 < sub_count(p), sg_of(p)[s1] == sg_of(p)[s2],
    ensures sub_adsh_of(p, s1) != sub_adsh_of(p, s2),
{
    let sa = u64s(p, P_SUB_ADSH);
    assert(pair_lt(sa[s1], sg_of(p)[s1], sa[s2], sg_of(p)[s2]));
    assert(sa[s1] < adsh_count(p) && sa[s2] < adsh_count(p));
    lemma_dict_codes(u64_part(p[P_ADSH_OFF as int]), u8_part(p[P_ADSH_OFF + 1]), adsh_count(p), sa[s1] as int, sa[s2] as int);
}

/// A stored row of sub-run `s` belongs to the group of live code `g` exactly when `s` is a sub-run of `g`.
pub proof fn lemma_yrow_hit(p: Seq<PartView>, s: int, i: int, g: int)
    requires pre_layout_ok(p), 0 <= s < sub_count(p), 0 <= g < group_count(p), live_of(p, g),
    ensures
        hit(gq(), yrow(p, s, i), key_of(p, g)) <==> sg_of(p)[s] == g,
        (gq().qual)(yrow(p, s, i)) <==> live_of(p, sg_of(p)[s] as int),
        (gq().key)(yrow(p, s, i)) == key_of(p, sg_of(p)[s] as int),
        line_of(yrow(p, s, i)) == ln_of(p)[i] as int,
        yrow(p, s, i)[0] == Val::Text(sub_adsh_of(p, s)),
{
    lemma_layout_facts(p);
    let h = sg_of(p)[s] as int;
    let y = yrow(p, s, i);
    assert((gq().key)(y) =~= key_of(p, h));
    if hit(gq(), y, key_of(p, g)) {
        lemma_key_injective(p, h, g);
    }
}

// ------------------------------------------------------------------------------------------------ sums over runs

/// Rows none of which hits `k` contribute nothing.
proof fn lemma_sum_none(ys: Seq<Row>, k: Row)
    requires forall|i: int| 0 <= i < ys.len() ==> !hit(gq(), #[trigger] ys[i], k),
    ensures
        sum_of(ys, count_term(gq(), k)) == 0,
        sum_of(ys, sum_term(gq(), k, 0)) == 0,
        forall|v: Val| !has_adsh(ys, k, v),
    decreases ys.len(),
{
    if ys.len() > 0 {
        let yi = ys.drop_last();
        assert forall|i: int| 0 <= i < yi.len() implies !hit(gq(), #[trigger] yi[i], k) by { assert(yi[i] == ys[i]); }
        lemma_sum_none(yi, k);
        assert(!hit(gq(), ys[ys.len() - 1], k));
    }
}

/// Rows that all hit `k`: their count, and their line sum when row `i` has line `l[a + i]`.
proof fn lemma_sum_all(ys: Seq<Row>, k: Row, l: Seq<i32>, a: int)
    requires
        forall|i: int| 0 <= i < ys.len() ==> hit(gq(), #[trigger] ys[i], k) && line_of(ys[i]) == l[a + i] as int,
    ensures
        sum_of(ys, count_term(gq(), k)) == ys.len(),
        sum_of(ys, sum_term(gq(), k, 0)) == line_total(l, a, a + ys.len()),
    decreases ys.len(),
{
    if ys.len() > 0 {
        let yi = ys.drop_last();
        assert forall|i: int| 0 <= i < yi.len() implies hit(gq(), #[trigger] yi[i], k) && line_of(yi[i]) == l[a + i] as int by {
            assert(yi[i] == ys[i]);
        }
        lemma_sum_all(yi, k, l, a);
        assert(hit(gq(), ys[ys.len() - 1], k));
    }
}

/// `has_adsh` over a concatenation.
proof fn lemma_has_adsh_append(a: Seq<Row>, b: Seq<Row>, k: Row, v: Val)
    ensures has_adsh(a + b, k, v) <==> has_adsh(a, k, v) || has_adsh(b, k, v),
{
    let c = a + b;
    if has_adsh(c, k, v) {
        let i = choose|i: int| 0 <= i < c.len() && #[trigger] hit(gq(), c[i], k) && c[i][0] == v;
        if i < a.len() {
            assert(c[i] == a[i]);
            assert(hit(gq(), a[i], k));
        } else {
            assert(c[i] == b[i - a.len()]);
            assert(hit(gq(), b[i - a.len()], k));
        }
    }
    if has_adsh(a, k, v) {
        let i = choose|i: int| 0 <= i < a.len() && #[trigger] hit(gq(), a[i], k) && a[i][0] == v;
        assert(c[i] == a[i]);
        assert(hit(gq(), c[i], k));
    }
    if has_adsh(b, k, v) {
        let i = choose|i: int| 0 <= i < b.len() && #[trigger] hit(gq(), b[i], k) && b[i][0] == v;
        assert(c[a.len() + i] == b[i]);
        assert(hit(gq(), c[a.len() + i], k));
    }
}

/// The adsh values of the sub-runs `[0, s)` of group code `g`, one per sub-run, in run order.
pub open spec fn adsh_runs(p: Seq<PartView>, g: int, s: int) -> Seq<Val>
    decreases s,
{
    if s <= 0 {
        Seq::empty()
    } else if sg_of(p)[s - 1] == g {
        adsh_runs(p, g, s - 1).push(Val::Text(sub_adsh_of(p, s - 1)))
    } else {
        adsh_runs(p, g, s - 1)
    }
}

/// One sub-run `s`: its rows' contribution to the group of live code `g`.
proof fn lemma_one_run(p: Seq<PartView>, rels: Seq<Seq<Row>>, g: int, s: int)
    requires represents(p, rels), 0 <= s < sub_count(p), 0 <= g < group_count(p), live_of(p, g),
    ensures ({
        let run = ys_of(p, rels).subrange(st_of(p)[s] as int, st_of(p)[s + 1] as int);
        let k = key_of(p, g);
        &&& sum_of(run, count_term(gq(), k)) == if sg_of(p)[s] == g { st_of(p)[s + 1] - st_of(p)[s] } else { 0 }
        &&& sum_of(run, sum_term(gq(), k, 0)) == if sg_of(p)[s] == g {
                line_total(ln_of(p), st_of(p)[s] as int, st_of(p)[s + 1] as int) } else { 0 }
        &&& forall|v: Val| has_adsh(run, k, v) <==> (sg_of(p)[s] == g && v == Val::Text(sub_adsh_of(p, s)))
    }),
{
    lemma_layout_facts(p);
    let (a, b) = (st_of(p)[s] as int, st_of(p)[s + 1] as int);
    assert(a < b);
    if s + 1 < sub_count(p) { assert(st_of(p)[s + 1] < st_of(p)[sub_count(p)]); }
    let ys = ys_of(p, rels);
    let run = ys.subrange(a, b);
    let k = key_of(p, g);
    assert forall|i: int| 0 <= i < run.len() implies #[trigger] run[i] == yrow(p, s, a + i) by {
        lemma_ys_row(p, rels, s, a + i);
    }
    assert forall|i: int| 0 <= i < run.len() implies
        (hit(gq(), #[trigger] run[i], k) <==> sg_of(p)[s] == g) && line_of(run[i]) == ln_of(p)[a + i] as int
        && run[i][0] == Val::Text(sub_adsh_of(p, s)) by {
        lemma_yrow_hit(p, s, a + i, g);
    }
    if sg_of(p)[s] == g {
        lemma_sum_all(run, k, ln_of(p), a);
        assert forall|v: Val| has_adsh(run, k, v) <==> v == Val::Text(sub_adsh_of(p, s)) by {
            if v == Val::Text(sub_adsh_of(p, s)) {
                assert(hit(gq(), run[0], k));
            }
        }
    } else {
        lemma_sum_none(run, k);
    }
}

/// The stored rows of the sub-runs `[0, s)`: per live group code `g`, the count, line sum and adsh values of the
/// group are those of its sub-runs.
proof fn lemma_runs_prefix(p: Seq<PartView>, rels: Seq<Seq<Row>>, g: int, s: int)
    requires represents(p, rels), 0 <= s <= sub_count(p), 0 <= g < group_count(p), live_of(p, g),
    ensures ({
        let pre = ys_of(p, rels).subrange(0, st_of(p)[s] as int);
        let k = key_of(p, g);
        let d = adsh_runs(p, g, s);
        &&& sum_of(pre, count_term(gq(), k)) == run_rows(st_of(p), sg_of(p), g, 0, s)
        &&& sum_of(pre, sum_term(gq(), k, 0)) == run_vals(st_of(p), sg_of(p), ln_of(p), g, 0, s)
        &&& d.no_duplicates()
        &&& d.len() == run_count(sg_of(p), g, 0, s)
        &&& forall|v: Val| #[trigger] d.contains(v) <==> has_adsh(pre, k, v)
        &&& forall|v: Val| #[trigger] d.contains(v) ==> exists|t: int| 0 <= t < s && sg_of(p)[t] == g && v == Val::Text(sub_adsh_of(p, t))
    }),
    decreases s,
{
    lemma_layout_facts(p);
    let ys = ys_of(p, rels);
    let k = key_of(p, g);
    let pre = ys.subrange(0, st_of(p)[s] as int);
    let d = adsh_runs(p, g, s);
    if s == 0 {
        assert(pre =~= Seq::<Row>::empty());
        assert(d =~= Seq::<Val>::empty());
    } else {
        let s0 = s - 1;
        lemma_runs_prefix(p, rels, g, s0);
        lemma_one_run(p, rels, g, s0);
        let (a, b) = (st_of(p)[s0] as int, st_of(p)[s] as int);
        if s < sub_count(p) { assert(st_of(p)[s] < st_of(p)[sub_count(p)]); }
        let pi = ys.subrange(0, a);
        let run = ys.subrange(a, b);
        assert(pre =~= pi + run);
        lemma_sum_of_append(pi, run, count_term(gq(), k));
        lemma_sum_of_append(pi, run, sum_term(gq(), k, 0));
        let di = adsh_runs(p, g, s0);
        assert forall|v: Val| has_adsh(pre, k, v) <==> has_adsh(pi, k, v) || has_adsh(run, k, v) by {
            lemma_has_adsh_append(pi, run, k, v);
        }
        if sg_of(p)[s0] == g {
            let x = Val::Text(sub_adsh_of(p, s0));
            assert(d == di.push(x));
            assert(!di.contains(x)) by {
                if di.contains(x) {
                    let t = choose|t: int| 0 <= t < s0 && sg_of(p)[t] == g && x == Val::Text(sub_adsh_of(p, t));
                    lemma_adsh_distinct(p, t, s0);
                }
            }
            assert forall|a1: int, b1: int| 0 <= a1 < b1 < d.len() implies d[a1] != d[b1] by {
                if b1 == di.len() {
                    assert(di.contains(d[a1]));
                } else {
                    assert(d[a1] == di[a1] && d[b1] == di[b1]);
                }
            }
            assert forall|v: Val| #[trigger] d.contains(v) <==> has_adsh(pre, k, v) by {
                if d.contains(v) && v != x {
                    let i = choose|i: int| 0 <= i < d.len() && d[i] == v;
                    assert(di[i] == v);
                    assert(di.contains(v));
                }
                if di.contains(v) {
                    let i = choose|i: int| 0 <= i < di.len() && di[i] == v;
                    assert(d[i] == v);
                }
                assert(d[di.len() as int] == x);
            }
            assert forall|v: Val| #[trigger] d.contains(v) implies exists|t: int| 0 <= t < s && sg_of(p)[t] == g && v == Val::Text(sub_adsh_of(p, t)) by {
                if v != x {
                    let i = choose|i: int| 0 <= i < d.len() && d[i] == v;
                    assert(di[i] == v);
                    assert(di.contains(v));
                    let t = choose|t: int| 0 <= t < s0 && sg_of(p)[t] == g && v == Val::Text(sub_adsh_of(p, t));
                    assert(0 <= t < s);
                } else {
                    assert(0 <= s0 < s && sg_of(p)[s0] == g);
                }
            }
        } else {
            assert(d == di);
            assert forall|v: Val| #[trigger] d.contains(v) implies exists|t: int| 0 <= t < s && sg_of(p)[t] == g && v == Val::Text(sub_adsh_of(p, t)) by {
                let t = choose|t: int| 0 <= t < s0 && sg_of(p)[t] == g && v == Val::Text(sub_adsh_of(p, t));
                assert(0 <= t < s);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------ the canonical groups

/// The canonical group of live code `g`: its count, line sum and adsh values are those of its sub-runs.
pub proof fn lemma_group_of_code(p: Seq<PartView>, db: Database, g: int)
    requires represents(p, stored_relations(db)), 0 <= g < group_count(p), live_of(p, g),
    ensures ({
        let xs = xs_of(db);
        let k = key_of(p, g);
        let d = adsh_runs(p, g, sub_count(p));
        &&& gcount(gq(), xs, k) == run_rows(st_of(p), sg_of(p), g, 0, sub_count(p))
        &&& gsum(gq(), xs, k, 0) == run_vals(st_of(p), sg_of(p), ln_of(p), g, 0, sub_count(p))
        &&& gcount(gq(), ys_of(p, stored_relations(db)), k) == gcount(gq(), xs, k)
        &&& d.no_duplicates()
        &&& d.len() == run_count(sg_of(p), g, 0, sub_count(p))
        &&& forall|v: Val| #[trigger] d.contains(v) <==> has_adsh(xs, k, v)
    }),
{
    let rels = stored_relations(db);
    let ys = ys_of(p, rels);
    let xs = xs_of(db);
    let k = key_of(p, g);
    lemma_layout_facts(p);
    lemma_ys_perm(p, db);
    lemma_runs_prefix(p, rels, g, sub_count(p));
    assert(ys.subrange(0, st_of(p)[sub_count(p)] as int) =~= ys);
    lemma_acc_sum_of(gq(), xs, k, 0);
    lemma_acc_sum_of(gq(), ys, k, 0);
    lemma_sum_of_perm(xs, ys, count_term(gq(), k));
    lemma_sum_of_perm(xs, ys, sum_term(gq(), k, 0));
    let d = adsh_runs(p, g, sub_count(p));
    assert forall|v: Val| #[trigger] d.contains(v) <==> has_adsh(xs, k, v) by {
        if has_adsh(xs, k, v) {
            let j = choose|j: int| 0 <= j < xs.len() && #[trigger] hit(gq(), xs[j], k) && xs[j][0] == v;
            xs.to_multiset_ensures();
            ys.to_multiset_ensures();
            assert(xs.contains(xs[j]));
            assert(xs.to_multiset().count(xs[j]) > 0);
            assert(ys.to_multiset().count(xs[j]) > 0);
            assert(ys.contains(xs[j]));
            let i = choose|i: int| 0 <= i < ys.len() && ys[i] == xs[j];
            assert(hit(gq(), ys[i], k));
        }
        if has_adsh(ys, k, v) {
            let i = choose|i: int| 0 <= i < ys.len() && #[trigger] hit(gq(), ys[i], k) && ys[i][0] == v;
            xs.to_multiset_ensures();
            ys.to_multiset_ensures();
            assert(ys.contains(ys[i]));
            assert(ys.to_multiset().count(ys[i]) > 0);
            assert(xs.to_multiset().count(ys[i]) > 0);
            assert(xs.contains(ys[i]));
            let j = choose|j: int| 0 <= j < xs.len() && xs[j] == ys[i];
            assert(hit(gq(), xs[j], k));
        }
    }
}

/// The canonical group keys are the keys of the live codes with rows.
pub proof fn lemma_gkeys_codes(p: Seq<PartView>, db: Database, k: Row)
    requires represents(p, stored_relations(db)),
    ensures
        gkeys(gq(), xs_of(db)).contains(k) <==> exists|g: int| 0 <= g < group_count(p) && live_of(p, g)
            && run_rows(st_of(p), sg_of(p), g, 0, sub_count(p)) > 0 && #[trigger] key_of(p, g) == k,
{
    let rels = stored_relations(db);
    let ys = ys_of(p, rels);
    let xs = xs_of(db);
    lemma_layout_facts(p);
    lemma_ys_perm(p, db);
    lemma_gkeys(gq(), xs);
    if gkeys(gq(), xs).contains(k) {
        lemma_acc_sum_of(gq(), xs, k, 0);
        lemma_acc_sum_of(gq(), ys, k, 0);
        lemma_sum_of_perm(xs, ys, count_term(gq(), k));
        lemma_count_witness(gq(), ys, k);
        let i = choose|i: int| 0 <= i < ys.len() && #[trigger] hit(gq(), ys[i], k);
        let st = st_of(p);
        assert(runs_partition_ok(st, sub_count(p), row_count(p)));
        lemma_run_of(st, sub_count(p), row_count(p), i);
        let s = run_of(st, sub_count(p), i);
        lemma_ys_row(p, rels, s, i);
        let g = sg_of(p)[s] as int;
        lemma_yrow_hit(p, s, i, g);
        assert(live_of(p, g));
        assert(key_of(p, g) == k);
        lemma_group_of_code(p, db, g);
        assert(0 <= g < group_count(p));
    }
    if exists|g: int| 0 <= g < group_count(p) && live_of(p, g)
        && run_rows(st_of(p), sg_of(p), g, 0, sub_count(p)) > 0 && #[trigger] key_of(p, g) == k {
        let g = choose|g: int| 0 <= g < group_count(p) && live_of(p, g)
            && run_rows(st_of(p), sg_of(p), g, 0, sub_count(p)) > 0 && #[trigger] key_of(p, g) == k;
        lemma_group_of_code(p, db, g);
    }
}

} // verus!
