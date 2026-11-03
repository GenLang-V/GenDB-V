//! Assembly of the tasks' results. The name ranges of the tasks partition the name codes, so the filings of all
//! tasks (`pall`) are every `sub` row with qualifying triples, once each, and the groups of all tasks (`gg`) have
//! distinct keys: each group's exact count, sum and mass are its key's accumulators (`lemma_group_vals`), and a key
//! of no group has no qualifying row.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::*;
use crate::spec::order::{ordered_ok, sorted_by, slice_rows, keys_cmp, key_cmp, sort_rows};
use crate::spec::limits::int8_max;
use crate::link::expr::i128_max;
use crate::spec::numeric::pow10;
use crate::bridge::order::{lemma_sort_rows, all_keys_ok, keys_ok, key_ok, key_val};
use crate::bridge::typing::val_family;
use crate::query::query_spec_at;
use crate::exec::value::EVal;
use crate::gendb_entry::{Answer, answer_meets, bound_db, outcome_ok};
use crate::gendb_entry::runtime::QueryError;
use crate::agent::meaning::{order_keys, ps_ok, tables_ok, lemma_tables_ok, lemma_denote_body, lemma_body_count_err,
    lemma_body_capacity, lemma_query_shape};
use crate::agent::bound::lemma_bound_base;
use crate::stores::sub::interface as si;
use crate::stores::sub::interface::common::text as stext;
use crate::agent::meaning::{qspec, joined};
use crate::agent::views::*;
use crate::agent::reorg::{cell_l, tri, lemma_acc_tri};
use crate::agent::fspec::*;
use crate::agent::filings::{Filing, FilingOut, filings_ok};
use crate::agent::join::*;
use crate::agent::common::sums::*;

verus! {

/// Number of distinct names (codes `0..name_count`).
pub open spec fn name_count(sv: StoresView) -> int {
    crate::stores::sub::interface::common::cols::text_count(sv.sub, si::P_NAME_DICT_OFF as int)
}

/// The tasks merged so far cover the name codes below `nlo`: their filings `pall` (distinct `sub` rows, every row
/// of those names with qualifying triples), their groups `gg` (distinct codes) and the groups' sums.
pub open spec fn merged_ok(sv: StoresView, ps: Seq<Literal>, nlo: int, pall: Seq<Filing>, gg: Seq<Partial>) -> bool {
    &&& forall|t: int| 0 <= t < pall.len() ==> filing_ok(sv, ps, #[trigger] pall[t]) && pall[t].nm < nlo
    &&& forall|x: int, y: int| 0 <= x < y < pall.len() ==> (#[trigger] pall[x]).j != (#[trigger] pall[y]).j
    &&& forall|j: int| 0 <= j < s_count(sv) && #[trigger] stext::u64_part(sv.sub[si::P_NAME_CODES as int])[j] < nlo
        ==> (zero_j(sv, ps, j) || exists|t: int| 0 <= t < pall.len() && pall[t].j == j)
    &&& forall|k: Row, w: int| #[trigger] psum(sv, ps, gg, 0, gg.len() as int, k, w)
        == tsum(pall, |f: Filing| fsum(sv, ps, f, k, w))
    &&& forall|x: int| 0 <= x < gg.len() ==> exact_ok(#[trigger] gg[x]) && codes_ok(sv, gg[x]) && gg[x].nm < nlo
    &&& forall|x: int, y: int| 0 <= x < y < gg.len() ==> !same_code(#[trigger] gg[x], #[trigger] gg[y])
}

pub proof fn lemma_merged_init(sv: StoresView, ps: Seq<Literal>)
    ensures merged_ok(sv, ps, 0, Seq::empty(), Seq::empty()),
{
}

/// A sum over the first `n` elements by index is the sum over the prefix.
pub proof fn lemma_isum_tsum<T>(s: Seq<T>, n: int, h: spec_fn(T) -> int)
    requires 0 <= n <= s.len(),
    ensures isum(0, n, |x: int| h(s[x])) == tsum(s.subrange(0, n), h),
    decreases n,
{
    if n > 0 {
        lemma_isum_tsum(s, n - 1, h);
        assert(s.subrange(0, n).drop_last() =~= s.subrange(0, n - 1));
    }
}

/// Merge one more task: the filings and groups of the names `[nlo, nhi)`.
pub proof fn lemma_merge_step(sv: StoresView, ps: Seq<Literal>, nlo: int, nhi: int, pall: Seq<Filing>, gg: Seq<Partial>,
    a: FilingOut, d: JoinOut)
    requires
        merged_ok(sv, ps, nlo, pall, gg), nlo <= nhi,
        filings_ok(sv, ps, nlo, nhi, a), !a.overflow,
        groups_ok(sv, ps, a.filings@, a.len as int, d),
    ensures merged_ok(sv, ps, nhi, pall + a.pushed@, gg + d.groups@),
{
    broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};
    let p = a.pushed@;
    let fl = a.filings@;
    let nf = a.len as int;
    let g = d.groups@;
    let pall2 = pall + p;
    let gg2 = gg + g;
    assert forall|t: int| 0 <= t < pall2.len() implies filing_ok(sv, ps, #[trigger] pall2[t]) && pall2[t].nm < nhi by {
        if t >= pall.len() {
            assert(pall2[t] == p[t - pall.len()]);
        }
    }
    assert forall|x: int, y: int| 0 <= x < y < pall2.len() implies (#[trigger] pall2[x]).j != (#[trigger] pall2[y]).j by {
        if y >= pall.len() && x < pall.len() {
            assert(pall2[y] == p[y - pall.len()]);
            assert(pall2[x].nm < nlo && pall2[y].nm >= nlo);
        } else if x >= pall.len() {
            assert(pall2[x] == p[x - pall.len()] && pall2[y] == p[y - pall.len()]);
        }
    }
    assert forall|j: int| 0 <= j < s_count(sv) && #[trigger] stext::u64_part(sv.sub[si::P_NAME_CODES as int])[j] < nhi
        implies (zero_j(sv, ps, j) || exists|t: int| 0 <= t < pall2.len() && pall2[t].j == j) by {
        if stext::u64_part(sv.sub[si::P_NAME_CODES as int])[j] < nlo {
            if !zero_j(sv, ps, j) {
                let t = choose|t: int| 0 <= t < pall.len() && pall[t].j == j;
                assert(pall2[t] == pall[t]);
            }
        } else if !zero_j(sv, ps, j) {
            let t = choose|t: int| 0 <= t < p.len() && p[t].j == j;
            assert(pall2[pall.len() + t] == p[t]);
        }
    }
    assert(fl.subrange(0, nf).to_multiset() == p.to_multiset());
    assert forall|k: Row, w: int| #[trigger] psum(sv, ps, gg2, 0, gg2.len() as int, k, w)
        == tsum(pall2, |f: Filing| fsum(sv, ps, f, k, w)) by {
        let h = |f: Filing| fsum(sv, ps, f, k, w);
        assert(g.subrange(0, g.len() as int) =~= g);
        lemma_psum_append(sv, ps, gg, g, g.len() as int, k, w);
        lemma_isum_tsum(fl, nf, h);
        lemma_isum_ext(0, nf, |x: int| h(fl[x]), |x: int| fsum(sv, ps, fl[x], k, w));
        lemma_tsum_perm(fl.subrange(0, nf), p, h);
        lemma_tsum_append(pall, p, h);
    }
    assert forall|x: int| 0 <= x < gg2.len() implies exact_ok(#[trigger] gg2[x]) && codes_ok(sv, gg2[x]) && gg2[x].nm < nhi
        && (x >= gg.len() ==> gg2[x].nm >= nlo) by {
        if x >= gg.len() {
            let gx = g[x - gg.len()];
            assert(gg2[x] == gx);
            let y = choose|y: int| 0 <= y < nf && gx.nm == #[trigger] fl[y].nm;
            let v = fl.subrange(0, nf)[y];
            assert(v == fl[y]);
            assert(fl.subrange(0, nf).contains(v));
            assert(p.to_multiset().count(v) > 0);
            assert(p.contains(v));
        }
    }
    assert forall|x: int, y: int| 0 <= x < y < gg2.len() implies !same_code(#[trigger] gg2[x], #[trigger] gg2[y]) by {
        if x >= gg.len() {
            assert(gg2[x] == g[x - gg.len()] && gg2[y] == g[y - gg.len()]);
        } else if y >= gg.len() {
            assert(exact_ok(gg2[y]) && gg2[y].nm >= nlo);
            assert(gg2[x].nm < nlo);
        }
    }
}

proof fn lemma_tsum_map_j(fs: Seq<Filing>, h: spec_fn(int) -> int)
    ensures tsum(fs, |f: Filing| h(f.j as int)) == lsum(fs.map_values(|f: Filing| f.j as int), h),
    decreases fs.len(),
{
    if fs.len() > 0 {
        lemma_tsum_map_j(fs.drop_last(), h);
        assert(fs.map_values(|f: Filing| f.j as int).drop_last() =~= fs.drop_last().map_values(|f: Filing| f.j as int));
    }
}

/// With every name merged, the triple sums are the filings' sums.
proof fn lemma_tri_pall(sv: StoresView, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>, k: Row, w: int)
    requires layouts(sv), merged_ok(sv, ps, name_count(sv), pall, gg),
    ensures tri(sv, ps, k, w) == tsum(pall, |f: Filing| fsum(sv, ps, f, k, w)),
{
    let sp = sv.sub;
    assert(si::sub_layout_ok(sp));
    let l = pall.map_values(|f: Filing| f.j as int);
    let cl = |j: int| cell_l(sv, ps, k, w, j);
    assert forall|a: int, b: int| 0 <= a < l.len() && 0 <= b < l.len() && a != b implies l[a] != l[b] by {
        if a < b {
            assert(pall[a].j != pall[b].j);
        } else {
            assert(pall[b].j != pall[a].j);
        }
    }
    assert forall|t: int| 0 <= t < l.len() implies 0 <= #[trigger] l[t] < s_count(sv) by {
        assert(filing_ok(sv, ps, pall[t]));
    }
    assert forall|j: int| 0 <= j < s_count(sv) && #[trigger] cl(j) != 0 implies l.contains(j) by {
        if zero_j(sv, ps, j) {
            lemma_zero_cells(sv, ps, k, w, j);
        }
        assert(stext::u64_part(sp[si::P_NAME_CODES as int])[j] < name_count(sv));
        let t = choose|t: int| 0 <= t < pall.len() && pall[t].j == j;
        assert(l[t] == j);
    }
    lemma_isum_list(0, s_count(sv), l, cl);
    lemma_isum_ext(0, s_count(sv), cl, |j: int| cell_l(sv, ps, k, w, j));
    lemma_tsum_map_j(pall, cl);
    let h1 = |f: Filing| cl(f.j as int);
    let h2 = |f: Filing| fsum(sv, ps, f, k, w);
    assert forall|t: int| 0 <= t < pall.len() implies #[trigger] h1(pall[t]) == h2(pall[t]) by {
        lemma_filing_cells(sv, ps, pall[t], k, w);
    }
    lemma_tsum_ext(pall, h1, h2);
}

/// With every name merged, the accumulators of every key are the groups' sums.
pub proof fn lemma_accounting(sv: StoresView, db: Database, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>, k: Row)
    requires base(sv, db), layouts(sv), merged_ok(sv, ps, name_count(sv), pall, gg),
    ensures
        gcount(qspec(ps), joined(db), k) == psum(sv, ps, gg, 0, gg.len() as int, k, 0),
        gsum(qspec(ps), joined(db), k, 0) == psum(sv, ps, gg, 0, gg.len() as int, k, 1),
        gabs(qspec(ps), joined(db), k, 0) == psum(sv, ps, gg, 0, gg.len() as int, k, 2),
{
    lemma_acc_tri(sv, db, ps, k);
    lemma_tri_pall(sv, ps, pall, gg, k, 0);
    lemma_tri_pall(sv, ps, pall, gg, k, 1);
    lemma_tri_pall(sv, ps, pall, gg, k, 2);
}

/// Group `x`'s exact values are the accumulators of its key.
pub proof fn lemma_group_vals(sv: StoresView, db: Database, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>, x: int)
    requires base(sv, db), layouts(sv), merged_ok(sv, ps, name_count(sv), pall, gg), 0 <= x < gg.len(),
    ensures
        gcount(qspec(ps), joined(db), kd(sv, ps, gg[x])) == gg[x].gc@,
        gsum(qspec(ps), joined(db), kd(sv, ps, gg[x]), 0) == gg[x].gs@,
        gabs(qspec(ps), joined(db), kd(sv, ps, gg[x]), 0) == gg[x].gm@,
{
    let k = kd(sv, ps, gg[x]);
    lemma_accounting(sv, db, ps, pall, gg, k);
    assert forall|w: int| psum(sv, ps, gg, 0, gg.len() as int, k, w) == pval(gg[x], w) by {
        let f = |t: int| pterm(sv, ps, gg[t], k, w);
        assert forall|t: int| 0 <= t < gg.len() && t != x implies #[trigger] f(t) == 0 by {
            if kd(sv, ps, gg[t]) == k {
                lemma_kd_inj(sv, ps, gg[t], gg[x]);
                if t < x {
                    assert(!same_code(gg[t], gg[x]));
                } else {
                    assert(!same_code(gg[x], gg[t]));
                }
            }
        }
        lemma_isum_single(0, gg.len() as int, x, f);
    }
    assert(psum(sv, ps, gg, 0, gg.len() as int, k, 0) == pval(gg[x], 0));
    assert(psum(sv, ps, gg, 0, gg.len() as int, k, 1) == pval(gg[x], 1));
    assert(psum(sv, ps, gg, 0, gg.len() as int, k, 2) == pval(gg[x], 2));
}

/// A key of no group has no qualifying row.
pub proof fn lemma_no_group(sv: StoresView, db: Database, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>, k: Row)
    requires
        base(sv, db), layouts(sv), merged_ok(sv, ps, name_count(sv), pall, gg),
        forall|x: int| 0 <= x < gg.len() ==> kd(sv, ps, #[trigger] gg[x]) != k,
    ensures gcount(qspec(ps), joined(db), k) == 0, gabs(qspec(ps), joined(db), k, 0) == 0,
{
    lemma_accounting(sv, db, ps, pall, gg, k);
    lemma_isum_zero(0, gg.len() as int, |t: int| pterm(sv, ps, gg[t], k, 0));
    lemma_isum_zero(0, gg.len() as int, |t: int| pterm(sv, ps, gg[t], k, 2));
}

// ------------------------------------------------------------------------------------------------ answers

/// The output row of group `x`: its key, its sum (scale 4) and its count.
pub open spec fn rrow(sv: StoresView, ps: Seq<Literal>, x: Partial) -> Row {
    kd(sv, ps, x) + seq![Val::Num { coeff: x.sum as int, scale: 4 }, Val::Int(x.cnt as int)]
}

pub open spec fn no_flags(gg: Seq<Partial>) -> bool {
    forall|x: int| 0 <= x < gg.len() ==> (#[trigger] gg[x]).cnt != CNT_OVER && gg[x].mass != MASS_OVER
}

/// The final lists: the candidates (sorted by sum, descending) and the other groups are all groups; every
/// candidate's sum is at least every other group's; with other groups there are at least `TOP` candidates; the
/// output is the first `TOP` candidates' rows.
pub open spec fn lists_ok(sv: StoresView, ps: Seq<Literal>, gg: Seq<Partial>, cand: Seq<Partial>, nonc: Seq<Partial>,
    out: Seq<Row>) -> bool {
    &&& (cand + nonc).to_multiset() == gg.to_multiset()
    &&& forall|a: int, b: int| 0 <= a < b < cand.len() ==> (#[trigger] cand[a]).sum >= (#[trigger] cand[b]).sum
    &&& forall|a: int, b: int| 0 <= a < cand.len() && 0 <= b < nonc.len() ==> (#[trigger] cand[a]).sum >= (#[trigger] nonc[b]).sum
    &&& nonc.len() > 0 ==> cand.len() >= TOP
    &&& out.len() == if cand.len() < TOP { cand.len() as int } else { TOP as int }
    &&& forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == rrow(sv, ps, cand[i])
}

/// No flags: key `k`'s count fits int8 and its mass `i128`.
proof fn lemma_cap_key(sv: StoresView, db: Database, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>, k: Row)
    requires base(sv, db), layouts(sv), merged_ok(sv, ps, name_count(sv), pall, gg), no_flags(gg),
    ensures gcount(qspec(ps), joined(db), k) <= int8_max(), gabs(qspec(ps), joined(db), k, 0) <= i128::MAX,
{
    if exists|x: int| 0 <= x < gg.len() && kd(sv, ps, #[trigger] gg[x]) == k {
        let x = choose|x: int| 0 <= x < gg.len() && kd(sv, ps, #[trigger] gg[x]) == k;
        lemma_group_vals(sv, db, ps, pall, gg, x);
        assert(exact_ok(gg[x]));
    } else {
        lemma_no_group(sv, db, ps, pall, gg, k);
    }
}

/// No flags: every key's count fits int8 and its mass `i128`.
proof fn lemma_caps(sv: StoresView, db: Database, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>)
    requires base(sv, db), layouts(sv), merged_ok(sv, ps, name_count(sv), pall, gg), no_flags(gg),
    ensures group_caps(qspec(ps), joined(db)),
{
    let g = qspec(ps);
    let r = joined(db);
    assert forall|k: Row, j: int| #![trigger gcount(g, r, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count implies gcount(g, r, k) <= int8_max() by {
        lemma_cap_key(sv, db, ps, pall, gg, k);
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, r, k, j) <= i128_max() by {
        assert(j == 0);
        lemma_cap_key(sv, db, ps, pall, gg, k);
    }
}

/// A group's row is its key's output row.
proof fn lemma_rrow_out(sv: StoresView, db: Database, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>, x: int)
    requires base(sv, db), layouts(sv), merged_ok(sv, ps, name_count(sv), pall, gg), no_flags(gg), 0 <= x < gg.len(),
    ensures rrow(sv, ps, gg[x]) == out_row(qspec(ps), joined(db), kd(sv, ps, gg[x])),
{
    let g = qspec(ps);
    let r = joined(db);
    let k = kd(sv, ps, gg[x]);
    lemma_group_vals(sv, db, ps, pall, gg, x);
    assert(exact_ok(gg[x]));
    let fr = full_row(g, r, k);
    assert(agg_outs(g, r, k) =~= seq![Val::Num { coeff: gg[x].sum as int, scale: 4 }, Val::Int(gg[x].cnt as int)]);
    assert(fr.len() == 6);
    lemma_select_identity(fr, g.outs);
    assert(fr =~= rrow(sv, ps, gg[x]));
}

/// Rows of larger or equal sums sort first.
proof fn lemma_cmp_rows(sv: StoresView, ps: Seq<Literal>, a: Partial, b: Partial)
    requires a.sum >= b.sum,
    ensures keys_cmp(order_keys(), rrow(sv, ps, a), rrow(sv, ps, b)) <= 0,
{
    let ks = order_keys();
    let (ra, rb) = (rrow(sv, ps, a), rrow(sv, ps, b));
    assert(ra[4] == Val::Num { coeff: a.sum as int, scale: 4 });
    assert(rb[4] == Val::Num { coeff: b.sum as int, scale: 4 });
    assert(pow10(0) == 1);
    assert(((4nat - 4nat) as nat) == 0nat);
    assert(key_cmp(ks[0], ra, rb) <= 0);
    assert(ks.drop_first().len() == 0);
    reveal_with_fuel(keys_cmp, 2);
}

proof fn lemma_rows_keys_ok(sv: StoresView, ps: Seq<Literal>, s: Seq<Partial>)
    ensures all_keys_ok(order_keys(), seq![1int], s.map_values(|x: Partial| rrow(sv, ps, x))),
{
    let rs = s.map_values(|x: Partial| rrow(sv, ps, x));
    assert forall|i: int| 0 <= i < rs.len() implies keys_ok(order_keys(), seq![1int], #[trigger] rs[i]) by {
        assert(rs[i] == rrow(sv, ps, s[i]));
        assert(rs[i][4] == Val::Num { coeff: s[i].sum as int, scale: 4 });
        assert(key_ok(order_keys()[0], 1, rs[i]));
    }
}

/// Every candidate and other group is a group.
pub proof fn lemma_in_groups(gg: Seq<Partial>, cand: Seq<Partial>, nonc: Seq<Partial>, v: Partial)
    requires (cand + nonc).to_multiset() == gg.to_multiset(), cand.contains(v) || nonc.contains(v),
    ensures exists|x: int| 0 <= x < gg.len() && gg[x] == v,
{
    broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};
    let c = cand + nonc;
    if cand.contains(v) {
        let i = choose|i: int| 0 <= i < cand.len() && cand[i] == v;
        assert(c[i] == v);
    } else {
        let i = choose|i: int| 0 <= i < nonc.len() && nonc[i] == v;
        assert(c[cand.len() + i] == v);
    }
    assert(c.contains(v));
    assert(gg.to_multiset().count(v) > 0);
    assert(gg.contains(v));
}

/// The multiset of the rows of all groups is the result rows'.
proof fn lemma_rows_mset(sv: StoresView, db: Database, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>)
    requires base(sv, db), layouts(sv), merged_ok(sv, ps, name_count(sv), pall, gg), no_flags(gg),
    ensures gg.map_values(|x: Partial| rrow(sv, ps, x)).to_multiset() == result_rows(qspec(ps), joined(db)).to_multiset(),
{
    let g = qspec(ps);
    let r = joined(db);
    let kk = gg.map_values(|x: Partial| kd(sv, ps, x));
    assert forall|a: int, b: int| 0 <= a < kk.len() && 0 <= b < kk.len() && a != b implies kk[a] != kk[b] by {
        if kk[a] == kk[b] {
            lemma_kd_inj(sv, ps, gg[a], gg[b]);
            if a < b {
                assert(!same_code(gg[a], gg[b]));
            } else {
                assert(!same_code(gg[b], gg[a]));
            }
        }
    }
    assert forall|k: Row| #[trigger] kk.contains(k) <==> gcount(g, r, k) > 0 by {
        if kk.contains(k) {
            let x = choose|x: int| 0 <= x < kk.len() && kk[x] == k;
            lemma_group_vals(sv, db, ps, pall, gg, x);
            assert(exact_ok(gg[x]));
        } else {
            assert forall|x: int| 0 <= x < gg.len() implies kd(sv, ps, #[trigger] gg[x]) != k by {
                assert(kk[x] == kd(sv, ps, gg[x]));
            }
            lemma_no_group(sv, db, ps, pall, gg, k);
        }
    }
    lemma_gkeys(g, r);
    lemma_nodup_same_multiset(kk, gkeys(g, r));
    let f = |k: Row| out_row(g, r, k);
    lemma_map_multiset(kk, gkeys(g, r), f);
    assert(result_rows(g, r) =~= gkeys(g, r).map_values(f));
    let gr = gg.map_values(|y: Partial| rrow(sv, ps, y));
    let kr = kk.map_values(f);
    assert forall|x: int| 0 <= x < gg.len() implies #[trigger] gr[x] == kr[x] by {
        lemma_rrow_out(sv, db, ps, pall, gg, x);
    }
    assert(gr =~= kr);
}

/// The rows answer: an allowed output.
proof fn lemma_ok_answer(sv: StoresView, db: Database, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>,
    cand: Seq<Partial>, nonc: Seq<Partial>, out: Seq<Row>)
    requires
        base(sv, db), layouts(sv), tables_ok(db), ps_ok(ps), merged_ok(sv, ps, name_count(sv), pall, gg), no_flags(gg),
        lists_ok(sv, ps, gg, cand, nonc, out),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let g = qspec(ps);
    let r = joined(db);
    let ks = order_keys();
    let rr = |x: Partial| rrow(sv, ps, x);
    lemma_caps(sv, db, ps, pall, gg);
    lemma_denote_body(db, ps);
    lemma_query_shape(ps);
    let cr = cand.map_values(rr);
    let nr = nonc.map_values(rr);
    lemma_rows_keys_ok(sv, ps, nonc);
    lemma_sort_rows(ks, seq![1int], nr);
    let sr = sort_rows(ks, nr);
    let p = cr + sr;
    // the same rows as the result
    lemma_rows_mset(sv, db, ps, pall, gg);
    lemma_map_multiset(cand + nonc, gg, rr);
    assert((cand + nonc).map_values(rr) =~= cr + nr);
    vstd::seq_lib::lemma_multiset_commutative(cr, nr);
    vstd::seq_lib::lemma_multiset_commutative(cr, sr);
    assert(p.to_multiset() == result_rows(g, r).to_multiset());
    // sorted
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(ks, #[trigger] p[i], #[trigger] p[j]) <= 0 by {
        if j < cr.len() {
            lemma_cmp_rows(sv, ps, cand[i], cand[j]);
        } else if i >= cr.len() {
            assert(p[i] == sr[i - cr.len()] && p[j] == sr[j - cr.len()]);
        } else {
            let v = sr[j - cr.len()];
            assert(p[j] == v);
            assert(sr.contains(v));
            broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};
            assert(sr.to_multiset().count(v) > 0);
            assert(nr.contains(v));
            let m = choose|m: int| 0 <= m < nr.len() && nr[m] == v;
            lemma_cmp_rows(sv, ps, cand[i], nonc[m]);
        }
    }
    // the first TOP rows
    assert(out =~= slice_rows(p, 0, Some(200nat)));
    lemma_result_ok_from(g, ks, 0, Some(200nat), r, p);
    lemma_ordered_link(db, query_spec_at(ps), g, r, out);
}

/// The rows answer meets the claim.
pub proof fn lemma_answer_rows(sv: StoresView, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>,
    cand: Seq<Partial>, nonc: Seq<Partial>, rows: Seq<Vec<EVal>>)
    requires
        ps_ok(ps), merged_ok(sv, ps, name_count(sv), pall, gg), no_flags(gg),
        lists_ok(sv, ps, gg, cand, nonc, view_rows(rows)),
    ensures forall|db: Database| #[trigger] bound_db(sv, db)
        ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(rows))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(rows))) by {
        lemma_bound_base(sv, db);
        lemma_tables_ok(db);
        lemma_ok_answer(sv, db, ps, pall, gg, cand, nonc, view_rows(rows));
    }
}

/// A group's count beyond int8: the SQL error 22003.
pub proof fn lemma_answer_count_err(sv: StoresView, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>, x: int)
    requires ps_ok(ps), merged_ok(sv, ps, name_count(sv), pall, gg), 0 <= x < gg.len(), gg[x].cnt == CNT_OVER,
    ensures forall|db: Database| #[trigger] bound_db(sv, db)
        ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)) by {
        lemma_bound_base(sv, db);
        lemma_tables_ok(db);
        lemma_group_vals(sv, db, ps, pall, gg, x);
        assert(exact_ok(gg[x]));
        lemma_body_count_err(db, ps, kd(sv, ps, gg[x]));
    }
}

/// No count beyond int8 and a group's mass beyond `i128`: outside the capacity domain.
pub proof fn lemma_answer_capacity(sv: StoresView, ps: Seq<Literal>, pall: Seq<Filing>, gg: Seq<Partial>, x: int)
    requires
        ps_ok(ps), merged_ok(sv, ps, name_count(sv), pall, gg), 0 <= x < gg.len(), gg[x].mass == MASS_OVER,
        forall|y: int| 0 <= y < gg.len() ==> (#[trigger] gg[y]).cnt != CNT_OVER,
    ensures forall|db: Database| #[trigger] bound_db(sv, db)
        ==> !crate::gendb_entry::capacity_domain(db, query_spec_at(ps)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies !crate::gendb_entry::capacity_domain(db, query_spec_at(ps)) by {
        lemma_bound_base(sv, db);
        lemma_tables_ok(db);
        assert forall|k: Row| #[trigger] gcount(qspec(ps), joined(db), k) <= int8_max() by {
            if exists|y: int| 0 <= y < gg.len() && kd(sv, ps, #[trigger] gg[y]) == k {
                let y = choose|y: int| 0 <= y < gg.len() && kd(sv, ps, #[trigger] gg[y]) == k;
                lemma_group_vals(sv, db, ps, pall, gg, y);
                assert(exact_ok(gg[y]));
            } else {
                lemma_no_group(sv, db, ps, pall, gg, k);
            }
        }
        lemma_group_vals(sv, db, ps, pall, gg, x);
        assert(exact_ok(gg[x]));
        lemma_body_capacity(db, ps, kd(sv, ps, gg[x]));
    }
}

/// No triple qualifies: the empty answer.
pub proof fn lemma_answer_empty(sv: StoresView, ps: Seq<Literal>)
    requires layouts(sv), ps_ok(ps), forall|j: int| 0 <= j < s_count(sv) ==> #[trigger] zero_j(sv, ps, j),
    ensures forall|db: Database| #[trigger] bound_db(sv, db)
        ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(Seq::<Vec<EVal>>::empty()))),
{
    let e: Seq<Partial> = Seq::empty();
    let ef: Seq<Filing> = Seq::empty();
    assert(merged_ok(sv, ps, name_count(sv), ef, e));
    assert(view_rows(Seq::<Vec<EVal>>::empty()) =~= Seq::<Row>::empty());
    assert(e + e =~= e);
    lemma_answer_rows(sv, ps, ef, e, e, e, Seq::<Vec<EVal>>::empty());
}

} // verus!
