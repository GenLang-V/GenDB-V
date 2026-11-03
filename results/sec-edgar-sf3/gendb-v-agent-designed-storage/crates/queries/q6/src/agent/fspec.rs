//! Filing-level specification. A filing (`Filing`, `filing_ok`) is a `sub` row `j` with `fy = $3`, the `num` run
//! of uom `$1` and adsh `adsh(j)` (stored rows `[rs, re)`), and the `pre` adsh code of `adsh(j)` (sub-runs
//! `[sa, sb)`). Its contribution to group `k` (`fsum`) is, over the selected sub-runs (stmt `$2`) and their rows `l`,
//! the weight of the `num` rows of the run whose pair code is the num pair of row `l`'s pre pair (`pair_of`), when
//! the row's key (`kd_row`) is `k`. `lemma_filing_cells`: that is the filing's triple sum over the cells;
//! `zero_j`: a `sub` row that is no filing has no qualifying triple.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::gendb_entry::stores::StoresView;
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::sub::interface as si;
use crate::stores::num::interface::common::runs as nruns;
use crate::stores::pre::interface::common::runs as pruns;
use crate::stores::num::interface::common::runs::pair_lt;
use crate::stores::num::interface::common::text::{text_entry, u64_part, u8_part, lemma_dict_codes};
use crate::stores::pre::interface::common::cols::{u64s as pu64s, list_entry};
use crate::agent::meaning::*;
use crate::agent::views::*;
use crate::agent::reorg::*;
use crate::agent::common::sums::*;
use crate::agent::filings::Filing;

verus! {

/// The layout facts of the three storages (part of `represents`).
pub open spec fn layouts(sv: StoresView) -> bool {
    &&& ni::num_layout_ok(sv.num)
    &&& pi::pre_layout_ok(sv.pre)
    &&& si::sub_layout_ok(sv.sub)
}

// ------------------------------------------------------------------------------------------------ pre sub-runs

pub open spec fn p_tv(sv: StoresView, l: int) -> u64 {
    pu64s(sv.pre, pi::P_TV)[l]
}

/// Sub-run `s` has stmt `$2`.
pub open spec fn sel_sub(sv: StoresView, ps: Seq<Literal>, s: int) -> bool {
    sub_stmt(sv, s) == Val::Text(p_stmt(ps))
}

pub open spec fn sel_len(sv: StoresView, ps: Seq<Literal>, s: int) -> int {
    if sel_sub(sv, ps, s) { p_start(sv)[s + 1] - p_start(sv)[s] } else { 0 }
}

/// Rows of the selected sub-runs among `[sa, sb)`.
pub open spec fn sel_rows(sv: StoresView, ps: Seq<Literal>, sa: int, sb: int) -> int {
    isum(sa, sb, |s: int| sel_len(sv, ps, s))
}

// ------------------------------------------------------------------------------------------------ pairs

pub open spec fn pre_pair_tag(sv: StoresView, c: int) -> Seq<u8> {
    list_entry(sv.pre, pi::P_TAG_OFF, pu64s(sv.pre, pi::P_PAIR_TAG)[c] as int)
}

pub open spec fn pre_pair_ver(sv: StoresView, c: int) -> Seq<u8> {
    list_entry(sv.pre, pi::P_VERSION_OFF, pu64s(sv.pre, pi::P_PAIR_VERSION)[c] as int)
}

pub open spec fn num_pair_tag(sv: StoresView, d: int) -> Seq<u8> {
    ni::dict_entry(sv.num, ni::P_TAG_OFF, ni::u64s(sv.num, ni::P_PAIR_TAG)[d] as int)
}

pub open spec fn num_pair_ver(sv: StoresView, d: int) -> Seq<u8> {
    ni::dict_entry(sv.num, ni::P_VERSION_OFF, ni::u64s(sv.num, ni::P_PAIR_VERSION)[d] as int)
}

/// Num pair `d` has the tag and version of pre pair `c`.
pub open spec fn pair_match(sv: StoresView, c: int, d: int) -> bool {
    &&& 0 <= d < ni::pair_count(sv.num)
    &&& num_pair_tag(sv, d) == pre_pair_tag(sv, c)
    &&& num_pair_ver(sv, d) == pre_pair_ver(sv, c)
}

/// The num pair of pre pair `c`, or -1.
pub open spec fn pair_of(sv: StoresView, c: int) -> int {
    if exists|d: int| pair_match(sv, c, d) { choose|d: int| pair_match(sv, c, d) } else { -1 }
}

/// At most one num pair matches.
pub proof fn lemma_pair_unique(sv: StoresView, c: int, d1: int, d2: int)
    requires layouts(sv), pair_match(sv, c, d1), pair_match(sv, c, d2),
    ensures d1 == d2,
{
    let np = sv.num;
    let pt = ni::u64s(np, ni::P_PAIR_TAG);
    let pv = ni::u64s(np, ni::P_PAIR_VERSION);
    let toff = u64_part(np[ni::P_TAG_OFF as int]);
    let tbytes = u8_part(np[ni::P_TAG_OFF + 1]);
    let voff = u64_part(np[ni::P_VERSION_OFF as int]);
    let vbytes = u8_part(np[ni::P_VERSION_OFF + 1]);
    assert(pt[d1] < ni::tag_count(np) && pt[d2] < ni::tag_count(np));
    assert(pv[d1] < ni::version_count(np) && pv[d2] < ni::version_count(np));
    lemma_dict_codes(toff, tbytes, ni::tag_count(np), pt[d1] as int, pt[d2] as int);
    lemma_dict_codes(voff, vbytes, ni::version_count(np), pv[d1] as int, pv[d2] as int);
    if d1 < d2 {
        assert(pair_lt(pt[d1], pv[d1], pt[d2], pv[d2]));
    } else if d2 < d1 {
        assert(pair_lt(pt[d2], pv[d2], pt[d1], pv[d1]));
    }
}

pub proof fn lemma_pair_of(sv: StoresView, c: int, d: int)
    requires layouts(sv), pair_match(sv, c, d),
    ensures pair_of(sv, c) == d,
{
    let e = choose|e: int| pair_match(sv, c, e);
    lemma_pair_unique(sv, c, d, e);
}

pub proof fn lemma_pair_none(sv: StoresView, c: int)
    requires forall|d: int| !pair_match(sv, c, d),
    ensures pair_of(sv, c) == -1,
{
}

/// Stored `num` row `i` and stored `pre` row `l` have the same tag and version exactly when the row's pair code is
/// the num pair of the pre row's pair.
pub proof fn lemma_row_pair(sv: StoresView, i: int, l: int)
    requires layouts(sv), 0 <= i < n_count(sv), 0 <= l < p_count(sv),
    ensures (n_tag(sv, i) == p_tag(sv, l) && n_ver(sv, i) == p_ver(sv, l)) == (n_tv(sv, i) as int == pair_of(sv, p_tv(sv, l) as int)),
{
    let c = p_tv(sv, l) as int;
    let d = n_tv(sv, i) as int;
    assert(n_tv(sv, i) < ni::pair_count(sv.num));
    if n_tag(sv, i) == p_tag(sv, l) && n_ver(sv, i) == p_ver(sv, l) {
        assert(pair_match(sv, c, d));
        lemma_pair_of(sv, c, d);
    }
    if d == pair_of(sv, c) {
        if exists|e: int| pair_match(sv, c, e) {
            assert(pair_match(sv, c, d));
        }
    }
}

// ------------------------------------------------------------------------------------------------ filings

/// `f` is the filing of `sub` row `f.j`, with its run `f.gr` and its pre adsh code `f.gb`.
pub open spec fn filing_ok(sv: StoresView, ps: Seq<Literal>, f: Filing) -> bool {
    let j = f.j as int;
    let r = f.gr@;
    let b = f.gb@;
    &&& 0 <= j < s_count(sv)
    &&& s_fy(sv, j) == Val::Int(p_fy(ps))
    &&& f.nm == u64_part(sv.sub[si::P_NAME_CODES as int])[j]
    &&& 0 <= r < ni::run_count(sv.num)
    &&& f.rs == n_start(sv)[r] && f.re == n_start(sv)[r + 1]
    &&& ni::run_uom_of(sv.num, r) == p_uom(ps)
    &&& ni::run_adsh_of(sv.num, r) == s_adsh(sv, j)
    &&& 0 <= b < pi::adsh_count(sv.pre)
    &&& f.sa == pu64s(sv.pre, pi::P_ADSH_SUBS)[b] && f.sb == pu64s(sv.pre, pi::P_ADSH_SUBS)[b + 1]
    &&& list_entry(sv.pre, pi::P_ADSH_OFF, b) == s_adsh(sv, j)
    &&& f.rows == sel_rows(sv, ps, f.sa as int, f.sb as int)
}

/// `sub` row `j` has no qualifying triple.
pub open spec fn zero_j(sv: StoresView, ps: Seq<Literal>, j: int) -> bool {
    forall|i: int, l: int| 0 <= i < n_count(sv) && 0 <= l < p_count(sv) ==> !#[trigger] pq(sv, ps, i, j, l)
}

/// Distinct `sub` rows have distinct adsh (the declared primary key of `sub`).
pub open spec fn adsh_unique(sv: StoresView) -> bool {
    forall|j1: int, j2: int| 0 <= j1 < s_count(sv) && 0 <= j2 < s_count(sv) && #[trigger] s_adsh(sv, j1) == #[trigger] s_adsh(sv, j2)
        ==> j1 == j2
}

/// The key of the triples of `sub` row `j` and stored `pre` row `l`.
pub open spec fn kd_row(sv: StoresView, ps: Seq<Literal>, j: int, l: int) -> Row {
    seq![s_name(sv, j), Val::Text(p_stmt(ps)), Val::Text(p_tag(sv, l)), p_plabel(sv, l)]
}

/// Weight of the run's rows matching pre row `l`.
pub open spec fn row_w(sv: StoresView, f: Filing, l: int, wsel: int) -> int {
    isum(f.rs as int, f.re as int, |i: int| if n_tv(sv, i) as int == pair_of(sv, p_tv(sv, l) as int) { wt(sv, wsel, i) } else { 0 })
}

pub open spec fn frow(sv: StoresView, ps: Seq<Literal>, f: Filing, k: Row, wsel: int, l: int) -> int {
    if kd_row(sv, ps, f.j as int, l) == k { row_w(sv, f, l, wsel) } else { 0 }
}

pub open spec fn fsub(sv: StoresView, ps: Seq<Literal>, f: Filing, k: Row, wsel: int, s: int) -> int {
    if sel_sub(sv, ps, s) { isum(p_start(sv)[s] as int, p_start(sv)[s + 1] as int, |l: int| frow(sv, ps, f, k, wsel, l)) } else { 0 }
}

/// The contribution of filing `f` to group `k`.
pub open spec fn fsum(sv: StoresView, ps: Seq<Literal>, f: Filing, k: Row, wsel: int) -> int {
    isum(f.sa as int, f.sb as int, |s: int| fsub(sv, ps, f, k, wsel, s))
}

/// A `sub` row without qualifying triples has no weight.
pub proof fn lemma_zero_cells(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int, j: int)
    requires zero_j(sv, ps, j),
    ensures cell_l(sv, ps, k, wsel, j) == 0,
{
    assert forall|l: int| 0 <= l < p_count(sv) implies #[trigger] cell_i(sv, ps, k, wsel, j, l) == 0 by {
        assert forall|i: int| 0 <= i < n_count(sv) implies #[trigger] cell(sv, ps, k, wsel, i, j, l) == 0 by {
            assert(!pq(sv, ps, i, j, l));
        }
        lemma_isum_zero(0, n_count(sv), |i: int| cell(sv, ps, k, wsel, i, j, l));
    }
    lemma_isum_zero(0, p_count(sv), |l: int| cell_i(sv, ps, k, wsel, j, l));
}

/// Codes of run `r` are dictionary codes.
pub proof fn lemma_run_codes(np: Seq<crate::gendb_entry::layout::PartView>, r: int)
    requires ni::num_layout_ok(np), 0 <= r < ni::run_count(np),
    ensures
        ni::u64s(np, ni::P_RUN_UOM)[r] < ni::uom_count(np),
        ni::u64s(np, ni::P_RUN_ADSH)[r] < ni::adsh_count(np),
{
    let nr = ni::run_count(np);
    let run_uom = ni::u64s(np, ni::P_RUN_UOM);
    let run_adsh = ni::u64s(np, ni::P_RUN_ADSH);
    assert(forall|r: int| 0 <= r < nr ==> #[trigger] run_uom[r] < ni::uom_count(np) && run_adsh[r] < ni::adsh_count(np));
}

/// The rows of a run's neighbours: a stored `num` row outside run `r` has another (uom, adsh).
pub proof fn lemma_outside_run(sv: StoresView, r: int, i: int)
    requires layouts(sv), 0 <= r < ni::run_count(sv.num), 0 <= i < n_count(sv),
        !(n_start(sv)[r] <= i < n_start(sv)[r + 1]),
    ensures !(n_uom(sv, i) == ni::run_uom_of(sv.num, r) && n_adsh(sv, i) == ni::run_adsh_of(sv.num, r)),
{
    let np = sv.num;
    let nr = ni::run_count(np);
    nruns::lemma_run_of(n_start(sv), nr, n_count(sv), i);
    let r2 = n_run(sv, i);
    assert(r2 != r);
    let ru = ni::u64s(np, ni::P_RUN_UOM);
    let ra = ni::u64s(np, ni::P_RUN_ADSH);
    lemma_run_codes(np, r);
    lemma_run_codes(np, r2);
    lemma_dict_codes(u64_part(np[ni::P_UOM_OFF as int]), u8_part(np[ni::P_UOM_OFF + 1]), ni::uom_count(np), ru[r] as int, ru[r2] as int);
    lemma_dict_codes(u64_part(np[ni::P_ADSH_OFF as int]), u8_part(np[ni::P_ADSH_OFF + 1]), ni::adsh_count(np), ra[r] as int, ra[r2] as int);
    if r < r2 {
        assert(pair_lt(ru[r], ra[r], ru[r2], ra[r2]));
    } else {
        assert(pair_lt(ru[r2], ra[r2], ru[r], ra[r]));
    }
}

/// A stored `pre` row outside the sub-runs of adsh code `b` has another adsh.
pub proof fn lemma_outside_adsh(sv: StoresView, b: int, l: int)
    requires layouts(sv), 0 <= b < pi::adsh_count(sv.pre), 0 <= l < p_count(sv),
        !(p_start(sv)[pu64s(sv.pre, pi::P_ADSH_SUBS)[b] as int] <= l < p_start(sv)[pu64s(sv.pre, pi::P_ADSH_SUBS)[b + 1] as int]),
    ensures p_adsh(sv, l) != list_entry(sv.pre, pi::P_ADSH_OFF, b),
{
    let pp = sv.pre;
    let ns = pi::sub_count(pp);
    let st = p_start(sv);
    let g = pu64s(pp, pi::P_ADSH_SUBS);
    pruns::lemma_run_of(st, ns, p_count(sv), l);
    let s = p_sub(sv, l);
    pi::lemma_adsh_subs(pp, b);
    let sa = pu64s(pp, pi::P_SUB_ADSH);
    if sa[s] == b {
        assert(g[b] <= s < g[b + 1]);
        assert(st[g[b] as int] <= st[s]) by {
            if (g[b] as int) < s { assert(st[g[b] as int] < st[s]); }
        }
        assert(st[s + 1] <= st[g[b + 1] as int]) by {
            if s + 1 < g[b + 1] { assert(st[s + 1] < st[g[b + 1] as int]); }
        }
    }
    assert(sa[s] < pi::adsh_count(pp));
    crate::stores::pre::interface::common::text::lemma_dict_codes(
        crate::stores::pre::interface::common::text::u64_part(pp[pi::P_ADSH_OFF as int]),
        crate::stores::pre::interface::common::text::u8_part(pp[pi::P_ADSH_OFF + 1]),
        pi::adsh_count(pp), sa[s] as int, b);
}


/// The run of a filing lies inside the stored `num` rows.
pub proof fn lemma_run_bounds(sv: StoresView, r: int)
    requires layouts(sv), 0 <= r < ni::run_count(sv.num),
    ensures 0 <= n_start(sv)[r] < n_start(sv)[r + 1] <= n_count(sv),
{
    let st = n_start(sv);
    let nr = ni::run_count(sv.num);
    assert(nruns::runs_partition_ok(st, nr, n_count(sv)));
    assert(st[0] <= st[r]) by { if r > 0 { assert(st[0] < st[r]); } }
    assert(st[r] < st[r + 1]);
    assert(st[r + 1] <= st[nr]) by { if r + 1 < nr { assert(st[r + 1] < st[nr]); } }
}

/// The sub-runs of a pre adsh code, and their rows.
pub proof fn lemma_subs_bounds(sv: StoresView, b: int)
    requires layouts(sv), 0 <= b < pi::adsh_count(sv.pre),
    ensures ({
        let g = pu64s(sv.pre, pi::P_ADSH_SUBS);
        let st = p_start(sv);
        &&& g[b] <= g[b + 1] <= pi::sub_count(sv.pre)
        &&& 0 <= st[g[b] as int] <= st[g[b + 1] as int] <= p_count(sv)
        &&& forall|s: int, t: int| g[b] <= s <= t <= g[b + 1] ==> #[trigger] st[s] <= #[trigger] st[t]
        &&& forall|s: int| g[b] <= s < g[b + 1] ==> #[trigger] pu64s(sv.pre, pi::P_SUB_ADSH)[s] == b
    }),
{
    let pp = sv.pre;
    let g = pu64s(pp, pi::P_ADSH_SUBS);
    let st = p_start(sv);
    let ns = pi::sub_count(pp);
    pi::lemma_adsh_subs(pp, b);
    assert(pruns::runs_partition_ok(st, ns, p_count(sv)));
    assert forall|s: int, t: int| g[b] <= s <= t <= g[b + 1] implies #[trigger] st[s] <= #[trigger] st[t] by {
        if s < t { assert(st[s] < st[t]); }
    }
    assert(st[0] <= st[g[b] as int]) by { if g[b] > 0 { assert(st[0] < st[g[b] as int]); } }
    assert(st[g[b + 1] as int] <= st[ns]) by { if g[b + 1] < ns { assert(st[g[b + 1] as int] < st[ns]); } }
}

/// One row `l` of a selected sub-run of a filing: its cells are the filing's row term.
pub proof fn lemma_cell_row(sv: StoresView, ps: Seq<Literal>, f: Filing, k: Row, wsel: int, l: int)
    requires
        layouts(sv), filing_ok(sv, ps, f), 0 <= l < p_count(sv),
        p_adsh(sv, l) == s_adsh(sv, f.j as int),
        p_stmt_val(sv, l) == Val::Text(p_stmt(ps)),
    ensures cell_i(sv, ps, k, wsel, f.j as int, l) == frow(sv, ps, f, k, wsel, l),
{
    let j = f.j as int;
    let r = f.gr@;
    let (rs, re) = (f.rs as int, f.re as int);
    let nn = n_count(sv);
    lemma_run_bounds(sv, r);
    let c = p_tv(sv, l) as int;
    let cf = |i: int| cell(sv, ps, k, wsel, i, j, l);
    assert forall|i: int| 0 <= i < nn && !(rs <= i < re) implies #[trigger] cf(i) == 0 by {
        lemma_outside_run(sv, r, i);
    }
    lemma_isum_restrict(0, nn, rs, re, cf);
    let rw = |i: int| if n_tv(sv, i) as int == pair_of(sv, c) { wt(sv, wsel, i) } else { 0 };
    if kd_row(sv, ps, j, l) == k {
        assert forall|i: int| rs <= i < re implies #[trigger] cf(i) == rw(i) by {
            nruns::lemma_run_of(n_start(sv), ni::run_count(sv.num), nn, i);
            lemma_row_pair(sv, i, l);
            if pq(sv, ps, i, j, l) {
                assert(pkey(sv, i, j, l) =~= kd_row(sv, ps, j, l));
            }
        }
        lemma_isum_ext(rs, re, cf, rw);
    } else {
        assert forall|i: int| rs <= i < re implies #[trigger] cf(i) == 0 by {
            nruns::lemma_run_of(n_start(sv), ni::run_count(sv.num), nn, i);
            if pq(sv, ps, i, j, l) {
                assert(pkey(sv, i, j, l) =~= kd_row(sv, ps, j, l));
            }
        }
        lemma_isum_zero(rs, re, cf);
    }
}

/// One sub-run `s` of a filing: its rows' cells are the filing's sub-run term.
proof fn lemma_cell_sub(sv: StoresView, ps: Seq<Literal>, f: Filing, k: Row, wsel: int, s: int)
    requires layouts(sv), filing_ok(sv, ps, f), f.sa <= s < f.sb,
    ensures
        isum(p_start(sv)[s] as int, p_start(sv)[s + 1] as int, |l: int| cell_i(sv, ps, k, wsel, f.j as int, l))
            == fsub(sv, ps, f, k, wsel, s),
{
    let j = f.j as int;
    let b = f.gb@;
    let st = p_start(sv);
    let pp = sv.pre;
    lemma_subs_bounds(sv, b);
    let ci = |l: int| cell_i(sv, ps, k, wsel, j, l);
    assert(st[s] < st[s + 1]) by { assert(pruns::runs_partition_ok(st, pi::sub_count(pp), p_count(sv))); }
    assert forall|l: int| st[s] <= l < st[s + 1] implies p_sub(sv, l) == s && p_adsh(sv, l) == s_adsh(sv, j) by {
        pruns::lemma_run_of(st, pi::sub_count(pp), p_count(sv), l);
        assert(pruns::in_run(st, s, l));
        assert(pu64s(pp, pi::P_SUB_ADSH)[s] == b);
    }
    if sel_sub(sv, ps, s) {
        let fr = |l: int| frow(sv, ps, f, k, wsel, l);
        assert forall|l: int| st[s] <= l < st[s + 1] implies #[trigger] ci(l) == fr(l) by {
            lemma_cell_row(sv, ps, f, k, wsel, l);
        }
        lemma_isum_ext(st[s] as int, st[s + 1] as int, ci, fr);
    } else {
        assert forall|l: int| st[s] <= l < st[s + 1] implies #[trigger] ci(l) == 0 by {
            assert forall|i: int| 0 <= i < n_count(sv) implies #[trigger] cell(sv, ps, k, wsel, i, j, l) == 0 by {}
            lemma_isum_zero(0, n_count(sv), |i: int| cell(sv, ps, k, wsel, i, j, l));
        }
        lemma_isum_zero(st[s] as int, st[s + 1] as int, ci);
    }
}

/// A filing's triple sum is its contribution `fsum`.
pub proof fn lemma_filing_cells(sv: StoresView, ps: Seq<Literal>, f: Filing, k: Row, wsel: int)
    requires layouts(sv), filing_ok(sv, ps, f),
    ensures cell_l(sv, ps, k, wsel, f.j as int) == fsum(sv, ps, f, k, wsel),
{
    let j = f.j as int;
    let b = f.gb@;
    let st = p_start(sv);
    let np = p_count(sv);
    let (sa, sb) = (f.sa as int, f.sb as int);
    lemma_subs_bounds(sv, b);
    let ci = |l: int| cell_i(sv, ps, k, wsel, j, l);
    let (l0, l1) = (st[sa] as int, st[sb] as int);
    assert forall|l: int| 0 <= l < np && !(l0 <= l < l1) implies #[trigger] ci(l) == 0 by {
        lemma_outside_adsh(sv, b, l);
        assert forall|i: int| 0 <= i < n_count(sv) implies #[trigger] cell(sv, ps, k, wsel, i, j, l) == 0 by {}
        lemma_isum_zero(0, n_count(sv), |i: int| cell(sv, ps, k, wsel, i, j, l));
    }
    lemma_isum_restrict(0, np, l0, l1, ci);
    let bnd = |s: int| st[s] as int;
    lemma_isum_runs(sa, sb, bnd, ci);
    let per = |s: int| isum(bnd(s), bnd(s + 1), ci);
    let fs = |s: int| fsub(sv, ps, f, k, wsel, s);
    assert forall|s: int| sa <= s < sb implies #[trigger] per(s) == fs(s) by {
        lemma_cell_sub(sv, ps, f, k, wsel, s);
    }
    lemma_isum_ext(sa, sb, per, fs);
}


/// The rows of the sub-runs of pre adsh code `b`.
pub open spec fn blk(sv: StoresView, b: int) -> int {
    p_start(sv)[pu64s(sv.pre, pi::P_ADSH_SUBS)[b + 1] as int] - p_start(sv)[pu64s(sv.pre, pi::P_ADSH_SUBS)[b] as int]
}

/// A filing's selected rows are at most the rows of its adsh.
pub proof fn lemma_rows_le_blk(sv: StoresView, ps: Seq<Literal>, f: Filing)
    requires layouts(sv), filing_ok(sv, ps, f),
    ensures 0 <= f.rows <= blk(sv, f.gb@),
{
    let b = f.gb@;
    let st = p_start(sv);
    lemma_subs_bounds(sv, b);
    let (sa, sb) = (f.sa as int, f.sb as int);
    let full = |s: int| (st[s + 1] - st[s]) as int;
    assert forall|s: int| sa <= s < sb implies #[trigger] sel_len(sv, ps, s) <= full(s) && sel_len(sv, ps, s) >= 0 by {
        assert(pruns::runs_partition_ok(st, pi::sub_count(sv.pre), p_count(sv)));
        assert(st[s] < st[s + 1]);
    }
    lemma_isum_le(sa, sb, |s: int| sel_len(sv, ps, s), full);
    lemma_isum_nonneg(sa, sb, |s: int| sel_len(sv, ps, s));
    lemma_isum_telescope(sa, sb, |s: int| st[s] as int);
    lemma_isum_ext(sa, sb, |i: int| (|s: int| st[s] as int)(i + 1) - (|s: int| st[s] as int)(i), full);
}

/// Filings of distinct `sub` rows have distinct pre adsh codes.
pub proof fn lemma_distinct_b(sv: StoresView, ps: Seq<Literal>, f1: Filing, f2: Filing)
    requires layouts(sv), adsh_unique(sv), filing_ok(sv, ps, f1), filing_ok(sv, ps, f2), f1.j != f2.j,
    ensures f1.gb@ != f2.gb@,
{
    if f1.gb@ == f2.gb@ {
        assert(s_adsh(sv, f1.j as int) == s_adsh(sv, f2.j as int));
    }
}

pub open spec fn rows_of(f: Filing) -> int {
    f.rows as int
}

pub open spec fn gb_of(f: Filing) -> int {
    f.gb@
}

proof fn lemma_tsum_map_gb(fs: Seq<Filing>, h: spec_fn(int) -> int)
    ensures tsum(fs, |f: Filing| h(f.gb@)) == lsum(fs.map_values(|f: Filing| f.gb@), h),
    decreases fs.len(),
{
    if fs.len() > 0 {
        lemma_tsum_map_gb(fs.drop_last(), h);
        assert(fs.map_values(|f: Filing| f.gb@).drop_last() =~= fs.drop_last().map_values(|f: Filing| f.gb@));
    }
}

/// Filings of strictly increasing `sub` rows select at most all `pre` rows.
pub proof fn lemma_rows_le_np(sv: StoresView, ps: Seq<Literal>, fs: Seq<Filing>)
    requires
        layouts(sv), adsh_unique(sv),
        forall|t: int| 0 <= t < fs.len() ==> filing_ok(sv, ps, #[trigger] fs[t]),
        forall|x: int, y: int| 0 <= x < y < fs.len() ==> (#[trigger] fs[x]).j < (#[trigger] fs[y]).j,
    ensures 0 <= tsum(fs, |f: Filing| rows_of(f)) <= p_count(sv),
{
    let pp = sv.pre;
    let na = pi::adsh_count(pp);
    let g = pu64s(pp, pi::P_ADSH_SUBS);
    let st = p_start(sv);
    let bl = |b: int| blk(sv, b);
    assert forall|t: int| 0 <= t < fs.len() implies #[trigger] rows_of(fs[t]) <= bl(fs[t].gb@) && rows_of(fs[t]) >= 0 by {
        lemma_rows_le_blk(sv, ps, fs[t]);
    }
    lemma_tsum_le(fs, |f: Filing| rows_of(f), |f: Filing| bl(f.gb@));
    lemma_tsum_nonneg(fs, |f: Filing| rows_of(f));
    lemma_tsum_map_gb(fs, bl);
    let bs = fs.map_values(|f: Filing| f.gb@);
    assert(bs.no_duplicates()) by {
        assert forall|x: int, y: int| 0 <= x < y < bs.len() implies bs[x] != bs[y] by {
            lemma_distinct_b(sv, ps, fs[x], fs[y]);
        }
    }
    assert forall|b: int| 0 <= b < na implies #[trigger] bl(b) >= 0 by {
        lemma_subs_bounds(sv, b);
    }
    lemma_lsum_le_isum(0, na, bs, bl);
    // telescoping over all adsh codes
    let bnd = |b: int| st[g[b] as int] as int;
    lemma_isum_telescope(0, na, bnd);
    lemma_isum_ext(0, na, |i: int| bnd(i + 1) - bnd(i), bl);
    assert(pi::pre_layout_ok(pp));
    if na > 0 {
        lemma_subs_bounds(sv, na - 1);
        lemma_subs_bounds(sv, 0);
    }
}

pub proof fn lemma_tsum_le<T>(s: Seq<T>, f: spec_fn(T) -> int, g: spec_fn(T) -> int)
    requires forall|k: int| 0 <= k < s.len() ==> #[trigger] f(s[k]) <= g(s[k]),
    ensures tsum(s, f) <= tsum(s, g),
    decreases s.len(),
{
    if s.len() > 0 {
        let init = s.drop_last();
        assert forall|k: int| 0 <= k < init.len() implies #[trigger] f(init[k]) <= g(init[k]) by {
            assert(init[k] == s[k]);
        }
        lemma_tsum_le(init, f, g);
        assert(f(s[s.len() - 1]) <= g(s[s.len() - 1]));
    }
}

pub proof fn lemma_tsum_nonneg<T>(s: Seq<T>, f: spec_fn(T) -> int)
    requires forall|k: int| 0 <= k < s.len() ==> #[trigger] f(s[k]) >= 0,
    ensures tsum(s, f) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        let init = s.drop_last();
        assert forall|k: int| 0 <= k < init.len() implies #[trigger] f(init[k]) >= 0 by {
            assert(init[k] == s[k]);
        }
        lemma_tsum_nonneg(init, f);
        assert(f(s[s.len() - 1]) >= 0);
    }
}


/// One sub-run is a nonempty range of the stored `pre` rows.
pub proof fn lemma_sub_step(sv: StoresView, s: int)
    requires layouts(sv), 0 <= s < pi::sub_count(sv.pre),
    ensures 0 <= p_start(sv)[s] < p_start(sv)[s + 1] <= p_count(sv),
{
    let st = p_start(sv);
    let ns = pi::sub_count(sv.pre);
    assert(pi::pre_layout_ok(sv.pre));
    assert(pruns::runs_partition_ok(st, ns, p_count(sv)));
    assert(st[s] < st[s + 1]);
    assert(st[0] <= st[s]) by { if s > 0 { assert(st[0] < st[s]); } }
    assert(st[s + 1] <= st[ns]) by { if s + 1 < ns { assert(st[s + 1] < st[ns]); } }
}

} // verus!
