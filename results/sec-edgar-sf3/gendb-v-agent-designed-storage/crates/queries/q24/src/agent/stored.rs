//! From stored parts to SQL rows. The scan's inputs (`ScanInput`) are the parts of the `num_tvg` and `pre`
//! storages (`inp_matches`) plus the num-pair map `npm` and the adsh map `amap`, whose meanings are stated over the
//! dictionary strings (`npm_ok`, `map_ok`). `lemma_pos_qual` is the per-row bridge: for a database bound to the parts, stored num row `i` of a run
//! of uom `$1` passes the anti-join (`model::num_spec`) exactly when the scan qualifies it, with the group key and
//! value read from the parts.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::layout::PartView;
use crate::stores::num_tvg::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::pre::interface::common::cols::{u64s as pu64s, list_entry as plist};
use crate::stores::num_tvg::interface::common::text::{text_entry, lemma_dict_codes};
use crate::stores::num_tvg::interface::common::cols::{i32_part, i128_part};
use crate::stores::pre::interface::common::runs::{run_of as prun_of, lemma_run_of as lemma_prun_of};
use crate::stores::num_tvg::interface::common::perm::{lemma_permutation_facts, position_of};
use super::common::chunks::chunks_shape;
use super::common::dictmap::{Dict, map_ok, map_entry_ok};
use super::common::pairmap::{Pairs, pair_entry_ok};
use super::scan::{ScanInput, Entry};
use super::model::*;

verus! {

// ---------------------------------------------------------------------------------------- strings of the parts

/// Tag and version strings of num pair `p`.
pub open spec fn ntag_str(np: Seq<PartView>, p: int) -> Seq<u8> {
    N::dict_entry(np, N::P_TAG_OFF, N::u64s(np, N::P_PAIR_TAG)[p] as int)
}

pub open spec fn nver_str(np: Seq<PartView>, p: int) -> Seq<u8> {
    N::dict_entry(np, N::P_VERSION_OFF, N::u64s(np, N::P_PAIR_VERSION)[p] as int)
}

/// Tag and version strings of pre pair `q`.
pub open spec fn ptag_str(pp: Seq<PartView>, q: int) -> Seq<u8> {
    plist(pp, P::P_TAG_OFF, pu64s(pp, P::P_PAIR_TAG)[q] as int)
}

pub open spec fn pver_str(pp: Seq<PartView>, q: int) -> Seq<u8> {
    plist(pp, P::P_VERSION_OFF, pu64s(pp, P::P_PAIR_VERSION)[q] as int)
}

/// The group key of num pair `p`: (tag, version).
pub open spec fn keyp(np: Seq<PartView>, p: int) -> Row {
    seq![Val::Text(ntag_str(np, p)), Val::Text(nver_str(np, p))]
}

/// `npm` maps every num pair to the pre pair with the same strings (+ 1), or 0 when there is none.
pub open spec fn npm_ok(np: Seq<PartView>, pp: Seq<PartView>, npm: Seq<u64>) -> bool {
    &&& npm.len() == N::pair_count(np)
    &&& forall|p: int| 0 <= p < npm.len() ==> {
        &&& #[trigger] npm[p] != 0 ==> npm[p] - 1 < P::pair_count(pp)
            && ptag_str(pp, npm[p] - 1) == ntag_str(np, p) && pver_str(pp, npm[p] - 1) == nver_str(np, p)
        &&& npm[p] == 0 ==> forall|q: int| 0 <= q < P::pair_count(pp) ==>
            !(#[trigger] ptag_str(pp, q) == ntag_str(np, p) && pver_str(pp, q) == nver_str(np, p))
    }
}

// --------------------------------------------------------------------------------------- dictionaries of the parts

/// `d` holds the num dictionary in parts `po`, `po + 1`.
pub open spec fn ndict_is(d: Dict, np: Seq<PartView>, po: usize) -> bool {
    &&& d.off@ == N::u64s(np, po)
    &&& d.bytes@ == crate::stores::num_tvg::interface::common::text::u8_part(np[po + 1])
    &&& d.count == N::common::cols::text_count(np, po as int)
}

/// `d` holds the pre dictionary in parts `po`, `po + 1`.
pub open spec fn pdict_is(d: Dict, pp: Seq<PartView>, po: usize) -> bool {
    &&& d.off@ == pu64s(pp, po)
    &&& d.bytes@ == crate::stores::pre::interface::common::text::u8_part(pp[po + 1])
    &&& d.count == P::common::cols::text_count(pp, po as int)
}

/// A num dictionary value through `Dict`.
pub proof fn lemma_ndict_at(d: Dict, np: Seq<PartView>, po: usize, k: int)
    requires ndict_is(d, np, po),
    ensures d.at(k) == N::dict_entry(np, po, k),
{
}

/// A pre dictionary value through `Dict`.
pub proof fn lemma_pdict_at(d: Dict, pp: Seq<PartView>, po: usize, k: int)
    requires pdict_is(d, pp, po),
    ensures d.at(k) == plist(pp, po, k),
{
    assert(d.at(k) == text_entry(d.off@, d.bytes@, k));
    assert(plist(pp, po, k) == crate::stores::pre::interface::common::text::text_entry(
        crate::stores::pre::interface::common::text::u64_part(pp[po as int]),
        crate::stores::pre::interface::common::text::u8_part(pp[po + 1]), k));
}

/// The dictionaries are sorted (`Dict::wf`) by the layouts.
pub proof fn lemma_ndict_wf(d: Dict, np: Seq<PartView>, po: usize)
    requires ndict_is(d, np, po), N::dict_ok(np, po), d.count < usize::MAX,
    ensures d.wf(),
{
}

pub proof fn lemma_pdict_wf(d: Dict, pp: Seq<PartView>, po: usize)
    requires pdict_is(d, pp, po), P::common::cols::sorted_list_ok(pp, po), d.count < usize::MAX,
    ensures d.wf(),
{
    assert forall|a: int, b: int| 0 <= a < b < d.count
        implies crate::spec::text::lex_cmp(#[trigger] text_entry(d.off@, d.bytes@, a), #[trigger] text_entry(d.off@, d.bytes@, b)) < 0 by {
        lemma_pdict_at(d, pp, po, a);
        lemma_pdict_at(d, pp, po, b);
    }
}

/// Distinct num pairs have distinct strings.
pub proof fn lemma_npair_inj(np: Seq<PartView>, p1: int, p2: int)
    requires
        N::num_layout_ok(np), 0 <= p1 < N::pair_count(np), 0 <= p2 < N::pair_count(np),
        ntag_str(np, p1) == ntag_str(np, p2), nver_str(np, p1) == nver_str(np, p2),
    ensures p1 == p2,
{
    let pt = N::u64s(np, N::P_PAIR_TAG);
    let pv = N::u64s(np, N::P_PAIR_VERSION);
    assert(pt[p1] < N::tag_count(np) && pt[p2] < N::tag_count(np));
    assert(pv[p1] < N::version_count(np) && pv[p2] < N::version_count(np));
    lemma_dict_codes(N::u64s(np, N::P_TAG_OFF), crate::stores::num_tvg::interface::common::text::u8_part(np[N::P_TAG_BYTES as int]),
        N::tag_count(np), pt[p1] as int, pt[p2] as int);
    lemma_dict_codes(N::u64s(np, N::P_VERSION_OFF), crate::stores::num_tvg::interface::common::text::u8_part(np[N::P_VERSION_BYTES as int]),
        N::version_count(np), pv[p1] as int, pv[p2] as int);
    if p1 < p2 {
        assert(crate::stores::num_tvg::interface::common::runs::pair_lt(pt[p1], pv[p1], pt[p2], pv[p2]));
    } else if p2 < p1 {
        assert(crate::stores::num_tvg::interface::common::runs::pair_lt(pt[p2], pv[p2], pt[p1], pv[p1]));
    }
}

/// Distinct pre pairs have distinct strings.
pub proof fn lemma_ppair_inj(pp: Seq<PartView>, q1: int, q2: int)
    requires
        P::pre_layout_ok(pp), 0 <= q1 < P::pair_count(pp), 0 <= q2 < P::pair_count(pp),
        ptag_str(pp, q1) == ptag_str(pp, q2), pver_str(pp, q1) == pver_str(pp, q2),
    ensures q1 == q2,
{
    let pt = pu64s(pp, P::P_PAIR_TAG);
    let pv = pu64s(pp, P::P_PAIR_VERSION);
    assert(pt[q1] < P::tag_count(pp) && pt[q2] < P::tag_count(pp));
    assert(pv[q1] < P::version_count(pp) && pv[q2] < P::version_count(pp));
    crate::stores::pre::interface::common::text::lemma_dict_codes(
        crate::stores::pre::interface::common::text::u64_part(pp[P::P_TAG_OFF as int]),
        crate::stores::pre::interface::common::text::u8_part(pp[P::P_TAG_OFF + 1]),
        P::tag_count(pp), pt[q1] as int, pt[q2] as int);
    crate::stores::pre::interface::common::text::lemma_dict_codes(
        crate::stores::pre::interface::common::text::u64_part(pp[P::P_VERSION_OFF as int]),
        crate::stores::pre::interface::common::text::u8_part(pp[P::P_VERSION_OFF + 1]),
        P::version_count(pp), pv[q1] as int, pv[q2] as int);
    if q1 < q2 {
        assert(crate::stores::pre::interface::common::runs::pair_lt(pt[q1], pv[q1], pt[q2], pv[q2]));
    } else if q2 < q1 {
        assert(crate::stores::pre::interface::common::runs::pair_lt(pt[q2], pv[q2], pt[q1], pv[q1]));
    }
}

/// The pair map computed from the tag and version maps (num -> pre) means `npm_ok`.
pub proof fn lemma_npm_ok(np: Seq<PartView>, pp: Seq<PartView>, ntag: Dict, nver: Dict, ptag: Dict, pver: Dict,
    tm: Seq<u64>, vm: Seq<u64>, src: Pairs, dst: Pairs, npm: Seq<u64>)
    requires
        N::num_layout_ok(np), P::pre_layout_ok(pp),
        ndict_is(ntag, np, N::P_TAG_OFF), ndict_is(nver, np, N::P_VERSION_OFF),
        pdict_is(ptag, pp, P::P_TAG_OFF), pdict_is(pver, pp, P::P_VERSION_OFF),
        ptag.wf(), pver.wf(),
        map_ok(ntag, ptag, tm), map_ok(nver, pver, vm),
        src.first@ == N::u64s(np, N::P_PAIR_TAG), src.second@ == N::u64s(np, N::P_PAIR_VERSION),
        src.count == N::pair_count(np),
        dst.first@ == pu64s(pp, P::P_PAIR_TAG), dst.second@ == pu64s(pp, P::P_PAIR_VERSION),
        dst.count == P::pair_count(pp),
        npm.len() == src.count,
        forall|p: int| 0 <= p < src.count ==> pair_entry_ok(src, dst, tm, vm, p, #[trigger] npm[p]),
    ensures npm_ok(np, pp, npm),
{
    assert forall|p: int| 0 <= p < npm.len() implies {
        &&& #[trigger] npm[p] != 0 ==> npm[p] - 1 < P::pair_count(pp)
            && ptag_str(pp, npm[p] - 1) == ntag_str(np, p) && pver_str(pp, npm[p] - 1) == nver_str(np, p)
        &&& npm[p] == 0 ==> forall|q: int| 0 <= q < P::pair_count(pp) ==>
            !(#[trigger] ptag_str(pp, q) == ntag_str(np, p) && pver_str(pp, q) == nver_str(np, p))
    } by {
        assert(pair_entry_ok(src, dst, tm, vm, p, npm[p]));
        let ct = src.first@[p] as int;
        let cv = src.second@[p] as int;
        assert(ct < N::tag_count(np) && cv < N::version_count(np));
        assert(map_entry_ok(ntag, ptag, ct, tm[ct]));
        assert(map_entry_ok(nver, pver, cv, vm[cv]));
        lemma_ndict_at(ntag, np, N::P_TAG_OFF, ct);
        lemma_ndict_at(nver, np, N::P_VERSION_OFF, cv);
        if npm[p] != 0 {
            let q = npm[p] - 1;
            lemma_pdict_at(ptag, pp, P::P_TAG_OFF, (tm[ct] - 1) as int);
            lemma_pdict_at(pver, pp, P::P_VERSION_OFF, (vm[cv] - 1) as int);
            assert(dst.first@[q] == tm[ct] - 1);
        } else {
            assert forall|q: int| 0 <= q < P::pair_count(pp) implies
                !(#[trigger] ptag_str(pp, q) == ntag_str(np, p) && pver_str(pp, q) == nver_str(np, p)) by {
                if ptag_str(pp, q) == ntag_str(np, p) && pver_str(pp, q) == nver_str(np, p) {
                    let tq = dst.first@[q] as int;
                    let vq = dst.second@[q] as int;
                    assert(tq < P::tag_count(pp) && vq < P::version_count(pp));
                    lemma_pdict_at(ptag, pp, P::P_TAG_OFF, tq);
                    lemma_pdict_at(pver, pp, P::P_VERSION_OFF, vq);
                    assert(tm[ct] != 0);
                    assert(vm[cv] != 0);
                    lemma_pdict_at(ptag, pp, P::P_TAG_OFF, (tm[ct] - 1) as int);
                    lemma_pdict_at(pver, pp, P::P_VERSION_OFF, (vm[cv] - 1) as int);
                    lemma_dict_codes(ptag.off@, ptag.bytes@, ptag.count as int, tq, (tm[ct] - 1) as int);
                    lemma_dict_codes(pver.off@, pver.bytes@, pver.count as int, vq, (vm[cv] - 1) as int);
                    assert(dst.first@[q] + 1 == tm[ct] && dst.second@[q] + 1 == vm[cv]);
                }
            }
        }
    }
}


// ------------------------------------------------------------------------------------------ the scan's inputs

/// The scan inputs are the stored parts, the parameters and meaningful adsh and pair maps.
pub open spec fn inp_matches(inp: ScanInput, np: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>) -> bool {
    &&& inp.run_start@ == N::u64s(np, N::P_RUN_START)
    &&& inp.run_adsh@ == N::u64s(np, N::P_RUN_ADSH)
    &&& inp.run_dmin@ == i32_part(np[N::P_RUN_DDATE_MIN as int])
    &&& inp.run_dmax@ == i32_part(np[N::P_RUN_DDATE_MAX as int])
    &&& inp.tv@ == N::u64s(np, N::P_TV)
    &&& inp.ddate@ == i32_part(np[N::P_DDATE as int])
    &&& inp.value@ == i128_part(np[N::P_VALUE as int])
    &&& ndict_is(inp.nadsh, np, N::P_ADSH_OFF)
    &&& pdict_is(inp.padsh, pp, P::P_ADSH_OFF)
    &&& inp.adsh_subs@ == pu64s(pp, P::P_ADSH_SUBS)
    &&& inp.sub_start@ == pu64s(pp, P::P_SUB_START)
    &&& inp.ptv@ == pu64s(pp, P::P_TV)
    &&& inp.n == N::row_count(np) && inp.runs == N::run_count(np)
    &&& inp.pn == P::row_count(pp) && inp.subs == P::sub_count(pp)
    &&& inp.npairs == N::pair_count(np) && inp.ppairs == P::pair_count(pp)
    &&& inp.nadsh_n == inp.nadsh.count
    &&& inp.dlo == dlo(ps) && inp.dhi == dhi(ps)
    &&& map_ok(inp.nadsh, inp.padsh, inp.amap@)
    &&& inp.npm_shape()
    &&& npm_ok(np, pp, inp.npmv())
    &&& inp.has_index == N::has_index(np)
    &&& inp.run_groups@ == N::u64s(np, N::P_RUN_GROUPS)
    &&& inp.group_start@ == N::u32s(np, N::P_GROUP_START)
    &&& inp.group_key@ == N::u32s(np, N::P_GROUP_KEY)
    &&& inp.ngroups == N::group_count(np)
}

/// The num facts of `ScanInput::wf`.
pub open spec fn wf_num(inp: ScanInput) -> bool {
    let start = inp.run_start@;
    let tv = inp.tv@;
    &&& crate::stores::num_tvg::interface::common::runs::runs_partition_ok(start, inp.runs as int, inp.n as int)
    &&& inp.run_adsh@.len() == inp.runs
    &&& forall|r: int| 0 <= r < inp.runs ==> (#[trigger] inp.run_adsh@[r]) < inp.nadsh.count
    &&& crate::stores::num_tvg::interface::common::runs::run_bounds_ok(inp.ddate@, start, inp.run_dmin@, inp.run_dmax@)
    &&& tv.len() == inp.n && inp.ddate@.len() == inp.n && inp.value@.len() == inp.n
    &&& inp.nadsh.wf()
    &&& forall|i: int| 0 <= i < inp.n ==> (#[trigger] tv[i]) < inp.npairs
    &&& inp.npairs < usize::MAX
    &&& inp.has_index ==> inp.index_wf()
}

proof fn lemma_wf_num(inp: ScanInput, np: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>)
    requires N::num_layout_ok(np), inp_matches(inp, np, pp, ps), inp.nadsh.count < usize::MAX, inp.npairs < usize::MAX,
    ensures wf_num(inp),
{
    lemma_ndict_wf(inp.nadsh, np, N::P_ADSH_OFF);
    assert forall|r: int| 0 <= r < inp.runs implies (#[trigger] inp.run_adsh@[r]) < inp.nadsh.count by {
        assert(N::u64s(np, N::P_RUN_UOM)[r] < N::uom_count(np));
    }
    if inp.has_index {
        assert(N::index_ok(np));
        assert(inp.index_wf());
    }
}

/// The pre facts of `ScanInput::wf`.
pub open spec fn wf_pre(inp: ScanInput) -> bool {
    &&& inp.padsh.wf()
    &&& inp.adsh_subs@.len() == inp.padsh.count + 1
    &&& forall|a: int| 0 <= a < inp.padsh.count ==>
        #[trigger] inp.adsh_subs@[a] <= inp.adsh_subs@[a + 1] <= inp.subs
    &&& inp.sub_start@.len() == inp.subs + 1
    &&& forall|a: int, b: int| 0 <= a <= b <= inp.subs ==> #[trigger] inp.sub_start@[a] <= #[trigger] inp.sub_start@[b]
    &&& inp.sub_start@[inp.subs as int] == inp.pn
    &&& inp.ptv@.len() == inp.pn
    &&& forall|j: int| 0 <= j < inp.pn ==> (#[trigger] inp.ptv@[j]) < inp.ppairs
    &&& forall|p: int| 0 <= p < inp.npairs ==> (#[trigger] inp.npmv()[p]) <= inp.ppairs
}

proof fn lemma_wf_pre(inp: ScanInput, np: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>)
    requires P::pre_layout_ok(pp), inp_matches(inp, np, pp, ps), inp.padsh.count < usize::MAX,
    ensures wf_pre(inp),
{
    lemma_pdict_wf(inp.padsh, pp, P::P_ADSH_OFF);
    assert forall|a: int| 0 <= a < inp.padsh.count implies
        #[trigger] inp.adsh_subs@[a] <= inp.adsh_subs@[a + 1] <= inp.subs by {
        P::lemma_adsh_subs(pp, a);
    }
    assert forall|a: int, b: int| 0 <= a <= b <= inp.subs implies #[trigger] inp.sub_start@[a] <= #[trigger] inp.sub_start@[b] by {
        if a < b {
            assert(inp.sub_start@[a] < inp.sub_start@[b]);
        }
    }
    assert forall|j: int| 0 <= j < inp.pn implies (#[trigger] inp.ptv@[j]) < inp.ppairs by {
        assert(pu64s(pp, P::P_TV)[j] < P::pair_count(pp));
    }
    assert forall|p: int| 0 <= p < inp.npairs implies (#[trigger] inp.npmv()[p]) <= inp.ppairs by {
        if inp.npmv()[p] != 0 {
            assert(inp.npmv()[p] - 1 < P::pair_count(pp));
        }
    }
}

/// The layouts give the scan's layout facts.
pub proof fn lemma_inp_wf(inp: ScanInput, np: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>)
    requires
        N::num_layout_ok(np), P::pre_layout_ok(pp), inp_matches(inp, np, pp, ps),
        inp.n < usize::MAX, inp.nadsh.count < usize::MAX, inp.padsh.count < usize::MAX, inp.npairs < usize::MAX,
        inp.ppairs < usize::MAX,
    ensures inp.wf(),
{
    lemma_wf_num(inp, np, pp, ps);
    lemma_wf_pre(inp, np, pp, ps);
}

// --------------------------------------------------------------------------------------- stored rows as rows

/// The values of stored num row `i` of run `r`.
proof fn lemma_num_row(np: Seq<PartView>, rn: Seq<Seq<Row>>, r: int, i: int)
    requires N::represents(np, rn), 0 <= r < N::run_count(np),
        N::u64s(np, N::P_RUN_START)[r] <= i < N::u64s(np, N::P_RUN_START)[r + 1],
    ensures ({
        let x = N::stored_row(np, rn, i);
        let p = N::u64s(np, N::P_TV)[i] as int;
        &&& 0 <= i < N::row_count(np)
        &&& x.len() == 9
        &&& x[0] == Val::Text(N::run_adsh_of(np, r))
        &&& x[1] == Val::Text(ntag_str(np, p))
        &&& x[2] == Val::Text(nver_str(np, p))
        &&& x[3] == Val::Int(i32_part(np[N::P_DDATE as int])[i] as int)
        &&& x[5] == Val::Text(N::run_uom_of(np, r))
        &&& x[7] == Val::Num { coeff: i128_part(np[N::P_VALUE as int])[i] as int, scale: 4 }
    }),
{
    let start = N::u64s(np, N::P_RUN_START);
    assert(start[r + 1] <= start[N::run_count(np)]);
    assert(N::stored_cols_ok(np, N::stored_row(np, rn, i), i));
    assert(N::run_cols_ok(np, N::stored_row(np, rn, i), r));
}

/// The values of stored pre row `j` (in sub-run `run_of(j)`).
proof fn lemma_pre_row(pp: Seq<PartView>, rp: Seq<Seq<Row>>, j: int)
    requires P::represents(pp, rp), 0 <= j < P::row_count(pp),
    ensures ({
        let start = pu64s(pp, P::P_SUB_START);
        let s = prun_of(start, P::sub_count(pp), j);
        let y = P::stored_row(pp, rp, j);
        let q = pu64s(pp, P::P_TV)[j] as int;
        &&& 0 <= s < P::sub_count(pp) && start[s] <= j < start[s + 1]
        &&& y[0] == Val::Text(P::sub_adsh_of(pp, s))
        &&& y[6] == Val::Text(ptag_str(pp, q))
        &&& y[7] == Val::Text(pver_str(pp, q))
    }),
{
    let start = pu64s(pp, P::P_SUB_START);
    lemma_prun_of(start, P::sub_count(pp), P::row_count(pp), j);
    let s = prun_of(start, P::sub_count(pp), j);
    assert(P::stored_cols_ok(pp, P::stored_row(pp, rp, j), j));
    assert(P::sub_cols_ok(pp, P::stored_row(pp, rp, j), s));
}

/// Pre row `j` lies in the rows of pre adsh code `a` exactly when its sub-run has adsh code `a`.
proof fn lemma_pre_in_adsh(inp: ScanInput, np: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, a: int, j: int)
    requires
        P::pre_layout_ok(pp), inp_matches(inp, np, pp, ps), inp.wf(),
        0 <= a < inp.padsh.count, 0 <= j < inp.pn,
    ensures ({
        let s = prun_of(inp.sub_start@, inp.subs as int, j);
        (inp.pre_lo(a) <= j < inp.pre_hi(a)) == (pu64s(pp, P::P_SUB_ADSH)[s] == a)
    }),
{
    let start = inp.sub_start@;
    let ns = inp.subs as int;
    lemma_prun_of(start, ns, inp.pn as int, j);
    let s = prun_of(start, ns, j);
    P::lemma_adsh_subs(pp, a);
    let (s0, s1) = (inp.adsh_subs@[a] as int, inp.adsh_subs@[a + 1] as int);
    if s < s0 {
        assert(start[s + 1] <= start[s0]);
    }
    if s >= s1 {
        assert(start[s1] <= start[s]);
    }
    if s0 <= s < s1 {
        assert(start[s0] <= start[s]);
        assert(start[s + 1] <= start[s1]);
    }
}


// ------------------------------------------------------------------------------------- the per-row bridge

/// A pre row matching stored num row `i` gives the scan's match.
proof fn lemma_match_fwd(np: Seq<PartView>, pp: Seq<PartView>, rn: Seq<Seq<Row>>, rp: Seq<Seq<Row>>, inp: ScanInput,
    ps: Seq<Literal>, r: int, i: int, j0: int)
    requires
        N::represents(np, rn), P::represents(pp, rp), inp_matches(inp, np, pp, ps), inp.wf(),
        0 <= r < inp.runs, inp.run_start@[r] <= i < inp.run_start@[r + 1],
        0 <= j0 < rp[0].len(), pre_matches(N::stored_row(np, rn, i), rp[0][j0]),
    ensures inp.matched(r, i),
{
    let x = N::stored_row(np, rn, i);
    let orig = pu64s(pp, P::P_ORIG);
    lemma_permutation_facts_pre(pp);
    let j = crate::stores::pre::interface::common::perm::position_of(orig, j0);
    assert(0 <= j < inp.pn && orig[j] == j0);
    let y = P::stored_row(pp, rp, j);
    assert(y == rp[0][j0]);
    lemma_num_row(np, rn, r, i);
    lemma_pre_row(pp, rp, j);
    let s = prun_of(inp.sub_start@, inp.subs as int, j);
    let a = pu64s(pp, P::P_SUB_ADSH)[s] as int;
    assert(a < P::adsh_count(pp));
    lemma_pdict_at(inp.padsh, pp, P::P_ADSH_OFF, a);
    lemma_ndict_at(inp.nadsh, np, N::P_ADSH_OFF, inp.run_adsh@[r] as int);
    assert(inp.padsh.at(a) == inp.nadsh.at(inp.run_adsh@[r] as int));
    lemma_pre_in_adsh(inp, np, pp, ps, a, j);
    let q = inp.ptv@[j] as int;
    let p = inp.tv@[i] as int;
    assert(p < N::pair_count(np)) by {
        assert(N::u64s(np, N::P_TV)[i] < N::pair_count(np));
    }
    assert(q < P::pair_count(pp)) by {
        assert(pu64s(pp, P::P_TV)[j] < P::pair_count(pp));
    }
    assert(ptag_str(pp, q) == ntag_str(np, p) && pver_str(pp, q) == nver_str(np, p));
    if inp.npmv()[p] == 0 {
        assert(!(ptag_str(pp, q) == ntag_str(np, p) && pver_str(pp, q) == nver_str(np, p)));
    }
    lemma_ppair_inj(pp, inp.npmv()[p] - 1, q);
    assert(inp.ptv@[j] + 1 == inp.npmv()[inp.tv@[i] as int]);
}

/// The scan's match gives a pre row matching stored num row `i`.
proof fn lemma_match_back(np: Seq<PartView>, pp: Seq<PartView>, rn: Seq<Seq<Row>>, rp: Seq<Seq<Row>>, inp: ScanInput,
    ps: Seq<Literal>, r: int, i: int)
    requires
        N::represents(np, rn), P::represents(pp, rp), inp_matches(inp, np, pp, ps), inp.wf(),
        0 <= r < inp.runs, inp.run_start@[r] <= i < inp.run_start@[r + 1],
        inp.matched(r, i),
    ensures has_pre(rp[0], N::stored_row(np, rn, i)),
{
    let x = N::stored_row(np, rn, i);
    let (a, j) = choose|a: int, j: int| 0 <= a < inp.padsh.count && #[trigger] inp.padsh.at(a) == inp.nadsh.at(inp.run_adsh@[r] as int)
        && inp.pre_lo(a) <= j < inp.pre_hi(a) && #[trigger] inp.ptv@[j] + 1 == inp.npmv()[inp.tv@[i] as int];
    assert(inp.adsh_subs@[a] <= inp.adsh_subs@[a + 1] <= inp.subs);
    assert(inp.pre_hi(a) <= inp.sub_start@[inp.subs as int]);
    assert(j < inp.pn);
    lemma_pre_in_adsh(inp, np, pp, ps, a, j);
    lemma_num_row(np, rn, r, i);
    lemma_pre_row(pp, rp, j);
    let s = prun_of(inp.sub_start@, inp.subs as int, j);
    lemma_pdict_at(inp.padsh, pp, P::P_ADSH_OFF, a);
    lemma_ndict_at(inp.nadsh, np, N::P_ADSH_OFF, inp.run_adsh@[r] as int);
    let q = inp.ptv@[j] as int;
    let p = inp.tv@[i] as int;
    assert(p < N::pair_count(np)) by {
        assert(N::u64s(np, N::P_TV)[i] < N::pair_count(np));
    }
    assert(inp.npmv()[p] != 0);
    assert(inp.npmv()[p] - 1 == q);
    let y = P::stored_row(pp, rp, j);
    assert(pre_matches(x, y));
    let orig = pu64s(pp, P::P_ORIG);
    lemma_permutation_facts_pre(pp);
    assert(orig[j] < rp[0].len());
    assert(y == rp[0][orig[j] as int]);
}

proof fn lemma_permutation_facts_pre(pp: Seq<PartView>)
    requires P::pre_layout_ok(pp),
    ensures ({
        let orig = pu64s(pp, P::P_ORIG);
        let n = P::row_count(pp);
        &&& orig.len() == n
        &&& forall|j: int| 0 <= j < n ==> #[trigger] orig[j] < n
        &&& forall|k: int| 0 <= k < n ==> 0 <= #[trigger] crate::stores::pre::interface::common::perm::position_of(orig, k) < n
            && orig[crate::stores::pre::interface::common::perm::position_of(orig, k)] == k
    }),
{
    crate::stores::pre::interface::common::perm::lemma_permutation_facts(pu64s(pp, P::P_ORIG), P::row_count(pp) as nat);
}

/// Stored num row `i` of run `r` (uom `$1`): it passes the anti-join exactly when the scan qualifies it; its group
/// key and value are read from the parts.
pub proof fn lemma_pos_qual(np: Seq<PartView>, pp: Seq<PartView>, rn: Seq<Seq<Row>>, rp: Seq<Seq<Row>>, inp: ScanInput,
    ps: Seq<Literal>, r: int, i: int)
    requires
        N::represents(np, rn), P::represents(pp, rp), inp_matches(inp, np, pp, ps), inp.wf(),
        0 <= r < inp.runs, inp.run_start@[r] <= i < inp.run_start@[r + 1],
        N::run_uom_of(np, r) == ukey(ps),
    ensures ({
        let x = N::stored_row(np, rn, i);
        &&& (num_spec(ps, rp[0]).qual)(x) == inp.qual(r, i)
        &&& key2(x) == keyp(np, inp.tv@[i] as int)
        &&& coeff7(1, x) == inp.value@[i]
    }),
{
    let x = N::stored_row(np, rn, i);
    lemma_num_row(np, rn, r, i);
    assert(key2(x) =~= keyp(np, inp.tv@[i] as int));
    if has_pre(rp[0], x) {
        let j0 = choose|j: int| 0 <= j < rp[0].len() && pre_matches(x, #[trigger] rp[0][j]);
        lemma_match_fwd(np, pp, rn, rp, inp, ps, r, i, j0);
    }
    if inp.matched(r, i) {
        lemma_match_back(np, pp, rn, rp, inp, ps, r, i);
    }
    assert(num_where(ps, x) == (inp.dlo <= inp.ddate@[i] <= inp.dhi));
}

/// A stored num row of a run of another uom does not pass the WHERE conditions.
pub proof fn lemma_pos_other_uom(np: Seq<PartView>, rn: Seq<Seq<Row>>, ps: Seq<Literal>, pre: Seq<Row>, r: int, i: int)
    requires
        N::represents(np, rn), 0 <= r < N::run_count(np),
        N::u64s(np, N::P_RUN_START)[r] <= i < N::u64s(np, N::P_RUN_START)[r + 1],
        N::run_uom_of(np, r) != ukey(ps),
    ensures !(num_spec(ps, pre).qual)(N::stored_row(np, rn, i)),
{
    lemma_num_row(np, rn, r, i);
}

} // verus!


