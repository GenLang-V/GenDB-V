//! The stored parts the query reads, each read whole by one extent, with their facts (`num_in_ok`, `pre_in_ok`,
//! `tag_in_ok`, `sub_in_ok`): every slice is its part and every dictionary is well formed.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
use crate::stores::num::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::sub_sic::interface as S;
use crate::stores::tag_tv::interface as T;
use crate::stores::num::interface::common::text::{text_parts_wf, text_strictly_sorted, text_entry};
use crate::agent::maps::{Dict, dict_wf};
use crate::agent::levels::{nvals, pre_u64s};
use crate::agent::filing::tu64s;

verus! {

pub open spec fn u64v(p: PartView) -> Seq<u64> { match p { PartView::U64(s) => s, _ => Seq::empty() } }
pub open spec fn u8v(p: PartView) -> Seq<u8> { match p { PartView::U8(s) => s, _ => Seq::empty() } }
pub open spec fn i32v(p: PartView) -> Seq<i32> { match p { PartView::I32(s) => s, _ => Seq::empty() } }
pub open spec fn i128v(p: PartView) -> Seq<i128> { match p { PartView::I128(s) => s, _ => Seq::empty() } }

pub fn rd_u64(st: &mut StoredParts, p: usize) -> (r: &'static [u64])
    requires p < old(st)@.len(), old(st)@[p as int] is U64,
    ensures final(st)@ == old(st)@, r@ == u64v(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_u64(p, 0, n);
    proof { assert(r@ =~= u64v(old(st)@[p as int])); }
    r
}

pub fn rd_u8(st: &mut StoredParts, p: usize) -> (r: &'static [u8])
    requires p < old(st)@.len(), old(st)@[p as int] is U8,
    ensures final(st)@ == old(st)@, r@ == u8v(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_u8(p, 0, n);
    proof { assert(r@ =~= u8v(old(st)@[p as int])); }
    r
}

pub fn rd_i32(st: &mut StoredParts, p: usize) -> (r: &'static [i32])
    requires p < old(st)@.len(), old(st)@[p as int] is I32,
    ensures final(st)@ == old(st)@, r@ == i32v(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_i32(p, 0, n);
    proof { assert(r@ =~= i32v(old(st)@[p as int])); }
    r
}

pub fn rd_i128(st: &mut StoredParts, p: usize) -> (r: &'static [i128])
    requires p < old(st)@.len(), old(st)@[p as int] is I128,
    ensures final(st)@ == old(st)@, r@ == i128v(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_i128(p, 0, n);
    proof { assert(r@ =~= i128v(old(st)@[p as int])); }
    r
}

/// The text list in parts `po`, `po + 1`.
pub fn rd_dict(st: &mut StoredParts, po: usize) -> (d: Dict)
    requires po + 1 < old(st)@.len(), old(st)@[po as int] is U64, old(st)@[po + 1] is U8, u64v(old(st)@[po as int]).len() >= 1,
    ensures final(st)@ == old(st)@, d.off@ == u64v(old(st)@[po as int]), d.bytes@ == u8v(old(st)@[po + 1]),
        d.n == u64v(old(st)@[po as int]).len() - 1,
{
    let np = st.part_count();
    let off = rd_u64(st, po);
    let bytes = rd_u8(st, po + 1);
    Dict { off, bytes, n: off.len() - 1 }
}

pub open spec fn dict_is(d: Dict, parts: Seq<PartView>, po: int) -> bool {
    d.off@ == u64v(parts[po]) && d.bytes@ == u8v(parts[po + 1]) && d.n == u64v(parts[po]).len() - 1 && dict_wf(d)
}

// ------------------------------------------------------------------------------------------------ dictionary facts

proof fn lemma_wf_pre(off: Seq<u64>, bytes: Seq<u8>, n: int)
    requires
        crate::stores::pre::interface::common::text::text_parts_wf(off, bytes, n),
        crate::stores::pre::interface::common::text::text_strictly_sorted(off, bytes, n),
    ensures text_parts_wf(off, bytes, n), text_strictly_sorted(off, bytes, n),
{
    assert forall|a: int, b: int| 0 <= a < b < n implies crate::spec::text::lex_cmp(#[trigger] text_entry(off, bytes, a), #[trigger] text_entry(off, bytes, b)) < 0 by {
        assert(crate::stores::pre::interface::common::text::text_entry(off, bytes, a) == text_entry(off, bytes, a));
        assert(crate::stores::pre::interface::common::text::text_entry(off, bytes, b) == text_entry(off, bytes, b));
    }
}

proof fn lemma_wf_tag(off: Seq<u64>, bytes: Seq<u8>, n: int)
    requires
        crate::stores::tag_tv::interface::common::text::text_parts_wf(off, bytes, n),
        crate::stores::tag_tv::interface::common::text::text_strictly_sorted(off, bytes, n),
    ensures text_parts_wf(off, bytes, n), text_strictly_sorted(off, bytes, n),
{
    assert forall|a: int, b: int| 0 <= a < b < n implies crate::spec::text::lex_cmp(#[trigger] text_entry(off, bytes, a), #[trigger] text_entry(off, bytes, b)) < 0 by {
        assert(crate::stores::tag_tv::interface::common::text::text_entry(off, bytes, a) == text_entry(off, bytes, a));
        assert(crate::stores::tag_tv::interface::common::text::text_entry(off, bytes, b) == text_entry(off, bytes, b));
    }
}

// ------------------------------------------------------------------------------------------------ num

pub struct NumIn {
    pub uom: Dict,
    pub adsh: Dict,
    pub tag: Dict,
    pub ver: Dict,
    pub uom_runs: &'static [u64],
    pub run_adsh: &'static [u64],
    pub run_start: &'static [u64],
    pub tv: &'static [u64],
    pub val: &'static [i128],
    pub pt: &'static [u64],
    pub pv: &'static [u64],
}

pub open spec fn num_in_ok(num: Seq<PartView>, x: NumIn) -> bool {
    &&& N::num_layout_ok(num)
    &&& dict_is(x.uom, num, N::P_UOM_OFF as int) && x.uom.n == N::uom_count(num)
    &&& dict_is(x.adsh, num, N::P_ADSH_OFF as int) && x.adsh.n == N::adsh_count(num)
    &&& dict_is(x.tag, num, N::P_TAG_OFF as int) && x.tag.n == N::tag_count(num)
    &&& dict_is(x.ver, num, N::P_VERSION_OFF as int) && x.ver.n == N::version_count(num)
    &&& x.uom_runs@ == N::u64s(num, N::P_UOM_RUNS)
    &&& x.run_adsh@ == N::u64s(num, N::P_RUN_ADSH)
    &&& x.run_start@ == N::u64s(num, N::P_RUN_START)
    &&& x.tv@ == N::u64s(num, N::P_TV)
    &&& x.val@ == nvals(num)
    &&& x.pt@ == N::u64s(num, N::P_PAIR_TAG)
    &&& x.pv@ == N::u64s(num, N::P_PAIR_VERSION)
}

pub fn read_num(st: &mut StoredParts) -> (x: NumIn)
    requires N::num_layout_ok(old(st)@),
    ensures final(st)@ == old(st)@, num_in_ok(old(st)@, x),
{
    let ghost num = st@;
    let uom = rd_dict(st, N::P_UOM_OFF);
    let adsh = rd_dict(st, N::P_ADSH_OFF);
    let tag = rd_dict(st, N::P_TAG_OFF);
    let ver = rd_dict(st, N::P_VERSION_OFF);
    let uom_runs = rd_u64(st, N::P_UOM_RUNS);
    let run_adsh = rd_u64(st, N::P_RUN_ADSH);
    let run_start = rd_u64(st, N::P_RUN_START);
    let tv = rd_u64(st, N::P_TV);
    let val = rd_i128(st, N::P_VALUE);
    let pt = rd_u64(st, N::P_PAIR_TAG);
    let pv = rd_u64(st, N::P_PAIR_VERSION);
    NumIn { uom, adsh, tag, ver, uom_runs, run_adsh, run_start, tv, val, pt, pv }
}

// ------------------------------------------------------------------------------------------------ pre

pub struct PreIn {
    pub adsh: Dict,
    pub stmt: Dict,
    pub tag: Dict,
    pub ver: Dict,
    pub gstmt: &'static [u64],
    pub sub_group: &'static [u64],
    pub sub_start: &'static [u64],
    pub adsh_subs: &'static [u64],
    pub tv: &'static [u64],
    pub pt: &'static [u64],
    pub pv: &'static [u64],
    pub nrows: usize,
    pub nsub: usize,
}

pub open spec fn pre_in_ok(pre: Seq<PartView>, x: PreIn) -> bool {
    &&& P::pre_layout_ok(pre)
    &&& dict_is(x.adsh, pre, P::P_ADSH_OFF as int) && x.adsh.n == P::adsh_count(pre)
    &&& dict_is(x.stmt, pre, P::P_STMT_OFF as int) && x.stmt.n == P::stmt_count(pre)
    &&& dict_is(x.tag, pre, P::P_TAG_OFF as int) && x.tag.n == P::tag_count(pre)
    &&& dict_is(x.ver, pre, P::P_VERSION_OFF as int) && x.ver.n == P::version_count(pre)
    &&& x.gstmt@ == pre_u64s(pre, P::P_GROUP_STMT)
    &&& x.sub_group@ == pre_u64s(pre, P::P_SUB_GROUP)
    &&& x.sub_start@ == pre_u64s(pre, P::P_SUB_START)
    &&& x.adsh_subs@ == pre_u64s(pre, P::P_ADSH_SUBS)
    &&& x.tv@ == pre_u64s(pre, P::P_TV)
    &&& x.pt@ == pre_u64s(pre, P::P_PAIR_TAG)
    &&& x.pv@ == pre_u64s(pre, P::P_PAIR_VERSION)
    &&& x.nrows == P::row_count(pre)
    &&& x.nsub == P::sub_count(pre)
}

pub fn read_pre(st: &mut StoredParts) -> (x: PreIn)
    requires P::pre_layout_ok(old(st)@),
    ensures final(st)@ == old(st)@, pre_in_ok(old(st)@, x),
{
    let ghost pre = st@;
    let adsh = rd_dict(st, P::P_ADSH_OFF);
    let stmt = rd_dict(st, P::P_STMT_OFF);
    let tag = rd_dict(st, P::P_TAG_OFF);
    let ver = rd_dict(st, P::P_VERSION_OFF);
    proof {
        lemma_wf_pre(adsh.off@, adsh.bytes@, adsh.n as int);
        lemma_wf_pre(stmt.off@, stmt.bytes@, stmt.n as int);
        lemma_wf_pre(tag.off@, tag.bytes@, tag.n as int);
        lemma_wf_pre(ver.off@, ver.bytes@, ver.n as int);
    }
    let gstmt = rd_u64(st, P::P_GROUP_STMT);
    let sub_group = rd_u64(st, P::P_SUB_GROUP);
    let sub_start = rd_u64(st, P::P_SUB_START);
    let adsh_subs = rd_u64(st, P::P_ADSH_SUBS);
    let tv = rd_u64(st, P::P_TV);
    let pt = rd_u64(st, P::P_PAIR_TAG);
    let pv = rd_u64(st, P::P_PAIR_VERSION);
    let nrows = st.part_len(P::P_ORIG);
    let nsub = st.part_len(P::P_SUB_ADSH);
    PreIn { adsh, stmt, tag, ver, gstmt, sub_group, sub_start, adsh_subs, tv, pt, pv, nrows, nsub }
}

// ------------------------------------------------------------------------------------------------ tag

pub struct TagIn {
    pub tag: Dict,
    pub ver: Dict,
    pub tl: Dict,
    pub tc: &'static [u64],
    pub vc: &'static [u64],
    pub ord: &'static [u64],
    pub tfirst: &'static [u64],
    pub tvver: &'static [u64],
    pub abs: &'static [i32],
    pub tlv: &'static [u8],
    pub tlc: &'static [u64],
    pub n: usize,
}

pub open spec fn tag_in_ok(tag: Seq<PartView>, x: TagIn) -> bool {
    &&& T::tag_layout_ok(tag)
    &&& dict_is(x.tag, tag, T::P_TAG_OFF as int)
        && x.tag.n == crate::stores::tag_tv::interface::common::cols::text_count(tag, T::P_TAG_OFF as int)
    &&& dict_is(x.ver, tag, T::P_VERSION_OFF as int)
        && x.ver.n == crate::stores::tag_tv::interface::common::cols::text_count(tag, T::P_VERSION_OFF as int)
    &&& dict_is(x.tl, tag, T::P_TLABEL_OFF as int) && x.tl.n == crate::stores::tag_tv::interface::common::cols::text_count(tag, T::P_TLABEL_OFF as int)
    &&& x.tc@ == crate::stores::tag_tv::interface::common::cols::u64s(tag, T::P_TAG_CODES)
    &&& x.vc@ == crate::stores::tag_tv::interface::common::cols::u64s(tag, T::P_VERSION_CODES)
    &&& x.ord@ == crate::stores::tag_tv::interface::common::cols::u64s(tag, T::P_TV_ORDER)
    &&& x.tfirst@ == crate::stores::tag_tv::interface::common::cols::u64s(tag, T::P_TAG_FIRST)
    &&& x.tvver@ == crate::stores::tag_tv::interface::common::cols::u64s(tag, T::P_TV_VERSION)
    &&& x.abs@ == crate::stores::tag_tv::interface::common::cols::i32_part(tag[T::P_ABSTRACT as int])
    &&& x.tlv@ == crate::stores::tag_tv::interface::common::text::u8_part(tag[T::P_TLABEL_VALID as int])
    &&& x.tlc@ == crate::stores::tag_tv::interface::common::cols::u64s(tag, T::P_TLABEL_CODES)
    &&& x.n == T::row_count(tag)
}

pub fn read_tag(st: &mut StoredParts) -> (x: TagIn)
    requires T::tag_layout_ok(old(st)@),
    ensures final(st)@ == old(st)@, tag_in_ok(old(st)@, x),
{
    let ghost tag = st@;
    let tg = rd_dict(st, T::P_TAG_OFF);
    let ver = rd_dict(st, T::P_VERSION_OFF);
    let tl = rd_dict(st, T::P_TLABEL_OFF);
    proof {
        lemma_wf_tag(tg.off@, tg.bytes@, tg.n as int);
        lemma_wf_tag(ver.off@, ver.bytes@, ver.n as int);
        lemma_wf_tag(tl.off@, tl.bytes@, tl.n as int);
    }
    let tc = rd_u64(st, T::P_TAG_CODES);
    let vc = rd_u64(st, T::P_VERSION_CODES);
    let ord = rd_u64(st, T::P_TV_ORDER);
    let tfirst = rd_u64(st, T::P_TAG_FIRST);
    let tvver = rd_u64(st, T::P_TV_VERSION);
    let abs = rd_i32(st, T::P_ABSTRACT);
    let tlv = rd_u8(st, T::P_TLABEL_VALID);
    let tlc = rd_u64(st, T::P_TLABEL_CODES);
    let n = st.part_len(T::P_CUSTOM);
    TagIn { tag: tg, ver, tl, tc, vc, ord, tfirst, tvver, abs, tlv, tlc, n }
}

// ------------------------------------------------------------------------------------------------ sub

pub struct SubIn {
    pub cik: &'static [i32],
    pub sic: &'static [i32],
    pub sicv: &'static [u8],
    pub adsh_off: &'static [u64],
    pub adsh_bytes: &'static [u8],
    pub rank: &'static [u64],
    /// `sic_order`: the rows sorted by (sic with NULL first, cik, row).
    pub ord: &'static [u64],
    pub n: usize,
}

pub open spec fn sub_in_ok(sub: Seq<PartView>, x: SubIn) -> bool {
    &&& S::sub_layout_ok(sub)
    &&& x.cik@ == i32v(sub[S::P_CIK as int]) && x.sic@ == i32v(sub[S::P_SIC as int]) && x.sicv@ == u8v(sub[S::P_SIC_VALID as int])
    &&& x.adsh_off@ == u64v(sub[S::P_ADSH_OFF as int]) && x.adsh_bytes@ == u8v(sub[S::P_ADSH_BYTES as int])
    &&& x.n == S::row_count(sub)
    &&& x.ord@ == u64v(sub[S::P_SIC_ORDER as int])
    &&& x.cik@.len() == x.n && x.sic@.len() == x.n && x.sicv@.len() == x.n
    &&& text_parts_wf(x.adsh_off@, x.adsh_bytes@, x.n as int)
    &&& x.rank@.len() == x.n
}

pub fn read_sub(st: &mut StoredParts) -> (x: SubIn)
    requires S::sub_layout_ok(old(st)@),
    ensures final(st)@ == old(st)@, sub_in_ok(old(st)@, x),
{
    let cik = rd_i32(st, S::P_CIK);
    let sic = rd_i32(st, S::P_SIC);
    let sicv = rd_u8(st, S::P_SIC_VALID);
    let adsh_off = rd_u64(st, S::P_ADSH_OFF);
    let adsh_bytes = rd_u8(st, S::P_ADSH_BYTES);
    let rank = rd_u64(st, S::P_ADSH_RANK);
    let ord = rd_u64(st, S::P_SIC_ORDER);
    let n = cik.len();
    SubIn { cik, sic, sicv, adsh_off, adsh_bytes, rank, ord, n }
}

} // verus!
