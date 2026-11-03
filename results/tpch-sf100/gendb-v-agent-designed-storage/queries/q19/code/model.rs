//! The stored parts as typed rows, and the column handles the kernel reads.
//!
//! Lineitem (storage `facts`, parts `0 .. 48`, clustered order): stored row `s` decodes to the six query columns
//! `[l_partkey, l_quantity, l_extendedprice, l_discount, l_shipinstruct, l_shipmode]` (`li_row`: an integer key,
//! numeric coefficients of scale 2, dictionary texts). Every integer column is frame-of-reference coded over uniform
//! groups of `li_bs` rows (`base[s / li_bs] + code[s]`); l_shipinstruct and l_shipmode are sorted dictionaries
//! whose entry index is coded the same way. The l_partkey key index (`LI_KEYIDX_*`, kind 1 or 2) lists stored rows
//! in nondecreasing key order: index position `p` holds stored row `irow_at(fp, p)` (`irows`: the stored rows in
//! index order).
//!
//! Part (storage `custpart`, parts `21 .. 50`, canonical order): stored row `j` decodes to
//! `[p_partkey, p_brand, p_size, p_container]` (`pa_row`), p_brand and p_container sorted dictionaries.
//!
//! `LiCols` / `PaCols` are the whole extents the kernel reads, `li_cols_ok` / `pa_cols_ok` state that they are the
//! parts' contents; `li_shape` / `pa_shape` are the facts of `represents` (and of the column types) they rely on.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::interface::common::keyidx::{keyidx_ok, irow, fkey};
use crate::stores::custpart::interface as cpi;
use crate::stores::custpart::interface::common::colfmt as cpc;
use super::common::fastdiv::{Divisor, divisor_ok};

verus! {

/// `10^15`: the exclusive bound of a numeric(15, 2) coefficient.
pub open spec fn p15() -> int {
    1_000_000_000_000_000
}

/// `|x| < b`.
pub open spec fn abs_lt(x: int, b: int) -> bool {
    -b < x && x < b
}

// ------------------------------------------------------------------------------------------------ lineitem rows

/// Number of stored lineitem rows.
pub open spec fn n_li(fp: Seq<PartView>) -> int {
    part_len(fp[LI_QUANTITY_CODES as int]) as int
}

/// Rows per lineitem group.
pub open spec fn li_bs(fp: Seq<PartView>) -> int {
    u64s(fp[LI_LAYOUT as int])[1] as int
}

/// The lineitem row groups.
pub open spec fn li_gs(fp: Seq<PartView>) -> Seq<u64> {
    u64s(fp[LI_GROUPS as int])
}

pub open spec fn lpk_at(fp: Seq<PartView>, s: int) -> int {
    for_at(li_gs(fp), fp[LI_PARTKEY_BASE as int], fp[LI_PARTKEY_CODES as int], s)
}

pub open spec fn qty_at(fp: Seq<PartView>, s: int) -> int {
    for_at(li_gs(fp), fp[LI_QUANTITY_BASE as int], fp[LI_QUANTITY_CODES as int], s)
}

pub open spec fn price_at(fp: Seq<PartView>, s: int) -> int {
    for_at(li_gs(fp), fp[LI_EXTENDEDPRICE_BASE as int], fp[LI_EXTENDEDPRICE_CODES as int], s)
}

pub open spec fn disc_at(fp: Seq<PartView>, s: int) -> int {
    for_at(li_gs(fp), fp[LI_DISCOUNT_BASE as int], fp[LI_DISCOUNT_CODES as int], s)
}

/// Dictionary index of the l_shipinstruct of stored row `s`.
pub open spec fn sidx_at(fp: Seq<PartView>, s: int) -> int {
    for_at(li_gs(fp), fp[LI_SHIPINSTRUCT_BASE as int], fp[LI_SHIPINSTRUCT_CODES as int], s)
}

/// Dictionary index of the l_shipmode of stored row `s`.
pub open spec fn midx_at(fp: Seq<PartView>, s: int) -> int {
    for_at(li_gs(fp), fp[LI_SHIPMODE_BASE as int], fp[LI_SHIPMODE_CODES as int], s)
}

pub open spec fn sd_o(fp: Seq<PartView>) -> Seq<u64> {
    u64s(fp[LI_SHIPINSTRUCT_DICT_OFFS as int])
}

pub open spec fn sd_y(fp: Seq<PartView>) -> Seq<u8> {
    u8s(fp[LI_SHIPINSTRUCT_DICT_BYTES as int])
}

/// Number of l_shipinstruct dictionary entries.
pub open spec fn n_sd(fp: Seq<PartView>) -> int {
    sd_o(fp).len() - 1
}

pub open spec fn sdict(fp: Seq<PartView>, e: int) -> Seq<u8> {
    text_of(sd_o(fp), sd_y(fp), e)
}

pub open spec fn md_o(fp: Seq<PartView>) -> Seq<u64> {
    u64s(fp[LI_SHIPMODE_DICT_OFFS as int])
}

pub open spec fn md_y(fp: Seq<PartView>) -> Seq<u8> {
    u8s(fp[LI_SHIPMODE_DICT_BYTES as int])
}

/// Number of l_shipmode dictionary entries.
pub open spec fn n_md(fp: Seq<PartView>) -> int {
    md_o(fp).len() - 1
}

pub open spec fn mdict(fp: Seq<PartView>, e: int) -> Seq<u8> {
    text_of(md_o(fp), md_y(fp), e)
}

/// A lineitem row of the six query columns.
pub open spec fn li_val(k: int, q: int, p: int, d: int, si: Seq<u8>, sm: Seq<u8>) -> Row {
    seq![Val::Int(k), Val::Num { coeff: q, scale: 2 }, Val::Num { coeff: p, scale: 2 }, Val::Num { coeff: d, scale: 2 },
        Val::Text(si), Val::Text(sm)]
}

/// Stored lineitem row `s`.
pub open spec fn li_row(fp: Seq<PartView>, s: int) -> Row {
    li_val(lpk_at(fp, s), qty_at(fp, s), price_at(fp, s), disc_at(fp, s), sdict(fp, sidx_at(fp, s)), mdict(fp, midx_at(fp, s)))
}

/// The query columns of every stored lineitem row, in stored order.
pub open spec fn li_rows(fp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_li(fp) as nat, |s: int| li_row(fp, s))
}

// ------------------------------------------------------------------------------------------------ the key index

pub open spec fn pk_c(fp: Seq<PartView>) -> Seq<u32> {
    u32s(fp[LI_PARTKEY_CODES as int])
}

pub open spec fn pk_b(fp: Seq<PartView>) -> Seq<i64> {
    i64s(fp[LI_PARTKEY_BASE as int])
}

pub open spec fn kx_c(fp: Seq<PartView>) -> Seq<u32> {
    u32s(fp[LI_KEYIDX_CODES as int])
}

pub open spec fn kx_b(fp: Seq<PartView>) -> Seq<u64> {
    u64s(fp[LI_KEYIDX_BASE as int])
}

/// Key index kind: 0 none, 1 stored rows sorted by key, 2 index column.
pub open spec fn kx_kind(fp: Seq<PartView>) -> u64 {
    u64s(fp[LI_KEYIDX_KIND as int])[0]
}

/// The stored row at key index position `p`.
pub open spec fn irow_at(fp: Seq<PartView>, p: int) -> int {
    irow(kx_kind(fp), kx_c(fp), kx_b(fp), li_bs(fp), p)
}

/// The key at key index position `p`.
pub open spec fn ikey_at(fp: Seq<PartView>, p: int) -> int {
    fkey(pk_c(fp), pk_b(fp), li_bs(fp), irow_at(fp, p))
}

/// The key index over the stored l_partkey column.
pub open spec fn kx_ok(fp: Seq<PartView>) -> bool {
    keyidx_ok(pk_c(fp), pk_b(fp), kx_c(fp), kx_b(fp), li_bs(fp), kx_kind(fp), n_li(fp))
}

/// The stored lineitem rows in key index order.
pub open spec fn irows(fp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_li(fp) as nat, |p: int| li_row(fp, irow_at(fp, p)))
}

// ------------------------------------------------------------------------------------------------ part rows

/// Index of part `k` of table part in the custpart parts.
pub open spec fn pp(k: usize) -> int {
    (cpi::PART_FIRST + k) as int
}

/// Number of stored part rows.
pub open spec fn n_pa(cp: Seq<PartView>) -> int {
    part_len(cp[pp(cpi::PA_PARTKEY_CODES)]) as int
}

/// Rows per part group.
pub open spec fn pa_bs(cp: Seq<PartView>) -> int {
    cpc::u64s(cp[pp(cpi::PA_LAYOUT)])[1] as int
}

/// The part row groups.
pub open spec fn pa_gs(cp: Seq<PartView>) -> Seq<u64> {
    cpc::u64s(cp[pp(cpi::PA_GROUPS)])
}

pub open spec fn pkey_at(cp: Seq<PartView>, j: int) -> int {
    cpc::for_at(pa_gs(cp), cp[pp(cpi::PA_PARTKEY_BASE)], cp[pp(cpi::PA_PARTKEY_CODES)], j)
}

/// Dictionary index of the p_brand of stored part row `j`.
pub open spec fn bidx_at(cp: Seq<PartView>, j: int) -> int {
    cpc::for_at(pa_gs(cp), cp[pp(cpi::PA_BRAND_BASE)], cp[pp(cpi::PA_BRAND_CODES)], j)
}

pub open spec fn size_at(cp: Seq<PartView>, j: int) -> int {
    cpc::for_at(pa_gs(cp), cp[pp(cpi::PA_SIZE_BASE)], cp[pp(cpi::PA_SIZE_CODES)], j)
}

/// Dictionary index of the p_container of stored part row `j`.
pub open spec fn cidx_at(cp: Seq<PartView>, j: int) -> int {
    cpc::for_at(pa_gs(cp), cp[pp(cpi::PA_CONTAINER_BASE)], cp[pp(cpi::PA_CONTAINER_CODES)], j)
}

pub open spec fn bd_o(cp: Seq<PartView>) -> Seq<u64> {
    cpc::u64s(cp[pp(cpi::PA_BRAND_DICT_OFFS)])
}

pub open spec fn bd_y(cp: Seq<PartView>) -> Seq<u8> {
    cpc::u8s(cp[pp(cpi::PA_BRAND_DICT_BYTES)])
}

pub open spec fn n_bd(cp: Seq<PartView>) -> int {
    bd_o(cp).len() - 1
}

pub open spec fn bdict(cp: Seq<PartView>, e: int) -> Seq<u8> {
    cpc::text_of(bd_o(cp), bd_y(cp), e)
}

pub open spec fn cd_o(cp: Seq<PartView>) -> Seq<u64> {
    cpc::u64s(cp[pp(cpi::PA_CONTAINER_DICT_OFFS)])
}

pub open spec fn cd_y(cp: Seq<PartView>) -> Seq<u8> {
    cpc::u8s(cp[pp(cpi::PA_CONTAINER_DICT_BYTES)])
}

pub open spec fn n_cd(cp: Seq<PartView>) -> int {
    cd_o(cp).len() - 1
}

pub open spec fn cdict(cp: Seq<PartView>, e: int) -> Seq<u8> {
    cpc::text_of(cd_o(cp), cd_y(cp), e)
}

/// A part row of the four query columns.
pub open spec fn pa_val(k: int, b: Seq<u8>, sz: int, c: Seq<u8>) -> Row {
    seq![Val::Int(k), Val::Text(b), Val::Int(sz), Val::Text(c)]
}

/// Stored part row `j`.
pub open spec fn pa_row(cp: Seq<PartView>, j: int) -> Row {
    pa_val(pkey_at(cp, j), bdict(cp, bidx_at(cp, j)), size_at(cp, j), cdict(cp, cidx_at(cp, j)))
}

/// The query columns of every stored part row, in stored (canonical) order.
pub open spec fn pa_rows(cp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_pa(cp) as nat, |j: int| pa_row(cp, j))
}

// ------------------------------------------------------------------------------------------------ shape facts

/// An I64 base part with one entry per lineitem group.
pub open spec fn li_ibase(fp: Seq<PartView>, k: int) -> bool {
    fp[k] is I64 && i64s(fp[k]).len() == li_gs(fp).len() - 1
}

/// A U64 base part with one entry per lineitem group.
pub open spec fn li_ubase(fp: Seq<PartView>, k: int) -> bool {
    fp[k] is U64 && u64s(fp[k]).len() == li_gs(fp).len() - 1
}

/// The facts of the lineitem parts the kernel relies on (consequences of `represents` and the column types).
pub open spec fn li_shape(fp: Seq<PartView>) -> bool {
    let n = n_li(fp);
    &&& fp.len() == FACTS_PARTS
    &&& fp[LI_LAYOUT as int] is U64 && u64s(fp[LI_LAYOUT as int]).len() == 2
    &&& groups_part_ok(fp[LI_GROUPS as int], n, li_bs(fp))
    &&& fp[LI_PARTKEY_CODES as int] is U32 && part_len(fp[LI_PARTKEY_CODES as int]) == n
    &&& fp[LI_QUANTITY_CODES as int] is U16
    &&& fp[LI_EXTENDEDPRICE_CODES as int] is U32 && part_len(fp[LI_EXTENDEDPRICE_CODES as int]) == n
    &&& fp[LI_DISCOUNT_CODES as int] is U8 && part_len(fp[LI_DISCOUNT_CODES as int]) == n
    &&& fp[LI_SHIPINSTRUCT_CODES as int] is U8 && part_len(fp[LI_SHIPINSTRUCT_CODES as int]) == n
    &&& fp[LI_SHIPMODE_CODES as int] is U8 && part_len(fp[LI_SHIPMODE_CODES as int]) == n
    &&& li_ibase(fp, LI_PARTKEY_BASE as int)
    &&& li_ibase(fp, LI_QUANTITY_BASE as int)
    &&& li_ibase(fp, LI_EXTENDEDPRICE_BASE as int)
    &&& li_ibase(fp, LI_DISCOUNT_BASE as int)
    &&& li_ubase(fp, LI_SHIPINSTRUCT_BASE as int)
    &&& li_ubase(fp, LI_SHIPMODE_BASE as int)
    &&& fp[LI_SHIPINSTRUCT_DICT_OFFS as int] is U64 && fp[LI_SHIPINSTRUCT_DICT_BYTES as int] is U8
    &&& sd_o(fp).len() >= 1 && text_parts_wf(sd_o(fp), sd_y(fp), n_sd(fp))
    &&& fp[LI_SHIPMODE_DICT_OFFS as int] is U64 && fp[LI_SHIPMODE_DICT_BYTES as int] is U8
    &&& md_o(fp).len() >= 1 && text_parts_wf(md_o(fp), md_y(fp), n_md(fp))
    &&& dict_sorted(sd_o(fp), sd_y(fp), n_sd(fp))
    &&& dict_sorted(md_o(fp), md_y(fp), n_md(fp))
    &&& fp[LI_KEYIDX_CODES as int] is U32 && fp[LI_KEYIDX_BASE as int] is U64
    &&& fp[LI_KEYIDX_KIND as int] is U64 && u64s(fp[LI_KEYIDX_KIND as int]).len() == 1
    &&& kx_ok(fp)
    &&& forall|s: int| 0 <= s < n ==> 0 <= #[trigger] sidx_at(fp, s) < n_sd(fp)
    &&& forall|s: int| 0 <= s < n ==> 0 <= #[trigger] midx_at(fp, s) < n_md(fp)
    &&& forall|s: int| 0 <= s < n ==> i64::MIN <= #[trigger] lpk_at(fp, s) <= i64::MAX
    &&& forall|s: int| 0 <= s < n ==> abs_lt(#[trigger] qty_at(fp, s), p15())
    &&& forall|s: int| 0 <= s < n ==> abs_lt(#[trigger] price_at(fp, s), p15())
    &&& forall|s: int| 0 <= s < n ==> abs_lt(#[trigger] disc_at(fp, s), p15())
}

/// The facts of the part parts the scan relies on.
pub open spec fn pa_shape(cp: Seq<PartView>) -> bool {
    let n = n_pa(cp);
    let ng = pa_gs(cp).len() - 1;
    &&& cp.len() == cpi::CUSTPART_PARTS
    &&& cp[pp(cpi::PA_LAYOUT)] is U64 && cpc::u64s(cp[pp(cpi::PA_LAYOUT)]).len() == 2
    &&& cpc::groups_part_ok(cp[pp(cpi::PA_GROUPS)], n, pa_bs(cp))
    &&& cp[pp(cpi::PA_PARTKEY_CODES)] is U32
    &&& cp[pp(cpi::PA_PARTKEY_BASE)] is I64 && part_len(cp[pp(cpi::PA_PARTKEY_BASE)]) == ng
    &&& cp[pp(cpi::PA_BRAND_CODES)] is U8 && part_len(cp[pp(cpi::PA_BRAND_CODES)]) == n
    &&& cp[pp(cpi::PA_BRAND_BASE)] is U64 && part_len(cp[pp(cpi::PA_BRAND_BASE)]) == ng
    &&& cp[pp(cpi::PA_SIZE_CODES)] is U8 && part_len(cp[pp(cpi::PA_SIZE_CODES)]) == n
    &&& cp[pp(cpi::PA_SIZE_BASE)] is I64 && part_len(cp[pp(cpi::PA_SIZE_BASE)]) == ng
    &&& cp[pp(cpi::PA_CONTAINER_CODES)] is U8 && part_len(cp[pp(cpi::PA_CONTAINER_CODES)]) == n
    &&& cp[pp(cpi::PA_CONTAINER_BASE)] is U64 && part_len(cp[pp(cpi::PA_CONTAINER_BASE)]) == ng
    &&& cp[pp(cpi::PA_BRAND_DICT_OFFS)] is U64 && cp[pp(cpi::PA_BRAND_DICT_BYTES)] is U8
    &&& bd_o(cp).len() >= 1 && cpc::text_parts_wf(bd_o(cp), bd_y(cp), n_bd(cp))
    &&& cp[pp(cpi::PA_CONTAINER_DICT_OFFS)] is U64 && cp[pp(cpi::PA_CONTAINER_DICT_BYTES)] is U8
    &&& cd_o(cp).len() >= 1 && cpc::text_parts_wf(cd_o(cp), cd_y(cp), n_cd(cp))
    &&& cpc::dict_sorted(bd_o(cp), bd_y(cp), n_bd(cp))
    &&& cpc::dict_sorted(cd_o(cp), cd_y(cp), n_cd(cp))
    &&& forall|j: int| 0 <= j < n ==> 0 <= #[trigger] bidx_at(cp, j) < n_bd(cp)
    &&& forall|j: int| 0 <= j < n ==> 0 <= #[trigger] cidx_at(cp, j) < n_cd(cp)
    &&& forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] pkey_at(cp, j) <= i64::MAX
    &&& forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] size_at(cp, j) <= i64::MAX
}

// ------------------------------------------------------------------------------------------------ column handles

/// The lineitem extents the kernel reads (whole parts).
#[derive(Clone, Copy)]
pub struct LiCols {
    /// Number of stored rows.
    pub n: usize,
    /// Rows per group.
    pub bs: u64,
    /// Division by `bs` (a shift for a power of two).
    pub dv: Divisor,
    pub pk: &'static [u32],
    pub pkb: &'static [i64],
    pub q: &'static [u16],
    pub qb: &'static [i64],
    pub pr: &'static [u32],
    pub prb: &'static [i64],
    pub d: &'static [u8],
    pub db: &'static [i64],
    pub si: &'static [u8],
    pub sib: &'static [u64],
    pub sm: &'static [u8],
    pub smb: &'static [u64],
    /// The key index column (kind 2) and its kind.
    pub kc: &'static [u32],
    pub kb: &'static [u64],
    pub kind: u64,
}

pub open spec fn li_cols_ok(c: LiCols, fp: Seq<PartView>) -> bool {
    &&& li_shape(fp)
    &&& c.n == n_li(fp)
    &&& c.bs == li_bs(fp)
    &&& divisor_ok(c.dv, li_bs(fp))
    &&& c.pk@ == pk_c(fp)
    &&& c.pkb@ == pk_b(fp)
    &&& c.q@ == u16s_of(fp[LI_QUANTITY_CODES as int])
    &&& c.qb@ == i64s(fp[LI_QUANTITY_BASE as int])
    &&& c.pr@ == u32s(fp[LI_EXTENDEDPRICE_CODES as int])
    &&& c.prb@ == i64s(fp[LI_EXTENDEDPRICE_BASE as int])
    &&& c.d@ == u8s(fp[LI_DISCOUNT_CODES as int])
    &&& c.db@ == i64s(fp[LI_DISCOUNT_BASE as int])
    &&& c.si@ == u8s(fp[LI_SHIPINSTRUCT_CODES as int])
    &&& c.sib@ == u64s(fp[LI_SHIPINSTRUCT_BASE as int])
    &&& c.sm@ == u8s(fp[LI_SHIPMODE_CODES as int])
    &&& c.smb@ == u64s(fp[LI_SHIPMODE_BASE as int])
    &&& c.kc@ == kx_c(fp)
    &&& c.kb@ == kx_b(fp)
    &&& c.kind == kx_kind(fp)
}

/// The U16 codes of a part.
pub open spec fn u16s_of(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

/// The part extents the scan reads (whole parts).
#[derive(Clone, Copy)]
pub struct PaCols {
    /// Number of stored rows.
    pub n: usize,
    /// Rows per group.
    pub bs: u64,
    /// Number of groups.
    pub ng: usize,
    pub pk: &'static [u32],
    pub pkb: &'static [i64],
    pub br: &'static [u8],
    pub brb: &'static [u64],
    pub sz: &'static [u8],
    pub szb: &'static [i64],
    pub ct: &'static [u8],
    pub ctb: &'static [u64],
}

pub open spec fn pa_cols_ok(c: PaCols, cp: Seq<PartView>) -> bool {
    &&& pa_shape(cp)
    &&& c.n == n_pa(cp)
    &&& c.bs == pa_bs(cp)
    &&& c.ng + 1 == pa_gs(cp).len()
    &&& c.pk@ == cpc::u32s(cp[pp(cpi::PA_PARTKEY_CODES)])
    &&& c.pkb@ == cpc::i64s(cp[pp(cpi::PA_PARTKEY_BASE)])
    &&& c.br@ == cpc::u8s(cp[pp(cpi::PA_BRAND_CODES)])
    &&& c.brb@ == cpc::u64s(cp[pp(cpi::PA_BRAND_BASE)])
    &&& c.sz@ == cpc::u8s(cp[pp(cpi::PA_SIZE_CODES)])
    &&& c.szb@ == cpc::i64s(cp[pp(cpi::PA_SIZE_BASE)])
    &&& c.ct@ == cpc::u8s(cp[pp(cpi::PA_CONTAINER_CODES)])
    &&& c.ctb@ == cpc::u64s(cp[pp(cpi::PA_CONTAINER_BASE)])
}

/// The dictionaries the tables are built from: l_shipinstruct, l_shipmode, p_brand, p_container.
#[derive(Clone, Copy)]
pub struct Dicts {
    pub so: &'static [u64],
    pub sy: &'static [u8],
    pub mo: &'static [u64],
    pub my: &'static [u8],
    pub bo: &'static [u64],
    pub by: &'static [u8],
    pub co: &'static [u64],
    pub cy: &'static [u8],
}

pub open spec fn dicts_ok(d: Dicts, fp: Seq<PartView>, cp: Seq<PartView>) -> bool {
    &&& d.so@ == sd_o(fp) && d.sy@ == sd_y(fp)
    &&& d.mo@ == md_o(fp) && d.my@ == md_y(fp)
    &&& d.bo@ == bd_o(cp) && d.by@ == bd_y(cp)
    &&& d.co@ == cd_o(cp) && d.cy@ == cd_y(cp)
}

// ------------------------------------------------------------------------------------------------ readers

/// The lineitem extents of the kernel.
pub fn read_li(f: &mut StoredParts, Ghost(fp): Ghost<Seq<PartView>>) -> (c: LiCols)
    requires
        old(f)@ == fp,
        li_shape(fp),
    ensures
        final(f)@ == fp,
        li_cols_ok(c, fp),
{
    let lay = f.extent_u64(LI_LAYOUT, 0, 2);
    let bs = lay[1];
    let dv = Divisor::new(bs);
    let n = f.part_len(LI_QUANTITY_CODES);
    let ng = f.part_len(LI_PARTKEY_BASE);
    let pk = f.extent_u32(LI_PARTKEY_CODES, 0, n);
    let pkb = f.extent_i64(LI_PARTKEY_BASE, 0, ng);
    let q = f.extent_u16(LI_QUANTITY_CODES, 0, n);
    let qb = f.extent_i64(LI_QUANTITY_BASE, 0, ng);
    let pr = f.extent_u32(LI_EXTENDEDPRICE_CODES, 0, n);
    let prb = f.extent_i64(LI_EXTENDEDPRICE_BASE, 0, ng);
    let d = f.extent_u8(LI_DISCOUNT_CODES, 0, n);
    let db = f.extent_i64(LI_DISCOUNT_BASE, 0, ng);
    let si = f.extent_u8(LI_SHIPINSTRUCT_CODES, 0, n);
    let sib = f.extent_u64(LI_SHIPINSTRUCT_BASE, 0, ng);
    let sm = f.extent_u8(LI_SHIPMODE_CODES, 0, n);
    let smb = f.extent_u64(LI_SHIPMODE_BASE, 0, ng);
    let nkc = f.part_len(LI_KEYIDX_CODES);
    let nkb = f.part_len(LI_KEYIDX_BASE);
    let kc = f.extent_u32(LI_KEYIDX_CODES, 0, nkc);
    let kb = f.extent_u64(LI_KEYIDX_BASE, 0, nkb);
    let kv = f.extent_u64(LI_KEYIDX_KIND, 0, 1);
    let kind = kv[0];
    let c = LiCols { n, bs, dv, pk, pkb, q, qb, pr, prb, d, db, si, sib, sm, smb, kc, kb, kind };
    proof {
        assert(pk@ =~= pk_c(fp));
        assert(pkb@ =~= pk_b(fp));
        assert(q@ =~= u16s_of(fp[LI_QUANTITY_CODES as int]));
        assert(qb@ =~= i64s(fp[LI_QUANTITY_BASE as int]));
        assert(pr@ =~= u32s(fp[LI_EXTENDEDPRICE_CODES as int]));
        assert(prb@ =~= i64s(fp[LI_EXTENDEDPRICE_BASE as int]));
        assert(d@ =~= u8s(fp[LI_DISCOUNT_CODES as int]));
        assert(db@ =~= i64s(fp[LI_DISCOUNT_BASE as int]));
        assert(si@ =~= u8s(fp[LI_SHIPINSTRUCT_CODES as int]));
        assert(sib@ =~= u64s(fp[LI_SHIPINSTRUCT_BASE as int]));
        assert(sm@ =~= u8s(fp[LI_SHIPMODE_CODES as int]));
        assert(smb@ =~= u64s(fp[LI_SHIPMODE_BASE as int]));
        assert(kc@ =~= kx_c(fp));
        assert(kb@ =~= kx_b(fp));
    }
    c
}

/// The part extents of the scan.
pub fn read_pa(f: &mut StoredParts, Ghost(cp): Ghost<Seq<PartView>>) -> (c: PaCols)
    requires
        old(f)@ == cp,
        pa_shape(cp),
    ensures
        final(f)@ == cp,
        pa_cols_ok(c, cp),
{
    let lay = f.extent_u64(cpi::PART_FIRST + cpi::PA_LAYOUT, 0, 2);
    let bs = lay[1];
    let n = f.part_len(cpi::PART_FIRST + cpi::PA_PARTKEY_CODES);
    let ng = f.part_len(cpi::PART_FIRST + cpi::PA_PARTKEY_BASE);
    let pk = f.extent_u32(cpi::PART_FIRST + cpi::PA_PARTKEY_CODES, 0, n);
    let pkb = f.extent_i64(cpi::PART_FIRST + cpi::PA_PARTKEY_BASE, 0, ng);
    let br = f.extent_u8(cpi::PART_FIRST + cpi::PA_BRAND_CODES, 0, n);
    let brb = f.extent_u64(cpi::PART_FIRST + cpi::PA_BRAND_BASE, 0, ng);
    let sz = f.extent_u8(cpi::PART_FIRST + cpi::PA_SIZE_CODES, 0, n);
    let szb = f.extent_i64(cpi::PART_FIRST + cpi::PA_SIZE_BASE, 0, ng);
    let ct = f.extent_u8(cpi::PART_FIRST + cpi::PA_CONTAINER_CODES, 0, n);
    let ctb = f.extent_u64(cpi::PART_FIRST + cpi::PA_CONTAINER_BASE, 0, ng);
    let c = PaCols { n, bs, ng, pk, pkb, br, brb, sz, szb, ct, ctb };
    proof {
        assert(pk@ =~= cpc::u32s(cp[pp(cpi::PA_PARTKEY_CODES)]));
        assert(pkb@ =~= cpc::i64s(cp[pp(cpi::PA_PARTKEY_BASE)]));
        assert(br@ =~= cpc::u8s(cp[pp(cpi::PA_BRAND_CODES)]));
        assert(brb@ =~= cpc::u64s(cp[pp(cpi::PA_BRAND_BASE)]));
        assert(sz@ =~= cpc::u8s(cp[pp(cpi::PA_SIZE_CODES)]));
        assert(szb@ =~= cpc::i64s(cp[pp(cpi::PA_SIZE_BASE)]));
        assert(ct@ =~= cpc::u8s(cp[pp(cpi::PA_CONTAINER_CODES)]));
        assert(ctb@ =~= cpc::u64s(cp[pp(cpi::PA_CONTAINER_BASE)]));
    }
    c
}

/// The four dictionaries.
pub fn read_dicts(f: &mut StoredParts, g: &mut StoredParts, Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>)
    -> (d: Dicts)
    requires
        old(f)@ == fp,
        old(g)@ == cp,
        li_shape(fp),
        pa_shape(cp),
    ensures
        final(f)@ == fp,
        final(g)@ == cp,
        dicts_ok(d, fp, cp),
{
    let n1 = f.part_len(LI_SHIPINSTRUCT_DICT_OFFS);
    let n2 = f.part_len(LI_SHIPINSTRUCT_DICT_BYTES);
    let so = f.extent_u64(LI_SHIPINSTRUCT_DICT_OFFS, 0, n1);
    let sy = f.extent_u8(LI_SHIPINSTRUCT_DICT_BYTES, 0, n2);
    let n3 = f.part_len(LI_SHIPMODE_DICT_OFFS);
    let n4 = f.part_len(LI_SHIPMODE_DICT_BYTES);
    let mo = f.extent_u64(LI_SHIPMODE_DICT_OFFS, 0, n3);
    let my = f.extent_u8(LI_SHIPMODE_DICT_BYTES, 0, n4);
    let n5 = g.part_len(cpi::PART_FIRST + cpi::PA_BRAND_DICT_OFFS);
    let n6 = g.part_len(cpi::PART_FIRST + cpi::PA_BRAND_DICT_BYTES);
    let bo = g.extent_u64(cpi::PART_FIRST + cpi::PA_BRAND_DICT_OFFS, 0, n5);
    let by = g.extent_u8(cpi::PART_FIRST + cpi::PA_BRAND_DICT_BYTES, 0, n6);
    let n7 = g.part_len(cpi::PART_FIRST + cpi::PA_CONTAINER_DICT_OFFS);
    let n8 = g.part_len(cpi::PART_FIRST + cpi::PA_CONTAINER_DICT_BYTES);
    let co = g.extent_u64(cpi::PART_FIRST + cpi::PA_CONTAINER_DICT_OFFS, 0, n7);
    let cy = g.extent_u8(cpi::PART_FIRST + cpi::PA_CONTAINER_DICT_BYTES, 0, n8);
    proof {
        assert(so@ =~= sd_o(fp));
        assert(sy@ =~= sd_y(fp));
        assert(mo@ =~= md_o(fp));
        assert(my@ =~= md_y(fp));
        assert(bo@ =~= bd_o(cp));
        assert(by@ =~= bd_y(cp));
        assert(co@ =~= cd_o(cp));
        assert(cy@ =~= cd_y(cp));
    }
    Dicts { so, sy, mo, my, bo, by, co, cy }
}

} // verus!
