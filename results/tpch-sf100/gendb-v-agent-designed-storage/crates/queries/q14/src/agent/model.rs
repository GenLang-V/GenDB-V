//! The stored parts as integer rows, and the column handles the scan reads.
//!
//! Lineitem (storage `facts`, clustered order): stored row `i` decodes to the four query columns
//! `[l_partkey, l_extendedprice, l_discount, l_shipdate]` (`li_rows`, exact integers: key, coefficients of scale 2,
//! days since 2000-01-01). Its uniform row groups carry one I64 base per column and an I64 shipdate maximum (zone
//! map); a row's value is its group's base plus its unsigned code.
//!
//! Part (storage `custpart`, canonical order): stored row `j` decodes to `[p_partkey, p_type]` (`pa_rows`); p_type is
//! a sorted dictionary entry whose index is a U64 base per group plus a U8 code.
//!
//! `LiCols` / `PaCols` are the whole extents the scan reads, with `li_cols_ok` / `pa_cols_ok` stating that they are
//! the parts' contents.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::custpart::interface::{PART_FIRST, PA_PARTS, PA_LAYOUT, PA_GROUPS, PA_PARTKEY_CODES,
    PA_PARTKEY_BASE, PA_TYPE_CODES, PA_TYPE_BASE, PA_TYPE_DICT_OFFS, PA_TYPE_DICT_BYTES, PA_KEYIDX_KIND,
    CUSTPART_PARTS};
use crate::stores::custpart::interface::common::colfmt as cpc;

verus! {

// ------------------------------------------------------------------------------------------------ lineitem rows

/// Number of stored lineitem rows.
pub open spec fn n_li(fp: Seq<PartView>) -> int {
    part_len(fp[LI_SHIPDATE_CODES as int]) as int
}

/// The lineitem row groups.
pub open spec fn li_gs(fp: Seq<PartView>) -> Seq<u64> {
    u64s(fp[LI_GROUPS as int])
}

pub open spec fn lpk_at(fp: Seq<PartView>, i: int) -> int {
    for_at(li_gs(fp), fp[LI_PARTKEY_BASE as int], fp[LI_PARTKEY_CODES as int], i)
}

pub open spec fn price_at(fp: Seq<PartView>, i: int) -> int {
    for_at(li_gs(fp), fp[LI_EXTENDEDPRICE_BASE as int], fp[LI_EXTENDEDPRICE_CODES as int], i)
}

pub open spec fn disc_at(fp: Seq<PartView>, i: int) -> int {
    for_at(li_gs(fp), fp[LI_DISCOUNT_BASE as int], fp[LI_DISCOUNT_CODES as int], i)
}

pub open spec fn ship_at(fp: Seq<PartView>, i: int) -> int {
    for_at(li_gs(fp), fp[LI_SHIPDATE_BASE as int], fp[LI_SHIPDATE_CODES as int], i)
}

/// A lineitem row of the four query columns.
pub open spec fn li_row(k: int, p: int, d: int, s: int) -> Row {
    seq![Val::Int(k), Val::Num { coeff: p, scale: 2 }, Val::Num { coeff: d, scale: 2 }, Val::Date(s)]
}

/// The query columns of every stored lineitem row, in stored order.
pub open spec fn li_rows(fp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_li(fp) as nat, |i: int| li_row(lpk_at(fp, i), price_at(fp, i), disc_at(fp, i), ship_at(fp, i)))
}

// ------------------------------------------------------------------------------------------------ part rows

/// Index of part `k` of table part in the custpart parts.
pub open spec fn pp(k: usize) -> int {
    (PART_FIRST + k) as int
}

/// Number of stored part rows.
pub open spec fn n_pa(cp: Seq<PartView>) -> int {
    part_len(cp[pp(PA_PARTKEY_CODES)]) as int
}

/// The part row groups.
pub open spec fn pa_gs(cp: Seq<PartView>) -> Seq<u64> {
    cpc::u64s(cp[pp(PA_GROUPS)])
}

/// Rows per part group (`[rows, block rows]` layout part).
pub open spec fn pa_bsize(cp: Seq<PartView>) -> int {
    cpc::u64s(cp[pp(PA_LAYOUT)])[1] as int
}

pub open spec fn pkey_at(cp: Seq<PartView>, j: int) -> int {
    cpc::for_at(pa_gs(cp), cp[pp(PA_PARTKEY_BASE)], cp[pp(PA_PARTKEY_CODES)], j)
}

/// Dictionary index of the p_type of stored part row `j`.
pub open spec fn tidx_at(cp: Seq<PartView>, j: int) -> int {
    cpc::for_at(pa_gs(cp), cp[pp(PA_TYPE_BASE)], cp[pp(PA_TYPE_CODES)], j)
}

pub open spec fn td_o(cp: Seq<PartView>) -> Seq<u64> {
    cpc::u64s(cp[pp(PA_TYPE_DICT_OFFS)])
}

pub open spec fn td_y(cp: Seq<PartView>) -> Seq<u8> {
    cpc::u8s(cp[pp(PA_TYPE_DICT_BYTES)])
}

/// Number of p_type dictionary entries.
pub open spec fn n_td(cp: Seq<PartView>) -> int {
    td_o(cp).len() - 1
}

/// Text of p_type dictionary entry `e`.
pub open spec fn tdict(cp: Seq<PartView>, e: int) -> Seq<u8> {
    cpc::text_of(td_o(cp), td_y(cp), e)
}

pub open spec fn ptype_at(cp: Seq<PartView>, j: int) -> Seq<u8> {
    tdict(cp, tidx_at(cp, j))
}

/// A part row of the two query columns.
pub open spec fn pa_row(k: int, t: Seq<u8>) -> Row {
    seq![Val::Int(k), Val::Text(t)]
}

/// The query columns of every stored part row, in stored (canonical) order.
pub open spec fn pa_rows(cp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_pa(cp) as nat, |j: int| pa_row(pkey_at(cp, j), ptype_at(cp, j)))
}

/// Part keys are `1, 2, ..., n` in stored order.
pub open spec fn dense(cp: Seq<PartView>) -> bool {
    forall|j: int| 0 <= j < n_pa(cp) ==> #[trigger] pkey_at(cp, j) == j + 1
}

// ------------------------------------------------------------------------------------------------ shape facts

/// `10^15`: the exclusive bound of a numeric(15, 2) coefficient.
pub open spec fn p15() -> int {
    1_000_000_000_000_000
}

/// An I64 part with one entry per lineitem group.
pub open spec fn li_group_part(fp: Seq<PartView>, k: int) -> bool {
    fp[k] is I64 && i64s(fp[k]).len() == li_gs(fp).len() - 1
}

/// The facts of the lineitem parts the scan relies on (consequences of `represents` and `db_wf`).
pub open spec fn li_shape(fp: Seq<PartView>) -> bool {
    let n = n_li(fp);
    &&& fp.len() == FACTS_PARTS
    &&& fp[LI_GROUPS as int] is U64
    &&& groups_wf(li_gs(fp), n)
    &&& fp[LI_SHIPDATE_CODES as int] is U16
    &&& fp[LI_PARTKEY_CODES as int] is U32 && part_len(fp[LI_PARTKEY_CODES as int]) == n
    &&& fp[LI_EXTENDEDPRICE_CODES as int] is U32 && part_len(fp[LI_EXTENDEDPRICE_CODES as int]) == n
    &&& fp[LI_DISCOUNT_CODES as int] is U8 && part_len(fp[LI_DISCOUNT_CODES as int]) == n
    &&& li_group_part(fp, LI_SHIPDATE_BASE as int)
    &&& li_group_part(fp, LI_SHIPDATE_ZMAX as int)
    &&& li_group_part(fp, LI_PARTKEY_BASE as int)
    &&& li_group_part(fp, LI_EXTENDEDPRICE_BASE as int)
    &&& li_group_part(fp, LI_DISCOUNT_BASE as int)
    &&& zone_max_ok(li_gs(fp), fp[LI_SHIPDATE_BASE as int], fp[LI_SHIPDATE_CODES as int], i64s(fp[LI_SHIPDATE_ZMAX as int]))
    &&& forall|i: int| 0 <= i < n ==> abs_lt(#[trigger] price_at(fp, i), p15())
    &&& forall|i: int| 0 <= i < n ==> abs_lt(#[trigger] disc_at(fp, i), p15())
}

/// `|x| < b`.
pub open spec fn abs_lt(x: int, b: int) -> bool {
    -b < x && x < b
}

/// The facts of the part parts the lookups rely on (consequences of `represents` and the primary key).
pub open spec fn pa_shape(cp: Seq<PartView>) -> bool {
    let n = n_pa(cp);
    &&& cp.len() == CUSTPART_PARTS
    &&& cp[pp(PA_LAYOUT)] is U64 && cpc::u64s(cp[pp(PA_LAYOUT)]).len() == 2
    &&& cpc::groups_part_ok(cp[pp(PA_GROUPS)], n, pa_bsize(cp))
    &&& cp[pp(PA_PARTKEY_CODES)] is U32
    &&& cp[pp(PA_PARTKEY_BASE)] is I64 && part_len(cp[pp(PA_PARTKEY_BASE)]) == pa_gs(cp).len() - 1
    &&& cp[pp(PA_TYPE_CODES)] is U8 && part_len(cp[pp(PA_TYPE_CODES)]) == n
    &&& cp[pp(PA_TYPE_BASE)] is U64 && part_len(cp[pp(PA_TYPE_BASE)]) == pa_gs(cp).len() - 1
    &&& cp[pp(PA_TYPE_DICT_OFFS)] is U64 && cp[pp(PA_TYPE_DICT_BYTES)] is U8
    &&& td_o(cp).len() >= 1
    &&& cpc::text_parts_wf(td_o(cp), td_y(cp), n_td(cp))
    &&& forall|j: int| 0 <= j < n ==> 0 <= #[trigger] tidx_at(cp, j) < n_td(cp)
    &&& cp[pp(PA_KEYIDX_KIND)] is U64 && cpc::u64s(cp[pp(PA_KEYIDX_KIND)]).len() == 1
    // stored rows sorted by key when the key index kind is 1
    &&& cpc::u64s(cp[pp(PA_KEYIDX_KIND)])[0] == 1 ==> forall|j: int| 0 <= j < n - 1 ==> #[trigger] pkey_at(cp, j) <= pkey_at(cp, j + 1)
    // p_partkey is the primary key
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] pkey_at(cp, a) != #[trigger] pkey_at(cp, b)
}

// ------------------------------------------------------------------------------------------------ column handles

/// The lineitem extents the scan reads (whole parts).
#[derive(Clone, Copy)]
pub struct LiCols {
    pub gs: &'static [u64],
    pub ship: &'static [u16],
    pub ship_base: &'static [i64],
    pub ship_zmax: &'static [i64],
    pub pk: &'static [u32],
    pub pk_base: &'static [i64],
    pub price: &'static [u32],
    pub price_base: &'static [i64],
    pub disc: &'static [u8],
    pub disc_base: &'static [i64],
    /// Number of groups.
    pub ng: usize,
    /// Number of rows.
    pub n: usize,
}

pub open spec fn li_cols_ok(c: LiCols, fp: Seq<PartView>) -> bool {
    &&& li_shape(fp)
    &&& c.n == n_li(fp)
    &&& c.ng + 1 == li_gs(fp).len()
    &&& c.gs@ == li_gs(fp)
    &&& c.ship@ == u16s_of(fp[LI_SHIPDATE_CODES as int])
    &&& c.pk@ == u32s(fp[LI_PARTKEY_CODES as int])
    &&& c.price@ == u32s(fp[LI_EXTENDEDPRICE_CODES as int])
    &&& c.disc@ == u8s(fp[LI_DISCOUNT_CODES as int])
    &&& c.ship_base@ == i64s(fp[LI_SHIPDATE_BASE as int])
    &&& c.ship_zmax@ == i64s(fp[LI_SHIPDATE_ZMAX as int])
    &&& c.pk_base@ == i64s(fp[LI_PARTKEY_BASE as int])
    &&& c.price_base@ == i64s(fp[LI_EXTENDEDPRICE_BASE as int])
    &&& c.disc_base@ == i64s(fp[LI_DISCOUNT_BASE as int])
}

/// The U16 codes of a part.
pub open spec fn u16s_of(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

/// The part extents the lookups read (whole parts).
#[derive(Clone, Copy)]
pub struct PaCols {
    pub pk: &'static [u32],
    pub pk_base: &'static [i64],
    pub ty: &'static [u8],
    pub ty_base: &'static [u64],
    pub d_offs: &'static [u64],
    pub d_bytes: &'static [u8],
    pub kind: u64,
    /// Rows per group.
    pub bsize: u64,
    /// Number of rows.
    pub n: usize,
}

pub open spec fn pa_cols_ok(c: PaCols, cp: Seq<PartView>) -> bool {
    &&& pa_shape(cp)
    &&& c.n == n_pa(cp)
    &&& c.bsize == pa_bsize(cp)
    &&& c.kind == cpc::u64s(cp[pp(PA_KEYIDX_KIND)])[0]
    &&& c.pk@ == cpc::u32s(cp[pp(PA_PARTKEY_CODES)])
    &&& c.pk_base@ == cpc::i64s(cp[pp(PA_PARTKEY_BASE)])
    &&& c.ty@ == cpc::u8s(cp[pp(PA_TYPE_CODES)])
    &&& c.ty_base@ == cpc::u64s(cp[pp(PA_TYPE_BASE)])
    &&& c.d_offs@ == td_o(cp)
    &&& c.d_bytes@ == td_y(cp)
}

/// The lineitem extents of the scan.
pub fn read_li(f: &mut StoredParts, Ghost(fp): Ghost<Seq<PartView>>) -> (c: LiCols)
    requires
        old(f)@ == fp,
        li_shape(fp),
    ensures
        final(f)@ == fp,
        li_cols_ok(c, fp),
{
    let n = f.part_len(LI_SHIPDATE_CODES);
    let ng1 = f.part_len(LI_GROUPS);
    proof {
        lemma_groups_bounds(li_gs(fp), n_li(fp), 0);
    }
    let ng = ng1 - 1;
    let gs = f.extent_u64(LI_GROUPS, 0, ng1);
    let ship_base = f.extent_i64(LI_SHIPDATE_BASE, 0, ng);
    let ship_zmax = f.extent_i64(LI_SHIPDATE_ZMAX, 0, ng);
    let pk_base = f.extent_i64(LI_PARTKEY_BASE, 0, ng);
    let price_base = f.extent_i64(LI_EXTENDEDPRICE_BASE, 0, ng);
    let disc_base = f.extent_i64(LI_DISCOUNT_BASE, 0, ng);
    let ship = f.extent_u16(LI_SHIPDATE_CODES, 0, n);
    let pk = f.extent_u32(LI_PARTKEY_CODES, 0, n);
    let price = f.extent_u32(LI_EXTENDEDPRICE_CODES, 0, n);
    let disc = f.extent_u8(LI_DISCOUNT_CODES, 0, n);
    let c = LiCols { gs, ship, ship_base, ship_zmax, pk, pk_base, price, price_base, disc, disc_base, ng, n };
    proof {
        assert(gs@ =~= li_gs(fp));
        assert(ship@ =~= u16s_of(fp[LI_SHIPDATE_CODES as int]));
        assert(pk@ =~= u32s(fp[LI_PARTKEY_CODES as int]));
        assert(price@ =~= u32s(fp[LI_EXTENDEDPRICE_CODES as int]));
        assert(disc@ =~= u8s(fp[LI_DISCOUNT_CODES as int]));
        assert(ship_base@ =~= i64s(fp[LI_SHIPDATE_BASE as int]));
        assert(ship_zmax@ =~= i64s(fp[LI_SHIPDATE_ZMAX as int]));
        assert(pk_base@ =~= i64s(fp[LI_PARTKEY_BASE as int]));
        assert(price_base@ =~= i64s(fp[LI_EXTENDEDPRICE_BASE as int]));
        assert(disc_base@ =~= i64s(fp[LI_DISCOUNT_BASE as int]));
    }
    c
}

/// The part extents of the lookups.
pub fn read_pa(f: &mut StoredParts, Ghost(cp): Ghost<Seq<PartView>>) -> (c: PaCols)
    requires
        old(f)@ == cp,
        pa_shape(cp),
    ensures
        final(f)@ == cp,
        pa_cols_ok(c, cp),
{
    let lay = f.extent_u64(PART_FIRST + PA_LAYOUT, 0, 2);
    let bsize = lay[1];
    let n = f.part_len(PART_FIRST + PA_PARTKEY_CODES);
    let ngp = f.part_len(PART_FIRST + PA_PARTKEY_BASE);
    let ngt = f.part_len(PART_FIRST + PA_TYPE_BASE);
    let pk = f.extent_u32(PART_FIRST + PA_PARTKEY_CODES, 0, n);
    let pk_base = f.extent_i64(PART_FIRST + PA_PARTKEY_BASE, 0, ngp);
    let ty = f.extent_u8(PART_FIRST + PA_TYPE_CODES, 0, n);
    let ty_base = f.extent_u64(PART_FIRST + PA_TYPE_BASE, 0, ngt);
    let no = f.part_len(PART_FIRST + PA_TYPE_DICT_OFFS);
    let nb = f.part_len(PART_FIRST + PA_TYPE_DICT_BYTES);
    let d_offs = f.extent_u64(PART_FIRST + PA_TYPE_DICT_OFFS, 0, no);
    let d_bytes = f.extent_u8(PART_FIRST + PA_TYPE_DICT_BYTES, 0, nb);
    let kv = f.extent_u64(PART_FIRST + PA_KEYIDX_KIND, 0, 1);
    let kind = kv[0];
    let c = PaCols { pk, pk_base, ty, ty_base, d_offs, d_bytes, kind, bsize, n };
    proof {
        assert(pk@ =~= cpc::u32s(cp[pp(PA_PARTKEY_CODES)]));
        assert(pk_base@ =~= cpc::i64s(cp[pp(PA_PARTKEY_BASE)]));
        assert(ty@ =~= cpc::u8s(cp[pp(PA_TYPE_CODES)]));
        assert(ty_base@ =~= cpc::u64s(cp[pp(PA_TYPE_BASE)]));
        assert(d_offs@ =~= td_o(cp));
        assert(d_bytes@ =~= td_y(cp));
    }
    c
}

} // verus!
