//! The extents the query reads, requested on the calling thread (whole parts): part columns and dictionaries
//! (`read_pa`), lineitem columns (`read_li_base`) and, in index mode, the directory, rows and quantity keys of
//! li_pkqty's (l_partkey, l_quantity) index (`read_li_dir`). part_bcs's extents are read by `ixscan::read_pidx`.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::stores::li_pkqty::interface as LI;
use crate::stores::custpart::interface as CPI;
use crate::stores::custpart::interface::common::colfmt as CF;
use super::bind::*;
use super::lookup::{LiCols, li_cols_ok};
use super::scan::{PaCols, pa_cols_ok};
use super::general::{LiBase, li_base_ok};

verus! {

/// The part dictionaries of p_brand and p_container (offsets, bytes).
pub struct Dicts {
    pub bo: &'static [u64],
    pub by: &'static [u8],
    pub co: &'static [u64],
    pub cy: &'static [u8],
}

pub open spec fn dicts_ok(d: Dicts, cp: Seq<PartView>) -> bool {
    &&& d.bo@ == bd_o(cp)
    &&& d.by@ == bd_y(cp)
    &&& d.co@ == cd_o(cp)
    &&& d.cy@ == cd_y(cp)
}

/// The part extents.
pub fn read_pa(f: &mut StoredParts, Ghost(cp): Ghost<Seq<PartView>>) -> (r: (PaCols, Dicts))
    requires old(f)@ == cp, pa_facts(cp),
    ensures final(f)@ == cp, pa_cols_ok(r.0, cp), dicts_ok(r.1, cp),
{
    let lay = f.extent_u64(CPI::PART_FIRST + CPI::PA_LAYOUT, 0, 2);
    let bs = lay[1];
    let n = f.part_len(CPI::PART_FIRST + CPI::PA_PARTKEY_CODES);
    let npk = f.part_len(CPI::PART_FIRST + CPI::PA_PARTKEY_BASE);
    let nbb = f.part_len(CPI::PART_FIRST + CPI::PA_BRAND_BASE);
    let ncb = f.part_len(CPI::PART_FIRST + CPI::PA_CONTAINER_BASE);
    let pk = f.extent_u32(CPI::PART_FIRST + CPI::PA_PARTKEY_CODES, 0, n);
    let pkb = f.extent_i64(CPI::PART_FIRST + CPI::PA_PARTKEY_BASE, 0, npk);
    let br = f.extent_u8(CPI::PART_FIRST + CPI::PA_BRAND_CODES, 0, n);
    let brb = f.extent_u64(CPI::PART_FIRST + CPI::PA_BRAND_BASE, 0, nbb);
    let ct = f.extent_u8(CPI::PART_FIRST + CPI::PA_CONTAINER_CODES, 0, n);
    let ctb = f.extent_u64(CPI::PART_FIRST + CPI::PA_CONTAINER_BASE, 0, ncb);
    let nbo = f.part_len(CPI::PART_FIRST + CPI::PA_BRAND_DICT_OFFS);
    let nby = f.part_len(CPI::PART_FIRST + CPI::PA_BRAND_DICT_BYTES);
    let nco = f.part_len(CPI::PART_FIRST + CPI::PA_CONTAINER_DICT_OFFS);
    let ncy = f.part_len(CPI::PART_FIRST + CPI::PA_CONTAINER_DICT_BYTES);
    let bo = f.extent_u64(CPI::PART_FIRST + CPI::PA_BRAND_DICT_OFFS, 0, nbo);
    let by = f.extent_u8(CPI::PART_FIRST + CPI::PA_BRAND_DICT_BYTES, 0, nby);
    let co = f.extent_u64(CPI::PART_FIRST + CPI::PA_CONTAINER_DICT_OFFS, 0, nco);
    let cy = f.extent_u8(CPI::PART_FIRST + CPI::PA_CONTAINER_DICT_BYTES, 0, ncy);
    let pa = PaCols { n, bs, pk, pkb, br, brb, ct, ctb };
    let d = Dicts { bo, by, co, cy };
    proof {
        assert(pk@ =~= CF::u32s(cp[pp(CPI::PA_PARTKEY_CODES)]));
        assert(pkb@ =~= CF::i64s(cp[pp(CPI::PA_PARTKEY_BASE)]));
        assert(br@ =~= CF::u8s(cp[pp(CPI::PA_BRAND_CODES)]));
        assert(brb@ =~= CF::u64s(cp[pp(CPI::PA_BRAND_BASE)]));
        assert(ct@ =~= CF::u8s(cp[pp(CPI::PA_CONTAINER_CODES)]));
        assert(ctb@ =~= CF::u64s(cp[pp(CPI::PA_CONTAINER_BASE)]));
        assert(bo@ =~= bd_o(cp));
        assert(by@ =~= bd_y(cp));
        assert(co@ =~= cd_o(cp));
        assert(cy@ =~= cd_y(cp));
    }
    (pa, d)
}

/// The lineitem column extents (stored order).
pub fn read_li_base(f: &mut StoredParts, Ghost(lp): Ghost<Seq<PartView>>) -> (c: LiBase)
    requires old(f)@ == lp, li_facts(lp),
    ensures final(f)@ == lp, li_base_ok(c, lp),
{
    let lay = f.extent_u64(LI::LI_LAYOUT, 0, 2);
    let bs = lay[1];
    let n = f.part_len(LI::LI_QUANTITY_CODES);
    let nkb = f.part_len(LI::LI_PARTKEY_BASE);
    let nqb = f.part_len(LI::LI_QUANTITY_BASE);
    let nxb = f.part_len(LI::LI_EXTENDEDPRICE_BASE);
    let kc = f.extent_u32(LI::LI_PARTKEY_CODES, 0, n);
    let kb = f.extent_i64(LI::LI_PARTKEY_BASE, 0, nkb);
    let qc = f.extent_u16(LI::LI_QUANTITY_CODES, 0, n);
    let qb = f.extent_i64(LI::LI_QUANTITY_BASE, 0, nqb);
    let xc = f.extent_u32(LI::LI_EXTENDEDPRICE_CODES, 0, n);
    let xb = f.extent_i64(LI::LI_EXTENDEDPRICE_BASE, 0, nxb);
    let c = LiBase { n, bs, kc, kb, qc, qb, xc, xb };
    proof {
        assert(kc@ =~= LI::u32s(lp[LI::LI_PARTKEY_CODES as int]));
        assert(kb@ =~= LI::i64s(lp[LI::LI_PARTKEY_BASE as int]));
        assert(qc@ =~= LI::u16s(lp[LI::LI_QUANTITY_CODES as int]));
        assert(qb@ =~= LI::i64s(lp[LI::LI_QUANTITY_BASE as int]));
        assert(xc@ =~= LI::u32s(lp[LI::LI_EXTENDEDPRICE_CODES as int]));
        assert(xb@ =~= LI::i64s(lp[LI::LI_EXTENDEDPRICE_BASE as int]));
    }
    c
}

/// In index mode (with blocks of 65536 rows), the extents of the lookups: the composite index's directory, rows and
/// quantity keys.
pub fn read_li_dir(f: &mut StoredParts, base: &LiBase, Ghost(lp): Ghost<Seq<PartView>>) -> (r: Option<LiCols>)
    requires old(f)@ == lp, li_facts(lp), li_base_ok(*base, lp),
    ensures
        final(f)@ == lp,
        r matches Some(c) ==> li_cols_ok(c, lp),
{
    let meta = f.extent_i64(LI::IDX_META, 0, 3);
    if meta[0] != LI::MODE_INDEX || base.bs != 65536 {
        return None;
    }
    let kmin = meta[1];
    let qbase = meta[2];
    let n = base.n;
    let no = f.part_len(LI::IDX_OFFS);
    let rows = f.extent_u32(LI::IDX_ROWS, 0, n);
    let qk = f.extent_u16(LI::IDX_QKEYS, 0, n);
    let offs = f.extent_u32(LI::IDX_OFFS, 0, no);
    let c = LiCols { n, rows, qk, qbase, xc: base.xc, xb: base.xb, kmin, nk: no - 1, offs };
    proof {
        assert(LI::has_idx(lp));
        assert(rows@ =~= LI::idx_rows(lp));
        assert(qk@ =~= LI::idx_qkeys(lp));
        assert(offs@ =~= LI::idx_offs(lp));
    }
    Some(c)
}

} // verus!
