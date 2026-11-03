//! The columns the query reads, as whole parts (one extent request per part): `sub.adsh, name, fy`,
//! `pre.adsh, stmt, tag, version, plabel` and `num.adsh, tag, version, uom, value`.
use vstd::prelude::*;
use crate::gendb_entry::stores::Stores;
use crate::link::query::TextCol;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_pre::interface as pi;
use crate::agent::ctx::*;

verus! {

pub struct Cols {
    pub sadsh: TextCol,
    pub sname: TextCol,
    pub sfy: &'static [i32],
    pub sfyv: &'static [u8],
    pub padsh: TextCol,
    pub pstmt: TextCol,
    pub pstmtv: &'static [u8],
    pub ptag: TextCol,
    pub pver: TextCol,
    pub plabel: TextCol,
    pub plabelv: &'static [u8],
    pub nadsh: TextCol,
    pub ntag: TextCol,
    pub nver: TextCol,
    pub nuom: TextCol,
    pub nval: &'static [i128],
}

pub open spec fn cols_ok(k: Cols, c: Ctx) -> bool {
    &&& k.sadsh@ == s_adsh_v(c)
    &&& k.sname@ == s_name_v(c)
    &&& k.sfy@ == s_fy_s(c)
    &&& k.sfyv@ == s_fyv_s(c)
    &&& k.padsh@ == p_adsh_v(c)
    &&& k.pstmt@ == p_stmt_v(c)
    &&& k.pstmtv@ == p_stmtv_s(c)
    &&& k.ptag@ == p_tag_v(c)
    &&& k.pver@ == p_ver_v(c)
    &&& k.plabel@ == p_plabel_v(c)
    &&& k.plabelv@ == p_plabelv_s(c)
    &&& k.nadsh@ == n_adsh_v(c)
    &&& k.ntag@ == n_tag_v(c)
    &&& k.nver@ == n_ver_v(c)
    &&& k.nuom@ == n_uom_v(c)
    &&& k.nval@ == n_val_s(c)
}

/// One whole text column (offsets and bytes parts) of a storage.
fn text_col(s: &mut crate::gendb_entry::stored::StoredParts, po: usize, pb: usize) -> (t: TextCol)
    requires po < old(s)@.len(), pb < old(s)@.len(), old(s)@[po as int] is I64, old(s)@[pb as int] is U8,
    ensures
        final(s)@ == old(s)@,
        t.offsets@ == ni::i64s(old(s)@[po as int]),
        t.bytes@ == ni::u8s(old(s)@[pb as int]),
{
    let lo = s.part_len(po);
    let off = s.extent_i64(po, 0, lo);
    let lb = s.part_len(pb);
    let bytes = s.extent_u8(pb, 0, lb);
    proof {
        assert(off@ =~= ni::i64s(old(s)@[po as int]));
        assert(bytes@ =~= ni::u8s(old(s)@[pb as int]));
    }
    TextCol { offsets: off, bytes }
}

/// Read every column the query uses.
pub fn read_cols(stores: &mut Stores, Ghost(c): Ghost<Ctx>) -> (k: Cols)
    requires
        ctx_ok(c),
        c.np == old(stores)@.flat_num,
        c.sp == old(stores)@.flat_sub,
        c.pp == old(stores)@.flat_pre,
    ensures
        final(stores)@ == old(stores)@,
        cols_ok(k, c),
{
    proof {
        reveal(ctx_ok);
    }
    let sadsh = text_col(&mut stores.flat_sub, si::ADSH_OFFSETS, si::ADSH_BYTES);
    let sname = text_col(&mut stores.flat_sub, si::NAME_OFFSETS, si::NAME_BYTES);
    let l = stores.flat_sub.part_len(si::FY);
    let sfy = stores.flat_sub.extent_i32(si::FY, 0, l);
    let l = stores.flat_sub.part_len(si::FY_VALIDITY);
    let sfyv = stores.flat_sub.extent_u8(si::FY_VALIDITY, 0, l);
    let padsh = text_col(&mut stores.flat_pre, pi::ADSH_OFFSETS, pi::ADSH_BYTES);
    let pstmt = text_col(&mut stores.flat_pre, pi::STMT_OFFSETS, pi::STMT_BYTES);
    let l = stores.flat_pre.part_len(pi::STMT_VALIDITY);
    let pstmtv = stores.flat_pre.extent_u8(pi::STMT_VALIDITY, 0, l);
    let ptag = text_col(&mut stores.flat_pre, pi::TAG_OFFSETS, pi::TAG_BYTES);
    let pver = text_col(&mut stores.flat_pre, pi::VERSION_OFFSETS, pi::VERSION_BYTES);
    let plabel = text_col(&mut stores.flat_pre, pi::PLABEL_OFFSETS, pi::PLABEL_BYTES);
    let l = stores.flat_pre.part_len(pi::PLABEL_VALIDITY);
    let plabelv = stores.flat_pre.extent_u8(pi::PLABEL_VALIDITY, 0, l);
    let nadsh = text_col(&mut stores.flat_num, ni::ADSH_OFFSETS, ni::ADSH_BYTES);
    let ntag = text_col(&mut stores.flat_num, ni::TAG_OFFSETS, ni::TAG_BYTES);
    let nver = text_col(&mut stores.flat_num, ni::VERSION_OFFSETS, ni::VERSION_BYTES);
    let nuom = text_col(&mut stores.flat_num, ni::UOM_OFFSETS, ni::UOM_BYTES);
    let l = stores.flat_num.part_len(ni::VALUE);
    let nval = stores.flat_num.extent_i128(ni::VALUE, 0, l);
    proof {
        assert(sfy@ =~= s_fy_s(c));
        assert(sfyv@ =~= s_fyv_s(c));
        assert(pstmtv@ =~= p_stmtv_s(c));
        assert(plabelv@ =~= p_plabelv_s(c));
        assert(nval@ =~= n_val_s(c));
        assert(sadsh@ =~= s_adsh_v(c));
        assert(sname@ =~= s_name_v(c));
        assert(padsh@ =~= p_adsh_v(c));
        assert(pstmt@ =~= p_stmt_v(c));
        assert(ptag@ =~= p_tag_v(c));
        assert(pver@ =~= p_ver_v(c));
        assert(plabel@ =~= p_plabel_v(c));
        assert(nadsh@ =~= n_adsh_v(c));
        assert(ntag@ =~= n_tag_v(c));
        assert(nver@ =~= n_ver_v(c));
        assert(nuom@ =~= n_uom_v(c));
    }
    Cols { sadsh, sname, sfy, sfyv, padsh, pstmt, pstmtv, ptag, pver, plabel, plabelv, nadsh, ntag, nver, nuom, nval }
}

} // verus!
