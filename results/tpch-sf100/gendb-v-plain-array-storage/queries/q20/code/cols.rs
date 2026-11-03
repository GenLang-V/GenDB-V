//! The stored columns the query reads, as whole extents of their parts (`read_cols`; nothing is copied): lineitem
//! `l_partkey`, `l_suppkey`, `l_shipdate`, `l_quantity`; part `p_partkey`, `p_name`; partsupp `ps_partkey`,
//! `ps_suppkey`, `ps_availqty`; supplier `s_suppkey`, `s_nationkey`, `s_name`, `s_address`; nation `n_nationkey`,
//! `n_name`. A text column is its offsets and bytes parts (`Text`); value `i` is `bytes[offs[i] .. offs[i + 1]]`.
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::{text_wf, text_at, TextView};
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::agent::tables::*;

verus! {

/// A stored text column: offsets (`rows + 1`) and bytes (`blen` of them).
#[derive(Clone, Copy)]
pub struct Text {
    pub offs: &'static [i64],
    pub bytes: &'static [u8],
    pub blen: usize,
}

/// `t` is the text column `tv` of `n` rows.
pub open spec fn text_ok(t: Text, tv: TextView, n: int) -> bool {
    &&& t.offs@ == tv.offsets && t.bytes@ == tv.bytes && t.blen == t.bytes@.len()
    &&& text_wf(tv, n)
}

/// The byte range of value `i` of a text column.
pub fn text_range(t: Text, i: usize, Ghost(tv): Ghost<TextView>, Ghost(n): Ghost<int>) -> (r: (usize, usize))
    requires text_ok(t, tv, n), i < n,
    ensures
        r.0 <= r.1 <= t.blen, t.bytes@.subrange(r.0 as int, r.1 as int) == text_at(tv, i as int),
        r.0 as int == tv.offsets[i as int], r.1 as int == tv.offsets[i + 1],
    no_unwind
{
    let s = t.offs[i];
    let e = t.offs[i + 1];
    assert(0 <= s <= e <= t.bytes@.len());
    (s as usize, e as usize)
}

/// The columns the query reads.
pub struct Cols {
    pub nl: usize,
    pub lpk: &'static [i64],
    pub lsk: &'static [i64],
    pub lsd: &'static [i32],
    pub lqt: &'static [i128],
    pub np: usize,
    pub pkey: &'static [i64],
    pub pname: Text,
    pub nps: usize,
    pub pspk: &'static [i64],
    pub pssk: &'static [i64],
    pub psaq: &'static [i64],
    pub ns: usize,
    pub skey: &'static [i64],
    pub snk: &'static [i64],
    pub sname: Text,
    pub saddr: Text,
    pub nn: usize,
    pub nkey: &'static [i64],
    pub nname: Text,
}

/// The handles are the stored columns of `sv`.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.nl as int == n_l(sv) && c.lpk@ == lpk(sv) && c.lsk@ == lsk(sv) && c.lsd@ == lsd(sv) && c.lqt@ == lqt(sv)
    &&& c.lpk@.len() == n_l(sv) && c.lsk@.len() == n_l(sv) && c.lsd@.len() == n_l(sv) && c.lqt@.len() == n_l(sv)
    &&& c.np as int == n_p(sv) && c.pkey@ == pk(sv) && text_ok(c.pname, pname_col(sv), n_p(sv) as int)
    &&& c.nps as int == n_ps(sv) && c.pspk@ == pspk(sv) && c.pssk@ == pssk(sv) && c.psaq@ == psaq(sv)
    &&& c.pssk@.len() == n_ps(sv) && c.psaq@.len() == n_ps(sv)
    &&& c.ns as int == n_s(sv) && c.skey@ == sk(sv) && c.snk@ == snk(sv) && c.snk@.len() == n_s(sv)
    &&& text_ok(c.sname, sname_col(sv), n_s(sv) as int) && text_ok(c.saddr, saddr_col(sv), n_s(sv) as int)
    &&& c.nn as int == n_n(sv) && c.nkey@ == nk(sv) && text_ok(c.nname, nname_col(sv), n_n(sv) as int)
}

/// Read every column the query needs (one extent per part, the whole part).
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires old(stores)@ == sv, stores_wf(sv),
    ensures final(stores)@ == sv, cols_ok(c, sv),
{
    proof {
        assert(li::parts_wf(sv.flat_lineitem, n_l(sv) as int));
        assert(pi::parts_wf(sv.flat_part, n_p(sv) as int));
        assert(psi::parts_wf(sv.flat_partsupp, n_ps(sv) as int));
        assert(si::parts_wf(sv.flat_supplier, n_s(sv) as int));
        assert(ni::parts_wf(sv.flat_nation, n_n(sv) as int));
    }
    // lineitem
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let lpk = stores.flat_lineitem.extent_i64(li::L_PARTKEY, 0, nl);
    let lsk = stores.flat_lineitem.extent_i64(li::L_SUPPKEY, 0, nl);
    let lsd = stores.flat_lineitem.extent_i32(li::L_SHIPDATE, 0, nl);
    let lqt = stores.flat_lineitem.extent_i128(li::L_QUANTITY, 0, nl);
    proof { assert(lpk@ =~= crate::agent::tables::lpk(sv) && lsk@ =~= crate::agent::tables::lsk(sv) && lsd@ =~= crate::agent::tables::lsd(sv) && lqt@ =~= crate::agent::tables::lqt(sv)); }
    // part
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let pkey = stores.flat_part.extent_i64(pi::P_PARTKEY, 0, np);
    let po = stores.flat_part.part_len(pi::P_NAME_OFFSETS);
    let pb = stores.flat_part.part_len(pi::P_NAME_BYTES);
    let poffs = stores.flat_part.extent_i64(pi::P_NAME_OFFSETS, 0, po);
    let pbytes = stores.flat_part.extent_u8(pi::P_NAME_BYTES, 0, pb);
    proof { assert(pkey@ =~= pk(sv) && poffs@ =~= pname_col(sv).offsets && pbytes@ =~= pname_col(sv).bytes); }
    // partsupp
    let nps = stores.flat_partsupp.part_len(psi::PS_PARTKEY);
    let pspk = stores.flat_partsupp.extent_i64(psi::PS_PARTKEY, 0, nps);
    let pssk = stores.flat_partsupp.extent_i64(psi::PS_SUPPKEY, 0, nps);
    let psaq = stores.flat_partsupp.extent_i64(psi::PS_AVAILQTY, 0, nps);
    proof { assert(pspk@ =~= crate::agent::tables::pspk(sv) && pssk@ =~= crate::agent::tables::pssk(sv) && psaq@ =~= crate::agent::tables::psaq(sv)); }
    // supplier
    let ns = stores.flat_supplier.part_len(si::S_SUPPKEY);
    let skey = stores.flat_supplier.extent_i64(si::S_SUPPKEY, 0, ns);
    let snk = stores.flat_supplier.extent_i64(si::S_NATIONKEY, 0, ns);
    let sno = stores.flat_supplier.part_len(si::S_NAME_OFFSETS);
    let snb = stores.flat_supplier.part_len(si::S_NAME_BYTES);
    let snoffs = stores.flat_supplier.extent_i64(si::S_NAME_OFFSETS, 0, sno);
    let snbytes = stores.flat_supplier.extent_u8(si::S_NAME_BYTES, 0, snb);
    let sao = stores.flat_supplier.part_len(si::S_ADDRESS_OFFSETS);
    let sab = stores.flat_supplier.part_len(si::S_ADDRESS_BYTES);
    let saoffs = stores.flat_supplier.extent_i64(si::S_ADDRESS_OFFSETS, 0, sao);
    let sabytes = stores.flat_supplier.extent_u8(si::S_ADDRESS_BYTES, 0, sab);
    proof {
        assert(skey@ =~= sk(sv) && snk@ =~= crate::agent::tables::snk(sv));
        assert(snoffs@ =~= sname_col(sv).offsets && snbytes@ =~= sname_col(sv).bytes);
        assert(saoffs@ =~= saddr_col(sv).offsets && sabytes@ =~= saddr_col(sv).bytes);
    }
    // nation
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    let nkey = stores.flat_nation.extent_i64(ni::N_NATIONKEY, 0, nn);
    let nno = stores.flat_nation.part_len(ni::N_NAME_OFFSETS);
    let nnb = stores.flat_nation.part_len(ni::N_NAME_BYTES);
    let nnoffs = stores.flat_nation.extent_i64(ni::N_NAME_OFFSETS, 0, nno);
    let nnbytes = stores.flat_nation.extent_u8(ni::N_NAME_BYTES, 0, nnb);
    proof { assert(nkey@ =~= nk(sv) && nnoffs@ =~= nname_col(sv).offsets && nnbytes@ =~= nname_col(sv).bytes); }
    Cols {
        nl, lpk, lsk, lsd, lqt,
        np, pkey, pname: Text { offs: poffs, bytes: pbytes, blen: pb },
        nps, pspk, pssk, psaq,
        ns, skey, snk, sname: Text { offs: snoffs, bytes: snbytes, blen: snb }, saddr: Text { offs: saoffs, bytes: sabytes, blen: sab },
        nn, nkey, nname: Text { offs: nnoffs, bytes: nnbytes, blen: nnb },
    }
}

} // verus!
