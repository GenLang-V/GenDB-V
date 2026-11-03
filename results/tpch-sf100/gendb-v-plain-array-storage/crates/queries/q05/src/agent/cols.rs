//! The stored columns Q5 reads, as whole-part slices (one extent per part; the host maps the parts lazily, so only
//! the pages the scans touch are read), and their relation to the model's columns (`cols_ok`).
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::TextCol;
use crate::agent::model::*;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;

verus! {

/// The columns Q5 reads, with their row counts.
pub struct Cols {
    pub nl: usize,
    pub lok: &'static [i64],
    pub lsk: &'static [i64],
    pub lext: &'static [i128],
    pub ldisc: &'static [i128],
    pub no: usize,
    pub ook: &'static [i64],
    pub ock: &'static [i64],
    pub odate: &'static [i32],
    pub nc: usize,
    pub ckeys: &'static [i64],
    pub cnk: &'static [i64],
    pub ns: usize,
    pub skeys: &'static [i64],
    pub snk: &'static [i64],
    pub nn: usize,
    pub nkeys: &'static [i64],
    pub nrk: &'static [i64],
    pub nname: TextCol,
    pub nr: usize,
    pub rkeys: &'static [i64],
    pub rname: TextCol,
}

/// The slices are the stored columns of `sv`.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.nl == nl(sv) && c.no == no(sv) && c.nc == nc(sv) && c.ns == ns(sv) && c.nn == nn(sv) && c.nr == nr(sv)
    &&& c.lok@ == l_ok(sv) && c.lsk@ == l_sk(sv) && c.lext@ == l_ext(sv) && c.ldisc@ == l_disc(sv)
    &&& c.ook@ == o_ok(sv) && c.ock@ == o_ck(sv) && c.odate@ == o_date(sv)
    &&& c.ckeys@ == c_ck(sv) && c.cnk@ == c_nk(sv)
    &&& c.skeys@ == s_sk(sv) && c.snk@ == s_nk(sv)
    &&& c.nkeys@ == n_nk(sv) && c.nrk@ == n_rk(sv) && c.nname@ == n_name_view(sv)
    &&& c.rkeys@ == r_rk(sv) && c.rname@ == r_name_view(sv)
    &&& c.lok@.len() == c.nl && c.lsk@.len() == c.nl && c.lext@.len() == c.nl && c.ldisc@.len() == c.nl
    &&& c.ook@.len() == c.no && c.ock@.len() == c.no && c.odate@.len() == c.no
    &&& c.ckeys@.len() == c.nc && c.cnk@.len() == c.nc
    &&& c.skeys@.len() == c.ns && c.snk@.len() == c.ns
    &&& c.nkeys@.len() == c.nn && c.nrk@.len() == c.nn
    &&& c.rkeys@.len() == c.nr
}

/// A copy of the column handles.
pub fn copy_cols(c: &Cols) -> (r: Cols)
    ensures r == *c,
{
    Cols {
        nl: c.nl, lok: c.lok, lsk: c.lsk, lext: c.lext, ldisc: c.ldisc,
        no: c.no, ook: c.ook, ock: c.ock, odate: c.odate,
        nc: c.nc, ckeys: c.ckeys, cnk: c.cnk,
        ns: c.ns, skeys: c.skeys, snk: c.snk,
        nn: c.nn, nkeys: c.nkeys, nrk: c.nrk, nname: TextCol { offsets: c.nname.offsets, bytes: c.nname.bytes },
        nr: c.nr, rkeys: c.rkeys, rname: TextCol { offsets: c.rname.offsets, bytes: c.rname.bytes },
    }
}

/// Reads every column Q5 uses as one extent per part.
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires old(stores)@ == sv, stores_wf(sv),
    ensures final(stores)@ == sv, cols_ok(c, sv),
{
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let lok = stores.flat_lineitem.extent_i64(li::L_ORDERKEY, 0, nl);
    let lsk = stores.flat_lineitem.extent_i64(li::L_SUPPKEY, 0, nl);
    let lext = stores.flat_lineitem.extent_i128(li::L_EXTENDEDPRICE, 0, nl);
    let ldisc = stores.flat_lineitem.extent_i128(li::L_DISCOUNT, 0, nl);
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let ook = stores.flat_orders.extent_i64(oi::O_ORDERKEY, 0, no);
    let ock = stores.flat_orders.extent_i64(oi::O_CUSTKEY, 0, no);
    let odate = stores.flat_orders.extent_i32(oi::O_ORDERDATE, 0, no);
    let nc = stores.flat_customer.part_len(ci::C_CUSTKEY);
    let ckeys = stores.flat_customer.extent_i64(ci::C_CUSTKEY, 0, nc);
    let cnk = stores.flat_customer.extent_i64(ci::C_NATIONKEY, 0, nc);
    let ns = stores.flat_supplier.part_len(si::S_SUPPKEY);
    let skeys = stores.flat_supplier.extent_i64(si::S_SUPPKEY, 0, ns);
    let snk = stores.flat_supplier.extent_i64(si::S_NATIONKEY, 0, ns);
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    let nkeys = stores.flat_nation.extent_i64(ni::N_NATIONKEY, 0, nn);
    let nrk = stores.flat_nation.extent_i64(ni::N_REGIONKEY, 0, nn);
    let nol = stores.flat_nation.part_len(ni::N_NAME_OFFSETS);
    let noff = stores.flat_nation.extent_i64(ni::N_NAME_OFFSETS, 0, nol);
    let nbl = stores.flat_nation.part_len(ni::N_NAME_BYTES);
    let nbytes = stores.flat_nation.extent_u8(ni::N_NAME_BYTES, 0, nbl);
    let nr = stores.flat_region.part_len(ri::R_REGIONKEY);
    let rkeys = stores.flat_region.extent_i64(ri::R_REGIONKEY, 0, nr);
    let rol = stores.flat_region.part_len(ri::R_NAME_OFFSETS);
    let roff = stores.flat_region.extent_i64(ri::R_NAME_OFFSETS, 0, rol);
    let rbl = stores.flat_region.part_len(ri::R_NAME_BYTES);
    let rbytes = stores.flat_region.extent_u8(ri::R_NAME_BYTES, 0, rbl);
    let c = Cols {
        nl, lok, lsk, lext, ldisc, no, ook, ock, odate, nc, ckeys, cnk, ns, skeys, snk,
        nn, nkeys, nrk, nname: TextCol { offsets: noff, bytes: nbytes },
        nr, rkeys, rname: TextCol { offsets: roff, bytes: rbytes },
    };
    proof {
        assert(lok@ =~= l_ok(sv));
        assert(lsk@ =~= l_sk(sv));
        assert(lext@ =~= l_ext(sv));
        assert(ldisc@ =~= l_disc(sv));
        assert(ook@ =~= o_ok(sv));
        assert(ock@ =~= o_ck(sv));
        assert(odate@ =~= o_date(sv));
        assert(ckeys@ =~= c_ck(sv));
        assert(cnk@ =~= c_nk(sv));
        assert(skeys@ =~= s_sk(sv));
        assert(snk@ =~= s_nk(sv));
        assert(nkeys@ =~= n_nk(sv));
        assert(nrk@ =~= n_rk(sv));
        assert(rkeys@ =~= r_rk(sv));
        assert(noff@ =~= n_name_view(sv).offsets);
        assert(nbytes@ =~= n_name_view(sv).bytes);
        assert(roff@ =~= r_name_view(sv).offsets);
        assert(rbytes@ =~= r_name_view(sv).bytes);
    }
    c
}

} // verus!
