//! The stored columns the query reads, as `&'static` slices (whole parts, requested once on the calling thread),
//! and their correspondence with the model's column views (`cols_ok`).
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::{text_wf, TextView};
use crate::agent::tables::*;
use crate::agent::common::text::tview;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;

verus! {

/// The columns, with their row counts (and byte counts of the text columns' bytes parts).
#[derive(Clone, Copy)]
pub struct Cols {
    pub l_ok: &'static [i64],
    pub l_pk: &'static [i64],
    pub l_sk: &'static [i64],
    pub l_price: &'static [i128],
    pub l_disc: &'static [i128],
    pub nl: usize,
    pub o_key: &'static [i64],
    pub o_cust: &'static [i64],
    pub o_date: &'static [i32],
    pub no: usize,
    pub c_key: &'static [i64],
    pub c_nat: &'static [i64],
    pub nc: usize,
    pub p_key: &'static [i64],
    pub p_toffs: &'static [i64],
    pub p_tbytes: &'static [u8],
    pub p_tnb: usize,
    pub np: usize,
    pub s_key: &'static [i64],
    pub s_nat: &'static [i64],
    pub ns: usize,
    pub n_key: &'static [i64],
    pub n_reg: &'static [i64],
    pub n_noffs: &'static [i64],
    pub n_nbytes: &'static [u8],
    pub n_nnb: usize,
    pub nn: usize,
    pub r_key: &'static [i64],
    pub r_noffs: &'static [i64],
    pub r_nbytes: &'static [u8],
    pub r_nnb: usize,
    pub nr: usize,
}

/// The `p_type`, `n_name` and `r_name` text columns.
pub open spec fn ptype_col(sv: StoresView) -> TextView { pi::text_view(sv.flat_part, pi::P_TYPE_OFFSETS as int, pi::P_TYPE_BYTES as int) }
pub open spec fn nname_col(sv: StoresView) -> TextView { ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int) }
pub open spec fn rname_col(sv: StoresView) -> TextView { ri::text_view(sv.flat_region, ri::R_NAME_OFFSETS as int, ri::R_NAME_BYTES as int) }

/// The slices are the stored columns, every column has its table's row count, and the text columns are well formed.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.l_ok@ == l_okey(sv) && c.l_pk@ == l_pkey(sv) && c.l_sk@ == l_skey(sv)
    &&& c.l_price@ == l_price(sv) && c.l_disc@ == l_disc(sv)
    &&& c.nl == n_l(sv) && l_pkey(sv).len() == n_l(sv) && l_skey(sv).len() == n_l(sv)
    &&& l_price(sv).len() == n_l(sv) && l_disc(sv).len() == n_l(sv)
    &&& c.o_key@ == o_key(sv) && c.o_cust@ == o_cust(sv) && c.o_date@ == o_date(sv)
    &&& c.no == n_o(sv) && o_cust(sv).len() == n_o(sv) && o_date(sv).len() == n_o(sv)
    &&& c.c_key@ == c_key(sv) && c.c_nat@ == c_nat(sv) && c.nc == n_c(sv) && c_nat(sv).len() == n_c(sv)
    &&& c.p_key@ == p_key(sv) && c.np == n_p(sv)
    &&& tview(c.p_toffs@, c.p_tbytes@) == ptype_col(sv) && text_wf(ptype_col(sv), n_p(sv) as int) && c.p_tnb == c.p_tbytes@.len()
    &&& c.s_key@ == s_key(sv) && c.s_nat@ == s_nat(sv) && c.ns == n_s(sv) && s_nat(sv).len() == n_s(sv)
    &&& c.n_key@ == n_key(sv) && c.n_reg@ == n_reg(sv) && c.nn == n_n(sv) && n_reg(sv).len() == n_n(sv)
    &&& tview(c.n_noffs@, c.n_nbytes@) == nname_col(sv) && text_wf(nname_col(sv), n_n(sv) as int) && c.n_nnb == c.n_nbytes@.len()
    &&& c.r_key@ == r_key(sv) && c.nr == n_r(sv)
    &&& tview(c.r_noffs@, c.r_nbytes@) == rname_col(sv) && text_wf(rname_col(sv), n_r(sv) as int) && c.r_nnb == c.r_nbytes@.len()
}

/// Request the columns (whole parts) from the stores.
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires old(stores)@ == sv, stores_wf(sv),
    ensures final(stores)@ == sv, cols_ok(c, sv),
{
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let x_l_ok = stores.flat_lineitem.extent_i64(li::L_ORDERKEY, 0, nl);
    let x_l_pk = stores.flat_lineitem.extent_i64(li::L_PARTKEY, 0, nl);
    let x_l_sk = stores.flat_lineitem.extent_i64(li::L_SUPPKEY, 0, nl);
    let x_l_price = stores.flat_lineitem.extent_i128(li::L_EXTENDEDPRICE, 0, nl);
    let x_l_disc = stores.flat_lineitem.extent_i128(li::L_DISCOUNT, 0, nl);
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let x_o_key = stores.flat_orders.extent_i64(oi::O_ORDERKEY, 0, no);
    let x_o_cust = stores.flat_orders.extent_i64(oi::O_CUSTKEY, 0, no);
    let x_o_date = stores.flat_orders.extent_i32(oi::O_ORDERDATE, 0, no);
    let nc = stores.flat_customer.part_len(ci::C_CUSTKEY);
    let x_c_key = stores.flat_customer.extent_i64(ci::C_CUSTKEY, 0, nc);
    let x_c_nat = stores.flat_customer.extent_i64(ci::C_NATIONKEY, 0, nc);
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let x_p_key = stores.flat_part.extent_i64(pi::P_PARTKEY, 0, np);
    let npo = stores.flat_part.part_len(pi::P_TYPE_OFFSETS);
    let x_p_toffs = stores.flat_part.extent_i64(pi::P_TYPE_OFFSETS, 0, npo);
    let p_tnb = stores.flat_part.part_len(pi::P_TYPE_BYTES);
    let x_p_tbytes = stores.flat_part.extent_u8(pi::P_TYPE_BYTES, 0, p_tnb);
    let ns = stores.flat_supplier.part_len(si::S_SUPPKEY);
    let x_s_key = stores.flat_supplier.extent_i64(si::S_SUPPKEY, 0, ns);
    let x_s_nat = stores.flat_supplier.extent_i64(si::S_NATIONKEY, 0, ns);
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    let x_n_key = stores.flat_nation.extent_i64(ni::N_NATIONKEY, 0, nn);
    let x_n_reg = stores.flat_nation.extent_i64(ni::N_REGIONKEY, 0, nn);
    let nno = stores.flat_nation.part_len(ni::N_NAME_OFFSETS);
    let x_n_noffs = stores.flat_nation.extent_i64(ni::N_NAME_OFFSETS, 0, nno);
    let n_nnb = stores.flat_nation.part_len(ni::N_NAME_BYTES);
    let x_n_nbytes = stores.flat_nation.extent_u8(ni::N_NAME_BYTES, 0, n_nnb);
    let nr = stores.flat_region.part_len(ri::R_REGIONKEY);
    let x_r_key = stores.flat_region.extent_i64(ri::R_REGIONKEY, 0, nr);
    let nro = stores.flat_region.part_len(ri::R_NAME_OFFSETS);
    let x_r_noffs = stores.flat_region.extent_i64(ri::R_NAME_OFFSETS, 0, nro);
    let r_nnb = stores.flat_region.part_len(ri::R_NAME_BYTES);
    let x_r_nbytes = stores.flat_region.extent_u8(ri::R_NAME_BYTES, 0, r_nnb);
    let c = Cols {
        l_ok: x_l_ok, l_pk: x_l_pk, l_sk: x_l_sk, l_price: x_l_price, l_disc: x_l_disc, nl,
        o_key: x_o_key, o_cust: x_o_cust, o_date: x_o_date, no, c_key: x_c_key, c_nat: x_c_nat, nc,
        p_key: x_p_key, p_toffs: x_p_toffs, p_tbytes: x_p_tbytes, p_tnb, np, s_key: x_s_key, s_nat: x_s_nat, ns,
        n_key: x_n_key, n_reg: x_n_reg, n_noffs: x_n_noffs, n_nbytes: x_n_nbytes, n_nnb, nn,
        r_key: x_r_key, r_noffs: x_r_noffs, r_nbytes: x_r_nbytes, r_nnb, nr,
    };
    proof {
        assert(c.l_ok@ =~= l_okey(sv) && c.l_pk@ =~= l_pkey(sv) && c.l_sk@ =~= l_skey(sv));
        assert(c.l_price@ =~= l_price(sv) && c.l_disc@ =~= l_disc(sv));
        assert(c.o_key@ =~= o_key(sv) && c.o_cust@ =~= o_cust(sv) && c.o_date@ =~= o_date(sv));
        assert(c.c_key@ =~= c_key(sv) && c.c_nat@ =~= c_nat(sv));
        assert(c.p_key@ =~= p_key(sv) && c.p_toffs@ =~= ptype_col(sv).offsets && c.p_tbytes@ =~= ptype_col(sv).bytes);
        assert(c.s_key@ =~= s_key(sv) && c.s_nat@ =~= s_nat(sv));
        assert(c.n_key@ =~= n_key(sv) && c.n_reg@ =~= n_reg(sv));
        assert(c.n_noffs@ =~= nname_col(sv).offsets && c.n_nbytes@ =~= nname_col(sv).bytes);
        assert(c.r_key@ =~= r_key(sv) && c.r_noffs@ =~= rname_col(sv).offsets && c.r_nbytes@ =~= rname_col(sv).bytes);
    }
    c
}

} // verus!
