//! The stored columns the query reads, as `&'static` slices (whole parts, requested once on the calling thread),
//! and their correspondence with the model's column views (`cols_ok`).
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::{text_wf, TextView};
use crate::agent::tables::*;
use crate::agent::sub::sizes_ok;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_part::interface as pi;

verus! {

/// The columns, with their row counts.
#[derive(Clone, Copy)]
pub struct Cols {
    pub l_pkey: &'static [i64],
    pub l_qty: &'static [i128],
    pub l_price: &'static [i128],
    pub nl: usize,
    pub p_key: &'static [i64],
    pub b_offs: &'static [i64],
    pub b_bytes: &'static [u8],
    pub c_offs: &'static [i64],
    pub c_bytes: &'static [u8],
    pub np: usize,
    pub b_nb: usize,
    pub c_nb: usize,
}

/// The text column of the offsets `offs` and bytes `bytes`.
pub open spec fn tview(offs: Seq<i64>, bytes: Seq<u8>) -> TextView {
    TextView { offsets: offs, bytes }
}

/// The slices are the stored columns, every column has its table's row count, and the text columns are well
/// formed.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.l_pkey@ == l_pkey(sv) && c.l_qty@ == l_qty(sv) && c.l_price@ == l_price(sv)
    &&& c.nl == n_l(sv)
    &&& l_pkey(sv).len() == n_l(sv) && l_qty(sv).len() == n_l(sv) && l_price(sv).len() == n_l(sv)
    &&& c.p_key@ == p_key(sv) && c.np == n_p(sv) && p_key(sv).len() == n_p(sv)
    &&& tview(c.b_offs@, c.b_bytes@) == brand_col(sv) && text_wf(brand_col(sv), n_p(sv) as int)
    &&& tview(c.c_offs@, c.c_bytes@) == cont_col(sv) && text_wf(cont_col(sv), n_p(sv) as int)
    &&& c.b_nb == c.b_bytes@.len() && c.c_nb == c.c_bytes@.len()
}

/// Request the columns (whole parts) from the stores.
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires old(stores)@ == sv, stores_wf(sv),
    ensures final(stores)@ == sv, cols_ok(c, sv), sizes_ok(sv),
{
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let x_pkey = stores.flat_lineitem.extent_i64(li::L_PARTKEY, 0, nl);
    let x_qty = stores.flat_lineitem.extent_i128(li::L_QUANTITY, 0, nl);
    let x_price = stores.flat_lineitem.extent_i128(li::L_EXTENDEDPRICE, 0, nl);
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let x_key = stores.flat_part.extent_i64(pi::P_PARTKEY, 0, np);
    let nbo = stores.flat_part.part_len(pi::P_BRAND_OFFSETS);
    let b_offs = stores.flat_part.extent_i64(pi::P_BRAND_OFFSETS, 0, nbo);
    let nbb = stores.flat_part.part_len(pi::P_BRAND_BYTES);
    let b_bytes = stores.flat_part.extent_u8(pi::P_BRAND_BYTES, 0, nbb);
    let nco = stores.flat_part.part_len(pi::P_CONTAINER_OFFSETS);
    let c_offs = stores.flat_part.extent_i64(pi::P_CONTAINER_OFFSETS, 0, nco);
    let ncb = stores.flat_part.part_len(pi::P_CONTAINER_BYTES);
    let c_bytes = stores.flat_part.extent_u8(pi::P_CONTAINER_BYTES, 0, ncb);
    let c = Cols { l_pkey: x_pkey, l_qty: x_qty, l_price: x_price, nl, p_key: x_key, b_offs, b_bytes, c_offs, c_bytes, np, b_nb: nbb, c_nb: ncb };
    proof {
        assert(c.l_pkey@ =~= l_pkey(sv) && c.l_qty@ =~= l_qty(sv) && c.l_price@ =~= l_price(sv));
        assert(c.p_key@ =~= p_key(sv));
        assert(c.b_offs@ =~= brand_col(sv).offsets && c.b_bytes@ =~= brand_col(sv).bytes);
        assert(c.c_offs@ =~= cont_col(sv).offsets && c.c_bytes@ =~= cont_col(sv).bytes);
    }
    c
}

} // verus!
