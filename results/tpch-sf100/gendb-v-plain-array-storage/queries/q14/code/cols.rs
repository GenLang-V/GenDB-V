//! The stored columns the query reads, as `&'static` slices (whole parts, requested once on the calling thread),
//! and their correspondence with the model's column views (`cols_ok`).
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::{text_wf, TextView};
use crate::agent::tables::*;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_part::interface as pi;

verus! {

/// The columns, with their row counts (and the byte count of the `p_type` bytes part).
#[derive(Clone, Copy)]
pub struct Cols {
    pub l_pkey: &'static [i64],
    pub l_price: &'static [i128],
    pub l_disc: &'static [i128],
    pub l_ship: &'static [i32],
    pub nl: usize,
    pub p_key: &'static [i64],
    pub p_toffs: &'static [i64],
    pub p_tbytes: &'static [u8],
    pub p_tnb: usize,
    pub np: usize,
}

/// The text column of the offsets `offs` and bytes `bytes`.
pub open spec fn tview(offs: Seq<i64>, bytes: Seq<u8>) -> TextView {
    TextView { offsets: offs, bytes }
}

/// The slices are the stored columns, every column has its table's row count, and `p_type` is well formed.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.l_pkey@ == l_pkey(sv) && c.l_price@ == l_price(sv) && c.l_disc@ == l_disc(sv) && c.l_ship@ == l_ship(sv)
    &&& c.nl == n_l(sv)
    &&& l_pkey(sv).len() == n_l(sv) && l_price(sv).len() == n_l(sv) && l_disc(sv).len() == n_l(sv)
    &&& l_ship(sv).len() == n_l(sv)
    &&& c.p_key@ == p_key(sv) && c.np == n_p(sv)
    &&& tview(c.p_toffs@, c.p_tbytes@) == ptype_col(sv) && text_wf(ptype_col(sv), n_p(sv) as int)
    &&& c.p_tnb == c.p_tbytes@.len()
}

/// Request the columns (whole parts) from the stores.
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires old(stores)@ == sv, stores_wf(sv),
    ensures final(stores)@ == sv, cols_ok(c, sv),
{
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let x_pkey = stores.flat_lineitem.extent_i64(li::L_PARTKEY, 0, nl);
    let x_price = stores.flat_lineitem.extent_i128(li::L_EXTENDEDPRICE, 0, nl);
    let x_disc = stores.flat_lineitem.extent_i128(li::L_DISCOUNT, 0, nl);
    let x_ship = stores.flat_lineitem.extent_i32(li::L_SHIPDATE, 0, nl);
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let x_key = stores.flat_part.extent_i64(pi::P_PARTKEY, 0, np);
    let npo = stores.flat_part.part_len(pi::P_TYPE_OFFSETS);
    let p_toffs = stores.flat_part.extent_i64(pi::P_TYPE_OFFSETS, 0, npo);
    let p_tnb = stores.flat_part.part_len(pi::P_TYPE_BYTES);
    let p_tbytes = stores.flat_part.extent_u8(pi::P_TYPE_BYTES, 0, p_tnb);
    let c = Cols { l_pkey: x_pkey, l_price: x_price, l_disc: x_disc, l_ship: x_ship, nl, p_key: x_key, p_toffs, p_tbytes, p_tnb, np };
    proof {
        assert(c.l_pkey@ =~= l_pkey(sv) && c.l_price@ =~= l_price(sv) && c.l_disc@ =~= l_disc(sv));
        assert(c.l_ship@ =~= l_ship(sv));
        assert(c.p_key@ =~= p_key(sv) && c.p_toffs@ =~= ptype_col(sv).offsets && c.p_tbytes@ =~= ptype_col(sv).bytes);
    }
    c
}

} // verus!
