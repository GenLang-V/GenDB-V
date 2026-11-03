//! The stored columns the query reads, as `&'static` slices (whole parts, requested once on the calling thread),
//! and their correspondence with the model's column views (`cols_ok`).
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::text_wf;
use crate::agent::tables::*;
use crate::agent::common::text_eq::tview;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_part::interface as pi;

verus! {

/// A text column: offsets (rows + 1) and bytes.
#[derive(Clone, Copy)]
pub struct Text {
    pub offs: &'static [i64],
    pub bytes: &'static [u8],
}

pub open spec fn tv(t: Text) -> crate::link::query::TextView { tview(t.offs@, t.bytes@) }

/// The lineitem columns.
#[derive(Clone, Copy)]
pub struct LineCols {
    pub pkey: &'static [i64],
    pub qty: &'static [i128],
    pub price: &'static [i128],
    pub disc: &'static [i128],
    pub instr: Text,
    pub mode: Text,
    pub nl: usize,
}

/// The part columns.
#[derive(Clone, Copy)]
pub struct PartCols {
    pub key: &'static [i64],
    pub size: &'static [i64],
    pub brand: Text,
    pub cont: Text,
    pub np: usize,
}

/// The lineitem slices are the stored columns, every column has the table's row count.
pub open spec fn line_cols_ok(c: LineCols, sv: StoresView) -> bool {
    &&& c.pkey@ == l_pkey(sv) && c.qty@ == l_qty(sv) && c.price@ == l_price(sv) && c.disc@ == l_disc(sv)
    &&& tv(c.instr) == instr_col(sv) && tv(c.mode) == mode_col(sv)
    &&& c.nl == n_l(sv)
    &&& l_pkey(sv).len() == n_l(sv) && l_qty(sv).len() == n_l(sv) && l_price(sv).len() == n_l(sv)
    &&& l_disc(sv).len() == n_l(sv)
    &&& text_wf(instr_col(sv), n_l(sv) as int) && text_wf(mode_col(sv), n_l(sv) as int)
}

/// The part slices are the stored columns, every column has the table's row count.
pub open spec fn part_cols_ok(c: PartCols, sv: StoresView) -> bool {
    &&& c.key@ == p_key(sv) && c.size@ == p_size(sv)
    &&& tv(c.brand) == brand_col(sv) && tv(c.cont) == cont_col(sv)
    &&& c.np == n_p(sv)
    &&& p_key(sv).len() == n_p(sv) && p_size(sv).len() == n_p(sv)
    &&& text_wf(brand_col(sv), n_p(sv) as int) && text_wf(cont_col(sv), n_p(sv) as int)
}

/// A whole text column of a storage.
fn read_text(s: &mut crate::gendb_entry::stored::StoredParts, po: usize, pb: usize) -> (t: Text)
    requires po < old(s)@.len(), pb < old(s)@.len(), old(s)@[po as int] is I64, old(s)@[pb as int] is U8,
    ensures final(s)@ == old(s)@, t.offs@ == old(s)@[po as int]->I64_0, t.bytes@ == old(s)@[pb as int]->U8_0,
{
    let no = s.part_len(po);
    let offs = s.extent_i64(po, 0, no);
    let nb = s.part_len(pb);
    let bytes = s.extent_u8(pb, 0, nb);
    proof {
        assert(offs@ =~= s@[po as int]->I64_0);
        assert(bytes@ =~= s@[pb as int]->U8_0);
    }
    Text { offs, bytes }
}

/// Request the lineitem columns (whole parts).
pub fn read_line(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: LineCols)
    requires old(stores)@ == sv, stores_wf(sv),
    ensures final(stores)@ == sv, line_cols_ok(c, sv),
{
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let pkey = stores.flat_lineitem.extent_i64(li::L_PARTKEY, 0, nl);
    let qty = stores.flat_lineitem.extent_i128(li::L_QUANTITY, 0, nl);
    let price = stores.flat_lineitem.extent_i128(li::L_EXTENDEDPRICE, 0, nl);
    let disc = stores.flat_lineitem.extent_i128(li::L_DISCOUNT, 0, nl);
    let instr = read_text(&mut stores.flat_lineitem, li::L_SHIPINSTRUCT_OFFSETS, li::L_SHIPINSTRUCT_BYTES);
    let mode = read_text(&mut stores.flat_lineitem, li::L_SHIPMODE_OFFSETS, li::L_SHIPMODE_BYTES);
    let c = LineCols { pkey, qty, price, disc, instr, mode, nl };
    proof {
        assert(c.pkey@ =~= l_pkey(sv) && c.qty@ =~= l_qty(sv) && c.price@ =~= l_price(sv) && c.disc@ =~= l_disc(sv));
    }
    c
}

/// Request the part columns (whole parts).
pub fn read_part(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: PartCols)
    requires old(stores)@ == sv, stores_wf(sv),
    ensures final(stores)@ == sv, part_cols_ok(c, sv),
{
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let key = stores.flat_part.extent_i64(pi::P_PARTKEY, 0, np);
    let size = stores.flat_part.extent_i64(pi::P_SIZE, 0, np);
    let brand = read_text(&mut stores.flat_part, pi::P_BRAND_OFFSETS, pi::P_BRAND_BYTES);
    let cont = read_text(&mut stores.flat_part, pi::P_CONTAINER_OFFSETS, pi::P_CONTAINER_BYTES);
    let c = PartCols { key, size, brand, cont, np };
    proof {
        assert(c.key@ =~= p_key(sv) && c.size@ =~= p_size(sv));
    }
    c
}

} // verus!
