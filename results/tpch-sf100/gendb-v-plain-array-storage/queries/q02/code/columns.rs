//! The stored columns the query reads, as whole-column slices (one extent per part; the host maps the parts lazily,
//! so only the pages the scans touch are read), and their relation to the model's stored columns (`cols_ok`).
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::{TextView, text_at};
use crate::agent::model::*;
use crate::agent::model;
use crate::agent::scan_part::{text_row, text_col_wf};
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;

verus! {

/// A text column of `n` rows: offsets (`n + 1`) and the bytes they address (`blen` bytes).
pub struct TextSlice {
    pub off: &'static [i64],
    pub bytes: &'static [u8],
    pub n: usize,
    pub blen: usize,
}

/// `t` holds the `n` values of the text column `view`.
pub open spec fn text_is(t: TextSlice, view: TextView, n: int) -> bool {
    &&& t.n == n
    &&& text_col_wf(t.off@, t.bytes@, n)
    &&& t.blen == t.bytes@.len()
    &&& forall|a: int| 0 <= a < n ==> #[trigger] text_row(t.off@, t.bytes@, a) == text_at(view, a)
}

/// The columns the query reads.
pub struct Cols {
    pub np: usize,
    pub p_keys: &'static [i64],
    pub p_sizes: &'static [i64],
    pub p_type: TextSlice,
    pub p_mfgr: TextSlice,
    pub nps: usize,
    pub ps_pkeys: &'static [i64],
    pub ps_skeys: &'static [i64],
    pub ps_costs: &'static [i128],
    pub ns: usize,
    pub s_keys: &'static [i64],
    pub s_nks: &'static [i64],
    pub s_accts: &'static [i128],
    pub s_name: TextSlice,
    pub s_address: TextSlice,
    pub s_phone: TextSlice,
    pub s_comment: TextSlice,
    pub nn: usize,
    pub n_keys: &'static [i64],
    pub n_rks: &'static [i64],
    pub n_name: TextSlice,
    pub nr: usize,
    pub r_keys: &'static [i64],
    pub r_name: TextSlice,
}

/// The slices are the stored columns of `sv`.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.np == part_n(sv) && c.nps == ps_n(sv) && c.ns == supp_n(sv) && c.nn == nat_n(sv) && c.nr == reg_n(sv)
    &&& c.p_keys@.len() == c.np && c.p_sizes@.len() == c.np
    &&& c.ps_pkeys@.len() == c.nps && c.ps_skeys@.len() == c.nps && c.ps_costs@.len() == c.nps
    &&& c.s_keys@.len() == c.ns && c.s_nks@.len() == c.ns && c.s_accts@.len() == c.ns
    &&& c.n_keys@.len() == c.nn && c.n_rks@.len() == c.nn
    &&& c.r_keys@.len() == c.nr
    &&& c.p_keys@ == p_keys(sv) && c.p_sizes@ == p_sizes(sv)
    &&& text_is(c.p_type, pi::text_view(sv.flat_part, pi::P_TYPE_OFFSETS as int, pi::P_TYPE_BYTES as int), c.np as int)
    &&& text_is(c.p_mfgr, pi::text_view(sv.flat_part, pi::P_MFGR_OFFSETS as int, pi::P_MFGR_BYTES as int), c.np as int)
    &&& c.ps_pkeys@ == ps_pkeys(sv) && c.ps_skeys@ == ps_skeys(sv) && c.ps_costs@ == ps_costs(sv)
    &&& c.s_keys@ == s_keys(sv) && c.s_nks@ == s_nks(sv) && c.s_accts@ == s_accts(sv)
    &&& text_is(c.s_name, si::text_view(sv.flat_supplier, si::S_NAME_OFFSETS as int, si::S_NAME_BYTES as int), c.ns as int)
    &&& text_is(c.s_address, si::text_view(sv.flat_supplier, si::S_ADDRESS_OFFSETS as int, si::S_ADDRESS_BYTES as int), c.ns as int)
    &&& text_is(c.s_phone, si::text_view(sv.flat_supplier, si::S_PHONE_OFFSETS as int, si::S_PHONE_BYTES as int), c.ns as int)
    &&& text_is(c.s_comment, si::text_view(sv.flat_supplier, si::S_COMMENT_OFFSETS as int, si::S_COMMENT_BYTES as int), c.ns as int)
    &&& c.n_keys@ == n_keys(sv) && c.n_rks@ == n_rks(sv)
    &&& text_is(c.n_name, ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int), c.nn as int)
    &&& c.r_keys@ == r_keys(sv)
    &&& text_is(c.r_name, ri::text_view(sv.flat_region, ri::R_NAME_OFFSETS as int, ri::R_NAME_BYTES as int), c.nr as int)
}

/// Turns the reader output `(offsets, bytes)` of rows `0..n` into a `TextSlice`.
fn text_slice_of(r: (&'static [i64], &'static [u8]), n: usize, Ghost(view): Ghost<TextView>) -> (t: TextSlice)
    requires
        n >= 1,
        r.0@.len() == n + 1,
        0 <= r.0@[0],
        forall|a: int, b: int| 0 <= a <= b <= n ==> r.0@[a] <= r.0@[b],
        r.1@.len() == r.0@[n as int] - r.0@[0],
        forall|j: int| 0 <= j < n ==> #[trigger] r.1@.subrange(r.0@[j] - r.0@[0], r.0@[j + 1] - r.0@[0]) == text_at(view, j),
    ensures text_is(t, view, n as int),
{
    let blen = r.1.len();
    let t = TextSlice { off: r.0, bytes: r.1, n, blen };
    proof {
        assert forall|a: int| 0 <= a < n implies #[trigger] text_row(t.off@, t.bytes@, a) == text_at(view, a) by {
            assert(r.1@.subrange(r.0@[a] - r.0@[0], r.0@[a + 1] - r.0@[0]) == text_at(view, a));
        }
    }
    t
}

/// Read every column the query reads (all tables non-empty).
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires
        old(stores)@ == sv,
        stores_wf(sv),
        part_n(sv) >= 1, ps_n(sv) >= 1, supp_n(sv) >= 1, nat_n(sv) >= 1, reg_n(sv) >= 1,
    ensures
        final(stores)@ == sv,
        cols_ok(c, sv),
{
    // part
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let p_keys = stores.flat_part.extent_i64(pi::P_PARTKEY, 0, np);
    let p_sizes = stores.flat_part.extent_i64(pi::P_SIZE, 0, np);
    assert(p_keys@ =~= model::p_keys(sv));
    assert(p_sizes@ =~= model::p_sizes(sv));
    let r = pi::text_rows(&mut stores.flat_part, pi::P_TYPE_OFFSETS, pi::P_TYPE_BYTES, 0, np, Ghost(np as int));
    let p_type = text_slice_of(r, np, Ghost(pi::text_view(sv.flat_part, pi::P_TYPE_OFFSETS as int, pi::P_TYPE_BYTES as int)));
    let r = pi::text_rows(&mut stores.flat_part, pi::P_MFGR_OFFSETS, pi::P_MFGR_BYTES, 0, np, Ghost(np as int));
    let p_mfgr = text_slice_of(r, np, Ghost(pi::text_view(sv.flat_part, pi::P_MFGR_OFFSETS as int, pi::P_MFGR_BYTES as int)));
    // partsupp
    let nps = stores.flat_partsupp.part_len(psi::PS_PARTKEY);
    let ps_pkeys = stores.flat_partsupp.extent_i64(psi::PS_PARTKEY, 0, nps);
    let ps_skeys = stores.flat_partsupp.extent_i64(psi::PS_SUPPKEY, 0, nps);
    let ps_costs = stores.flat_partsupp.extent_i128(psi::PS_SUPPLYCOST, 0, nps);
    assert(ps_pkeys@ =~= model::ps_pkeys(sv));
    assert(ps_skeys@ =~= model::ps_skeys(sv));
    assert(ps_costs@ =~= model::ps_costs(sv));
    // supplier
    let ns = stores.flat_supplier.part_len(si::S_SUPPKEY);
    let s_keys = stores.flat_supplier.extent_i64(si::S_SUPPKEY, 0, ns);
    let s_nks = stores.flat_supplier.extent_i64(si::S_NATIONKEY, 0, ns);
    let s_accts = stores.flat_supplier.extent_i128(si::S_ACCTBAL, 0, ns);
    assert(s_keys@ =~= model::s_keys(sv));
    assert(s_nks@ =~= model::s_nks(sv));
    assert(s_accts@ =~= model::s_accts(sv));
    let r = si::text_rows(&mut stores.flat_supplier, si::S_NAME_OFFSETS, si::S_NAME_BYTES, 0, ns, Ghost(ns as int));
    let s_name = text_slice_of(r, ns, Ghost(si::text_view(sv.flat_supplier, si::S_NAME_OFFSETS as int, si::S_NAME_BYTES as int)));
    let r = si::text_rows(&mut stores.flat_supplier, si::S_ADDRESS_OFFSETS, si::S_ADDRESS_BYTES, 0, ns, Ghost(ns as int));
    let s_address = text_slice_of(r, ns, Ghost(si::text_view(sv.flat_supplier, si::S_ADDRESS_OFFSETS as int, si::S_ADDRESS_BYTES as int)));
    let r = si::text_rows(&mut stores.flat_supplier, si::S_PHONE_OFFSETS, si::S_PHONE_BYTES, 0, ns, Ghost(ns as int));
    let s_phone = text_slice_of(r, ns, Ghost(si::text_view(sv.flat_supplier, si::S_PHONE_OFFSETS as int, si::S_PHONE_BYTES as int)));
    let r = si::text_rows(&mut stores.flat_supplier, si::S_COMMENT_OFFSETS, si::S_COMMENT_BYTES, 0, ns, Ghost(ns as int));
    let s_comment = text_slice_of(r, ns, Ghost(si::text_view(sv.flat_supplier, si::S_COMMENT_OFFSETS as int, si::S_COMMENT_BYTES as int)));
    // nation
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    let n_keys = stores.flat_nation.extent_i64(ni::N_NATIONKEY, 0, nn);
    let n_rks = stores.flat_nation.extent_i64(ni::N_REGIONKEY, 0, nn);
    assert(n_keys@ =~= model::n_keys(sv));
    assert(n_rks@ =~= model::n_rks(sv));
    let r = ni::text_rows(&mut stores.flat_nation, ni::N_NAME_OFFSETS, ni::N_NAME_BYTES, 0, nn, Ghost(nn as int));
    let n_name = text_slice_of(r, nn, Ghost(ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int)));
    // region
    let nr = stores.flat_region.part_len(ri::R_REGIONKEY);
    let r_keys = stores.flat_region.extent_i64(ri::R_REGIONKEY, 0, nr);
    assert(r_keys@ =~= model::r_keys(sv));
    let r = ri::text_rows(&mut stores.flat_region, ri::R_NAME_OFFSETS, ri::R_NAME_BYTES, 0, nr, Ghost(nr as int));
    let r_name = text_slice_of(r, nr, Ghost(ri::text_view(sv.flat_region, ri::R_NAME_OFFSETS as int, ri::R_NAME_BYTES as int)));
    Cols {
        np, p_keys, p_sizes, p_type, p_mfgr,
        nps, ps_pkeys, ps_skeys, ps_costs,
        ns, s_keys, s_nks, s_accts, s_name, s_address, s_phone, s_comment,
        nn, n_keys, n_rks, n_name,
        nr, r_keys, r_name,
    }
}

} // verus!
