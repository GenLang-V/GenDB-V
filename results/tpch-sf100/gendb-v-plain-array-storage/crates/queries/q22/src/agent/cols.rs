//! The stored columns the query reads, as whole-part slices: `o_custkey` of `flat_orders`; `c_custkey`, `c_phone`
//! (offsets and bytes) and `c_acctbal` (coefficients at scale 2) of `flat_customer`. `cols_ok` ties the slices to
//! the column views of `tables` and carries the facts every bound database gives (well-formed parts, the
//! numeric(15,2) domain, the customer row count below `2^61`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::{bound_db, stores_ready};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::text_wf;
use crate::agent::tables::*;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;

verus! {

/// The columns the query reads (one extent per part) and the row counts.
#[derive(Clone, Copy)]
pub struct Cols {
    /// `o_custkey` of every orders row.
    pub ock: &'static [i64],
    /// `c_custkey` of every customer row.
    pub cck: &'static [i64],
    /// `c_phone` offsets (customer rows + 1) and bytes.
    pub poffs: &'static [i64],
    pub pbytes: &'static [u8],
    /// `c_acctbal` coefficients (scale 2).
    pub bal: &'static [i128],
    /// Orders rows, customer rows, phone bytes.
    pub no: usize,
    pub nc: usize,
    pub nbytes: usize,
}

/// The slices are the stored columns of `sv`, with the facts every bound database gives.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.ock@ == ock(sv) && c.cck@ == cck(sv) && c.bal@ == bal(sv)
    &&& c.poffs@ == phone_col(sv).offsets && c.pbytes@ == phone_col(sv).bytes
    &&& c.no as int == n_o(sv) && c.nc as int == n_c(sv) && c.nbytes as int == c.pbytes@.len()
    &&& model_ok(sv)
    &&& sizes_ok(sv)
}

/// The facts of the model hold for the parts alone (they hold for every bound database).
#[verifier::spinoff_prover]
pub proof fn lemma_ready_model(sv: StoresView)
    requires stores_ready(sv),
    ensures model_ok(sv),
{
    let db = choose|db: Database| bound_db(sv, db);
    lemma_model(sv, db);
}

/// The phone of customer row `i` is the byte range of its offsets.
#[verifier::spinoff_prover]
pub proof fn lemma_phone_range(c: Cols, sv: StoresView, i: int)
    requires cols_ok(c, sv), 0 <= i < c.nc,
    ensures
        0 <= c.poffs@[i] <= c.poffs@[i + 1] <= c.nbytes,
        phone(sv, i) == c.pbytes@.subrange(c.poffs@[i] as int, c.poffs@[i + 1] as int),
{
    assert(text_wf(phone_col(sv), n_c(sv) as int));
}

/// Reads every column the query needs as one extent per part.
#[verifier::spinoff_prover]
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires old(stores)@ == sv, stores_ready(sv),
    ensures final(stores)@ == sv, cols_ok(c, sv),
{
    proof {
        lemma_ready_model(sv);
        assert(text_wf(phone_col(sv), n_c(sv) as int));
    }
    let no = stores.flat_orders.part_len(oi::O_CUSTKEY);
    let ock = stores.flat_orders.extent_i64(oi::O_CUSTKEY, 0, no);
    let nc = stores.flat_customer.part_len(ci::C_CUSTKEY);
    let cck = stores.flat_customer.extent_i64(ci::C_CUSTKEY, 0, nc);
    let npo = stores.flat_customer.part_len(ci::C_PHONE_OFFSETS);
    let poffs = stores.flat_customer.extent_i64(ci::C_PHONE_OFFSETS, 0, npo);
    let nbytes = stores.flat_customer.part_len(ci::C_PHONE_BYTES);
    let pbytes = stores.flat_customer.extent_u8(ci::C_PHONE_BYTES, 0, nbytes);
    let nb = stores.flat_customer.part_len(ci::C_ACCTBAL);
    let bal = stores.flat_customer.extent_i128(ci::C_ACCTBAL, 0, nb);
    // the customer key column is a slice of 8-byte elements: fewer than 2^61 rows
    let size = core::mem::size_of_val(cck);
    proof {
        broadcast use vstd::layout::layout_of_primitives, vstd::layout::layout_of_slices;
        assert(cck@.len() * 8 <= usize::MAX);
        assert(usize::MAX <= u64::MAX);
        assert(ock@ =~= crate::agent::tables::ock(sv));
        assert(cck@ =~= crate::agent::tables::cck(sv));
        assert(poffs@ =~= phone_col(sv).offsets);
        assert(pbytes@ =~= phone_col(sv).bytes);
        assert(bal@ =~= crate::agent::tables::bal(sv));
    }
    Cols { ock, cck, poffs, pbytes, bal, no, nc, nbytes }
}

} // verus!
