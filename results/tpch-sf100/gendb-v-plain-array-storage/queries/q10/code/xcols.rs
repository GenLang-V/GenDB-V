//! The executable column handles shared by every task (`Cols`, plain `&'static` slices of the stored parts) and the
//! facts they carry about the stored columns (`cols_ok`).
//!
//! `dlo`/`dhi` are the window on stored days (`[dlo, dhi)`, `dlo <= dhi`); `cbase` is `c_custkey` of customer row 0,
//! so that, once the customer keys are checked to be positional (`c_custkey[r] == cbase + r`), the customer row of a
//! key is a subtraction.
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::bound_db;
use crate::link::query::text_wf;
use crate::spec::value::Database;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_nation::interface as ni;
use crate::agent::cols::*;

verus! {

#[derive(Clone, Copy)]
pub struct Cols {
    pub lk: &'static [i64],
    pub rfo: &'static [i64],
    pub rfb: &'static [u8],
    pub lp: &'static [i128],
    pub ld: &'static [i128],
    pub ok: &'static [i64],
    pub oc: &'static [i64],
    pub od: &'static [i32],
    pub ck: &'static [i64],
    pub cnk: &'static [i64],
    pub nk: &'static [i64],
    pub nl: usize,
    pub no: usize,
    pub nc: usize,
    pub nn: usize,
    pub dlo: i64,
    pub dhi: i64,
    pub cbase: i64,
}

/// The handles are the stored columns of `sv`, with the facts the tasks rely on.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.lk@ == lk(sv) && c.lp@ == lp(sv) && c.ld@ == ld(sv)
    &&& c.rfo@ == rf_col(sv).offsets && c.rfb@ == rf_col(sv).bytes
    &&& c.ok@ == ok(sv) && c.oc@ == oc(sv) && c.od@ == od(sv)
    &&& c.ck@ == ck(sv) && c.cnk@ == cnk(sv) && c.nk@ == nk(sv)
    &&& c.nl as int == n_l(sv) && c.no as int == n_o(sv) && c.nc as int == n_c(sv) && c.nn as int == n_n(sv)
    &&& lp(sv).len() == n_l(sv) && ld(sv).len() == n_l(sv)
    &&& oc(sv).len() == n_o(sv) && od(sv).len() == n_o(sv) && cnk(sv).len() == n_c(sv)
    &&& text_wf(rf_col(sv), n_l(sv))
    &&& keys_unique(ok(sv)) && keys_unique(ck(sv)) && keys_unique(nk(sv))
    &&& forall|i: int| 0 <= i < n_l(sv) ==> num15(#[trigger] lp(sv)[i]) && num15(ld(sv)[i])
    &&& c.dlo <= c.dhi
}

/// The stored columns of every bound database satisfy the facts of `cols_ok` (except the window fields).
pub proof fn lemma_bound_facts(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        parts_shape(sv),
        lp(sv).len() == n_l(sv), ld(sv).len() == n_l(sv),
        oc(sv).len() == n_o(sv), od(sv).len() == n_o(sv), cnk(sv).len() == n_c(sv), cacct(sv).len() == n_c(sv),
        text_wf(rf_col(sv), n_l(sv)),
        keys_unique(ok(sv)), keys_unique(ck(sv)), keys_unique(nk(sv)),
        forall|i: int| 0 <= i < n_l(sv) ==> num15(#[trigger] lp(sv)[i]) && num15(ld(sv)[i]),
{
    lemma_parts_shape(sv, db);
    lemma_keys_unique(sv, db);
    assert forall|i: int| 0 <= i < n_l(sv) implies num15(#[trigger] lp(sv)[i]) && num15(ld(sv)[i]) by {
        lemma_lineitem_row(sv, db, i);
    }
}

/// Reads the columns the tasks use (whole parts) and fixes the window and the customer key base.
pub fn read_cols(stores: &mut Stores, dlo: i64, dhi: i64, Ghost(db): Ghost<Database>) -> (c: Cols)
    requires bound_db(old(stores)@, db), dlo <= dhi,
    ensures final(stores)@ == old(stores)@, cols_ok(c, old(stores)@), c.dlo == dlo, c.dhi == dhi,
        c.nc > 0 ==> c.cbase == ck(old(stores)@)[0],
{
    let ghost sv = stores@;
    proof { lemma_bound_facts(sv, db); }
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let lk_p = stores.flat_lineitem.extent_i64(li::L_ORDERKEY, 0, nl);
    let nro = stores.flat_lineitem.part_len(li::L_RETURNFLAG_OFFSETS);
    let rfo_p = stores.flat_lineitem.extent_i64(li::L_RETURNFLAG_OFFSETS, 0, nro);
    let nrb = stores.flat_lineitem.part_len(li::L_RETURNFLAG_BYTES);
    let rfb_p = stores.flat_lineitem.extent_u8(li::L_RETURNFLAG_BYTES, 0, nrb);
    let lp_p = stores.flat_lineitem.extent_i128(li::L_EXTENDEDPRICE, 0, nl);
    let ld_p = stores.flat_lineitem.extent_i128(li::L_DISCOUNT, 0, nl);
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let ok_p = stores.flat_orders.extent_i64(oi::O_ORDERKEY, 0, no);
    let oc_p = stores.flat_orders.extent_i64(oi::O_CUSTKEY, 0, no);
    let od_p = stores.flat_orders.extent_i32(oi::O_ORDERDATE, 0, no);
    let nc = stores.flat_customer.part_len(ci::C_CUSTKEY);
    let ck_p = stores.flat_customer.extent_i64(ci::C_CUSTKEY, 0, nc);
    let cnk_p = stores.flat_customer.extent_i64(ci::C_NATIONKEY, 0, nc);
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    let nk_p = stores.flat_nation.extent_i64(ni::N_NATIONKEY, 0, nn);
    let cbase: i64 = if nc > 0 { ck_p[0] } else { 0 };
    proof {
        assert(stores@ == sv);
        assert(lk_p@ =~= lk(sv) && lp_p@ =~= lp(sv) && ld_p@ =~= ld(sv));
        assert(rfo_p@ =~= rf_col(sv).offsets && rfb_p@ =~= rf_col(sv).bytes);
        assert(ok_p@ =~= ok(sv) && oc_p@ =~= oc(sv) && od_p@ =~= od(sv));
        assert(ck_p@ =~= ck(sv) && cnk_p@ =~= cnk(sv) && nk_p@ =~= nk(sv));
    }
    Cols { lk: lk_p, rfo: rfo_p, rfb: rfb_p, lp: lp_p, ld: ld_p, ok: ok_p, oc: oc_p, od: od_p, ck: ck_p, cnk: cnk_p, nk: nk_p,
        nl, no, nc, nn, dlo, dhi, cbase }
}

} // verus!
