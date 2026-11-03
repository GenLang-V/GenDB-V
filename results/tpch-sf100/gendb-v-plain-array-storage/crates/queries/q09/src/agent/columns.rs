//! The stored columns the query reads, as whole-column slices (one extent per part; the host maps the parts, so
//! only the pages the scans touch are read), and the facts every bound database gives about them (`cols_ok`):
//! the slices are the column views of `agent::tables`, the name columns are well-formed text, the key columns are
//! duplicate-free and the numeric columns are inside numeric(15,2).
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::{stores_ready, bound_db};
use crate::link::query::text_wf;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::agent::tables::*;

verus! {

/// The columns of the six tables the query reads (whole columns) and the row counts.
#[derive(Clone, Copy)]
pub struct Cols {
    pub lokey: &'static [i64],
    pub lpart: &'static [i64],
    pub lsupp: &'static [i64],
    pub lqty: &'static [i128],
    pub lprice: &'static [i128],
    pub ldisc: &'static [i128],
    pub okey: &'static [i64],
    pub odate: &'static [i32],
    pub pkey: &'static [i64],
    pub poffs: &'static [i64],
    pub pbytes: &'static [u8],
    pub pspart: &'static [i64],
    pub pssupp: &'static [i64],
    pub pscost: &'static [i128],
    pub skey: &'static [i64],
    pub snat: &'static [i64],
    pub nkey: &'static [i64],
    pub noffs: &'static [i64],
    pub nbytes: &'static [u8],
    pub pbl: usize,
    pub nbl: usize,
    pub nl: usize,
    pub no: usize,
    pub np: usize,
    pub nps: usize,
    pub ns: usize,
    pub nn: usize,
}

/// The slices are the stored columns of `sv`, with the facts every bound database gives about them.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.lokey@ == lok(sv) && c.lpart@ == lpk(sv) && c.lsupp@ == lsk(sv)
    &&& c.lqty@ == lqt(sv) && c.lprice@ == lpr(sv) && c.ldisc@ == ldc(sv)
    &&& c.okey@ == ok(sv) && c.odate@ == od(sv)
    &&& c.pkey@ == pk(sv) && c.poffs@ == pname_col(sv).offsets && c.pbytes@ == pname_col(sv).bytes
    &&& c.pspart@ == pspk(sv) && c.pssupp@ == pssk(sv) && c.pscost@ == psc(sv)
    &&& c.skey@ == sk(sv) && c.snat@ == sn(sv)
    &&& c.nkey@ == nk(sv) && c.noffs@ == nname_col(sv).offsets && c.nbytes@ == nname_col(sv).bytes
    &&& c.nl as int == n_l(sv) && c.no as int == n_o(sv) && c.np as int == n_p(sv)
    &&& c.nps as int == n_ps(sv) && c.ns as int == n_s(sv) && c.nn as int == n_n(sv)
    &&& c.pbl as int == c.pbytes@.len() && c.nbl as int == c.nbytes@.len()
    &&& col_lens(sv)
    &&& text_wf(pname_col(sv), n_p(sv)) && text_wf(nname_col(sv), n_n(sv))
    &&& keys_unique(pk(sv)) && keys_unique(sk(sv)) && keys_unique(ok(sv)) && keys_unique(nk(sv))
    &&& keys2_unique(pspk(sv), pssk(sv))
    &&& nums_ok(sv)
}

/// Every bound database gives the same column facts (they are facts of the parts alone).
pub proof fn lemma_cols_facts(sv: StoresView)
    requires stores_ready(sv),
    ensures
        parts_shape(sv), col_lens(sv),
        text_wf(pname_col(sv), n_p(sv)), text_wf(nname_col(sv), n_n(sv)),
        keys_unique(pk(sv)), keys_unique(sk(sv)), keys_unique(ok(sv)), keys_unique(nk(sv)),
        keys2_unique(pspk(sv), pssk(sv)),
        nums_ok(sv),
{
    let db = choose|db: crate::spec::value::Database| bound_db(sv, db);
    lemma_parts_shape(sv, db);
    lemma_keys_unique(sv, db);
    lemma_nums_ok(sv, db);
}

/// Reads every column the query needs as one extent per part.
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires old(stores)@ == sv, stores_ready(sv),
    ensures final(stores)@ == sv, cols_ok(c, sv),
{
    proof { lemma_cols_facts(sv); }
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let lokey = stores.flat_lineitem.extent_i64(li::L_ORDERKEY, 0, nl);
    let lpart = stores.flat_lineitem.extent_i64(li::L_PARTKEY, 0, nl);
    let lsupp = stores.flat_lineitem.extent_i64(li::L_SUPPKEY, 0, nl);
    let lqty = stores.flat_lineitem.extent_i128(li::L_QUANTITY, 0, nl);
    let lprice = stores.flat_lineitem.extent_i128(li::L_EXTENDEDPRICE, 0, nl);
    let ldisc = stores.flat_lineitem.extent_i128(li::L_DISCOUNT, 0, nl);
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let okey = stores.flat_orders.extent_i64(oi::O_ORDERKEY, 0, no);
    let odate = stores.flat_orders.extent_i32(oi::O_ORDERDATE, 0, no);
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let pkey = stores.flat_part.extent_i64(pi::P_PARTKEY, 0, np);
    let poffs_len = stores.flat_part.part_len(pi::P_NAME_OFFSETS);
    let poffs = stores.flat_part.extent_i64(pi::P_NAME_OFFSETS, 0, poffs_len);
    let pbytes_len = stores.flat_part.part_len(pi::P_NAME_BYTES);
    let pbytes = stores.flat_part.extent_u8(pi::P_NAME_BYTES, 0, pbytes_len);
    let nps = stores.flat_partsupp.part_len(psi::PS_PARTKEY);
    let pspart = stores.flat_partsupp.extent_i64(psi::PS_PARTKEY, 0, nps);
    let pssupp = stores.flat_partsupp.extent_i64(psi::PS_SUPPKEY, 0, nps);
    let pscost = stores.flat_partsupp.extent_i128(psi::PS_SUPPLYCOST, 0, nps);
    let ns = stores.flat_supplier.part_len(si::S_SUPPKEY);
    let skey = stores.flat_supplier.extent_i64(si::S_SUPPKEY, 0, ns);
    let snat = stores.flat_supplier.extent_i64(si::S_NATIONKEY, 0, ns);
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    let nkey = stores.flat_nation.extent_i64(ni::N_NATIONKEY, 0, nn);
    let noffs_len = stores.flat_nation.part_len(ni::N_NAME_OFFSETS);
    let noffs = stores.flat_nation.extent_i64(ni::N_NAME_OFFSETS, 0, noffs_len);
    let nbytes_len = stores.flat_nation.part_len(ni::N_NAME_BYTES);
    let nbytes = stores.flat_nation.extent_u8(ni::N_NAME_BYTES, 0, nbytes_len);
    let c = Cols { lokey, lpart, lsupp, lqty, lprice, ldisc, okey, odate, pkey, poffs, pbytes, pspart, pssupp, pscost,
        skey, snat, nkey, noffs, nbytes, pbl: pbytes_len, nbl: nbytes_len, nl, no, np, nps, ns, nn };
    proof {
        assert(stores@ == sv);
        assert(c.lokey@ =~= lok(sv) && c.lpart@ =~= lpk(sv) && c.lsupp@ =~= lsk(sv));
        assert(c.lqty@ =~= lqt(sv) && c.lprice@ =~= lpr(sv) && c.ldisc@ =~= ldc(sv));
        assert(c.okey@ =~= ok(sv) && c.odate@ =~= od(sv));
        assert(c.pkey@ =~= pk(sv) && c.poffs@ =~= pname_col(sv).offsets && c.pbytes@ =~= pname_col(sv).bytes);
        assert(c.pspart@ =~= pspk(sv) && c.pssupp@ =~= pssk(sv) && c.pscost@ =~= psc(sv));
        assert(c.skey@ =~= sk(sv) && c.snat@ =~= sn(sv));
        assert(c.nkey@ =~= nk(sv) && c.noffs@ =~= nname_col(sv).offsets && c.nbytes@ =~= nname_col(sv).bytes);
    }
    c
}

} // verus!
