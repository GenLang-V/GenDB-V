//! Column views of the two flat storages the query reads (`flat_orders`, `flat_customer`), how they denote the
//! database tables, and reading them.
//!
//! `ock(sv)[j]` is `o_custkey` of orders row `j`, `cmt(sv, j)` the bytes of its `o_comment`, `cck(sv)[i]` is
//! `c_custkey` of customer row `i`. For a database `db` bound to the parts (`bound_db`), orders row `j` is
//! `db.tables[1][j]` (9 columns: `o_orderkey` at 0 is an integer, `o_custkey` at 1, `o_comment` at 8) and customer
//! row `i` is `db.tables[2][i]` (8 columns, `c_custkey` at 0); the declared primary key makes `c_custkey`
//! duplicate-free (`lemma_cust_keys_unique`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::constraints::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::{bound_db, stores_ready};
use crate::gendb_constraints::declared_db;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::link::query::{text_at, TextView, proj};
use crate::link::source::lemma_proj_all_index;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_orders::declaration as oid;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_customer::declaration as cid;
use crate::agent::common::text_rows::offs_wf;

verus! {

// ------------------------------------------------------------------------------------------------ column views

/// `o_orderkey` of every orders row (its length is the row count).
pub open spec fn ook(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }

/// `o_custkey` of every orders row.
pub open spec fn ock(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]) }

/// The `o_comment` text column (offsets and bytes parts).
pub open spec fn cmt_col(sv: StoresView) -> TextView {
    oi::text_view(sv.flat_orders, oi::O_COMMENT_OFFSETS as int, oi::O_COMMENT_BYTES as int)
}

/// `o_comment` of orders row `j` (its bytes).
pub open spec fn cmt(sv: StoresView, j: int) -> Seq<u8> { text_at(cmt_col(sv), j) }

/// `c_custkey` of every customer row.
pub open spec fn cck(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]) }

/// Row counts.
pub open spec fn n_o(sv: StoresView) -> int { ook(sv).len() as int }
pub open spec fn n_c(sv: StoresView) -> int { cck(sv).len() as int }

/// The parts have the shape of the two flat storages (a consequence of `bound_db`, `lemma_parts_shape`). Opaque:
/// the offsets' quantifier instantiates without end when it is visible in larger proofs.
#[verifier::opaque]
pub open spec fn parts_shape(sv: StoresView) -> bool {
    &&& oi::parts_wf(sv.flat_orders, n_o(sv))
    &&& ci::parts_wf(sv.flat_customer, n_c(sv))
    &&& ock(sv).len() == n_o(sv)
    &&& offs_wf(cmt_col(sv).offsets, n_o(sv), cmt_col(sv).bytes.len() as int)
}

/// The tables of a bound database have the parts' row counts.
pub proof fn lemma_table_lens(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables.len() == 8, db.tables[1].len() == n_o(sv), db.tables[2].len() == n_c(sv),
{
    oid::lemma_declared_schema();
    cid::lemma_declared_schema();
    lemma_proj_all_index(db.tables[1], oid::stored_cols_t0());
    lemma_proj_all_index(db.tables[2], cid::stored_cols_t0());
    assert(oid::stored_relations(db)[0].len() == db.tables[1].len());
    assert(cid::stored_relations(db)[0].len() == db.tables[2].len());
}

/// The parts of a bound database have the storages' shape, and the tables have the parts' row counts.
pub proof fn lemma_parts_shape(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        parts_shape(sv),
        db.tables.len() == 8,
        db.tables[1].len() == n_o(sv),
        db.tables[2].len() == n_c(sv),
{
    reveal(parts_shape);
    lemma_table_lens(sv, db);
}

/// Orders row `j`: arity, an integer `o_orderkey`, `o_custkey`, `o_comment`.
pub proof fn lemma_orders_row(sv: StoresView, db: Database, j: int)
    requires bound_db(sv, db), 0 <= j < n_o(sv),
    ensures
        db.tables[1][j].len() == 9,
        db.tables[1][j][0] == Val::Int(ook(sv)[j] as int),
        db.tables[1][j][1] == Val::Int(ock(sv)[j] as int),
        db.tables[1][j][8] == Val::Text(cmt(sv, j)),
{
    lemma_table_lens(sv, db);
    oid::lemma_declared_schema();
    let t = db.tables[1];
    let cols = oid::stored_cols_t0();
    let rels = oid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][j] == oi::row_at(sv.flat_orders, j));
    assert(rels[0][j] == proj(t[j], cols));
    assert(row_in_table(t[j], db.schema[1]));
    assert(cols[0] == 0 && cols[1] == 1 && cols[8] == 8);
    assert(proj(t[j], cols)[0] == t[j][0]);
    assert(proj(t[j], cols)[1] == t[j][1]);
    assert(proj(t[j], cols)[8] == t[j][8]);
}

/// Customer row `i`: arity, `c_custkey`.
pub proof fn lemma_customer_row(sv: StoresView, db: Database, i: int)
    requires bound_db(sv, db), 0 <= i < n_c(sv),
    ensures
        db.tables[2][i].len() == 8,
        db.tables[2][i][0] == Val::Int(cck(sv)[i] as int),
{
    lemma_table_lens(sv, db);
    cid::lemma_declared_schema();
    let t = db.tables[2];
    let cols = cid::stored_cols_t0();
    let rels = cid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][i] == ci::row_at(sv.flat_customer, i));
    assert(rels[0][i] == proj(t[i], cols));
    assert(row_in_table(t[i], db.schema[2]));
    assert(cols[0] == 0);
    assert(proj(t[i], cols)[0] == t[i][0]);
}

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(s: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] ==> a == b
}

/// PRIMARY KEY (c_custkey): the stored customer keys of a bound database are duplicate-free.
pub proof fn lemma_cust_keys_unique(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_unique(cck(sv)),
{
    lemma_table_lens(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    let ddb = declared_db(db);
    let kcols = seq![0nat];
    assert(ddb.schema[2].constraints[0] == (Constraint::Key { cols: kcols, primary: true, nulls_distinct: true }));
    assert forall|a: int, b: int| 0 <= a < cck(sv).len() && 0 <= b < cck(sv).len() && #[trigger] cck(sv)[a] == #[trigger] cck(sv)[b]
        implies a == b by {
        lemma_customer_row(sv, db, a);
        lemma_customer_row(sv, db, b);
        let ka = key_of(db.tables[2][a], kcols);
        let kb = key_of(db.tables[2][b], kcols);
        assert(ka[0] == db.tables[2][a][0]);
        assert(kb[0] == db.tables[2][b][0]);
        assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
        assert(crate::spec::equality::row_not_distinct(ka, kb));
        lemma_primary_key_identifies(ddb, 2, 0, kcols, true, a, b);
    }
}

// ------------------------------------------------------------------------------------------------ reading

/// The columns the query reads, as whole-column slices (one extent per part), and the row counts.
#[derive(Clone, Copy)]
pub struct Cols {
    pub ock: &'static [i64],
    pub offs: &'static [i64],
    pub bytes: &'static [u8],
    pub cck: &'static [i64],
    pub no: usize,
    pub nc: usize,
    pub nbytes: usize,
}

/// The slices are the stored columns of `sv`, with the shape facts every bound database gives.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.ock@ == ock(sv) && c.offs@ == cmt_col(sv).offsets && c.bytes@ == cmt_col(sv).bytes && c.cck@ == cck(sv)
    &&& c.no as int == n_o(sv) && c.nc as int == n_c(sv) && c.nbytes as int == c.bytes@.len()
    &&& parts_shape(sv)
}

/// The shape facts of the parts (they hold for every bound database, so for the parts alone).
pub proof fn lemma_shape(sv: StoresView)
    requires stores_ready(sv),
    ensures parts_shape(sv),
{
    let db = choose|db: Database| bound_db(sv, db);
    lemma_parts_shape(sv, db);
}

/// Reads every column the query needs as one extent per part.
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires old(stores)@ == sv, stores_ready(sv),
    ensures final(stores)@ == sv, cols_ok(c, sv),
{
    proof { lemma_shape(sv); }
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let ock_s = stores.flat_orders.extent_i64(oi::O_CUSTKEY, 0, no);
    let noffs = stores.flat_orders.part_len(oi::O_COMMENT_OFFSETS);
    let offs = stores.flat_orders.extent_i64(oi::O_COMMENT_OFFSETS, 0, noffs);
    let nbytes = stores.flat_orders.part_len(oi::O_COMMENT_BYTES);
    let bytes = stores.flat_orders.extent_u8(oi::O_COMMENT_BYTES, 0, nbytes);
    let nc = stores.flat_customer.part_len(ci::C_CUSTKEY);
    let cck_s = stores.flat_customer.extent_i64(ci::C_CUSTKEY, 0, nc);
    let c = Cols { ock: ock_s, offs, bytes, cck: cck_s, no, nc, nbytes };
    proof {
        assert(c.ock@ =~= ock(sv));
        assert(c.offs@ =~= cmt_col(sv).offsets);
        assert(c.bytes@ =~= cmt_col(sv).bytes);
        assert(c.cck@ =~= cck(sv));
    }
    c
}

} // verus!
