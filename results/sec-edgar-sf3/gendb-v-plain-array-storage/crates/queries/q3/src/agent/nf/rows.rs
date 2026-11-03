//! What the query uses of a database bound to the stored parts: its `sub` (table 0) and `num` (table 1) relations
//! are the stored rows (`row_at` of the flat interfaces), every `num.value` coefficient is below `10^28` in absolute
//! value (numeric(28,4)), and `sub.adsh` is a key (PRIMARY KEY): two different sub rows have different adsh bytes.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::scalar::*;
use crate::spec::text::*;
use crate::spec::equality::*;
use crate::spec::constraints::*;
use crate::link::query::{proj, proj_all, text_at};
use crate::link::source::{lemma_proj_all_index, rows_in_columns};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::layout::PartView;
use crate::schema::schema_spec;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::declaration as sd;
use crate::stores::flat_num::declaration as nd;

verus! {

/// The adsh bytes of sub row `j`.
pub open spec fn sub_adsh(sp: Seq<PartView>, j: int) -> Seq<u8> {
    text_at(si::text_view(sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int), j)
}

/// The adsh bytes of num row `i`.
pub open spec fn num_adsh(np: Seq<PartView>, i: int) -> Seq<u8> {
    text_at(ni::text_view(np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int), i)
}

/// The uom bytes of num row `i`.
pub open spec fn num_uom(np: Seq<PartView>, i: int) -> Seq<u8> {
    text_at(ni::text_view(np, ni::UOM_OFFSETS as int, ni::UOM_BYTES as int), i)
}

/// The value coefficient (scale 4) of num row `i`.
pub open spec fn num_value(np: Seq<PartView>, i: int) -> int {
    ni::i128s(np[ni::VALUE as int])[i] as int
}

/// Sub row `j` has `fy = p1` (a NULL fy never qualifies).
pub open spec fn sub_fy_is(sp: Seq<PartView>, j: int, p1: int) -> bool {
    si::u8s(sp[si::FY_VALIDITY as int])[j] != 0 && si::i32s(sp[si::FY as int])[j] as int == p1
}

/// The stored facts of the parts that hold for every bound database (`lemma_bound_facts`).
pub open spec fn parts_facts(sv: StoresView, n_sub: nat, n_num: nat) -> bool {
    &&& si::parts_wf(sv.flat_sub, n_sub as int)
    &&& ni::parts_wf(sv.flat_num, n_num as int)
    &&& forall|i: int| 0 <= i < n_num ==> #[trigger] abs(num_value(sv.flat_num, i)) < pow10(28)
    &&& forall|j1: int, j2: int| 0 <= j1 < n_sub && 0 <= j2 < n_sub && j1 != j2
        ==> #[trigger] sub_adsh(sv.flat_sub, j1) != #[trigger] sub_adsh(sv.flat_sub, j2)
}

/// The `sub` and `num` relations of `db` are the stored rows.
pub open spec fn tables_are(sv: StoresView, db: Database) -> bool {
    &&& db.tables.len() == 4
    &&& forall|j: int| 0 <= j < db.tables[0].len() ==> #[trigger] db.tables[0][j] == si::row_at(sv.flat_sub, j)
    &&& forall|i: int| 0 <= i < db.tables[1].len() ==> #[trigger] db.tables[1][i] == ni::row_at(sv.flat_num, i)
}

/// A projection onto all positions `0..n` of an `n`-column row is the row.
proof fn lemma_proj_identity(r: Row, cols: Seq<nat>)
    requires cols.len() == r.len(), forall|k: int| 0 <= k < cols.len() ==> #[trigger] cols[k] == k,
    ensures proj(r, cols) == r,
{
    assert(proj(r, cols) =~= r);
}

proof fn lemma_sub_cols()
    ensures
        sd::stored_cols_t0().len() == 20,
        forall|k: int| 0 <= k < 20 ==> #[trigger] sd::stored_cols_t0()[k] == k,
{
    assert(sd::stored_cols_t0() =~= Seq::new(20, |k: int| k as nat));
}

proof fn lemma_num_cols()
    ensures
        nd::stored_cols_t0().len() == 9,
        forall|k: int| 0 <= k < 9 ==> #[trigger] nd::stored_cols_t0()[k] == k,
{
    assert(nd::stored_cols_t0() =~= Seq::new(9, |k: int| k as nat));
}

/// The sub relation of a bound database is the stored rows.
proof fn lemma_sub_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        db.tables.len() == 4,
        si::parts_wf(sv.flat_sub, db.tables[0].len() as int),
        forall|j: int| 0 <= j < db.tables[0].len() ==> #[trigger] db.tables[0][j] == si::row_at(sv.flat_sub, j),
{
    sd::lemma_declared_schema();
    lemma_sub_cols();
    let rels = sd::stored_relations(db);
    lemma_proj_all_index(db.tables[0], sd::stored_cols_t0());
    assert forall|j: int| 0 <= j < db.tables[0].len() implies #[trigger] db.tables[0][j] == si::row_at(sv.flat_sub, j) by {
        assert(row_in_table(db.tables[0][j], db.schema[0]));
        assert(rels[0][j] == si::row_at(sv.flat_sub, j));
        lemma_proj_identity(db.tables[0][j], sd::stored_cols_t0());
    }
}

/// The num relation of a bound database is the stored rows, and every value coefficient is below `10^28`.
proof fn lemma_num_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        db.tables.len() == 4,
        ni::parts_wf(sv.flat_num, db.tables[1].len() as int),
        forall|i: int| 0 <= i < db.tables[1].len() ==> #[trigger] db.tables[1][i] == ni::row_at(sv.flat_num, i),
        forall|i: int| 0 <= i < db.tables[1].len() ==> #[trigger] abs(num_value(sv.flat_num, i)) < pow10(28),
{
    nd::lemma_declared_schema();
    nd::lemma_stored_relations(db);
    lemma_num_cols();
    let rels = nd::stored_relations(db);
    lemma_proj_all_index(db.tables[1], nd::stored_cols_t0());
    assert forall|i: int| 0 <= i < db.tables[1].len() implies #[trigger] db.tables[1][i] == ni::row_at(sv.flat_num, i) by {
        assert(row_in_table(db.tables[1][i], db.schema[1]));
        assert(rels[0][i] == ni::row_at(sv.flat_num, i));
        lemma_proj_identity(db.tables[1][i], nd::stored_cols_t0());
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies #[trigger] abs(num_value(sv.flat_num, i)) < pow10(28) by {
        assert(rels[0][i] == ni::row_at(sv.flat_num, i));
        assert(rows_in_columns(rels[0], nd::stored_columns_t0()));
        assert(value_in_column(rels[0][i][7], nd::stored_columns_t0()[7]));
        assert(ni::row_at(sv.flat_num, i)[7] == ni::value_value(sv.flat_num, i));
    }
}

/// `sub.adsh` is the primary key: different sub rows have different adsh bytes.
proof fn lemma_sub_key(sv: StoresView, db: Database, j1: int, j2: int)
    requires
        bound_db(sv, db),
        0 <= j1 < db.tables[0].len(), 0 <= j2 < db.tables[0].len(), j1 != j2,
    ensures sub_adsh(sv.flat_sub, j1) != sub_adsh(sv.flat_sub, j2),
{
    lemma_sub_table(sv, db);
    let ddb = declared_db(db);
    let cols = seq![0nat];
    assert(declared_schema()[0].constraints[0] == (Constraint::Key { cols, primary: true, nulls_distinct: true }));
    assert(ddb.schema[0].constraints.len() == 1);
    assert(ddb.schema.len() == 4);
    if sub_adsh(sv.flat_sub, j1) == sub_adsh(sv.flat_sub, j2) {
        let a = sub_adsh(sv.flat_sub, j1);
        assert(db.tables[0][j1][0] == Val::Text(a));
        assert(db.tables[0][j2][0] == Val::Text(a));
        let k1 = key_of(ddb.tables[0][j1], cols);
        let k2 = key_of(ddb.tables[0][j2], cols);
        assert(k1[0] == Val::Text(a));
        assert(k2[0] == Val::Text(a));
        lemma_lex_cmp_zero(a, a);
        assert(val_not_distinct(k1[0], k2[0]));
        assert(row_not_distinct(k1, k2));
        lemma_primary_key_identifies(ddb, 0, 0, cols, true, j1, j2);
    }
}

/// Every bound database: its sub and num relations are the stored rows, and the parts facts hold.
pub proof fn lemma_bound_facts(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        tables_are(sv, db),
        parts_facts(sv, db.tables[0].len(), db.tables[1].len()),
{
    lemma_sub_table(sv, db);
    lemma_num_table(sv, db);
    assert forall|j1: int, j2: int| 0 <= j1 < db.tables[0].len() && 0 <= j2 < db.tables[0].len() && j1 != j2
        implies #[trigger] sub_adsh(sv.flat_sub, j1) != #[trigger] sub_adsh(sv.flat_sub, j2) by {
        lemma_sub_key(sv, db, j1, j2);
    }
}

} // verus!
