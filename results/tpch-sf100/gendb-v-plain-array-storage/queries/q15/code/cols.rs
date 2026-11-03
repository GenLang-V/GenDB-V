//! The stored columns the statement reads and their binding to every database the entry quantifies over.
//!
//! `Cols`: the four `lineitem` columns as whole stored parts (`&'static` slices of `n` rows); row `i` of the
//! normal form's projected relation is `crow(c, i)` = (suppkey, extendedprice, discount, shipdate), the numerics as
//! scale-2 coefficients and the date as days since 2000-01-01. `SuppKeys`: the `s_suppkey` column of `supplier`.
//! For each bound `db` (`lemma_bound`): `db.tables[0]` and `db.tables[5]` are the stored relations, the `lineitem`
//! rows are well formed (`li_rows_ok`) and project to `crows(c)`, and supplier row `j` has 7 values with key
//! `keys[j]`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::ast::Literal;
use crate::spec::typing::*;
use crate::spec::numeric::{pow10, abs};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::stores::StoresView;
use crate::query::param_domain;
use crate::link::query::*;
use crate::link::source::*;
use crate::schema::schema_spec;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration as ld;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_supplier::declaration as sd;
use crate::agent::normal::*;

verus! {

/// Column slices of `lineitem` (`n` rows; stored dates are days since 1970-01-01).
#[derive(Clone, Copy)]
pub struct Cols {
    pub ship: &'static [i32],
    pub supp: &'static [i64],
    pub price: &'static [i128],
    pub disc: &'static [i128],
    pub n: usize,
}

/// Days since 2000-01-01 of a stored date (days since 1970-01-01).
pub open spec fn day_of(d: i32) -> int {
    d as int - 10957
}

/// Projected row `i`: (l_suppkey, l_extendedprice, l_discount, l_shipdate).
pub open spec fn crow(c: Cols, i: int) -> Row {
    seq![
        Val::Int(c.supp@[i] as int),
        Val::Num { coeff: c.price@[i] as int, scale: 2 },
        Val::Num { coeff: c.disc@[i] as int, scale: 2 },
        Val::Date(day_of(c.ship@[i]))
    ]
}

/// All projected rows.
pub open spec fn crows(c: Cols) -> Seq<Row> {
    Seq::new(c.n as nat, |i: int| crow(c, i))
}

/// A numeric(15,2) coefficient: `|x| < 10^15`.
pub open spec fn coeff_ok(x: i128) -> bool {
    -1_000_000_000_000_000 < x < 1_000_000_000_000_000
}

/// The slices hold `n` rows, and the factors of the summed product are numeric(15,2) coefficients.
pub open spec fn cols_wf(c: Cols) -> bool {
    &&& c.ship@.len() == c.n
    &&& c.supp@.len() == c.n
    &&& c.price@.len() == c.n
    &&& c.disc@.len() == c.n
    &&& forall|i: int| 0 <= i < c.n ==> coeff_ok(#[trigger] c.price@[i])
    &&& forall|i: int| 0 <= i < c.n ==> coeff_ok(#[trigger] c.disc@[i])
}

/// Stored row `r` (16 columns) holds the column values of row `j` of `c`.
pub open spec fn row_matches(c: Cols, r: Row, j: int) -> bool {
    &&& r.len() == 16
    &&& r[2] == Val::Int(c.supp@[j] as int)
    &&& r[5] == Val::Num { coeff: c.price@[j] as int, scale: 2 }
    &&& r[6] == Val::Num { coeff: c.disc@[j] as int, scale: 2 }
    &&& r[10] == Val::Date(day_of(c.ship@[j]))
}

/// The column slices are those of the stored relation `rel`, row for row.
pub open spec fn cols_match(c: Cols, rel: Seq<Row>) -> bool {
    &&& c.n == rel.len()
    &&& c.ship@.len() == c.n
    &&& c.supp@.len() == c.n
    &&& c.price@.len() == c.n
    &&& c.disc@.len() == c.n
    &&& forall|j: int| 0 <= j < c.n ==> row_matches(c, #[trigger] rel[j], j)
}

/// The `s_suppkey` column of `supplier` (`ns` rows).
#[derive(Clone, Copy)]
pub struct SuppKeys {
    pub keys: &'static [i64],
    pub ns: usize,
}

/// The key slice is that of the stored relation `rel`, row for row (every stored row has the 7 columns).
pub open spec fn keys_match(k: SuppKeys, rel: Seq<Row>) -> bool {
    &&& k.ns == rel.len()
    &&& k.keys@.len() == k.ns
    &&& forall|j: int| 0 <= j < k.ns ==> (#[trigger] rel[j]).len() == 7 && rel[j][0] == Val::Int(k.keys@[j] as int)
}

/// What reading establishes about the stores and the parameters.
pub open spec fn read_facts(sv: StoresView, c: Cols, k: SuppKeys, lrels: Seq<Seq<Row>>, srels: Seq<Seq<Row>>, ps: Seq<Literal>) -> bool {
    &&& li::represents(sv.flat_lineitem, lrels)
    &&& cols_match(c, lrels[0])
    &&& si::represents(sv.flat_supplier, srels)
    &&& keys_match(k, srels[0])
    &&& param_domain(ps)
}

/// A numeric(15,2) value of the declared domain.
pub proof fn lemma_num15_2(v: Val)
    requires value_in_column(v, Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
    ensures num15_2(v),
{
    lemma_pow10_small();
    assert(abs(v->Num_coeff) < pow10(15));
}

/// Rows of the stored `lineitem` relation of a well-formed database are well-formed rows, and the summed factors
/// are numeric(15,2) coefficients.
pub proof fn lemma_rel_rows_ok(c: Cols, db: Database)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        cols_match(c, ld::stored_relations(db)[0]),
    ensures
        li_rows_ok(ld::stored_relations(db)[0]),
        cols_wf(c),
{
    let rel = ld::stored_relations(db)[0];
    ld::lemma_stored_relations(db);
    let cs = ld::stored_columns_t0();
    assert(cs[5] == Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false });
    assert(cs[6] == Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false });
    assert forall|j: int| 0 <= j < rel.len() implies li_row_ok(#[trigger] rel[j]) by {
        assert(row_matches(c, rel[j], j));
        assert(rel[j].len() == cs.len());
        lemma_num15_2(rel[j][5]);
        lemma_num15_2(rel[j][6]);
    }
    assert forall|j: int| 0 <= j < c.n implies coeff_ok(#[trigger] c.price@[j]) by {
        assert(row_matches(c, rel[j], j));
        assert(li_row_ok(rel[j]));
    }
    assert forall|j: int| 0 <= j < c.n implies coeff_ok(#[trigger] c.disc@[j]) by {
        assert(row_matches(c, rel[j], j));
        assert(li_row_ok(rel[j]));
    }
}

/// A bound database's `lineitem` table is the stored relation; its rows are well formed and project to the column
/// view.
pub proof fn lemma_li_rows(c: Cols, db: Database)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        cols_match(c, ld::stored_relations(db)[0]),
    ensures
        db.tables.len() == 8,
        db.tables[0] == ld::stored_relations(db)[0],
        li_rows_ok(db.tables[0]),
        proj_all(db.tables[0], src_cols()) == crows(c),
        cols_wf(c),
{
    ld::lemma_declared_schema();
    ld::lemma_stored_relations(db);
    lemma_rel_rows_ok(c, db);
    let rows = db.tables[0];
    let rel = ld::stored_relations(db)[0];
    assert(db.tables.len() == 8);
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j] == rel[j] by {
        assert(row_in_table(rows[j], db.schema[0]));
        lemma_proj_all_index(rows, ld::stored_cols_t0());
        assert(rel[j] == proj(rows[j], ld::stored_cols_t0()));
        assert(rows[j] =~= proj(rows[j], ld::stored_cols_t0()));
    }
    assert(rows =~= rel);
    assert forall|j: int| 0 <= j < c.n implies #[trigger] proj_all(rows, src_cols())[j] == crows(c)[j] by {
        assert(row_matches(c, rel[j], j));
        lemma_proj_row(rel[j]);
        assert(proj(rel[j], src_cols()) =~= crow(c, j));
    }
    assert(proj_all(rows, src_cols()) =~= crows(c));
}

/// A bound database's `supplier` table is the stored relation.
pub proof fn lemma_supp_rows(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures db.tables[5] == sd::stored_relations(db)[0],
{
    sd::lemma_declared_schema();
    sd::lemma_stored_relations(db);
    let rows = db.tables[5];
    let rel = sd::stored_relations(db)[0];
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j] == rel[j] by {
        assert(row_in_table(rows[j], db.schema[5]));
        lemma_proj_all_index(rows, sd::stored_cols_t0());
        assert(rel[j] == proj(rows[j], sd::stored_cols_t0()));
        assert(rows[j] =~= proj(rows[j], sd::stored_cols_t0()));
    }
    assert(rows =~= rel);
}

/// Every bound database holds the stored relations read, as tables 0 and 5.
pub proof fn lemma_bound(sv: StoresView, db: Database, c: Cols, k: SuppKeys, lrels: Seq<Seq<Row>>, srels: Seq<Seq<Row>>,
    ps: Seq<Literal>)
    requires bound_db(sv, db), read_facts(sv, c, k, lrels, srels, ps),
    ensures
        db.tables.len() == 8,
        db.tables[0] == lrels[0],
        db.tables[5] == srels[0],
        li_rows_ok(db.tables[0]),
        proj_all(db.tables[0], src_cols()) == crows(c),
        cols_wf(c),
        db_wf(db),
        db.schema == schema_spec(),
{
    li::lemma_represents_determines(sv.flat_lineitem, ld::stored_relations(db), lrels);
    si::lemma_represents_determines(sv.flat_supplier, sd::stored_relations(db), srels);
    lemma_li_rows(c, db);
    lemma_supp_rows(db);
}

/// Reads the four `lineitem` columns (whole parts).
pub fn read_cols(s: &mut StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (c: Cols)
    requires li::represents(old(s)@, rels),
    ensures
        final(s)@ == old(s)@,
        cols_match(c, rels[0]),
{
    let ghost parts = s@;
    let n = li::stored_rows(s, Ghost(rels));
    let ship = li::read_l_shipdate(s, 0, n, Ghost(rels));
    let supp = li::read_l_suppkey(s, 0, n, Ghost(rels));
    let price = li::read_l_extendedprice(s, 0, n, Ghost(rels));
    let disc = li::read_l_discount(s, 0, n, Ghost(rels));
    let c = Cols { ship, supp, price, disc, n };
    proof {
        assert forall|j: int| 0 <= j < c.n implies row_matches(c, #[trigger] rels[0][j], j) by {
            assert(rels[0][j] == li::row_at(parts, j));
            assert(rels[0][0 + j][2] == Val::Int(supp@[j] as int));
            assert(rels[0][0 + j][5] == Val::Num { coeff: price@[j] as int, scale: 2 });
            assert(rels[0][0 + j][6] == Val::Num { coeff: disc@[j] as int, scale: 2 });
            assert(rels[0][0 + j][10] == crate::gendb_entry::source_check::date32_val(ship@[j]));
        }
    }
    c
}

/// Reads the `s_suppkey` column (whole part).
pub fn read_keys(s: &mut StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (k: SuppKeys)
    requires si::represents(old(s)@, rels),
    ensures
        final(s)@ == old(s)@,
        keys_match(k, rels[0]),
{
    let ghost parts = s@;
    let ns = si::stored_rows(s, Ghost(rels));
    let keys = si::read_s_suppkey(s, 0, ns, Ghost(rels));
    let k = SuppKeys { keys, ns };
    proof {
        assert forall|j: int| 0 <= j < k.ns implies (#[trigger] rels[0][j]).len() == 7 && rels[0][j][0] == Val::Int(keys@[j] as int) by {
            assert(rels[0][j] == si::row_at(parts, j));
            assert(rels[0][0 + j][0] == Val::Int(keys@[j] as int));
        }
    }
    k
}

} // verus!
