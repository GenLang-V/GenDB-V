//! Generator of the flat access module of a crate whose storages include generated flat storages
//! (`obligations::flat_storage`): their tables by table id and column id, so that code reading them names no table or
//! column of the schema (the general engine line's schema-name rule). One generator, two
//! sites ([`FlatAccessSite`]):
//!
//! - engine crates: `flat_tables.rs` (`crate::flat_tables`), over the storage uses (`crate::gendb_entry::stores`);
//! - storage crates built from admitted storages: `sources_flat.rs` (`crate::sources_flat`), over the sources
//!   (`crate::gendb_entry::sources`).
//!
//! The module is a crate-root module, declared by the generated crate root, because the fixed entry roots
//! (`gendb_entry.rs`) declare their own submodules and stay byte for byte. As used ([`FlatAccess::AsUsed`]) it is
//! present exactly when at least one storage of the crate is a generated flat storage ([`generated_flat_table`]), so
//! every other crate assembles byte for byte as before; the engine crates of a stage run or of a run of several
//! workloads and the storage crates of a storage family's instances always carry it ([`FlatAccess::Uniform`], below).
//! Its path is covered by no `Presence::Shared` definition of `gendb_registry`, so it
//! is in no storage's closure (unit test), and its name exists in one crate kind only: a storage interface naming
//! `crate::flat_tables` or `crate::sources_flat` fails to compile in its own storage crate or in every engine crate, as
//! the closure basis of `obligations::closure` requires.
//!
//! What it offers, each stated for a database bound to the parts (`flat_bound`: of the schema, `db_wf`, every use's
//! `stored_ok`; implied by the engine entry's `bound_db` and by the derived storage entry's `sources_bound`):
//! - `TABLE_COUNT`, `flat_table(t)` and its executable form `is_flat_table(t)`: the tables a flat storage stores;
//! - `table_rows(stores, t, db)`: `db.tables[t].len()`;
//! - `materialize_table(stores, t, db)`: every row of table `t` as interpreter rows, `view_rows == db.tables[t]`;
//! - `column_slice(stores, t, c, lo, hi, db)`: rows `lo..hi` of column `c` as stored (no copy), with
//!   `db.tables[t][lo + j][c] == slice_value(s, j)`;
//! - `lemma_flat_table_unique(sv, a, b, t)`: two bound databases have the same flat table `t`;
//! - `slice_fits(s, ty)`: `column_slice`'s variant follows the column's declared type (`Int32` integer, `Int64`
//!   bigint, `Numeric` numeric at its scale, `Date` date, `Text` text, varchar and char), so generic code can dispatch
//!   on the type;
//! - the plain-columns vocabulary as submodule `plain` (file `<module>/plain.rs`; `obligations::plain_columns`, the
//!   same text a storage interface may carry), with `flat_parts(sv, t)` (the parts of the flat storage of table `t`), `flat_layout(t)` (the
//!   part of each column, data), `flat_part_count(t)` and `lemma_flat_plain(sv, db, t)`: the flat parts hold
//!   `db.tables[t]` plainly. A storage built from a flat storage restates the flat parts with its own copy of the
//!   vocabulary (for example to keep them, `extends`), without naming the flat storage or its columns;
//! - engine crates in which every table is flat-stored: `materialize_database(stores, db)` (`edb@ == db`, the
//!   interpreter's runtime database) and `lemma_flat_database_unique(sv, a, b)` (`a == b`).
//!
//! **Nullable columns** (only in a crate where some flat-stored table has one; every other crate's module is the text
//! generated before): `nullable_column(t, c)` (data; `lemma_nullable_column`: it is the declared nullability),
//! `column_slice` requires a column that is not nullable, `nullable_column_slice(stores, t, c, lo, hi, db)` returns the
//! slice with the validity bytes (`db.tables[t][lo + j][c]` is `Val::Null` when the byte is 0, else `slice_value`),
//! `materialize_table` gives NULL rows as `EVal::Null`, and the plain-columns facts (`lemma_flat_plain`) hold for the
//! tables without a nullable column (`plain_table(t)`): the vocabulary has no validity.
//!
//! **Uniform access** ([`FlatAccess::Uniform`]; the engine crates of a stage run):
//! one shared engine source is compiled against the crate of every workload, so every such crate carries the module
//! and its nullable items whatever its storages are. Without a generated flat storage `flat_table(t)` is `false` (the
//! readers' preconditions cannot hold; their bodies are `unreached()`); without a nullable flat-stored column
//! `nullable_column(t, c)` is `false`, so `column_slice`'s precondition `!nullable_column(t, c)` holds by unfolding the
//! open definition and `nullable_column_slice` cannot be called; `plain_table(t)` is the flat-stored tables without a
//! nullable column. The same holds for `sources_flat.rs` of a storage family's instance (a derived storage whose own
//! declaration stores every column of every table, `obligations::whole_schema`; `obligations::storage_crate`): one
//! family builder text is compiled against the instance of every workload, the schemas with and without nullable
//! columns alike. There the header note is written only when it changes the text (no flat source, or no nullable
//! flat-stored column), so an instance over a schema with a nullable flat column gets the as-used module byte for byte.
//! Every other crate keeps [`FlatAccess::AsUsed`], the text generated before (unit tests with golden digests).
//!
//! Trust: none. The text is generated from the schema and the flat declarations only and is checked by Verus with
//! `--no-cheating` in the crate it belongs to, so a wrong generation fails verification. The proofs use each flat
//! storage's lossless lemma and readers and the fact that a flat storage's stored relation is its table (it declares
//! every column, in table order).

use super::declared::{ColumnKind, DeclaredColumn, DeclaredType};
use super::flat_storage::{flat_storage_of, FlatBuffer, FlatStorage};
use super::plain_columns::PLAIN_COLUMNS;
use super::query_crate::StorageUse;
use super::storage_crate::StorageName;
use crate::verus::FrameworkSource;
use gendb_frontend::ast::TableDef;
use serde::{Deserialize, Serialize};
use std::fmt::Write as _;

/// Identity of this generator, named in the generated module's header.
pub const FLAT_TABLES_GENERATOR: &str = "gendb-flat-tables-v1";

/// Which flat access module a crate carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FlatAccess {
    /// Only when some storage is a generated flat storage, with the nullable items only when some flat-stored table has
    /// a nullable column: every other crate, byte for byte as before.
    AsUsed,
    /// Always, with the nullable items always (module documentation, "Uniform access"): the engine crates of a stage
    /// run or a run of several workloads, and the storage crates of a storage family's instances.
    Uniform,
}

/// Where a flat access module is generated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlatAccessSite {
    /// An engine crate: over its storage uses.
    Engine,
    /// A storage crate built from admitted storages: over its sources.
    DerivedSources,
}

impl FlatAccessSite {
    /// The module's path relative to `src/` (a crate-root module).
    pub fn path(self) -> &'static str {
        match self {
            Self::Engine => "flat_tables.rs",
            Self::DerivedSources => "sources_flat.rs",
        }
    }

    /// The path of its submodule `plain`, the plain-columns vocabulary (`obligations::plain_columns`).
    pub fn plain_path(self) -> String {
        format!("{}/{}", self.module(), super::plain_columns::PLAIN_COLUMNS_FILE)
    }

    /// The module's name in the crate root.
    pub fn module(self) -> &'static str {
        match self {
            Self::Engine => "flat_tables",
            Self::DerivedSources => "sources_flat",
        }
    }

    /// The generated module holding `Stores`, `StoresView` and `stored_ok` at this site.
    fn stores_module(self) -> &'static str {
        match self {
            Self::Engine => "crate::gendb_entry::stores",
            Self::DerivedSources => "crate::gendb_entry::sources",
        }
    }

    /// The entry predicate a bound database satisfies at this site, which implies `flat_bound`.
    fn bound_predicate(self) -> &'static str {
        match self {
            Self::Engine => "the engine entry's `bound_db`",
            Self::DerivedSources => "the derived storage entry's `sources_bound`",
        }
    }
}

/// The table id stored by use `u` when `u` is a generated flat storage of `schema`: its declaration stores every column
/// of one table in table order, and its name and interface files are exactly the flat storage generator's output for
/// that declaration (`flat_storage_of`). `None` for every other storage.
pub fn generated_flat_table(schema: &[TableDef], u: &StorageUse<'_>) -> Option<usize> {
    let flat = flat_storage_of(u.declaration).ok()?;
    let table = &flat.declaration.tables[0];
    let width = schema.get(table.table_id)?.columns.len();
    let every_column = table.columns.len() == width && table.columns.iter().enumerate().all(|(k, c)| c.ordinal == k);
    let interface: Vec<&FrameworkSource> = flat.files.iter().filter(|f| f.path.starts_with(&flat.name.interface_prefix())).collect();
    let same_files = u.interface.len() == interface.len() && interface.iter().all(|f| u.interface.iter().any(|g| g.path == f.path && g.text == f.text));
    (every_column && flat.name == *u.name && same_files).then_some(table.table_id)
}

/// One flat-stored table of the crate: its id, its storage's name and its flat layout.
struct FlatTable<'a> {
    id: usize,
    name: &'a StorageName,
    flat: FlatStorage,
}

impl FlatTable<'_> {
    /// `crate::stores::<name>`.
    fn module(&self) -> String {
        format!("crate::stores::{}", self.name)
    }

    fn columns(&self) -> &[DeclaredColumn] {
        &self.flat.declaration.tables[0].columns
    }

    /// Whether some column of the table is nullable.
    fn has_nullable(&self) -> bool {
        self.flat.has_nullable()
    }
}

/// The flat access module of a crate over `schema` whose storages (uses or sources, in `Stores` order) are `uses`, at
/// `site`, under `access`: the module and its submodule `plain` (the plain-columns vocabulary). As used
/// ([`FlatAccess::AsUsed`]) nothing when no use is a generated flat storage; with [`FlatAccess::Uniform`] the module is
/// always generated, with its nullable items.
pub(super) fn flat_access_files_with(schema: &[TableDef], uses: &[StorageUse<'_>], site: FlatAccessSite, access: FlatAccess) -> Vec<FrameworkSource> {
    let mut tables: Vec<FlatTable<'_>> = uses
        .iter()
        .filter_map(|u| Some(FlatTable { id: generated_flat_table(schema, u)?, name: u.name, flat: flat_storage_of(u.declaration).ok()? }))
        .collect();
    let uniform = access == FlatAccess::Uniform;
    if tables.is_empty() && !uniform {
        return vec![];
    }
    tables.sort_by_key(|t| t.id);
    let complete = site == FlatAccessSite::Engine && tables.len() == schema.len();
    // Whether the nullable items are generated: always under uniform access, else when a flat-stored column is nullable.
    let nullable = uniform || tables.iter().any(FlatTable::has_nullable);
    let mut o = String::new();
    write_header(&mut o, schema, &tables, site, complete, uniform);
    o.push_str(HELPERS);
    if nullable {
        write_nullable_columns(&mut o, &tables);
    }
    for t in &tables {
        write_types_lemma(&mut o, t, nullable);
        write_table_lemma(&mut o, t);
        write_table_reader(&mut o, t);
        write_table_slice(&mut o, t);
        if t.has_nullable() {
            write_nullable_table_slice(&mut o, t);
        }
    }
    write_dispatch(&mut o, &tables, site, nullable);
    if nullable {
        write_nullable_dispatch(&mut o, &tables);
    }
    write_plain_facts(&mut o, &tables, nullable);
    if complete {
        write_database(&mut o, &tables);
    }
    o.push_str("} // verus!\n");
    vec![FrameworkSource { path: site.path().into(), text: o }, FrameworkSource { path: site.plain_path(), text: PLAIN_COLUMNS.into() }]
}

fn write_header(o: &mut String, schema: &[TableDef], tables: &[FlatTable<'_>], site: FlatAccessSite, complete: bool, uniform: bool) {
    let _ = writeln!(o, "// FRAMEWORK FILE, GENERATED by gendb_verification::obligations ({FLAT_TABLES_GENERATOR}): the generated flat storages of");
    let _ = writeln!(o, "// this crate by table id and column id (`{}`), so that code reading them names no table or column.", site.stores_module());
    o.push_str("// Data only (the schema and the flat storages' declarations); checked by Verus with the crate.\n");
    if uniform {
        write_uniform_note(o, tables, site);
    }
    for t in tables {
        let nullable: Vec<String> = t.columns().iter().enumerate().filter(|(_, c)| c.nullable).map(|(k, _)| k.to_string()).collect();
        let nullable = if nullable.is_empty() { String::new() } else { format!(", nullable columns {}", nullable.join(", ")) };
        let _ = writeln!(o, "// Table {} = `{}` ({} columns{nullable}): flat storage `{}`.", t.id, schema[t.id].name, t.columns().len(), t.name);
    }
    if tables.is_empty() {
        o.push_str("// No storage of this crate is a generated flat storage.\n");
    }
    if complete {
        o.push_str("// Every table of the schema is flat-stored: `materialize_database` and `lemma_flat_database_unique` are here.\n");
    }
    let stores = site.stores_module();
    let _ = write!(
        o,
        "use vstd::prelude::*;\nuse crate::spec::value::{{Database, Row, Val}};\nuse crate::spec::typing::{{db_wf, row_in_table, value_in_column}};\n\
         use crate::spec::datetime::date_valid;\nuse crate::spec::types::{{Column, SqlType}};\nuse crate::schema::schema_spec;\n\
         use crate::exec::value::{{view_row, ERow, EVal}};\nuse crate::gendb_entry::layout::PartView;\n\
         use crate::exec::relational::schema::{{view_rows{}}};\nuse crate::link::query::proj_all;\nuse crate::link::source::{{lemma_proj_all_index, rows_in_columns}};\n\
         use crate::gendb_entry::source_check::date32_val;\nuse crate::gendb_entry::stored::StoredParts;\nuse {stores}::{{stored_ok, Stores, StoresView}};\n",
        if complete { ", EDatabase" } else { "" }
    );
    if complete {
        o.push_str("use crate::gendb_entry::schema_exec::schema_exec;\n");
    }
    o.push_str("\n/// The plain-columns vocabulary (`gendb-plain-columns-v1`), the same text a storage interface may carry.\npub mod plain;\n");
    let flat_ids: Vec<String> = tables.iter().map(|t| format!("t == {}", t.id)).collect();
    let flat_ids = if flat_ids.is_empty() { "false".to_string() } else { flat_ids.join(" || ") };
    let _ = write!(
        o,
        "\nverus! {{\n\n/// The number of tables of the schema (table ids `0..TABLE_COUNT`, in `schema_spec()` order).\npub const TABLE_COUNT: usize = {};\n\n\
         /// The tables a generated flat storage of this crate stores: every column, as plain arrays in source row order.\n\
         pub open spec fn flat_table(t: int) -> bool {{\n    {}\n}}\n\n\
         /// `flat_table`, executable.\npub fn is_flat_table(t: usize) -> (r: bool)\n    ensures\n        r == flat_table(t as int),\n{{\n    {}\n}}\n\n\
         /// `db` is bound to the stored parts `sv`: a database of the schema, in the semantics' input domain, whose stored\n\
         /// relations the parts of every storage represent ({} implies it).\n\
         pub open spec fn flat_bound(sv: StoresView, db: Database) -> bool {{\n    &&& db.schema == schema_spec()\n    &&& db_wf(db)\n    &&& stored_ok(sv, db)\n}}\n\n",
        schema.len(),
        flat_ids,
        flat_ids,
        site.bound_predicate()
    );
}

/// The header note of a uniform module (what it is for). In an engine crate always; in a storage family's instance only
/// when uniform access changes the text (no flat source, or no nullable flat-stored column), so that an instance over a
/// schema with a nullable flat column gets the as-used module byte for byte (module documentation, "Uniform access").
fn write_uniform_note(o: &mut String, tables: &[FlatTable<'_>], site: FlatAccessSite) {
    match site {
        FlatAccessSite::Engine => {
            o.push_str("// Uniform access (an engine crate of a stage run): this module and its nullable items are here whatever the\n");
            o.push_str("// crate's storages; `flat_table(t)` is false for a table no flat storage stores, `nullable_column(t, c)` is false\n");
            o.push_str("// for a column that is not a nullable flat-stored column.\n");
        }
        FlatAccessSite::DerivedSources if !tables.iter().any(FlatTable::has_nullable) => {
            o.push_str("// Uniform access (a storage family's instance): this module and its nullable items are here whatever the sources,\n");
            o.push_str("// so one family builder text compiles in every workload's instance; `flat_table(t)` is false for a table no flat\n");
            o.push_str("// source stores, `nullable_column(t, c)` is false for a column that is not a nullable flat-stored column.\n");
        }
        FlatAccessSite::DerivedSources => {}
    }
}

/// The slice type, its view and the helpers shared by every flat table (the same text in every module).
const HELPERS: &str = r#"/// Rows `lo..hi` of one column of a flat-stored table, as its flat parts hold them (no copy).
pub enum ColumnSlice {
    /// `integer`: one value per row.
    Int32(&'static [i32]),
    /// `bigint`: one value per row.
    Int64(&'static [i64]),
    /// `numeric(p, s)`: one coefficient per row, at the scale given (value = coefficient * 10^-scale).
    Numeric(&'static [i128], u32),
    /// `date`: days since 1970-01-01, one per row.
    Date(&'static [i32]),
    /// `text`, `varchar`, `char`: the rows' offsets as stored (one more than the rows; not decreasing; the first not
    /// necessarily 0) and the bytes from the first offset to the last.
    Text(&'static [i64], &'static [u8]),
}

/// The number of rows a slice holds.
pub open spec fn slice_len(s: ColumnSlice) -> int {
    match s {
        ColumnSlice::Int32(v) => v@.len() as int,
        ColumnSlice::Int64(v) => v@.len() as int,
        ColumnSlice::Numeric(v, _) => v@.len() as int,
        ColumnSlice::Date(v) => v@.len() as int,
        ColumnSlice::Text(o, _) => o@.len() - 1,
    }
}

/// A text slice's offsets start non-negative, do not decrease and address exactly its bytes.
pub open spec fn slice_wf(s: ColumnSlice) -> bool {
    match s {
        ColumnSlice::Text(o, b) => {
            &&& o@.len() >= 1
            &&& 0 <= o@[0]
            &&& forall|x: int, y: int| 0 <= x <= y < o@.len() ==> o@[x] <= o@[y]
            &&& b@.len() == o@[o@.len() - 1] - o@[0]
        },
        _ => true,
    }
}

/// The SQL value of row `j` of a slice (row `lo + j` of the column).
pub open spec fn slice_value(s: ColumnSlice, j: int) -> Val {
    match s {
        ColumnSlice::Int32(v) => Val::Int(v@[j] as int),
        ColumnSlice::Int64(v) => Val::Int(v@[j] as int),
        ColumnSlice::Numeric(v, scale) => Val::Num { coeff: v@[j] as int, scale: scale as nat },
        ColumnSlice::Date(v) => date32_val(v@[j]),
        ColumnSlice::Text(o, b) => Val::Text(b@.subrange(o@[j] - o@[0], o@[j + 1] - o@[0])),
    }
}

/// The slice's variant follows the column's declared type `ty`.
pub open spec fn slice_fits(s: ColumnSlice, ty: SqlType) -> bool {
    match s {
        ColumnSlice::Int32(_) => ty is Int4,
        ColumnSlice::Int64(_) => ty is Int8,
        ColumnSlice::Numeric(_, scale) => ty is Numeric && ty->Numeric_scale == scale,
        ColumnSlice::Date(_) => ty is Date,
        ColumnSlice::Text(_, _) => ty is Text || ty is Varchar || ty is Bpchar,
    }
}

/// A relation whose rows have `n` columns is its own projection onto columns `0..n`.
proof fn lemma_proj_identity(rows: Seq<Row>, cols: Seq<nat>, n: nat)
    requires
        cols.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] cols[k] == k,
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] rows[i].len() == n,
    ensures
        proj_all(rows, cols) == rows,
{
    lemma_proj_all_index(rows, cols);
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, cols)[i] == rows[i] by {
        assert(proj_all(rows, cols)[i] =~= rows[i]);
    }
    assert(proj_all(rows, cols) =~= rows);
}

/// A date column value (days since 1970-01-01) as an interpreter value; the column domain keeps it in `i32`.
fn date_value(x: i32) -> (v: EVal)
    requires
        date_valid(x as int - 10957),
    ensures
        v@ == date32_val(x),
{
    EVal::Date(x - 10957)
}

/// Row `j` of a text column read as `(offsets, bytes)` (the offsets as stored, the bytes from `offsets[0]`), copied.
fn text_value(offsets: &[i64], bytes: &[u8], j: usize) -> (v: EVal)
    requires
        j + 1 < offsets@.len(),
        0 <= offsets@[0],
        forall|a: int, b: int| 0 <= a <= b < offsets@.len() ==> offsets@[a] <= offsets@[b],
        bytes@.len() == offsets@[offsets@.len() - 1] - offsets@[0],
    ensures
        v@ == Val::Text(bytes@.subrange(offsets@[j as int] - offsets@[0], offsets@[j + 1] - offsets@[0])),
{
    let last = offsets.len() - 1;
    let size = bytes.len();
    assert(offsets@[0] <= offsets@[j as int] <= offsets@[j + 1] <= offsets@[last as int]);
    let (first, start, end) = (offsets[0], offsets[j], offsets[j + 1]);
    assert(0 <= start - first <= end - first <= size);
    let lo = (start - first) as usize;
    let hi = (end - first) as usize;
    assert(lo as int == start - first && hi as int == end - first);
    let mut out: Vec<u8> = Vec::with_capacity(hi - lo);
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi <= bytes@.len(),
            out@ == bytes@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        out.push(bytes[i]);
        i += 1;
        assert(out@ =~= bytes@.subrange(lo as int, i as int));
    }
    EVal::Text(out)
}

"#;

/// `lemma_types_<id>`: the declared SQL type of every column of table `id` (by compute), and in a crate with nullable
/// columns (`nullable`) the declared nullability of each too.
fn write_types_lemma(o: &mut String, t: &FlatTable<'_>, nullable: bool) {
    let columns = t.columns();
    let _ = write!(
        o,
        "/// The declared SQL types of the columns of table {id} (`schema_spec()`, by compute).\nproof fn lemma_types_{id}()\n    ensures\n        \
         schema_spec()[{id}].columns.len() == {n},\n",
        id = t.id,
        n = columns.len()
    );
    for (k, c) in columns.iter().enumerate() {
        let _ = writeln!(o, "        schema_spec()[{}].columns[{k}].ty == ({}),", t.id, c.ty.sql_type());
        if nullable {
            let _ = writeln!(o, "        schema_spec()[{}].columns[{k}].nullable == {},", t.id, c.nullable);
        }
    }
    let _ = writeln!(o, "{{\n    assert(schema_spec()[{id}].columns.len() == {n}) by (compute);", id = t.id, n = columns.len());
    for (k, c) in columns.iter().enumerate() {
        let _ = writeln!(o, "    assert(schema_spec()[{}].columns[{k}].ty == ({})) by (compute);", t.id, c.ty.sql_type());
        if nullable {
            let _ = writeln!(o, "    assert(schema_spec()[{}].columns[{k}].nullable == {}) by (compute);", t.id, c.nullable);
        }
    }
    o.push_str("}\n\n");
}

/// `lemma_table_<id>`: the flat storage's stored relation is the database's table itself.
fn write_table_lemma(o: &mut String, t: &FlatTable<'_>) {
    let s = t.module();
    let n = t.columns().len();
    let split: String = (0..n).map(|i| format!("{}if k == {i} {{}}", if i == 0 { "" } else { " else " })).collect();
    let _ = write!(
        o,
        "/// The stored relation of flat storage `{name}` is `db`'s table {id} itself (the storage declares every column, in order).\n\
         proof fn lemma_table_{id}(db: Database)\n    requires\n        db.schema == schema_spec(),\n        db_wf(db),\n    \
         ensures\n        {s}::declaration::stored_relations(db)[0] == db.tables[{id}],\n{{\n    \
         {s}::declaration::lemma_declared_schema();\n    let cols = {s}::declaration::stored_cols_t0();\n    \
         assert forall|k: int| 0 <= k < {n} implies #[trigger] cols[k] == k by {{\n        {split}\n    }}\n    \
         let rows = db.tables[{id}];\n    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] rows[i].len() == {n} by {{\n        \
         assert(row_in_table(rows[i], db.schema[{id}]));\n    }}\n    lemma_proj_identity(rows, cols, {n});\n}}\n\n",
        name = t.name,
        id = t.id,
    );
}

/// The reader of one column of `t` for rows `lo..hi`, and the slice variant it fills.
fn column_read(t: &FlatTable<'_>, c: &DeclaredColumn) -> (String, String) {
    let s = t.module();
    match c.ty {
        DeclaredType::Int4 => (format!("{s}::interface::read_{}(st, lo, hi, Ghost(rels))", c.name), "ColumnSlice::Int32(r)".into()),
        DeclaredType::Int8 => (format!("{s}::interface::read_{}(st, lo, hi, Ghost(rels))", c.name), "ColumnSlice::Int64(r)".into()),
        DeclaredType::Numeric { scale, .. } => (format!("{s}::interface::read_{}(st, lo, hi, Ghost(rels))", c.name), format!("ColumnSlice::Numeric(r, {scale})")),
        DeclaredType::Date => (format!("{s}::interface::read_{}(st, lo, hi, Ghost(rels))", c.name), "ColumnSlice::Date(r)".into()),
        DeclaredType::Text | DeclaredType::Varchar { .. } | DeclaredType::Bpchar { .. } => {
            (format!("{s}::interface::read_{}_range(st, lo, hi, Ghost(rels))", c.name), "ColumnSlice::Text(r.0, r.1)".into())
        }
    }
}

/// What a column's reader states of row `lo + j` (its ensures, with `r` the read value).
fn column_fact(c: &DeclaredColumn, k: usize) -> String {
    let value = match c.ty {
        DeclaredType::Int4 | DeclaredType::Int8 => "Val::Int(r@[j] as int)".to_string(),
        DeclaredType::Numeric { scale, .. } => format!("Val::Num {{ coeff: r@[j] as int, scale: {scale} }}"),
        DeclaredType::Date => "date32_val(r@[j])".to_string(),
        DeclaredType::Text | DeclaredType::Varchar { .. } | DeclaredType::Bpchar { .. } => "Val::Text(r.1@.subrange(r.0@[j] - r.0@[0], r.0@[j + 1] - r.0@[0]))".to_string(),
    };
    format!("rels[0][lo as int + j][{k}] == {value}")
}

/// `read_rows_<id>`: every row of table `id` from its flat storage, proved equal to the represented relation.
fn write_table_reader(o: &mut String, t: &FlatTable<'_>) {
    let s = t.module();
    let columns = t.columns();
    let n = columns.len();
    let _ = write!(
        o,
        "/// Every row of table {id} from flat storage `{name}`, in stored order.\n#[verifier::loop_isolation(false)]\n\
         fn read_rows_{id}(st: &mut StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (rows: Vec<ERow>)\n    requires\n        \
         {s}::interface::represents(old(st)@, rels),\n        rows_in_columns(rels[0], {s}::declaration::stored_columns_t0()),\n    \
         ensures\n        final(st)@ == old(st)@,\n        view_rows(rows@) == rels[0],\n{{\n    \
         let ghost cols = {s}::declaration::stored_columns_t0();\n    assert(cols.len() == {n});\n    \
         let n = {s}::interface::stored_rows(st, Ghost(rels));\n    let mut rows: Vec<ERow> = Vec::new();\n    \
         if n == 0 {{\n        assert(view_rows(rows@) =~= rels[0]);\n        return rows;\n    }}\n",
        id = t.id,
        name = t.name,
    );
    let mut values = vec![];
    let mut dates = vec![];
    for (k, c) in columns.iter().enumerate() {
        let reader = if c.ty.kind() == ColumnKind::Utf8 { format!("read_{}_range", c.name) } else { format!("read_{}", c.name) };
        let _ = writeln!(o, "    let c{k} = {s}::interface::{reader}(st, 0, n, Ghost(rels));");
        if c.nullable {
            let _ = writeln!(o, "    let v{k} = {s}::interface::read_{}_validity(st, 0, n, Ghost(rels));", c.name);
        }
        let value = match c.ty {
            DeclaredType::Int4 => format!("EVal::Int(c{k}[i] as i64)"),
            DeclaredType::Int8 => format!("EVal::Int(c{k}[i])"),
            DeclaredType::Numeric { scale, .. } => format!("EVal::Num {{ coeff: c{k}[i], scale: {scale} }}"),
            DeclaredType::Date => {
                dates.push(k);
                format!("date_value(c{k}[i])")
            }
            DeclaredType::Text | DeclaredType::Varchar { .. } | DeclaredType::Bpchar { .. } => format!("text_value(c{k}.0, c{k}.1, i)"),
        };
        values.push(if c.nullable { format!("if v{k}[i] == 0 {{ EVal::Null }} else {{ {value} }}") } else { value });
    }
    // In the loop: the row's length (which triggers `rows_in_columns`), each reader's fact at row `i` (its trigger is
    // `rels[0][0 + j][k]`), and the column domain of every date (it keeps the value inside `i32`).
    o.push_str("    let mut i: usize = 0;\n    while i < n\n        invariant\n            i <= n,\n            view_rows(rows@) == rels[0].take(i as int),\n        decreases n - i,\n    {\n");
    let _ = writeln!(o, "        proof {{\n            assert(rels[0][i as int].len() == {n});");
    for k in 0..n {
        let _ = writeln!(o, "            assert(rels[0][0 + i as int][{k}] == rels[0][i as int][{k}]);");
    }
    for k in &dates {
        let _ = writeln!(o, "            assert(value_in_column(rels[0][i as int][{k}], cols[{k}]));");
    }
    o.push_str("        }\n");
    let _ = writeln!(o, "        let row: ERow = vec![{}];", values.join(", "));
    o.push_str(
        "        proof {\n            assert(view_row(row@) =~= rels[0][i as int]);\n        }\n        \
         rows.push(row);\n        proof {\n            assert(view_rows(rows@) =~= rels[0].take(i as int + 1));\n        }\n        i += 1;\n    }\n    \
         assert(rels[0].take(n as int) =~= rels[0]);\n    rows\n}\n\n",
    );
}

/// `slice_<id>`: rows `lo..hi` of one column of table `id`, as its flat storage holds them.
fn write_table_slice(o: &mut String, t: &FlatTable<'_>) {
    let s = t.module();
    let columns = t.columns();
    let n = columns.len();
    let not_nullable = if t.has_nullable() { format!("        !nullable_column({}, c as int),\n", t.id) } else { String::new() };
    let _ = write!(
        o,
        "/// Rows `lo..hi` of column `c` of table {id}, as flat storage `{name}` holds them.\n\
         fn slice_{id}(st: &mut StoredParts, c: usize, lo: usize, hi: usize, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (s: ColumnSlice)\n    \
         requires\n        {s}::interface::represents(old(st)@, rels),\n        c < {n},\n{not_nullable}        lo < hi <= rels[0].len(),\n    \
         ensures\n        final(st)@ == old(st)@,\n        slice_wf(s),\n        slice_len(s) == hi - lo,\n        \
         slice_fits(s, schema_spec()[{id}].columns[c as int].ty),\n        \
         forall|j: int| 0 <= j < hi - lo ==> #[trigger] rels[0][lo as int + j][c as int] == slice_value(s, j),\n{{\n    \
         proof {{\n        lemma_types_{id}();\n    }}\n",
        id = t.id,
        name = t.name,
    );
    for (k, c) in columns.iter().enumerate() {
        let (read, variant) = column_read(t, c);
        let fact = column_fact(c, k);
        let open = match (k, k + 1 == n) {
            (0, true) => "    {\n".to_string(),
            (0, false) => format!("    if c == {k} {{\n"),
            (_, true) => "    } else {\n".to_string(),
            (_, false) => format!("    }} else if c == {k} {{\n"),
        };
        o.push_str(&open);
        if c.nullable {
            // Excluded by the precondition: `nullable_slice_<id>` reads this column.
            o.push_str("        vstd::pervasive::unreached()\n");
            continue;
        }
        let _ = write!(
            o,
            "        let r = {read};\n        let s = {variant};\n        proof {{\n            \
             assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rels[0][lo as int + j][c as int] == slice_value(s, j) by {{\n                \
             assert({fact});\n            }}\n        }}\n        s\n"
        );
    }
    o.push_str("    }\n}\n\n");
}

/// The public functions that dispatch on the table id: `table_rows`, `materialize_table`, `column_slice` and
/// `lemma_flat_table_unique`. With `nullable` (the crate's nullable items are generated) `column_slice` reads the
/// columns that are not nullable. Without a flat table (uniform access) their precondition `flat_table(t)` is false:
/// the executable bodies are `unreached()` and the lemma's body is empty.
fn write_dispatch(o: &mut String, tables: &[FlatTable<'_>], site: FlatAccessSite, nullable: bool) {
    // `if t == a { .. } else if t == b { .. } else { .. }`: the last flat table is the final branch (`flat_table(t)`).
    let branch = |o: &mut String, index: usize, id: usize| {
        let open = match (index, index + 1 == tables.len()) {
            (0, true) => "    {\n".to_string(),
            (0, false) => format!("    if t == {id} {{\n"),
            (_, true) => "    } else {\n".to_string(),
            (_, false) => format!("    }} else if t == {id} {{\n"),
        };
        o.push_str(&open);
    };
    let stores_note = match site {
        FlatAccessSite::Engine => "storage uses",
        FlatAccessSite::DerivedSources => "sources",
    };
    let _ = write!(
        o,
        "/// The number of rows of flat-stored table `t`.\npub fn table_rows(stores: &Stores, t: usize, Ghost(db): Ghost<Database>) -> (n: usize)\n    \
         requires\n        flat_bound(stores@, db),\n        flat_table(t as int),\n    ensures\n        n == db.tables[t as int].len(),\n{{\n"
    );
    for (index, t) in tables.iter().enumerate() {
        branch(o, index, t.id);
        let s = t.module();
        let _ = write!(
            o,
            "        proof {{\n            lemma_table_{id}(db);\n        }}\n        {s}::interface::stored_rows(&stores.{name}, Ghost({s}::declaration::stored_relations(db)))\n",
            id = t.id,
            name = t.name
        );
    }
    close_chain(o, tables.len(), true);

    let _ = write!(
        o,
        "/// Every row of flat-stored table `t`, in stored order (the table's row order), as interpreter rows.\n\
         pub fn materialize_table(stores: &mut Stores, t: usize, Ghost(db): Ghost<Database>) -> (rows: Vec<ERow>)\n    \
         requires\n        flat_bound(old(stores)@, db),\n        flat_table(t as int),\n    \
         ensures\n        final(stores)@ == old(stores)@,\n        view_rows(rows@) == db.tables[t as int],\n{{\n"
    );
    for (index, t) in tables.iter().enumerate() {
        branch(o, index, t.id);
        let s = t.module();
        let _ = write!(
            o,
            "        proof {{\n            lemma_table_{id}(db);\n            {s}::declaration::lemma_stored_relations(db);\n        }}\n        \
             read_rows_{id}(&mut stores.{name}, Ghost({s}::declaration::stored_relations(db)))\n",
            id = t.id,
            name = t.name
        );
    }
    close_chain(o, tables.len(), true);

    // In a crate with the nullable items, `column_slice` reads the columns that are not nullable
    // (`nullable_column_slice` reads the others).
    let (not_nullable_doc, not_nullable) = if nullable {
        (" (not nullable; `nullable_column_slice` reads a nullable one)", "!nullable_column(t as int, c as int),\n        ")
    } else {
        ("", "")
    };
    let _ = write!(
        o,
        "/// Rows `lo..hi` (at least one) of column `c`{not_nullable_doc} of flat-stored table `t`, as stored (no copy): row `lo + j` of the column\n\
         /// is `slice_value(s, j)`.\n\
         pub fn column_slice(stores: &mut Stores, t: usize, c: usize, lo: usize, hi: usize, Ghost(db): Ghost<Database>) -> (s: ColumnSlice)\n    \
         requires\n        flat_bound(old(stores)@, db),\n        flat_table(t as int),\n        c < schema_spec()[t as int].columns.len(),\n        \
         {not_nullable}lo < hi <= db.tables[t as int].len(),\n    \
         ensures\n        final(stores)@ == old(stores)@,\n        slice_wf(s),\n        slice_len(s) == hi - lo,\n        \
         slice_fits(s, schema_spec()[t as int].columns[c as int].ty),\n        \
         forall|j: int| 0 <= j < hi - lo ==> #[trigger] db.tables[t as int][lo as int + j][c as int] == slice_value(s, j),\n{{\n"
    );
    for (index, t) in tables.iter().enumerate() {
        branch(o, index, t.id);
        let s = t.module();
        let _ = write!(
            o,
            "        let ghost rels = {s}::declaration::stored_relations(db);\n        proof {{\n            lemma_table_{id}(db);\n            \
             {s}::declaration::lemma_declared_schema();\n        }}\n        let s = slice_{id}(&mut stores.{name}, c, lo, hi, Ghost(rels));\n        \
             proof {{\n            assert forall|j: int| 0 <= j < hi - lo implies #[trigger] db.tables[t as int][lo as int + j][c as int] == slice_value(s, j) by {{\n                \
             assert(rels[0][lo as int + j][c as int] == slice_value(s, j));\n            }}\n        }}\n        s\n",
            id = t.id,
            name = t.name
        );
    }
    close_chain(o, tables.len(), true);

    let _ = write!(
        o,
        "/// Two databases bound to the same parts of the {stores_note} have the same flat-stored table `t` (the flat storages are\n\
         /// lossless).\npub proof fn lemma_flat_table_unique(sv: StoresView, a: Database, b: Database, t: int)\n    \
         requires\n        flat_bound(sv, a),\n        flat_bound(sv, b),\n        flat_table(t),\n    ensures\n        a.tables[t] == b.tables[t],\n{{\n"
    );
    for (index, t) in tables.iter().enumerate() {
        branch(o, index, t.id);
        let s = t.module();
        let _ = write!(
            o,
            "        {s}::interface::lemma_represents_determines(sv.{name}, {s}::declaration::stored_relations(a), {s}::declaration::stored_relations(b));\n        \
             lemma_table_{id}(a);\n        lemma_table_{id}(b);\n",
            id = t.id,
            name = t.name
        );
    }
    close_chain(o, tables.len(), false);
}

/// The end of a function whose body is one `if` chain over `branches` branches (the last one the final `else`): the
/// chain's closing brace and the function's. Without a branch (uniform access without a table the function reads) its
/// precondition cannot hold: an executable body is `unreached()`, a proof's body is empty.
fn close_chain(o: &mut String, branches: usize, executable: bool) {
    o.push_str(match (branches, executable) {
        (0, true) => "    vstd::pervasive::unreached()\n}\n\n",
        (0, false) => "}\n\n",
        _ => "    }\n}\n\n",
    });
}

/// `nullable_column` (the nullable columns of the flat-stored tables, data) and `lemma_nullable_column` (it is their
/// declared nullability), in a crate with the nullable items (some flat-stored table has a nullable column, or uniform
/// access: then without one `nullable_column` is `false`).
fn write_nullable_columns(o: &mut String, tables: &[FlatTable<'_>]) {
    let mut cases = vec![];
    for t in tables.iter().filter(|t| t.has_nullable()) {
        let columns: Vec<String> = t.columns().iter().enumerate().filter(|(_, c)| c.nullable).map(|(k, _)| format!("c == {k}")).collect();
        cases.push(format!("(t == {} && ({}))", t.id, columns.join(" || ")));
    }
    let _ = write!(
        o,
        "/// The nullable columns of the flat-stored tables (data): column `c` of table `t` may hold SQL NULL\n\
         /// (`lemma_nullable_column`: exactly the declared nullable columns).\n\
         pub open spec fn nullable_column(t: int, c: int) -> bool {{\n    {}\n}}\n\n\
         /// `nullable_column` is the declared nullability of every column of every flat-stored table.\n\
         pub proof fn lemma_nullable_column(t: int, c: int)\n    requires\n        flat_table(t),\n        0 <= c < schema_spec()[t].columns.len(),\n    \
         ensures\n        nullable_column(t, c) == schema_spec()[t].columns[c].nullable,\n{{\n",
        if cases.is_empty() { "false".to_string() } else { cases.join(" || ") }
    );
    for (index, t) in tables.iter().enumerate() {
        o.push_str(&branch_open(index, tables.len(), "t", t.id, "    "));
        let split: String = (0..t.columns().len()).map(|k| format!("{}if c == {k} {{}}", if k == 0 { "" } else { " else " })).collect();
        let _ = writeln!(o, "        lemma_types_{}();\n        {split}", t.id);
    }
    close_chain(o, tables.len(), false);
}

/// `if <var> == <id> {` / `} else if ... {` / `} else {` (the last of `count` branches is the final `else`), indented.
fn branch_open(index: usize, count: usize, var: &str, id: usize, indent: &str) -> String {
    match (index, index + 1 == count) {
        (0, true) => format!("{indent}{{\n"),
        (0, false) => format!("{indent}if {var} == {id} {{\n"),
        (_, true) => format!("{indent}}} else {{\n"),
        (_, false) => format!("{indent}}} else if {var} == {id} {{\n"),
    }
}

/// `nullable_slice_<id>`: rows `lo..hi` of a nullable column of table `id` with their validity.
fn write_nullable_table_slice(o: &mut String, t: &FlatTable<'_>) {
    let s = t.module();
    let nullable: Vec<(usize, &DeclaredColumn)> = t.columns().iter().enumerate().filter(|(_, c)| c.nullable).collect();
    let _ = write!(
        o,
        "/// Rows `lo..hi` of nullable column `c` of table {id}, as flat storage `{name}` holds them: the values and the validity.\n\
         fn nullable_slice_{id}(st: &mut StoredParts, c: usize, lo: usize, hi: usize, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (r: (ColumnSlice, &'static [u8]))\n    \
         requires\n        {s}::interface::represents(old(st)@, rels),\n        nullable_column({id}, c as int),\n        lo < hi <= rels[0].len(),\n    \
         ensures\n        final(st)@ == old(st)@,\n        slice_wf(r.0),\n        slice_len(r.0) == hi - lo,\n        r.1@.len() == hi - lo,\n        \
         slice_fits(r.0, schema_spec()[{id}].columns[c as int].ty),\n        \
         forall|j: int| 0 <= j < hi - lo ==> #[trigger] rels[0][lo as int + j][c as int] == if r.1@[j] == 0 {{ Val::Null }} else {{ slice_value(r.0, j) }},\n{{\n    \
         proof {{\n        lemma_types_{id}();\n    }}\n",
        id = t.id,
        name = t.name,
    );
    for (index, (k, c)) in nullable.iter().enumerate() {
        let (read, variant) = column_read(t, c);
        let fact = column_fact(c, *k);
        o.push_str(&branch_open(index, nullable.len(), "c", *k, "    "));
        let _ = write!(
            o,
            "        let r = {read};\n        let s = {variant};\n        let v = {s}::interface::read_{name}_validity(st, lo, hi, Ghost(rels));\n        proof {{\n            \
             assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rels[0][lo as int + j][c as int] == if v@[j] == 0 {{ Val::Null }} else {{ slice_value(s, j) }} by {{\n                \
             assert(rels[0][lo as int + j][{k}] is Null || {fact});\n                \
             assert((rels[0][lo as int + j][{k}] is Null) == (v@[j] == 0));\n            }}\n        }}\n        (s, v)\n",
            name = c.name,
        );
    }
    o.push_str("    }\n}\n\n");
}

/// `nullable_column_slice`: the public reader of a nullable column, dispatching on the table id (without a nullable
/// flat-stored column, uniform access, its precondition `nullable_column(t, c)` cannot hold).
fn write_nullable_dispatch(o: &mut String, tables: &[FlatTable<'_>]) {
    let nullable: Vec<&FlatTable<'_>> = tables.iter().filter(|t| t.has_nullable()).collect();
    o.push_str(
        "/// Rows `lo..hi` (at least one) of nullable column `c` of flat-stored table `t`, as stored (no copy): the values `r.0`\n\
         /// and the validity `r.1`; row `lo + j` of the column is SQL NULL when `r.1[j] == 0`, else `slice_value(r.0, j)`.\n\
         pub fn nullable_column_slice(stores: &mut Stores, t: usize, c: usize, lo: usize, hi: usize, Ghost(db): Ghost<Database>) -> (r: (ColumnSlice, &'static [u8]))\n    \
         requires\n        flat_bound(old(stores)@, db),\n        nullable_column(t as int, c as int),\n        lo < hi <= db.tables[t as int].len(),\n    \
         ensures\n        final(stores)@ == old(stores)@,\n        slice_wf(r.0),\n        slice_len(r.0) == hi - lo,\n        r.1@.len() == hi - lo,\n        \
         slice_fits(r.0, schema_spec()[t as int].columns[c as int].ty),\n        \
         forall|j: int| 0 <= j < hi - lo ==> #[trigger] db.tables[t as int][lo as int + j][c as int] == if r.1@[j] == 0 { Val::Null } else { slice_value(r.0, j) },\n{\n",
    );
    for (index, t) in nullable.iter().enumerate() {
        o.push_str(&branch_open(index, nullable.len(), "t", t.id, "    "));
        let s = t.module();
        let _ = write!(
            o,
            "        let ghost rels = {s}::declaration::stored_relations(db);\n        proof {{\n            lemma_table_{id}(db);\n            \
             {s}::declaration::lemma_declared_schema();\n        }}\n        let r = nullable_slice_{id}(&mut stores.{name}, c, lo, hi, Ghost(rels));\n        \
             proof {{\n            assert forall|j: int| 0 <= j < hi - lo implies #[trigger] db.tables[t as int][lo as int + j][c as int]\n                \
             == if r.1@[j] == 0 {{ Val::Null }} else {{ slice_value(r.0, j) }} by {{\n                \
             assert(rels[0][lo as int + j][c as int] == if r.1@[j] == 0 {{ Val::Null }} else {{ slice_value(r.0, j) }});\n            }}\n        }}\n        r\n",
            id = t.id,
            name = t.name
        );
    }
    close_chain(o, nullable.len(), true);
}

/// The first part of every column of `t` (text: its offsets part; its bytes part follows), in column order.
fn layout(t: &FlatTable<'_>) -> Vec<usize> {
    let mut at = vec![];
    for (index, part) in t.flat.parts.iter().enumerate() {
        if matches!(part.buffer, FlatBuffer::Values | FlatBuffer::Offsets) {
            at.push(index);
        }
    }
    at
}

/// `flat_parts`, `flat_part_count`, `flat_part_of`, `flat_layout`, `lemma_flat_plain` and the per-table
/// `lemma_plain_<id>`: what every flat storage's parts hold, in the plain-columns vocabulary (submodule `plain`). With
/// the nullable items (`nullable`) `lemma_flat_plain` holds for `plain_table(t)`, the tables without a nullable column.
fn write_plain_facts(o: &mut String, tables: &[FlatTable<'_>], nullable: bool) {
    let plain: Vec<&FlatTable<'_>> = tables.iter().filter(|t| !t.has_nullable()).collect();
    let chain = |value: &dyn Fn(&FlatTable<'_>) -> String, otherwise: &str| -> String {
        let mut text = String::new();
        for t in tables {
            let _ = write!(text, "if t == {} {{ {} }} else ", t.id, value(t));
        }
        let _ = write!(text, "{{ {otherwise} }}");
        text
    };
    let _ = write!(
        o,
        "/// The parts of the flat storage of table `t` (empty for a table no flat storage of this crate stores).\n\
         pub open spec fn flat_parts(sv: StoresView, t: int) -> Seq<PartView> {{\n    {}\n}}\n\n\
         /// The number of parts of the flat storage of table `t`.\npub open spec fn flat_part_count(t: int) -> int {{\n    {}\n}}\n\n",
        chain(&|t| format!("sv.{}", t.name), "Seq::empty()"),
        chain(&|t| t.flat.parts.len().to_string(), "0")
    );
    let part_of = |t: &FlatTable<'_>| -> String {
        let at = layout(t);
        let mut text = String::new();
        for (k, p) in at.iter().enumerate() {
            let _ = write!(text, "if c == {k} {{ {p} }} else ");
        }
        text.push_str("{ 0 }");
        text
    };
    let _ = write!(
        o,
        "/// The part that holds column `c` of table `t` in its flat storage (text: its offsets; its bytes part follows).\n\
         pub open spec fn flat_part_of(t: int, c: int) -> int {{\n    {}\n}}\n\n\
         /// The part of every column of table `t` in its flat storage, in column order (data for `plain::plain_columns`).\n\
         pub open spec fn flat_layout(t: int) -> Seq<int> {{\n    {}\n}}\n\n",
        chain(&|t| part_of(t), "0"),
        chain(&|t| format!("Seq::new({}, |c: int| flat_part_of({}, c))", t.columns().len(), t.id), "Seq::empty()")
    );
    for t in &plain {
        write_plain_lemma(o, t);
    }
    let plain_requires = if nullable {
        let ids: Vec<String> = plain.iter().map(|t| format!("t == {}", t.id)).collect();
        let _ = write!(
            o,
            "/// The flat-stored tables without a nullable column: their parts hold them plainly (`lemma_flat_plain`).\n\
             pub open spec fn plain_table(t: int) -> bool {{\n    {}\n}}\n\n",
            if ids.is_empty() { "false".to_string() } else { ids.join(" || ") }
        );
        "        plain_table(t),\n"
    } else {
        ""
    };
    let _ = write!(
        o,
        "/// The parts of the flat storage of table `t` hold `db.tables[t]` plainly: column `c` from part\n\
         /// `flat_layout(t)[c]`, typed by the declared column types (`plain::plain_columns`).\n\
         pub proof fn lemma_flat_plain(sv: StoresView, db: Database, t: int)\n    requires\n        flat_bound(sv, db),\n        flat_table(t),\n{plain_requires}    \
         ensures\n        flat_parts(sv, t).len() == flat_part_count(t),\n        \
         plain::plain_columns(flat_parts(sv, t), db.tables[t], schema_spec()[t].columns, flat_layout(t)),\n{{\n"
    );
    for (index, t) in plain.iter().enumerate() {
        let open = match (index, index + 1 == plain.len()) {
            (0, true) => "    {\n".to_string(),
            (0, false) => format!("    if t == {} {{\n", t.id),
            (_, true) => "    } else {\n".to_string(),
            (_, false) => format!("    }} else if t == {} {{\n", t.id),
        };
        o.push_str(&open);
        let _ = writeln!(o, "        lemma_plain_{}(sv, db);", t.id);
    }
    // Without a plain table the precondition `plain_table(t)` is false and the body is empty.
    close_chain(o, plain.len(), false);
}

/// `lemma_plain_<id>`: the parts of table `id`'s flat storage hold the table plainly (from its `represents`).
fn write_plain_lemma(o: &mut String, t: &FlatTable<'_>) {
    let s = t.module();
    let columns = t.columns();
    let at = layout(t);
    let _ = write!(
        o,
        "/// The parts of flat storage `{name}` hold `db.tables[{id}]` plainly.\nproof fn lemma_plain_{id}(sv: StoresView, db: Database)\n    \
         requires\n        flat_bound(sv, db),\n    ensures\n        sv.{name}.len() == {count},\n        \
         plain::plain_columns(sv.{name}, db.tables[{id}], schema_spec()[{id}].columns, flat_layout({id})),\n{{\n    \
         let parts = sv.{name};\n    let rels = {s}::declaration::stored_relations(db);\n    let rows = db.tables[{id}];\n    \
         let cols = schema_spec()[{id}].columns;\n    let at = flat_layout({id});\n    lemma_table_{id}(db);\n    lemma_types_{id}();\n    \
         assert({s}::interface::represents(parts, rels));\n    \
         assert forall|i: int| 0 <= i < rows.len() implies #[trigger] rows[i].len() == cols.len() by {{\n        \
         assert(rows[i] == {s}::interface::row_at(parts, i));\n    }}\n    \
         assert forall|k: int| 0 <= k < cols.len() implies #[trigger] plain::plain_column(parts, at[k], cols[k].ty, rows, k) by {{\n",
        name = t.name,
        id = t.id,
        count = t.flat.parts.len(),
    );
    for (k, c) in columns.iter().enumerate() {
        let p = at[k];
        let open = match (k, k + 1 == columns.len()) {
            (0, true) => "        {\n".to_string(),
            (0, false) => format!("        if k == {k} {{\n"),
            (_, true) => "        } else {\n".to_string(),
            (_, false) => format!("        }} else if k == {k} {{\n"),
        };
        o.push_str(&open);
        let _ = writeln!(o, "            assert(at[{k}] == {p});");
        let value = match c.ty {
            DeclaredType::Int4 => Some(("I32", format!("Val::Int(parts[{p}]->I32_0[i] as int)"))),
            DeclaredType::Date => Some(("I32", format!("date32_val(parts[{p}]->I32_0[i])"))),
            DeclaredType::Int8 => Some(("I64", format!("Val::Int(parts[{p}]->I64_0[i] as int)"))),
            DeclaredType::Numeric { scale, .. } => Some(("I128", format!("Val::Num {{ coeff: parts[{p}]->I128_0[i] as int, scale: {scale} }}"))),
            DeclaredType::Text | DeclaredType::Varchar { .. } | DeclaredType::Bpchar { .. } => None,
        };
        match value {
            Some((variant, value)) => {
                let _ = write!(
                    o,
                    "            assert(parts[{p}] is {variant});\n            \
                     assert forall|i: int| 0 <= i < rows.len() implies #[trigger] rows[i][{k}] == {value} by {{\n                \
                     assert(rows[i] == {s}::interface::row_at(parts, i));\n            }}\n            \
                     assert(plain::plain_values(parts[{p}], cols[{k}].ty, rows, {k}));\n"
                );
            }
            None => {
                let _ = write!(
                    o,
                    "            assert(parts[{p}] is I64 && parts[{q}] is U8);\n            \
                     assert(plain::plain_text(parts, {p}) == {s}::interface::text_view(parts, {p}, {q}));\n            \
                     assert forall|i: int| 0 <= i < rows.len() implies #[trigger] rows[i][{k}] == Val::Text(crate::link::query::text_at(plain::plain_text(parts, {p}), i)) by {{\n                \
                     assert(rows[i] == {s}::interface::row_at(parts, i));\n            }}\n",
                    q = p + 1
                );
            }
        }
    }
    o.push_str("        }\n    }\n}\n\n");
}

/// `materialize_database` and `lemma_flat_database_unique` (engine crates in which every table is flat-stored).
fn write_database(o: &mut String, tables: &[FlatTable<'_>]) {
    let first = tables[0].module();
    o.push_str(
        "/// Every table, as the interpreter's runtime database (`crate::exec::relational::schema::EDatabase`): `edb@ == db`.\n\
         pub fn materialize_database(stores: &mut Stores, Ghost(db): Ghost<Database>) -> (edb: EDatabase)\n    \
         requires\n        flat_bound(old(stores)@, db),\n    ensures\n        final(stores)@ == old(stores)@,\n        edb@ == db,\n{\n",
    );
    for t in tables {
        let _ = writeln!(o, "    let t{id} = materialize_table(stores, {id}, Ghost(db));", id = t.id);
    }
    let names: Vec<String> = tables.iter().map(|t| format!("t{}", t.id)).collect();
    let _ = write!(
        o,
        "    let tables: Vec<Vec<ERow>> = vec![{}];\n    let edb = EDatabase {{ schema: schema_exec(), tables }};\n    proof {{\n        \
         {first}::declaration::lemma_declared_schema();\n        assert(edb@.tables =~= db.tables);\n        assert(edb@ == db);\n    }}\n    edb\n}}\n\n",
        names.join(", ")
    );
    o.push_str(
        "/// Two databases bound to the same parts are equal: every table is flat-stored, and the flat storages are lossless.\n\
         pub proof fn lemma_flat_database_unique(sv: StoresView, a: Database, b: Database)\n    \
         requires\n        flat_bound(sv, a),\n        flat_bound(sv, b),\n    ensures\n        a == b,\n{\n",
    );
    for t in tables {
        let _ = writeln!(o, "    lemma_flat_table_unique(sv, a, b, {});", t.id);
    }
    let _ = write!(o, "    {first}::declaration::lemma_declared_schema();\n    assert(a.tables =~= b.tables);\n}}\n\n");
}
