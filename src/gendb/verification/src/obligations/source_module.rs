//! Generator of `gendb_source.rs`, the source module of a candidate crate (entry v3) or of a storage crate, from the
//! declared source only.
//!
//! The module defines, for the delivered columns of every source table `t{j}` (field `k` is `t{j}_f{k}`):
//! - the ghost view `SourceView`, the executable `SourceRef` and the per-table row counts `source_rows_t{j}`;
//! - `source_wf` (every field of a table has that table's row count; text offsets are well formed);
//! - the source relations `table_t{j}` / `tables` (row `i` lists the declared columns' SQLSpec values);
//! - the declared column domain `in_domain` (`spec::typing::value_in_column` of every value), its exact executable
//!   decision `source_in_domain` and the per-table lemmas `lemma_table_t{j}_in` behind it;
//! - the binding premise `source_columns_are_tables` (each relation is its database table projected onto the
//!   declared columns), `lemma_source_schema` (the declared columns are the emitted schema's, by compute) and
//!   `lemma_source_in_domain` (a `db_wf` database is inside the declared domain).
//!
//! No predicate, aggregate, ordering, capacity or bridge logic. The names above are what authors import
//! (`crate::gendb_source::*`), so they are stable. The per-table declaration functions and the schema lemma are shared
//! with the storage declaration generator (`declaration_module`), under its own names (`TableNaming`).
//!
//! **Nullable columns.** A nullable field `t{j}_f{k}` comes with its validity `t{j}_v{k}` (one `u8` per row; same row
//! count): row `i`'s value is `or_null(t{j}_v{k}[i], <value of t{j}_f{k}[i]>)`, SQL NULL exactly when the byte is 0, and
//! the value bytes under a NULL row mean nothing. Its domain and exact decision are generated here
//! (`nullable_*_values_in`, `nullable_*_column_in`, deciding each valid row with the fixed `source_check` decision on
//! a one-row slice), only when the declaration has a nullable column: the text generated for NOT NULL columns, and so
//! for every TPC-H declaration, is unchanged.

use super::candidate::ENTRY_IDENTITY;
use super::declared::{ColumnKind, DeclaredColumn, DeclaredSource, DeclaredTable, DeclaredType};
use super::storage_crate::{STORAGE_ENTRY_IDENTITY, STORAGE_ENTRY_V2_IDENTITY};
use gendb_frontend::translator::comment_text;
use std::fmt::Write as _;

/// Which fixed entry a generated source module belongs to.
pub(super) struct SourceSite {
    /// Named in the generated header.
    pub entry_identity: &'static str,
    /// The module `schema_spec` is imported from.
    pub schema_module: &'static str,
    /// The trusted assumption that states the binding premise `source_columns_are_tables`.
    pub binding_assumption: &'static str,
}

/// The source module of a candidate crate of the fixed entry v3 (the statement's own demand; the saved route).
pub(super) const STATEMENT_SOURCE: SourceSite =
    SourceSite { entry_identity: ENTRY_IDENTITY, schema_module: "crate::query", binding_assumption: "canonical_columns" };

/// The source module of a storage crate (the storage declaration's columns, the storage builder's input).
pub(super) const STORAGE_SOURCE: SourceSite =
    SourceSite { entry_identity: STORAGE_ENTRY_IDENTITY, schema_module: "crate::schema", binding_assumption: "storage_source_columns" };

/// The source module of a storage crate of the storage entry v2 (the same text as [`STORAGE_SOURCE`] but its header).
pub(super) const STORAGE_V2_SOURCE: SourceSite =
    SourceSite { entry_identity: STORAGE_ENTRY_V2_IDENTITY, schema_module: "crate::schema", binding_assumption: "storage_source_columns" };

/// Names of the per-table declaration functions `{prefix}_table_t{j}`, `{prefix}_cols_t{j}`, `{prefix}_columns_t{j}`
/// and of the lemma that proves them equal to the schema's.
pub(super) struct TableNaming {
    pub prefix: &'static str,
    pub schema_lemma: &'static str,
}

/// The names of `gendb_source.rs`.
pub(super) const SOURCE_NAMING: TableNaming = TableNaming { prefix: "source", schema_lemma: "lemma_source_schema" };

/// The imports of the generated module: SQLSpec values and typing, the fixed source/answer definitions of `link`,
/// the entry's verified domain decisions (the schema import follows, per `SourceSite`).
const IMPORTS: &str = "use vstd::prelude::*;\n\
    use crate::spec::value::*;\n\
    use crate::spec::types::{Column, SqlType, TableSchema};\n\
    use crate::spec::typing::{db_wf, value_in_column};\n\
    use crate::link::query::{proj, proj_all, text_at, text_wf};\n\
    pub use crate::link::query::{TextCol, TextView};\n\
    use crate::link::source::{cols_in_table, proj_columns, rows_in_columns};\n\
    use crate::gendb_entry::source_check::*;\n\
    pub use crate::gendb_entry::source_check::date32_val;\n";

/// `gendb_source.rs` of `source` for the entry `site` (checked by `DeclaredSource::check_deliverable` against
/// `schema_widths`, the column count of every table of the schema). `identity` names the statement or storage in the
/// header only.
pub(super) fn source_module(source: &DeclaredSource, schema_widths: &[usize], identity: &str, site: &SourceSite) -> String {
    let mut o = String::new();
    write_header(&mut o, source, identity, site);
    o.push_str(IMPORTS);
    let _ = write!(o, "use {}::schema_spec;\n\nverus! {{\n\n", site.schema_module);
    write_nullable_helpers(&mut o, source);
    write_view_types(&mut o, source);
    write_row_counts(&mut o, source);
    write_relations(&mut o, source, site);
    write_schema_lemma(&mut o, source, schema_widths, &SOURCE_NAMING);
    for (j, _) in source.tables.iter().enumerate() {
        write_table_domain_lemma(&mut o, source, j);
    }
    write_domain_decision(&mut o, source);
    write_domain_lemma(&mut o, source);
    o.push_str("} // verus!\n");
    o
}

fn write_header(o: &mut String, source: &DeclaredSource, identity: &str, site: &SourceSite) {
    let _ = writeln!(o, "// FRAMEWORK FILE, GENERATED by gendb_verification::obligations ({}) from the source", site.entry_identity);
    let _ = writeln!(o, "// declaration of {identity}. Data only: which columns of which tables are delivered, in which ABI order, with");
    let _ = writeln!(o, "// their declared SQL types. No predicate, aggregate, ordering, capacity or bridge logic.");
    for (j, t) in source.tables.iter().enumerate() {
        let _ = writeln!(o, "// Source table t{j} = {} (table id {}):", comment_text(&t.name), t.table_id);
        for (k, c) in t.columns.iter().enumerate() {
            let carrier = if c.row_count_only { ", delivered only for the row count (not in the relation)" } else { "" };
            let nullable = if c.nullable { format!(", nullable (validity t{j}_v{k})") } else { String::new() };
            let _ = writeln!(o, "//   t{j}_f{k} = {} (ordinal {}): {}{carrier}{nullable}.", comment_text(&c.name), c.ordinal, c.ty.sql_type());
        }
    }
}

/// `SourceView` (ghost), `SourceRef` (what `crate::agent::build` receives) and its view.
fn write_view_types(o: &mut String, source: &DeclaredSource) {
    let validity = if source.has_nullable() { " and the validity `tj_vk` of a nullable field (0: NULL)" } else { "" };
    let _ = writeln!(o, "/// Ghost view of the delivered columns (field k of source table j is `tj_fk`{validity}).\npub struct SourceView {{");
    for (j, k, c) in source.fields() {
        let _ = writeln!(o, "    pub t{j}_f{k}: {},", ghost_field_type(c.ty.kind()));
        if c.nullable {
            let _ = writeln!(o, "    pub t{j}_v{k}: Seq<u8>,");
        }
    }
    o.push_str("}\n\n/// The delivered columns as the entry passes them to `crate::agent::build`.\npub struct SourceRef {\n");
    for (j, k, c) in source.fields() {
        let _ = writeln!(o, "    pub t{j}_f{k}: {},", exec_field_type(c.ty.kind()));
        if c.nullable {
            let _ = writeln!(o, "    pub t{j}_v{k}: &'static [u8],");
        }
    }
    let view = source
        .fields()
        .flat_map(|(j, k, c)| {
            let value = format!("t{j}_f{k}: self.t{j}_f{k}@");
            if c.nullable { vec![value, format!("t{j}_v{k}: self.t{j}_v{k}@")] } else { vec![value] }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let _ = writeln!(
        o,
        "}}\n\nimpl View for SourceRef {{\n    type V = SourceView;\n\n    open spec fn view(&self) -> SourceView {{\n        SourceView {{ {view} }}\n    }}\n}}\n"
    );
}

fn ghost_field_type(kind: ColumnKind) -> &'static str {
    match kind {
        ColumnKind::I32 => "Seq<i32>",
        ColumnKind::I64 => "Seq<i64>",
        ColumnKind::I128 => "Seq<i128>",
        ColumnKind::Utf8 => "TextView",
    }
}

fn exec_field_type(kind: ColumnKind) -> &'static str {
    match kind {
        ColumnKind::I32 => "&'static [i32]",
        ColumnKind::I64 => "&'static [i64]",
        ColumnKind::I128 => "&'static [i128]",
        ColumnKind::Utf8 => "TextCol",
    }
}

/// `source_rows_t{j}` (field 0 of each table carries its row count; a text field has offsets = rows + 1) and
/// `source_wf`.
fn write_row_counts(o: &mut String, source: &DeclaredSource) {
    for (j, t) in source.tables.iter().enumerate() {
        let rows = if t.columns[0].ty.kind() == ColumnKind::Utf8 { format!("v.t{j}_f0.offsets.len() - 1") } else { format!("v.t{j}_f0.len() as int") };
        let _ = writeln!(o, "/// Row count of source table t{j} (from its field 0).\npub open spec fn source_rows_t{j}(v: SourceView) -> int {{\n    {rows}\n}}\n");
    }
    o.push_str("/// Every table's fields have that table's row count; text offsets are well formed (decided by the binder).\npub open spec fn source_wf(v: SourceView) -> bool {\n");
    for (j, t) in source.tables.iter().enumerate() {
        let _ = writeln!(o, "    &&& source_rows_t{j}(v) >= 0");
        for (k, c) in t.columns.iter().enumerate() {
            if c.ty.kind() == ColumnKind::Utf8 {
                let _ = writeln!(o, "    &&& text_wf(v.t{j}_f{k}, source_rows_t{j}(v))");
            } else {
                let _ = writeln!(o, "    &&& v.t{j}_f{k}.len() == source_rows_t{j}(v)");
            }
            if c.nullable {
                let _ = writeln!(o, "    &&& v.t{j}_v{k}.len() == source_rows_t{j}(v)");
            }
        }
    }
    o.push_str("}\n\n");
}

/// Per table: its id, declared ordinals and SQL columns, and its relation `table_t{j}`; then `tables`, the declared
/// domain `in_domain` and the binding premise `source_columns_are_tables`.
fn write_relations(o: &mut String, source: &DeclaredSource, site: &SourceSite) {
    for (j, t) in source.tables.iter().enumerate() {
        let relation = t.relation_columns();
        write_table_declaration(o, &SOURCE_NAMING, j, t);
        let _ = writeln!(
            o,
            "/// Source relation t{j} in delivered row order: row i lists the declared columns' VERUS_SQL values.\npub open spec fn table_t{j}(v: SourceView) -> Seq<Row> {{\n    Seq::new(source_rows_t{j}(v) as nat, |i: int| {})\n}}\n",
            row_literal(j, &relation)
        );
    }
    let relations = (0..source.tables.len()).map(|j| format!("table_t{j}(v)")).collect::<Vec<_>>().join(", ");
    let _ = writeln!(o, "/// The source relations, one per distinct source table.\npub open spec fn tables(v: SourceView) -> Seq<Seq<Row>> {{\n    seq![{relations}]\n}}\n");
    o.push_str("/// The declared column domain: every value of every relation in its declared SQL column (`value_in_column`).\npub open spec fn in_domain(ts: Seq<Seq<Row>>) -> bool {\n");
    let _ = writeln!(o, "    &&& ts.len() == {}", source.tables.len());
    for j in 0..source.tables.len() {
        let _ = writeln!(o, "    &&& rows_in_columns(ts[{j}], source_columns_t{j}())");
    }
    o.push_str("}\n\n");
    let _ = write!(
        o,
        "/// The binding premise (TCB `{}`): the delivered columns are well formed and each source relation is\n\
         /// its database table projected onto the declared columns, row for row in table order.\n\
         pub open spec fn source_columns_are_tables(v: SourceView, db: Database) -> bool {{\n    &&& source_wf(v)\n",
        site.binding_assumption
    );
    for j in 0..source.tables.len() {
        let _ = writeln!(o, "    &&& table_t{j}(v) == proj_all(db.tables[source_table_t{j}() as int], source_cols_t{j}())");
    }
    o.push_str("}\n\n");
}

/// Per table `t{j}`: its table id, the ordinals of its relation columns and their SQL columns
/// (`{prefix}_table_t{j}`, `{prefix}_cols_t{j}`, `{prefix}_columns_t{j}`).
pub(super) fn write_table_declaration(o: &mut String, naming: &TableNaming, j: usize, t: &DeclaredTable) {
    let (prefix, lemma) = (naming.prefix, naming.schema_lemma);
    let relation = t.relation_columns();
    let _ = writeln!(o, "/// Table id of {prefix} table t{j} ({}).\npub open spec fn {prefix}_table_t{j}() -> nat {{\n    {}\n}}\n", comment_text(&t.name), t.table_id);
    let ordinals: Vec<String> =
        relation.iter().enumerate().map(|(n, (_, c))| if n == 0 { format!("{}nat", c.ordinal) } else { c.ordinal.to_string() }).collect();
    let _ = writeln!(
        o,
        "/// Declared columns of the relation of t{j} (table ordinals).\npub open spec fn {prefix}_cols_t{j}() -> Seq<nat> {{\n    {}\n}}\n",
        seq_literal(&ordinals, "nat")
    );
    let _ = writeln!(
        o,
        "/// Declared SQL columns of the relation of t{j} (proved equal to the emitted schema's, `{lemma}`).\npub open spec fn {prefix}_columns_t{j}() -> Seq<Column> {{\n    {}\n}}\n",
        seq_literal(&relation.iter().map(|(_, c)| c.column()).collect::<Vec<_>>(), "Column")
    );
}

/// `{schema_lemma}`: the declared tables and columns are the schema's, each fact by compute.
pub(super) fn write_schema_lemma(o: &mut String, source: &DeclaredSource, schema_widths: &[usize], naming: &TableNaming) {
    let (prefix, lemma) = (naming.prefix, naming.schema_lemma);
    let _ = write!(o, "/// The declared tables and columns are those of the emitted schema.\npub proof fn {lemma}()\n    ensures\n");
    let _ = writeln!(o, "        schema_spec().len() == {},", schema_widths.len());
    for (j, t) in source.tables.iter().enumerate() {
        let _ = writeln!(o, "        schema_spec()[{}].columns.len() == {},", t.table_id, schema_widths[t.table_id]);
        let _ = writeln!(o, "        proj_columns(schema_spec()[{}], {prefix}_cols_t{j}()) == {prefix}_columns_t{j}(),", t.table_id);
        let _ = writeln!(o, "        cols_in_table(schema_spec()[{}], {prefix}_cols_t{j}()),", t.table_id);
    }
    o.push_str("{\n");
    let _ = writeln!(o, "    assert(schema_spec().len() == {}) by (compute);", schema_widths.len());
    for (j, t) in source.tables.iter().enumerate() {
        let tid = t.table_id;
        let relation = t.relation_columns();
        let _ = writeln!(o, "    assert(schema_spec()[{tid}].columns.len() == {}) by (compute);", schema_widths[tid]);
        for (_, c) in &relation {
            let _ = writeln!(o, "    assert(schema_spec()[{tid}].columns[{}] == {}) by (compute);", c.ordinal, c.column());
        }
        let _ = writeln!(o, "    let (cols, cs) = ({prefix}_cols_t{j}(), {prefix}_columns_t{j}());");
        o.push_str("    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] < schema_spec()[");
        let _ = writeln!(o, "{tid}].columns.len() && proj_columns(schema_spec()[{tid}], cols)[k] == cs[k] by {{");
        o.push_str(&case_split(relation.len(), "k"));
        o.push_str("    }\n");
        let _ = writeln!(o, "    assert(proj_columns(schema_spec()[{tid}], cols) =~= cs);");
    }
    o.push_str("}\n\n");
}

/// `lemma_table_t{j}_in`: the domain of relation `t{j}` is the conjunction of its columns' `*_values_in` facts
/// (which `source_check`'s `*_column_in` functions decide).
fn write_table_domain_lemma(o: &mut String, source: &DeclaredSource, j: usize) {
    let relation = source.tables[j].relation_columns();
    let conj: Vec<String> = relation
        .iter()
        .enumerate()
        .map(|(n, (k, c))| c.values_in(&format!("v.t{j}_f{k}"), &format!("v.t{j}_v{k}"), &format!("source_rows_t{j}(v)"), &format!("source_columns_t{j}()[{n}]")))
        .collect();
    let conj_text = if conj.is_empty() { "true".to_string() } else { conj.join("\n            && ") };
    let _ = writeln!(o, "/// The domain of relation t{j} is decided column by column (`gendb_entry::source_check`).");
    let _ = writeln!(o, "pub proof fn lemma_table_t{j}_in(v: SourceView)\n    requires source_wf(v),\n    ensures\n        rows_in_columns(table_t{j}(v), source_columns_t{j}()) == (\n            {conj_text}),\n{{");
    let _ = writeln!(o, "    let rows = table_t{j}(v);\n    let cs = source_columns_t{j}();");
    let _ = writeln!(o, "    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] rows[i] == {} by {{}}", row_literal(j, &relation));
    // Direction 1: a relation inside the domain has each column inside it.
    if !relation.is_empty() {
        o.push_str("    if rows_in_columns(rows, cs) {\n");
        for (n, (k, c)) in relation.iter().enumerate() {
            let rows = if c.ty.kind() == ColumnKind::Utf8 { format!("source_rows_t{j}(v)") } else { format!("v.t{j}_f{k}.len()") };
            let value = field_value(j, *k, c);
            let _ = writeln!(
                o,
                "        assert forall|i: int| 0 <= i < {rows} implies #[trigger] value_in_column({value}, cs[{n}]) by {{\n            assert(0 <= i < rows.len());\n            assert(rows[i].len() == cs.len());\n            assert(rows[i][{n}] == {value});\n        }}"
            );
        }
        o.push_str("    }\n");
    }
    // Direction 2: columns inside the domain make every row inside it.
    let _ = writeln!(o, "    if {conj_text} {{");
    o.push_str("        assert forall|i: int| 0 <= i < rows.len() implies {\n            &&& #[trigger] rows[i].len() == cs.len()\n            &&& forall|k: int| 0 <= k < cs.len() ==> value_in_column(#[trigger] rows[i][k], cs[k])\n        } by {\n");
    if !relation.is_empty() {
        o.push_str("            assert forall|k: int| 0 <= k < cs.len() implies value_in_column(#[trigger] rows[i][k], cs[k]) by {\n");
        for (n, (k, c)) in relation.iter().enumerate() {
            let _ = writeln!(
                o,
                "                {}if k == {n} {{\n                    assert(value_in_column({}, cs[{n}]));\n                }}",
                if n == 0 { "" } else { "else " },
                field_value(j, *k, c)
            );
        }
        o.push_str("            }\n");
    }
    o.push_str("        }\n    }\n}\n\n");
}

/// `source_in_domain`: the exact executable decision of `in_domain(tables(s@))`, run by `gendb_entry::abi_build`
/// before the author's builder.
fn write_domain_decision(o: &mut String, source: &DeclaredSource) {
    o.push_str("/// Decides `in_domain(tables(s@))` exactly (called by `gendb_entry::abi_build` before the author's builder).\npub fn source_in_domain(s: &SourceRef) -> (b: bool)\n    requires source_wf(s@),\n    ensures b == in_domain(tables(s@)),\n{\n    let ghost v = s@;\n");
    let mut decisions = vec![];
    for (j, t) in source.tables.iter().enumerate() {
        let relation = t.relation_columns();
        // Text columns are checked up to the table's row count `n{j}`.
        if relation.iter().any(|(_, c)| c.ty.kind() == ColumnKind::Utf8) {
            if t.columns[0].ty.kind() == ColumnKind::Utf8 {
                let _ = writeln!(o, "    let n{j}: usize = s.t{j}_f0.offsets.len() - 1;");
            } else {
                let _ = writeln!(o, "    let n{j}: usize = s.t{j}_f0.len();");
            }
        }
        for (n, (k, c)) in relation.iter().enumerate() {
            let _ = writeln!(o, "    let b{j}_{n} = {};", c.column_in(&format!("s.t{j}_f{k}"), &format!("s.t{j}_v{k}"), &format!("n{j}")));
            decisions.push(format!("b{j}_{n}"));
        }
        let _ = writeln!(o, "    proof {{\n        lemma_table_t{j}_in(v);\n    }}");
    }
    let _ = writeln!(o, "    {}\n}}\n", if decisions.is_empty() { "true".to_string() } else { decisions.join(" && ") });
}

/// `lemma_source_in_domain`: on a `db_wf` database of the emitted schema the delivered relations are inside the
/// declared domain (from `link::source::lemma_source_in_domain` per table).
fn write_domain_lemma(o: &mut String, source: &DeclaredSource) {
    o.push_str(
        "/// On a well-formed database of the emitted schema, the delivered relations are inside the declared column domain\n\
         /// (the builder never answers `InvalidInput` on real data: `gendb_entry::theorem_build_total`).\n\
         pub proof fn lemma_source_in_domain(db: Database, v: SourceView)\n    requires db.schema == schema_spec(), db_wf(db), source_columns_are_tables(v, db),\n    ensures source_wf(v), in_domain(tables(v)),\n{\n    lemma_source_schema();\n",
    );
    for j in 0..source.tables.len() {
        let _ = writeln!(o, "    crate::link::source::lemma_source_in_domain(db, source_table_t{j}(), source_cols_t{j}());");
    }
    o.push_str("}\n\n");
}

/// Row `i` of relation `t{j}`: `seq![value of each relation column]`.
fn row_literal(j: usize, relation: &[(usize, &DeclaredColumn)]) -> String {
    seq_literal(&relation.iter().map(|(k, c)| field_value(j, *k, c)).collect::<Vec<_>>(), "Val")
}

/// SQLSpec value of row `i` of field `t{j}_f{k}` (of the view `v`): `or_null` of its validity for a nullable column.
fn field_value(j: usize, k: usize, c: &DeclaredColumn) -> String {
    let value = c.ty.value(&format!("v.t{j}_f{k}"));
    if c.nullable { format!("or_null(v.t{j}_v{k}[i], {value})") } else { value }
}

/// `seq![items]`, or the typed empty sequence.
fn seq_literal(items: &[String], elem: &str) -> String {
    if items.is_empty() { format!("Seq::<{elem}>::empty()") } else { format!("seq![{}]", items.join(", ")) }
}

/// `if k == 0 {} else if k == 1 {} ...`: a proof by cases over `0 <= k < n`.
pub(super) fn case_split(n: usize, var: &str) -> String {
    let mut o = String::from("        ");
    for i in 0..n {
        let _ = write!(o, "{}if {var} == {i} {{}}", if i == 0 { "" } else { " else " });
    }
    o.push('\n');
    o
}

/// Verus text of a declared column in the generated modules.
impl DeclaredColumn {
    /// The `spec::types::Column` of the column: its type and declared nullability.
    pub(super) fn column(&self) -> String {
        format!("Column {{ ty: {}, nullable: {} }}", self.ty.sql_type(), self.nullable)
    }

    /// Spec: every value of view field `f` (validity `valid` when nullable; table rows `n`) lies in its column `col`.
    fn values_in(&self, f: &str, valid: &str, n: &str, col: &str) -> String {
        if !self.nullable {
            return self.ty.values_in(f, n, col);
        }
        match (NullableKind::of(self.ty), self.ty) {
            (_, DeclaredType::Numeric { scale, .. }) => format!("nullable_decimal_values_in({f}, {valid}, {scale}, {col})"),
            (NullableKind::Text, _) => format!("nullable_text_values_in({f}, {valid}, {n}, {col})"),
            (kind, _) => format!("nullable_{}_values_in({f}, {valid}, {col})", kind.stem()),
        }
    }

    /// Exec: decide `values_in` on the `SourceRef` field `f` (validity `valid`) with row count `n: usize`.
    fn column_in(&self, f: &str, valid: &str, n: &str) -> String {
        if !self.nullable {
            return self.ty.column_in(f, n);
        }
        let col = self.column();
        match (NullableKind::of(self.ty), self.ty) {
            (_, DeclaredType::Numeric { scale, .. }) => format!("nullable_decimal_column_in({f}, {valid}, {scale}, {col})"),
            (NullableKind::Text, _) => format!("nullable_text_column_in(&{f}, {valid}, {n}, {col})"),
            (kind, _) => format!("nullable_{}_column_in({f}, {valid}, {col})", kind.stem()),
        }
    }
}

/// The element kinds of nullable columns, each with its generated domain helpers (`nullable_<stem>_values_in`,
/// `nullable_<stem>_column_in`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum NullableKind {
    Int32,
    Int64,
    Decimal,
    Date32,
    Text,
}

impl NullableKind {
    fn of(ty: DeclaredType) -> NullableKind {
        match ty {
            DeclaredType::Int4 => Self::Int32,
            DeclaredType::Int8 => Self::Int64,
            DeclaredType::Numeric { .. } => Self::Decimal,
            DeclaredType::Date => Self::Date32,
            DeclaredType::Text | DeclaredType::Varchar { .. } | DeclaredType::Bpchar { .. } => Self::Text,
        }
    }

    fn stem(self) -> &'static str {
        match self {
            Self::Int32 => "int32",
            Self::Int64 => "int64",
            Self::Decimal => "decimal",
            Self::Date32 => "date32",
            Self::Text => "text",
        }
    }

    /// The generated domain helpers of this kind.
    fn helpers(self) -> String {
        match self {
            Self::Int32 => nullable_fixed_helpers("int32", "i32", "Val::Int({c} as int)", "int32_values_in", "int32_column_in(one, col)"),
            Self::Int64 => nullable_fixed_helpers("int64", "i64", "Val::Int({c} as int)", "int64_values_in", "int64_column_in(one, col)"),
            Self::Date32 => nullable_fixed_helpers("date32", "i32", "date32_val({c})", "date32_values_in", "date32_column_in(one, col)"),
            Self::Decimal => NULLABLE_DECIMAL.to_string(),
            Self::Text => NULLABLE_TEXT.to_string(),
        }
    }
}

/// `or_null` and the domain helpers of the kinds the declaration's nullable relation columns use (nothing without a
/// nullable column). Each decision is exact: a NULL row is in its column exactly when the column is nullable, a valid
/// row exactly when the fixed `source_check` decision accepts it as a one-row column.
fn write_nullable_helpers(o: &mut String, source: &DeclaredSource) {
    let kinds: std::collections::BTreeSet<NullableKind> =
        source.fields().filter(|(_, _, c)| c.nullable && !c.row_count_only).map(|(_, _, c)| NullableKind::of(c.ty)).collect();
    if kinds.is_empty() {
        return;
    }
    o.push_str(OR_NULL);
    for kind in kinds {
        o.push_str(&kind.helpers());
    }
}

const OR_NULL: &str = "/// Row value of a nullable column: SQL NULL when its validity byte is 0, else the value its value buffer holds.
pub open spec fn or_null(valid: u8, value: Val) -> Val {
    if valid == 0 { Val::Null } else { value }
}

";

/// The domain helpers of a nullable fixed-width column of elements `elem`, whose valid row value is `value` over the
/// element `{c}`, decided per valid row by `decide` (the fixed one-row decision of `one`, whose spec is `values_in`).
fn nullable_fixed_helpers(stem: &str, elem: &str, value: &str, values_in: &str, decide: &str) -> String {
    let at = |c: &str| value.replace("{c}", c);
    format!(
        "/// Every row of a nullable {stem} column (validity `valid`) lies in `col`.
pub open spec fn nullable_{stem}_values_in(c: Seq<{elem}>, valid: Seq<u8>, col: Column) -> bool {{
    forall|i: int| 0 <= i < c.len() ==> #[trigger] value_in_column(or_null(valid[i], {spec_value}), col)
}}

/// Decides `nullable_{stem}_values_in` exactly.
pub fn nullable_{stem}_column_in(c: &[{elem}], valid: &[u8], col: Column) -> (b: bool)
    requires
        valid@.len() == c@.len(),
    ensures
        b == nullable_{stem}_values_in(c@, valid@, col),
{{
    let mut i: usize = 0;
    while i < c.len()
        invariant
            i <= c@.len(),
            valid@.len() == c@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] value_in_column(or_null(valid@[k], {k_value}), col),
        decreases c@.len() - i,
    {{
        let ok = if valid[i] == 0 {{
            col.nullable
        }} else {{
            let one = vstd::slice::slice_subrange(c, i, i + 1);
            let b = {decide};
            proof {{
                assert(one@[0] == c@[i as int]);
                assert({values_in}(one@, col) == value_in_column({one_value}, col));
            }}
            b
        }};
        if !ok {{
            proof {{
                assert(!value_in_column(or_null(valid@[i as int], {i_value}), col));
            }}
            return false;
        }}
        i += 1;
    }}
    true
}}

",
        spec_value = at("c[i]"),
        k_value = at("c@[k]"),
        one_value = at("one@[0]"),
        i_value = at("c@[i as int]"),
    )
}

const NULLABLE_DECIMAL: &str = "/// Every row of a nullable numeric column of scale `scale` (validity `valid`) lies in `col`.
pub open spec fn nullable_decimal_values_in(c: Seq<i128>, valid: Seq<u8>, scale: nat, col: Column) -> bool {
    forall|i: int| 0 <= i < c.len() ==> #[trigger] value_in_column(or_null(valid[i], Val::Num { coeff: c[i] as int, scale }), col)
}

/// Decides `nullable_decimal_values_in` exactly.
pub fn nullable_decimal_column_in(c: &[i128], valid: &[u8], scale: u32, col: Column) -> (b: bool)
    requires
        valid@.len() == c@.len(),
        col.ty matches SqlType::Numeric { precision, .. } ==> precision <= 38,
    ensures
        b == nullable_decimal_values_in(c@, valid@, scale as nat, col),
{
    let mut i: usize = 0;
    while i < c.len()
        invariant
            i <= c@.len(),
            valid@.len() == c@.len(),
            col.ty matches SqlType::Numeric { precision, .. } ==> precision <= 38,
            forall|k: int| 0 <= k < i ==> #[trigger] value_in_column(or_null(valid@[k], Val::Num { coeff: c@[k] as int, scale: scale as nat }), col),
        decreases c@.len() - i,
    {
        let ok = if valid[i] == 0 {
            col.nullable
        } else {
            let one = vstd::slice::slice_subrange(c, i, i + 1);
            let b = decimal_column_in(one, scale, col);
            proof {
                assert(one@[0] == c@[i as int]);
                assert(decimal_values_in(one@, scale as nat, col) == value_in_column(Val::Num { coeff: one@[0] as int, scale: scale as nat }, col));
            }
            b
        };
        if !ok {
            proof {
                assert(!value_in_column(or_null(valid@[i as int], Val::Num { coeff: c@[i as int] as int, scale: scale as nat }), col));
            }
            return false;
        }
        i += 1;
    }
    true
}

";

const NULLABLE_TEXT: &str = "/// Every row `0..n` of a nullable text column (validity `valid`) lies in `col`.
pub open spec fn nullable_text_values_in(t: TextView, valid: Seq<u8>, n: int, col: Column) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] value_in_column(or_null(valid[i], Val::Text(text_at(t, i))), col)
}

/// Decides `nullable_text_values_in` exactly.
pub fn nullable_text_column_in(c: &TextCol, valid: &[u8], n: usize, col: Column) -> (b: bool)
    requires
        text_wf(c@, n as int),
        valid@.len() == n,
    ensures
        b == nullable_text_values_in(c@, valid@, n as int, col),
{
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            text_wf(c@, n as int),
            valid@.len() == n,
            forall|k: int| 0 <= k < i ==> #[trigger] value_in_column(or_null(valid@[k], Val::Text(text_at(c@, k))), col),
        decreases n - i,
    {
        let ok = if valid[i] == 0 {
            col.nullable
        } else {
            assert(0 <= c.offsets@[i as int] <= c.offsets@[i + 1] <= c.bytes@.len());
            // Offsets i and i + 1 (`text_wf`: there are n + 1 offsets).
            let offset_count = c.offsets.len();
            assert(i + 2 <= offset_count);
            let one = TextCol { offsets: vstd::slice::slice_subrange(c.offsets, i, i + 2), bytes: c.bytes };
            proof {
                assert(one@.offsets[0] == c@.offsets[i as int] && one@.offsets[1] == c@.offsets[i + 1]);
                assert(text_wf(one@, 1));
                assert(text_at(one@, 0) == text_at(c@, i as int));
            }
            let b = text_column_in(&one, 1, col);
            proof {
                assert(text_values_in(one@, 1, col) == value_in_column(Val::Text(text_at(one@, 0)), col));
            }
            b
        };
        if !ok {
            proof {
                assert(!value_in_column(or_null(valid@[i as int], Val::Text(text_at(c@, i as int))), col));
            }
            return false;
        }
        i += 1;
    }
    true
}

";

/// Verus text of a declared type in the generated module.
impl DeclaredType {
    /// The `spec::types::SqlType` constructor.
    pub(super) fn sql_type(self) -> String {
        match self {
            Self::Int4 => "SqlType::Int4".into(),
            Self::Int8 => "SqlType::Int8".into(),
            Self::Numeric { precision, scale } => format!("SqlType::Numeric {{ precision: {precision}, scale: {scale} }}"),
            Self::Date => "SqlType::Date".into(),
            Self::Text => "SqlType::Text".into(),
            Self::Varchar { max_chars } => format!("SqlType::Varchar {{ max_chars: {max_chars} }}"),
            Self::Bpchar { len } => format!("SqlType::Bpchar {{ len: {len} }}"),
        }
    }

    /// The `spec::types::Column` of a NOT NULL column of this type.
    fn not_null_column(self) -> String {
        format!("Column {{ ty: {}, nullable: false }}", self.sql_type())
    }

    /// SQLSpec value of row `i` of the view field `f` (for example `v.t0_f1`).
    fn value(self, f: &str) -> String {
        self.value_at(f, "i")
    }

    /// SQLSpec value of row `i` (an expression) of the column view `f`: a sequence of the column's native values, or a
    /// `TextView` for text.
    pub(super) fn value_at(self, f: &str, i: &str) -> String {
        match self {
            Self::Int4 | Self::Int8 => format!("Val::Int({f}[{i}] as int)"),
            Self::Numeric { scale, .. } => format!("Val::Num {{ coeff: {f}[{i}] as int, scale: {scale} }}"),
            Self::Date => format!("date32_val({f}[{i}])"),
            Self::Text | Self::Varchar { .. } | Self::Bpchar { .. } => format!("Val::Text(text_at({f}, {i}))"),
        }
    }

    /// Spec: every value of view field `f` (table rows `n`) lies in column `col` (`source_check::*_values_in`).
    fn values_in(self, f: &str, n: &str, col: &str) -> String {
        match self {
            Self::Int4 => format!("int32_values_in({f}, {col})"),
            Self::Int8 => format!("int64_values_in({f}, {col})"),
            Self::Numeric { scale, .. } => format!("decimal_values_in({f}, {scale}, {col})"),
            Self::Date => format!("date32_values_in({f}, {col})"),
            Self::Text | Self::Varchar { .. } | Self::Bpchar { .. } => format!("text_values_in({f}, {n}, {col})"),
        }
    }

    /// Exec: decide `values_in` on the `SourceRef` field `f` with row count `n: usize` (`source_check::*_column_in`).
    fn column_in(self, f: &str, n: &str) -> String {
        let col = self.not_null_column();
        match self {
            Self::Int4 => format!("int32_column_in({f}, {col})"),
            Self::Int8 => format!("int64_column_in({f}, {col})"),
            Self::Numeric { scale, .. } => format!("decimal_column_in({f}, {scale}, {col})"),
            Self::Date => format!("date32_column_in({f}, {col})"),
            Self::Text | Self::Varchar { .. } | Self::Bpchar { .. } => format!("text_column_in(&{f}, {n}, {col})"),
        }
    }
}
