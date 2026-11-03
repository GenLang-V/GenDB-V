//! A storage author's candidate manifest (`verus-storage.json`): the storage's name and stored columns, its crate
//! directory, the meaning of each stored part, the author's layout explanation, its stored-data policy declaration,
//! its declared modules, its compiler choice and whether its builder assumes the run's declared integrity constraints
//! (`uses_declared_constraints`). Workload and query authors write the same manifest.
//!
//! A storage crate has two author roots (`src/stores/<name>/interface/`, `src/builder/`); every other file is
//! framework text regenerated at freeze (`gendb_verification::obligations::storage_crate_files`). The stored columns
//! become the storage declaration with the statements' delivery rules (`DeclaredSource::for_storage`): columns of an ABI
//! type, a nullable one with its validity; a table listed with no column is stored through a row-count carrier.
//!
//! `modules` is optional: when it is empty the freeze derives it from the files under the two roots
//! ([`derived_module`]: `interface/mod.rs` declares `represents`, `builder/mod.rs` declares `build`, other interface
//! files are readers, other builder files helpers) and the checked build lists each module's items from Verus's own
//! report, so a hand-written list can no longer go stale. `data_policy` is the per-part declaration of the stored-data
//! policy ([`PartPolicy`]); the free-text form of earlier manifests is still read but is not a declaration under
//! `physical_only`.

use crate::query::candidate::CompilerChoice;
use gendb_frontend::ast::TableDef;
use gendb_verification::admission::AdmissionError;
use gendb_verification::obligations::{DeclaredSource, StorageName};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The manifest's `tables[].columns` description in a run whose dataset schema has a nullable column.
pub const NULLABLE_STORED_COLUMNS: &str = "stored columns; a nullable column is delivered to the builder with its validity (gendb_source.rs t{j}_v{k}, one byte per row, 0: NULL) and its NULL rows are Val::Null in stored_relations; empty: the table is stored through a row-count carrier";

/// Conventional file name of a storage manifest.
pub const STORAGE_MANIFEST_FILE: &str = "verus-storage.json";
/// The storage items the fixed storage entry uses: the interface's relation and the builder.
pub const REQUIRED_STORAGE_ITEMS: [(&str, &str); 2] = [("interface", "represents"), ("builder", "build")];

/// Declared role of one author file of a storage crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StorageModuleRole {
    /// `stores/<name>/interface/mod.rs`: declares `represents` (copied into every query crate that reads the storage).
    Interface,
    /// An interface file with readers over `StoredParts` (copied into query crates, compiled into served queries).
    Reader,
    /// `builder/mod.rs`: declares `build` (storage crate only).
    Builder,
    /// Any other interface or builder file.
    Helper,
}

/// One author file of a storage crate, relative to the crate's `src/`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StorageModule {
    /// `stores/<name>/interface/**.rs` or `builder/**.rs`.
    pub file: String,
    pub role: StorageModuleRole,
    /// Functions this module contributes, named as Verus reports them relative to the module (`name`, `Type::method`).
    pub items: Vec<String>,
}

/// The derived declaration of the author file `file` (relative to `src/`) of storage `name`'s crate: its role by
/// position, with the item the fixed storage entry uses for the two roots. Every other item is taken from Verus's
/// report after the whole-crate run (`storage::build`).
pub fn derived_module(name: &str, file: &str) -> StorageModule {
    let interface_root = format!("stores/{name}/interface/mod.rs");
    let (role, items) = if file == interface_root {
        (StorageModuleRole::Interface, vec![REQUIRED_STORAGE_ITEMS[0].1.to_string()])
    } else if file == "builder/mod.rs" {
        (StorageModuleRole::Builder, vec![REQUIRED_STORAGE_ITEMS[1].1.to_string()])
    } else if file.starts_with("builder/") {
        (StorageModuleRole::Helper, vec![])
    } else {
        (StorageModuleRole::Reader, vec![])
    };
    StorageModule { file: file.to_string(), role, items }
}

/// Which kind of stored data one part is (`storage::policy`). Under `physical_only` (revision 2) the
/// allowed kinds are `base_payload`, `index_keys`, `permutation`, `own_skip_metadata` and `layout_offsets_counts`;
/// `query_derived_values` is allowed only under `unrestricted`. `own_source_values` and `own_index` are the revision-1
/// kinds of earlier registrations (an own-table copy or covering index could carry a second payload copy): still read
/// from records, refused in new declarations under `physical_only`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PartKind {
    /// Part of the one stored copy of `columns`' values of the table: any order (possibly co-clustered with another
    /// table's order, every row kept), partitioning or lossless encoding. One copy may span several parts of the same
    /// storage (codes, dictionary, offsets, values; disjoint partitions), each declaring the column.
    BasePayload,
    /// An index of the table: the values of its key `columns` -> the table's own row positions or ranges, holding no
    /// other column's values (no covering payload).
    IndexKeys,
    /// Row positions only, into the one stored copy of the table: another order (`columns`: the order's keys, whose
    /// values are not stored here).
    Permutation,
    /// Skip metadata over the table's own rows or blocks (min/max zone maps, Bloom or trigram filters, statistics).
    OwnSkipMetadata,
    /// Run offsets, row counts or block offsets that describe the representation itself.
    LayoutOffsetsCounts,
    /// Anything else (query-derived values); refused under `physical_only`.
    QueryDerivedValues,
    /// Revision 1: the table's own source values in any layout (could be a second, re-sorted copy).
    OwnSourceValues,
    /// Revision 1: an own-table index, optionally covering own values.
    OwnIndex,
}

impl PartKind {
    /// The kinds a new declaration may use (the author schema); `query_derived_values` only under `unrestricted`.
    pub const CURRENT: [PartKind; 6] =
        [PartKind::BasePayload, PartKind::IndexKeys, PartKind::Permutation, PartKind::OwnSkipMetadata, PartKind::LayoutOffsetsCounts, PartKind::QueryDerivedValues];

    pub fn name(self) -> &'static str {
        match self {
            PartKind::BasePayload => "base_payload",
            PartKind::IndexKeys => "index_keys",
            PartKind::Permutation => "permutation",
            PartKind::OwnSkipMetadata => "own_skip_metadata",
            PartKind::LayoutOffsetsCounts => "layout_offsets_counts",
            PartKind::QueryDerivedValues => "query_derived_values",
            PartKind::OwnSourceValues => "own_source_values",
            PartKind::OwnIndex => "own_index",
        }
    }

    /// A revision-1 kind (earlier registrations only).
    pub fn is_revision_1(self) -> bool {
        matches!(self, PartKind::OwnSourceValues | PartKind::OwnIndex)
    }

    /// Whether a declaration of this kind must name its columns (the payload or key columns).
    pub fn names_columns(self) -> bool {
        matches!(self, PartKind::BasePayload | PartKind::IndexKeys)
    }
}

/// The stored-data declaration of one part: the one table whose rows it is computed from, its kind, the columns it
/// holds or describes, and why.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PartPolicy {
    /// Part index (0-based, the builder's part order).
    pub part: usize,
    pub table: String,
    pub kind: PartKind,
    /// Stored columns of `table`: whose values the part holds (`base_payload`), its key columns (`index_keys`), or the
    /// columns it orders or summarizes (`permutation`, `own_skip_metadata`, `layout_offsets_counts`; optional there).
    /// Absent in revision-1 records; not serialized when empty.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub columns: Vec<String>,
    pub why: String,
}

/// `data_policy` of a manifest: one [`PartPolicy`] per part, or the free text of earlier manifests (read, recorded,
/// but no declaration under `physical_only`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum DataPolicy {
    Parts(Vec<PartPolicy>),
    Text(String),
}

impl Default for DataPolicy {
    fn default() -> Self {
        DataPolicy::Text(String::new())
    }
}

impl DataPolicy {
    /// Whether nothing is declared (absent, empty text or an empty list).
    pub fn is_empty(&self) -> bool {
        match self {
            DataPolicy::Parts(parts) => parts.is_empty(),
            DataPolicy::Text(text) => text.trim().is_empty(),
        }
    }
}

/// One stored table: its name and stored column names (empty: stored through a row-count carrier).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StoredTable {
    pub table: String,
    pub columns: Vec<String>,
}

/// The admitted storages a storage is built from: its builder reads their stored parts through
/// their readers (fixed derived storage entry), never the source data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BuiltFrom {
    /// The admitted source storages, in the builder's use order (the fields of `gendb_entry::stores::Stores`).
    pub sources: Vec<SourceStorage>,
    /// Optional: the source whose parts this storage keeps unchanged, before its builder's parts (they are linked, not
    /// copied or rebuilt; a storage extended by new parts).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub extends: Option<String>,
}

/// One admitted source storage: its name and admitted package id (contract storages.json `use_as`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceStorage {
    pub name: String,
    pub admitted: gendb_artifacts::ContentId,
}

impl BuiltFrom {
    /// The index of the extended source, checked to be one of the sources.
    pub fn extends_index(&self) -> Result<Option<usize>, AdmissionError> {
        match &self.extends {
            None => Ok(None),
            Some(name) => self
                .sources
                .iter()
                .position(|s| &s.name == name)
                .map(Some)
                .ok_or_else(|| AdmissionError::refusal(format!("built_from.extends names {name}, which is not one of its sources"))),
        }
    }
}

/// The author's explanation of its stored organization (descriptive; recorded, never interpreted).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StorageLayout {
    /// What the parts hold and how they are organized (blocks, order, encodings, indexes, metadata).
    pub summary: String,
    /// Units of the stored values and offsets (for example days since 1970-01-01, rows, bytes).
    pub units: String,
    /// Why this organization: the size, build, read and query costs you measured or expect, and what you traded.
    pub choice: String,
}

/// `verus-storage.json`. `crate_dir` is relative to the manifest's directory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StorageManifest {
    pub format_version: u32,
    pub name: String,
    pub crate_dir: String,
    pub tables: Vec<StoredTable>,
    /// One label per part the builder returns, in order.
    pub parts: Vec<String>,
    pub layout: StorageLayout,
    /// Per part, the table it is computed from and which kind of stored data it is under the run's storage policy
    /// (`storage::policy`; required under `physical_only` and checked against the parts and stored tables, recorded
    /// with the registration; whether it is true is decided by review).
    #[serde(default)]
    pub data_policy: DataPolicy,
    /// Every author file once; empty: derived from the files under the two roots ([`derived_module`]).
    #[serde(default)]
    pub modules: Vec<StorageModule>,
    #[serde(default)]
    pub compiler: Option<CompilerChoice>,
    #[serde(default)]
    pub notes: String,
    /// Whether the builder assumes the run's declared integrity constraints (storage entry v2: `source_witnessed`). The
    /// declarations are the run's, never chosen here; opting in only narrows where the storage applies, to runs with
    /// exactly that declaration set, and is refused in a run that declares none (`declared_constraints_unavailable`).
    /// Absent means `false` and is not serialized, so every existing manifest record is unchanged.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub uses_declared_constraints: bool,
    /// The admitted storages this storage is built from (fixed derived storage entry); absent: built from the source
    /// columns of its declared tables (storage entry v1/v2). Absent is not serialized.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub built_from: Option<BuiltFrom>,
}

impl StorageManifest {
    /// The example written into author workspaces.
    pub fn example() -> Self {
        Self {
            format_version: 1,
            name: "<storage name: lowercase Rust identifier>".into(),
            crate_dir: "crate".into(),
            tables: vec![StoredTable { table: "<table>".into(), columns: vec!["<column>".into()] }],
            parts: vec!["<meaning of part 0>".into()],
            layout: StorageLayout {
                summary: "<what the parts hold and how they are organized>".into(),
                units: "<units of stored values and offsets>".into(),
                choice: "<why: measured or expected stored size, build, read and query cost; reuse is a valid choice>".into(),
            },
            data_policy: DataPolicy::Parts(vec![PartPolicy {
                part: 0,
                table: "<the one table whose rows part 0 is computed from>".into(),
                kind: PartKind::BasePayload,
                columns: vec!["<column whose one stored copy part 0 holds>".into()],
                why: "<why it holds no query computation and no second copy of a column>".into(),
            }]),
            modules: vec![],
            compiler: Some(CompilerChoice::default()),
            notes: String::new(),
            uses_declared_constraints: false,
            built_from: None,
        }
    }

    /// [`Self::schema`] (or [`Self::schema_with_declared_constraints`]) for a dataset schema with a nullable column:
    /// `tables[].columns` says how a nullable stored column is delivered (the text of a schema of NOT NULL columns is
    /// unchanged).
    pub fn with_nullable_columns(mut schema: Value) -> Value {
        schema["properties"]["tables"]["items"]["properties"]["columns"]["description"] = json!(NULLABLE_STORED_COLUMNS);
        schema
    }

    /// JSON schema of the manifest (author contract).
    pub fn schema() -> Value {
        json!({"type":"object","additionalProperties":false,"required":["format_version","name","crate_dir","tables","parts","layout"],
            "properties":{
                "format_version":{"const":1},
                "name":{"type":"string","pattern":"^[a-z][a-z0-9_]{0,63}$","description":"the storage's module stores::<name> and its Stores field in query crates; not a Rust keyword. A new admitted package of an existing name becomes that name's newest version"},
                "crate_dir":{"type":"string","description":"crate directory relative to this manifest's directory, inside the author workspace, no `..`; you own <crate_dir>/src/stores/<name>/interface/** and <crate_dir>/src/builder/**"},
                "tables":{"type":"array","minItems":1,"items":{"type":"object","additionalProperties":false,"required":["table","columns"],"properties":{
                    "table":{"type":"string"},"columns":{"type":"array","items":{"type":"string"},"description":"stored NOT NULL columns; empty: the table is stored through a row-count carrier"}}}},
                "parts":{"type":"array","minItems":1,"items":{"type":"string","minLength":1},"description":"one label per part your builder returns, in order"},
                "layout":{"type":"object","additionalProperties":false,"required":["summary","units","choice"],"properties":{
                    "summary":{"type":"string","minLength":1},"units":{"type":"string","minLength":1},"choice":{"type":"string","minLength":1}}},
                "data_policy":{"type":"array","description":"one entry per part of this manifest's parts list (part = its index there, from 0; with built_from.extends the inherited parts are the source's and are declared by it, so they are not listed or numbered here) (stored-data.json storage_policy): the one stored table whose rows it is computed from, its kind, the columns it holds or describes, and why it holds no query computation and no second payload copy; required under storage_policy physical_only (query_derived_values is refused there; each column is base_payload of at most one storage of the serving storage), recorded with the storage; storage_check reports each part and which parts hold each column",
                    "items":{"type":"object","additionalProperties":false,"required":["part","table","kind","why"],"properties":{
                        "part":{"type":"integer","minimum":0},"table":{"type":"string"},"kind":{"enum":PartKind::CURRENT.map(PartKind::name),
                            "description":"base_payload: part of the ONE stored copy of `columns` (any order, partitioning, lossless encoding; one copy may span several parts of this storage, e.g. codes + dictionary + offsets, each listing the column); index_keys: key `columns` -> this table's own row positions or ranges, no other column's values (no covering index); permutation: row positions only into the one copy (another order); own_skip_metadata: min/max, Bloom/trigram filters, statistics; layout_offsets_counts: run offsets, row counts, block offsets of the representation; query_derived_values: anything else (unrestricted only)"},
                        "columns":{"type":"array","items":{"type":"string"},"description":"stored columns of `table` (this manifest's tables): the payload columns (base_payload) or key columns (index_keys), required there; the order or summarized columns otherwise, optional"},
                        "why":{"type":"string","minLength":1}}}},
                "modules":{"type":"array","description":"optional; omit to derive it from the files under src/stores/<name>/interface and src/builder (interface/mod.rs declares represents, builder/mod.rs declares build, other interface files are readers, other builder files helpers; items come from Verus's report). When given: every such .rs file exactly once",
                    "items":{"type":"object","additionalProperties":false,"required":["file","role","items"],"properties":{
                        "file":{"type":"string","description":"relative to src/, e.g. stores/<name>/interface/mod.rs or builder/mod.rs"},
                        "role":{"enum":["interface","reader","builder","helper"]},
                        "items":{"type":"array","items":{"type":"string"},"description":"functions this module contributes, as Verus names them relative to the module; represents in the interface root, build in the builder root"}}}},
                "compiler":{"type":"object","additionalProperties":false,"required":["opt_level"],"properties":{
                    "opt_level":{"type":"integer","minimum":0,"maximum":3},"target_cpu":{"type":["string","null"]}}},
                "notes":{"type":"string"},
                "built_from":{"type":"object","additionalProperties":false,"required":["sources"],
                    "description":"build this storage from ADMITTED storages instead of source columns (fixed derived storage entry, gendb-verus-storage-entry-derived-v1): its builder (pub fn build(stores: &mut Stores, workers, dispatch)) reads each source only through that source's interface readers and StoredParts extents, and proves: for every database whose stored relations the sources' parts represent, the new parts represent this storage's stored relations (old represents + correct copy => new represents). Required for storages created by query authors (the original input may be deleted). The name must differ from every source's",
                    "properties":{
                        "sources":{"type":"array","minItems":1,"items":{"type":"object","additionalProperties":false,"required":["name","admitted"],
                            "properties":{"name":{"type":"string"},"admitted":{"type":"string","description":"admitted package id (storages.json use_as)"}}}},
                        "extends":{"type":"string","description":"optional: the name of one source whose parts this storage keeps unchanged before its builder's parts (linked, never copied or rebuilt): extend a storage by new columns or index parts. The interface's represents then describes the source's parts followed by the new ones"}}}}})
    }

    /// [`Self::schema`] with the `uses_declared_constraints` opt-in, for the authors of a run that declares integrity
    /// constraints (the manifest parser accepts the field in every run; a run without declarations refuses `true`).
    pub fn schema_with_declared_constraints() -> Value {
        let mut schema = Self::schema();
        schema["properties"]["uses_declared_constraints"] = json!({"type":"boolean",
            "description":"true: the builder may assume the run's declared integrity constraints (fixed storage entry v2, precondition source_witnessed: some full database satisfying the declarations delivers the source); the storage then applies only to runs with exactly this declaration set. Default false: storage entry v1, usable in every run"});
        schema
    }

    /// The storage name, checked as a crate module name.
    pub fn storage_name(&self) -> Result<StorageName, AdmissionError> {
        StorageName::new(&self.name).map_err(AdmissionError::refusal)
    }

    /// The crate-relative author roots of this storage: `(interface root, builder root)`.
    pub fn author_roots(&self) -> (String, String) {
        (format!("stores/{}/interface", self.name), "builder".to_string())
    }

    /// The manifest's own completeness rules (the schema cannot state them all).
    pub fn check(&self) -> Result<(), AdmissionError> {
        let layout = &self.layout;
        let complete = self.format_version == 1
            && !self.tables.is_empty()
            && !self.parts.is_empty()
            && self.parts.iter().all(|p| !p.trim().is_empty())
            && [&layout.summary, &layout.units, &layout.choice].iter().all(|text| !text.trim().is_empty());
        if !complete {
            return Err(AdmissionError::refusal(
                "storage manifest needs format_version 1, at least one stored table, part labels and a layout summary, units and choice",
            ));
        }
        self.storage_name()?;
        if self.compiler.as_ref().is_some_and(|choice| choice.opt_level > 3) {
            return Err(AdmissionError::refusal("compiler.opt_level must be 0..=3"));
        }
        let (interface, builder) = self.author_roots();
        let mut files = BTreeSet::new();
        for module in &self.modules {
            let under_root = [&interface, &builder].iter().any(|root| module.file.strip_prefix(root.as_str()).is_some_and(|rest| rest.starts_with('/')));
            if !under_root || !module.file.ends_with(".rs") {
                return Err(AdmissionError::refusal(format!("storage module {} is not a .rs file under {interface}/ or {builder}/", module.file)));
            }
            if !files.insert(module.file.as_str()) {
                return Err(AdmissionError::refusal(format!("storage module {} declared twice", module.file)));
            }
        }
        for (root, item) in [(&interface, REQUIRED_STORAGE_ITEMS[0].1), (&builder, REQUIRED_STORAGE_ITEMS[1].1)] {
            let root_file = format!("{root}/mod.rs");
            if !self.modules.is_empty() && !self.modules.iter().any(|m| m.file == root_file && m.items.iter().any(|i| i == item)) {
                return Err(AdmissionError::refusal(format!("{root_file} must be declared with item {item}")));
            }
        }
        Ok(())
    }

    /// The per-part declarations, checked against the manifest: exactly one entry per part (by index), each naming one
    /// of this storage's stored tables (own-table wording), only stored columns of that table, each once, and a reason
    /// (which kinds a policy allows, and which must name columns, is `storage::policy`'s check). `Ok(None)` for the free-text form of earlier
    /// manifests (no per-part source table is declared); refusals are `storage_policy_declaration_invalid`.
    pub fn part_policies(&self) -> Result<Option<Vec<&PartPolicy>>, AdmissionError> {
        let DataPolicy::Parts(declared) = &self.data_policy else { return Ok(None) };
        let invalid = |detail: String| AdmissionError::refusal(format!("storage_policy_declaration_invalid: storage {}: {detail}", self.name));
        let mut by_part: Vec<Option<&PartPolicy>> = vec![None; self.parts.len()];
        for entry in declared {
            let slot = by_part.get_mut(entry.part).ok_or_else(|| invalid(format!("data_policy names part {}, but the manifest lists {} parts (part is the index in this manifest's parts list, from 0; parts inherited through built_from.extends are the source's and are not declared here)", entry.part, self.parts.len())))?;
            if slot.replace(entry).is_some() {
                return Err(invalid(format!("part {} is declared twice", entry.part)));
            }
            let Some(stored) = self.tables.iter().find(|t| t.table == entry.table) else {
                return Err(invalid(format!("part {} is declared as computed from table {}, which this storage does not store", entry.part, entry.table)));
            };
            let mut named = BTreeSet::new();
            for column in &entry.columns {
                if !stored.columns.contains(column) || !named.insert(column) {
                    return Err(invalid(format!(
                        "part {} names column {column} of {} twice or a column this manifest does not store (tables[].columns)",
                        entry.part, entry.table
                    )));
                }
            }
            if entry.why.trim().is_empty() {
                return Err(invalid(format!("part {} has no why", entry.part)));
            }
        }
        if let Some(missing) = by_part.iter().position(Option::is_none) {
            return Err(invalid(format!("part {missing} ({}) has no data_policy entry", self.parts[missing])));
        }
        Ok(Some(by_part.into_iter().flatten().collect()))
    }

    /// The storage declaration of the stored columns over the dataset schema (`doc.tables`). An unknown or duplicate
    /// table or column is `missing_input` naming it; an unbindable column is refused with the frontend's reason.
    pub fn declaration(&self, schema: &[TableDef]) -> Result<DeclaredSource, AdmissionError> {
        let mut selection: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        for stored in &self.tables {
            let table_id = schema
                .iter()
                .position(|t| t.name == stored.table)
                .ok_or_else(|| AdmissionError::missing_input(format!("unknown_source_column: table {} is not in the schema", stored.table)))?;
            let chosen = BTreeSet::new();
            if selection.insert(table_id, chosen).is_some() {
                return Err(AdmissionError::missing_input(format!("table {} is listed twice", stored.table)));
            }
            for column in &stored.columns {
                let ordinal = schema[table_id].columns.iter().position(|c| &c.name == column).ok_or_else(|| {
                    AdmissionError::missing_input(format!("unknown_source_column: {}.{column} is not a column of the schema", stored.table))
                })?;
                if !selection.get_mut(&table_id).expect("inserted above").insert(ordinal) {
                    return Err(AdmissionError::missing_input(format!("column {}.{column} is listed twice", stored.table)));
                }
            }
        }
        DeclaredSource::for_storage(schema, &selection).map_err(|e| AdmissionError::refusal(format!("storage declaration: {e}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gendb_frontend::ast::{ColumnDef, PgType};

    fn schema() -> Vec<TableDef> {
        let column = |name: &str, ty: PgType, nullable: bool| ColumnDef { name: name.into(), ty, nullable };
        vec![TableDef {
            name: "sensor".into(),
            columns: vec![column("id", PgType::Int4, false), column("note", PgType::Text, true), column("day", PgType::Date, false)],
            constraints: vec![],
        }]
    }

    fn manifest() -> StorageManifest {
        let mut m = StorageManifest::example();
        m.name = "sensor_days".into();
        m.tables = vec![StoredTable { table: "sensor".into(), columns: vec!["id".into(), "day".into()] }];
        m.modules = ["stores/sensor_days/interface/mod.rs", "builder/mod.rs"].map(|file| derived_module("sensor_days", file)).to_vec();
        m
    }

    #[test]
    fn manifests_are_checked_and_declared_over_the_schema() {
        let m = manifest();
        m.check().unwrap();
        let mut derived = m.clone();
        derived.modules.clear();
        derived.check().expect("modules may be omitted: they are derived from the files");
        assert_eq!(derived_module("sensor_days", "stores/sensor_days/interface/zone.rs").role, StorageModuleRole::Reader);
        let declaration = m.declaration(&schema()).unwrap();
        assert_eq!(declaration.tables[0].columns.iter().map(|c| c.ordinal).collect::<Vec<_>>(), [0, 2]);
        let mut missing_root = m.clone();
        missing_root.modules.retain(|module| module.role != StorageModuleRole::Builder);
        assert!(missing_root.check().unwrap_err().message.contains("builder/mod.rs"));
        let mut outside = m.clone();
        outside.modules.push(StorageModule { file: "agent/mod.rs".into(), role: StorageModuleRole::Helper, items: vec![] });
        assert!(outside.check().is_err());
        let mut unknown = m.clone();
        unknown.tables[0].columns.push("reading".into());
        assert!(unknown.declaration(&schema()).unwrap_err().message.starts_with("unknown_source_column"));
        // A nullable column is stored with its validity: declared nullable.
        let mut nullable = m.clone();
        nullable.tables[0].columns.push("note".into());
        let declared = nullable.declaration(&schema()).unwrap();
        assert_eq!(declared.tables[0].columns.iter().map(|c| (c.ordinal, c.nullable)).collect::<Vec<_>>(), [(0, false), (1, true), (2, false)]);
        let mut keyword = m.clone();
        keyword.name = "match".into();
        assert!(keyword.check().is_err());
        assert!(serde_json::from_value::<StorageManifest>(json!({"format_version":1,"extra":1})).is_err());
        // The opt-in defaults to false and is not serialized then; `true` round-trips.
        let plain = serde_json::to_value(&m).unwrap();
        assert!(plain.get("uses_declared_constraints").is_none());
        let mut opted = plain.clone();
        opted["uses_declared_constraints"] = json!(true);
        assert!(serde_json::from_value::<StorageManifest>(opted).unwrap().uses_declared_constraints);
        assert!(StorageManifest::schema()["properties"].get("uses_declared_constraints").is_none(), "default author schema unchanged");
        assert_eq!(StorageManifest::schema_with_declared_constraints()["properties"]["uses_declared_constraints"]["type"], "boolean");
    }
}
