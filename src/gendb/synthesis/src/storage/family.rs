//! Storage families: storage code written once by the engine author and composed by
//! GenDB into every workload of a run of several workloads (`engine.workloads`) as one whole-schema storage named after
//! the family.
//!
//! A family's source lies in the author workspace; the engine manifest's `families[].source` names its manifest:
//! - `verus-family.json` ([`FamilyManifest`]): the family's name, crate directory, layout explanation, compiler choice,
//!   whether its builder assumes the declared integrity constraints, and its **part template** ([`PartTemplate`]: the
//!   parts of every table, of every column by its type class, and the extra parts of a nullable column);
//! - `<crate_dir>/src/builder/**` and `<crate_dir>/src/stores/<name>/interface/**`: the builder and the interface,
//!   the same text in every instance, whose store is `crate::stores::<name>`. `builder/plan.rs` is GenDB's slot;
//! - `default_plan.rs`: the plan of a workload without one of its own.
//!
//! [`compose_instance`] writes one workload's instance as an ordinary storage workspace: the family's two author roots,
//! `builder/plan.rs` (the workload's plan `plans/<workload>/<family>.rs` when it has one, else `default_plan.rs`; either
//! checked by the plan rule, `gendb_verification::verus::engine_rules::PLAN_IS_DATA_RULE`) and a generated
//! `verus-storage.json`: `tables` = every table and column of the workload's schema (whole-schema), `parts` and
//! `data_policy` = the template expanded in table and column order ([`expand_parts`]), `built_from.sources` = the
//! workload's plain flat storages (one per table, admitted in its library), no `extends`. From there it is a workspace
//! storage like any other: frozen, verified whole, built, checked against the storage policy and budget, registered and
//! admitted in that workload's library (`query::candidate::resolve_uses`, the storage path, unchanged). A derived storage
//! that stores every column of every table carries two more generated files, `schema_exec.rs` and `whole_schema.rs`
//! (`gendb_verification::obligations`), so the builder reads the schema's types at run time and states its relations by
//! table id for any table count.
//!
//! Trust: none in proofs. The expansion and the composition are host code that writes the inputs of the ordinary storage
//! path; each generated manifest is checked there like an author's (its declaration against the schema, its data policy
//! against its parts and the storage policy, its crate by Verus).

use super::manifest::{BuiltFrom, DataPolicy, PartKind, PartPolicy, STORAGE_MANIFEST_FILE, SourceStorage, StorageLayout, StorageManifest, StoredTable};
use crate::query::candidate::CompilerChoice;
use gendb_artifacts::ContentId;
use gendb_frontend::ast::{PgType, TableDef};
use gendb_verification::admission::AdmissionError;
use gendb_verification::obligations::StorageName;
use gendb_verification::verus::engine_rules::{PLAN_IS_DATA_RULE, scan_plan_source};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::fs;
use std::path::{Component, Path, PathBuf};

/// The file name of a family's manifest.
pub const FAMILY_MANIFEST_FILE: &str = "verus-family.json";
/// The file name of a family's default plan, beside its manifest.
pub const DEFAULT_PLAN_FILE: &str = "default_plan.rs";
/// The plan's path in an instance's storage crate, relative to `src/` (module `crate::builder::plan`).
pub const PLAN_PATH: &str = "builder/plan.rs";
/// The crate directory of a composed instance, relative to its storage workspace.
pub const INSTANCE_CRATE_DIRECTORY: &str = "crate";

/// `verus-family.json`. Paths are relative to the manifest's directory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyManifest {
    pub format_version: u32,
    /// The family's name: its instances' storage name and module `crate::stores::<name>` in every workload
    /// (a storage name: a lowercase Rust identifier that is not a keyword).
    pub name: String,
    /// The crate directory holding `src/builder/**` and `src/stores/<name>/interface/**`, inside the family's directory.
    pub crate_dir: String,
    /// The author's explanation of the stored organization (each instance's `layout`).
    pub layout: StorageLayout,
    /// The parts of every instance, by table, column type class and nullability ([`expand_parts`]).
    pub parts: PartTemplate,
    #[serde(default)]
    pub compiler: Option<CompilerChoice>,
    #[serde(default)]
    pub notes: String,
    /// Whether the builder assumes the run's declared integrity constraints (storage manifests' field of that name).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub uses_declared_constraints: bool,
}

/// The part template of a family: the slots every instance's builder returns, in table and column order. Contents may
/// vary by data and plan; the slots may not (an unused slot is an empty part).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PartTemplate {
    /// The parts of every table, before its columns' parts (layout, metadata). Their kind may not be one that names
    /// columns (`base_payload`, `index_keys`).
    #[serde(default)]
    pub table: Vec<PartSlot>,
    /// The parts of every column, by its type class.
    pub column: ColumnSlots,
    /// The extra parts of a nullable column, after its type class's parts.
    #[serde(default)]
    pub nullable: Vec<PartSlot>,
}

/// The parts of one column by its SQL type class. A class the schema has a column of needs at least one slot.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ColumnSlots {
    /// `integer`.
    #[serde(default)]
    pub int4: Vec<PartSlot>,
    /// `bigint`.
    #[serde(default)]
    pub int8: Vec<PartSlot>,
    /// `numeric(p, s)`.
    #[serde(default)]
    pub numeric: Vec<PartSlot>,
    /// `date`.
    #[serde(default)]
    pub date: Vec<PartSlot>,
    /// `text`, `varchar(n)` and `char(n)`.
    #[serde(default)]
    pub text: Vec<PartSlot>,
}

/// One slot of the template: its label and reason patterns (`{table}`, `{column}` replaced by the names) and its kind
/// of stored data (`storage::manifest::PartKind`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PartSlot {
    pub label: String,
    pub kind: PartKind,
    /// Why the part holds no query computation and no second copy of a column (each instance's `data_policy[].why`).
    pub why: String,
}

/// The type class of a stored column ([`ColumnSlots`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeClass {
    Int4,
    Int8,
    Numeric,
    Date,
    Text,
}

impl TypeClass {
    /// The class of a stored column's type; `None` for a type no storage stores (`boolean`, `timestamp`).
    pub fn of(ty: &PgType) -> Option<Self> {
        match ty {
            PgType::Int4 => Some(Self::Int4),
            PgType::Int8 => Some(Self::Int8),
            PgType::Numeric { .. } => Some(Self::Numeric),
            PgType::Date => Some(Self::Date),
            PgType::Text | PgType::Varchar { .. } | PgType::Bpchar { .. } => Some(Self::Text),
            PgType::Bool | PgType::Timestamp => None,
        }
    }

    /// The class's name in `parts.column`.
    pub fn name(self) -> &'static str {
        match self {
            Self::Int4 => "int4",
            Self::Int8 => "int8",
            Self::Numeric => "numeric",
            Self::Date => "date",
            Self::Text => "text",
        }
    }
}

impl ColumnSlots {
    /// The slots of class `class`.
    pub fn of(&self, class: TypeClass) -> &[PartSlot] {
        match class {
            TypeClass::Int4 => &self.int4,
            TypeClass::Int8 => &self.int8,
            TypeClass::Numeric => &self.numeric,
            TypeClass::Date => &self.date,
            TypeClass::Text => &self.text,
        }
    }
}

/// One expanded part: its label and its data-policy declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpandedPart {
    pub label: String,
    pub policy: PartPolicy,
}

/// The template of `manifest` expanded over `schema` (pure data): for each table in table order, its table slots, then
/// for each column in column order the slots of its type class and, for a nullable column, the nullable slots. Each
/// part's data policy names its table, its kind and why, and a column part its column. Refused: a column type no
/// storage stores, a class with a column and no slot, a table slot whose kind names columns or whose patterns name
/// `{column}`, an empty label or reason.
pub fn expand_parts(manifest: &FamilyManifest, schema: &[TableDef]) -> Result<Vec<ExpandedPart>, AdmissionError> {
    let refused = |detail: String| AdmissionError::refusal(format!("storage family {}: {detail}", manifest.name));
    let fill = |pattern: &str, table: &str, column: Option<&str>| pattern.replace("{table}", table).replace("{column}", column.unwrap_or("{column}"));
    let mut parts = vec![];
    for table in schema {
        for slot in &manifest.parts.table {
            if slot.kind.names_columns() || slot.label.contains("{column}") || slot.why.contains("{column}") {
                return Err(refused(format!("table slot {:?}: a table's part names no column (no {{column}} pattern; kind {} names columns)", slot.label, slot.kind.name())));
            }
            parts.push(expanded(slot, &table.name, None, &fill)?);
        }
        for column in &table.columns {
            let class = TypeClass::of(&column.ty).ok_or_else(|| refused(format!("{}.{}: its type {:?} is stored by no storage", table.name, column.name, column.ty)))?;
            let slots = manifest.parts.column.of(class);
            if slots.is_empty() {
                return Err(refused(format!("parts.column.{} has no slot, but {}.{} is of that class", class.name(), table.name, column.name)));
            }
            let nullable: &[PartSlot] = if column.nullable { &manifest.parts.nullable } else { &[] };
            for slot in slots.iter().chain(nullable) {
                parts.push(expanded(slot, &table.name, Some(&column.name), &fill)?);
            }
        }
    }
    Ok(parts)
}

/// One slot expanded for `table` (and `column`, for a column slot), its policy's part index filled by the caller's order.
fn expanded(slot: &PartSlot, table: &str, column: Option<&str>, fill: &impl Fn(&str, &str, Option<&str>) -> String) -> Result<ExpandedPart, AdmissionError> {
    let (label, why) = (fill(&slot.label, table, column), fill(&slot.why, table, column));
    if label.trim().is_empty() || why.trim().is_empty() {
        return Err(AdmissionError::refusal(format!("a part slot of {table} has an empty label or why")));
    }
    let policy = PartPolicy { part: 0, table: table.to_string(), kind: slot.kind, columns: column.map(|c| vec![c.to_string()]).unwrap_or_default(), why };
    Ok(ExpandedPart { label, policy })
}

impl FamilyManifest {
    /// The manifest's own rules: format 1, a storage name, a relative crate directory without `..`, a complete layout.
    pub fn check(&self) -> Result<(), AdmissionError> {
        if self.format_version != 1 {
            return Err(AdmissionError::refusal(format!("storage family {}: a family manifest has format_version 1", self.name)));
        }
        StorageName::new(&self.name).map_err(|e| AdmissionError::refusal(format!("storage family: {e}")))?;
        let crate_dir = Path::new(&self.crate_dir);
        if self.crate_dir.is_empty() || crate_dir.is_absolute() || crate_dir.components().any(|c| !matches!(c, Component::Normal(_) | Component::CurDir)) {
            return Err(AdmissionError::refusal(format!("storage family {}: crate_dir is a relative path inside the family's directory, without `..`", self.name)));
        }
        let layout = &self.layout;
        if [&layout.summary, &layout.units, &layout.choice].iter().any(|text| text.trim().is_empty()) {
            return Err(AdmissionError::refusal(format!("storage family {}: layout needs its summary, units and choice", self.name)));
        }
        if self.compiler.as_ref().is_some_and(|choice| choice.opt_level > 3) {
            return Err(AdmissionError::refusal(format!("storage family {}: compiler.opt_level must be 0..=3", self.name)));
        }
        Ok(())
    }

    /// The instance's storage manifest over `schema` built from `flat_storages` (one per table, in table order): every
    /// table and column stored, the expanded parts and data policy, derived modules, no `extends`.
    pub fn instance_manifest(&self, schema: &[TableDef], flat_storages: &[(String, ContentId)]) -> Result<StorageManifest, AdmissionError> {
        let parts = expand_parts(self, schema)?;
        Ok(StorageManifest {
            format_version: 1,
            name: self.name.clone(),
            crate_dir: INSTANCE_CRATE_DIRECTORY.into(),
            tables: schema.iter().map(|t| StoredTable { table: t.name.clone(), columns: t.columns.iter().map(|c| c.name.clone()).collect() }).collect(),
            parts: parts.iter().map(|p| p.label.clone()).collect(),
            layout: self.layout.clone(),
            data_policy: DataPolicy::Parts(parts.into_iter().enumerate().map(|(k, p)| PartPolicy { part: k, ..p.policy }).collect()),
            modules: vec![],
            compiler: self.compiler.clone(),
            notes: self.notes.clone(),
            uses_declared_constraints: self.uses_declared_constraints,
            built_from: Some(BuiltFrom { sources: flat_storages.iter().map(|(name, package)| SourceStorage { name: name.clone(), admitted: *package }).collect(), extends: None }),
        })
    }

    /// JSON schema of the manifest (author contract).
    pub fn schema() -> Value {
        let slot = json!({"type":"object","additionalProperties":false,"required":["label","kind","why"],"properties":{
            "label":{"type":"string","minLength":1,"description":"the part's label; {table} and {column} are replaced by the names"},
            "kind":{"enum":PartKind::CURRENT.map(PartKind::name),"description":"the part's kind of stored data (verus-storage.json data_policy kinds)"},
            "why":{"type":"string","minLength":1,"description":"why the part holds no query computation and no second copy of a column; {table} and {column} are replaced"}}});
        let slots = json!({"type":"array","items":slot});
        json!({"type":"object","additionalProperties":false,"required":["format_version","name","crate_dir","layout","parts"],"properties":{
            "format_version":{"const":1},
            "name":{"type":"string","pattern":"^[a-z][a-z0-9_]{0,63}$","description":"the family's name: every instance's storage name (crate::stores::<name> in every workload's crates); not a Rust keyword"},
            "crate_dir":{"type":"string","description":"relative to this manifest's directory: holds src/builder/** and src/stores/<name>/interface/**, the same text in every instance; builder/plan.rs is composed by GenDB (the workload's plan or default_plan.rs beside this manifest)"},
            "layout":{"type":"object","additionalProperties":false,"required":["summary","units","choice"],"properties":{
                "summary":{"type":"string","minLength":1},"units":{"type":"string","minLength":1},"choice":{"type":"string","minLength":1}}},
            "parts":{"type":"object","additionalProperties":false,"required":["column"],"description":"the part template, expanded by GenDB for every table in table order: the table slots, then for every column the slots of its type class, then for a nullable column the nullable slots; an unused slot is an empty part",
                "properties":{"table":slots.clone(),
                    "column":{"type":"object","additionalProperties":false,"properties":{"int4":slots.clone(),"int8":slots.clone(),"numeric":slots.clone(),"date":slots.clone(),"text":slots.clone()},
                        "description":"by type class: int4 (integer), int8 (bigint), numeric, date, text (text, varchar, char); a class with a column in the schema needs at least one slot"},
                    "nullable":slots}},
            "compiler":{"type":"object","additionalProperties":false,"required":["opt_level"],"properties":{"opt_level":{"type":"integer","minimum":0,"maximum":3},"target_cpu":{"type":["string","null"]}}},
            "notes":{"type":"string"},
            "uses_declared_constraints":{"type":"boolean"}}})
    }
}

/// A family's source as the workspace holds it: its manifest file (absolute) and its parsed manifest.
#[derive(Clone, Debug)]
pub struct FamilySource {
    pub manifest_path: PathBuf,
    pub manifest: FamilyManifest,
}

impl FamilySource {
    /// Read and check the family manifest at `path` (absolute), and that its crate's two author roots and its default
    /// plan exist and that the builder has no `plan.rs` of its own.
    pub fn read(path: &Path) -> Result<Self, AdmissionError> {
        let bytes = fs::read(path).map_err(|e| AdmissionError::missing_input(format!("{}: {e}", path.display())))?;
        let manifest: FamilyManifest = serde_json::from_slice(&bytes).map_err(|e| AdmissionError::refusal(format!("{}: {e}", path.display())))?;
        manifest.check()?;
        let source = Self { manifest_path: path.to_path_buf(), manifest };
        for dir in [source.builder_root(), source.interface_root()] {
            if !dir.join("mod.rs").is_file() {
                return Err(AdmissionError::missing_input(format!("storage family {}: {} is missing", source.manifest.name, dir.join("mod.rs").display())));
            }
        }
        if fs::symlink_metadata(source.builder_root().join("plan.rs")).is_ok() {
            return Err(AdmissionError::refusal(format!(
                "storage family {}: builder/plan.rs is composed by GenDB (the workload's plans/<workload>/{}.rs, else {DEFAULT_PLAN_FILE}); remove it from the family's builder",
                source.manifest.name, source.manifest.name
            )));
        }
        if !source.default_plan().is_file() {
            return Err(AdmissionError::missing_input(format!("storage family {}: {} is missing (the plan of a workload without one)", source.manifest.name, source.default_plan().display())));
        }
        Ok(source)
    }

    /// The family's directory (its manifest's).
    pub fn directory(&self) -> &Path {
        self.manifest_path.parent().unwrap_or(Path::new("/"))
    }

    /// `<crate_dir>/src/builder`.
    pub fn builder_root(&self) -> PathBuf {
        self.directory().join(&self.manifest.crate_dir).join("src/builder")
    }

    /// `<crate_dir>/src/stores/<name>/interface`.
    pub fn interface_root(&self) -> PathBuf {
        self.directory().join(&self.manifest.crate_dir).join("src/stores").join(&self.manifest.name).join("interface")
    }

    /// `default_plan.rs` beside the manifest.
    pub fn default_plan(&self) -> PathBuf {
        self.directory().join(DEFAULT_PLAN_FILE)
    }

    /// Every file of the family's source, relative to its directory, sorted: the manifest, the default plan and the
    /// files under its two author roots (what a version's code and the shared-source digest hold).
    pub fn files(&self) -> Result<Vec<PathBuf>, AdmissionError> {
        let dir = self.directory();
        let mut files = vec![PathBuf::from(FAMILY_MANIFEST_FILE), PathBuf::from(DEFAULT_PLAN_FILE)];
        for root in [self.builder_root(), self.interface_root()] {
            for file in tree_files(&root)? {
                files.push(root.join(file).strip_prefix(dir).map_err(AdmissionError::tool)?.to_path_buf());
            }
        }
        files.sort();
        Ok(files)
    }
}

/// Which plan an instance was composed with.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PlanChoice {
    /// The workload's own `plans/<workload>/<family>.rs`.
    Workload,
    /// The family's `default_plan.rs`.
    Default,
}

/// What one instance is composed from ([`compose_instance`]).
pub struct InstanceInput<'a> {
    pub family: &'a FamilySource,
    /// The workload's schema (its dataset's tables with the declared constraints).
    pub schema: &'a [TableDef],
    /// The workload's plain flat storages `(name, package)`, one per table in table order: the instance's sources.
    pub flat_storages: &'a [(String, ContentId)],
    /// The workload's plan of this family, when it has one (`plans/<workload>/<family>.rs`).
    pub plan: Option<&'a Path>,
}

/// One composed instance: its storage workspace (`verus-storage.json` at the root), its generated manifest, the plan
/// it was composed with and that plan's lines.
#[derive(Clone, Debug)]
pub struct ComposedInstance {
    pub workspace: PathBuf,
    pub manifest: StorageManifest,
    pub plan: PlanChoice,
    pub plan_lines: usize,
}

/// Compose the instance of `input` into the fresh directory `to` (module documentation): `to/verus-storage.json`
/// ([`FamilyManifest::instance_manifest`]), `to/crate/src/builder/**` and `to/crate/src/stores/<name>/interface/**`
/// (the family's bytes), `to/crate/src/builder/plan.rs` (the plan). The plan composed and the family's default plan are
/// checked by the plan rule first ([`PLAN_IS_DATA_RULE`]). Refused: a plan with findings, flat storages that are not one
/// per table with distinct names other than the family's, a template that does not expand over the schema; a symlink in
/// the family's roots.
pub fn compose_instance(input: &InstanceInput<'_>, to: &Path) -> Result<ComposedInstance, AdmissionError> {
    let family = &input.family.manifest;
    let refused = |detail: String| AdmissionError::refusal(format!("storage family {}: {detail}", family.name));
    if input.flat_storages.len() != input.schema.len() {
        return Err(AdmissionError::tool(format!("storage family {}: {} plain flat storages for {} tables (one per table, in table order)", family.name, input.flat_storages.len(), input.schema.len())));
    }
    let mut names = std::collections::BTreeSet::new();
    if let Some((name, _)) = input.flat_storages.iter().find(|(name, _)| *name == family.name || !names.insert(name.as_str())) {
        return Err(refused(format!("the flat storage {name} is named twice or has the family's name")));
    }
    let (plan_file, plan) = match input.plan {
        Some(path) => (path.to_path_buf(), PlanChoice::Workload),
        None => (input.family.default_plan(), PlanChoice::Default),
    };
    let mut checked = vec![(input.family.default_plan(), DEFAULT_PLAN_FILE.to_string())];
    if plan == PlanChoice::Workload {
        checked.push((plan_file.clone(), format!("plans/<workload>/{}.rs", family.name)));
    }
    for (file, shown) in &checked {
        let text = fs::read_to_string(file).map_err(|e| AdmissionError::missing_input(format!("{}: {e}", file.display())))?;
        let findings = scan_plan_source(shown, &text);
        if !findings.is_empty() {
            let listed: Vec<String> = findings.iter().map(|f| format!("{}:{}: {}", f.file, f.line, f.detail)).collect();
            return Err(refused(format!("{}: {} ({})", PLAN_IS_DATA_RULE.id, listed.join("; "), PLAN_IS_DATA_RULE.refuses)));
        }
    }
    let manifest = family.instance_manifest(input.schema, input.flat_storages)?;
    let src = to.join(INSTANCE_CRATE_DIRECTORY).join("src");
    fs::create_dir(to).map_err(|e| AdmissionError::tool(format!("{}: {e}", to.display())))?;
    copy_author_tree(&input.family.builder_root(), &src.join("builder"))?;
    copy_author_tree(&input.family.interface_root(), &src.join("stores").join(&family.name).join("interface"))?;
    let plan_text = fs::read(&plan_file).map_err(AdmissionError::tool)?;
    fs::write(src.join(PLAN_PATH), &plan_text).map_err(AdmissionError::tool)?;
    let text = format!("{}\n", serde_json::to_string_pretty(&manifest).map_err(AdmissionError::tool)?);
    fs::write(to.join(STORAGE_MANIFEST_FILE), text).map_err(AdmissionError::tool)?;
    let plan_lines = String::from_utf8_lossy(&plan_text).lines().count();
    Ok(ComposedInstance { workspace: to.to_path_buf(), manifest, plan, plan_lines })
}

/// A recursive copy of the author tree `from` into `to` (created; directories and regular files only, bytes unchanged).
/// Anything else (a symlink) is refused, as the freeze refuses it in an author root.
pub(crate) fn copy_author_tree(from: &Path, to: &Path) -> Result<(), AdmissionError> {
    fs::create_dir_all(to).map_err(AdmissionError::tool)?;
    for item in fs::read_dir(from).map_err(|e| AdmissionError::tool(format!("{}: {e}", from.display())))? {
        let item = item.map_err(AdmissionError::tool)?;
        let kind = item.file_type().map_err(AdmissionError::tool)?;
        let target = to.join(item.file_name());
        if kind.is_dir() {
            copy_author_tree(&item.path(), &target)?;
        } else if kind.is_file() {
            fs::write(&target, fs::read(item.path()).map_err(AdmissionError::tool)?).map_err(AdmissionError::tool)?;
        } else {
            return Err(AdmissionError::refusal(format!("{}: only directories and `.rs` files are allowed in an author tree (no symlinks)", item.path().display())));
        }
    }
    Ok(())
}

/// Every regular file under `dir`, relative to it, sorted (none when it does not exist).
pub(crate) fn tree_files(dir: &Path) -> Result<Vec<PathBuf>, AdmissionError> {
    let mut found = vec![];
    let mut stack = vec![PathBuf::new()];
    while let Some(relative) = stack.pop() {
        let Ok(entries) = fs::read_dir(dir.join(&relative)) else { continue };
        for entry in entries {
            let entry = entry.map_err(AdmissionError::tool)?;
            let path = relative.join(entry.file_name());
            if entry.file_type().map_err(AdmissionError::tool)?.is_dir() {
                stack.push(path);
            } else {
                found.push(path);
            }
        }
    }
    found.sort();
    Ok(found)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use gendb_frontend::ast::ColumnDef;

    fn slot(label: &str, kind: PartKind) -> PartSlot {
        PartSlot { label: label.into(), kind, why: format!("{label}: one copy of its own rows") }
    }

    /// A family with a layout part per table, one part per fixed-width column, two per text column and one validity
    /// part per nullable column.
    pub(crate) fn family(name: &str) -> FamilyManifest {
        FamilyManifest {
            format_version: 1,
            name: name.into(),
            crate_dir: "crate".into(),
            layout: StorageLayout { summary: "plain arrays".into(), units: "rows".into(), choice: "a test family".into() },
            parts: PartTemplate {
                table: vec![slot("{table} layout", PartKind::LayoutOffsetsCounts)],
                column: ColumnSlots {
                    int4: vec![slot("{table}.{column} values", PartKind::BasePayload)],
                    int8: vec![slot("{table}.{column} values", PartKind::BasePayload)],
                    numeric: vec![slot("{table}.{column} coefficients", PartKind::BasePayload)],
                    date: vec![slot("{table}.{column} days", PartKind::BasePayload)],
                    text: vec![slot("{table}.{column} offsets", PartKind::BasePayload), slot("{table}.{column} bytes", PartKind::BasePayload)],
                },
                nullable: vec![slot("{table}.{column} validity", PartKind::BasePayload)],
            },
            compiler: None,
            notes: String::new(),
            uses_declared_constraints: false,
        }
    }

    fn column(name: &str, ty: PgType, nullable: bool) -> ColumnDef {
        ColumnDef { name: name.into(), ty, nullable }
    }

    /// Every stored type class, a nullable column and an empty table (the anyschema fixture's shapes).
    pub(crate) fn schema() -> Vec<TableDef> {
        vec![
            TableDef {
                name: "ax_owner".into(),
                columns: vec![
                    column("ow_id", PgType::Int8, false),
                    column("ow_rank", PgType::Int4, true),
                    column("ow_credit", PgType::Numeric { typmod: Some((15, 2)) }, false),
                    column("ow_born", PgType::Date, true),
                    column("ow_name", PgType::Varchar { max_chars: Some(24) }, false),
                    column("ow_code", PgType::Bpchar { n: Some(4) }, false),
                ],
                constraints: vec![],
            },
            TableDef { name: "ax_void".into(), columns: vec![column("vd_id", PgType::Int4, false), column("vd_text", PgType::Text, true)], constraints: vec![] },
        ]
    }

    /// The template expands per table, per column class and per nullable column, in table and column order, with each
    /// part's policy naming its table and column; an empty table gets its slots too.
    #[test]
    fn templates_expand_in_table_and_column_order() {
        let parts = expand_parts(&family("plainfam"), &schema()).unwrap();
        let labels: Vec<&str> = parts.iter().map(|p| p.label.as_str()).collect();
        assert_eq!(
            labels,
            [
                "ax_owner layout",
                "ax_owner.ow_id values",
                "ax_owner.ow_rank values",
                "ax_owner.ow_rank validity",
                "ax_owner.ow_credit coefficients",
                "ax_owner.ow_born days",
                "ax_owner.ow_born validity",
                "ax_owner.ow_name offsets",
                "ax_owner.ow_name bytes",
                "ax_owner.ow_code offsets",
                "ax_owner.ow_code bytes",
                "ax_void layout",
                "ax_void.vd_id values",
                "ax_void.vd_text offsets",
                "ax_void.vd_text bytes",
                "ax_void.vd_text validity",
            ]
        );
        assert_eq!((parts[0].policy.table.as_str(), parts[0].policy.columns.len(), parts[0].policy.kind), ("ax_owner", 0, PartKind::LayoutOffsetsCounts));
        assert_eq!((parts[13].policy.table.as_str(), parts[13].policy.columns.as_slice()), ("ax_void", &["vd_text".to_string()][..]));
        assert_eq!(parts[3].policy.why, "{table}.{column} validity: one copy of its own rows".replace("{table}", "ax_owner").replace("{column}", "ow_rank"));
    }

    /// The expansion's refusals: a class with a column and no slot, a table slot naming a column or of a kind that names
    /// columns, a type no storage stores.
    #[test]
    fn templates_refuse_what_does_not_expand() {
        let refusal = |edit: &dyn Fn(&mut FamilyManifest, &mut Vec<TableDef>), words: &str| {
            let (mut manifest, mut tables) = (family("plainfam"), schema());
            edit(&mut manifest, &mut tables);
            let error = expand_parts(&manifest, &tables).unwrap_err().to_string();
            assert!(error.contains(words), "{words}: {error}");
        };
        refusal(&|m, _| m.parts.column.text.clear(), "parts.column.text has no slot");
        refusal(&|m, _| m.parts.table.push(slot("{table}.{column} zone", PartKind::OwnSkipMetadata)), "a table's part names no column");
        refusal(&|m, _| m.parts.table.push(slot("{table} keys", PartKind::IndexKeys)), "kind index_keys names columns");
        refusal(&|_, t| t[0].columns.push(column("ow_flag", PgType::Bool, false)), "is stored by no storage");
        refusal(&|m, _| m.parts.column.int8[0].label = " ".into(), "empty label or why");
        // A class without a column in the schema needs no slot.
        let mut no_date = family("plainfam");
        no_date.parts.column.date.clear();
        let mut tables = schema();
        tables[0].columns.retain(|c| c.ty != PgType::Date);
        assert_eq!(expand_parts(&no_date, &tables).unwrap().len(), 14);
    }

    /// The instance manifest stores every table and column, declares one policy per part (by index) and is built from
    /// the flat storages; the storage manifest's own checks accept it.
    #[test]
    fn the_instance_manifest_is_whole_schema_and_built_from_the_flat_storages() {
        let flats = vec![("flat_ax_owner".to_string(), ContentId::from_bytes([1; 32])), ("flat_ax_void".to_string(), ContentId::from_bytes([2; 32]))];
        let manifest = family("plainfam").instance_manifest(&schema(), &flats).unwrap();
        manifest.check().unwrap();
        assert_eq!(manifest.tables.iter().map(|t| t.columns.len()).collect::<Vec<_>>(), [6, 2]);
        let policies = manifest.part_policies().unwrap().unwrap();
        assert_eq!(policies.len(), manifest.parts.len());
        assert!(policies.iter().enumerate().all(|(k, p)| p.part == k));
        let built_from = manifest.built_from.clone().unwrap();
        assert_eq!((built_from.sources.len(), built_from.extends.is_none()), (2, true));
        let declaration = manifest.declaration(&schema()).unwrap();
        assert_eq!(declaration.tables.len(), 2);
        assert!(serde_json::from_value::<FamilyManifest>(json!(family("plainfam"))).is_ok());
        assert!(serde_json::from_value::<FamilyManifest>(json!({"format_version":1,"name":"x","crate_dir":"c","layout":{"summary":"s","units":"u","choice":"c"},"parts":{"column":{}},"extra":1})).is_err());
        assert!(FamilyManifest::schema()["properties"]["parts"]["properties"]["column"]["properties"]["text"].is_object());
    }

    pub(crate) fn write(path: &Path, text: &str) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    /// A family source written under `dir`: its manifest, builder, interface and default plan.
    pub(crate) fn write_family(dir: &Path, name: &str) -> PathBuf {
        let manifest = dir.join(FAMILY_MANIFEST_FILE);
        write(&manifest, &serde_json::to_string_pretty(&family(name)).unwrap());
        write(&dir.join("crate/src/builder/mod.rs"), "pub mod plan;\n// builder\n");
        write(&dir.join("crate/src/builder/copy.rs"), "// copy\n");
        write(&dir.join(format!("crate/src/stores/{name}/interface/mod.rs")), "// interface\n");
        write(&dir.join(DEFAULT_PLAN_FILE), "use super::Plan;\nverus! {\npub fn plan() -> Plan { Plan { sorted: vec![] } }\n}\n");
        manifest
    }

    /// Composition per workload: the family's files and the plan (the workload's, else the default) in an ordinary
    /// storage workspace with its generated manifest; a plan that computes, a builder with its own plan.rs and flat
    /// storages that are not one per table are refused.
    #[test]
    fn instances_are_composed_with_the_workload_plan_or_the_default() {
        let root = crate::controller::test_support::scratch_root("family-compose");
        let source = FamilySource::read(&write_family(&root.join("storages/plainfam"), "plainfam")).unwrap();
        assert_eq!(
            source.files().unwrap(),
            ["crate/src/builder/copy.rs", "crate/src/builder/mod.rs", "crate/src/stores/plainfam/interface/mod.rs", DEFAULT_PLAN_FILE, FAMILY_MANIFEST_FILE].map(PathBuf::from)
        );
        let tables = schema();
        let flats = vec![("flat_ax_owner".to_string(), ContentId::from_bytes([1; 32])), ("flat_ax_void".to_string(), ContentId::from_bytes([2; 32]))];
        let default = compose_instance(&InstanceInput { family: &source, schema: &tables, flat_storages: &flats, plan: None }, &root.join("default")).unwrap();
        assert_eq!((default.plan, default.plan_lines), (PlanChoice::Default, 4));
        let files = tree_files(&root.join("default")).unwrap();
        assert_eq!(
            files,
            ["crate/src/builder/copy.rs", "crate/src/builder/mod.rs", "crate/src/builder/plan.rs", "crate/src/stores/plainfam/interface/mod.rs", STORAGE_MANIFEST_FILE].map(PathBuf::from)
        );
        assert_eq!(fs::read(root.join("default/crate/src/builder/plan.rs")).unwrap(), fs::read(source.default_plan()).unwrap());
        let written: StorageManifest = serde_json::from_slice(&fs::read(root.join("default").join(STORAGE_MANIFEST_FILE)).unwrap()).unwrap();
        assert_eq!(written, default.manifest);
        let plan = root.join("plans/sec/plainfam.rs");
        write(&plan, "verus! {\npub fn plan() -> Plan { Plan { sorted: vec![Sort { table: 0, column: 2 }] } }\n}\n");
        let own = compose_instance(&InstanceInput { family: &source, schema: &tables, flat_storages: &flats, plan: Some(&plan) }, &root.join("own")).unwrap();
        assert_eq!(own.plan, PlanChoice::Workload);
        assert_eq!(fs::read(root.join("own/crate/src/builder/plan.rs")).unwrap(), fs::read(&plan).unwrap());
        // A plan that computes is refused by the plan rule.
        write(&plan, "verus! {\npub fn plan() -> Plan { if true { Plan::default() } else { Plan::default() } }\n}\n");
        let error = compose_instance(&InstanceInput { family: &source, schema: &tables, flat_storages: &flats, plan: Some(&plan) }, &root.join("computed")).unwrap_err().to_string();
        assert!(error.contains(PLAN_IS_DATA_RULE.id), "{error}");
        assert!(!root.join("computed").exists(), "nothing is written for a refused plan");
        let short = compose_instance(&InstanceInput { family: &source, schema: &tables, flat_storages: &flats[..1], plan: None }, &root.join("short")).unwrap_err();
        assert!(short.to_string().contains("one per table"), "{short}");
        write(&root.join("storages/plainfam/crate/src/builder/plan.rs"), "");
        assert!(FamilySource::read(&source.manifest_path).unwrap_err().to_string().contains("composed by GenDB"));
        fs::remove_dir_all(&root).unwrap();
    }
}
