//! The engine submission: the author's manifest `verus-engine.json`,
//! the freeze of a submission into an immutable engine crate (fixed entry `gendb-verus-engine-entry-v1`), and the Verus
//! runs of frozen engine crates.
//!
//! - [`EngineManifest`]: the engine crate directory, its storage uses (admitted packages of the engine library, or
//!   storages of the workspace built from admitted ones), the `agent/` modules with their roles and items (the entry
//!   module declares `engine`), the compiler choice and notes.
//! - [`freeze_engine`]: the checks, in order: the manifest and path containment; every storage use, resolved as a query
//!   freeze resolves them (`query::candidate::resolve_uses`), and the derived storages' source versions; complete
//!   column coverage of the schema by the uses (`check_engine_coverage`, the engine's admission rule, here first for
//!   early feedback); the crate's framework files (`engine_crate_files`, toolkit included, and the trusted engine shim);
//!   the central author-source scan of every author file, the static-item rule (no state between calls) and the engine
//!   rules of the run's line (`verus::engine_rules::EngineRuleSet`: template constants, AST fragments, and the
//!   whole-statement evaluator on the schema-engine line or the schema names on the general line) of every `agent/`
//!   file, and on the general line the schema-name rule on the own interface and builder files of every use that is not
//!   a generated flat storage; the storage composition rule per use; and that the manifest declares every `agent/` file
//!   once with the entry's item. The frozen record is [`FrozenEngine`] (`<frozen>/candidate.json`), the crate is
//!   `<frozen>/crate`.
//! - General-line manifest fields ([`EngineManifest::general_schema`]): the branch's `direction`, measured `findings`
//!   for the run's findings log, `next_session` (`continue` or `fresh`) and `base` (the version the submission's code
//!   derives from: the branch head, or the main-line head for a rebase). The schema-engine line refuses them.
//! - [`EngineBuilds`]: the whole-crate verify-and-compile run (the build a submission's evaluation uses) and the
//!   unverified diagnostic build (`rust_verify --no-verify`, never evidence), cached per exact crate content within a
//!   session, so a tool run and an evaluation of unchanged sources compile once.
//! - [`toolkit_digest`]: the identity of the engine toolkit (`sqlspec/engine_link/**`) every engine crate carries
//!   (`gendb_verification::obligations::engine_toolkit_files`), recorded with each frozen engine.
//! - **Stage runs** (`controller::request::EngineStage`): one engine source, one
//!   crate per workload. The manifest names no storage use of its own and has one [`WorkloadModules`] entry per workload
//!   (its storage uses and its module files under `<crate_dir>/workloads/<name>/`). [`freeze_stage_engine`] freezes one
//!   workload's crate ([`StageCrate`]): `src/agent/**` with that workload's module copied in as `agent/workload/**`
//!   (when the workspace has workload modules: they are optional together, and `src/agent/workload` itself is refused),
//!   over that workload's uses, schema and library, with the uniform flat access (`FlatAccess::Uniform`) and the run's
//!   stage rule set (`EngineRuleSet::for_stage`). The frozen record names the workload, its module files and the
//!   module's report (`engine_rules::workload_module_report`). [`write_root_from_version`] writes a stage run's first
//!   workspace from an accepted version of another general-line run. Every other freeze is as before.
//! - **Runs of several workloads** (`engine.workloads`; [`members`]): the stage
//!   form, plus the storage families of the workspace (`families`, each a `verus-family.json`), family uses
//!   (`{"name", "family"}`), the shared default module `<crate_dir>/workloads/default/` (`default_modules`) and data-only
//!   plans `<crate_dir>/plans/<workload>/<family>.rs`. [`freeze_member_crate`] freezes one workload's crate
//!   ([`MemberCrate`]): its own module `workloads/<workload>/` when it has one, else the default module, as
//!   `agent/workload/**`; each family use composed by GenDB into that workload's whole-schema instance
//!   (`storage::family::compose_instance`) and frozen as a workspace storage; the rules R3-R5
//!   (`verus::engine_rules::FAMILY_RULES`: no workspace storage, plans are data, an own module only beside an inherited
//!   storage). The frozen record's workload carries [`members::MemberRecord`] (its module, families, inherited storages,
//!   plans and the digest of the shared sources). [`members::write_side_root`] and [`members::write_source_root`] write
//!   a side's root workspace from a version folder or an exported engine folder.
//!
//! On the schema-engine line the whole-statement evaluator rule applies to engines in a wider form than for query
//! crates: one of the engine rules (`verus::engine_rules::
//! WHOLE_STATEMENT_EVALUATOR_RULE`: the evaluator modules, globs and aliases of `exec::relational`, and every function
//! that can reach the evaluator, by name), applied here and again at admission. The general line lifts it:
//! its version 0 is the interpreter.

use super::sessions::NextSession;
use crate::controller::author::{CandidateSubmission, resolve_candidate_manifest};
use crate::controller::records::write_new_json;
use crate::query::candidate::{
    CompilerChoice, FrozenModule, FrozenUse, ModuleDeclaration, ModuleRole, StorageUseDeclaration, UseContext, check_source_versions, crate_files,
    declared_agent_modules, inside, refuse_author_findings, resolve_uses,
};
use crate::query::compile::{self, DeclaredModule, declared_items};
use crate::query::host_locks::HostLocks;
use crate::storage::family::copy_author_tree;
use crate::storage::freeze::{FrozenStorage, freeze_error, read_frozen_storage};
use crate::storage::policy::StoredDataPolicy;
use crate::tools::TrialVerification;
use gendb_artifacts::ContentId;
use gendb_frontend::ast::TableDef;
use gendb_registry::CrateKind;
use gendb_runtime::abi::GENDB_ENGINE_SHIM_SOURCE;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::engine::engine_storage_findings;
use gendb_verification::obligations::{
    AssemblyError, ENGINE_ENTRY_IDENTITY, FlatAccess, StorageUse, check_engine_coverage, check_storage_composition, engine_crate_files_with,
    engine_toolkit_files, generated_flat_table, interpreter_engine, with_trusted_shim,
};
use gendb_verification::verus::engine_rules::{EngineLine, EngineRuleSet, workload_module_report};
use gendb_verification::verus::{AuthorRoot, FrameworkSource, FrozenCrate, RefusalRule, freeze_author_crate, scan_static_items};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Conventional file name of the engine manifest (the submission names its path).
pub const MANIFEST_FILE: &str = "verus-engine.json";
/// `kind` of a frozen engine candidate.
pub const CANDIDATE_KIND: &str = "verus_engine";
/// The item the fixed engine entry calls in `crate::agent`.
pub const REQUIRED_ITEMS: [&str; 1] = ["engine"];
/// The engine crate directory of the workspace (the manifest example's `crate_dir`).
pub const CRATE_DIRECTORY: &str = "engine";
/// The directory of the workload modules of a stage run, in the engine crate directory (`workloads/<name>/`).
pub const WORKLOADS_DIRECTORY: &str = "workloads";
/// The module of the shared engine a workload's module becomes in its crate (`crate::agent::workload`).
pub const WORKLOAD_MODULE: &str = "workload";
/// The identity the engine crate's generated headers name (`engine_crate_files(.., identity)`); admission regenerates
/// the framework files with it.
pub const GENERATION_IDENTITY: &str = "schema engine";
/// The shared default workload module's directory name under `<crate_dir>/workloads/` (runs of several workloads): the
/// module of every workload without one of its own.
pub const DEFAULT_WORKLOAD: &str = "default";
/// The directory of the plans in the engine crate directory (`plans/<workload>/<family>.rs`; runs of several workloads).
pub const PLANS_DIRECTORY: &str = "plans";

pub mod members;

/// SHA-256 of the engine toolkit every engine crate carries (paths and texts of `engine_toolkit_files`), recorded with
/// every frozen engine.
pub fn toolkit_digest() -> String {
    let mut hasher = Sha256::new();
    for file in engine_toolkit_files() {
        hasher.update(file.path.as_bytes());
        hasher.update([0]);
        hasher.update(file.text.as_bytes());
        hasher.update([0]);
    }
    hasher.finalize().iter().map(|b| format!("{b:02x}")).collect()
}

/// `verus-engine.json`. Paths are relative to the manifest's directory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EngineManifest {
    pub format_version: u32,
    pub crate_dir: PathBuf,
    /// The storages the engine reads, in the order of `Stores` and of the entry's `uses`; together they store every
    /// column of every table.
    pub storage_uses: Vec<StorageUseDeclaration>,
    pub modules: Vec<ModuleDeclaration>,
    #[serde(default)]
    pub compiler: Option<CompilerChoice>,
    #[serde(default)]
    pub notes: String,
    /// General line: the branch's direction (required on its first submission; restating it records a change).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub direction: Option<String>,
    /// General line: short measured lessons for the run's findings log.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub findings: Vec<String>,
    /// General line: go on in this session (default) or hand the branch to a fresh session after this evaluation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub next_session: Option<NextSession>,
    /// General line: the version this submission's code derives from (default: the branch head).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub base: Option<SubmissionBase>,
    /// Stage runs and runs of several workloads only: one entry per workload, its storage uses and its module files; the
    /// top-level `storage_uses` is then empty. Absent elsewhere (and the manifest keeps its JSON identity).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub workloads: Vec<WorkloadModules>,
    /// Runs of several workloads only: the storage families of the workspace, each by its `verus-family.json`
    /// (`storage::family`). Absent elsewhere (and the manifest keeps its JSON identity).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub families: Vec<FamilyDeclaration>,
    /// Runs of several workloads only: every `.rs` file of the shared default workload module
    /// `<crate_dir>/workloads/default/` exactly once (`file` relative to that directory; in a crate it is
    /// `agent/workload/<file>`), or none without that module. Absent elsewhere.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub default_modules: Vec<ModuleDeclaration>,
}

/// One storage family of a run of several workloads' manifest: its name (the instances' storage name) and its
/// `verus-family.json`, relative to the manifest's directory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyDeclaration {
    pub name: String,
    pub source: PathBuf,
}

/// One workload's part of a stage run's manifest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkloadModules {
    /// The workload's name (`engine.stage`'s).
    pub name: String,
    /// The storages its crate reads, in `Stores` order; together they store every column of every table of its schema.
    pub storage_uses: Vec<StorageUseDeclaration>,
    /// Every `.rs` file under `<crate_dir>/workloads/<name>/` exactly once (`file` relative to that directory), or none
    /// when the workspace has no workload modules.
    #[serde(default)]
    pub modules: Vec<ModuleDeclaration>,
}

/// Which crate of a stage run a freeze assembles ([`freeze_stage_engine`]).
#[derive(Clone, Copy, Debug)]
pub struct StageCrate<'a> {
    /// The workload whose crate this is.
    pub workload: &'a str,
    /// Every workload of the run, goal first: the manifest has one `workloads` entry for each.
    pub workloads: &'a [String],
}

/// Which crate of a run of several workloads a freeze assembles ([`freeze_member_crate`]).
#[derive(Clone, Copy, Debug)]
pub struct MemberCrate<'a> {
    /// The workload whose crate this is.
    pub workload: &'a str,
    /// The workloads the manifest has one `workloads` entry for, the primary first: every workload of the run, or only
    /// this one (the freeze of one side of the root, whose workspace names only its own workload).
    pub workloads: &'a [String],
    /// The workload's plain flat storages `(name, package)`, one per table in table order (admitted in its library;
    /// [`members::plain_flat_storages`]): the sources of every family instance it composes.
    pub flat_storages: &'a [(String, ContentId)],
}

/// The form of the crate a freeze assembles.
#[derive(Clone, Copy, Debug)]
enum CrateForm<'a> {
    /// A run of one workload ([`freeze_engine`]).
    One,
    /// A stage run's crate ([`freeze_stage_engine`]).
    Stage(&'a StageCrate<'a>),
    /// A run of several workloads' crate ([`freeze_member_crate`]).
    Members(&'a MemberCrate<'a>),
}

impl CrateForm<'_> {
    /// The workload of the crate and every workload with a manifest entry (`None` for a run of one workload).
    fn workloads(&self) -> Option<(&str, &[String])> {
        match self {
            CrateForm::One => None,
            CrateForm::Stage(stage) => Some((stage.workload, stage.workloads)),
            CrateForm::Members(member) => Some((member.workload, member.workloads)),
        }
    }
}

/// The version a general-line submission's code derives from: its parent, which it is raced against.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SubmissionBase {
    /// The branch head (the default; a merge session's base is the main-line head).
    BranchHead,
    /// The main-line head: the branch rebases onto it ("restarting a branch").
    MainLineHead,
}

impl EngineManifest {
    /// The generated example of the author workspace over `uses` (`(name, package)` of each seeded storage).
    pub fn example(uses: &[(String, ContentId)]) -> Self {
        Self {
            format_version: 1,
            crate_dir: CRATE_DIRECTORY.into(),
            storage_uses: uses.iter().map(|(name, package)| StorageUseDeclaration::admitted(name, *package)).collect(),
            modules: vec![ModuleDeclaration { file: "mod.rs".into(), role: ModuleRole::Entry, items: REQUIRED_ITEMS.map(String::from).to_vec() }],
            compiler: Some(CompilerChoice::default()),
            notes: String::new(),
            direction: None,
            findings: vec![],
            next_session: None,
            base: None,
            workloads: vec![],
            families: vec![],
            default_modules: vec![],
        }
    }

    /// The stage-form manifest over `workloads` (each with its storage uses): no storage use of its own, the modules,
    /// compiler and notes of `seed` (for example a version's seed manifest).
    pub fn stage_form(seed: &EngineManifest, workloads: Vec<WorkloadModules>) -> Self {
        Self { crate_dir: CRATE_DIRECTORY.into(), storage_uses: vec![], workloads, ..seed.for_seed() }
    }

    /// The manifest a version's folder keeps for seeding a later workspace: this one without the fields that belong
    /// to one submission (direction, findings, next session, base).
    pub fn for_seed(&self) -> Self {
        Self { direction: None, findings: vec![], next_session: None, base: None, ..self.clone() }
    }

    /// Whether a general-line field is set.
    pub fn has_general_fields(&self) -> bool {
        self.direction.is_some() || !self.findings.is_empty() || self.next_session.is_some() || self.base.is_some()
    }

    /// The manifest's JSON schema on the general line: [`EngineManifest::schema`] with the general-line fields.
    pub fn general_schema() -> Value {
        let mut schema = Self::schema();
        let properties = &mut schema["properties"];
        properties["direction"] = json!({"type":"string","minLength":1,"description":"the branch's direction: which areas it explores, how it differs from the other branches, what it expects to gain per template class; required on the branch's first submission"});
        properties["findings"] = json!({"type":"array","items":{"type":"string","minLength":1},"description":"short measured lessons from this submission for the run's findings log (FINDINGS.md)"});
        properties["next_session"] = json!({"enum":["continue","fresh"],"description":"continue (default): this session goes on after the evaluation; fresh: a fresh session continues the branch from its files"});
        properties["base"] = json!({"enum":["branch_head","main_line_head"],"description":"the version this submission's code derives from and is raced against: the branch head (default) or the main-line head (a rebase)"});
        schema
    }

    /// The manifest's JSON schema in a stage run: [`EngineManifest::general_schema`] with `workloads` (one entry per
    /// workload: its storage uses and module files) and no storage use of its own.
    pub fn stage_schema() -> Value {
        let mut schema = Self::general_schema();
        let uses = schema["properties"]["storage_uses"].clone();
        let modules = schema["properties"]["modules"].clone();
        schema["properties"]["storage_uses"] = json!({"type":"array","maxItems":0,"description":"empty in a stage run: each workload names its storage uses in workloads[]"});
        schema["properties"]["workloads"] = json!({"type":"array","minItems":1,"description":"one entry per workload of the run (its name as engine.stage gives it): the storage uses of its crate and the files of its module",
            "items":{"type":"object","additionalProperties":false,"required":["name","storage_uses"],"properties":{
                "name":{"type":"string"},
                "storage_uses":{"description":"the storages this workload's crate reads, in Stores field order; together they store every column of every table of its schema","type":"array","minItems":1,"items":uses["items"].clone()},
                "modules":{"type":"array","description":"every .rs file under <crate_dir>/workloads/<name>/ exactly once (file relative to that directory; in the crate it is agent/workload/<file>), or none when the workspace has no workload modules","items":modules["items"].clone()}}}});
        schema["required"] = json!(["format_version", "crate_dir", "storage_uses", "modules", "workloads"]);
        schema
    }

    /// The manifest's JSON schema in a run of several workloads: [`EngineManifest::stage_schema`] with `families`,
    /// `default_modules` and family uses (`{"name", "family"}`) in each workload's `storage_uses`; a workspace storage
    /// is refused there (R3, `storage_family_required`).
    pub fn members_schema() -> Value {
        let mut schema = Self::stage_schema();
        let modules = schema["properties"]["modules"]["items"].clone();
        let workload = &mut schema["properties"]["workloads"];
        workload["description"] = json!("one entry per workload of the run (its name as engine.workloads gives it): the storage uses of its crate and the files of its own module, if any");
        let item = &mut workload["items"]["properties"];
        item["modules"]["description"] = json!("every .rs file under <crate_dir>/workloads/<name>/ exactly once (file relative to that directory; in the crate it is agent/workload/<file>); none when the workload has no module of its own (it uses the default module). An own module is allowed only beside an inherited storage that is neither a family instance nor a plain flat storage (workload_module_scope)");
        let uses = &mut item["storage_uses"];
        uses["description"] = json!("the storages this workload's crate reads, in Stores field order; together they store every column of every table of its schema. New storage is a family use {\"name\": <family>, \"family\": <family>}; a workspace storage is refused (storage_family_required)");
        let use_properties = &mut uses["items"]["properties"];
        use_properties["family"] = json!({"type":"string","description":"a storage family of families[] (its name, equal to name): GenDB composes its instance over this workload's whole schema, with plans/<workload>/<family>.rs or the family's default_plan.rs"});
        use_properties["workspace"]["description"] = json!("refused in a run of several workloads (storage_family_required): write new storage as a storage family");
        uses["items"]["description"] = json!("exactly one of admitted or family");
        schema["properties"]["families"] = json!({"type":"array","description":"the storage families of the workspace: each written once (builder, interface and default plan generic over the schema) and composed by GenDB into every workload that uses it",
            "items":{"type":"object","additionalProperties":false,"required":["name","source"],"properties":{
                "name":{"type":"string","description":"the family's name (its verus-family.json name): every instance's storage name"},
                "source":{"type":"string","description":"its verus-family.json, relative to this manifest's directory (by convention storages/<name>/verus-family.json)"}}}});
        schema["properties"]["default_modules"] = json!({"type":"array","description":"every .rs file under <crate_dir>/workloads/default/ exactly once (file relative to that directory): the shared default workload module of every workload without one of its own; none without that directory","items":modules});
        schema
    }

    /// JSON schema of the manifest (author contract).
    pub fn schema() -> Value {
        json!({"type":"object","additionalProperties":false,"required":["format_version","crate_dir","storage_uses","modules"],
            "properties":{
                "format_version":{"const":1},
                "crate_dir":{"type":"string","description":"the engine crate directory relative to this manifest's directory, inside the author workspace, with no `..` component; the author owns only <crate_dir>/src/agent/**"},
                "storage_uses":{"type":"array","minItems":1,"description":"the storages the engine reads, in Stores field order; together they must store every column of every table (engine_storage_coverage_incomplete)",
                    "items":{"type":"object","additionalProperties":false,"required":["name"],"properties":{
                        "name":{"type":"string","description":"the storage's name (its package's or workspace storage's)"},
                        "admitted":{"type":"string","pattern":"^[0-9a-f]{64}$","description":"an admitted storage package id (storages.json use_as)"},
                        "workspace":{"type":"string","description":"a verus-storage.json of this workspace (built from admitted storages), relative to this manifest's directory"}},
                        "description":"exactly one of admitted or workspace"}},
                "modules":{"type":"array","minItems":1,"description":"every .rs file under src/agent exactly once",
                    "items":{"type":"object","additionalProperties":false,"required":["file","role","items"],"properties":{
                        "file":{"type":"string","description":"relative to src/agent, e.g. mod.rs or plan/join.rs"},
                        "role":{"enum":["entry","reader","kernel","helper"]},
                        "items":{"type":"array","items":{"type":"string"},"description":"functions this module contributes, named as Verus reports them relative to the module; engine must be declared in the entry module"}}}},
                "compiler":{"type":"object","additionalProperties":false,"required":["opt_level"],"properties":{
                    "opt_level":{"type":"integer","minimum":0,"maximum":3},"target_cpu":{"type":["string","null"]}},
                    "description":"optional rustc code generation; default opt_level 3, rustc default target cpu"},
                "notes":{"type":"string"}}})
    }

    /// The manifest's own rules (the schema cannot state them all), for the crate of `form` (a stage run's or a run of
    /// several workloads': every workload's entry checked).
    fn check(&self, form: CrateForm<'_>) -> Result<(), AdmissionError> {
        if self.format_version != 1 {
            return Err(AdmissionError::refusal("an engine manifest has format_version 1"));
        }
        let members_only = !self.families.is_empty() || !self.default_modules.is_empty() || self.all_uses().any(|u| u.family.is_some());
        if members_only && !matches!(form, CrateForm::Members(_)) {
            return Err(AdmissionError::refusal("verus-engine manifest: families, default_modules and family uses are fields of a run of several workloads (engine.workloads)"));
        }
        match form.workloads() {
            None => {
                if !self.workloads.is_empty() {
                    return Err(AdmissionError::refusal("verus-engine manifest: workloads is a stage-run field (engine.stage)"));
                }
                if self.modules.is_empty() || self.storage_uses.is_empty() {
                    return Err(AdmissionError::refusal("an engine manifest needs at least one storage use and one module"));
                }
                check_storage_uses(&self.storage_uses, "", &[])?;
            }
            Some((_, workloads)) => {
                let run = if matches!(form, CrateForm::Members(_)) { "a run of several workloads'" } else { "a stage run's" };
                if self.modules.is_empty() || !self.storage_uses.is_empty() {
                    return Err(AdmissionError::refusal(format!("{run} engine manifest has at least one module and no storage use of its own: each workload names its storage uses in workloads[]")));
                }
                let named: Vec<&str> = self.workloads.iter().map(|w| w.name.as_str()).collect();
                let mut expected: Vec<&str> = workloads.iter().map(String::as_str).collect();
                expected.sort();
                let mut given = named.clone();
                given.sort();
                if given != expected {
                    return Err(AdmissionError::refusal(format!("verus-engine manifest: workloads names {named:?}; {run} manifest has exactly one entry per workload {workloads:?}")));
                }
                for w in &self.workloads {
                    if w.storage_uses.is_empty() {
                        return Err(AdmissionError::refusal(format!("verus-engine manifest: workload {} needs at least one storage use", w.name)));
                    }
                    check_storage_uses(&w.storage_uses, &format!("workload {}: ", w.name), &self.families)?;
                    check_module_list(&w.modules, &format!("workload {}", w.name))?;
                }
                if matches!(form, CrateForm::Members(_)) {
                    self.check_members_fields()?;
                }
            }
        }
        if self.compiler.as_ref().is_some_and(|choice| choice.opt_level > 3) {
            return Err(AdmissionError::refusal("compiler.opt_level must be 0..=3"));
        }
        for required in REQUIRED_ITEMS {
            if !self.modules.iter().any(|m| m.role == ModuleRole::Entry && m.items.iter().any(|i| i == required)) {
                return Err(AdmissionError::refusal(format!("the entry module must declare item {required}")));
            }
        }
        if self.direction.as_deref().is_some_and(|d| d.trim().is_empty()) || self.findings.iter().any(|f| f.trim().is_empty()) {
            return Err(AdmissionError::refusal("direction and findings, when given, are not empty"));
        }
        Ok(())
    }
}

impl EngineManifest {
    /// Every storage use the manifest names (its own and every workload's).
    fn all_uses(&self) -> impl Iterator<Item = &StorageUseDeclaration> {
        self.storage_uses.iter().chain(self.workloads.iter().flat_map(|w| &w.storage_uses))
    }

    /// The rules of the fields of a run of several workloads: R3 (`storage_family_required`: no workspace storage use),
    /// families with distinct storage names and a source each, and the default module's files declared once each.
    fn check_members_fields(&self) -> Result<(), AdmissionError> {
        if let Some(u) = self.all_uses().find(|u| u.workspace.is_some()) {
            let rule = gendb_verification::verus::engine_rules::STORAGE_FAMILY_RULE;
            return Err(AdmissionError::refusal(format!("{}: storage use {} names a workspace storage ({})", rule.id, u.name, rule.refuses)));
        }
        let mut names = std::collections::BTreeSet::new();
        for family in &self.families {
            gendb_verification::obligations::StorageName::new(&family.name).map_err(|e| AdmissionError::refusal(format!("verus-engine manifest: families: {e}")))?;
            if !names.insert(family.name.as_str()) {
                return Err(AdmissionError::refusal(format!("verus-engine manifest: family {} is declared twice", family.name)));
            }
            if family.source.as_os_str().is_empty() {
                return Err(AdmissionError::refusal(format!("verus-engine manifest: family {} names its verus-family.json (source)", family.name)));
            }
        }
        check_module_list(&self.default_modules, "the default module")
    }
}

/// Each storage use of a list names exactly one of an admitted package, a workspace storage or (with `families`, a run
/// of several workloads) a family of `families` under the family's own name, and no storage twice (`what` prefixes the
/// refusal).
fn check_storage_uses(uses: &[StorageUseDeclaration], what: &str, families: &[FamilyDeclaration]) -> Result<(), AdmissionError> {
    let mut names = std::collections::BTreeSet::new();
    for storage_use in uses {
        if storage_use.source_count() != 1 {
            let sources = if families.is_empty() { "admitted or workspace" } else { "admitted or family" };
            return Err(AdmissionError::refusal(format!("{what}storage use {} needs exactly one of {sources}", storage_use.name)));
        }
        if let Some(family) = &storage_use.family {
            if family != &storage_use.name || !families.iter().any(|f| &f.name == family) {
                return Err(AdmissionError::refusal(format!(
                    "{what}storage use {}: family {family} must be one of families[] and the use is named after it ({{\"name\": \"{family}\", \"family\": \"{family}\"}})",
                    storage_use.name
                )));
            }
        }
        if !names.insert(storage_use.name.as_str()) {
            return Err(AdmissionError::refusal(format!("{what}storage {} is used twice", storage_use.name)));
        }
    }
    Ok(())
}

/// The module files of a list are declared once each (`what` names the list's module in the refusal).
fn check_module_list(modules: &[ModuleDeclaration], what: &str) -> Result<(), AdmissionError> {
    let mut files = std::collections::BTreeSet::new();
    match modules.iter().find(|m| !files.insert(m.file.as_str())) {
        Some(twice) => Err(AdmissionError::refusal(format!("verus-engine manifest: {what}: module {} declared twice", twice.file))),
        None => Ok(()),
    }
}

/// `candidate.json` of a frozen engine submission (the recorded candidate of the ledger's trial).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenEngine {
    pub kind: String,
    pub format_version: u32,
    pub entry_identity: String,
    /// SHA-256 of the toolkit files the crate was frozen with ([`toolkit_digest`]).
    pub toolkit_digest: String,
    pub storage_uses: Vec<FrozenUse>,
    pub compiler: CompilerChoice,
    /// The engine's `agent/` modules, then every workspace storage's modules.
    pub modules: Vec<FrozenModule>,
    /// Author files of the engine crate, relative to `src/`.
    pub author_files: Vec<String>,
    /// Framework files relative to `src/`, in generation order.
    pub framework_files: Vec<String>,
    pub notes: String,
    /// The engine source rules it was frozen under (`EngineRuleSet::record`: line, rules, constants, schema names).
    #[serde(default, skip_serializing_if = "Value::is_null")]
    pub rule_set: Value,
    /// A stage run's crate: its workload ([`FrozenWorkload`]). Absent for every other freeze.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub workload: Option<FrozenWorkload>,
}

/// The workload of a stage run's frozen crate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenWorkload {
    pub name: String,
    /// Its module files, relative to the module's directory (`<crate_dir>/workloads/<name>/`, or in a run of several
    /// workloads `<crate_dir>/workloads/default/` for the default module; each is `agent/workload/<file>` in the crate);
    /// empty when the crate has no workload module.
    pub module_files: Vec<String>,
    /// The crate's flat access module (`uniform` in a stage run and a run of several workloads).
    pub flat_access: FlatAccess,
    /// What the module holds (`engine_rules::workload_module_report`: files, lines, item kinds, loops, storages named).
    pub module_report: Value,
    /// A run of several workloads' crate: its module, families, inherited storages, plans and the shared sources'
    /// digest ([`members::MemberRecord`]). Absent in a stage run's (whose record keeps its JSON identity).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub member: Option<members::MemberRecord>,
}

impl FrozenEngine {
    /// The frozen engine crate under its freeze directory (`<frozen_dir>/crate`).
    pub fn crate_in(&self, frozen_dir: &Path) -> FrozenCrate {
        FrozenCrate::from_recorded_author_files(frozen_dir.join("crate"), self.author_files.clone(), self.framework_files.clone())
    }

    /// The engine crate's declared `agent/` modules.
    pub fn agent_modules(&self) -> Vec<DeclaredModule> {
        self.modules
            .iter()
            .filter(|m| m.file.starts_with("agent/"))
            .map(|m| DeclaredModule { file: m.file.clone(), role: m.role.clone(), items: m.items.clone() })
            .collect()
    }

    /// The frozen workspace storage of use `name` (`<frozen_dir>/storages/<name>`).
    pub fn workspace_storage(frozen_dir: &Path, name: &str) -> Result<(PathBuf, FrozenStorage), AdmissionError> {
        let dir = frozen_dir.join("storages").join(name);
        Ok((dir.clone(), read_frozen_storage(&dir)?))
    }

    /// Identity of the crate's author sources, storage interfaces, toolkit and compiler choice: two freezes with equal
    /// keys compile to the same library. Used only to reuse a session's compiled library.
    pub fn source_key(&self, krate: &FrozenCrate) -> Result<Vec<u8>, AdmissionError> {
        let mut key = serde_json::to_vec(&(&self.compiler, &self.storage_uses, &self.toolkit_digest)).map_err(AdmissionError::tool)?;
        // A stage run's crate: its workload and flat access too (every other key is as before).
        if let Some(workload) = &self.workload {
            key.extend(serde_json::to_vec(&(&workload.name, workload.flat_access)).map_err(AdmissionError::tool)?);
        }
        for file in krate.framework_files.iter().filter(|f| f.starts_with("stores/")).chain(&krate.author_files) {
            key.extend(file.as_bytes());
            key.push(0);
            key.extend(fs::read(krate.root.join("src").join(file)).map_err(AdmissionError::tool)?);
            key.push(0);
        }
        Ok(key)
    }
}

/// Where an engine crate is frozen from.
pub struct EngineFreeze<'a> {
    pub workspace: &'a Path,
    /// The dataset schema with the request's declared integrity constraints (a translated template's `tables`).
    pub schema: &'a [TableDef],
    /// The engine library (admitted storage uses are read from it).
    pub library: &'a Path,
    /// Admitted packages replaced by their current versions (re-verified against the current framework).
    pub substitutes: &'a BTreeMap<ContentId, ContentId>,
    pub policy: &'a StoredDataPolicy,
    /// The run's engine source rules (`verus::engine_rules::EngineRuleSet`: its line, the training templates'
    /// constants and, on the general line, the schema's names).
    pub rules: &'a EngineRuleSet,
}

/// A frozen engine and the framework files it was frozen with (for the author's workspace copy).
pub struct Frozen {
    pub engine: FrozenEngine,
    pub framework: Vec<FrameworkSource>,
    /// The author's workspace crate directory.
    pub workspace_crate: PathBuf,
}

/// Parse and freeze `submission` into the fresh directory `frozen_dir` (`crate/`, `storages/<name>/` for workspace
/// storages, `candidate.json`, `decision.json`, `manifest.json`); the checks are in the module documentation.
pub fn freeze_engine(context: &EngineFreeze<'_>, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Frozen, AdmissionError> {
    freeze(context, CrateForm::One, frozen_dir, submission)
}

/// [`freeze_engine`] for the crate of workload `stage.workload` of a stage run (module documentation, "Stage runs"):
/// `context` gives that workload's schema, library and storage policy and the run's stage rule set
/// (`EngineRuleSet::for_stage`; another rule set, a run of several workloads' included, is refused as a tool failure,
/// the caller's).
pub fn freeze_stage_engine(context: &EngineFreeze<'_>, stage: &StageCrate<'_>, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Frozen, AdmissionError> {
    if !context.rules.is_stage() || context.rules.is_members() {
        return Err(AdmissionError::tool("freeze_stage_engine: the rule set is not a stage run's (EngineRuleSet::for_stage; a run of several workloads freezes with freeze_member_crate)"));
    }
    freeze(context, CrateForm::Stage(stage), frozen_dir, submission)
}

/// [`freeze_engine`] for the crate of workload `member.workload` of a run of several workloads (module documentation,
/// "Runs of several workloads"): `context` gives that workload's schema, library and storage policy and the run's rule
/// set (`EngineRuleSet::for_members`; another is refused as a tool failure, the caller's). Besides the crate,
/// `frozen_dir` holds every composed family instance as a frozen workspace storage (`storages/<family>/`) and copies of
/// the shared sources the version's code is written from ([`members`]: `family-sources/`, `plans/`, `default-module/`).
pub fn freeze_member_crate(context: &EngineFreeze<'_>, member: &MemberCrate<'_>, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Frozen, AdmissionError> {
    if !context.rules.is_members() {
        return Err(AdmissionError::tool("freeze_member_crate: the rule set is not a run of several workloads' (EngineRuleSet::for_members)"));
    }
    freeze(context, CrateForm::Members(member), frozen_dir, submission)
}

/// [`freeze_engine`], [`freeze_stage_engine`] and [`freeze_member_crate`].
fn freeze(context: &EngineFreeze<'_>, form: CrateForm<'_>, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Frozen, AdmissionError> {
    let workspace = context.workspace.canonicalize().map_err(AdmissionError::tool)?;
    let (manifest_path, _) = resolve_candidate_manifest(&workspace, &submission.candidate_manifest)
        .map_err(|e| AdmissionError::missing_input(format!("{}: {e}", submission.candidate_manifest.display())))?;
    let bytes = fs::read(&manifest_path).map_err(|e| AdmissionError::missing_input(format!("{}: {e}", manifest_path.display())))?;
    let manifest: EngineManifest = serde_json::from_slice(&bytes).map_err(|e| AdmissionError::refusal(format!("verus-engine manifest: {e}")))?;
    manifest.check(form)?;
    if context.rules.line() == EngineLine::SchemaEngine && manifest.has_general_fields() {
        return Err(AdmissionError::refusal("verus-engine manifest: direction, findings, next_session and base are general-line fields"));
    }
    let base = manifest_path.parent().ok_or_else(|| AdmissionError::missing_input("manifest directory absent"))?;
    let crate_dir = inside(base, &manifest.crate_dir)?;
    if !crate_dir.starts_with(&workspace) {
        return Err(AdmissionError::refusal("crate_dir must be inside the author workspace"));
    }
    let agent = crate_dir.join("src/agent");
    if !agent.is_dir() {
        return Err(AdmissionError::missing_input(format!("{} is not a directory", agent.display())));
    }
    let workload = match form {
        CrateForm::One => None,
        CrateForm::Stage(stage) => Some(stage_workload(&manifest, &crate_dir, &agent, stage)?),
        CrateForm::Members(member) => Some(members::member_workload(&manifest, &crate_dir, &agent, member)?),
    };
    fs::create_dir(frozen_dir).map_err(AdmissionError::tool)?;
    // A run of several workloads: the families this workload uses composed into its instances (and copies of the
    // shared sources kept for the version's code).
    let families = match form {
        CrateForm::Members(member) => {
            let sources = members::SharedSources { manifest: &manifest, manifest_dir: base, workspace: &workspace, crate_dir: &crate_dir };
            members::compose_families(&sources, member, context.schema, frozen_dir)?
        }
        _ => members::ComposedFamilies::default(),
    };
    let declared_uses = workload.as_ref().map_or(&manifest.storage_uses, |w| &w.entry.storage_uses);
    let use_context = UseContext { library: context.library, substitutes: context.substitutes, policy: context.policy, families: &families.uses };
    let uses = resolve_uses(&use_context, declared_uses, base, &workspace, frozen_dir, context.schema)?;
    families.remove_scratch()?;
    check_source_versions(&uses)?;
    let storage_uses: Vec<StorageUse<'_>> = uses.iter().map(|u| StorageUse { name: &u.name, declaration: &u.frozen.declaration, interface: &u.interface }).collect();
    check_engine_coverage(context.schema, &storage_uses).map_err(|e| AdmissionError::refusal(e.to_string()))?;
    let storages = match (&form, &workload) {
        (CrateForm::Members(_), Some(w)) => Some(members::check_module_scope(w, &uses, context.schema)?),
        _ => None,
    };
    let access = if form.workloads().is_some() { FlatAccess::Uniform } else { FlatAccess::AsUsed };
    let framework = engine_crate_files_with(context.schema, &storage_uses, GENERATION_IDENTITY, access).map_err(|e| match e.failure_class() {
        "missing_input" => AdmissionError::missing_input(e),
        "refusal" => AdmissionError::refusal(e),
        _ => AdmissionError::tool(e),
    })?;
    let framework = with_trusted_shim(framework, GENDB_ENGINE_SHIM_SOURCE);
    // A crate with a workload module freezes `src/agent/**` with that module as `agent/workload/**`, composed in a
    // scratch tree that is removed once the crate is frozen.
    let composed = frozen_dir.join("composed-agent");
    let module_dir = workload.as_ref().and_then(|w| w.module_dir.as_deref());
    let source = match module_dir {
        Some(module) => {
            compose_agent(&agent, module, &composed).inspect_err(|_| {
                let _ = fs::remove_dir_all(&composed);
            })?;
            composed.as_path()
        }
        None => agent.as_path(),
    };
    let frozen_crate = freeze_author_crate(&framework, &[AuthorRoot { crate_directory: "agent", source }], &frozen_dir.join("crate"));
    if module_dir.is_some() {
        fs::remove_dir_all(&composed).map_err(AdmissionError::tool)?;
    }
    let krate = frozen_crate.map_err(freeze_error)?;
    let engine_files = crate_files(&krate)?;
    refuse_author_findings(&engine_files)?;
    refuse_engine_static_items(&engine_files)?;
    refuse_engine_rule_findings(&engine_files, context.rules)?;
    if context.rules.line() == EngineLine::General {
        for u in uses.iter().filter(|u| generated_flat_table(context.schema, &StorageUse { name: &u.name, declaration: &u.frozen.declaration, interface: &u.interface }).is_none()) {
            refuse_findings("schema-name findings in storage ".to_string() + u.name.as_str(), engine_storage_findings(&u.storage_files, &u.name, context.rules))?;
        }
    }
    for u in &uses {
        check_storage_composition(&u.storage_files, &engine_files, &u.name).map_err(|e| AdmissionError::refusal(format!("storage composition of {}: {e}", u.name)))?;
    }
    let mut declared = manifest.modules.clone();
    if let Some(w) = &workload {
        declared.extend(w.module_files.iter().map(|m| ModuleDeclaration { file: format!("{WORKLOAD_MODULE}/{}", m.file), ..m.clone() }));
    }
    let mut modules = declared_agent_modules(&declared, &krate)?;
    modules.extend(uses.iter().flat_map(|u| u.modules.clone()));
    let module_report = workload_module_report(&engine_files);
    let member = match (&workload, storages) {
        (Some(w), Some(storages)) => Some(members::member_record(w, &families, storages, &module_report, frozen_dir)?),
        _ => None,
    };
    let frozen_workload = workload.as_ref().map(|w| FrozenWorkload {
        name: w.entry.name.clone(),
        module_files: w.module_files.iter().map(|m| m.file.clone()).collect(),
        flat_access: access,
        module_report: module_report.clone(),
        member,
    });
    let engine = FrozenEngine {
        kind: CANDIDATE_KIND.into(),
        format_version: 1,
        entry_identity: ENGINE_ENTRY_IDENTITY.into(),
        toolkit_digest: toolkit_digest(),
        storage_uses: uses.into_iter().map(|u| u.frozen).collect(),
        compiler: manifest.compiler.clone().unwrap_or_default(),
        modules,
        author_files: krate.author_files.clone(),
        framework_files: krate.framework_files.clone(),
        notes: manifest.notes.clone(),
        rule_set: context.rules.record(),
        workload: frozen_workload,
    };
    let record = |name: &str, value: Value| write_new_json(&frozen_dir.join(name), &value).map_err(AdmissionError::tool);
    record("candidate.json", json!(engine))?;
    record("decision.json", json!(submission))?;
    record("manifest.json", json!(manifest))?;
    Ok(Frozen { engine, framework, workspace_crate: crate_dir })
}

/// The workload of a stage crate's or a run of several workloads' crate's freeze: its manifest entry, the module the
/// crate composes as `agent/workload/` (`None`: no module) and that module's file declarations, and in a run of several
/// workloads which module it is.
struct CrateWorkload<'m> {
    entry: &'m WorkloadModules,
    module_dir: Option<PathBuf>,
    module_files: &'m [ModuleDeclaration],
    module: Option<members::MemberModule>,
}

/// The workload `stage.workload` of the manifest, with the checks of the workspace's workload modules: `src/agent/workload`
/// is refused (each crate composes it), the directories under `<crate_dir>/workloads/` are exactly one per workload or
/// none (optional together; without them no workload declares a module), and a workload with modules has its `mod.rs`.
fn stage_workload<'m>(manifest: &'m EngineManifest, crate_dir: &Path, agent: &Path, stage: &StageCrate<'_>) -> Result<CrateWorkload<'m>, AdmissionError> {
    refuse_composed_module_directory(agent)?;
    let entry = manifest.workloads.iter().find(|w| w.name == stage.workload).ok_or_else(|| AdmissionError::tool(format!("the manifest has no entry for workload {}", stage.workload)))?;
    let root = crate_dir.join(WORKLOADS_DIRECTORY);
    let mut present = vec![];
    if root.is_dir() {
        for item in fs::read_dir(&root).map_err(AdmissionError::tool)? {
            let item = item.map_err(AdmissionError::tool)?;
            let name = item.file_name().to_string_lossy().into_owned();
            let is_dir = item.file_type().map_err(AdmissionError::tool)?.is_dir();
            if !is_dir || !stage.workloads.contains(&name) {
                return Err(AdmissionError::refusal(format!("{WORKLOADS_DIRECTORY}/{name}: {WORKLOADS_DIRECTORY}/ holds one directory per workload {:?} and nothing else", stage.workloads)));
            }
            present.push(name);
        }
    }
    if present.is_empty() {
        if let Some(w) = manifest.workloads.iter().find(|w| !w.modules.is_empty()) {
            return Err(AdmissionError::refusal(format!("verus-engine manifest: workload {} declares modules but {WORKLOADS_DIRECTORY}/{}/ does not exist", w.name, w.name)));
        }
        return Ok(CrateWorkload { entry, module_dir: None, module_files: &entry.modules, module: None });
    }
    if let Some(missing) = stage.workloads.iter().find(|w| !present.contains(w)) {
        return Err(AdmissionError::refusal(format!(
            "{WORKLOADS_DIRECTORY}/{missing}/ is missing: workload modules are optional together (every workload has its module, or none has)"
        )));
    }
    let module_dir = root.join(stage.workload);
    if !module_dir.join("mod.rs").is_file() {
        return Err(AdmissionError::refusal(format!("{WORKLOADS_DIRECTORY}/{}/mod.rs is missing: a workload's module root is its mod.rs (crate::agent::{WORKLOAD_MODULE})", stage.workload)));
    }
    Ok(CrateWorkload { entry, module_dir: Some(module_dir), module_files: &entry.modules, module: None })
}

/// `src/agent/workload` is refused: each crate composes it from the workload modules under `workloads/`.
fn refuse_composed_module_directory(agent: &Path) -> Result<(), AdmissionError> {
    if fs::symlink_metadata(agent.join(WORKLOAD_MODULE)).is_ok() {
        return Err(AdmissionError::refusal(format!(
            "src/agent/{WORKLOAD_MODULE} is each workload's module in its crate (composed from {WORKLOADS_DIRECTORY}/<name>/): write the workload modules under {WORKLOADS_DIRECTORY}/<name>/ instead"
        )));
    }
    Ok(())
}

/// `<to>/` = a copy of the shared engine `agent` with the workload's module `module` as its `workload/` (file bytes
/// unchanged): the author root one stage crate is frozen from. Only directories and regular files are copied; anything
/// else (a symlink) is refused, as the freeze refuses it in an author root.
fn compose_agent(agent: &Path, module: &Path, to: &Path) -> Result<(), AdmissionError> {
    copy_author_tree(agent, to)?;
    copy_author_tree(module, &to.join(WORKLOAD_MODULE))
}

/// The root of a stage run's first workspace from an accepted version of another general-line run: the
/// folder's `code/agent/**` copied into `<workspace>/engine/src/agent/` (writable), and the
/// stage-form manifest `verus-engine.json` ([`EngineManifest::stage_form`]): the version's module list, compiler and
/// notes (its seed manifest, else its manifest), no storage use of its own, and `workloads` as given (each workload's
/// storage uses; no module: the version's own shape). Refused (missing input): a folder whose `node.json` is not an
/// accepted version, or without `code/agent/mod.rs` or a manifest; a workspace that already has `engine/src/agent`.
/// Returns the written author files (relative to the crate's `src/`).
pub fn write_root_from_version(workspace: &Path, version_dir: &Path, workloads: Vec<WorkloadModules>) -> Result<Vec<String>, AdmissionError> {
    let (code, seed) = seed_version_parts(version_dir)?;
    write_seed_workspace(workspace, &code, &EngineManifest::stage_form(&seed, workloads))
}

/// The root of a continued run's first workspace (`controller::request::EngineRequest::seed_version`)
/// from an accepted version of another general-line run of one workload: the folder's `code/agent/**` copied into
/// `<workspace>/engine/src/agent/` (writable) and its manifest as `verus-engine.json` ([`EngineManifest::for_seed`]: its
/// storage uses, module list, compiler and notes, without the fields of one submission). Refused (missing input) as
/// [`write_root_from_version`] refuses, and for a stage version (its storage uses are per workload). Returns the
/// written author files (relative to the crate's `src/`).
pub fn write_root_from_seed_version(workspace: &Path, version_dir: &Path) -> Result<Vec<String>, AdmissionError> {
    let (code, seed) = seed_version_parts(version_dir)?;
    if !seed.workloads.is_empty() {
        return Err(AdmissionError::missing_input(format!(
            "seed version {}: a stage version names its storage uses per workload; a continued run of one workload starts from a version of a one-workload run",
            version_dir.display()
        )));
    }
    write_seed_workspace(workspace, &code, &EngineManifest { crate_dir: CRATE_DIRECTORY.into(), ..seed.for_seed() })
}

/// The parts of an accepted version folder a root is written from: its `code/agent` directory and its manifest (its
/// seed manifest, else its manifest). Refused (missing input): a folder whose `node.json` is not an accepted version,
/// or without `code/agent/mod.rs` or a manifest.
fn seed_version_parts(version_dir: &Path) -> Result<(PathBuf, EngineManifest), AdmissionError> {
    let missing = |what: String| AdmissionError::missing_input(format!("seed version {}: {what}", version_dir.display()));
    let node: Value = crate::controller::records::read_json(&version_dir.join("node.json")).map_err(|e| missing(e.to_string()))?;
    if node["accepted"] != true {
        return Err(missing("its node.json is not an accepted version".into()));
    }
    let code = version_dir.join("code/agent");
    if !code.join("mod.rs").is_file() {
        return Err(missing("no code/agent/mod.rs".into()));
    }
    let manifest_file = ["seed-manifest.json", "manifest.json"].into_iter().map(|f| version_dir.join(f)).find(|p| p.is_file()).ok_or_else(|| missing("no manifest".into()))?;
    let seed: EngineManifest = crate::controller::records::read_json(&manifest_file).map_err(|e| missing(e.to_string()))?;
    Ok((code, seed))
}

/// `code` copied into `<workspace>/engine/src/agent/` (a fresh workspace: an existing `agent` directory is a tool
/// failure) and `manifest` written as `verus-engine.json`. Returns the written author files (relative to the crate's
/// `src/`), sorted.
fn write_seed_workspace(workspace: &Path, code: &Path, manifest: &EngineManifest) -> Result<Vec<String>, AdmissionError> {
    let agent = workspace.join(CRATE_DIRECTORY).join("src/agent");
    if fs::symlink_metadata(&agent).is_ok() {
        return Err(AdmissionError::tool(format!("{} exists: the root is written into a fresh workspace", agent.display())));
    }
    copy_author_tree(code, &agent)?;
    fs::write(workspace.join(MANIFEST_FILE), format!("{}\n", serde_json::to_string_pretty(manifest).map_err(AdmissionError::tool)?)).map_err(AdmissionError::tool)?;
    let mut files = vec![];
    let mut stack = vec![(agent.clone(), "agent".to_string())];
    while let Some((dir, prefix)) = stack.pop() {
        for item in fs::read_dir(&dir).map_err(AdmissionError::tool)? {
            let item = item.map_err(AdmissionError::tool)?;
            let path = format!("{prefix}/{}", item.file_name().to_string_lossy());
            if item.file_type().map_err(AdmissionError::tool)?.is_dir() {
                stack.push((item.path(), path));
            } else {
                files.push(path);
            }
        }
    }
    files.sort();
    Ok(files)
}

/// The notes of version 0's manifest.
pub const VERSION_ZERO_NOTES: &str = "version 0 of the general engine, generated by GenDB (gendb-interpreter-engine-v0): every table read from its flat storage, every statement answered by SQLSpec's verified interpreter (exec_ordered)";

/// The generator of a root version's `agent/` files from the schema and the flat uses (version 0:
/// `gendb_verification::obligations::interpreter_engine`).
pub type RootAgentGenerator = fn(&[TableDef], &[StorageUse<'_>]) -> Result<Vec<FrameworkSource>, AssemblyError>;

/// Write version 0 of the general line into the workspace of `context`: its
/// manifest `verus-engine.json` over the storage uses `uses` (the flat storage of every table, in `Stores` order) and
/// its `agent/` sources, generated from the schema and those uses by
/// `gendb_verification::obligations::interpreter_engine` (identity `gendb-interpreter-engine-v0`). `scratch` receives
/// what resolving the uses writes. Returns the written author files (relative to the crate's `src/`).
pub fn write_version_zero(context: &EngineFreeze<'_>, uses: &[(String, ContentId)], scratch: &Path) -> Result<Vec<String>, AdmissionError> {
    write_root_version(context, uses, scratch, interpreter_engine, VERSION_ZERO_NOTES)
}

/// [`write_version_zero`] with the `agent/` files of `generate` and the manifest notes `notes`: the root version a run
/// is seeded with (`engine::branches::RootSource`; in production always version 0).
pub fn write_root_version(context: &EngineFreeze<'_>, uses: &[(String, ContentId)], scratch: &Path, generate: RootAgentGenerator, notes: &str) -> Result<Vec<String>, AdmissionError> {
    let workspace = context.workspace;
    let manifest = EngineManifest { notes: notes.into(), ..EngineManifest::example(uses) };
    fs::create_dir_all(workspace).map_err(AdmissionError::tool)?;
    fs::write(workspace.join(MANIFEST_FILE), format!("{}\n", serde_json::to_string_pretty(&manifest).map_err(AdmissionError::tool)?)).map_err(AdmissionError::tool)?;
    fs::create_dir_all(scratch).map_err(AdmissionError::tool)?;
    let workspace = workspace.canonicalize().map_err(AdmissionError::tool)?;
    let no_families = BTreeMap::new();
    let use_context = UseContext { library: context.library, substitutes: context.substitutes, policy: context.policy, families: &no_families };
    let resolved = resolve_uses(&use_context, &manifest.storage_uses, &workspace, &workspace, scratch, context.schema)?;
    let storage_uses: Vec<StorageUse<'_>> = resolved.iter().map(|u| StorageUse { name: &u.name, declaration: &u.frozen.declaration, interface: &u.interface }).collect();
    let files = generate(context.schema, &storage_uses).map_err(|e| match e.failure_class() {
        "missing_input" => AdmissionError::missing_input(e),
        "refusal" => AdmissionError::refusal(e),
        _ => AdmissionError::tool(e),
    })?;
    let src = workspace.join(CRATE_DIRECTORY).join("src");
    for file in &files {
        let path = src.join(&file.path);
        fs::create_dir_all(path.parent().unwrap_or(&src)).map_err(AdmissionError::tool)?;
        fs::write(&path, &file.text).map_err(AdmissionError::tool)?;
    }
    Ok(files.into_iter().map(|f| f.path).collect())
}

/// The static-item rule of engine author files: the query rule's lexical scan (`verus::scan_static_items`) with the
/// engine's reason. Every engine call is measured in a fresh child process, but a call within one process may follow
/// another (the warm and hot calls of a cell), so nothing computed in one call may be kept for a later one.
pub const ENGINE_STATIC_ITEM_RULE: RefusalRule = RefusalRule {
    id: "static_item",
    refuses: "a `static` item (the keyword `static`, not the `'static` lifetime) in an engine author file",
    reason: "Verus admits an `exec static` atomic with load and store under --no-cheating (shown by a probe), so a static could carry a value from one engine call to the next (the warm and hot calls of a timing cell share a process); an engine call keeps nothing for a later call. Constants (`const`) stay allowed",
};

/// [`ENGINE_STATIC_ITEM_RULE`] over every `agent/` file: the first finding refuses the submission.
fn refuse_engine_static_items(files: &[FrameworkSource]) -> Result<(), AdmissionError> {
    match files.iter().filter(|f| f.path.starts_with("agent/")).flat_map(|f| scan_static_items(&f.path, &f.text)).next() {
        Some(found) => Err(AdmissionError::refusal(format!("{}: {}:{}: {} ({})", ENGINE_STATIC_ITEM_RULE.id, found.file, found.line, ENGINE_STATIC_ITEM_RULE.refuses, ENGINE_STATIC_ITEM_RULE.reason))),
        None => Ok(()),
    }
}

/// The engine rules of the run's line (`verus::engine_rules::EngineRuleSet`) over every `agent/` file.
fn refuse_engine_rule_findings(files: &[FrameworkSource], rules: &EngineRuleSet) -> Result<(), AdmissionError> {
    let findings: Vec<_> = files.iter().filter(|f| f.path.starts_with("agent/")).flat_map(|f| rules.scan_agent_source(&f.path, &f.text)).collect();
    refuse_findings("engine rule findings".to_string(), findings)
}

/// Refuse with `what` and every finding (file, line, rule, detail); nothing found passes.
fn refuse_findings(what: String, findings: Vec<gendb_verification::verus::RefusalFinding>) -> Result<(), AdmissionError> {
    if findings.is_empty() {
        return Ok(());
    }
    Err(AdmissionError::refusal(format!("{what} {}", json!(findings.iter().map(|f| json!({"file":f.file,"line":f.line,"rule":f.rule,"detail":f.detail})).collect::<Vec<_>>()))))
}

/// The compiled libraries of one session's frozen engine crates, by build mode and source key.
#[derive(Default)]
pub struct EngineBuilds {
    builds: BTreeMap<(TrialVerification, Vec<u8>), (PathBuf, Value)>,
    /// Whole-crate verifications that passed, by source key.
    verified: BTreeMap<Vec<u8>, Value>,
}

/// One compiled engine library.
#[derive(Clone, Debug)]
pub struct EngineBuild {
    pub library: PathBuf,
    /// The build record (verification counts, wall time, argv, items, outcome).
    pub record: Value,
    /// Reused from an earlier build of identical content in this session.
    pub reused: bool,
}

impl EngineBuilds {
    /// The whole-crate verify-and-compile run of a frozen engine, reused for equal sources unless `fresh` (a
    /// submission's evaluation always runs it again); every declared `agent/` item must be one Verus checked.
    pub fn compile(&mut self, locks: &HostLocks, engine: &FrozenEngine, frozen_dir: &Path, out: &Path, fresh: bool) -> Result<EngineBuild, AdmissionError> {
        let krate = engine.crate_in(frozen_dir);
        let key = (TrialVerification::WholeCrate, engine.source_key(&krate)?);
        if !fresh && let Some((library, record)) = self.builds.get(&key) {
            return Ok(EngineBuild { library: library.clone(), record: record.clone(), reused: true });
        }
        let (run, library) = compile::compile(locks, &krate, CrateKind::Engine, &engine.compiler, out)?;
        let items = declared_items(&engine.agent_modules(), &krate, CrateKind::Engine, run["stdout"].as_str().unwrap_or_default())?;
        let record = json!({"verification":run["verification"],"wall_ns":run["wall_ns"],"argv":run["argv"],"library":library,"items":items,"record":out.join("run.json"),
            "outcome":run["outcome"],"detail":run["detail"]});
        self.verified.insert(key.1.clone(), json!({"verification":run["verification"],"record":out.join("run.json")}));
        self.builds.insert(key, (library.clone(), record.clone()));
        Ok(EngineBuild { library, record, reused: false })
    }

    /// The whole-crate verify-and-compile run that an earlier evaluation of this frozen engine recorded in `out` (its
    /// `run.json` and the library beside it), read back without running Verus again (`gendb engine re-evaluate`, which
    /// re-times a recorded attempt). Refused unless that run verified the entire crate with 0 errors and wrote its
    /// library in `out`; the build record is the one [`EngineBuilds::compile`] makes, so the admission reads the same
    /// Verus record (trusted as recorded, like an admission resumed from its intent).
    pub fn recorded(&mut self, engine: &FrozenEngine, frozen_dir: &Path, out: &Path) -> Result<EngineBuild, AdmissionError> {
        let krate = engine.crate_in(frozen_dir);
        let key = (TrialVerification::WholeCrate, engine.source_key(&krate)?);
        let record_file = out.join("run.json");
        let run: Value = crate::controller::records::read_json(&record_file).map_err(AdmissionError::tool)?;
        let verification = &run["verification"];
        let library = PathBuf::from(run["artifact"].as_str().unwrap_or_default());
        let verified_whole = run["outcome"] == "compiled" && verification["success"] == true && verification["errors"] == 0 && verification["is-verifying-entire-crate"] == true;
        if !verified_whole || library.parent() != Some(out) || !library.is_file() {
            return Err(AdmissionError::tool(format!("{}: not a recorded whole-crate Verus run with 0 errors and its library in {}", record_file.display(), out.display())));
        }
        let items = declared_items(&engine.agent_modules(), &krate, CrateKind::Engine, run["stdout"].as_str().unwrap_or_default())?;
        let record = json!({"verification":run["verification"],"wall_ns":run["wall_ns"],"argv":run["argv"],"library":library,"items":items,"record":record_file,
            "outcome":run["outcome"],"detail":run["detail"],"recorded":"the Verus run of this frozen crate's first evaluation, read back; Verus was not run again"});
        self.verified.insert(key.1.clone(), json!({"verification":run["verification"],"record":record_file}));
        self.builds.insert(key, (library.clone(), record.clone()));
        Ok(EngineBuild { library, record, reused: true })
    }

    /// The unverified diagnostic build (`rust_verify --no-verify`), reused for equal sources within this mode only.
    pub fn compile_unverified(&mut self, locks: &HostLocks, engine: &FrozenEngine, frozen_dir: &Path, out: &Path) -> Result<EngineBuild, AdmissionError> {
        let krate = engine.crate_in(frozen_dir);
        let key = (TrialVerification::NotRun, engine.source_key(&krate)?);
        if let Some((library, record)) = self.builds.get(&key) {
            return Ok(EngineBuild { library: library.clone(), record: record.clone(), reused: true });
        }
        let (run, library) = compile::compile_unverified(locks, &krate, CrateKind::Engine, &engine.compiler, out)?;
        let record = json!({"verification":crate::tools::bench::UNVERIFIED_LABEL,"verus_summary":run["verification"],"wall_ns":run["wall_ns"],"argv":run["argv"],
            "library":library,"record":out.join("run.json"),"outcome":run["outcome"],"detail":run["detail"]});
        self.builds.insert(key, (library.clone(), record.clone()));
        Ok(EngineBuild { library, record, reused: false })
    }

    /// One whole-crate verification (no library), skipped for content verified whole before in this session.
    pub fn verify(&mut self, locks: &HostLocks, engine: &FrozenEngine, frozen_dir: &Path, out: &Path) -> Result<(Value, bool), AdmissionError> {
        let krate = engine.crate_in(frozen_dir);
        let key = engine.source_key(&krate)?;
        if let Some(record) = self.verified.get(&key) {
            return Ok((record.clone(), true));
        }
        let run = compile::verify(locks, &krate, CrateKind::Engine, &engine.compiler, out)?;
        let record = json!({"verification":run["verification"],"wall_ns":run["wall_ns"],"argv":run["argv"],"record":out.join("run.json")});
        self.verified.insert(key, record.clone());
        Ok((record, false))
    }
}

/// A short identity of an engine crate's exact content (`query::candidate::crate_version` of its source key).
pub fn engine_version_id(engine: &FrozenEngine, frozen_dir: &Path) -> Result<String, AdmissionError> {
    Ok(crate::query::candidate::crate_version(&engine.source_key(&engine.crate_in(frozen_dir))?))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn engine_manifest_rules() {
        let package = ContentId::from_bytes([7; 32]);
        let manifest = EngineManifest::example(&[("facts".into(), package)]);
        manifest.check(CrateForm::One).unwrap();
        assert_eq!(serde_json::from_value::<EngineManifest>(json!(manifest)).unwrap(), manifest);
        let mut twice = manifest.clone();
        twice.storage_uses.push(twice.storage_uses[0].clone());
        assert!(twice.check(CrateForm::One).unwrap_err().message.contains("used twice"));
        let mut both = manifest.clone();
        both.storage_uses[0].workspace = Some("s.json".into());
        assert!(both.check(CrateForm::One).unwrap_err().message.contains("exactly one"));
        let mut no_engine = manifest.clone();
        no_engine.modules[0].items = vec!["query".into()];
        assert_eq!(no_engine.check(CrateForm::One).unwrap_err().to_string(), "refusal: the entry module must declare item engine");
        let mut format = manifest;
        format.format_version = 2;
        assert!(format.check(CrateForm::One).is_err());
    }

    fn admitted(name: &str, byte: u8) -> StorageUseDeclaration {
        StorageUseDeclaration::admitted(name, ContentId::from_bytes([byte; 32]))
    }

    fn module(file: &str, role: ModuleRole) -> ModuleDeclaration {
        ModuleDeclaration { file: file.into(), role, items: if role == ModuleRole::Entry { vec!["engine".into()] } else { vec![] } }
    }

    /// A stage run's manifest: every workload's entry once, its storage uses, no top-level use;
    /// `workloads` refused outside stage runs and absent from the JSON when empty; the stage schema names it.
    #[test]
    fn stage_manifest_rules() {
        let names = vec!["sec".to_string(), "tpch".to_string()];
        let stage = StageCrate { workload: "sec", workloads: &names };
        let entry = |name: &str, uses: Vec<StorageUseDeclaration>, modules: Vec<ModuleDeclaration>| WorkloadModules { name: name.into(), storage_uses: uses, modules };
        let seed = EngineManifest::example(&[("narrowpack".into(), ContentId::from_bytes([1; 32]))]);
        let manifest = EngineManifest::stage_form(&seed, vec![entry("tpch", vec![admitted("narrowpack", 1)], vec![]), entry("sec", vec![admitted("flat_sub", 2)], vec![])]);
        manifest.check(CrateForm::Stage(&stage)).unwrap();
        assert!(manifest.storage_uses.is_empty() && json!(manifest)["workloads"][0]["name"] == "tpch");
        assert_eq!(serde_json::from_value::<EngineManifest>(json!(manifest)).unwrap(), manifest);
        assert!(json!(seed).get("workloads").is_none(), "a manifest without workloads keeps its JSON identity");
        assert!(manifest.check(CrateForm::One).unwrap_err().message.contains("stage-run field"));
        assert!(seed.check(CrateForm::Stage(&stage)).unwrap_err().message.contains("no storage use of its own"));
        let refused = |edit: &dyn Fn(&mut EngineManifest), words: &str| {
            let mut m = manifest.clone();
            edit(&mut m);
            let error = m.check(CrateForm::Stage(&stage)).unwrap_err().message;
            assert!(error.contains(words), "{words}: {error}");
        };
        refused(&|m| { m.workloads.pop(); }, "exactly one entry per workload");
        refused(&|m| m.workloads[1].name = "tpch".into(), "exactly one entry per workload");
        refused(&|m| m.workloads.push(entry("other", vec![admitted("x", 3)], vec![])), "exactly one entry per workload");
        refused(&|m| m.workloads[0].storage_uses.clear(), "workload tpch needs at least one storage use");
        refused(&|m| m.workloads[1].storage_uses.push(admitted("flat_sub", 4)), "workload sec: storage flat_sub is used twice");
        refused(&|m| m.workloads[1].modules = vec![module("mod.rs", ModuleRole::Helper), module("mod.rs", ModuleRole::Helper)], "module mod.rs declared twice");
        let schema = EngineManifest::stage_schema();
        assert_eq!(schema["properties"]["storage_uses"]["maxItems"], 0);
        assert!(schema["properties"]["workloads"]["items"]["properties"]["storage_uses"]["items"]["properties"]["admitted"].is_object());
        assert!(schema["required"].as_array().unwrap().contains(&json!("workloads")) && schema["properties"]["direction"].is_object());
    }

    fn write(path: &Path, text: &str) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    fn tree(dir: &Path) -> Vec<String> {
        let mut files = vec![];
        let mut stack = vec![(dir.to_path_buf(), String::new())];
        while let Some((d, prefix)) = stack.pop() {
            for item in fs::read_dir(&d).unwrap() {
                let item = item.unwrap();
                let name = format!("{prefix}{}", item.file_name().to_string_lossy());
                if item.file_type().unwrap().is_dir() { stack.push((item.path(), format!("{name}/"))) } else { files.push(name) }
            }
        }
        files.sort();
        files
    }

    /// The workload modules of a stage workspace: each crate composes the shared `src/agent/**`
    /// with its own workload's module as `workload/**` (the file list per workload); without `workloads/` nothing is
    /// composed; `src/agent/workload`, a missing or unknown workload directory, declared modules without their
    /// directory, a module without `mod.rs` and a symlink are refused. The rule set must be a stage run's.
    #[test]
    fn stage_workload_modules_compose_per_workload() {
        let root = crate::controller::test_support::scratch_root("engine-stage-compose");
        let crate_dir = root.join("engine");
        let agent = crate_dir.join("src/agent");
        write(&agent.join("mod.rs"), "pub mod workload;\npub mod plan;\n");
        write(&agent.join("plan/join.rs"), "// join\n");
        write(&crate_dir.join("workloads/sec/mod.rs"), "// sec\n");
        write(&crate_dir.join("workloads/sec/open.rs"), "// open sec\n");
        write(&crate_dir.join("workloads/tpch/mod.rs"), "// tpch\n");
        let names = vec!["sec".to_string(), "tpch".to_string()];
        let entry = |name: &str, modules: Vec<ModuleDeclaration>| WorkloadModules { name: name.into(), storage_uses: vec![admitted("s", 1)], modules };
        let seed = EngineManifest::example(&[("s".into(), ContentId::from_bytes([1; 32]))]);
        let manifest = EngineManifest::stage_form(&seed, vec![entry("sec", vec![module("mod.rs", ModuleRole::Helper), module("open.rs", ModuleRole::Reader)]), entry("tpch", vec![module("mod.rs", ModuleRole::Helper)])]);
        let mut lists = vec![];
        for workload in ["sec", "tpch"] {
            let stage = StageCrate { workload, workloads: &names };
            let found = stage_workload(&manifest, &crate_dir, &agent, &stage).unwrap();
            assert_eq!(found.entry.name, workload);
            let to = root.join(format!("composed-{workload}"));
            compose_agent(&agent, found.module_dir.as_deref().unwrap(), &to).unwrap();
            assert_eq!(fs::read_to_string(to.join("workload/mod.rs")).unwrap(), format!("// {workload}\n"), "the bytes as written");
            lists.push(tree(&to));
        }
        assert_eq!(lists, [vec!["mod.rs", "plan/join.rs", "workload/mod.rs", "workload/open.rs"], vec!["mod.rs", "plan/join.rs", "workload/mod.rs"]]);
        let stage = StageCrate { workload: "sec", workloads: &names };
        let refusal = |manifest: &EngineManifest| match stage_workload(manifest, &crate_dir, &agent, &stage) {
            Ok(_) => panic!("accepted"),
            Err(e) => e.to_string(),
        };
        fs::rename(crate_dir.join("workloads/tpch"), root.join("tpch-aside")).unwrap();
        assert!(refusal(&manifest).contains("optional together"));
        write(&crate_dir.join("workloads/other/mod.rs"), "");
        assert!(refusal(&manifest).contains("one directory per workload"));
        fs::remove_dir_all(crate_dir.join("workloads/other")).unwrap();
        fs::rename(root.join("tpch-aside"), crate_dir.join("workloads/tpch")).unwrap();
        fs::remove_file(crate_dir.join("workloads/sec/mod.rs")).unwrap();
        assert!(refusal(&manifest).contains("workloads/sec/mod.rs is missing"));
        write(&crate_dir.join("workloads/sec/mod.rs"), "// sec\n");
        write(&agent.join("workload/mod.rs"), "");
        assert!(refusal(&manifest).contains("src/agent/workload is each workload's module"));
        fs::remove_dir_all(agent.join("workload")).unwrap();
        // Without workload modules nothing is composed, and no workload may declare one.
        fs::rename(crate_dir.join("workloads"), root.join("workloads-aside")).unwrap();
        assert!(refusal(&manifest).contains("declares modules but workloads/sec/ does not exist"));
        let bare = EngineManifest::stage_form(&seed, vec![entry("sec", vec![]), entry("tpch", vec![])]);
        assert!(stage_workload(&bare, &crate_dir, &agent, &stage).unwrap().module_dir.is_none());
        // A symlink in an author tree is refused by the composition, as by the freeze.
        std::os::unix::fs::symlink(agent.join("mod.rs"), agent.join("alias.rs")).unwrap();
        assert!(compose_agent(&agent, &root.join("workloads-aside/sec"), &root.join("composed-symlink")).unwrap_err().to_string().contains("no symlinks"));
        // A stage freeze needs the stage rule set.
        let rules = EngineRuleSet::for_line(EngineLine::General, Default::default(), &[]);
        let context = EngineFreeze { workspace: &root, schema: &[], library: &root, substitutes: &BTreeMap::new(), policy: &StoredDataPolicy::default(), rules: &rules };
        let submission = CandidateSubmission { candidate_manifest: MANIFEST_FILE.into(), rationale: String::new(), data_access_analysis: String::new() };
        assert!(freeze_stage_engine(&context, &stage, &root.join("frozen"), &submission).err().unwrap().to_string().contains("not a stage run's"));
        assert!(gendb_verification::verus::engine_rules::WORKLOAD_MODULE_ROOT == format!("agent/{WORKLOAD_MODULE}/"), "the rule's directory is the composed module's");
        fs::remove_dir_all(&root).unwrap();
    }

    /// A stage run's first workspace from a version folder: its code copied writable, the stage-form
    /// manifest with its modules and the workloads' uses; a folder that is not an accepted version, and a workspace that
    /// already has code, are refused.
    #[test]
    fn root_from_a_version_folder() {
        use std::os::unix::fs::PermissionsExt;
        let root = crate::controller::test_support::scratch_root("engine-stage-root");
        let version = root.join("run/engine/versions/v016");
        write(&version.join("code/agent/mod.rs"), "pub mod common;\n");
        write(&version.join("code/agent/common/sval.rs"), "// sval\n");
        fs::set_permissions(version.join("code/agent/mod.rs"), fs::Permissions::from_mode(0o444)).unwrap();
        write(&version.join("node.json"), &json!({"id":"v016","accepted":true}).to_string());
        let mut seed = EngineManifest::example(&[("narrowpack".into(), ContentId::from_bytes([1; 32]))]);
        seed.modules.push(module("common/sval.rs", ModuleRole::Helper));
        seed.notes = "the head".into();
        write(&version.join("manifest.json"), &json!(EngineManifest { direction: Some("d".into()), ..seed.clone() }).to_string());
        let workloads = vec![
            WorkloadModules { name: "sec".into(), storage_uses: vec![admitted("flat_sub", 2)], modules: vec![] },
            WorkloadModules { name: "tpch".into(), storage_uses: seed.storage_uses.clone(), modules: vec![] },
        ];
        let workspace = root.join("author");
        let files = write_root_from_version(&workspace, &version, workloads.clone()).unwrap();
        assert_eq!(files, ["agent/common/sval.rs", "agent/mod.rs"]);
        assert!(!fs::metadata(workspace.join("engine/src/agent/mod.rs")).unwrap().permissions().readonly(), "the workspace copy is writable");
        let written: EngineManifest = serde_json::from_slice(&fs::read(workspace.join(MANIFEST_FILE)).unwrap()).unwrap();
        assert_eq!(written, EngineManifest { storage_uses: vec![], workloads: workloads.clone(), ..seed.clone() });
        let names = vec!["sec".to_string(), "tpch".to_string()];
        written.check(CrateForm::Stage(&StageCrate { workload: "sec", workloads: &names })).unwrap();
        assert!(write_root_from_version(&workspace, &version, workloads.clone()).unwrap_err().to_string().contains("fresh workspace"));
        write(&version.join("node.json"), &json!({"id":"v016","accepted":false}).to_string());
        assert!(write_root_from_version(&root.join("other"), &version, workloads).unwrap_err().to_string().contains("not an accepted version"));
        fs::set_permissions(version.join("code/agent/mod.rs"), fs::Permissions::from_mode(0o644)).unwrap();
        fs::remove_dir_all(&root).unwrap();
    }

    /// A continued run's first workspace from a version folder: its code copied writable and its
    /// own manifest (its storage uses, modules, compiler and notes; no field of one submission), which passes the
    /// one-workload manifest check; a stage version, a folder that is not an accepted version, and a workspace that
    /// already has code are refused.
    #[test]
    fn root_of_a_continued_run_from_a_version_folder() {
        let root = crate::controller::test_support::scratch_root("engine-continued-root");
        let version = root.join("run/engine/versions/v016");
        write(&version.join("code/agent/mod.rs"), "pub mod common;\n");
        write(&version.join("code/agent/common/sval.rs"), "// sval\n");
        write(&version.join("node.json"), &json!({"id":"v016","accepted":true}).to_string());
        let mut seed = EngineManifest::example(&[("narrowpack".into(), ContentId::from_bytes([1; 32])), ("flat_nation".into(), ContentId::from_bytes([2; 32]))]);
        seed.modules.push(module("common/sval.rs", ModuleRole::Helper));
        seed.notes = "the head".into();
        write(&version.join("seed-manifest.json"), &json!(seed).to_string());
        write(&version.join("manifest.json"), &json!(EngineManifest { direction: Some("d".into()), findings: vec!["f".into()], ..seed.clone() }).to_string());
        let workspace = root.join("author");
        let files = write_root_from_seed_version(&workspace, &version).unwrap();
        assert_eq!(files, ["agent/common/sval.rs", "agent/mod.rs"]);
        let written: EngineManifest = serde_json::from_slice(&fs::read(workspace.join(MANIFEST_FILE)).unwrap()).unwrap();
        assert_eq!(written, seed, "the seed's own manifest: its uses, modules, compiler and notes");
        written.check(CrateForm::One).unwrap();
        assert!(write_root_from_seed_version(&workspace, &version).unwrap_err().to_string().contains("fresh workspace"));
        let stage_version = root.join("stage/engine/versions/v001");
        write(&stage_version.join("code/agent/mod.rs"), "pub mod common;\n");
        write(&stage_version.join("node.json"), &json!({"id":"v001","accepted":true}).to_string());
        let workloads = vec![WorkloadModules { name: "tpch".into(), storage_uses: seed.storage_uses.clone(), modules: vec![] }];
        write(&stage_version.join("manifest.json"), &json!(EngineManifest::stage_form(&seed, workloads)).to_string());
        assert!(write_root_from_seed_version(&root.join("other"), &stage_version).unwrap_err().to_string().contains("a stage version"));
        write(&version.join("node.json"), &json!({"id":"v016","accepted":false}).to_string());
        assert!(write_root_from_seed_version(&root.join("third"), &version).unwrap_err().to_string().contains("not an accepted version"));
        fs::remove_dir_all(&root).unwrap();
    }

}
