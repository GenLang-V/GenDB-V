//! The engine submission of a run of several workloads (`engine.workloads`):
//! what [`super::freeze_member_crate`] adds to a stage crate's freeze, the record it writes, and the root writers.
//!
//! **One workload's crate.** The shared engine `src/agent/**`, with as `agent/workload/**` the workload's own module
//! `<crate_dir>/workloads/<workload>/` when the workspace has one, else the shared default module
//! `<crate_dir>/workloads/default/` (`default_modules` of the manifest), else no module ([`member_workload`]). Every
//! family use `{"name": <family>, "family": <family>}` of the workload is composed by GenDB into that workload's
//! instance (`storage::family::compose_instance`: its whole schema, its plain flat storages as sources, its plan
//! `<crate_dir>/plans/<workload>/<family>.rs` or the family's default plan) and frozen as a workspace storage
//! ([`compose_families`]). The rules: R3 (no workspace storage; the manifest's check), R4 (plans are data; the
//! composition) and R5 ([`check_module_scope`]: an own module only beside an inherited storage that is neither a family
//! instance nor a plain flat storage).
//!
//! **What the freeze keeps** under the frozen directory, besides the crate and the frozen storages
//! (`storages/<family>/`): a copy of every declared family's source (`family-sources/<family>/`: `verus-family.json`,
//! `default_plan.rs`, the builder and interface), of the workload's own plans (`plans/<family>.rs`) and of the default
//! module (`default-module/`), byte for byte, from which a version's code is written ([`write_member_code`]). Its record
//! ([`MemberRecord`], `candidate.json` `workload.member`) names the module, the families composed, the storages by kind
//! and the digest of the shared sources ([`shared_sources_digest`]: equal for every workload's crate of one submission,
//! the recorded "one engine").
//!
//! **A version's code** (written by [`write_member_code`], read by [`write_side_root`]): `code/agent/**` (the shared
//! engine), `code/workloads/<workload>/**` (own modules), `code/workloads/default/**`, `code/families/<family>/**` (each
//! family's source) and `code/plans/<workload>/<family>.rs`; its seed manifest names every family's source relative to
//! `code/` ([`EngineManifest::with_version_family_sources`]).
//!
//! **Root writers** (each writes a fresh workspace for one workload's side of the root, whose manifest names only that
//! workload): [`write_side_root`] from an accepted version folder (a version of one workload, or one workload of a
//! version of several), [`write_source_root`] from an exported engine folder (`gendb engine export`: `agent/**`,
//! `workloads/default/**`, the families its `manifest.json` names, `plans/<workload>/**`). In the workspace the families
//! lie under `storages/<family>/` and the plans under `<crate_dir>/plans/<workload>/`.
//!
//! Trust: none in proofs. These are host steps that choose and copy author files and decide refusals and records; every
//! crate and every instance is verified whole by Verus.

use super::{CRATE_DIRECTORY, CrateWorkload, DEFAULT_WORKLOAD, EngineManifest, FamilyDeclaration, MANIFEST_FILE, MemberCrate, PLANS_DIRECTORY, WORKLOADS_DIRECTORY, WORKLOAD_MODULE, WorkloadModules, refuse_composed_module_directory};
use crate::controller::records::read_json;
use crate::query::candidate::{ComposedUse, ResolvedUse, StorageUseDeclaration, inside};
use crate::storage::catalog;
use crate::storage::family::{ComposedInstance, FAMILY_MANIFEST_FILE, FamilySource, InstanceInput, PlanChoice, compose_instance, copy_author_tree, tree_files};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::TableDef;
use gendb_verification::admission::AdmissionError;
use gendb_verification::obligations::{StorageName, StorageUse, generated_flat_table, whole_schema_declaration};
use gendb_verification::verus::engine_rules::{PLAN_IS_DATA_RULE, WORKLOAD_MODULE_SCOPE_RULE, scan_plan_source};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// The families' directory in a workspace (`storages/<family>/`, beside the manifest).
pub const WORKSPACE_FAMILIES_DIRECTORY: &str = "storages";
/// The families' directory in a version's code (`code/families/<family>/`).
pub const VERSION_FAMILIES_DIRECTORY: &str = "families";
/// A frozen crate's copies of every declared family's source (`<frozen>/family-sources/<family>/`).
pub const FROZEN_FAMILY_SOURCES: &str = "family-sources";
/// A frozen crate's copies of its workload's own plans (`<frozen>/plans/<family>.rs`).
pub const FROZEN_PLANS: &str = "plans";
/// A frozen crate's copy of the default module (`<frozen>/default-module/`).
pub const FROZEN_DEFAULT_MODULE: &str = "default-module";
/// The scratch of the compositions in a frozen directory (removed once the instances are frozen).
const COMPOSITION_SCRATCH: &str = "families";

/// Which workload module a crate of a run of several workloads composes as `agent/workload/`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MemberModule {
    /// The workload's own `workloads/<workload>/`.
    Own,
    /// The shared default module `workloads/default/`.
    Default,
    /// No module (the workspace has neither).
    None,
}

/// One family instance a crate composed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenFamily {
    pub name: String,
    /// Its `verus-family.json`, relative to the author workspace.
    pub source: PathBuf,
    /// The plan it was composed with, and that plan's lines.
    pub plan: PlanChoice,
    pub plan_lines: usize,
    /// The number of its parts over this workload's schema.
    pub parts: usize,
}

/// What a run of several workloads records of one workload's crate (`candidate.json` `workload.member`; the workloads
/// fixture's `general` fields are derived from it).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberRecord {
    pub module: MemberModule,
    /// The families this freeze composed (each a workspace storage of the crate).
    pub families: Vec<FrozenFamily>,
    /// The uses that are family instances (composed now, or admitted earlier): derived storages that store every column
    /// of every table.
    pub family_storages: Vec<String>,
    /// The uses that are plain flat storages (the generated flat storage of a table).
    pub plain_storages: Vec<String>,
    /// The other uses: inherited workload-specific storages (a seed's per-table packed storages, ...), to be replaced.
    pub inherited_storages: Vec<String>,
    /// Lines of the workload's own module (0 with the default module or none).
    pub own_module_lines: u64,
    /// Lines of the workload's own plans (0 when every family uses its default plan).
    pub plan_lines: u64,
    /// [`shared_sources_digest`] of the crate's shared sources.
    pub shared_sources_digest: String,
}

/// The workload `member.workload` of the manifest (module documentation, "One workload's crate"): its entry, and its own
/// module, else the default module, else none. Refused: `src/agent/workload`, anything under `<crate_dir>/workloads/`
/// but one directory per workload of the manifest and `default`, a module directory without `mod.rs`, module
/// declarations of a module the workspace does not have.
pub(super) fn member_workload<'m>(manifest: &'m EngineManifest, crate_dir: &Path, agent: &Path, member: &MemberCrate<'_>) -> Result<CrateWorkload<'m>, AdmissionError> {
    refuse_composed_module_directory(agent)?;
    let entry = manifest.workloads.iter().find(|w| w.name == member.workload).ok_or_else(|| AdmissionError::tool(format!("the manifest has no entry for workload {}", member.workload)))?;
    let root = crate_dir.join(WORKLOADS_DIRECTORY);
    if root.is_dir() {
        for item in fs::read_dir(&root).map_err(AdmissionError::tool)? {
            let item = item.map_err(AdmissionError::tool)?;
            let name = item.file_name().to_string_lossy().into_owned();
            let is_dir = item.file_type().map_err(AdmissionError::tool)?.is_dir();
            if !is_dir || !(name == DEFAULT_WORKLOAD || member.workloads.contains(&name)) {
                return Err(AdmissionError::refusal(format!(
                    "{WORKLOADS_DIRECTORY}/{name}: {WORKLOADS_DIRECTORY}/ holds the shared default module {DEFAULT_WORKLOAD}/ and one directory per workload with a module of its own {:?}, nothing else",
                    member.workloads
                )));
            }
        }
    }
    let (own, default) = (root.join(member.workload), root.join(DEFAULT_WORKLOAD));
    if !default.is_dir() && !manifest.default_modules.is_empty() {
        return Err(AdmissionError::refusal(format!("verus-engine manifest: default_modules are declared but {WORKLOADS_DIRECTORY}/{DEFAULT_WORKLOAD}/ does not exist")));
    }
    if !own.is_dir() && !entry.modules.is_empty() {
        return Err(AdmissionError::refusal(format!("verus-engine manifest: workload {} declares modules but {WORKLOADS_DIRECTORY}/{}/ does not exist", entry.name, entry.name)));
    }
    let (module, dir, files) = if own.is_dir() {
        (MemberModule::Own, Some(own), entry.modules.as_slice())
    } else if default.is_dir() {
        (MemberModule::Default, Some(default), manifest.default_modules.as_slice())
    } else {
        (MemberModule::None, None, &[][..])
    };
    if let Some(dir) = &dir
        && !dir.join("mod.rs").is_file()
    {
        return Err(AdmissionError::refusal(format!("{}/mod.rs is missing: a workload module's root is its mod.rs (crate::agent::{WORKLOAD_MODULE})", dir.display())));
    }
    Ok(CrateWorkload { entry, module_dir: dir, module_files: files, module: Some(module) })
}

/// Where a crate's shared sources lie: the manifest, its directory, the author workspace and the engine crate directory.
pub(super) struct SharedSources<'a> {
    pub(super) manifest: &'a EngineManifest,
    pub(super) manifest_dir: &'a Path,
    pub(super) workspace: &'a Path,
    pub(super) crate_dir: &'a Path,
}

/// The family instances one freeze composed: per use name, its composed workspace (for `query::candidate::resolve_uses`)
/// and its record.
#[derive(Default)]
pub(super) struct ComposedFamilies {
    pub(super) uses: BTreeMap<String, ComposedUse>,
    records: Vec<FrozenFamily>,
    scratch: Option<PathBuf>,
}

impl ComposedFamilies {
    /// Remove the compositions' scratch once the instances are frozen (their frozen storages hold everything).
    pub(super) fn remove_scratch(&self) -> Result<(), AdmissionError> {
        match &self.scratch {
            Some(dir) if dir.exists() => fs::remove_dir_all(dir).map_err(|e| AdmissionError::tool(format!("{}: {e}", dir.display()))),
            _ => Ok(()),
        }
    }
}

/// Every family use of workload `member.workload` composed into the frozen directory, and copies of the shared sources
/// kept there (module documentation): the plans directory checked ([`check_plans_directory`]), every declared family's
/// source read and copied, each family use composed with the workload's plan or the default one, the workload's own
/// plans and the default module copied.
pub(super) fn compose_families(sources: &SharedSources<'_>, member: &MemberCrate<'_>, schema: &[TableDef], frozen_dir: &Path) -> Result<ComposedFamilies, AdmissionError> {
    let manifest = sources.manifest;
    check_plans_directory(sources.crate_dir, member.workloads, &manifest.families)?;
    let mut read = BTreeMap::new();
    for family in &manifest.families {
        let path = inside(sources.manifest_dir, &family.source)?;
        if !path.starts_with(sources.workspace) {
            return Err(AdmissionError::missing_input(format!("family {}: its source {} escapes the author workspace", family.name, family.source.display())));
        }
        let source = FamilySource::read(&path)?;
        if source.manifest.name != family.name {
            return Err(AdmissionError::refusal(format!("verus-engine manifest: family {} names {}, whose name is {}", family.name, family.source.display(), source.manifest.name)));
        }
        copy_listed_files(source.directory(), &source.files()?, &frozen_dir.join(FROZEN_FAMILY_SOURCES).join(&family.name))?;
        let relative = path.strip_prefix(sources.workspace).map_err(AdmissionError::tool)?.to_path_buf();
        read.insert(family.name.clone(), (source, relative));
    }
    let entry = manifest.workloads.iter().find(|w| w.name == member.workload).ok_or_else(|| AdmissionError::tool(format!("the manifest has no entry for workload {}", member.workload)))?;
    let mut composed = ComposedFamilies::default();
    let scratch = frozen_dir.join(COMPOSITION_SCRATCH);
    for family in entry.storage_uses.iter().filter_map(|u| u.family.as_deref()) {
        let (source, relative) = read.get(family).ok_or_else(|| AdmissionError::tool(format!("family {family} was not read")))?;
        let plan_file = plan_path(sources.crate_dir, member.workload, family);
        let plan = plan_file.is_file().then_some(plan_file.as_path());
        fs::create_dir_all(&scratch).map_err(AdmissionError::tool)?;
        let input = InstanceInput { family: source, schema, flat_storages: member.flat_storages, plan };
        let instance: ComposedInstance = compose_instance(&input, &scratch.join(family))?;
        if let Some(plan) = plan {
            let copy = frozen_dir.join(FROZEN_PLANS).join(format!("{family}.rs"));
            fs::create_dir_all(copy.parent().unwrap_or(frozen_dir)).map_err(AdmissionError::tool)?;
            fs::copy(plan, &copy).map_err(|e| AdmissionError::tool(format!("{}: {e}", plan.display())))?;
        }
        composed.records.push(FrozenFamily { name: family.to_string(), source: relative.clone(), plan: instance.plan, plan_lines: instance.plan_lines, parts: instance.manifest.parts.len() });
        composed.uses.insert(family.to_string(), ComposedUse { workspace: instance.workspace, family_manifest: relative.clone() });
    }
    if composed.records.is_empty() {
        composed.scratch = None;
    } else {
        composed.scratch = Some(scratch);
    }
    let default = sources.crate_dir.join(WORKLOADS_DIRECTORY).join(DEFAULT_WORKLOAD);
    if default.is_dir() {
        copy_author_tree(&default, &frozen_dir.join(FROZEN_DEFAULT_MODULE))?;
    }
    Ok(composed)
}

/// `<crate_dir>/plans/<workload>/<family>.rs`.
fn plan_path(crate_dir: &Path, workload: &str, family: &str) -> PathBuf {
    crate_dir.join(PLANS_DIRECTORY).join(workload).join(format!("{family}.rs"))
}

/// `<crate_dir>/plans/` holds only `<workload>/<family>.rs` files of the manifest's workloads and families (a plan
/// elsewhere would be silently unused), and every one of them is data (R4, `plan_is_data`), whether or not this
/// workload composes it.
fn check_plans_directory(crate_dir: &Path, workloads: &[String], families: &[FamilyDeclaration]) -> Result<(), AdmissionError> {
    let root = crate_dir.join(PLANS_DIRECTORY);
    for file in tree_files(&root)? {
        let parts: Vec<String> = file.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect();
        let known = match parts.as_slice() {
            [workload, name] => workloads.contains(workload) && families.iter().any(|f| format!("{}.rs", f.name) == *name),
            _ => false,
        };
        if !known {
            return Err(AdmissionError::refusal(format!(
                "{PLANS_DIRECTORY}/{}: {PLANS_DIRECTORY}/ holds only <workload>/<family>.rs, for the workloads {workloads:?} and the families of families[]",
                file.display()
            )));
        }
        let shown = format!("{PLANS_DIRECTORY}/{}", file.display());
        let text = fs::read_to_string(root.join(&file)).map_err(|e| AdmissionError::tool(format!("{shown}: {e}")))?;
        let findings = scan_plan_source(&shown, &text);
        if !findings.is_empty() {
            let listed: Vec<String> = findings.iter().map(|f| format!("{}:{}: {}", f.file, f.line, f.detail)).collect();
            return Err(AdmissionError::refusal(format!("{}: {} ({})", PLAN_IS_DATA_RULE.id, listed.join("; "), PLAN_IS_DATA_RULE.refuses)));
        }
    }
    Ok(())
}

/// The storages of a workload's crate by kind ([`check_module_scope`]).
#[derive(Debug)]
pub(super) struct MemberStorages {
    family: Vec<String>,
    plain: Vec<String>,
    inherited: Vec<String>,
}

/// R5 (`workload_module_scope`) over the resolved uses of a workload's crate: each use is a plain flat storage (the
/// generated flat storage of a table), a family instance (a derived storage that stores every column of every table)
/// or an inherited storage (anything else); an own module with no inherited storage is refused.
pub(super) fn check_module_scope(workload: &CrateWorkload<'_>, uses: &[ResolvedUse], schema: &[TableDef]) -> Result<MemberStorages, AdmissionError> {
    let mut storages = MemberStorages { family: vec![], plain: vec![], inherited: vec![] };
    for u in uses {
        let as_use = StorageUse { name: &u.name, declaration: &u.frozen.declaration, interface: &u.interface };
        let kind = if generated_flat_table(schema, &as_use).is_some() {
            &mut storages.plain
        } else if whole_schema_declaration(schema, &u.frozen.declaration) && !u.sources.is_empty() {
            &mut storages.family
        } else {
            &mut storages.inherited
        };
        kind.push(u.frozen.name.clone());
    }
    if workload.module == Some(MemberModule::Own) && storages.inherited.is_empty() {
        let rule = WORKLOAD_MODULE_SCOPE_RULE;
        return Err(AdmissionError::refusal(format!(
            "{}: workload {} has a module of its own ({WORKLOADS_DIRECTORY}/{}/) but reads only family instances and plain flat storages; move its code into the shared engine or the default module {WORKLOADS_DIRECTORY}/{DEFAULT_WORKLOAD}/ ({})",
            rule.id, workload.entry.name, workload.entry.name, rule.refuses
        )));
    }
    Ok(storages)
}

/// The record of a workload's crate ([`MemberRecord`]) once frozen in `frozen_dir`.
pub(super) fn member_record(workload: &CrateWorkload<'_>, families: &ComposedFamilies, storages: MemberStorages, module_report: &serde_json::Value, frozen_dir: &Path) -> Result<MemberRecord, AdmissionError> {
    let module = workload.module.unwrap_or(MemberModule::None);
    let own_module_lines = if module == MemberModule::Own { module_report["lines"].as_u64().unwrap_or(0) } else { 0 };
    let plan_lines = families.records.iter().filter(|f| f.plan == PlanChoice::Workload).map(|f| f.plan_lines as u64).sum();
    Ok(MemberRecord {
        module,
        families: families.records.clone(),
        family_storages: storages.family,
        plain_storages: storages.plain,
        inherited_storages: storages.inherited,
        own_module_lines,
        plan_lines,
        shared_sources_digest: shared_sources_digest(frozen_dir)?,
    })
}

/// SHA-256 of the shared sources a crate of a run of several workloads was frozen from: every file of its shared engine
/// (`crate/src/agent/**` without the composed `workload/`), of the default module and of every declared family's source
/// (as kept in the frozen directory), each as its path (`agent/..`, `workloads/default/..`, `families/<family>/..`) and
/// bytes. Equal digests: the same shared engine, default module and family sources.
pub fn shared_sources_digest(frozen_dir: &Path) -> Result<String, AdmissionError> {
    let mut hasher = Sha256::new();
    let roots = [
        (frozen_dir.join("crate/src/agent"), "agent"),
        (frozen_dir.join(FROZEN_DEFAULT_MODULE), "workloads/default"),
        (frozen_dir.join(FROZEN_FAMILY_SOURCES), VERSION_FAMILIES_DIRECTORY),
    ];
    for (dir, prefix) in &roots {
        for file in tree_files(dir)? {
            if *prefix == "agent" && file.starts_with(WORKLOAD_MODULE) {
                continue;
            }
            hasher.update(format!("{prefix}/{}", file.display()).as_bytes());
            hasher.update([0]);
            hasher.update(fs::read(dir.join(&file)).map_err(AdmissionError::tool)?);
            hasher.update([0]);
        }
    }
    Ok(hasher.finalize().iter().map(|b| format!("{b:02x}")).collect())
}

/// Copy `files` (relative to `from`) into `to`, creating directories.
fn copy_listed_files(from: &Path, files: &[PathBuf], to: &Path) -> Result<(), AdmissionError> {
    for file in files {
        let target = to.join(file);
        fs::create_dir_all(target.parent().unwrap_or(to)).map_err(AdmissionError::tool)?;
        fs::copy(from.join(file), &target).map_err(|e| AdmissionError::tool(format!("{}: {e}", from.join(file).display())))?;
    }
    Ok(())
}

/// The plain flat storages of a workload, `(name, package)` in table order, among `seeded` (its seeded storages,
/// admitted in `library`): the generated flat storage of each table of `schema`. Refused (missing input): a table
/// without one, or with two.
pub fn plain_flat_storages(library: &Path, schema: &[TableDef], seeded: &[(String, ContentId)]) -> Result<Vec<(String, ContentId)>, AdmissionError> {
    let store = ObjectStore::open_existing(library).map_err(|e| AdmissionError::tool(format!("{}: {e}", library.display())))?;
    let mut by_table: BTreeMap<usize, (String, ContentId)> = BTreeMap::new();
    for (name, package) in seeded {
        let (record, declaration) = catalog::admitted_storage(&store, *package)?;
        let interface = catalog::interface_files(&store, &record)?;
        let storage_name = StorageName::new(name).map_err(AdmissionError::refusal)?;
        let as_use = StorageUse { name: &storage_name, declaration: &declaration, interface: &interface };
        if let Some(table) = generated_flat_table(schema, &as_use)
            && let Some((other, _)) = by_table.insert(table, (name.clone(), *package))
        {
            return Err(AdmissionError::missing_input(format!("table {} has two plain flat storages, {other} and {name}", schema[table].name)));
        }
    }
    if let Some(missing) = schema.iter().enumerate().find(|(t, _)| !by_table.contains_key(t)) {
        return Err(AdmissionError::missing_input(format!("table {} has no plain flat storage among the seeded storages of {}", missing.1.name, library.display())));
    }
    Ok(by_table.into_values().collect())
}

impl EngineManifest {
    /// This manifest with every family's source named as a version's code holds it, relative to `code/`
    /// (`families/<family>/verus-family.json`): the families of a version's seed manifest.
    pub fn with_version_family_sources(&self) -> Self {
        let families = self.families.iter().map(|f| FamilyDeclaration { name: f.name.clone(), source: family_manifest_in(VERSION_FAMILIES_DIRECTORY, &f.name) }).collect();
        Self { families, ..self.clone() }
    }
}

/// `<directory>/<family>/verus-family.json`.
fn family_manifest_in(directory: &str, family: &str) -> PathBuf {
    Path::new(directory).join(family).join(FAMILY_MANIFEST_FILE)
}

/// What a side's root workspace is written from ([`write_side_root`], [`write_source_root`]).
struct SideParts<'a> {
    member: &'a str,
    /// The shared engine's `agent` directory.
    agent: PathBuf,
    /// The workload's own module, when it has one.
    module: Option<PathBuf>,
    /// The default module, when the source has one.
    default_module: PathBuf,
    /// The workload's plans directory, when the source has one.
    plans: PathBuf,
    /// The source's manifest (its modules, compiler, notes, families and default module declarations) and the
    /// directory its families' sources are relative to.
    manifest: &'a EngineManifest,
    families_root: &'a Path,
    /// The workload's entry of the written manifest.
    entry: WorkloadModules,
}

/// Write `parts` into the fresh workspace `workspace`: the shared engine into `engine/src/agent/`, the own module into
/// `engine/workloads/<workload>/`, the default module into `engine/workloads/default/`, every family into
/// `storages/<family>/`, the plans into `engine/plans/<workload>/`, and the manifest `verus-engine.json` of one workload
/// (the source's modules, compiler and notes, its families at their workspace paths, its default module declarations,
/// the entry). Every copy is writable. Returns every file written, relative to the workspace, sorted.
fn write_side_workspace(workspace: &Path, parts: SideParts<'_>) -> Result<Vec<String>, AdmissionError> {
    let crate_dir = workspace.join(CRATE_DIRECTORY);
    let agent = crate_dir.join("src/agent");
    if fs::symlink_metadata(&agent).is_ok() {
        return Err(AdmissionError::tool(format!("{} exists: the root is written into a fresh workspace", agent.display())));
    }
    if !parts.agent.join("mod.rs").is_file() {
        return Err(AdmissionError::missing_input(format!("{}: no mod.rs (the shared engine)", parts.agent.display())));
    }
    copy_author_tree(&parts.agent, &agent)?;
    if let Some(module) = &parts.module {
        copy_author_tree(module, &crate_dir.join(WORKLOADS_DIRECTORY).join(parts.member))?;
    }
    if parts.default_module.is_dir() {
        copy_author_tree(&parts.default_module, &crate_dir.join(WORKLOADS_DIRECTORY).join(DEFAULT_WORKLOAD))?;
    }
    let mut families = vec![];
    for family in &parts.manifest.families {
        let source = parts.families_root.join(&family.source);
        let dir = source.parent().ok_or_else(|| AdmissionError::missing_input(format!("family {}: {} has no directory", family.name, source.display())))?;
        if !source.is_file() {
            return Err(AdmissionError::missing_input(format!("family {}: {} is missing", family.name, source.display())));
        }
        copy_author_tree(dir, &workspace.join(WORKSPACE_FAMILIES_DIRECTORY).join(&family.name))?;
        families.push(FamilyDeclaration { name: family.name.clone(), source: family_manifest_in(WORKSPACE_FAMILIES_DIRECTORY, &family.name) });
    }
    if parts.plans.is_dir() {
        copy_author_tree(&parts.plans, &crate_dir.join(PLANS_DIRECTORY).join(parts.member))?;
    }
    let manifest = EngineManifest { crate_dir: CRATE_DIRECTORY.into(), storage_uses: vec![], workloads: vec![parts.entry], families, ..parts.manifest.for_seed() };
    fs::write(workspace.join(MANIFEST_FILE), format!("{}\n", serde_json::to_string_pretty(&manifest).map_err(AdmissionError::tool)?)).map_err(AdmissionError::tool)?;
    let mut written: Vec<String> = tree_files(workspace)?.into_iter().map(|f| f.display().to_string()).collect();
    written.sort();
    Ok(written)
}

/// The root workspace of workload `member`'s side from the accepted version folder `version_dir` (a
/// seed `{run, version, workload?}`): the version's shared engine (`code/agent/**`), and
/// - of a version of one workload (`seed_workload` none): its storage uses, no module;
/// - of a version of several workloads, the workload `seed_workload`'s (required there): its storage uses, its own module
///   (`code/workloads/<seed_workload>/**`, as the member's own module) with its declarations, and its plans;
///
/// plus the version's default module and families when it has them (a run of several workloads' version). The manifest
/// names only `member`'s entry, so the side is frozen with `MemberCrate { workloads: [member], .. }`. Refused (missing
/// input): a folder that is not an accepted version (`seed_version_parts`), a seed workload the version does not have or
/// that a version of one workload is given; a workspace that already has code (tool).
pub fn write_side_root(workspace: &Path, version_dir: &Path, seed_workload: Option<&str>, member: &str) -> Result<Vec<String>, AdmissionError> {
    let (agent, seed) = super::seed_version_parts(version_dir)?;
    let code = version_dir.join("code");
    let missing = |what: String| AdmissionError::missing_input(format!("seed version {}: {what}", version_dir.display()));
    let (entry, module, plans) = match (seed.workloads.is_empty(), seed_workload) {
        (true, None) => (WorkloadModules { name: member.into(), storage_uses: seed.storage_uses.clone(), modules: vec![] }, None, PathBuf::new()),
        (true, Some(w)) => return Err(missing(format!("a version of one workload has no workload {w} (seed.workload is for versions of several workloads)"))),
        (false, None) => return Err(missing(format!("a version of several workloads ({:?}): the seed names the workload whose side it is (seed.workload)", seed.workloads.iter().map(|w| &w.name).collect::<Vec<_>>()))),
        (false, Some(w)) => {
            let found = seed.workloads.iter().find(|e| e.name == w).ok_or_else(|| missing(format!("no workload {w}")))?;
            let module = code.join(WORKLOADS_DIRECTORY).join(w);
            let module = module.is_dir().then_some(module);
            let modules = if module.is_some() { found.modules.clone() } else { vec![] };
            (WorkloadModules { name: member.into(), storage_uses: found.storage_uses.clone(), modules }, module, code.join(PLANS_DIRECTORY).join(w))
        }
    };
    let parts = SideParts {
        member,
        agent,
        module,
        default_module: code.join(WORKLOADS_DIRECTORY).join(DEFAULT_WORKLOAD),
        plans,
        manifest: &seed,
        families_root: &code,
        entry,
    };
    write_side_workspace(workspace, parts)
}

/// The manifest of an exported engine folder (`gendb engine export`), beside its `agent/`.
pub const EXPORT_MANIFEST_FILE: &str = "manifest.json";

/// The root workspace of workload `member`'s side from the exported engine folder `source` (a seed `{source}`):
/// the folder's shared engine (`agent/**`), default module (`workloads/default/**`), the families its
/// `manifest.json` names (sources relative to the folder) and `member`'s plans (`plans/<member>/**`) when it has them.
/// The workload's storage uses are one family use per family when the engine has families, else `plain_uses` (its plain
/// flat storages, admitted in its library); an exported workload's own module is not carried (it opens storages of the
/// exporting run). Refused (missing input): a folder without `agent/mod.rs` or its manifest; a workspace that already
/// has code (tool).
pub fn write_source_root(workspace: &Path, source: &Path, member: &str, plain_uses: &[(String, ContentId)]) -> Result<Vec<String>, AdmissionError> {
    let manifest_file = source.join(EXPORT_MANIFEST_FILE);
    let manifest: EngineManifest = read_json(&manifest_file).map_err(|e| AdmissionError::missing_input(format!("exported engine {}: {e}", source.display())))?;
    let storage_uses = if manifest.families.is_empty() {
        plain_uses.iter().map(|(name, package)| StorageUseDeclaration::admitted(name, *package)).collect()
    } else {
        manifest.families.iter().map(|f| StorageUseDeclaration { name: f.name.clone(), admitted: None, workspace: None, family: Some(f.name.clone()) }).collect()
    };
    let parts = SideParts {
        member,
        agent: source.join("agent"),
        module: None,
        default_module: source.join(WORKLOADS_DIRECTORY).join(DEFAULT_WORKLOAD),
        plans: source.join(PLANS_DIRECTORY).join(member),
        manifest: &manifest,
        families_root: source,
        entry: WorkloadModules { name: member.into(), storage_uses, modules: vec![] },
    };
    write_side_workspace(workspace, parts)
}

/// The code of a version of a run of several workloads (module documentation, "A version's code") into `code` from its
/// crates `(workload, frozen directory)`, the primary's first: the shared engine from the first crate (without its
/// composed `workload/`), each own module from its crate, the default module and every family's source from the first
/// crate that kept them, each workload's own plans from its crate. Frozen storages and reading views are the caller's.
pub fn write_member_code(code: &Path, crates: &[(&str, &Path)]) -> Result<(), AdmissionError> {
    let Some((_, first)) = crates.first() else { return Err(AdmissionError::tool("a version without its crates")) };
    copy_author_tree(&first.join("crate/src/agent"), &code.join("agent"))?;
    let composed = code.join("agent").join(WORKLOAD_MODULE);
    if composed.exists() {
        fs::remove_dir_all(&composed).map_err(|e| AdmissionError::tool(format!("{}: {e}", composed.display())))?;
    }
    for (workload, frozen) in crates {
        let engine: super::FrozenEngine = read_json(&frozen.join("candidate.json")).map_err(AdmissionError::tool)?;
        let module = engine.workload.as_ref().and_then(|w| w.member.as_ref()).map(|m| m.module);
        if module == Some(MemberModule::Own) {
            copy_author_tree(&frozen.join("crate/src/agent").join(WORKLOAD_MODULE), &code.join(WORKLOADS_DIRECTORY).join(workload))?;
        }
        let default = code.join(WORKLOADS_DIRECTORY).join(DEFAULT_WORKLOAD);
        if !default.exists() && frozen.join(FROZEN_DEFAULT_MODULE).is_dir() {
            copy_author_tree(&frozen.join(FROZEN_DEFAULT_MODULE), &default)?;
        }
        for family in tree_children(&frozen.join(FROZEN_FAMILY_SOURCES))? {
            let target = code.join(VERSION_FAMILIES_DIRECTORY).join(&family);
            if !target.exists() {
                copy_author_tree(&frozen.join(FROZEN_FAMILY_SOURCES).join(&family), &target)?;
            }
        }
        if frozen.join(FROZEN_PLANS).is_dir() {
            copy_author_tree(&frozen.join(FROZEN_PLANS), &code.join(PLANS_DIRECTORY).join(workload))?;
        }
    }
    Ok(())
}

/// The names of the directories directly under `dir`, sorted (none when it does not exist).
fn tree_children(dir: &Path) -> Result<Vec<String>, AdmissionError> {
    let mut names = vec![];
    for entry in fs::read_dir(dir).into_iter().flatten() {
        let entry = entry.map_err(AdmissionError::tool)?;
        if entry.file_type().map_err(AdmissionError::tool)?.is_dir() {
            names.push(entry.file_name().to_string_lossy().into_owned());
        }
    }
    names.sort();
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::super::{CrateForm, ModuleDeclaration, ModuleRole, StageCrate};
    use super::*;
    use crate::query::candidate::{FrozenUse, StorageSource};
    use crate::storage::family::tests::{schema, write, write_family};
    use gendb_verification::obligations::{DeclaredSource, flat_storage};
    use serde_json::json;

    fn module(file: &str, role: ModuleRole) -> ModuleDeclaration {
        ModuleDeclaration { file: file.into(), role, items: if role == ModuleRole::Entry { vec!["engine".into()] } else { vec![] } }
    }

    fn admitted(name: &str, byte: u8) -> StorageUseDeclaration {
        StorageUseDeclaration::admitted(name, ContentId::from_bytes([byte; 32]))
    }

    fn family_use(name: &str) -> StorageUseDeclaration {
        StorageUseDeclaration { name: name.into(), admitted: None, workspace: None, family: Some(name.into()) }
    }

    /// A manifest of a run of several workloads: `tpch` on narrowpack (inherited), `sec` and `anyschema` on the
    /// family `plainfam`.
    fn members_manifest() -> EngineManifest {
        let entry = |name: &str, uses: Vec<StorageUseDeclaration>| WorkloadModules { name: name.into(), storage_uses: uses, modules: vec![] };
        let seed = EngineManifest::example(&[("flat_t".into(), ContentId::from_bytes([1; 32]))]);
        EngineManifest {
            families: vec![FamilyDeclaration { name: "plainfam".into(), source: "storages/plainfam/verus-family.json".into() }],
            default_modules: vec![module("mod.rs", ModuleRole::Reader)],
            ..EngineManifest::stage_form(&seed, vec![entry("tpch", vec![admitted("narrowpack", 2)]), entry("sec", vec![family_use("plainfam")]), entry("anyschema", vec![family_use("plainfam")])])
        }
    }

    fn names() -> Vec<String> {
        ["tpch", "sec", "anyschema"].map(String::from).to_vec()
    }

    /// The manifest of a run of several workloads: family uses name a declared family after its
    /// own name; R3 refuses a workspace storage; families are unique; its fields are refused in every other form; the
    /// schema names them.
    #[test]
    fn member_manifests_follow_their_rules() {
        let names = names();
        let crate_of = MemberCrate { workload: "sec", workloads: &names, flat_storages: &[] };
        let manifest = members_manifest();
        manifest.check(CrateForm::Members(&crate_of)).unwrap();
        assert_eq!(serde_json::from_value::<EngineManifest>(json!(manifest)).unwrap(), manifest);
        let refused = |edit: &dyn Fn(&mut EngineManifest), words: &str| {
            let mut m = members_manifest();
            edit(&mut m);
            let error = m.check(CrateForm::Members(&crate_of)).unwrap_err().to_string();
            assert!(error.contains(words), "{words}: {error}");
        };
        refused(&|m| m.workloads[1].storage_uses = vec![StorageUseDeclaration { name: "own".into(), admitted: None, workspace: Some("s.json".into()), family: None }], "storage_family_required");
        refused(&|m| m.workloads[1].storage_uses[0].family = Some("other".into()), "must be one of families[]");
        refused(&|m| m.workloads[1].storage_uses[0].name = "renamed".into(), "named after it");
        refused(&|m| m.workloads[1].storage_uses[0].admitted = Some(ContentId::from_bytes([3; 32])), "exactly one of admitted or family");
        refused(&|m| m.families.push(m.families[0].clone()), "declared twice");
        refused(&|m| m.default_modules.push(m.default_modules[0].clone()), "the default module: module mod.rs declared twice");
        refused(&|m| { m.workloads.pop(); }, "exactly one entry per workload");
        // Every other form refuses the fields of a run of several workloads.
        let stage = StageCrate { workload: "sec", workloads: &names };
        assert!(manifest.check(CrateForm::Stage(&stage)).unwrap_err().to_string().contains("fields of a run of several workloads"));
        let one = EngineManifest { families: vec![FamilyDeclaration { name: "plainfam".into(), source: "f.json".into() }], ..EngineManifest::example(&[("flat_t".into(), ContentId::from_bytes([1; 32]))]) };
        assert!(one.check(CrateForm::One).unwrap_err().to_string().contains("fields of a run of several workloads"));
        assert!(json!(EngineManifest::example(&[])).get("families").is_none() && json!(EngineManifest::example(&[])).get("default_modules").is_none(), "absent, a manifest keeps its JSON identity");
        let schema = EngineManifest::members_schema();
        assert!(schema["properties"]["families"]["items"]["properties"]["source"].is_object() && schema["properties"]["default_modules"].is_object());
        assert!(schema["properties"]["workloads"]["items"]["properties"]["storage_uses"]["items"]["properties"]["family"].is_object());
    }

    /// The module a workload's crate composes: its own, else the default module, else none; anything
    /// else under `workloads/`, a module without `mod.rs` and declarations without their module are refused.
    #[test]
    fn workloads_compose_their_own_module_or_the_default() {
        let root = crate::controller::test_support::scratch_root("members-module");
        let crate_dir = root.join("engine");
        let agent = crate_dir.join("src/agent");
        write(&agent.join("mod.rs"), "pub mod workload;\n");
        write(&crate_dir.join("workloads/default/mod.rs"), "// default\n");
        write(&crate_dir.join("workloads/tpch/mod.rs"), "// tpch\n");
        let names = names();
        let mut manifest = members_manifest();
        manifest.workloads[0].modules = vec![module("mod.rs", ModuleRole::Reader)];
        let chosen = |manifest: &EngineManifest, workload: &str| -> Result<(MemberModule, Option<PathBuf>, usize), String> {
            let crate_of = MemberCrate { workload, workloads: &names, flat_storages: &[] };
            member_workload(manifest, &crate_dir, &agent, &crate_of).map(|w| (w.module.unwrap(), w.module_dir, w.module_files.len())).map_err(|e| e.to_string())
        };
        assert_eq!(chosen(&manifest, "tpch").unwrap(), (MemberModule::Own, Some(crate_dir.join("workloads/tpch")), 1));
        assert_eq!(chosen(&manifest, "sec").unwrap(), (MemberModule::Default, Some(crate_dir.join("workloads/default")), 1));
        write(&crate_dir.join("workloads/other/mod.rs"), "");
        assert!(chosen(&manifest, "sec").unwrap_err().contains("nothing else"));
        fs::remove_dir_all(crate_dir.join("workloads/other")).unwrap();
        fs::remove_file(crate_dir.join("workloads/default/mod.rs")).unwrap();
        assert!(chosen(&manifest, "sec").unwrap_err().contains("mod.rs is missing"));
        fs::remove_dir_all(crate_dir.join("workloads/default")).unwrap();
        assert!(chosen(&manifest, "sec").unwrap_err().contains("default_modules are declared"));
        let without_default = EngineManifest { default_modules: vec![], ..manifest.clone() };
        assert_eq!(chosen(&without_default, "sec").unwrap(), (MemberModule::None, None, 0));
        let mut declared = without_default.clone();
        declared.workloads[1].modules = vec![module("mod.rs", ModuleRole::Reader)];
        assert!(chosen(&declared, "sec").unwrap_err().contains("declares modules but workloads/sec/ does not exist"));
        write(&agent.join("workload/mod.rs"), "");
        assert!(chosen(&without_default, "tpch").unwrap_err().contains("src/agent/workload is each workload's module"));
        fs::remove_dir_all(&root).unwrap();
    }

    /// A resolved use with `declaration`, `interface` and derivation `sources`.
    fn resolved(name: &str, declaration: DeclaredSource, interface: Vec<gendb_verification::verus::FrameworkSource>, sources: Vec<(String, ContentId)>) -> ResolvedUse {
        ResolvedUse {
            frozen: FrozenUse { name: name.into(), source: StorageSource::Admitted { package: ContentId::from_bytes([9; 32]) }, declaration },
            name: StorageName::new(name).unwrap(),
            interface,
            storage_files: vec![],
            modules: vec![],
            package: None,
            sources,
        }
    }

    /// R5 (`workload_module_scope`): uses are classified as plain flat storages, family instances
    /// (derived, every column of every table) and inherited storages; an own module needs an inherited storage.
    #[test]
    fn an_own_module_needs_an_inherited_storage() {
        let tables = schema();
        let flats: Vec<_> = (0..tables.len()).map(|t| flat_storage(&tables, t).unwrap()).collect();
        let interface = |f: &gendb_verification::obligations::FlatStorage| f.files.iter().filter(|x| x.path.starts_with(&f.name.interface_prefix())).cloned().collect::<Vec<_>>();
        let every = std::collections::BTreeMap::from([(0, (0..tables[0].columns.len()).collect()), (1, (0..tables[1].columns.len()).collect())]);
        let whole = DeclaredSource::for_storage(&tables, &every).unwrap();
        let flat_sources: Vec<(String, ContentId)> = flats.iter().map(|f| (f.name.to_string(), ContentId::from_bytes([1; 32]))).collect();
        let plain = resolved(flats[0].name.as_str(), flats[0].declaration.clone(), interface(&flats[0]), vec![]);
        let family = resolved("plainfam", whole, vec![], flat_sources.clone());
        let packed = resolved("narrowpack1", flats[1].declaration.clone(), vec![], flat_sources[1..].to_vec());
        let entry = WorkloadModules { name: "sec".into(), storage_uses: vec![], modules: vec![] };
        let workload = |module: MemberModule| CrateWorkload { entry: &entry, module_dir: None, module_files: &[], module: Some(module) };
        let storages = check_module_scope(&workload(MemberModule::Default), &[plain, family, packed], &tables).unwrap();
        assert_eq!((storages.plain.clone(), storages.family.clone(), storages.inherited.clone()), (vec![flats[0].name.to_string()], vec!["plainfam".into()], vec!["narrowpack1".into()]));
        let packed = resolved("narrowpack1", flats[1].declaration.clone(), vec![], flat_sources[1..].to_vec());
        assert!(check_module_scope(&workload(MemberModule::Own), &[packed], &tables).is_ok(), "an own module beside an inherited storage");
        let family = resolved("plainfam", DeclaredSource::for_storage(&tables, &every).unwrap(), vec![], flat_sources);
        let plain = resolved(flats[0].name.as_str(), flats[0].declaration.clone(), interface(&flats[0]), vec![]);
        let error = check_module_scope(&workload(MemberModule::Own), &[plain, family], &tables).unwrap_err().to_string();
        assert!(error.contains("workload_module_scope") && error.contains("workloads/default/"), "{error}");
    }

    /// Family composition at freeze: each family use is composed with the workload's plan, else the
    /// default plan; every declared family's source, the workload's plans and the default module are kept; a plan
    /// outside `plans/<workload>/<family>.rs` and a family manifest of another name are refused.
    #[test]
    fn family_uses_are_composed_per_workload() {
        let root = crate::controller::test_support::scratch_root("members-compose");
        let workspace = root.join("author");
        write_family(&workspace.join("storages/plainfam"), "plainfam");
        let crate_dir = workspace.join("engine");
        write(&crate_dir.join("src/agent/mod.rs"), "// agent\n");
        write(&crate_dir.join("workloads/default/mod.rs"), "// default\n");
        write(&crate_dir.join("plans/sec/plainfam.rs"), "verus! {\npub fn plan() -> Plan { Plan { sorted: vec![] } }\n}\n");
        let workspace = workspace.canonicalize().unwrap();
        let crate_dir = crate_dir.canonicalize().unwrap();
        let manifest = members_manifest();
        let names = names();
        let flats = vec![("flat_ax_owner".to_string(), ContentId::from_bytes([1; 32])), ("flat_ax_void".to_string(), ContentId::from_bytes([2; 32]))];
        let tables = schema();
        let sources = SharedSources { manifest: &manifest, manifest_dir: &workspace, workspace: &workspace, crate_dir: &crate_dir };
        let compose = |workload: &str, frozen: &Path| {
            let crate_of = MemberCrate { workload, workloads: &names, flat_storages: &flats };
            compose_families(&sources, &crate_of, &tables, frozen)
        };
        let sec = root.join("frozen-sec");
        fs::create_dir_all(&sec).unwrap();
        let composed = compose("sec", &sec).unwrap();
        assert_eq!(composed.records, [FrozenFamily { name: "plainfam".into(), source: "storages/plainfam/verus-family.json".into(), plan: PlanChoice::Workload, plan_lines: 3, parts: 16 }]);
        assert_eq!(composed.uses["plainfam"].workspace, sec.join("families/plainfam"));
        assert!(sec.join("families/plainfam/verus-storage.json").is_file() && sec.join("plans/plainfam.rs").is_file());
        assert!(sec.join("family-sources/plainfam/verus-family.json").is_file() && sec.join("family-sources/plainfam/crate/src/builder/copy.rs").is_file());
        assert!(sec.join("default-module/mod.rs").is_file());
        composed.remove_scratch().unwrap();
        assert!(!sec.join("families").exists());
        let any = root.join("frozen-anyschema");
        fs::create_dir_all(&any).unwrap();
        let composed = compose("anyschema", &any).unwrap();
        assert_eq!(composed.records[0].plan, PlanChoice::Default);
        assert!(!any.join("plans").exists());
        let tpch = root.join("frozen-tpch");
        fs::create_dir_all(&tpch).unwrap();
        assert!(compose("tpch", &tpch).unwrap().uses.is_empty(), "a workload without family uses composes none");
        assert!(tpch.join("family-sources/plainfam").is_dir(), "and keeps the family sources");
        write(&crate_dir.join("plans/tpch/plainfam.rs"), "verus! {\npub fn plan() -> Plan { Plan { sorted: compute() } }\n}\n");
        let unused = root.join("frozen-unused");
        fs::create_dir_all(&unused).unwrap();
        assert!(compose("anyschema", &unused).err().unwrap().to_string().contains("plan_is_data"), "every plan file is data, used here or not");
        fs::remove_file(crate_dir.join("plans/tpch/plainfam.rs")).unwrap();
        write(&crate_dir.join("plans/sec/other.rs"), "");
        let stray = root.join("frozen-stray");
        fs::create_dir_all(&stray).unwrap();
        assert!(compose("sec", &stray).err().unwrap().to_string().contains("holds only <workload>/<family>.rs"));
        fs::remove_dir_all(crate_dir.join("plans")).unwrap();
        let mut renamed = members_manifest();
        renamed.families[0].name = "otherfam".into();
        renamed.workloads[1].storage_uses = vec![family_use("otherfam")];
        let sources = SharedSources { manifest: &renamed, manifest_dir: &workspace, workspace: &workspace, crate_dir: &crate_dir };
        let crate_of = MemberCrate { workload: "anyschema", workloads: &names, flat_storages: &flats };
        let other = root.join("frozen-other");
        fs::create_dir_all(&other).unwrap();
        assert!(compose_families(&sources, &crate_of, &tables, &other).err().unwrap().to_string().contains("whose name is plainfam"));
        fs::remove_dir_all(&root).unwrap();
    }

    /// A version folder of a run of several workloads with a shared engine, a default module, an own module of `sec`, a
    /// family and `sec`'s plan, and its seed manifest naming the family's source relative to `code/`.
    fn version_folder(dir: &Path) -> EngineManifest {
        write(&dir.join("code/agent/mod.rs"), "pub mod workload;\n");
        write(&dir.join("code/agent/common/sval.rs"), "// sval\n");
        write(&dir.join("code/workloads/default/mod.rs"), "// default\n");
        write(&dir.join("code/workloads/sec/mod.rs"), "// sec\n");
        write_family(&dir.join("code/families/plainfam"), "plainfam");
        write(&dir.join("code/plans/sec/plainfam.rs"), "verus! {\npub fn plan() -> Plan { Plan { sorted: vec![] } }\n}\n");
        write(&dir.join("node.json"), &json!({"id":"v003","accepted":true}).to_string());
        let mut seed = members_manifest().with_version_family_sources();
        seed.workloads[1].storage_uses = vec![admitted("dictpack", 4)];
        seed.workloads[1].modules = vec![module("mod.rs", ModuleRole::Reader)];
        seed.notes = "the head".into();
        write(&dir.join("seed-manifest.json"), &json!(seed).to_string());
        seed
    }

    /// A side's root from a version of several workloads: the shared engine, the seed workload's own
    /// module and plans under the member's name, the default module, the family under `storages/`; the manifest names
    /// only the member, with the seed workload's uses and modules, and passes the check of a crate of that one workload.
    /// A version of one workload gives its uses and no module. A missing or superfluous seed workload is refused.
    #[test]
    fn side_roots_from_version_folders() {
        let root = crate::controller::test_support::scratch_root("members-side-root");
        let version = root.join("run/engine/versions/v003");
        let seed = version_folder(&version);
        let workspace = root.join("author");
        let files = write_side_root(&workspace, &version, Some("sec"), "sec").unwrap();
        for file in ["engine/src/agent/mod.rs", "engine/src/agent/common/sval.rs", "engine/workloads/sec/mod.rs", "engine/workloads/default/mod.rs",
            "engine/plans/sec/plainfam.rs", "storages/plainfam/verus-family.json", "storages/plainfam/default_plan.rs", MANIFEST_FILE] {
            assert!(files.contains(&file.to_string()), "{file}: {files:?}");
        }
        let written: EngineManifest = read_json(&workspace.join(MANIFEST_FILE)).unwrap();
        assert_eq!(written.workloads, vec![WorkloadModules { name: "sec".into(), storage_uses: vec![admitted("dictpack", 4)], modules: vec![module("mod.rs", ModuleRole::Reader)] }]);
        assert_eq!(written.families, vec![FamilyDeclaration { name: "plainfam".into(), source: "storages/plainfam/verus-family.json".into() }]);
        assert_eq!((written.default_modules.clone(), written.notes.as_str(), written.modules.clone()), (seed.default_modules.clone(), "the head", seed.modules.clone()));
        let only = vec!["sec".to_string()];
        written.check(CrateForm::Members(&MemberCrate { workload: "sec", workloads: &only, flat_storages: &[] })).unwrap();
        assert!(write_side_root(&workspace, &version, Some("sec"), "sec").unwrap_err().to_string().contains("fresh workspace"));
        assert!(write_side_root(&root.join("a"), &version, None, "sec").unwrap_err().to_string().contains("seed.workload"));
        assert!(write_side_root(&root.join("b"), &version, Some("nope"), "sec").unwrap_err().to_string().contains("no workload nope"));
        // A version of one workload: its own uses, no module.
        let one = root.join("ce/engine/versions/v004");
        write(&one.join("code/agent/mod.rs"), "// agent\n");
        write(&one.join("node.json"), &json!({"id":"v004","accepted":true}).to_string());
        write(&one.join("manifest.json"), &json!(EngineManifest::example(&[("narrowpack1".into(), ContentId::from_bytes([5; 32]))])).to_string());
        let tpch = root.join("tpch");
        write_side_root(&tpch, &one, None, "tpch").unwrap();
        let written: EngineManifest = read_json(&tpch.join(MANIFEST_FILE)).unwrap();
        assert_eq!((written.workloads[0].name.as_str(), written.workloads[0].storage_uses.clone(), written.storage_uses.len()), ("tpch", vec![admitted("narrowpack1", 5)], 0));
        assert!(!tpch.join("engine/workloads").exists());
        assert!(write_side_root(&root.join("c"), &one, Some("tpch"), "tpch").unwrap_err().to_string().contains("version of one workload"));
        fs::remove_dir_all(&root).unwrap();
    }

    /// A side's root from an exported engine folder: its shared engine, default module, families and
    /// the member's plans; the uses are one family use per family, else the member's plain flat storages; no own module.
    #[test]
    fn side_roots_from_exported_engines() {
        let root = crate::controller::test_support::scratch_root("members-source-root");
        let export = root.join("export");
        write(&export.join("agent/mod.rs"), "pub mod workload;\n");
        write(&export.join("workloads/default/mod.rs"), "// default\n");
        write(&export.join("workloads/tpch/mod.rs"), "// opens the exporting run's storages\n");
        write_family(&export.join("storages/plainfam"), "plainfam");
        write(&export.join("plans/newschema/plainfam.rs"), "verus! {\npub fn plan() -> Plan { Plan { sorted: vec![] } }\n}\n");
        write(&export.join(EXPORT_MANIFEST_FILE), &json!(members_manifest()).to_string());
        let plain = vec![("flat_ax_owner".to_string(), ContentId::from_bytes([1; 32]))];
        let workspace = root.join("author");
        write_source_root(&workspace, &export, "newschema", &plain).unwrap();
        let written: EngineManifest = read_json(&workspace.join(MANIFEST_FILE)).unwrap();
        assert_eq!(written.workloads, vec![WorkloadModules { name: "newschema".into(), storage_uses: vec![family_use("plainfam")], modules: vec![] }]);
        assert!(workspace.join("engine/workloads/default/mod.rs").is_file() && !workspace.join("engine/workloads/tpch").exists() && !workspace.join("engine/workloads/newschema").exists());
        assert!(workspace.join("engine/plans/newschema/plainfam.rs").is_file() && workspace.join("storages/plainfam/verus-family.json").is_file());
        let only = vec!["newschema".to_string()];
        written.check(CrateForm::Members(&MemberCrate { workload: "newschema", workloads: &only, flat_storages: &plain })).unwrap();
        // Without families: the plain flat storages.
        let bare = root.join("bare");
        write(&bare.join("agent/mod.rs"), "// agent\n");
        write(&bare.join(EXPORT_MANIFEST_FILE), &json!(EngineManifest::example(&[])).to_string());
        write_source_root(&root.join("author2"), &bare, "newschema", &plain).unwrap();
        let written: EngineManifest = read_json(&root.join("author2").join(MANIFEST_FILE)).unwrap();
        assert_eq!(written.workloads[0].storage_uses, vec![admitted("flat_ax_owner", 1)]);
        assert!(write_source_root(&root.join("author3"), &root.join("missing"), "newschema", &plain).unwrap_err().to_string().contains("exported engine"));
        fs::remove_dir_all(&root).unwrap();
    }

    /// A frozen crate directory of workload `module` kind, its shared engine `agent`, kept default module and family.
    fn frozen_crate(dir: &Path, module: MemberModule, agent: &str) {
        write(&dir.join("crate/src/agent/mod.rs"), agent);
        write(&dir.join("crate/src/agent/workload/mod.rs"), &format!("// the composed module of {}\n", dir.display()));
        write(&dir.join("default-module/mod.rs"), "// default\n");
        write_family(&dir.join("family-sources/plainfam"), "plainfam");
        let member = MemberRecord { module, families: vec![], family_storages: vec![], plain_storages: vec![], inherited_storages: vec![], own_module_lines: 0, plan_lines: 0, shared_sources_digest: String::new() };
        let workload = super::super::FrozenWorkload { name: "w".into(), module_files: vec![], flat_access: gendb_verification::obligations::FlatAccess::Uniform, module_report: json!({}), member: Some(member) };
        let engine = super::super::FrozenEngine { kind: super::super::CANDIDATE_KIND.into(), format_version: 1, entry_identity: String::new(), toolkit_digest: String::new(), storage_uses: vec![],
            compiler: Default::default(), modules: vec![], author_files: vec![], framework_files: vec![], notes: String::new(), rule_set: json!(null), workload: Some(workload) };
        write(&dir.join("candidate.json"), &json!(engine).to_string());
    }

    /// A version's code from its crates and back: the shared engine without the composed module, an
    /// own module per workload that has one, the default module, the families and plans, then a side root from it; the
    /// shared sources' digest is equal for crates that differ only in their composed module.
    #[test]
    fn version_code_round_trips_and_the_shared_digest_ignores_the_module() {
        let root = crate::controller::test_support::scratch_root("members-code");
        let (tpch, sec) = (root.join("frozen-tpch"), root.join("frozen-sec"));
        frozen_crate(&tpch, MemberModule::Own, "// shared\n");
        frozen_crate(&sec, MemberModule::Default, "// shared\n");
        write(&sec.join("plans/plainfam.rs"), "verus! {\npub fn plan() -> Plan { Plan { sorted: vec![] } }\n}\n");
        assert_eq!(shared_sources_digest(&tpch).unwrap(), shared_sources_digest(&sec).unwrap(), "the composed module is not a shared source");
        let other = root.join("frozen-other");
        frozen_crate(&other, MemberModule::Default, "// another engine\n");
        assert_ne!(shared_sources_digest(&tpch).unwrap(), shared_sources_digest(&other).unwrap());
        let version = root.join("run/engine/versions/v001");
        let code = version.join("code");
        write_member_code(&code, &[("tpch", &tpch), ("sec", &sec)]).unwrap();
        assert!(!code.join("agent/workload").exists() && code.join("agent/mod.rs").is_file());
        assert!(code.join("workloads/tpch/mod.rs").is_file() && !code.join("workloads/sec").exists() && code.join("workloads/default/mod.rs").is_file());
        assert!(code.join("families/plainfam/verus-family.json").is_file() && code.join("plans/sec/plainfam.rs").is_file());
        write(&version.join("node.json"), &json!({"id":"v001","accepted":true}).to_string());
        let mut seed = members_manifest().with_version_family_sources();
        seed.workloads.retain(|w| w.name != "anyschema");
        write(&version.join("seed-manifest.json"), &json!(seed).to_string());
        let workspace = root.join("author");
        write_side_root(&workspace, &version, Some("sec"), "sec").unwrap();
        assert!(workspace.join("engine/plans/sec/plainfam.rs").is_file() && workspace.join("storages/plainfam/crate/src/builder/mod.rs").is_file());
        fs::remove_dir_all(&root).unwrap();
    }
}
