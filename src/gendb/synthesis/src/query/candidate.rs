//! A query author's candidate over stored data: its manifest (`verus-query.json`, format 2) and the freeze of a
//! submission into an immutable query crate (fixed entry v4, or v5 under declared integrity constraints) whose
//! framework files are a fresh generation for the statement and the declared storage uses, and whose `agent/**` files
//! are the author's.
//!
//! A storage use is either an admitted storage package (pinned by id; its interface text comes from the package's
//! stored closure) or a storage candidate in the author's workspace (frozen with it; checked, built and registered
//! through the same storage path as a workload author's). An engine crate of a run of several workloads may also name a
//! storage family's instance (`family`), which its freeze composes (`storage::family`) and [`resolve_uses`] then
//! freezes like a workspace storage; query manifests refuse it. The freeze checks, in order: the manifest schema and path
//! containment, every use (admitted, or frozen), coverage of the statement's demand (`storage_does_not_cover_demand`),
//! the central source scan of every author file (`freeze_author_crate`) and of every file an author wrote, including
//! the copied interfaces (`author_source_findings`), the storage composition rule for each use, the lexical
//! whole-statement-evaluator rule, and that the manifest declares every `agent/` file once with the entry's item.
//! Declared items are checked against Verus's own output only after the whole-crate run (`compile`).

use super::session::QuerySession;
use crate::controller::author::{CandidateSubmission, resolve_candidate_manifest};
use crate::controller::records::write_new_json;
use crate::query::compile::DeclaredModule;
use crate::storage::catalog;
use crate::storage::freeze::{FrozenStorage, freeze_error, freeze_storage, read_frozen_storage};
use crate::storage::policy::StoredDataPolicy;
use gendb_artifacts::verus as records;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_runtime::abi::GENDB_QUERY_SHIM_V4_SOURCE;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::storage::{check_storage_assumptions, run_constraints_digest};
use gendb_verification::obligations::{
    DeclaredSource, StorageName, StorageUse, author_source_findings, check_storage_composition, query_crate_files, query_entry, with_trusted_shim,
};
use gendb_verification::verus::{AuthorRoot, FrameworkSource, FrozenCrate, freeze_author_crate, scan_whole_statement_evaluator};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};

/// Conventional file name of the author's query manifest (the submission names its path).
pub const MANIFEST_FILE: &str = "verus-query.json";
/// `kind` of a frozen query candidate over stored data.
pub const CANDIDATE_KIND: &str = "verus_rust_stored";
/// The item the fixed query entry (v4, or v5 under declared integrity constraints) calls in `crate::agent`.
pub const REQUIRED_ITEMS: [&str; 1] = ["query"];

/// The narrow tool check behind the author requirement "no whole-statement evaluator". Lexical and documented as such
/// (`rules.json`); the requirement itself is audited on the trajectory. The whole-statement evaluation lives in exactly
/// two modules: `eval` (the recursive `exec_query`/`exec_pred`) and `entry` (the checked `evaluate` and the ordered
/// whole-statement `exec_ordered`). The per-operator helpers of `relational::{ops, group, aggregate, order, rows}`
/// stay callable. The check is `gendb_verification::verus::scan_whole_statement_evaluator`; engine crates apply a wider
/// rule (`engine_rules::WHOLE_STATEMENT_EVALUATOR_RULE`, which also refuses the helpers that can reach the evaluator).
pub const EVALUATOR_RULE: &str = "agent sources may not reference the whole-statement evaluator crate::exec::relational::{eval, entry} (eval: the recursive exec_query/exec_pred; entry: evaluate and exec_ordered; framework test infrastructure, calling it is not specialized synthesis): a narrow lexical check at freeze (comments and literals removed; the path `relational::eval`/`relational::entry` or a `relational::{..}` group naming them), backed by the trajectory audit. The per-operator helpers of exec::relational::{ops, group, aggregate, order, rows} are not refused by this check";

/// Author-declared role of one `agent/` file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ModuleRole {
    /// Declares the required entry item `query`.
    Entry,
    /// Reads stored data (directly or through storage readers) for the query.
    Reader,
    Kernel,
    Helper,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ModuleDeclaration {
    /// Path relative to `<crate_dir>/src/agent/`.
    pub file: String,
    pub role: ModuleRole,
    /// Item names as Verus reports them relative to the module (`name` or `Type::method`).
    pub items: Vec<String>,
}

/// The author's rustc code generation choice.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompilerChoice {
    /// rustc `-C opt-level` (0..=3).
    pub opt_level: u8,
    /// rustc `-C target-cpu` (for example `native`); absent = rustc default.
    #[serde(default)]
    pub target_cpu: Option<String>,
}

impl Default for CompilerChoice {
    fn default() -> Self {
        Self { opt_level: 3, target_cpu: None }
    }
}

/// One storage the query reads: an admitted package, or a storage candidate of this workspace. An engine of several
/// workloads (`engine.workloads`) may also name a storage family's instance (`family`; refused in query manifests).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StorageUseDeclaration {
    /// The storage's name (`crate::stores::<name>`, the `Stores` field); must equal the package's or candidate's name.
    pub name: String,
    /// An admitted storage package id (contract storages.json `use_as`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub admitted: Option<ContentId>,
    /// A `verus-storage.json` of this workspace (relative to this manifest's directory).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub workspace: Option<PathBuf>,
    /// Engine manifests of a run of several workloads only: the storage family (`storage::family`) whose instance over
    /// the workload's whole schema this use is, composed by GenDB at freeze; `name` is the family's name. Absent
    /// elsewhere (and the declaration keeps its JSON identity).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub family: Option<String>,
}

impl StorageUseDeclaration {
    /// A use of the admitted package `package` named `name`.
    pub fn admitted(name: &str, package: ContentId) -> Self {
        Self { name: name.to_string(), admitted: Some(package), workspace: None, family: None }
    }

    /// The number of sources the declaration names (exactly one is valid: admitted, workspace or family).
    pub fn source_count(&self) -> usize {
        usize::from(self.admitted.is_some()) + usize::from(self.workspace.is_some()) + usize::from(self.family.is_some())
    }
}

/// `verus-query.json`. Paths are relative to the manifest's directory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct QueryManifest {
    pub format_version: u32,
    pub crate_dir: PathBuf,
    /// The storages the query reads, in the order of `Stores` and of the entry's `uses`.
    pub storage_uses: Vec<StorageUseDeclaration>,
    pub modules: Vec<ModuleDeclaration>,
    #[serde(default)]
    pub compiler: Option<CompilerChoice>,
    #[serde(default)]
    pub notes: String,
}

impl QueryManifest {
    /// The generated example of the author workspace.
    pub fn example() -> Self {
        Self {
            format_version: 2,
            crate_dir: "verus".into(),
            storage_uses: vec![StorageUseDeclaration { name: "<storage name>".into(), admitted: None, workspace: Some("<path to a verus-storage.json, or use admitted: <package id>>".into()), family: None }],
            modules: vec![ModuleDeclaration { file: "mod.rs".into(), role: ModuleRole::Entry, items: REQUIRED_ITEMS.map(String::from).to_vec() }],
            compiler: Some(CompilerChoice::default()),
            notes: String::new(),
        }
    }

    /// JSON schema of the manifest (author contract).
    pub fn schema() -> Value {
        json!({"type":"object","additionalProperties":false,"required":["format_version","crate_dir","storage_uses","modules"],
            "properties":{
                "format_version":{"const":2},
                "crate_dir":{"type":"string","description":"crate directory relative to this manifest's directory, inside the author workspace, with no `..` component; the author owns only <crate_dir>/src/agent/**"},
                "storage_uses":{"type":"array","minItems":1,"description":"the storages the query reads, in Stores field order; together they must store every column and table the statement demands",
                    "items":{"type":"object","additionalProperties":false,"required":["name"],"properties":{
                        "name":{"type":"string","description":"the storage's name (its package's or candidate's)"},
                        "admitted":{"type":"string","pattern":"^[0-9a-f]{64}$","description":"an admitted storage package id (storages.json use_as)"},
                        "workspace":{"type":"string","description":"a verus-storage.json of this workspace, relative to this manifest's directory (`..` allowed while the file stays inside the author workspace)"}},
                        "description":"exactly one of admitted or workspace"}},
                "modules":{"type":"array","minItems":1,"description":"every .rs file under src/agent exactly once",
                    "items":{"type":"object","additionalProperties":false,"required":["file","role","items"],"properties":{
                        "file":{"type":"string","description":"relative to src/agent, e.g. mod.rs or kernels/sum.rs"},
                        "role":{"enum":["entry","reader","kernel","helper"]},
                        "items":{"type":"array","items":{"type":"string"},"description":"functions this module contributes, named as Verus reports them relative to the module: name or Type::method; query must be declared in the entry module"}}}},
                "compiler":{"type":"object","additionalProperties":false,"required":["opt_level"],"properties":{
                    "opt_level":{"type":"integer","minimum":0,"maximum":3},"target_cpu":{"type":["string","null"]}},
                    "description":"optional rustc code generation; default opt_level 3, rustc default target cpu"},
                "notes":{"type":"string"}}})
    }

    /// The manifest's own completeness rules (the schema cannot state them all).
    fn check(&self) -> Result<(), AdmissionError> {
        if self.format_version != 2 {
            return Err(AdmissionError::refusal(
                "a query manifest has format_version 2 (verus-query.json over storage uses); format 1 (verus-candidate.json, one crate with its own builder) is the saved v3 route and is not synthesized any more",
            ));
        }
        if self.modules.is_empty() || self.storage_uses.is_empty() {
            return Err(AdmissionError::refusal("a query manifest needs at least one storage use and one module"));
        }
        if self.compiler.as_ref().is_some_and(|choice| choice.opt_level > 3) {
            return Err(AdmissionError::refusal("compiler.opt_level must be 0..=3"));
        }
        let mut names = BTreeSet::new();
        for storage_use in &self.storage_uses {
            if storage_use.family.is_some() {
                return Err(AdmissionError::refusal(format!("storage use {}: family is a field of engine manifests of a run of several workloads, not of query manifests", storage_use.name)));
            }
            if storage_use.admitted.is_some() == storage_use.workspace.is_some() {
                return Err(AdmissionError::refusal(format!("storage use {} needs exactly one of admitted or workspace", storage_use.name)));
            }
            if !names.insert(storage_use.name.as_str()) {
                return Err(AdmissionError::refusal(format!("storage {} is used twice", storage_use.name)));
            }
        }
        for required in REQUIRED_ITEMS {
            if !self.modules.iter().any(|m| m.role == ModuleRole::Entry && m.items.iter().any(|i| i == required)) {
                return Err(AdmissionError::refusal(format!("the entry module must declare item {required}")));
            }
        }
        Ok(())
    }
}

/// Where a frozen storage use comes from. No path: the frozen candidate of equal sources is equal
/// (unchanged-resubmission detection compares the whole record).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StorageSource {
    Admitted { package: ContentId },
    /// Frozen with the candidate under `<frozen>/storages/<name>`; its author files are in `modules`.
    Workspace { manifest: PathBuf },
}

/// One frozen storage use.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenUse {
    pub name: String,
    pub source: StorageSource,
    pub declaration: DeclaredSource,
}

/// One declared author file of a frozen candidate (an `agent/` file, or a workspace storage's file).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenModule {
    /// Relative to the crate's `src/` (`agent/...`), or `storages/<name>/<src-relative>` for a workspace storage.
    pub file: String,
    pub role: String,
    pub items: Vec<String>,
    /// The frozen source file.
    pub source: PathBuf,
}

/// `candidate.json` of a frozen submission (the recorded candidate of the ledger's trial).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenCandidate {
    pub kind: String,
    pub format_version: u32,
    /// Statement key v2 (schema + statement + parameters + output).
    pub statement_key: String,
    pub sql: String,
    pub entry_identity: String,
    pub storage_uses: Vec<FrozenUse>,
    pub compiler: CompilerChoice,
    /// The query's `agent/` modules, then every workspace storage's modules.
    pub modules: Vec<FrozenModule>,
    /// Author files of the query crate, relative to `src/`.
    pub author_files: Vec<String>,
    /// Framework files relative to `src/`, in generation order.
    pub framework_files: Vec<String>,
    pub notes: String,
}

impl FrozenCandidate {
    /// The frozen query crate under its freeze directory (`<frozen_dir>/crate`).
    pub fn crate_in(&self, frozen_dir: &Path) -> FrozenCrate {
        FrozenCrate::from_recorded_author_files(frozen_dir.join("crate"), self.author_files.clone(), self.framework_files.clone())
    }

    /// The query crate's declared `agent/` modules.
    pub fn agent_modules(&self) -> Vec<DeclaredModule> {
        self.modules
            .iter()
            .filter(|m| m.file.starts_with("agent/"))
            .map(|m| DeclaredModule { file: m.file.clone(), role: m.role.clone(), items: m.items.clone() })
            .collect()
    }

    /// The frozen workspace storage of use `name` (`<frozen_dir>/storages/<name>`).
    pub fn workspace_storage(&self, frozen_dir: &Path, name: &str) -> Result<(PathBuf, FrozenStorage), AdmissionError> {
        let dir = frozen_dir.join("storages").join(name);
        Ok((dir.clone(), read_frozen_storage(&dir)?))
    }

    /// Identity of the query crate's sources and compiler choice: two freezes with equal keys compile to the same
    /// library (framework files follow from the statement and the storage uses, which the key includes). Used only to
    /// reuse a local job's compiled library.
    pub fn source_key(&self, krate: &FrozenCrate) -> Result<Vec<u8>, AdmissionError> {
        let mut key = serde_json::to_vec(&(&self.compiler, &self.storage_uses)).map_err(AdmissionError::tool)?;
        for file in krate.framework_files.iter().filter(|f| f.starts_with("stores/")).chain(&krate.author_files) {
            key.extend(file.as_bytes());
            key.push(0);
            key.extend(fs::read(krate.root.join("src").join(file)).map_err(AdmissionError::tool)?);
            key.push(0);
        }
        Ok(key)
    }
}

/// A short identity of a crate's exact author content (its source key, [`FrozenCandidate::source_key`]), shown in
/// local job results, the next attempt's trial log and its submission list, so the author can tell versions apart.
pub fn crate_version(source_key: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    Sha256::digest(source_key).iter().take(6).map(|b| format!("{b:02x}")).collect()
}

/// What the next attempt reads about a retained query submission's code (`RolePolicy::submission_code`): its
/// `crate_version` (the identity local trials of the same code report), its frozen crate, and, given the author
/// `workspace`, whether the submitted manifest and the crate's `src/agent` files there are still exactly the frozen
/// ones (`workspace`: `same` or `changed`; `not_compared` without a workspace). Workspace storages the manifest names
/// are not compared. A frozen record that cannot be read is named (`error`).
pub fn submission_code(frozen_dir: &Path, submission: &Value, workspace: Option<&Path>) -> Value {
    let frozen: FrozenCandidate = match fs::read(frozen_dir.join("candidate.json")).map_err(|e| e.to_string()).and_then(|bytes| serde_json::from_slice(&bytes).map_err(|e| e.to_string())) {
        Ok(frozen) => frozen,
        Err(error) => return json!({"error":format!("{}: {error}", frozen_dir.join("candidate.json").display())}),
    };
    let krate = frozen.crate_in(frozen_dir);
    let version = frozen.source_key(&krate).map(|key| crate_version(&key)).map_err(|e| e.to_string());
    let comparison = match workspace {
        None => "not_compared",
        Some(workspace) if workspace_holds(frozen_dir, &frozen, submission, workspace) => "same",
        Some(_) => "changed",
    };
    json!({"crate_version":version.as_ref().ok(),"error":version.err(),"frozen_crate":krate.root,"workspace":comparison})
}

/// Whether the workspace still holds `frozen`'s code: the submitted manifest (JSON-equal to the frozen
/// `manifest.json`) and exactly the frozen `agent/` files with equal bytes in its crate.
fn workspace_holds(frozen_dir: &Path, frozen: &FrozenCandidate, submission: &Value, workspace: &Path) -> bool {
    let read_json = |path: &Path| fs::read(path).ok().and_then(|bytes| serde_json::from_slice::<Value>(&bytes).ok());
    let Some(manifest_path) = submission["candidate_manifest"].as_str().map(|path| workspace.join(path)) else { return false };
    let (Some(manifest), Some(frozen_manifest)) = (read_json(&manifest_path), read_json(&frozen_dir.join("manifest.json"))) else { return false };
    let Some(crate_dir) = manifest["crate_dir"].as_str().and_then(|dir| manifest_path.parent().map(|parent| parent.join(dir))) else { return false };
    let mut workspace_files = BTreeSet::new();
    collect_files(&crate_dir.join("src"), &crate_dir.join("src/agent"), &mut workspace_files);
    let frozen_files: BTreeSet<PathBuf> = frozen.author_files.iter().map(PathBuf::from).collect();
    manifest == frozen_manifest
        && workspace_files == frozen_files
        && frozen_files.iter().all(|file| fs::read(crate_dir.join("src").join(file)).ok() == fs::read(frozen_dir.join("crate/src").join(file)).ok())
}

/// Every file under `dir`, relative to `base`.
fn collect_files(base: &Path, dir: &Path, found: &mut BTreeSet<PathBuf>) {
    for entry in fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_files(base, &path, found);
        } else if let Ok(relative) = path.strip_prefix(base) {
            found.insert(relative.to_path_buf());
        }
    }
}

/// Resolve a relative path inside `base` (no absolute path, no `..`; the resolved file stays inside `base`).
pub fn inside(base: &Path, path: &Path) -> Result<PathBuf, AdmissionError> {
    if path.is_absolute() || path.components().any(|c| !matches!(c, Component::Normal(_) | Component::CurDir)) {
        return Err(AdmissionError::missing_input("candidate source must be a relative path within its workspace"));
    }
    let base = base.canonicalize().map_err(AdmissionError::missing_input)?;
    let resolved = base.join(path).canonicalize().map_err(AdmissionError::missing_input)?;
    if !resolved.starts_with(&base) {
        return Err(AdmissionError::missing_input("candidate source escapes workspace"));
    }
    Ok(resolved)
}

/// Resolve a workspace storage use's `verus-storage.json`, given relative to the query manifest's directory. Unlike
/// `crate_dir`, it may climb with `..` to a sibling directory of the author workspace (a diagnostic query crate under
/// `diagnostic-queries/<i>/` reads `../../storages/<name>/verus-storage.json`; a manifest in `c2/` reads
/// `../new-storages/<name>/verus-storage.json`); the resolved file must stay inside the workspace (`workspace` is
/// canonical).
fn workspace_storage_manifest(workspace: &Path, manifest_dir: &Path, path: &Path) -> Result<PathBuf, AdmissionError> {
    if path.is_absolute() {
        return Err(AdmissionError::missing_input("a workspace storage use must be relative to the query manifest's directory"));
    }
    let resolved = manifest_dir.join(path).canonicalize().map_err(|e| AdmissionError::missing_input(format!("{}: {e}", path.display())))?;
    if !resolved.starts_with(workspace) {
        return Err(AdmissionError::missing_input(format!("workspace storage use {} escapes the author workspace", path.display())));
    }
    Ok(resolved)
}

/// A resolved storage use: its name, declaration, the interface text the crate copies, and every file of the
/// storage's checked (or frozen) build for the composition check. Shared by query and engine freezes.
pub(crate) struct ResolvedUse {
    pub(crate) frozen: FrozenUse,
    pub(crate) name: StorageName,
    pub(crate) interface: Vec<FrameworkSource>,
    pub(crate) storage_files: Vec<FrameworkSource>,
    pub(crate) modules: Vec<FrozenModule>,
    /// The admitted package read (`None`: a workspace storage).
    pub(crate) package: Option<ContentId>,
    /// Every admitted storage it is built from, transitively, as `(name, package)` (empty: built from source columns).
    pub(crate) sources: Vec<(String, ContentId)>,
}

/// What resolving declared storage uses reads: the admitted library, the admitted packages replaced by their current
/// versions, the run's stored-data policy (the part of [`QueryFreeze`] an engine freeze shares) and, for an engine crate
/// of a run of several workloads, the family instances composed for it.
pub(crate) struct UseContext<'a> {
    pub(crate) library: &'a Path,
    pub(crate) substitutes: &'a BTreeMap<ContentId, ContentId>,
    pub(crate) policy: &'a StoredDataPolicy,
    /// Per family use name, its composed instance (`storage::family::compose_instance`): the storage workspace holding
    /// its `verus-storage.json`, and the family's manifest path relative to the author workspace (the frozen use's
    /// recorded source). Empty outside such a freeze: a family use is then refused.
    pub(crate) families: &'a BTreeMap<String, ComposedUse>,
}

/// One family instance composed for an engine freeze ([`UseContext::families`]).
pub(crate) struct ComposedUse {
    /// The composed storage workspace (its `verus-storage.json` at the root).
    pub(crate) workspace: PathBuf,
    /// The family's `verus-family.json`, relative to the author workspace.
    pub(crate) family_manifest: PathBuf,
}

/// Where the query crate is frozen from and for which statement.
pub struct QueryFreeze<'a> {
    pub workspace: &'a Path,
    pub session: &'a QuerySession,
    /// The admitted library (admitted storage uses are read from it).
    pub library: &'a Path,
    /// Admitted packages replaced by their current versions (re-verified against the current framework), for admitted
    /// uses and for the `built_from` sources of workspace storages.
    pub substitutes: &'a BTreeMap<ContentId, ContentId>,
    /// The run's stored-data policy: under `fixed_flat` only eligible flat packages may be named, no workspace storage,
    /// and no `static` item in the agent files.
    pub policy: &'a StoredDataPolicy,
}

/// The frozen candidate and the framework files it was frozen with (for the author's workspace copy).
pub struct Frozen {
    pub candidate: FrozenCandidate,
    pub framework: Vec<FrameworkSource>,
    /// The author's workspace crate directory.
    pub workspace_crate: PathBuf,
}

/// Parse and freeze `submission` into the fresh directory `frozen_dir` (`crate/`, `storages/<name>/` for workspace
/// storages, `candidate.json`, `decision.json`, `manifest.json`).
pub fn freeze(context: &QueryFreeze<'_>, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Frozen, AdmissionError> {
    let workspace = context.workspace.canonicalize().map_err(AdmissionError::tool)?;
    let (manifest_path, _) = resolve_candidate_manifest(&workspace, &submission.candidate_manifest)
        .map_err(|e| AdmissionError::missing_input(format!("{}: {e}", submission.candidate_manifest.display())))?;
    let bytes = fs::read(&manifest_path).map_err(|e| AdmissionError::missing_input(format!("{}: {e}", manifest_path.display())))?;
    let manifest: QueryManifest = serde_json::from_slice(&bytes).map_err(|e| AdmissionError::refusal(format!("verus-query manifest: {e}")))?;
    manifest.check()?;
    let base = manifest_path.parent().ok_or_else(|| AdmissionError::missing_input("manifest directory absent"))?;
    let crate_dir = inside(base, &manifest.crate_dir)?;
    if !crate_dir.starts_with(&workspace) {
        return Err(AdmissionError::refusal("crate_dir must be inside the author workspace"));
    }
    let agent = crate_dir.join("src/agent");
    if !agent.is_dir() {
        return Err(AdmissionError::missing_input(format!("{} is not a directory", agent.display())));
    }
    fs::create_dir(frozen_dir).map_err(AdmissionError::tool)?;
    let statement = context.session.statement();
    let schema = &statement.instance.doc.tables;
    let no_families = BTreeMap::new();
    let use_context = UseContext { library: context.library, substitutes: context.substitutes, policy: context.policy, families: &no_families };
    let uses = resolve_uses(&use_context, &manifest.storage_uses, base, &workspace, frozen_dir, schema)?;
    check_source_versions(&uses)?;
    let storage_uses: Vec<StorageUse<'_>> = uses.iter().map(|u| StorageUse { name: &u.name, declaration: &u.frozen.declaration, interface: &u.interface }).collect();
    let framework = query_crate_files(&statement.instance, &statement.source, &storage_uses, &statement.identity()).map_err(|e| match e.failure_class() {
        "missing_input" => AdmissionError::missing_input(e),
        _ => AdmissionError::tool(e),
    })?;
    let framework = with_trusted_shim(framework, GENDB_QUERY_SHIM_V4_SOURCE);
    let krate = freeze_author_crate(&framework, &[AuthorRoot { crate_directory: "agent", source: &agent }], &frozen_dir.join("crate")).map_err(freeze_error)?;
    let query_files = crate_files(&krate)?;
    refuse_author_findings(&query_files)?;
    if context.policy.is_fixed_flat() {
        refuse_static_items(&query_files)?;
    }
    for u in &uses {
        check_storage_composition(&u.storage_files, &query_files, &u.name)
            .map_err(|e| AdmissionError::refusal(format!("storage composition of {}: {e}", u.name)))?;
    }
    for file in &krate.agent_files {
        let text = fs::read_to_string(krate.root.join("src/agent").join(file)).map_err(AdmissionError::tool)?;
        if !scan_whole_statement_evaluator(file, &text).is_empty() {
            return Err(AdmissionError::refusal(format!("agent/{file} references the whole-query evaluator ({EVALUATOR_RULE})")));
        }
    }
    let mut modules = declared_agent_modules(&manifest.modules, &krate)?;
    modules.extend(uses.iter().flat_map(|u| u.modules.clone()));
    let candidate = FrozenCandidate {
        kind: CANDIDATE_KIND.into(),
        format_version: 2,
        statement_key: statement.key_v4_id.clone(),
        sql: statement.sql.clone(),
        entry_identity: query_entry(&statement.instance).identity.into(),
        storage_uses: uses.into_iter().map(|u| u.frozen).collect(),
        compiler: manifest.compiler.clone().unwrap_or_default(),
        modules,
        author_files: krate.author_files.clone(),
        framework_files: krate.framework_files.clone(),
        notes: manifest.notes.clone(),
    };
    let record = |name: &str, value: Value| write_new_json(&frozen_dir.join(name), &value).map_err(AdmissionError::tool);
    record("candidate.json", json!(candidate))?;
    record("decision.json", json!(submission))?;
    record("manifest.json", json!(manifest))?;
    Ok(Frozen { candidate, framework, workspace_crate: crate_dir })
}

/// Every declared use, resolved: an admitted package from the library, or a workspace storage frozen into
/// `<frozen_dir>/storages/<name>`.
pub(crate) fn resolve_uses(
    context: &UseContext<'_>,
    declared_uses: &[StorageUseDeclaration],
    manifest_dir: &Path,
    workspace: &Path,
    frozen_dir: &Path,
    schema: &[gendb_frontend::ast::TableDef],
) -> Result<Vec<ResolvedUse>, AdmissionError> {
    let mut resolved = vec![];
    for declared in declared_uses {
        let name = StorageName::new(&declared.name).map_err(AdmissionError::refusal)?;
        if context.policy.is_fixed_flat() && (declared.workspace.is_some() || declared.family.is_some()) {
            return Err(fixed_flat_workspace_storage(&declared.name));
        }
        if declared.source_count() != 1 {
            return Err(AdmissionError::refusal(format!("storage use {} needs exactly one of admitted, workspace or family", declared.name)));
        }
        let use_ = match (&declared.admitted, &declared.workspace) {
            (None, None) => {
                // A family use: its instance was composed for this freeze (`storage::family::compose_instance`) and is
                // frozen as a workspace storage under `<frozen_dir>/storages/<name>`, the family's manifest recorded as
                // its source.
                let family = declared.family.as_deref().unwrap_or_default();
                let composed = context.families.get(&declared.name).ok_or_else(|| {
                    AdmissionError::refusal(format!("storage use {}: the instance of family {family} is composed only by the engine freeze of a run of several workloads (engine.workloads)", declared.name))
                })?;
                let dir = frozen_dir.join("storages").join(&declared.name);
                fs::create_dir_all(frozen_dir.join("storages")).map_err(AdmissionError::tool)?;
                let store = ObjectStore::open_existing(context.library).map_err(AdmissionError::tool)?;
                let manifest = Path::new(crate::storage::manifest::STORAGE_MANIFEST_FILE);
                let storage = freeze_storage(&composed.workspace, manifest, &dir, schema, Some(&store), context.substitutes)?;
                if storage.manifest.name != declared.name {
                    return Err(AdmissionError::tool(format!("the composed instance of family {family} is named {}, not {}", storage.manifest.name, declared.name)));
                }
                ResolvedUse {
                    interface: storage.interface_files(&dir)?,
                    storage_files: storage.crate_files(&dir)?,
                    frozen: FrozenUse {
                        name: declared.name.clone(),
                        source: StorageSource::Workspace { manifest: composed.family_manifest.clone() },
                        declaration: storage.declaration.clone(),
                    },
                    name,
                    modules: frozen_storage_modules(&declared.name, &storage),
                    package: None,
                    sources: derivation_sources(&store, storage.derivation.as_ref())?,
                }
            }
            (Some(package_id), None) => {
                let package_id = context.substitutes.get(package_id).unwrap_or(package_id);
                let store = ObjectStore::open_existing(context.library).map_err(AdmissionError::tool)?;
                if context.policy.is_fixed_flat()
                    && let Some(reason) = context.policy.ineligible(&store, *package_id, &declared.name)?
                {
                    return Err(AdmissionError::refusal(reason));
                }
                let (package, declaration) = catalog::admitted_storage(&store, *package_id)?;
                check_storage_assumptions(&package, run_constraints_digest(schema)?)?;
                if package.name != declared.name {
                    return Err(AdmissionError::refusal(format!("storage package {package_id} is named {}, not {}", package.name, declared.name)));
                }
                let build = records::storage_build(&store, &package).map_err(AdmissionError::tool)?;
                let storage_files = build
                    .source_texts(&store)
                    .map_err(AdmissionError::tool)?
                    .into_iter()
                    .map(|(path, _, text)| FrameworkSource { path, text })
                    .collect();
                let interface = catalog::interface_files(&store, &package)?;
                let sources = derivation_sources(&store, package.derived_from.as_ref())?;
                ResolvedUse {
                    frozen: FrozenUse { name: declared.name.clone(), source: StorageSource::Admitted { package: *package_id }, declaration },
                    name,
                    interface,
                    storage_files,
                    modules: vec![],
                    package: Some(*package_id),
                    sources,
                }
            }
            (None, Some(path)) => {
                let manifest_path = workspace_storage_manifest(workspace, manifest_dir, path)?;
                let relative = manifest_path.strip_prefix(workspace).map_err(AdmissionError::tool)?.to_path_buf();
                let dir = frozen_dir.join("storages").join(&declared.name);
                fs::create_dir_all(frozen_dir.join("storages")).map_err(AdmissionError::tool)?;
                let store = ObjectStore::open_existing(context.library).map_err(AdmissionError::tool)?;
                let storage = freeze_storage(workspace, &relative, &dir, schema, Some(&store), context.substitutes)?;
                if storage.manifest.name != declared.name {
                    return Err(AdmissionError::refusal(format!("workspace storage {} is named {}, not {}", path.display(), storage.manifest.name, declared.name)));
                }
                ResolvedUse {
                    interface: storage.interface_files(&dir)?,
                    storage_files: storage.crate_files(&dir)?,
                    frozen: FrozenUse { name: declared.name.clone(), source: StorageSource::Workspace { manifest: relative }, declaration: storage.declaration.clone() },
                    name,
                    modules: frozen_storage_modules(&declared.name, &storage),
                    package: None,
                    sources: derivation_sources(&store, storage.derivation.as_ref())?,
                }
            }
            _ => unreachable!("checked: exactly one source"),
        };
        resolved.push(use_);
    }
    Ok(resolved)
}

/// The frozen modules of the workspace storage `storage` of use `name` (`storages/<name>/<src-relative>`).
fn frozen_storage_modules(name: &str, storage: &FrozenStorage) -> Vec<FrozenModule> {
    storage
        .modules
        .iter()
        .map(|m| FrozenModule { file: format!("storages/{name}/{}", m.file), role: json!(m.role).as_str().unwrap_or_default().to_string(), items: m.items.clone(), source: m.source.clone() })
        .collect()
}

/// Under `fixed_flat` a query reads only the prepared flat storages: a workspace storage (new, or a copy of a flat one) is
/// refused.
fn fixed_flat_workspace_storage(name: &str) -> AdmissionError {
    AdmissionError::refusal(format!(
        "fixed_flat_workspace_storage: storage use {name} names a workspace storage; under storage_policy fixed_flat a query names only the admitted flat packages listed in storages.json"
    ))
}

/// [`fixed_flat_workspace_storage`] for the uses of a frozen candidate (checked again before its storages resolve).
pub fn refuse_workspace_storages(uses: &[FrozenUse]) -> Result<(), AdmissionError> {
    match uses.iter().find(|u| matches!(u.source, StorageSource::Workspace { .. })) {
        Some(workspace) => Err(fixed_flat_workspace_storage(&workspace.name)),
        None => Ok(()),
    }
}

/// Under `fixed_flat`, refuse `static` items in the query's agent files (`storage::flat::static_item_refusal`).
pub(crate) fn refuse_static_items(files: &[FrameworkSource]) -> Result<(), AdmissionError> {
    match crate::storage::flat::static_item_refusal(files.iter().map(|f| (f.path.as_str(), f.text.as_str()))) {
        Some(reason) => Err(AdmissionError::refusal(reason)),
        None => Ok(()),
    }
}

/// Every admitted storage a storage is built from, transitively: `(name, package)` of each source of `derivation`, then
/// of the sources' own derivations.
fn derivation_sources(store: &ObjectStore, derivation: Option<&records::VerusDerivationV1>) -> Result<Vec<(String, ContentId)>, AdmissionError> {
    let mut sources = vec![];
    for source in derivation.into_iter().flat_map(|d| &d.sources) {
        sources.push((source.name.clone(), source.package));
        let record = records::resolve_admitted_storage(store, source.package).map_err(AdmissionError::tool)?;
        sources.extend(derivation_sources(store, record.derived_from.as_ref())?);
    }
    Ok(sources)
}

/// A storage built from admitted storages was proved over the exact interfaces of its sources: its `represents` and
/// readers may name `crate::stores::<source>` items, which in a query crate resolve to whichever version of that name
/// the query reads. So a query that reads a storage and also reads one of its (transitive) sources by name must read
/// exactly the recorded source package; otherwise it is refused (`storage_source_version_mismatch`). A source the query
/// does not read is absent from its crate, so a storage whose specification names it does not compile there.
pub(crate) fn check_source_versions(uses: &[ResolvedUse]) -> Result<(), AdmissionError> {
    for user in uses {
        for (source, package) in &user.sources {
            if let Some(other) = uses.iter().find(|u| u.frozen.name == *source)
                && other.package != Some(*package)
            {
                let read = other.package.map_or("a workspace storage".to_string(), |p| format!("package {p}"));
                return Err(AdmissionError::refusal(format!(
                    "storage_source_version_mismatch: storage {} is built from {source} package {package}, but this query reads {source} as {read}; read that exact package (or a storage built from the version you read)",
                    user.frozen.name
                )));
            }
        }
    }
    Ok(())
}

/// Every file of a frozen crate (framework and author), relative to `src/`.
pub fn crate_files(krate: &FrozenCrate) -> Result<Vec<FrameworkSource>, AdmissionError> {
    krate
        .framework_files
        .iter()
        .chain(&krate.author_files)
        .map(|path| Ok(FrameworkSource { path: path.clone(), text: fs::read_to_string(krate.root.join("src").join(path)).map_err(AdmissionError::tool)? }))
        .collect()
}

/// The central author-source rule over every file an author wrote (the query's `agent/**` and the copied storage
/// interfaces), as admission applies it.
pub(crate) fn refuse_author_findings(files: &[FrameworkSource]) -> Result<(), AdmissionError> {
    let findings = author_source_findings(files);
    if findings.is_empty() {
        return Ok(());
    }
    Err(AdmissionError::refusal(format!("refusal-list findings {}", json!(findings))))
}

/// The manifest's modules, each an `agent/` file of the frozen crate, declared exactly once, covering every agent file.
pub(crate) fn declared_agent_modules(declared_modules: &[ModuleDeclaration], krate: &FrozenCrate) -> Result<Vec<FrozenModule>, AdmissionError> {
    let mut declared = BTreeSet::new();
    let mut modules = vec![];
    for module in declared_modules {
        if !declared.insert(module.file.clone()) {
            return Err(AdmissionError::refusal(format!("module {} declared twice", module.file)));
        }
        if !krate.agent_files.contains(&module.file) {
            return Err(AdmissionError::missing_input(format!("declared module {} is not an agent file", module.file)));
        }
        modules.push(FrozenModule {
            file: format!("agent/{}", module.file),
            role: json!(module.role).as_str().unwrap_or_default().to_string(),
            items: module.items.clone(),
            source: krate.root.join("src/agent").join(&module.file),
        });
    }
    let undeclared: Vec<&String> = krate.agent_files.iter().filter(|f| !declared.contains(*f)).collect();
    if !undeclared.is_empty() {
        return Err(AdmissionError::refusal(format!("agent files not declared in the manifest: {undeclared:?}")));
    }
    Ok(modules)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A submission's code identity is the local trials' `crate_version` of the same crate content, and the
    /// workspace holds it exactly while the submitted manifest and every `src/agent` file are unchanged.
    #[test]
    fn submission_code_names_the_frozen_crate_and_compares_the_workspace() {
        let root = crate::controller::test_support::scratch_root("submission-code");
        let (frozen, workspace) = (root.join("frozen"), root.join("author"));
        let manifest = json!({"format_version":2,"crate_dir":"verus","storage_uses":[],"modules":[]});
        for (crate_src, manifest_path) in [(frozen.join("crate/src"), frozen.join("manifest.json")), (workspace.join("verus/src"), workspace.join("verus-query.json"))] {
            fs::create_dir_all(crate_src.join("agent")).unwrap();
            fs::write(crate_src.join("agent/mod.rs"), "pub fn query() {}\n").unwrap();
            fs::write(&manifest_path, manifest.to_string()).unwrap();
        }
        let candidate = json!({"kind":CANDIDATE_KIND,"format_version":2,"statement_key":"k","sql":"SELECT 1","entry_identity":"e","storage_uses":[],
            "compiler":{"opt_level":3},"modules":[],"author_files":["agent/mod.rs"],"framework_files":[],"notes":""});
        fs::write(frozen.join("candidate.json"), candidate.to_string()).unwrap();
        let submission = json!({"candidate_manifest":"verus-query.json"});
        let code = submission_code(&frozen, &submission, Some(&workspace));
        let frozen_candidate: FrozenCandidate = serde_json::from_value(candidate).unwrap();
        let expected = crate_version(&frozen_candidate.source_key(&frozen_candidate.crate_in(&frozen)).unwrap());
        assert_eq!((code["crate_version"].as_str(), code["workspace"].as_str()), (Some(expected.as_str()), Some("same")), "{code}");
        assert_eq!(submission_code(&frozen, &submission, None)["workspace"], "not_compared");
        fs::write(workspace.join("verus/src/agent/extra.rs"), "").unwrap();
        assert_eq!(submission_code(&frozen, &submission, Some(&workspace))["workspace"], "changed", "an added agent file changes the code");
        fs::remove_file(workspace.join("verus/src/agent/extra.rs")).unwrap();
        fs::write(workspace.join("verus/src/agent/mod.rs"), "pub fn query() { }\n").unwrap();
        assert_eq!(submission_code(&frozen, &submission, Some(&workspace))["workspace"], "changed", "an edited agent file changes the code");
        assert!(submission_code(&root.join("missing"), &submission, None)["error"].is_string());
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn query_manifest_rules() {
        let mut manifest = QueryManifest::example();
        manifest.storage_uses[0].name = "by_day".into();
        manifest.check().unwrap();
        let decoded: QueryManifest = serde_json::from_value(json!(manifest)).unwrap();
        assert_eq!(decoded, manifest);
        let mut both = manifest.clone();
        both.storage_uses[0].admitted = Some(ContentId::from_bytes([7; 32]));
        assert!(both.check().unwrap_err().message.contains("exactly one"));
        let mut twice = manifest.clone();
        twice.storage_uses.push(twice.storage_uses[0].clone());
        assert!(twice.check().unwrap_err().message.contains("used twice"));
        let mut v3 = manifest.clone();
        v3.format_version = 1;
        assert!(v3.check().unwrap_err().message.contains("saved v3 route"));
        let mut missing_query = manifest;
        missing_query.modules[0].items.clear();
        assert_eq!(missing_query.check().unwrap_err().to_string(), "refusal: the entry module must declare item query");
    }

    /// The generated diagnostic-query example path (`../../storages/<name>/verus-storage.json` from
    /// `diagnostic-queries/<i>/`) resolves; absolute paths and paths leaving the workspace are refused.
    #[test]
    fn workspace_storage_uses_resolve_inside_the_workspace() {
        let scratch = PathBuf::from(std::env::var("TMPDIR").expect("TMPDIR (scratch)")).join(format!("storage-use-paths-{}", std::process::id()));
        let workspace = scratch.join("author");
        let manifest_dir = workspace.join("diagnostic-queries/0");
        fs::create_dir_all(&manifest_dir).unwrap();
        fs::create_dir_all(workspace.join("storages/by_day")).unwrap();
        fs::write(workspace.join("storages/by_day/verus-storage.json"), "{}").unwrap();
        fs::write(scratch.join("outside.json"), "{}").unwrap();
        let workspace = workspace.canonicalize().unwrap();
        let manifest_dir = manifest_dir.canonicalize().unwrap();

        let resolved = workspace_storage_manifest(&workspace, &manifest_dir, Path::new("../../storages/by_day/verus-storage.json")).unwrap();
        assert_eq!(resolved.strip_prefix(&workspace).unwrap(), Path::new("storages/by_day/verus-storage.json"));
        let escape = workspace_storage_manifest(&workspace, &manifest_dir, Path::new("../../../outside.json")).unwrap_err();
        assert!(escape.message.contains("escapes the author workspace"), "{escape}");
        let absolute = workspace.join("storages/by_day/verus-storage.json");
        assert!(workspace_storage_manifest(&workspace, &manifest_dir, &absolute).unwrap_err().message.contains("relative"));
        fs::remove_dir_all(&scratch).unwrap();
    }
}
