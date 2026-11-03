//! Freeze of a storage candidate: the author's `verus-storage.json` and its two author roots become an immutable
//! storage crate whose framework files are a fresh generation (`storage_crate_files` with the storage shim) and whose
//! author files were scanned with the central source rule (`freeze_author_crate`).
//!
//! The freeze checks, in order: manifest schema and completeness, path containment, the stored columns against the
//! dataset schema, the author roots, the central source scan of every author file (inside `freeze_author_crate`), and
//! that the manifest declares every author file once. Declared items are checked against Verus's own output after the
//! whole-crate run (`storage::build`).

use super::manifest::{StorageManifest, StorageModule, StorageModuleRole, derived_module};
use crate::controller::author::resolve_candidate_manifest;
use crate::controller::records::write_new_json;
use crate::query::candidate::{CompilerChoice, inside};
use crate::query::compile::{DeclaredModule, module_path};
use gendb_frontend::ast::TableDef;
use gendb_artifacts::ObjectStore;
use gendb_artifacts::verus::{VerusDerivationSourceV1, VerusDerivationV1};
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::storage::{CandidateDerivation, candidate_framework_files};
use gendb_verification::obligations::{DeclaredSource, StorageName};
use gendb_verification::verus::{AuthorRoot, FrameworkSource, FreezeError, FrozenCrate, freeze_author_crate};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

/// One declared author file of a frozen storage crate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenStorageModule {
    /// Relative to the crate's `src/`.
    pub file: String,
    pub role: StorageModuleRole,
    pub items: Vec<String>,
    /// The frozen source file (compared byte for byte by unchanged-resubmission detection).
    pub source: PathBuf,
    /// Derived (the manifest listed no modules): every function Verus reports in this module is one of its items
    /// (`storage::build`), in addition to `items`.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub items_from_verus: bool,
}

/// `storage.json` of a frozen storage candidate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenStorage {
    pub manifest: StorageManifest,
    pub declaration: DeclaredSource,
    pub compiler: CompilerChoice,
    pub modules: Vec<FrozenStorageModule>,
    /// Author files relative to `src/`, sorted.
    pub author_files: Vec<String>,
    /// Framework files relative to `src/`, in generation order.
    pub framework_files: Vec<String>,
    /// The admitted storages it is built from (`manifest.built_from`, resolved to its use order and extended index).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub derivation: Option<VerusDerivationV1>,
}

impl FrozenStorage {
    pub fn name(&self) -> Result<StorageName, AdmissionError> {
        self.manifest.storage_name()
    }

    /// The frozen crate of this storage under its freeze directory (`<frozen_dir>/crate`).
    pub fn frozen_crate(&self, frozen_dir: &Path) -> FrozenCrate {
        FrozenCrate::from_recorded_author_files(frozen_dir.join("crate"), self.author_files.clone(), self.framework_files.clone())
    }

    /// Every file of the frozen crate (framework and author), relative to `src/`, as frozen.
    pub fn crate_files(&self, frozen_dir: &Path) -> Result<Vec<FrameworkSource>, AdmissionError> {
        let src = frozen_dir.join("crate/src");
        self.framework_files
            .iter()
            .chain(&self.author_files)
            .map(|path| Ok(FrameworkSource { path: path.clone(), text: fs::read_to_string(src.join(path)).map_err(AdmissionError::tool)? }))
            .collect()
    }

    /// The interface files (`stores/<name>/interface/**`) as frozen: the text query crates copy.
    pub fn interface_files(&self, frozen_dir: &Path) -> Result<Vec<FrameworkSource>, AdmissionError> {
        let prefix = format!("stores/{}/interface/", self.manifest.name);
        self.author_files
            .iter()
            .filter(|path| path.starts_with(&prefix))
            .map(|path| {
                let text = fs::read_to_string(frozen_dir.join("crate/src").join(path)).map_err(AdmissionError::tool)?;
                Ok(FrameworkSource { path: path.clone(), text })
            })
            .collect()
    }

    /// The admitted sources of a derived storage with their checked builds' files, read from the library.
    pub fn candidate_derivation(&self, store: &ObjectStore) -> Result<Option<CandidateDerivation>, AdmissionError> {
        self.derivation.as_ref().map(|d| resolve_derivation(store, d)).transpose()
    }

    /// The declared modules in the form the Verus item check takes, with the items of derived modules completed from
    /// the whole-crate run's report (`verus_stdout`, its `--output-json`): every function Verus reports directly in the
    /// module (not in a child module of another author file).
    pub fn declared_modules(&self, verus_stdout: &str) -> Result<Vec<DeclaredModule>, AdmissionError> {
        let reported: Vec<String> = match self.modules.iter().any(|m| m.items_from_verus) {
            true => {
                let output: Value = serde_json::from_str(verus_stdout.trim()).map_err(AdmissionError::tool)?;
                output["func-details"].as_object().map(|o| o.keys().cloned().collect()).unwrap_or_default()
            }
            false => vec![],
        };
        let paths: Vec<String> = self.modules.iter().map(|m| module_path(&m.file)).collect::<Result<_, _>>()?;
        let prefix = format!("{}::", gendb_verification::obligations::STORAGE_CRATE_NAME);
        self.modules
            .iter()
            .zip(&paths)
            .map(|(m, path)| {
                let mut items = m.items.clone();
                if m.items_from_verus {
                    let own = format!("{prefix}{path}::");
                    for full in &reported {
                        let Some(rest) = full.strip_prefix(&own) else { continue };
                        let first = rest.split("::").next().unwrap_or(rest);
                        let in_child = paths.iter().any(|other| *other == format!("{path}::{first}"));
                        if !in_child && !items.iter().any(|i| i == rest) {
                            items.push(rest.to_string());
                        }
                    }
                }
                Ok(DeclaredModule { file: m.file.clone(), role: json!(m.role).as_str().unwrap_or_default().to_string(), items })
            })
            .collect()
    }

    /// Identity of the author's sources, stored columns and compiler choice: two freezes with equal keys build the
    /// same checked storage (its framework files are fixed by name, declaration and schema). Used only to reuse a
    /// checked build within one session.
    pub fn source_key(&self, frozen_dir: &Path) -> Result<Vec<u8>, AdmissionError> {
        let mut key = serde_json::to_vec(&(&self.manifest.name, &self.declaration, &self.compiler)).map_err(AdmissionError::tool)?;
        for file in &self.author_files {
            key.extend(file.as_bytes());
            key.push(0);
            key.extend(fs::read(frozen_dir.join("crate/src").join(file)).map_err(AdmissionError::tool)?);
            key.push(0);
        }
        Ok(key)
    }
}

/// The framework files of a storage crate: the fresh generation for this name, declaration, opt-in
/// (`uses_declared_constraints`: storage entry v2 over the run's declared constraints) and derivation (built from
/// admitted storages: the derived entry, the sources' interfaces), with the shim of its kind.
pub fn storage_framework(
    schema: &[TableDef],
    name: &StorageName,
    declaration: &DeclaredSource,
    uses_declared_constraints: bool,
    derivation: Option<&CandidateDerivation>,
) -> Result<Vec<FrameworkSource>, AdmissionError> {
    candidate_framework_files(schema, name, declaration, uses_declared_constraints, derivation)
}

/// The derivation of a manifest's `built_from` (`None` without it): each source an admitted package of its name, in
/// use order, with the extended source's index.
pub fn manifest_derivation(store: Option<&ObjectStore>, manifest: &StorageManifest) -> Result<Option<VerusDerivationV1>, AdmissionError> {
    let Some(built_from) = &manifest.built_from else { return Ok(None) };
    let store = store.ok_or_else(|| AdmissionError::missing_input("built_from needs the library of admitted storages"))?;
    let derivation = VerusDerivationV1 {
        sources: built_from.sources.iter().map(|s| VerusDerivationSourceV1 { name: s.name.clone(), package: s.admitted }).collect(),
        extends: built_from.extends_index()?,
    };
    resolve_derivation(store, &derivation)?;
    Ok(Some(derivation))
}

/// The sources of `derivation` (if any) with their checked builds' files.
pub fn manifest_derivation_of(store: &ObjectStore, derivation: Option<&VerusDerivationV1>) -> Result<Option<CandidateDerivation>, AdmissionError> {
    derivation.map(|d| resolve_derivation(store, d)).transpose()
}

/// The sources of `derivation` with their checked builds' files.
fn resolve_derivation(store: &ObjectStore, derivation: &VerusDerivationV1) -> Result<CandidateDerivation, AdmissionError> {
    let sources = derivation.sources.iter().map(|s| CandidateDerivation::source(store, &s.name, s.package)).collect::<Result<_, _>>()?;
    Ok(CandidateDerivation { sources, extends: derivation.extends })
}

/// Read and check the manifest `manifest` (workspace-relative or absolute inside `workspace`): `(manifest, crate
/// directory)`.
pub fn read_manifest(workspace: &Path, manifest: &Path) -> Result<(StorageManifest, PathBuf), AdmissionError> {
    let workspace = workspace.canonicalize().map_err(AdmissionError::tool)?;
    let (path, _) = resolve_candidate_manifest(&workspace, manifest).map_err(|e| AdmissionError::missing_input(format!("storage manifest {}: {e}", manifest.display())))?;
    let bytes = fs::read(&path).map_err(|e| AdmissionError::missing_input(format!("{}: {e}", path.display())))?;
    let parsed: StorageManifest = serde_json::from_slice(&bytes).map_err(|e| AdmissionError::refusal(format!("verus-storage manifest: {e}")))?;
    parsed.check()?;
    let base = path.parent().ok_or_else(|| AdmissionError::missing_input("manifest directory absent"))?;
    let crate_dir = inside(base, Path::new(&parsed.crate_dir))?;
    if !crate_dir.starts_with(&workspace) {
        return Err(AdmissionError::refusal("crate_dir must be inside the author workspace"));
    }
    Ok((parsed, crate_dir))
}

/// Write the framework files of a crate into the author's workspace crate (read-only), so the author can run the
/// pinned `rust_verify` directly. Returns the files whose earlier workspace copy differed (they were rewritten; freezes
/// never read workspace framework copies).
pub fn write_workspace_framework(crate_dir: &Path, framework: &[FrameworkSource]) -> Result<Vec<String>, AdmissionError> {
    let mut rewritten = vec![];
    for f in framework {
        let path = crate_dir.join("src").join(&f.path);
        if path.exists() && fs::read(&path).map_err(AdmissionError::tool)? != f.text.as_bytes() {
            rewritten.push(f.path.clone());
        }
        crate::storage::catalog::write_read_only(&path, &f.text)?;
    }
    Ok(rewritten)
}

/// Generate the crate of the storage manifest `manifest` (workspace-relative) in the author workspace: its framework
/// files (read-only, a fresh generation for its name, declaration and opt-in) and its two author root directories when
/// absent. Author files are never written. Returns the crate's `src/` and whether both author roots already had their
/// `mod.rs`.
pub fn scaffold_storage_crate(workspace: &Path, manifest: &Path, schema: &[TableDef], store: Option<&ObjectStore>) -> Result<(PathBuf, bool), AdmissionError> {
    let (manifest, crate_dir) = read_manifest(workspace, manifest)?;
    let name = manifest.storage_name()?;
    let declaration = manifest.declaration(schema)?;
    let derivation = match manifest_derivation(store, &manifest)? {
        Some(d) => Some(resolve_derivation(store.expect("checked by manifest_derivation"), &d)?),
        None => None,
    };
    write_workspace_framework(&crate_dir, &storage_framework(schema, &name, &declaration, manifest.uses_declared_constraints, derivation.as_ref())?)?;
    let src = crate_dir.join("src");
    let (interface, builder) = manifest.author_roots();
    let mut complete = true;
    for root in [interface, builder] {
        fs::create_dir_all(src.join(&root)).map_err(AdmissionError::tool)?;
        complete &= src.join(&root).join("mod.rs").is_file();
    }
    Ok((src, complete))
}

/// Freeze the storage candidate of `manifest` from `workspace` into the fresh directory `frozen_dir` (`crate/`,
/// `storage.json`, `manifest.json`). `schema`: the dataset schema (`doc.tables`); `store`: the library, needed to resolve
/// the admitted sources of a manifest with `built_from`, each replaced by its current version in `substitutes` (a stale
/// source's re-verification, `storage::reverify`).
pub fn freeze_storage(
    workspace: &Path,
    manifest: &Path,
    frozen_dir: &Path,
    schema: &[TableDef],
    store: Option<&ObjectStore>,
    substitutes: &BTreeMap<gendb_artifacts::ContentId, gendb_artifacts::ContentId>,
) -> Result<FrozenStorage, AdmissionError> {
    let (manifest, crate_dir) = read_manifest(workspace, manifest)?;
    let name = manifest.storage_name()?;
    let declaration = manifest.declaration(schema)?;
    let mut derivation = manifest_derivation(store, &manifest)?;
    for source in derivation.iter_mut().flat_map(|d| d.sources.iter_mut()) {
        if let Some(current) = substitutes.get(&source.package) {
            source.package = *current;
        }
    }
    let candidate_derivation = match (&derivation, store) {
        (Some(d), Some(store)) => Some(resolve_derivation(store, d)?),
        _ => None,
    };
    let framework = storage_framework(schema, &name, &declaration, manifest.uses_declared_constraints, candidate_derivation.as_ref())?;
    let (interface_root, builder_root) = manifest.author_roots();
    let (interface_dir, builder_dir) = (crate_dir.join("src").join(&interface_root), crate_dir.join("src").join(&builder_root));
    for dir in [&interface_dir, &builder_dir] {
        if !dir.is_dir() {
            return Err(AdmissionError::missing_input(format!("{} is not a directory", dir.display())));
        }
    }
    fs::create_dir(frozen_dir).map_err(AdmissionError::tool)?;
    let roots = [AuthorRoot { crate_directory: &interface_root, source: &interface_dir }, AuthorRoot { crate_directory: &builder_root, source: &builder_dir }];
    let krate = freeze_author_crate(&framework, &roots, &frozen_dir.join("crate")).map_err(freeze_error)?;
    let modules = declared_storage_modules(&manifest, &krate)?;
    let frozen = FrozenStorage {
        compiler: manifest.compiler.clone().unwrap_or_default(),
        manifest,
        declaration,
        modules,
        author_files: krate.author_files.clone(),
        framework_files: krate.framework_files.clone(),
        derivation,
    };
    write_new_json(&frozen_dir.join("storage.json"), &frozen).map_err(AdmissionError::tool)?;
    Ok(frozen)
}

/// A freeze refusal (source rule or file set) or a framework failure, as an admission error.
pub fn freeze_error(error: FreezeError) -> AdmissionError {
    match error {
        FreezeError::Refused { findings } => AdmissionError::refusal(format!("refusal-list findings {}", json!(findings))),
        FreezeError::Framework { message } => AdmissionError::tool(message),
    }
}

/// One derived module per author file of `krate` (items from Verus), for a manifest without modules.
pub fn derived_modules(manifest: &StorageManifest, krate: &FrozenCrate) -> Vec<FrozenStorageModule> {
    krate
        .author_files
        .iter()
        .map(|file| {
            let m = derived_module(&manifest.name, file);
            FrozenStorageModule { source: krate.root.join("src").join(&m.file), file: m.file, role: m.role, items: m.items, items_from_verus: true }
        })
        .collect()
}

/// The manifest's modules, each an author file of the frozen crate, declared exactly once, covering every author file;
/// or, when the manifest lists none, one derived module per author file ([`derived_module`], items from Verus).
fn declared_storage_modules(manifest: &StorageManifest, krate: &FrozenCrate) -> Result<Vec<FrozenStorageModule>, AdmissionError> {
    let derived = manifest.modules.is_empty();
    let modules: Vec<StorageModule> = if derived {
        krate.author_files.iter().map(|file| derived_module(&manifest.name, file)).collect()
    } else {
        manifest.modules.clone()
    };
    let declared: BTreeSet<&str> = modules.iter().map(|m| m.file.as_str()).collect();
    if let Some(missing) = modules.iter().find(|m| !krate.author_files.contains(&m.file)) {
        return Err(AdmissionError::missing_input(format!("declared module {} is not an author file of the storage crate", missing.file)));
    }
    let undeclared: Vec<&String> = krate.author_files.iter().filter(|f| !declared.contains(f.as_str())).collect();
    if !undeclared.is_empty() {
        return Err(AdmissionError::refusal(format!("author files not declared in the storage manifest: {undeclared:?} (omit modules to derive them from the files)")));
    }
    let (interface, builder) = manifest.author_roots();
    for root in [interface, builder] {
        let root_file = format!("{root}/mod.rs");
        if !krate.author_files.contains(&root_file) {
            return Err(AdmissionError::missing_input(format!("the storage crate has no {root_file}")));
        }
    }
    Ok(modules
        .into_iter()
        .map(|m| FrozenStorageModule { source: krate.root.join("src").join(&m.file), file: m.file, role: m.role, items: m.items, items_from_verus: derived })
        .collect())
}

/// The frozen storage recorded in `frozen_dir`.
pub fn read_frozen_storage(frozen_dir: &Path) -> Result<FrozenStorage, AdmissionError> {
    crate::controller::records::read_json(&frozen_dir.join("storage.json")).map_err(AdmissionError::tool)
}

/// The descriptive record of a storage candidate for authors and admission evidence.
pub fn description(frozen: &FrozenStorage, registered_by: Value) -> Value {
    json!({"name":frozen.manifest.name,"tables":frozen.manifest.tables,"parts":frozen.manifest.parts,"layout":frozen.manifest.layout,
        "data_policy":frozen.manifest.data_policy,"notes":frozen.manifest.notes,"built_from":frozen.manifest.built_from,"registered_by":registered_by})
}
