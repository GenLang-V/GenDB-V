//! Storage packages: publication of a checked storage build, the one build of each stored asset by the stored
//! library, and admission.
//!
//! The steps, in the order the storage tools call them:
//! 1. [`publish_storage`]: the storage crate's one whole-crate verify-and-compile run becomes a build record (admissible
//!    evidence), and its package record names the build, the storage declaration, the interface's dependency closure
//!    (`gendb_verification::obligations::storage_closure`) and the check configuration. The build's framework files
//!    must be exactly a fresh generation of the storage crate (`storage_crate_files` with the storage shim); author
//!    files lie only under `stores/<name>/interface/` and `builder/`. A storage whose manifest opts in
//!    (`uses_declared_constraints`) is checked with the storage entry v2 and records the exact declaration set it
//!    assumes (`assumed_constraints`); without a declaration set in the run it is refused before any build
//!    (`declared_constraints_unavailable`).
//! 2. [`build_storage_asset`]: the asset of the package for the current capture. When its key already has an asset,
//!    that asset is returned and nothing is built (reuse across queries and at final qualification). Otherwise the
//!    **stored library object of the build** runs the builder once, in the worker child, over the stored tables'
//!    declared columns of the current capture, writing its parts straight into the library's asset staging directory;
//!    the complete build is placed as `assets/<key id>` and recorded. So every published asset comes from the checked
//!    artifact itself, never from a library in a run directory, and each key is built once: the key's lock
//!    (`records::lock_storage_asset`) is held from the lookup to the publication, so concurrent sessions and processes
//!    asking for the same key wait and then reuse the one asset; other keys proceed in parallel. A failed build releases
//!    the lock and removes its unplaced staging directory, so a retry builds again; an interrupted publication is
//!    completed or refused as `records::locked_storage_asset` documents, never overwritten.
//!    A storage that is not admitted yet is built the same way by [`build_trial_asset`], but into its session's trial
//!    directory outside the library, publishing nothing; [`promote_trial_asset`] publishes it at registration by
//!    renaming that sealed directory into the library with the record (and id) computed at its build.
//! 3. [`admit_storage`]: the package joins the admitted versions of its name.
//!
//! Every asset build and lookup takes the run's declared constraints ([`run_constraints_digest`]) and refuses a
//! package that assumes another set (`storage_assumes_declared_constraints`, the records' exact-set rule), so a
//! constraint-dependent builder never runs, and its asset is never used, outside the declarations it assumes.
//!
//! Query packages over stored data are admitted by `qualification_v4`, which requires admitted storage packages.

use super::execution::{CandidateRunner, RANGE_CAPACITY, RESERVE_STOP, status_error};
use super::qualification::{entry_assumptions, framework_trusted_items, publish_checked_build, record_error, store_error};
use super::{AdmissionError, FailureClass};
use crate::obligations::{
    author_source_findings, check_storage_composition, declared_constraints_text, derived_storage_crate_files, storage_closure, storage_crate_files,
    storage_entry_of, with_trusted_shim, AssemblyError, DeclaredSource, Derivation, StorageEntry, StorageName, StorageUse, STORAGE_THEOREMS,
};
use crate::verus::{FrameworkSource, VerusToolchain, VERUS_REFUSAL_RULES};
use gendb_artifacts::verus::{
    self as records, BuiltParts, VerusBuildV1, VerusClosureFileV1, VerusDerivationSourceV1, VerusDerivationV1, VerusItemV1, VerusSourceOwnerV1,
    VerusStorageAdmissionV1, VerusStorageAssetV1, VerusStoragePackageV1, VerusStoredTableV1, VerusTcbV1, VerusTrustedItemV1,
};
use gendb_artifacts::asset_directory::remove_build_directory;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::TableDef;
use gendb_runtime::abi::{CallStatus, GENDB_STORAGE_DERIVED_SHIM_SOURCE, GENDB_STORAGE_NULLABLE_SHIM_SOURCE, GENDB_STORAGE_SHIM_SOURCE, MAX_WORKERS};
use gendb_runtime::identity::runtime_build_identity;
use gendb_runtime::worker::{StorageUseInput, TableColumns, WorkerInput, WorkerRequest};
use gendb_storage::import::PreparedSource;
use gendb_storage::versions::CurrentCapture;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

mod flat_asset;
pub use flat_asset::{FLAT_CAPTURE_ASSET_KIND, FLAT_CAPTURE_PARTS, flat_storage_of_build, generated_flat_storage};

/// Gate identity of every storage admission written here.
pub const STORAGE_GATE_IDENTITY: &str = "gendb.verus.storage-admission.v1";
/// Record kind of the evidence of one asset build.
pub const STORAGE_ASSET_BUILD_KIND: &str = "gendb.verus.storage-asset-build.v1";

/// Trusted host items of stored assets, `(id, statement)`, for the TCB records of storage and query packages.
pub const STORAGE_HOST_ITEMS: [(&str, &str); 2] = [
    (
        "storage_asset_publication",
        "gendb_verification::admission::storage::build_storage_asset with gendb_artifacts storage records: the asset of a \
         key is built by the stored library object of the storage package's checked build, in the worker child, over the \
         stored tables' declared columns of the current capture; its parts are written once into the library's asset \
         staging directory and placed by rename as assets/<key id> (directory 0555, files 0444), recorded by a \
         library-relative path; one asset per key; part payload is never hashed or rescanned. The parts of a storage \
         not yet admitted are written once into its session's trial directory outside the library, sealed, and \
         placed by the same rename, with the record computed at their build, only when the storage is registered; \
         a trial directory that is never registered is removed by its session and never enters the library. A storage \
         built from admitted storages that extends a source gets that source asset's part files, unchanged, as hard \
         links before its builder's parts (gendb_storage::io::PartFilesWriter::link_parts_of). An asset of a package whose \
         build compiled byte-identical source files (by content id) with the same toolchain, configuration and codegen \
         options, over the same declaration, tables and admitted sources, as an earlier package's build is that earlier \
         asset's part files as hard links (synthesis::storage::identity; it rests on the trusted compiler compiling equal \
         input equally). Part payload is never copied, hashed or rescanned; linked file lengths are checked against the \
         manifest",
    ),
    (
        "storage_asset_resolution",
        "gendb_storage::versions: every storage use of one execution is resolved against one current capture by \
         (storage package, per stored table: source version, row-order identity, row count). Row-order identities are \
         capture receipt labels: a fresh read of a table's source files gets a new label, a reused capture shares it, and \
         an extension keeps the labels of its base tables under the extension's recorded assumption that unchanged \
         files hold the same rows in the same order (checked: stamps and row counts; not a byte comparison)",
    ),
];

/// The dataset schema a storage is checked over: the schema of the AST documents (`doc.tables`), the DDL they were
/// translated from and the frontend that translated it.
#[derive(Clone, Copy)]
pub struct StorageSchema<'a> {
    pub tables: &'a [TableDef],
    pub ddl: &'a str,
    pub frontend: &'a Value,
}

/// One checked storage crate: its name and declaration, whether its builder assumes the run's declared constraints
/// (the manifest's `uses_declared_constraints`: storage entry v2), the frozen crate (`<root>/src/`) that one
/// whole-crate verify-and-compile run checked, the run record (`VerusRun::record`), and the interface readers with
/// their checked clause text (descriptive).
pub struct StorageCandidate<'a> {
    pub name: &'a StorageName,
    pub declaration: &'a DeclaredSource,
    pub uses_declared_constraints: bool,
    /// The admitted storages it is built from (derived storage entry); `None`: built from source columns.
    pub derivation: Option<&'a CandidateDerivation>,
    pub frozen_root: &'a Path,
    pub verus_run: &'a Value,
    pub readers: Vec<VerusItemV1>,
    /// A fixed flat storage (`obligations::flat_storage`): its author sources must be the generator's output for its
    /// declaration, and its TCB record names the flat asset host item `flat_capture_parts`.
    pub flat: bool,
}

/// One admitted source of a derived storage candidate: its package, declaration, the interface files of its checked
/// build (copied into the derived crate) and every file of that build (for the composition check).
#[derive(Clone, Debug)]
pub struct CandidateSource {
    pub name: StorageName,
    pub package: ContentId,
    pub declaration: DeclaredSource,
    pub interface: Vec<FrameworkSource>,
    pub build_files: Vec<FrameworkSource>,
}

/// The admitted sources of a derived storage candidate and the source it extends (an index into `sources`).
#[derive(Clone, Debug)]
pub struct CandidateDerivation {
    pub sources: Vec<CandidateSource>,
    pub extends: Option<usize>,
}

impl CandidateDerivation {
    /// The admitted source `package` of storage name `name` with its build's files (interface and closure as checked).
    pub fn source(store: &ObjectStore, name: &str, package: ContentId) -> Result<CandidateSource, AdmissionError> {
        let record = records::resolve_admitted_storage(store, package).map_err(|e| AdmissionError::missing_input(format!("source storage {name} ({package}): {e}")))?;
        if record.name != name {
            return Err(AdmissionError::refusal(format!("source storage package {package} is named {}, not {name}", record.name)));
        }
        let declaration: DeclaredSource = serde_json::from_value(record.declaration.clone()).map_err(AdmissionError::tool)?;
        let build = records::storage_build(store, &record).map_err(record_error)?;
        let build_files = build_files(store, &build)?;
        let storage_name = StorageName::new(name).map_err(AdmissionError::refusal)?;
        let interface = build_files.iter().filter(|f| f.path.starts_with(&storage_name.interface_prefix())).cloned().collect();
        Ok(CandidateSource { name: storage_name, package, declaration, interface, build_files })
    }

    /// The sources as crate-assembly storage uses.
    fn uses(&self) -> Vec<StorageUse<'_>> {
        self.sources.iter().map(|s| StorageUse { name: &s.name, declaration: &s.declaration, interface: &s.interface }).collect()
    }

    /// The package record of the derivation.
    fn record(&self) -> VerusDerivationV1 {
        VerusDerivationV1 {
            sources: self.sources.iter().map(|s| VerusDerivationSourceV1 { name: s.name.to_string(), package: s.package }).collect(),
            extends: self.extends,
        }
    }
}

/// Every framework file (with the trusted shim) of the storage crate of `candidate` over `schema`: a fresh generation
/// of its kind (built from source columns, or from admitted storages). A storage built from source columns whose
/// declaration has a nullable column gets the shim that also delivers validity
/// (`GENDB_STORAGE_NULLABLE_SHIM_SOURCE`); every other storage crate the shim it always had.
pub fn candidate_framework_files(schema: &[TableDef], candidate_name: &StorageName, declaration: &DeclaredSource, uses_declared_constraints: bool, derivation: Option<&CandidateDerivation>) -> Result<Vec<FrameworkSource>, AdmissionError> {
    Ok(match derivation {
        None => {
            let shim = if declaration.has_nullable() { GENDB_STORAGE_NULLABLE_SHIM_SOURCE } else { GENDB_STORAGE_SHIM_SOURCE };
            with_trusted_shim(storage_crate_files(schema, candidate_name, declaration, uses_declared_constraints).map_err(assembly_error)?, shim)
        }
        Some(derivation) => {
            let uses = derivation.uses();
            let files = derived_storage_crate_files(schema, candidate_name, declaration, Derivation { sources: &uses, extends: derivation.extends }, uses_declared_constraints)
                .map_err(assembly_error)?;
            with_trusted_shim(files, GENDB_STORAGE_DERIVED_SHIM_SOURCE)
        }
    })
}

/// The records of a published storage package.
#[derive(Clone, Debug)]
pub struct PublishedStorage {
    pub package: ContentId,
    pub build: ContentId,
    pub tcb: ContentId,
    pub implementation: ContentId,
    pub record: VerusStoragePackageV1,
}

/// Publish the build and package records of a checked storage crate in `store` (see the module documentation, step 1).
/// `clause_text(source, item)`: the lexical `requires`/`ensures` extractor for the recorded entry items.
pub fn publish_storage(
    store: &ObjectStore,
    schema: StorageSchema<'_>,
    candidate: &StorageCandidate<'_>,
    clause_text: super::qualification::ClauseText<'_>,
) -> Result<PublishedStorage, AdmissionError> {
    let entry = storage_entry_of(candidate.derivation.is_some(), candidate.uses_declared_constraints);
    let expected = candidate_framework_files(schema.tables, candidate.name, candidate.declaration, candidate.uses_declared_constraints, candidate.derivation)?;
    let interface = candidate.name.interface_prefix();
    let is_author = |path: &str| path.starts_with(&interface) || path.starts_with("builder/");
    let sources = crate_sources(candidate.frozen_root, &is_author)?;
    let toolchain = VerusToolchain::from_env().map_err(AdmissionError::tool)?;
    let host_items: &[(&str, &str)] = if candidate.flat { &[FLAT_CAPTURE_PARTS] } else { &[] };
    let tcb = store.put(1, records::VERUS_TCB_KIND, &storage_tcb_record_with(&entry, host_items)?).map_err(store_error)?;
    let build = publish_checked_build(store, &toolchain, tcb, candidate.frozen_root, sources, candidate.verus_run)?;
    let build_record: VerusBuildV1 = store.read(build).and_then(|o| o.decode()).map_err(store_error)?;
    refuse_unscanned_author_sources(store, &build_record)?;
    if candidate.flat {
        if candidate.derivation.is_some() || candidate.uses_declared_constraints {
            return Err(AdmissionError::refusal("flat_storage_not_generated: a flat storage is built from source columns and assumes no declared constraint"));
        }
        flat_storage_of_build(store, &build_record, &serde_json::to_value(candidate.declaration).map_err(AdmissionError::tool)?)?;
    }
    if let Some(derivation) = candidate.derivation {
        // Each source's propositions must mean the same here as in its own checked build (`storage_spec_identity`).
        let files = build_files(store, &build_record)?;
        for source in &derivation.sources {
            check_storage_composition(&source.build_files, &files, &source.name)
                .map_err(|e| AdmissionError::refusal(format!("storage composition of source {}: {e}", source.name)))?;
        }
    }
    let closure = closure_files(store, &build_record, candidate.name)?;
    // Entry v2: the exact declaration set the builder assumed, the generated module of the run's schema (its blob).
    let assumed_constraints = match expected.iter().find(|f| f.path == records::CONSTRAINTS_MODULE_PATH) {
        Some(module) => Some(store.put_blob(module.text.as_bytes()).map_err(store_error)?),
        None => None,
    };
    if let Some(derivation) = candidate.derivation {
        // A source proved under the declared constraints holds only on databases that satisfy them, so its derived
        // storage must assume the same declarations (and then applies only to runs with exactly that set).
        for source in &derivation.sources {
            let record = records::resolve_admitted_storage(store, source.package).map_err(record_error)?;
            if record.assumed_constraints.is_some() && record.assumed_constraints != assumed_constraints {
                return Err(AdmissionError::refusal(format!(
                    "derived_storage_constraints_not_inherited: source {} assumes the declared integrity constraints; a storage built from it must assume the same declarations (verus-storage.json uses_declared_constraints: true)",
                    source.name
                )));
            }
        }
    }
    let package = VerusStoragePackageV1 {
        name: candidate.name.to_string(),
        build,
        entry_identity: entry.identity.into(),
        assumed_constraints,
        tables: stored_tables(candidate.declaration),
        declaration: serde_json::to_value(candidate.declaration).map_err(AdmissionError::tool)?,
        schema_ddl: store.put_blob(schema.ddl.as_bytes()).map_err(store_error)?,
        frontend: schema.frontend.clone(),
        closure,
        configuration: build_record.check_configuration().map_err(record_error)?,
        readers: candidate.readers.clone(),
        theorems: STORAGE_THEOREMS.iter().map(|t| t.to_string()).collect(),
        workers: (1, MAX_WORKERS as u32),
        tcb,
        derived_from: candidate.derivation.map(CandidateDerivation::record),
    };
    let expected: Vec<(&str, &str)> = expected.iter().map(|f| (f.path.as_str(), f.text.as_str())).collect();
    let id = records::publish_storage_package(store, &package, &expected).map_err(record_error)?;
    let entry_items = entry
        .recorded_items
        .iter()
        .map(|name| {
            let (requires, ensures) = clause_text(entry.source, name)
                .ok_or_else(|| AdmissionError::tool(format!("{}: clause text of {name} absent", entry.name)))?;
            Ok(VerusItemV1 { path: format!("{}::gendb_entry::{name}", crate::obligations::STORAGE_CRATE_NAME), requires, ensures })
        })
        .collect::<Result<Vec<_>, AdmissionError>>()?;
    let implementation = store
        .put(1, records::VERUS_IMPLEMENTATION_KIND, &records::VerusImplementationV1 {
            build,
            module: format!("stores/{} (storage interface and builder{})", candidate.name, if candidate.derivation.is_some() { ", built from admitted storages" } else { "" }),
            operations: vec![],
            items: entry_items.into_iter().chain(candidate.readers.iter().cloned()).collect(),
        })
        .map_err(store_error)?;
    Ok(PublishedStorage { package: id, build, tcb, implementation, record: package })
}

/// An assembly failure with its author-contract class (`declared_constraints_unavailable` is a refusal).
fn assembly_error(error: AssemblyError) -> AdmissionError {
    let class = FailureClass::ALL.into_iter().find(|c| c.name() == error.failure_class()).unwrap_or(FailureClass::ToolFailure);
    AdmissionError::new(class, error)
}

/// The run's declared integrity constraints as the storage tools compare them with a package's `assumed_constraints`:
/// the identity (`declared_constraints_digest`) of the generated `gendb_constraints.rs` of the dataset schema `schema`
/// (a document's `tables`), `None` when the run declares none.
pub fn run_constraints_digest(schema: &[TableDef]) -> Result<Option<ContentId>, AdmissionError> {
    let text = declared_constraints_text(schema).map_err(assembly_error)?;
    Ok(text.as_deref().map(records::declared_constraints_digest))
}

/// The exact-set rule (`VerusStoragePackageV1::check_declared_constraints`) as an admission refusal.
pub fn check_storage_assumptions(package: &VerusStoragePackageV1, declared: Option<ContentId>) -> Result<(), AdmissionError> {
    package.check_declared_constraints(declared).map_err(AdmissionError::refusal)
}

/// The asset of a storage package for one capture.
#[derive(Clone, Debug)]
pub struct StorageAsset {
    pub id: ContentId,
    pub asset: VerusStorageAssetV1,
    /// The asset's parts directory in the library.
    pub directory: PathBuf,
    /// `false` when the key already had an asset and nothing was built.
    pub built: bool,
}

/// The asset of storage package `package_id` for `capture` (step 2 of the module documentation): the published one,
/// or one build by the package's stored library over `input` (the stored tables' declared columns of that capture,
/// [`storage_input`]) with `workers` workers, evidence of the child run under `evidence` (created only when this call
/// builds). `declared`: the run's declared constraints ([`run_constraints_digest`]); a package assuming another set is
/// refused before anything is looked up or built. Blocks while another caller holds the same key's lock.
/// [`lookup_storage_asset`] and [`AssetBuildSlot::build`] are its two steps, for callers that decide something between
/// them (free space).
#[allow(clippy::too_many_arguments)]
pub fn build_storage_asset(
    store: &ObjectStore,
    runner: &CandidateRunner,
    package_id: ContentId,
    capture: &CurrentCapture,
    declared: Option<ContentId>,
    input: WorkerInput,
    workers: u32,
    evidence: &Path,
) -> Result<StorageAsset, AdmissionError> {
    match lookup_storage_asset(store, package_id, capture, declared)? {
        AssetLookup::Published(asset) => Ok(asset),
        AssetLookup::Absent(slot) => slot.build(store, runner, input, workers, evidence),
    }
}

/// The key of a package for a capture: its published asset, or the key's lock held for its one build.
pub enum AssetLookup {
    Published(StorageAsset),
    Absent(AssetBuildSlot),
}

/// The right and duty to build one key's asset: the key's lock is held until [`AssetBuildSlot::build`] publishes or
/// fails (or the slot is dropped, building nothing).
pub struct AssetBuildSlot {
    package_id: ContentId,
    package: VerusStoragePackageV1,
    lock: records::StorageAssetLock,
    /// Bytes of this key's leftover staged builds (failed or crashed, never placed) removed at the lookup.
    pub stale_staging_bytes: u64,
}

impl AssetBuildSlot {
    pub fn key(&self) -> &records::VerusStorageAssetKeyV1 {
        self.lock.key()
    }

    pub fn package(&self) -> &VerusStoragePackageV1 {
        &self.package
    }

    /// Build the key's asset once by the package's stored library and publish it (see [`build_storage_asset`]). A
    /// failed build removes its staged directory; its error is kept, and names `insufficient_storage` only when the
    /// failure itself reports that the parts writer stopped at the free-space reserve or that the device or quota is
    /// full ([`disk_full_evidence`]).
    pub fn build(self, store: &ObjectStore, runner: &CandidateRunner, input: WorkerInput, workers: u32, evidence: &Path) -> Result<StorageAsset, AdmissionError> {
        let staged = store.fresh_asset_staging_directory(self.lock.asset_name()).map_err(store_error)?;
        let build = BuilderRun { package_id: self.package_id, package: &self.package, key: self.lock.key() };
        let (built, wall_ns, evidence_id) = build.run(store, runner, input, workers, &staged, evidence)?;
        let (id, asset) = records::publish_storage_asset(store, &self.lock, &staged, built, wall_ns, evidence_id).map_err(record_error)?;
        let directory = records::storage_asset_directory(store, &asset).map_err(record_error)?;
        Ok(StorageAsset { id, asset, directory, built: true })
    }
}

/// One child run of a storage package's stored library as the builder of one key.
struct BuilderRun<'a> {
    package_id: ContentId,
    package: &'a VerusStoragePackageV1,
    key: &'a records::VerusStorageAssetKeyV1,
}

impl BuilderRun<'_> {
    /// Build into `output` (created by the builder) and store the build record: `(parts, wall ns, build record id)`.
    /// On failure the partial `output` is removed and the error carries the disk facts ([`disk_full_evidence`]).
    fn run(&self, store: &ObjectStore, runner: &CandidateRunner, input: WorkerInput, workers: u32, output: &Path, evidence: &Path) -> Result<(BuiltParts, u64, ContentId), AdmissionError> {
        self.run_child(store, runner, input, workers, output, evidence).or_else(|error| {
            let free = free_bytes_at(output.parent().unwrap_or(output));
            let removed = remove_build_directory(output).map_err(store_error)?;
            Err(disk_full_evidence(error, free, removed))
        })
    }

    fn run_child(&self, store: &ObjectStore, runner: &CandidateRunner, input: WorkerInput, workers: u32, output: &Path, evidence: &Path) -> Result<(BuiltParts, u64, ContentId), AdmissionError> {
        let build = records::check_build_evidence(store, self.package.build).map_err(record_error)?;
        let library = records::library_path(store, &build).map_err(record_error)?;
        let request = WorkerRequest::for_storage_build(&library, input.clone(), output, workers, RANGE_CAPACITY);
        let result = runner.run(evidence, &request, None)?;
        let observation = result.observations.first().ok_or_else(|| AdmissionError::tool("storage build returned no call"))?;
        let status = observation.outcome.status;
        let manifest = match (status, &result.parts) {
            (CallStatus::Ok, Some(manifest)) => manifest.clone(),
            (CallStatus::InvalidInput, _) => {
                return Err(AdmissionError::tool(format!(
                    "the capture's columns are outside the storage's declared column domain (decided by the fixed storage entry before the builder); evidence {}",
                    evidence.display()
                )));
            }
            _ => return Err(status_error(Some(status), "storage builder", evidence)),
        };
        if matches!(input, WorkerInput::Tables { .. }) {
            check_built_rows(self.package, self.key, &result.column_rows)?;
        }
        let parts = manifest.parts.iter().map(|(elem, len)| Ok((element_name(elem)?, *len))).collect::<Result<Vec<_>, AdmissionError>>()?;
        let wall_ns = observation.outcome.usage.wall_ns;
        let record = json!({"storage_package":self.package_id,"build":self.package.build,"library_object":library,"key":self.key,
            "input":input,"column_rows":result.column_rows,"call":observation,"parts":manifest,"evidence":evidence,
            "scope":"one build of the storage package's stored, checked library over the declared columns of the capture named by the key"});
        let evidence_id = store.put(1, STORAGE_ASSET_BUILD_KIND, &record).map_err(store_error)?;
        let built = BuiltParts {
            format_version: manifest.format_version,
            byte_order: manifest.byte_order.map(|order| format!("{order:?}").to_lowercase()).unwrap_or_else(|| "host".into()),
            parts,
            storage_bytes: manifest.storage_bytes,
        };
        Ok((built, wall_ns, evidence_id))
    }
}

/// The asset of a storage that is not admitted yet, built outside the library: its sealed parts directory in the
/// session's trial directory and exactly the record (and id) its publication at registration stores.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrialAsset {
    pub id: ContentId,
    pub asset: VerusStorageAssetV1,
    /// `<trial root>/<key id>` (absolute).
    pub directory: PathBuf,
}

/// Build the asset of `package_id` for `capture` by the package's stored library into `<trial_root>/<key id>`
/// (written as `<key id>.building`, a leftover of which is removed first, then sealed 0555/0444 and renamed), with
/// its build record in the library and nothing published. The trial directory must not exist: its owner decides
/// whether an existing one is reused (see `synthesis::query::assets`). `declared`: the run's declared constraints; a
/// package assuming another set is refused before anything is built.
#[allow(clippy::too_many_arguments)]
pub fn build_trial_asset(
    store: &ObjectStore,
    runner: &CandidateRunner,
    package_id: ContentId,
    capture: &CurrentCapture,
    declared: Option<ContentId>,
    input: WorkerInput,
    workers: u32,
    trial_root: &Path,
    evidence: &Path,
) -> Result<TrialAsset, AdmissionError> {
    let package: VerusStoragePackageV1 = store.read(package_id).and_then(|o| o.decode()).map_err(store_error)?;
    check_storage_assumptions(&package, declared)?;
    let key = capture.asset_key(package_id, &package).map_err(AdmissionError::missing_input)?;
    let name = key.identity().map_err(AdmissionError::tool)?.to_hex();
    let (building, directory) = (trial_root.join(format!("{name}.building")), trial_root.join(&name));
    if directory.exists() {
        return Err(AdmissionError::tool(format!("trial asset directory {} already exists", directory.display())));
    }
    std::fs::create_dir_all(trial_root).map_err(|e| AdmissionError::tool(format!("{}: {e}", trial_root.display())))?;
    remove_build_directory(&building).map_err(store_error)?;
    let (built, wall_ns, evidence_id) = BuilderRun { package_id, package: &package, key: &key }.run(store, runner, input, workers, &building, evidence)?;
    let asset = records::storage_asset_record(key, built, wall_ns, evidence_id).map_err(record_error)?;
    let id = records::storage_asset_id(&asset).map_err(record_error)?;
    std::fs::set_permissions(&building, std::fs::Permissions::from_mode(0o555)).map_err(|e| AdmissionError::tool(format!("{}: {e}", building.display())))?;
    std::fs::rename(&building, &directory).map_err(|e| AdmissionError::tool(format!("{}: {e}", directory.display())))?;
    Ok(TrialAsset { id, asset, directory })
}

/// The parts of one unverified diagnostic storage build (`storage_build` with `verification: "not_run"`).
#[derive(Clone, Debug, Serialize)]
pub struct DiagnosticBuild {
    pub parts: gendb_storage::io::PartsManifest,
    pub build_wall_ns: u64,
    pub column_rows: Vec<u64>,
}

/// Run the builder of an UNVERIFIED storage library (compiled with `rust_verify --no-verify`) once over `input` into
/// the new directory `output`, outside the library and with no record in it: never an asset, never admissible. A
/// failed build removes its partial directory (with the disk facts, as for asset builds).
pub fn build_diagnostic_parts(runner: &CandidateRunner, library: &Path, input: WorkerInput, workers: u32, output: &Path, evidence: &Path) -> Result<DiagnosticBuild, AdmissionError> {
    let run = || -> Result<DiagnosticBuild, AdmissionError> {
        let request = WorkerRequest::for_storage_build(library, input, output, workers, RANGE_CAPACITY);
        let result = runner.run(evidence, &request, None)?;
        let observation = result.observations.first().ok_or_else(|| AdmissionError::tool("storage build returned no call"))?;
        match (observation.outcome.status, &result.parts) {
            (CallStatus::Ok, Some(parts)) => Ok(DiagnosticBuild { parts: parts.clone(), build_wall_ns: observation.outcome.usage.wall_ns, column_rows: result.column_rows.clone() }),
            (status, _) => Err(status_error(Some(status), "unverified storage builder", evidence)),
        }
    };
    run().or_else(|error| {
        let free = free_bytes_at(output.parent().unwrap_or(output));
        let removed = remove_build_directory(output).map_err(store_error)?;
        Err(disk_full_evidence(error, free, removed))
    })
}

/// The builder input of a storage `declaration` over a prepared capture (as [`storage_input`] for a package): its
/// stored tables' declared columns, persisted as the view archive `directory` unless it exists.
pub fn declared_storage_input(source: &PreparedSource, declaration: &DeclaredSource, directory: &Path) -> Result<WorkerInput, AdmissionError> {
    let tables = stored_tables(declaration);
    let projection: Vec<(String, Vec<usize>)> = tables.iter().map(|t| (t.table.clone(), t.ordinals.clone())).collect();
    write_storage_input(source, &projection, "the declared storage", directory)
}

/// Record kind of the evidence of an asset made by reusing the parts of an asset of equal builder identity.
pub const STORAGE_ASSET_REUSE_KIND: &str = "gendb.verus.storage-asset-reuse.v1";

/// The trial asset of `package_id` for `capture` made from the committed parts directory `source_directory` of an asset
/// whose package has the same builder identity (`reuse`: the evidence naming both and the identity), by hard links to
/// its part files in `<trial_root>/<key id>` (written as `<key id>.building`, sealed and renamed as a built trial):
/// nothing is rebuilt, copied or read. Its record names the reuse evidence; `build_wall_ns` is the source asset's.
pub fn link_trial_asset(
    store: &ObjectStore,
    package_id: ContentId,
    capture: &CurrentCapture,
    declared: Option<ContentId>,
    source_directory: &Path,
    source_wall_ns: u64,
    reuse: Value,
    trial_root: &Path,
) -> Result<TrialAsset, AdmissionError> {
    let package: VerusStoragePackageV1 = store.read(package_id).and_then(|o| o.decode()).map_err(store_error)?;
    check_storage_assumptions(&package, declared)?;
    let key = capture.asset_key(package_id, &package).map_err(AdmissionError::missing_input)?;
    let name = key.identity().map_err(AdmissionError::tool)?.to_hex();
    let (building, directory) = (trial_root.join(format!("{name}.building")), trial_root.join(&name));
    if directory.exists() {
        return Err(AdmissionError::tool(format!("trial asset directory {} already exists", directory.display())));
    }
    std::fs::create_dir_all(trial_root).map_err(|e| AdmissionError::tool(format!("{}: {e}", trial_root.display())))?;
    remove_build_directory(&building).map_err(store_error)?;
    let linked = || -> Result<gendb_storage::io::PartsManifest, AdmissionError> {
        let mut writer = gendb_storage::io::PartFilesWriter::new(&building, gendb_storage::io::PartsFormat::LittleEndian).map_err(AdmissionError::tool)?;
        writer.link_parts_of(source_directory).map_err(AdmissionError::tool)?;
        writer.finish().map_err(AdmissionError::tool)
    };
    let manifest = match linked() {
        Ok(manifest) => manifest,
        Err(error) => {
            remove_build_directory(&building).map_err(store_error)?;
            return Err(error);
        }
    };
    let parts = manifest.parts.iter().map(|(elem, len)| Ok((element_name(elem)?, *len))).collect::<Result<Vec<_>, AdmissionError>>()?;
    let evidence = store
        .put(1, STORAGE_ASSET_REUSE_KIND, &json!({"storage_package":package_id,"key":key,"source_directory":source_directory,"parts":manifest,"reuse":reuse}))
        .map_err(store_error)?;
    let built = BuiltParts {
        format_version: manifest.format_version,
        byte_order: manifest.byte_order.map(|order| format!("{order:?}").to_lowercase()).unwrap_or_else(|| "host".into()),
        parts,
        storage_bytes: manifest.storage_bytes,
    };
    let asset = records::storage_asset_record(key, built, source_wall_ns, evidence).map_err(record_error)?;
    let id = records::storage_asset_id(&asset).map_err(record_error)?;
    std::fs::set_permissions(&building, std::fs::Permissions::from_mode(0o555)).map_err(|e| AdmissionError::tool(format!("{}: {e}", building.display())))?;
    std::fs::rename(&building, &directory).map_err(|e| AdmissionError::tool(format!("{}: {e}", directory.display())))?;
    Ok(TrialAsset { id, asset, directory })
}

/// Publish a trial asset (at registration): under its key's lock, rename its sealed directory into the library as
/// `assets/<key id>` and store and append exactly its record, so the published id is the trial's. A key already
/// published with the trial's id is returned as it is; with another id, refused (`asset_key_already_published`).
pub fn promote_trial_asset(store: &ObjectStore, trial: &TrialAsset) -> Result<StorageAsset, AdmissionError> {
    let lock = records::lock_storage_asset(store, trial.asset.key.clone()).map_err(record_error)?;
    let (id, asset) = match records::locked_storage_asset(store, &lock).map_err(record_error)? {
        Some((id, asset)) if id == trial.id => (id, asset),
        Some((id, _)) => {
            return Err(AdmissionError::refusal(format!("asset_key_already_published: the key already has asset {id}, not the trial asset {}", trial.id)));
        }
        None => records::publish_trial_storage_asset(store, &lock, &trial.directory, trial.asset.clone()).map_err(record_error)?,
    };
    if id != trial.id {
        return Err(AdmissionError::tool(format!("the published asset {id} is not the trial asset {}", trial.id)));
    }
    let directory = records::storage_asset_directory(store, &asset).map_err(record_error)?;
    Ok(StorageAsset { id, asset, directory, built: false })
}

/// Look up the asset of `package_id` for `capture` under the key's lock (waiting while another caller holds it):
/// the published asset, or the held lock for one build, after removing the key's leftover staged builds. A package
/// that assumes declared constraints other than the run's (`declared`) is refused first: its asset is neither used
/// nor built. A released asset (`records::release_storage_asset`) is absent: the caller builds it again. A published
/// asset whose directory holds no complete build (removed outside GenDB, or a release interrupted before its record)
/// is refused by name (`asset_directory_missing`), before any worker would read it.
pub fn lookup_storage_asset(store: &ObjectStore, package_id: ContentId, capture: &CurrentCapture, declared: Option<ContentId>) -> Result<AssetLookup, AdmissionError> {
    let package: VerusStoragePackageV1 = store.read(package_id).and_then(|o| o.decode()).map_err(store_error)?;
    check_storage_assumptions(&package, declared)?;
    let key = capture.asset_key(package_id, &package).map_err(AdmissionError::missing_input)?;
    // One builder per key: the lock is held from this lookup until publication (or failure), so a concurrent caller
    // for the same key waits here and then finds the published asset; other keys are not blocked.
    let lock = records::lock_storage_asset(store, key).map_err(record_error)?;
    if let Some((id, asset)) = records::locked_storage_asset(store, &lock).map_err(record_error)? {
        let directory = records::storage_asset_directory(store, &asset).map_err(record_error)?;
        if !directory.join("parts.json").is_file() {
            return Err(AdmissionError::tool(format!(
                "asset_directory_missing: the published asset {id} of storage {} names {}, which holds no complete build (removed outside GenDB, or a release stopped before its record); nothing was built or run. On the general engine line the next release of superseded assets releases its record, so the asset is then built again by its stored builder",
                package.name,
                directory.display()
            )));
        }
        return Ok(AssetLookup::Published(StorageAsset { id, asset, directory, built: false }));
    }
    let stale_staging_bytes = store.remove_stale_asset_staging(lock.asset_name()).map_err(store_error)?;
    Ok(AssetLookup::Absent(AssetBuildSlot { package_id, package, lock, stale_staging_bytes }))
}

/// The free-space margin: the asset build guard requires it before a build (beyond a reliable size estimate), and
/// the parts writer keeps it free while the build writes (`gendb_storage::io::PartFilesWriter`); also the level below
/// which a failed build's report records disk pressure. With the free-space probe, shared from the storage I/O.
pub use gendb_storage::io::{STORAGE_MARGIN_BYTES, free_bytes_at};

/// The error of a failed asset build with what the disk showed. It is `insufficient_storage` (a tool failure: no
/// candidate is implicated) only on explicit evidence: the parts writer refused a write at the free-space reserve
/// (already classified by `CandidateRunner::run`, whatever the free space after the child ended; the disk facts are
/// appended), or the failure text reports a full device or quota (`os error 28`/`122`, as the child prints an I/O
/// error) AND the library's filesystem had less than the margin free when the build failed. Otherwise the original
/// class and message stay, with free space appended as an observation when it was below the margin. `free`: free
/// bytes measured before the partial build was removed; `removed`: the bytes that partial build held.
pub fn disk_full_evidence(error: AdmissionError, free: Option<u64>, removed: u64) -> AdmissionError {
    let low = free.is_some_and(|free| free < STORAGE_MARGIN_BYTES);
    let device_full = ["(os error 28)", "(os error 122)"].iter().any(|errno| error.message.contains(errno));
    let observed = format!("{} bytes free on the library filesystem when the build failed; its partial build ({removed} bytes) was removed", free.map_or("unknown".into(), |f| f.to_string()));
    if error.class == FailureClass::ToolFailure && error.message.starts_with(RESERVE_STOP) {
        return AdmissionError::tool(format!("{}; observation: {observed}", error.message));
    }
    match (device_full, low) {
        (true, true) => AdmissionError::tool(format!("insufficient_storage: the storage build ran out of disk space ({observed}; no candidate is implicated); original error: {error}")),
        (_, true) => AdmissionError::new(error.class, format!("{}; observation: {observed}", error.message)),
        _ => error,
    }
}

/// The builder input of `package` over a prepared capture: its stored tables' declared columns, projected from the
/// capture (metadata only) and persisted as the view archive `directory` unless it exists.
pub fn storage_input(source: &PreparedSource, package: &VerusStoragePackageV1, directory: &Path) -> Result<WorkerInput, AdmissionError> {
    if package.derived_from.is_some() {
        return Err(AdmissionError::tool(format!("storage {} is built from admitted storages: its input is their assets (derived_storage_input)", package.name)));
    }
    let projection: Vec<(String, Vec<usize>)> = package.tables.iter().map(|t| (t.table.clone(), t.ordinals.clone())).collect();
    write_storage_input(source, &projection, &format!("storage {}", package.name), directory)
}

/// The builder input of `projection` (stored tables with their ordinals): projected from the capture (metadata only)
/// and persisted as the view archive `directory` unless it exists (its parent created when absent).
fn write_storage_input(source: &PreparedSource, projection: &[(String, Vec<usize>)], what: &str, directory: &Path) -> Result<WorkerInput, AdmissionError> {
    if !directory.exists() {
        // A rebuild (after a reclaim) may run under an evidence directory nothing has created yet.
        if let Some(parent) = directory.parent() {
            std::fs::create_dir_all(parent).map_err(|e| AdmissionError::tool(format!("{}: {e}", parent.display())))?;
        }
        let columns = source
            .project(projection)
            .map_err(|e| AdmissionError::missing_input(format!("the prepared capture does not hold {what}'s columns: {e}")))?;
        columns.write_archive(directory).map_err(AdmissionError::tool)?;
    }
    Ok(WorkerInput::Tables {
        path: directory.to_owned(),
        tables: projection.iter().map(|(table, ordinals)| TableColumns { table: table.clone(), ordinals: ordinals.clone() }).collect(),
    })
}

/// The builder input of a storage built from admitted storages (`package.derived_from`) for `capture`: every source's
/// published asset for the same capture (its parts directory), in the builder's use order, and the extended source. A
/// source without an asset for the capture is `missing_input` (its asset is built when a query or storage first uses
/// it). Nothing is read from the original input.
pub fn derived_storage_input(store: &ObjectStore, package: &VerusStoragePackageV1, capture: &CurrentCapture) -> Result<WorkerInput, AdmissionError> {
    let derivation = package.derived_from.as_ref().ok_or_else(|| AdmissionError::tool(format!("storage {} is not built from admitted storages", package.name)))?;
    derivation_input(store, &package.name, derivation, capture)
}

/// The builder input of storage `name` built from admitted storages by `derivation`: each source's published asset
/// for `capture` (no source column is read); also the input of an unverified diagnostic build of such a storage.
pub fn derivation_input(store: &ObjectStore, name: &str, derivation: &VerusDerivationV1, capture: &CurrentCapture) -> Result<WorkerInput, AdmissionError> {
    let mut uses = vec![];
    for source in &derivation.sources {
        let record = records::resolve_admitted_storage(store, source.package).map_err(record_error)?;
        let key = capture.asset_key(source.package, &record).map_err(AdmissionError::missing_input)?;
        let (_, asset) = records::resolve_storage_asset(store, &key).map_err(record_error)?.ok_or_else(|| {
            AdmissionError::missing_input(format!(
                "source storage {} of {name} has no asset for the current data; build it first (any trial or storage_build that uses it)",
                source.name
            ))
        })?;
        uses.push(StorageUseInput { name: source.name.clone(), parts_directory: records::storage_asset_directory(store, &asset).map_err(record_error)? });
    }
    Ok(WorkerInput::StoredParts { uses, extends: derivation.extends })
}

/// Admit a published storage package with its evidence (step 3).
pub fn admit_storage(store: &ObjectStore, package: ContentId, evidence: Vec<ContentId>) -> Result<ContentId, AdmissionError> {
    records::admit_storage_package(store, &VerusStorageAdmissionV1 { package, gate_identity: STORAGE_GATE_IDENTITY.into(), evidence })
        .map_err(record_error)
}

/// The TCB record of storage packages of `entry`: the shared items, the v4 runtime, stored assets and the entry's
/// assumptions (storage entry v2: also `declared_integrity_constraints`).
pub fn storage_tcb_record(entry: &StorageEntry) -> Result<VerusTcbV1, AdmissionError> {
    storage_tcb_record_with(entry, &[])
}

/// [`storage_tcb_record`] with the further trusted host items `extra` (a flat storage: `flat_capture_parts`).
fn storage_tcb_record_with(entry: &StorageEntry, extra: &[(&str, &str)]) -> Result<VerusTcbV1, AdmissionError> {
    let mut items = framework_trusted_items();
    items.extend(v4_host_items(extra));
    items.extend(entry_assumptions(entry.trusted_assumptions, entry.identity));
    Ok(VerusTcbV1 { items, refusal_rules: serde_json::to_value(VERUS_REFUSAL_RULES).map_err(AdmissionError::tool)? })
}

/// Trusted host items of the v4 path: the runtime's, stored assets, and `extra` (for example serving lookup).
pub(super) fn v4_host_items(extra: &[(&str, &str)]) -> Vec<VerusTrustedItemV1> {
    let runtime = runtime_build_identity();
    gendb_runtime::trusted_items_v4()
        .into_iter()
        .map(|item| (item, "host side of the v4 ABI"))
        .chain(STORAGE_HOST_ITEMS.into_iter().map(|item| (item, "stored assets")))
        .chain(extra.iter().copied().map(|item| (item, "serving")))
        .map(|((id, item), reason)| VerusTrustedItemV1 {
            id: id.into(),
            item: item.into(),
            identity: format!("verus abi v4 host ({runtime})"),
            reason: reason.into(),
        })
        .collect()
}

/// Every file of the frozen crate `<root>/src/`, relative to `src/`, sorted, with its owner (`is_author`).
pub(super) fn crate_sources(root: &Path, is_author: &dyn Fn(&str) -> bool) -> Result<Vec<(String, VerusSourceOwnerV1)>, AdmissionError> {
    fn walk(directory: &Path, prefix: &str, out: &mut Vec<String>) -> Result<(), AdmissionError> {
        let entries = std::fs::read_dir(directory).map_err(|e| AdmissionError::missing_input(format!("{}: {e}", directory.display())))?;
        for entry in entries {
            let entry = entry.map_err(|e| AdmissionError::tool(format!("{}: {e}", directory.display())))?;
            let name = entry.file_name().to_string_lossy().to_string();
            let path = if prefix.is_empty() { name.clone() } else { format!("{prefix}/{name}") };
            if entry.file_type().map_err(AdmissionError::tool)?.is_dir() {
                walk(&entry.path(), &path, out)?;
            } else {
                out.push(path);
            }
        }
        Ok(())
    }
    let mut paths = vec![];
    walk(&root.join("src"), "", &mut paths)?;
    paths.sort();
    Ok(paths
        .into_iter()
        .map(|path| {
            let owner = if is_author(&path) { VerusSourceOwnerV1::Agent } else { VerusSourceOwnerV1::Framework };
            (path, owner)
        })
        .collect())
}

/// Every author file of the stored build (the registry's author roots: `builder/**`, `agent/**`, every
/// `stores/*/interface/**`) passes the central author-source scan (`obligations::author_source_findings`, the refusal
/// list freezing applies), read back from the build record: admission never relies on a scan it did not see.
pub(super) fn refuse_unscanned_author_sources(store: &ObjectStore, build: &VerusBuildV1) -> Result<(), AdmissionError> {
    let findings = author_source_findings(&build_files(store, build)?);
    if findings.is_empty() {
        return Ok(());
    }
    let listed: Vec<String> = findings.iter().map(|x| format!("{}:{}: {}: {}", x.file, x.line, x.rule, x.detail)).collect();
    Err(AdmissionError::refusal(format!("author sources of the build break the author-source rules: {}", listed.join("; "))))
}

/// Every stored source of `build` as a `FrameworkSource` (framework and author files alike, as checked).
pub(super) fn build_files(store: &ObjectStore, build: &VerusBuildV1) -> Result<Vec<FrameworkSource>, AdmissionError> {
    Ok(build
        .source_texts(store)
        .map_err(record_error)?
        .into_iter()
        .map(|(path, _, text)| FrameworkSource { path, text })
        .collect())
}

/// The dependency closure of storage `name` in `build` (the registry's shared files), with their stored blobs.
fn closure_files(store: &ObjectStore, build: &VerusBuildV1, name: &StorageName) -> Result<Vec<VerusClosureFileV1>, AdmissionError> {
    let files = build_files(store, build)?;
    storage_closure(&files, name)
        .keys()
        .map(|path| {
            let source = build.sources.iter().find(|s| s.path == *path).ok_or_else(|| AdmissionError::tool("closure file absent from its build"))?;
            Ok(VerusClosureFileV1 { path: source.path.clone(), blob: source.blob, bytes: source.bytes })
        })
        .collect()
}

/// The typed summary of a storage declaration: table, table id, delivered ordinals.
fn stored_tables(declaration: &DeclaredSource) -> Vec<VerusStoredTableV1> {
    declaration
        .tables
        .iter()
        .map(|t| VerusStoredTableV1 { table: t.name.clone(), table_id: t.table_id, ordinals: t.columns.iter().map(|c| c.ordinal).collect() })
        .collect()
}

/// The builder saw exactly the key's row count of every stored table (first column of each table in ABI order).
fn check_built_rows(package: &VerusStoragePackageV1, key: &records::VerusStorageAssetKeyV1, column_rows: &[u64]) -> Result<(), AdmissionError> {
    let mut column = 0;
    for (stored, keyed) in package.tables.iter().zip(&key.tables) {
        if column_rows.get(column) != Some(&keyed.rows) {
            return Err(AdmissionError::tool(format!(
                "the storage build read {:?} rows of table {} where the capture has {}",
                column_rows.get(column),
                stored.table,
                keyed.rows
            )));
        }
        column += stored.ordinals.len();
    }
    Ok(())
}

/// The recorded element name of a part element type (`i32`, ...).
fn element_name(elem: &gendb_storage::io::PartElem) -> Result<String, AdmissionError> {
    match serde_json::to_value(elem).map_err(AdmissionError::tool)? {
        Value::String(name) => Ok(name),
        other => Err(AdmissionError::tool(format!("part element {other} is not a name"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `insufficient_storage` needs the writer's reserve refusal (classified by the runner), or both the child's
    /// full-device report and low free space; low space alone is only an observation on the original error, and
    /// anything else is returned unchanged.
    #[test]
    fn disk_full_needs_explicit_evidence() {
        let enospc = || AdmissionError::execution("child worker ended without a status: /x/part-0003.bin: No space left on device (os error 28)");
        let low = Some(STORAGE_MARGIN_BYTES - 1);
        let full = disk_full_evidence(enospc(), low, 7);
        assert_eq!(full.class, crate::admission::FailureClass::ToolFailure);
        assert!(full.message.starts_with("insufficient_storage:") && full.message.contains("(os error 28)") && full.message.contains("7 bytes"));
        let proof = || AdmissionError::execution("storage builder returned SqlError");
        let observed = disk_full_evidence(proof(), low, 0);
        assert_eq!(observed.class, crate::admission::FailureClass::ExecutionFailure, "low space alone never reclassifies");
        assert!(observed.message.starts_with("storage builder returned SqlError; observation:"));
        assert_eq!(disk_full_evidence(enospc(), Some(STORAGE_MARGIN_BYTES), 0), enospc(), "errno text alone with ample space: unchanged");
        assert_eq!(disk_full_evidence(proof(), None, 0), proof());
        let stopped = || AdmissionError::tool(format!("{RESERVE_STOP}: storage_reserve_reached: writing 64 more bytes under /x"));
        let reserve = disk_full_evidence(stopped(), Some(STORAGE_MARGIN_BYTES + 5), 9);
        assert_eq!(reserve.class, FailureClass::ToolFailure, "the writer's refusal is the evidence, whatever the free space after");
        assert!(reserve.message.starts_with(RESERVE_STOP) && reserve.message.ends_with("its partial build (9 bytes) was removed"));
    }
}
