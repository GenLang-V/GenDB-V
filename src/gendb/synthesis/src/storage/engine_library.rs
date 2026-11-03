//! The engine library of a schema-engine run: one library per engine run, seeded with admitted storage
//! packages and their assets, holding no query package, its engine versions on the engine stream.
//!
//! - [`seed_engine_library`] (`gendb seed-engine-library`): plan, and with `apply` carry, admitted storage packages of a
//!   source library with their records and assets by hard links (`gendb_artifacts::verus::engine::seed`). Nothing is
//!   built, no data is read or hashed; a dry run writes nothing. The same seed starts a new library for query sessions
//!   that continue from another run's admitted packages (`queries[].continue_from`): it holds the storages they read. The record states each package's standing under
//!   `physical_only` and the seeded assets' bytes counted by inode, the way the storage budget counts them.
//! - [`check_engine_storage_uses`]: the storage policy of an engine version's storage uses as the serving storage will
//!   stand once that version is selected (`storage::budget::engine_serving_storages`): every admitted use applicable,
//!   eligible and built for the current capture, together with the candidate's new (not yet registered) storages;
//!   under `physical_only` each column stored once across them (and what they extend); their serving bytes under the
//!   run's budget rule ([`BudgetRule`]). In an engine library a registered storage does not serve until a version
//!   reading it is selected, so a re-layout is checked here, against the candidate, not against the selected version;
//!   the general line's branches therefore never block each other's storage.
//! - [`admit_engine_version`]: under the library's budget lock (held by the caller, who registers the candidate's new
//!   storages under the same lock), that check again over the admitted uses, then the engine's admission
//!   (`gendb_verification::admission::engine::admit_engine`), so no storage registration races the selection.
//! - [`engine_assets`]: the current capture's asset of every storage use of an engine, for its worker calls.
//! - [`version_serving_bytes`]: the serving bytes of an admitted version's uses (by inode); [`plain_storage_bytes`]: the
//!   plain storage's bytes at a capture (version 0's serving storage, which the general line reports beside its budget);
//!   and
//!   [`library_bytes`]: the bytes of the whole library on disk (by inode), which the general line records after each
//!   admission.

use super::budget::{StorageBudget, engine_serving_storages};
use super::library_lock::LibraryLock;
use super::payload::{PayloadHolder, check_single_copy, payload_of_serving};
use super::policy::{PHYSICAL_ONLY, StoredDataPolicy};
use crate::query::source_items::requires_ensures;
use gendb_artifacts::verus::engine::seed::{SeedPlan, apply_seed, plan_seed};
use gendb_artifacts::verus::{self as records, VerusStorageUseV1};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::TableDef;
use gendb_runtime::worker::StorageUseInput;
use gendb_storage::versions::{CurrentCapture, resolve_storage_assets};
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::engine::{EngineAdmission, EngineCandidate, EngineSchema, admit_engine_on_line};
use gendb_verification::verus::engine_rules::EngineLine;
use serde::Serialize;
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::os::unix::fs::MetadataExt;
use std::path::Path;

/// Record kind of the storage policy check of an engine version's uses (admission evidence).
pub const ENGINE_STORAGE_POLICY_KIND: &str = "gendb.verus.engine-storage-policy.v1";

/// Seed the engine library `target` with the admitted storage packages `packages` of the library `source` (empty: every
/// storage name's current version there), with their records and assets by hard links; with `apply == false` a dry run
/// that only reads `source`. Refused: a package the user excluded in `source` under `physical_only`
/// (`seed_package_excluded`), and every refusal of the plan and its application (`gendb_artifacts::verus::engine::seed`).
/// The record lists each package with its assets and its standing under `physical_only`, and the seeded assets' part
/// bytes counted once per inode in the source and, after applying, in the target.
pub fn seed_engine_library(source: &Path, target: &Path, packages: &[ContentId], apply: bool) -> Result<Value, AdmissionError> {
    let source_store = ObjectStore::open_existing(source).map_err(|e| AdmissionError::missing_input(format!("source library {}: {e}", source.display())))?;
    let packages: Vec<ContentId> = if packages.is_empty() {
        records::current_storages(&source_store).map_err(AdmissionError::tool)?.into_iter().map(|(id, _)| id).collect()
    } else {
        packages.to_vec()
    };
    let physical = StoredDataPolicy::PhysicalOnly { eligible_storages: vec![] };
    for package in &packages {
        if let Some(reason) = physical.excluded(&source_store, *package)? {
            return Err(AdmissionError::refusal(format!("seed_package_excluded: {reason}")));
        }
    }
    let plan = plan_seed(&source_store, &packages).map_err(AdmissionError::refusal)?;
    let mut record = json!({"mode":if apply { "applied" } else { "dry_run" },"source":source,"target":target,
        "storages":storage_rows(&source_store, &plan, &physical)?,"objects":plan.objects.len(),"part_files":plan.part_files,
        "part_bytes_by_inode":plan.part_bytes_by_inode,
        "method":"objects and asset part files hard-linked under their own names; nothing built, read, copied or hashed beyond the typed records walked; no query package",
        "serving_set":"before the first engine version is selected, each seeded name's current version; afterwards exactly the storages the selected engine version reads"});
    if apply {
        let target_store = ObjectStore::open(target).map_err(|e| AdmissionError::tool(format!("target library {}: {e}", target.display())))?;
        let outcome = apply_seed(&source_store, &target_store, &plan).map_err(AdmissionError::refusal)?;
        let seeded = plan_seed(&target_store, &packages).map_err(AdmissionError::tool)?;
        record["applied"] = json!({"outcome":outcome,"target_storages":storage_rows(&target_store, &seeded, &physical)?,
            "target_part_bytes_by_inode":seeded.part_bytes_by_inode,"same_inodes":seeded.part_bytes_by_inode == plan.part_bytes_by_inode});
    }
    Ok(record)
}

/// Each seeded storage of `plan` with its assets and its standing under `physical_only` in `store`.
fn storage_rows(store: &ObjectStore, plan: &SeedPlan, physical: &StoredDataPolicy) -> Result<Vec<Value>, AdmissionError> {
    plan.storages
        .iter()
        .map(|s| {
            let ineligible = physical.ineligible(store, s.package, &s.name)?;
            let assets: Vec<Value> = s.assets.iter().map(|(id, a)| json!({"asset":id,"directory":a.directory,"storage_bytes":a.storage_bytes})).collect();
            Ok(json!({"name":s.name,"package":s.package,"admission":s.admission,"assets":assets,
                "eligible_under":PHYSICAL_ONLY,"eligible":ineligible.is_none(),"ineligible_reason":ineligible}))
        })
        .collect()
}

/// A storage an engine candidate reads that is not admitted yet (a workspace storage the controller registers together
/// with the version): its payload as its manifest declares it and the directory of its built asset.
pub struct NewEngineStorage<'a> {
    pub holder: PayloadHolder,
    pub asset_directory: &'a Path,
}

/// The storage budget rule of an engine version's serving storage (the bytes of the storages it reads, each part file
/// once, once it is selected). Recorded with every check of the storage policy.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "rule", rename_all = "snake_case")]
pub enum BudgetRule {
    /// The schema line: within the user's `data_allowance.live_bytes` (`None`: no budget).
    Allowance { allowance_bytes: Option<u64> },
    /// The general line (the template runs' allowance): a version that reads only plain storages
    /// (`plain_storages`: the seeded storages version 0 reads, the generated flat storage of every table) and adds none
    /// is allowed as is, whatever its size. Any other version (a new layout, encoding, index or metadata) keeps its
    /// serving storage within the scale's original data size (`original_data_bytes`: the raw generator text size,
    /// `engine.scales[].original_data_bytes`, as the template runs' `data_allowance.live_bytes`).
    OriginalDataSize { original_data_bytes: u64, scale: String, plain_storages: BTreeSet<ContentId> },
}

impl BudgetRule {
    /// Decide the serving storage of a version that reads the admitted storages `uses`, adds `new_storages` new ones
    /// and serves `serving_bytes` once selected; `Err` is the refusal's text.
    pub fn decide(&self, uses: &[VerusStorageUseV1], new_storages: usize, serving_bytes: u64) -> Result<String, String> {
        match self {
            BudgetRule::Allowance { allowance_bytes: None } => Ok("no storage budget".into()),
            BudgetRule::Allowance { allowance_bytes: Some(allowance) } if serving_bytes <= *allowance => Ok(format!("within the user's data_allowance of {allowance} bytes")),
            BudgetRule::Allowance { allowance_bytes: Some(allowance) } => Err(format!("{serving_bytes} serving bytes exceed the user's data_allowance of {allowance} bytes")),
            BudgetRule::OriginalDataSize { original_data_bytes, scale, plain_storages } => {
                if new_storages == 0 && uses.iter().all(|u| plain_storages.contains(&u.package)) {
                    Ok(format!(
                        "plain storage only at {scale}: {serving_bytes} serving bytes, allowed as is (the original data size, {original_data_bytes} bytes, bounds changed storage only)"
                    ))
                } else if serving_bytes <= *original_data_bytes {
                    Ok(format!(
                        "changed storage within the original data size at {scale}: {serving_bytes} serving bytes of {original_data_bytes}, {} bytes left",
                        original_data_bytes - serving_bytes
                    ))
                } else {
                    Err(format!(
                        "{serving_bytes} serving bytes of changed storage exceed the original data size at {scale}, {original_data_bytes} bytes, by {} bytes",
                        serving_bytes - original_data_bytes
                    ))
                }
            }
        }
    }

    /// The limit the shared budget facts state (`StorageBudget::allowance`): the schema line's allowance; none on the
    /// general line, whose rule and decision state its numbers.
    fn allowance(&self) -> Option<u64> {
        match self {
            BudgetRule::Allowance { allowance_bytes } => *allowance_bytes,
            BudgetRule::OriginalDataSize { .. } => None,
        }
    }
}

/// The storage policy of an engine version reading the admitted storages `uses` and the new storages `new`, as the
/// serving storage will stand once it is selected (see the module documentation), with the serving bytes decided by
/// `budget`. Returns the check's record (admission evidence); a failed rule is a refusal naming it.
pub fn check_engine_storage_uses(
    store: &ObjectStore,
    capture: &CurrentCapture,
    schema: &[TableDef],
    policy: &StoredDataPolicy,
    budget_rule: &BudgetRule,
    uses: &[VerusStorageUseV1],
    new: &[NewEngineStorage<'_>],
) -> Result<Value, AdmissionError> {
    for storage_use in uses {
        if let Some(reason) = policy.ineligible(store, storage_use.package, &storage_use.name)? {
            return Err(AdmissionError::refusal(reason));
        }
    }
    let packages: BTreeSet<ContentId> = uses.iter().map(|u| u.package).collect();
    let (serving, superseded) = engine_serving_storages(store, capture, schema, policy, &packages)?;
    for storage_use in uses {
        let Some(storage) = serving.iter().find(|s| s.package_id == storage_use.package) else {
            return Err(AdmissionError::refusal(format!("engine_storage_not_admitted: storage use {} ({}) is not an admitted storage of this library", storage_use.name, storage_use.package)));
        };
        if let Err(reason) = &storage.applicability {
            return Err(AdmissionError::refusal(format!("storage use {}: {reason}", storage_use.name)));
        }
        if storage.asset.is_none() {
            return Err(AdmissionError::refusal(format!("no_storage_asset: storage use {} has no asset for the current capture", storage_use.name)));
        }
    }
    if policy.stores_columns_once() {
        let new_holders: Vec<PayloadHolder> = new.iter().map(|n| n.holder.clone()).collect();
        check_single_copy(&new_holders, &payload_of_serving(store, &serving)?)?;
    }
    let mut budget = StorageBudget::of_serving(store, &serving, &superseded, budget_rule.allowance())?;
    let mut new_bytes = 0u64;
    for storage in new {
        new_bytes = new_bytes.saturating_add(budget.add_new(storage.asset_directory)?);
    }
    let serving_bytes = budget.used_bytes.saturating_add(new_bytes);
    let decision = match budget_rule {
        // The schema line keeps its refusal text (`StorageBudget::check_room`).
        BudgetRule::Allowance { .. } => {
            budget.check_room(new_bytes, "the storages this engine version reads (the serving storage once it is selected)")?;
            budget_rule.decide(uses, new.len(), serving_bytes).map_err(AdmissionError::refusal)?
        }
        BudgetRule::OriginalDataSize { .. } => budget_rule
            .decide(uses, new.len(), serving_bytes)
            .map_err(|reason| AdmissionError::refusal(format!("storage_budget_exceeded: {reason}")))?,
    };
    Ok(json!({"storage_policy":policy.kind(),"serving_once_selected":uses,"new_storages":new.iter().map(|n| &n.holder.name).collect::<Vec<_>>(),
        "new_bytes":new_bytes,"serving_bytes":serving_bytes,"eligible":true,"applicable_with_assets":true,
        "single_copy":if policy.stores_columns_once() { "checked: the uses, the new storages and what they extend hold each column once" } else { "not applicable" },
        "budget":budget.facts(),"budget_rule":budget_rule,"budget_decision":decision,
        "rule":"in an engine library the serving storage is exactly the storages the selected engine version reads; older versions pin no payload"}))
}

/// The serving bytes of an admitted engine version reading `uses` (the part files of their assets for `capture`, each
/// once by its filesystem identity): what [`check_engine_storage_uses`] counts for it once it is selected.
pub fn version_serving_bytes(store: &ObjectStore, capture: &CurrentCapture, schema: &[TableDef], policy: &StoredDataPolicy, uses: &[VerusStorageUseV1]) -> Result<u64, AdmissionError> {
    let packages: BTreeSet<ContentId> = uses.iter().map(|u| u.package).collect();
    let (serving, superseded) = engine_serving_storages(store, capture, schema, policy, &packages)?;
    Ok(StorageBudget::of_serving(store, &serving, &superseded, None)?.used_bytes)
}

/// The plain storage's bytes at `capture`: the serving bytes of the seeded storages `seeded` (`(name, package)`), which
/// version 0 reads (the generated flat storage of every table, plain typed arrays in source row order), counted like
/// any version's serving storage ([`version_serving_bytes`]: every part file once by filesystem identity; metadata
/// only, never data). The general line reports it beside its budget (a version reading only the
/// plain storage is allowed at this size; changed storage is bounded by the original data size). A seeded storage
/// that is not usable for `capture` (not admitted, not allowed by `policy`, or without an asset for it) is
/// `flat_storage_not_prepared` with the command that prepares it.
pub fn plain_storage_bytes(store: &ObjectStore, capture: &CurrentCapture, schema: &[TableDef], policy: &StoredDataPolicy, seeded: &[(String, ContentId)]) -> Result<u64, AdmissionError> {
    let packages: BTreeSet<ContentId> = seeded.iter().map(|(_, package)| *package).collect();
    let (serving, superseded) = engine_serving_storages(store, capture, schema, policy, &packages)?;
    for (name, package) in seeded {
        if !serving.iter().any(|s| s.package_id == *package && s.asset.is_some()) {
            return Err(AdmissionError::missing_input(format!(
                "flat_storage_not_prepared: the plain storage (version 0's storage) is measured over every seeded storage, and {name} ({package}) has no usable asset for this scale's capture; run gendb prepare-flat-storage for this scale's capture into the run library, then relaunch"
            )));
        }
    }
    Ok(StorageBudget::of_serving(store, &serving, &superseded, None)?.used_bytes)
}

/// The bytes of the library at `library` on disk, by filesystem identity (each hard-linked file once): its stored
/// assets' files and its records and blobs. Metadata only (`stat`), never data.
pub fn library_bytes(library: &Path) -> Result<Value, AdmissionError> {
    let mut seen: BTreeSet<(u64, u64)> = BTreeSet::new();
    let mut sizes = [0u64; 2];
    let mut files = [0u64; 2];
    for (index, part) in ["assets", "objects"].iter().enumerate() {
        let mut stack = vec![library.join(part)];
        while let Some(dir) = stack.pop() {
            let Ok(entries) = std::fs::read_dir(&dir) else { continue };
            for entry in entries.flatten() {
                let meta = entry.metadata().map_err(|e| AdmissionError::tool(format!("{}: {e}", entry.path().display())))?;
                if meta.is_dir() {
                    stack.push(entry.path());
                } else if meta.is_file() && seen.insert((meta.dev(), meta.ino())) {
                    sizes[index] += meta.len();
                    files[index] += 1;
                }
            }
        }
    }
    Ok(json!({"library":library,"bytes":sizes[0] + sizes[1],"asset_bytes":sizes[0],"asset_files":files[0],"record_bytes":sizes[1],"record_files":files[1],
        "counted":"every file under the library's assets/ and objects/, each once by filesystem identity (hard links into a capture count here, on the same disk); metadata only","measured_unix_ms":crate::controller::records::now_unix_ms()}))
}

/// Admit an engine version of the schema-engine line into the engine library `store` (see the module documentation):
/// [`admit_engine_version_on_line`] with the user's `data_allowance` and the schema-engine rules. The admitted version
/// becomes the selected one (that library has no selection record).
pub fn admit_engine_version(
    budget_lock: &LibraryLock,
    store: &ObjectStore,
    capture: &CurrentCapture,
    policy: &StoredDataPolicy,
    allowance: Option<u64>,
    schema: EngineSchema<'_>,
    candidate: EngineCandidate<'_>,
) -> Result<EngineAdmission, AdmissionError> {
    let rule = BudgetRule::Allowance { allowance_bytes: allowance };
    admit_engine_version_on_line(budget_lock, store, capture, policy, &rule, EngineLine::SchemaEngine, schema, candidate)
}

/// Admit an engine version into the engine library `store` (see the module documentation): holding the library's
/// budget lock (`_budget_lock`, `LibraryLock::acquire(store, BUDGET_LOCK)`, under which the caller has registered the
/// candidate's new storages), [`check_engine_storage_uses`] for the candidate's uses under `budget_rule` (every one
/// admitted now; its record joins the evidence), then the admission under the engine source rules of `line`
/// (`admit_engine_on_line`). In a library without selection records the admitted version becomes the selected one;
/// with them (the general line) it selects nothing (`gendb_artifacts::verus::engine`).
#[allow(clippy::too_many_arguments)]
pub fn admit_engine_version_on_line(
    _budget_lock: &LibraryLock,
    store: &ObjectStore,
    capture: &CurrentCapture,
    policy: &StoredDataPolicy,
    budget_rule: &BudgetRule,
    line: EngineLine,
    schema: EngineSchema<'_>,
    mut candidate: EngineCandidate<'_>,
) -> Result<EngineAdmission, AdmissionError> {
    let storage_policy = check_engine_storage_uses(store, capture, schema.tables, policy, budget_rule, &candidate.uses, &[])?;
    candidate.evidence.push((ENGINE_STORAGE_POLICY_KIND, storage_policy));
    let clause_text = |text: &str, name: &str| requires_ensures(text, name);
    admit_engine_on_line(store, schema, candidate, line, &clause_text)
}

/// The current capture's asset of every storage use of an engine, in use order: the worker's storage-use inputs and the
/// asset ids. A use without an asset for `capture` is `no_storage_asset`.
pub fn engine_assets(store: &ObjectStore, uses: &[VerusStorageUseV1], capture: &CurrentCapture) -> Result<(Vec<StorageUseInput>, Vec<ContentId>), AdmissionError> {
    let packages = uses
        .iter()
        .map(|u| records::resolve_admitted_storage(store, u.package).map_err(|e| AdmissionError::missing_input(format!("storage use {}: {e}", u.name))))
        .collect::<Result<Vec<_>, _>>()?;
    let assets = resolve_storage_assets(store, uses.iter().zip(&packages).map(|(u, p)| (u.name.as_str(), u.package, p)), capture)
        .map_err(|e| AdmissionError::refusal(e.to_string()))?;
    Ok((
        assets.iter().map(|a| StorageUseInput { name: a.name.clone(), parts_directory: a.directory.clone() }).collect(),
        assets.iter().map(|a| a.asset_id).collect(),
    ))
}

#[cfg(test)]
pub(crate) mod tests {
    //! An engine library over fixture records (no Verus run, no data): storage packages whose builds are fixture JSON
    //! reporting a complete verification, registered under `physical_only` revision 2 with their `data_policy`, with
    //! small assets for one fixture capture; engine versions whose builds carry every storage's closure. The serving
    //! set, the budget by inode, the single-copy rule and the seed are the code under test. The fixture is shared with
    //! the general line's asset release tests (`storage::asset_release`, `engine::asset_upkeep`), which also build
    //! derived storages and assets for further captures ([`Fixture::derived`], [`capture_at`]).
    use super::*;
    use crate::storage::catalog;
    use crate::storage::payload::{PayloadHolder, payload_holders, recorded_storages, serving_payload};
    use crate::storage::registration::register_storage;
    use gendb_artifacts::verus::*;
    use gendb_frontend::ast::{ColumnDef, PgType};
    use gendb_storage::versions::CapturedTable;
    use gendb_verification::obligations::DeclaredSource;
    use std::collections::{BTreeMap, BTreeSet};
    use std::os::unix::fs::MetadataExt;
    use std::path::PathBuf;

    const COMPLETE: &str = "{\"verification-results\":{\"success\":true,\"verified\":1,\"errors\":0,\"is-verifying-entire-crate\":true,\"encountered-error\":false,\"encountered-vir-error\":false}}";
    const ALLOWANCE: Option<u64> = Some(1 << 30);

    /// `lineitem(l_a, l_b)` and `orders(o_a)`, all bigint NOT NULL.
    pub(crate) fn schema() -> Vec<TableDef> {
        let column = |name: &str| ColumnDef { name: name.into(), ty: PgType::Int8, nullable: false };
        vec![
            TableDef { name: "lineitem".into(), columns: vec![column("l_a"), column("l_b")], constraints: vec![] },
            TableDef { name: "orders".into(), columns: vec![column("o_a")], constraints: vec![] },
        ]
    }

    pub(crate) fn capture() -> CurrentCapture {
        let table = |table: &str, rows: u64, ordinals: Vec<usize>| CapturedTable { table: table.into(), source_version: format!("{table}-v1"), row_order: format!("{table}-r1"), rows, ordinals };
        CurrentCapture { tables: vec![table("lineitem", 4, vec![0, 1]), table("orders", 2, vec![0])] }
    }

    /// Another capture of the same tables (a later scale: other source versions, ten times the rows).
    pub(crate) fn capture_at(scale: &str) -> CurrentCapture {
        let table = |table: &str, rows: u64, ordinals: Vec<usize>| CapturedTable { table: table.into(), source_version: format!("{table}-{scale}"), row_order: format!("{table}-r-{scale}"), rows, ordinals };
        CurrentCapture { tables: vec![table("lineitem", 40, vec![0, 1]), table("orders", 20, vec![0])] }
    }

    fn physical() -> StoredDataPolicy {
        StoredDataPolicy::PhysicalOnly { eligible_storages: vec![] }
    }

    /// A library of fixture records under the scratch directory.
    pub(crate) struct Fixture {
        pub(crate) root: PathBuf,
        pub(crate) store: ObjectStore,
        pub(crate) tcb: ContentId,
        pub(crate) evidence: ContentId,
        pub(crate) next: u32,
    }

    impl Fixture {
        pub(crate) fn new(root: &Path, name: &str) -> Fixture {
            let store = ObjectStore::open(root.join(name)).unwrap();
            let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: json!([]) }).unwrap();
            let evidence = store.put(1, "fixture-evidence", &json!({"fixture": true})).unwrap();
            Fixture { root: root.to_path_buf(), store, tcb, evidence, next: 0 }
        }

        /// Publish one complete fixture build of `files` (path, text, owner).
        fn build(&mut self, files: &[(String, String, VerusSourceOwnerV1)]) -> ContentId {
            self.next += 1;
            let dir = self.root.join(format!("builds/{}", self.next));
            for (path, text, _) in files {
                let file = dir.join("src").join(path);
                std::fs::create_dir_all(file.parent().unwrap()).unwrap();
                std::fs::write(file, text).unwrap();
            }
            std::fs::write(dir.join("lib.so"), format!("\x7fELF-fixture-{}", self.next)).unwrap();
            let argv = ["lib.rs", "--edition=2021", "--no-cheating", "--output-json", "--compile", "-o", "/x/lib.so"].map(String::from).to_vec();
            publish_build(&self.store, VerusBuildInput {
                purpose: VerusBuildPurposeV1::Candidate,
                provider_identity: "pinned".into(),
                argv,
                environment: BTreeMap::from([("VSTD_KIND".into(), "Imported".into())]),
                exit_code: Some(0),
                stdout: COMPLETE,
                frozen_directory: &dir,
                sources: files.iter().map(|(p, _, o)| (p.clone(), *o)).collect(),
                library_path: &dir.join("lib.so"),
                wall_ns: 1,
                tcb: self.tcb,
            })
            .unwrap()
        }

        /// Publish and register storage `name` ([`Fixture::publish`], then registration under physical_only revision 2
        /// with `data_policy`). Returns the package.
        pub(crate) fn storage(&mut self, name: &str, columns: &[(usize, &[usize])], data_policy: Value, shared: Option<&Path>, parts: usize) -> ContentId {
            let (package, asset) = self.publish(name, columns, shared, parts);
            let description = json!({"storage_policy":"physical_only","storage_policy_revision":2,"data_policy":data_policy});
            register_storage(&self.store, name, package, asset, &[self.evidence], &description).unwrap();
            package
        }

        /// Publish (not admit) storage `name` storing `columns` (table id -> ordinals) and its asset for [`capture`]:
        /// `parts` new part files of 64 bytes each, after the part files of `shared` (an asset directory whose files it
        /// links, as an extension does). Returns `(package, asset)`.
        pub(crate) fn publish(&mut self, name: &str, columns: &[(usize, &[usize])], shared: Option<&Path>, parts: usize) -> (ContentId, ContentId) {
            let id = self.publish_package(name, columns, None);
            (id, self.publish_asset(id, &capture(), shared, parts))
        }

        /// Publish (not admit) the package of storage `name` storing `columns`, built from the admitted storages of
        /// `derived_from` (`None`: from source columns, storage entry v1; else the derived entry).
        pub(crate) fn publish_package(&mut self, name: &str, columns: &[(usize, &[usize])], derived_from: Option<VerusDerivationV1>) -> ContentId {
            let selection: BTreeMap<usize, BTreeSet<usize>> = columns.iter().map(|(t, c)| (*t, c.iter().copied().collect())).collect();
            let declaration = DeclaredSource::for_storage(&schema(), &selection).unwrap();
            let framework = VerusSourceOwnerV1::Framework;
            let entry = if derived_from.is_some() { VERUS_STORAGE_ENTRY_DERIVED_IDENTITY } else { VERUS_STORAGE_ENTRY_V1_IDENTITY };
            let files = vec![
                ("schema.rs".to_string(), "SCHEMA".to_string(), framework),
                (format!("stores/{name}/declaration.rs"), format!("DECLARATION {name}"), framework),
                (format!("stores/{name}/interface/mod.rs"), format!("INTERFACE {name}"), VerusSourceOwnerV1::Agent),
                ("gendb_entry.rs".to_string(), format!("// fixture `{entry}`\npub proof fn theorem_storage_built() {{}}\n"), framework),
                ("builder/mod.rs".to_string(), format!("BUILDER {name}"), VerusSourceOwnerV1::Agent),
            ];
            let build = self.build(&files);
            let record: VerusBuildV1 = self.store.read(build).unwrap().decode().unwrap();
            let closure = record
                .sources
                .iter()
                .filter(|s| !s.path.starts_with("builder/") && s.path != "gendb_entry.rs")
                .map(|s| VerusClosureFileV1 { path: s.path.clone(), blob: s.blob, bytes: s.bytes })
                .collect();
            let package = VerusStoragePackageV1 {
                name: name.into(),
                build,
                entry_identity: entry.into(),
                assumed_constraints: None,
                tables: declaration.tables.iter().map(|t| VerusStoredTableV1 { table: t.name.clone(), table_id: t.table_id, ordinals: t.columns.iter().map(|c| c.ordinal).collect() }).collect(),
                declaration: serde_json::to_value(&declaration).unwrap(),
                schema_ddl: self.store.put_blob(b"DDL").unwrap(),
                frontend: json!({"identity": "fixture"}),
                closure,
                configuration: record.check_configuration().unwrap(),
                readers: vec![],
                theorems: vec!["gendb_entry::theorem_storage_built".into()],
                workers: (1, 64),
                tcb: self.tcb,
                derived_from,
            };
            let expected: Vec<(&str, &str)> = files.iter().filter(|f| f.2 == framework).map(|f| (f.0.as_str(), f.1.as_str())).collect();
            publish_storage_package(&self.store, &package, &expected).unwrap()
        }

        /// Publish the asset of package `id` for `capture`: `parts` new part files of 64 bytes each after the linked part
        /// files of `shared`, as [`Fixture::publish`] does. Returns the asset.
        pub(crate) fn publish_asset(&mut self, id: ContentId, capture: &CurrentCapture, shared: Option<&Path>, parts: usize) -> ContentId {
            let package: VerusStoragePackageV1 = self.store.read(id).unwrap().decode().unwrap();
            let key = capture.asset_key(id, &package).unwrap();
            let lock = lock_storage_asset(&self.store, key).unwrap();
            let staged = self.store.fresh_asset_staging_directory(lock.asset_name()).unwrap();
            std::fs::create_dir(&staged).unwrap();
            let mut index = 0;
            for entry in shared.map(|dir| std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|x| x == "bin")).collect::<Vec<_>>()).unwrap_or_default() {
                std::fs::hard_link(&entry, staged.join(format!("part-{index:04}.bin"))).unwrap();
                index += 1;
            }
            for _ in 0..parts {
                std::fs::write(staged.join(format!("part-{index:04}.bin")), [index as u8; 64]).unwrap();
                index += 1;
            }
            std::fs::write(staged.join("parts.json"), "{}").unwrap();
            let built = BuiltParts { format_version: 2, byte_order: "little".into(), parts: (0..index).map(|_| ("u8".to_string(), 64)).collect(), storage_bytes: 64 * index as u64 };
            let (asset, _) = publish_storage_asset(&self.store, &lock, &staged, built, 1, self.evidence).unwrap();
            asset
        }

        /// Publish and register the derived storage `name` storing `columns`, built from the admitted `sources`
        /// (`extends`: the index of the source whose part files its assets link first), with an asset of `parts` own
        /// part files for each of `captures`. Returns the package.
        pub(crate) fn derived(&mut self, name: &str, columns: &[(usize, &[usize])], sources: &[(&str, ContentId)], extends: Option<usize>, parts: usize, captures: &[CurrentCapture]) -> ContentId {
            let derivation = VerusDerivationV1 { sources: sources.iter().map(|(n, p)| VerusDerivationSourceV1 { name: (*n).into(), package: *p }).collect(), extends };
            let package = self.publish_package(name, columns, Some(derivation));
            let mut first = None;
            for capture in captures {
                let shared = extends.map(|k| self.asset_dir_at(sources[k].1, capture));
                let asset = self.publish_asset(package, capture, shared.as_deref(), parts);
                first.get_or_insert(asset);
            }
            let description = json!({"storage_policy":"physical_only","storage_policy_revision":2,"data_policy":payload("lineitem", &["l_a", "l_b"])});
            register_storage(&self.store, name, package, first.expect("at least one capture"), &[self.evidence], &description).unwrap();
            package
        }

        /// The asset directory of `package` (published, admitted or not) for [`capture`].
        pub(crate) fn asset_dir(&self, package: ContentId) -> PathBuf {
            self.asset_dir_at(package, &capture())
        }

        /// The asset directory of `package` for `capture`.
        pub(crate) fn asset_dir_at(&self, package: ContentId, capture: &CurrentCapture) -> PathBuf {
            let record: VerusStoragePackageV1 = self.store.read(package).unwrap().decode().unwrap();
            let (_, asset) = resolve_storage_asset(&self.store, &capture.asset_key(package, &record).unwrap()).unwrap().unwrap();
            storage_asset_directory(&self.store, &asset).unwrap()
        }

        /// Admit an engine version reading `uses` (`(name, package)`): its build carries every use's closure.
        fn engine(&mut self, uses: &[(&str, ContentId)]) -> u64 {
            self.engine_with_lineage(uses, None).version
        }

        /// [`Fixture::engine`] with a lineage record in its admission evidence (the general line).
        pub(crate) fn engine_with_lineage(&mut self, uses: &[(&str, ContentId)], lineage: Option<VerusEngineLineageV1>) -> EngineVersion {
            let (_, version) = self.admit_with_lineage(uses, lineage).unwrap();
            engine_versions(&self.store).unwrap().into_iter().find(|v| v.version == version).unwrap()
        }

        /// Publish an engine package reading `uses` and try to admit it with `lineage` in its evidence.
        fn admit_with_lineage(&mut self, uses: &[(&str, ContentId)], lineage: Option<VerusEngineLineageV1>) -> Result<(ContentId, u64), gendb_artifacts::verus::RecordError> {
            let framework = VerusSourceOwnerV1::Framework;
            let mut files: BTreeMap<String, (String, VerusSourceOwnerV1)> = BTreeMap::new();
            files.insert("gendb_entry.rs".into(), ("// fixture `gendb-verus-engine-entry-v1`\npub proof fn theorem_engine_end_to_end() {}\npub proof fn corollary_inside_capacity() {}\n".into(), framework));
            files.insert("gendb_constraints.rs".into(), ("CONSTRAINTS".into(), framework));
            files.insert("agent/mod.rs".into(), (format!("ENGINE {}", self.next), VerusSourceOwnerV1::Agent));
            for (_, package) in uses {
                for file in resolve_admitted_storage(&self.store, *package).unwrap().closure {
                    let text = String::from_utf8(self.store.read_blob(file.blob, None).unwrap()).unwrap();
                    files.insert(file.path, (text, framework));
                }
            }
            let files: Vec<(String, String, VerusSourceOwnerV1)> = files.into_iter().map(|(p, (t, o))| (p, t, o)).collect();
            let build = self.build(&files);
            let package = VerusEnginePackageV1 {
                entry_identity: VERUS_ENGINE_ENTRY_V1_IDENTITY.into(),
                build,
                theorems: vec!["gendb_entry::theorem_engine_end_to_end".into(), "gendb_entry::corollary_inside_capacity".into()],
                schema_ddl: self.store.put_blob(b"DDL").unwrap(),
                frontend: json!({"identity": "fixture"}),
                constraints: gendb_artifacts::blob_id(b"CONSTRAINTS"),
                generation_identity: "fixture engine".into(),
                storage_uses: uses.iter().map(|(name, package)| VerusStorageUseV1 { name: (*name).into(), package: *package }).collect(),
                toolkit: vec![],
                implementations: vec![],
                abi_version: ENGINE_PACKAGE_ABI_VERSION,
                workers: (1, 64),
                tcb: self.tcb,
            };
            let expected: Vec<(&str, &str)> = files.iter().filter(|f| f.2 == framework).map(|f| (f.0.as_str(), f.1.as_str())).collect();
            let package = publish_engine_package(&self.store, &package, &expected).unwrap();
            let mut evidence = vec![self.evidence];
            if let Some(lineage) = lineage {
                evidence.push(self.store.put(1, VERUS_ENGINE_LINEAGE_KIND, &lineage).unwrap());
            }
            let admission = VerusEngineAdmissionV1 { package, gate_identity: "fixture".into(), evidence, assets: vec![] };
            gendb_artifacts::verus::admit_engine_version(&self.store, &admission, &|_| Ok(()))
        }

        /// The serving storages' `(name, package)` and the budget's used bytes.
        fn serving(&self) -> (BTreeSet<String>, u64) {
            let (serving, superseded) = crate::storage::budget::serving_storages(&self.store, &capture(), &schema(), &physical(), &BTreeSet::new()).unwrap();
            let budget = StorageBudget::of_serving(&self.store, &serving, &superseded, ALLOWANCE).unwrap();
            (serving.iter().map(|s| s.package.name.clone()).collect(), budget.used_bytes)
        }

        /// The single-copy check of `name`'s package `package` as a new holder against the serving storage (the check
        /// registration and storage tools apply): `Ok` or the refusal.
        fn dry_run(&self, name: &str, package: ContentId) -> Result<(), String> {
            let holders: Vec<PayloadHolder> = payload_holders(&recorded_storages(&self.store, vec![(name.into(), package)]).unwrap());
            let serving = serving_payload(&self.store, &capture(), &schema(), &physical(), &BTreeSet::new()).unwrap();
            check_single_copy(&holders, &serving).map_err(|e| e.message)
        }
    }

    /// Remove a scratch tree whose sealed asset directories (0555) are made writable first; file modes are untouched
    /// (a seeded part file is a hard link of the source's).
    pub(crate) fn remove_scratch(root: &Path) {
        use std::os::unix::fs::PermissionsExt;
        fn open_up(dir: &Path) {
            std::fs::set_permissions(dir, std::fs::Permissions::from_mode(0o755)).unwrap();
            for entry in std::fs::read_dir(dir).unwrap() {
                let entry = entry.unwrap();
                if entry.file_type().unwrap().is_dir() {
                    open_up(&entry.path());
                }
            }
        }
        open_up(root);
        std::fs::remove_dir_all(root).unwrap();
    }

    pub(crate) fn payload(table: &str, columns: &[&str]) -> Value {
        json!([{"part":0,"table":table,"kind":"base_payload","columns":columns,"why":"the one copy"}])
    }

    /// Done-check 1 at fixture scale: a seed carries the storages (an extension sharing its base's part files
    /// included) with their records and assets by hard links, no query or engine record; the target lists every seeded
    /// storage as applicable and eligible under physical_only, and its budget, counted by inode, equals the source's;
    /// the part files are the source's inodes; a second seed changes nothing; a seed whose records reach a query record
    /// is refused.
    #[test]
    fn seeded_engine_library_lists_eligible_storages_and_counts_the_same_inodes() {
        let root = crate::controller::test_support::scratch_root("engine-library-seed");
        let mut source = Fixture::new(&root, "source");
        let base = source.storage("base", &[(0, &[0, 1])], payload("lineitem", &["l_a", "l_b"]), None, 2);
        let base_dir = source.asset_dir(base);
        let keys = source.storage("base_keys", &[(0, &[0])], json!([{"part":0,"table":"lineitem","kind":"index_keys","columns":["l_a"],"why":"own keys"}]), Some(&base_dir), 1);
        let orders = source.storage("orders_flat", &[(1, &[0])], payload("orders", &["o_a"]), None, 1);
        let source_budget = source.serving().1;
        assert_eq!(source_budget, 64 * 4, "base's two parts are counted once although base_keys links them");

        let target_root = root.join("engine");
        let seeded = seed_engine_library(&root.join("source"), &target_root, &[], true).unwrap();
        assert_eq!(seeded["applied"]["same_inodes"], true, "{seeded:#}");
        assert_eq!(seeded["part_bytes_by_inode"], 64 * 4);
        let target = ObjectStore::open_existing(&target_root).unwrap();
        let listed = catalog::admitted_storages(&target, &capture(), &schema()).unwrap();
        assert_eq!(listed.iter().map(|s| s.package_id).collect::<BTreeSet<_>>(), BTreeSet::from([base, keys, orders]));
        for storage in &listed {
            assert!(storage.applicability.is_ok() && storage.asset.is_some(), "{}", storage.package.name);
            assert_eq!(physical().ineligible(&target, storage.package_id, &storage.package.name).unwrap(), None, "{} is eligible", storage.package.name);
        }
        let target_fixture = Fixture { root: root.clone(), store: target.clone(), tcb: source.tcb, evidence: source.evidence, next: 100 };
        assert_eq!(target_fixture.serving(), (BTreeSet::from(["base".into(), "base_keys".into(), "orders_flat".into()]), source_budget));
        let inode = |p: &Path| std::fs::metadata(p).map(|m| (m.dev(), m.ino())).unwrap();
        assert_eq!(inode(&target_fixture.asset_dir(base).join("part-0001.bin")), inode(&base_dir.join("part-0001.bin")), "a hard link, not a copy");
        for kind in [VERUS_PACKAGE_ADMISSION_V2_KIND, VERUS_QUERY_PACKAGE_V3_KIND, VERUS_ENGINE_PACKAGE_KIND, VERUS_ENGINE_ADMISSION_KIND] {
            assert!(target.list_kind(kind).unwrap().is_empty(), "{kind} is not seeded");
        }
        let again = seed_engine_library(&root.join("source"), &target_root, &[], true).unwrap();
        assert_eq!(again["applied"]["outcome"]["admissions_appended"], 0);
        assert_eq!(again["applied"]["outcome"]["assets_linked"], 0);
        let dry = seed_engine_library(&root.join("source"), &root.join("never-written"), &[base, keys, orders], false).unwrap();
        assert!(dry["mode"] == "dry_run" && dry["storages"].as_array().unwrap().iter().all(|s| s["eligible"] == true) && !root.join("never-written").exists());

        // A storage whose evidence names a query package record is never seeded.
        let query = source.store.put(1, VERUS_QUERY_PACKAGE_V3_KIND, &json!({"fixture": "query"})).unwrap();
        let tainted = {
            source.evidence = query;
            source.storage("tainted", &[(1, &[0])], payload("orders", &["o_a"]), None, 1)
        };
        let refused = seed_engine_library(&root.join("source"), &root.join("tainted"), &[tainted], false).unwrap_err();
        assert!(refused.message.contains("seed_reaches_query_record"), "{refused}");
        remove_scratch(&root);
    }

    /// Done-check 2 at fixture scale: in an engine library the serving storage is exactly the storages the selected
    /// engine version reads. A re-layout of lineitem (another storage holding the same columns) is refused while the
    /// selected version reads the old storage, and accepted once the selected version reads the re-layout instead;
    /// the old storage then pins no payload and is not counted, and the older version stays recorded.
    #[test]
    fn relayout_is_accepted_only_once_the_selected_engine_stops_reading_the_old_storage() {
        let root = crate::controller::test_support::scratch_root("engine-library-relayout");
        let mut library = Fixture::new(&root, "engine");
        let base = library.storage("base", &[(0, &[0, 1])], payload("lineitem", &["l_a", "l_b"]), None, 2);
        let orders = library.storage("orders_flat", &[(1, &[0])], payload("orders", &["o_a"]), None, 1);
        // The seed state: every name's current version serves.
        assert_eq!(library.serving(), (BTreeSet::from(["base".into(), "orders_flat".into()]), 64 * 3));
        assert_eq!(library.engine(&[("base", base), ("orders_flat", orders)]), 1);
        // A re-layout of lineitem built for a candidate version (published, not registered yet).
        let (relayout, _) = library.publish("lineitem_by_b", &[(0, &[0, 1])], None, 3);
        let relayout_dir = library.asset_dir(relayout);
        let holder = || PayloadHolder {
            name: "lineitem_by_b".into(),
            package: Some(relayout),
            lineage: BTreeSet::from([relayout]),
            columns: BTreeSet::from([("lineitem".into(), "l_a".into()), ("lineitem".into(), "l_b".into())]),
            declared: true,
        };
        let serving = serving_payload(&library.store, &capture(), &schema(), &physical(), &BTreeSet::new()).unwrap();
        let refused = check_single_copy(&[holder()], &serving).unwrap_err().message;
        assert!(refused.starts_with("storage_payload_duplicate: column lineitem.l_a") && refused.contains("base"), "the selected v1 reads base: {refused}");
        // The candidate's own storage policy, as the serving storage will stand once it is selected.
        let uses = |list: &[(&str, ContentId)]| -> Vec<VerusStorageUseV1> { list.iter().map(|(n, p)| VerusStorageUseV1 { name: (*n).into(), package: *p }).collect() };
        let new = [NewEngineStorage { holder: holder(), asset_directory: &relayout_dir }];
        let check = |admitted: &[(&str, ContentId)], allowance: Option<u64>| {
            check_engine_storage_uses(&library.store, &capture(), &schema(), &physical(), &BudgetRule::Allowance { allowance_bytes: allowance }, &uses(admitted), &new)
        };
        let accepted = check(&[("orders_flat", orders)], ALLOWANCE).unwrap();
        assert_eq!((accepted["budget"]["used_bytes"].as_u64(), accepted["new_bytes"].as_u64()), (Some(64), Some(64 * 3)));
        assert!(check(&[("base", base), ("orders_flat", orders)], ALLOWANCE).unwrap_err().message.starts_with("storage_payload_duplicate"), "a candidate reading both copies");
        assert!(check(&[("orders_flat", orders)], Some(64 * 3)).unwrap_err().message.starts_with("storage_budget_exceeded"));
        // The controller registers the new storage under the budget lock, then the version that reads it is selected.
        let description = json!({"storage_policy":"physical_only","storage_policy_revision":2,"data_policy":payload("lineitem", &["l_a", "l_b"])});
        let asset = resolve_storage_asset(&library.store, &capture().asset_key(relayout, &library.store.read(relayout).unwrap().decode().unwrap()).unwrap()).unwrap().unwrap().0;
        register_storage(&library.store, "lineitem_by_b", relayout, asset, &[library.evidence], &description).unwrap();
        assert_eq!(library.serving(), (BTreeSet::from(["base".into(), "orders_flat".into()]), 64 * 3), "registered, it does not serve while v1 is selected");
        assert!(library.dry_run("lineitem_by_b", relayout).is_err());
        assert_eq!(library.engine(&[("lineitem_by_b", relayout), ("orders_flat", orders)]), 2);
        assert_eq!(library.serving(), (BTreeSet::from(["lineitem_by_b".into(), "orders_flat".into()]), 64 * 4));
        library.dry_run("lineitem_by_b", relayout).unwrap();
        assert!(library.dry_run("base", base).unwrap_err().starts_with("storage_payload_duplicate"), "the old copy is now the second one");
        let versions = engine_versions(&library.store).unwrap();
        assert_eq!(versions.iter().map(|v| v.version).collect::<Vec<_>>(), [1, 2]);
        let old = resolve_engine(&library.store, Some(versions[0].package_id)).unwrap().unwrap();
        assert!(!old.selected && old.storages[0].name == "base", "the older version stays resolvable and pins nothing");
        assert!(resolve_engine(&library.store, None).unwrap().unwrap().selected);
        remove_scratch(&root);
    }

    /// Done-check 4 of the general line : with selection records, admitting a version on a branch does not
    /// change the selected version or the serving set; a selection record does. Lineage parents must be admitted
    /// versions, and a selection names an admitted version once.
    #[test]
    fn branch_admission_selects_nothing_and_a_selection_record_moves_the_serving_set() {
        let root = crate::controller::test_support::scratch_root("engine-library-selection");
        let mut library = Fixture::new(&root, "engine");
        let base = library.storage("base", &[(0, &[0, 1])], payload("lineitem", &["l_a", "l_b"]), None, 2);
        let orders = library.storage("orders_flat", &[(1, &[0])], payload("orders", &["o_a"]), None, 1);
        let lineage = |branch: &str, kind: &str, parents: &[ContentId]| Some(VerusEngineLineageV1 { branch: branch.into(), kind: kind.into(), parents: parents.to_vec() });
        // Version 0 (framework generated) is selected by a selection record.
        let v0 = library.engine_with_lineage(&[("base", base), ("orders_flat", orders)], lineage("main", "framework_generated", &[]));
        let select = |library: &Fixture, version: &EngineVersion, reason: &str| {
            select_engine_version(&library.store, &VerusEngineSelectionV1 { package: version.package_id, admission: version.admission_id, reason: reason.into(), evidence: vec![] })
        };
        assert_eq!(select(&library, &v0, "version 0").unwrap().1, 1);
        assert!(select(&library, &v0, "again").unwrap_err().to_string().contains("selected version already"));
        // Branch b1 re-lays out lineitem and admits v1 reading it: nothing is selected by the admission.
        let (relayout, asset) = library.publish("lineitem_by_b", &[(0, &[0, 1])], None, 3);
        let description = json!({"storage_policy":"physical_only","storage_policy_revision":2,"data_policy":payload("lineitem", &["l_a", "l_b"])});
        register_storage(&library.store, "lineitem_by_b", relayout, asset, &[library.evidence], &description).unwrap();
        let v1 = library.engine_with_lineage(&[("lineitem_by_b", relayout), ("orders_flat", orders)], lineage("b1", "branch", &[v0.package_id]));
        assert_eq!(selected_engine(&library.store).unwrap().unwrap().package_id, v0.package_id, "a branch admission does not select");
        assert_eq!(library.serving(), (BTreeSet::from(["base".into(), "orders_flat".into()]), 64 * 3));
        assert!(resolve_engine(&library.store, None).unwrap().unwrap().version.package_id == v0.package_id);
        let found = engine_lineage(&library.store, &v1).unwrap().unwrap();
        assert_eq!((found.branch.as_str(), found.parents.as_slice()), ("b1", [v0.package_id].as_slice()));
        // The interleaved timing moved the main line: the selection record changes the serving set.
        select(&library, &v1, "interleaved timing against v000").unwrap();
        assert_eq!(selected_engine(&library.store).unwrap().unwrap().package_id, v1.package_id);
        assert_eq!(library.serving(), (BTreeSet::from(["lineitem_by_b".into(), "orders_flat".into()]), 64 * 4));
        assert!(!resolve_engine(&library.store, Some(v0.package_id)).unwrap().unwrap().selected);
        assert_eq!(engine_selections(&library.store).unwrap().len(), 2);
        // A merge names both parents; a lineage naming a version of no library, or the wrong number of parents, is refused.
        let merge = library.engine_with_lineage(&[("base", base), ("orders_flat", orders)], lineage("main", "merge", &[v1.package_id, v0.package_id]));
        assert_eq!(engine_lineage(&library.store, &merge).unwrap().unwrap().kind, "merge");
        let stranger = ContentId::from_bytes([9; 32]);
        for (kind, parents, words) in [("branch", vec![stranger], "not an admitted engine version"), ("branch", vec![], "names 0 parents"),
            ("merge", vec![v0.package_id], "names 1 parents"), ("rebuilt", vec![v0.package_id], "not one of")]
        {
            let refused = library.admit_with_lineage(&[("base", base), ("orders_flat", orders)], lineage("b2", kind, &parents)).unwrap_err().to_string();
            assert!(refused.contains(words), "lineage {kind} {parents:?}: {refused}");
        }
        assert!(select_engine_version(&library.store, &VerusEngineSelectionV1 { package: stranger, admission: stranger, reason: "r".into(), evidence: vec![] }).is_err());
        let bytes = library_bytes(&root.join("engine")).unwrap();
        assert!(bytes["asset_bytes"].as_u64().unwrap() >= 64 * 6 && bytes["record_files"].as_u64().unwrap() > 0, "{bytes}");
        remove_scratch(&root);
    }

    /// The general line's budget rule (the template runs' allowance) through the storage check: a
    /// version reading only the plain storage (the seeded storages, measured by `plain_storage_bytes`) is accepted
    /// above the original data size; a version with changed storage (a re-layout it reads, or a new storage it adds) is
    /// accepted within the original data size and at it, and refused over it.
    #[test]
    fn plain_storage_is_allowed_as_is_and_changed_storage_stays_within_the_original_data_size() {
        let root = crate::controller::test_support::scratch_root("engine-library-budget-rule");
        let mut library = Fixture::new(&root, "engine");
        let base = library.storage("base", &[(0, &[0, 1])], payload("lineitem", &["l_a", "l_b"]), None, 2);
        let orders = library.storage("orders_flat", &[(1, &[0])], payload("orders", &["o_a"]), None, 1);
        let (relayout, asset) = library.publish("lineitem_by_b", &[(0, &[0, 1])], None, 3);
        let description = json!({"storage_policy":"physical_only","storage_policy_revision":2,"data_policy":payload("lineitem", &["l_a", "l_b"])});
        register_storage(&library.store, "lineitem_by_b", relayout, asset, &[library.evidence], &description).unwrap();
        // The plain storage: the seeded storages (version 0's uses) counted as a version's serving storage.
        let seeded = [("base".to_string(), base), ("orders_flat".to_string(), orders)];
        let plain = plain_storage_bytes(&library.store, &capture(), &schema(), &physical(), &seeded).unwrap();
        assert_eq!(plain, 64 * 3);
        let stranger = ContentId::from_bytes([9; 32]);
        let stranger_seed = [("base".to_string(), base), ("missing".to_string(), stranger)];
        let refused = plain_storage_bytes(&library.store, &capture(), &schema(), &physical(), &stranger_seed).unwrap_err();
        assert!(refused.message.starts_with("flat_storage_not_prepared") && refused.message.contains("missing"), "{refused}");
        let rule = |original_data_bytes: u64| BudgetRule::OriginalDataSize {
            original_data_bytes,
            scale: "sf1".into(),
            plain_storages: seeded.iter().map(|(_, package)| *package).collect(),
        };
        let check = |original: u64, uses: &[VerusStorageUseV1]| check_engine_storage_uses(&library.store, &capture(), &schema(), &physical(), &rule(original), uses, &[]);
        // Plain storage only, above the original data size: accepted as is.
        let v0_uses = [VerusStorageUseV1 { name: "base".into(), package: base }, VerusStorageUseV1 { name: "orders_flat".into(), package: orders }];
        let plain_only = check(100, &v0_uses).unwrap();
        assert_eq!(plain_only["serving_bytes"].as_u64(), Some(plain));
        assert!(plain_only["budget_decision"].as_str().unwrap().starts_with("plain storage only at sf1: 192 serving bytes, allowed as is"), "{plain_only}");
        // Changed storage (the re-layout): within, at and over the original data size.
        let changed = [VerusStorageUseV1 { name: "lineitem_by_b".into(), package: relayout }, VerusStorageUseV1 { name: "orders_flat".into(), package: orders }];
        assert_eq!(version_serving_bytes(&library.store, &capture(), &schema(), &physical(), &changed).unwrap(), 64 * 4);
        let within = check(64 * 5, &changed).unwrap();
        assert!(within["budget_decision"].as_str().unwrap().starts_with("changed storage within the original data size at sf1: 256 serving bytes of 320, 64 bytes left"), "{within}");
        let at = check(64 * 4, &changed).unwrap();
        assert!(at["budget_decision"].as_str().unwrap().ends_with("256 serving bytes of 256, 0 bytes left"), "equality at the boundary is accepted: {at}");
        let over = check(64 * 4 - 1, &changed).unwrap_err();
        assert!(over.message.starts_with("storage_budget_exceeded: 256 serving bytes of changed storage exceed the original data size at sf1, 255 bytes, by 1 bytes"), "{over}");
        // A new storage makes a version's storage changed even when every admitted use is plain.
        assert!(rule(100).decide(&v0_uses, 1, 100).unwrap().starts_with("changed storage within the original data size"));
        assert!(rule(100).decide(&v0_uses, 1, 101).unwrap_err().contains("exceed the original data size at sf1, 100 bytes, by 1 bytes"));
        assert!(rule(100).decide(&v0_uses, 0, 101).unwrap().starts_with("plain storage only"));
        // The schema line's allowance is unchanged.
        assert!(BudgetRule::Allowance { allowance_bytes: Some(10) }.decide(&v0_uses, 0, 11).is_err() && BudgetRule::Allowance { allowance_bytes: None }.decide(&[], 0, u64::MAX).is_ok());
        remove_scratch(&root);
    }
}
