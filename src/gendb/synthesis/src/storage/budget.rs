//! The storage budget: the serving bytes of the workload's admitted storages stay within the
//! user's hard limit `data_allowance.live_bytes` (about the raw size of the dataset; the original input is not
//! counted). It is the only hard limit on storage design; nothing else bounds an author's layouts.
//!
//! **What is counted.** The serving storage: every asset, for the current capture, of every admitted storage version the
//! run's storage policy allows (`storage::policy`) that is its name's current (newest) version or is read by an
//! admitted query package. A superseded version no admitted query reads is not serving storage (it stays in the
//! library, listed apart as `superseded`). In an **engine library** (seeded with storages, no
//! query package, engine versions on the engine stream) the serving storage is exactly the storages the *selected*
//! engine version reads ([`engine_serving_storages`]); before the first version is selected it is each name's current
//! version, the seed. The selected version is the newest admitted one, or, in a library with selection records (the
//! general line, whose branches admit versions that select nothing), the one the newest selection record names
//! (`gendb_artifacts::verus::selected_engine`); a candidate's own storage is checked against its own uses
//! (`storage::engine_library::check_engine_storage_uses`), so branches never block each other's storage. Older engine versions stay recorded and rebuildable but pin no payload, and a storage registered
//! for a candidate version does not serve until a version reading it is selected. Counted are the bytes of its part files on disk, each file counted once by its filesystem
//! identity (device, inode), so a part shared by hard link between an extended storage and its base, or an asset reused
//! by two packages, is counted once. Only file metadata is read (`stat`), never data. Unregistered trial assets and
//! unverified diagnostic builds are not serving storage and are not counted (they are reported apart by their tools).
//!
//! **Where it is enforced.** In the evaluation of a submission, once its storages are built: the measured bytes of all
//! its new assets together (each part file once), against the budget as it will stand after registration (a new
//! version of a name replaces that name's current version unless an admitted query reads it); a refusal makes the
//! evaluation ineligible (`storage_budget_exceeded`, in the author's feedback). Again at registration (every admission
//! path: the workload role, a query's new storages, `storage_register`, re-verification), all storages of one
//! submission together under the budget lock, before any of them is registered. At a query package's evaluation and,
//! under the same lock, its admission: the storages it reads that are not serving storage yet (an older version of a
//! name it pins) join the serving storage when it is admitted, so their asset bytes are checked the same way
//! (`tools::bench` `check_query_storage_uses`). Before a build, with a measured estimate (an earlier build of the same key or of the
//! same storage name): the same refusal, so a build that cannot be admitted is not started. A build whose only estimate
//! is the canonical column width is not refused before it runs (compression can make it fit); its measured size decides
//! at registration. Registration holds the library's budget lock (`storage::library_lock`) from the check until the storage is
//! recorded, so concurrent sessions over one library cannot together pass the limit.

use super::catalog::{self, AdmittedStorage};
use super::policy::StoredDataPolicy;
use gendb_artifacts::verus::{self as records, VerusStorageAssetV1};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::TableDef;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::AdmissionError;
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::os::unix::fs::MetadataExt;
use std::path::Path;

/// One counted asset.
#[derive(Clone, Debug)]
pub struct CountedAsset {
    pub name: String,
    pub package: ContentId,
    pub asset: ContentId,
    /// Bytes of its part files not already counted for an earlier asset of the listing.
    pub own_bytes: u64,
    /// Per part: `{part, label, elem, len, bytes}` (bytes of the file, whether or not shared).
    pub parts: Vec<Value>,
}

/// The budget state of the library for the current capture.
#[derive(Clone, Debug)]
pub struct StorageBudget {
    /// The user's limit (`None`: the request sets none).
    pub allowance: Option<u64>,
    pub used_bytes: u64,
    pub assets: Vec<CountedAsset>,
    /// Superseded versions no admitted query reads (`{name, package, asset, storage_bytes}`; not counted).
    pub superseded: Vec<Value>,
    /// File identities already counted.
    counted: BTreeSet<(u64, u64)>,
}

impl StorageBudget {
    /// Count every usable admitted storage's asset for `capture` (see the module documentation).
    pub fn of_library(store: &ObjectStore, capture: &CurrentCapture, schema: &[TableDef], policy: &StoredDataPolicy, allowance: Option<u64>) -> Result<Self, AdmissionError> {
        Self::of_library_replacing(store, capture, schema, policy, allowance, &BTreeSet::new())
    }

    /// [`StorageBudget::of_library`] as it will stand once new versions of the storage names `replacing` are
    /// registered: their current versions that no admitted query reads become superseded and are not counted.
    pub fn of_library_replacing(
        store: &ObjectStore,
        capture: &CurrentCapture,
        schema: &[TableDef],
        policy: &StoredDataPolicy,
        allowance: Option<u64>,
        replacing: &BTreeSet<String>,
    ) -> Result<Self, AdmissionError> {
        let (serving, superseded) = serving_storages(store, capture, schema, policy, replacing)?;
        Self::of_serving(store, &serving, &superseded, allowance)
    }

    /// Count the assets of `serving` (from [`serving_storages`]); `superseded` are listed apart, not counted.
    pub fn of_serving(store: &ObjectStore, serving: &[AdmittedStorage], superseded: &[AdmittedStorage], allowance: Option<u64>) -> Result<Self, AdmissionError> {
        let mut budget = StorageBudget { allowance, used_bytes: 0, assets: vec![], superseded: vec![], counted: BTreeSet::new() };
        for storage in superseded {
            if let Some((id, asset)) = &storage.asset {
                budget.superseded.push(json!({"name":storage.package.name,"package":storage.package_id,"asset":id,"storage_bytes":asset.storage_bytes}));
            }
        }
        for storage in serving {
            if let Some((id, asset)) = &storage.asset {
                let directory = gendb_artifacts::verus::storage_asset_directory(store, asset).map_err(AdmissionError::tool)?;
                budget.count(storage, *id, asset, &directory)?;
            }
        }
        Ok(budget)
    }

    /// Bytes left under the allowance (`None`: no allowance).
    pub fn left_bytes(&self) -> Option<u64> {
        self.allowance.map(|a| a.saturating_sub(self.used_bytes))
    }

    /// Bytes of the part files under `directory` that this budget has not counted yet (a new asset's own bytes).
    pub fn uncounted_bytes(&self, directory: &Path) -> Result<u64, AdmissionError> {
        Ok(part_files(directory)?.into_iter().filter(|(identity, _)| !self.counted.contains(identity)).map(|(_, bytes)| bytes).sum())
    }

    /// Count the part files under `directory` not counted yet (a new asset joining the serving storage); their bytes.
    pub fn add_new(&mut self, directory: &Path) -> Result<u64, AdmissionError> {
        let mut bytes = 0;
        for (identity, size) in part_files(directory)? {
            if self.counted.insert(identity) {
                bytes += size;
            }
        }
        Ok(bytes)
    }

    /// Refuse (`storage_budget_exceeded`) when `bytes` more would exceed the allowance; `what` names them.
    pub fn check_room(&self, bytes: u64, what: &str) -> Result<(), AdmissionError> {
        match self.allowance {
            Some(allowance) if self.used_bytes.saturating_add(bytes) > allowance => Err(AdmissionError::refusal(format!(
                "storage_budget_exceeded: {what} needs {bytes} bytes; the admitted storages already use {} of the user's data_allowance of {allowance} bytes ({} left)",
                self.used_bytes,
                allowance.saturating_sub(self.used_bytes)
            ))),
            _ => Ok(()),
        }
    }

    /// The facts both roles read (CURRENT FACTS, Storage / `storage-budget.json`): allowance, used and left bytes, and every
    /// counted asset with its parts.
    pub fn facts(&self) -> Value {
        let assets: Vec<Value> = self
            .assets
            .iter()
            .map(|a| json!({"name":a.name,"package":a.package,"asset":a.asset,"own_bytes":a.own_bytes,"parts":a.parts}))
            .collect();
        json!({"allowance_bytes":self.allowance,"used_bytes":self.used_bytes,"left_bytes":self.left_bytes(),"assets":assets,"superseded":self.superseded,
            "counted":"the part files of the current data's asset of every usable admitted storage that is its name's newest version or is read by an admitted query package (in an engine library: exactly the storages the selected engine version reads), each file once (hard-linked parts of an extended storage count once); superseded unread versions, trial assets and unverified diagnostic builds are not counted",
            "enforced":"storage_budget_exceeded: at registration with the measured bytes, and before a build when a measured size estimate already exceeds what is left"})
    }

    fn count(&mut self, storage: &AdmittedStorage, id: ContentId, asset: &VerusStorageAssetV1, directory: &Path) -> Result<(), AdmissionError> {
        let files = part_files(directory)?;
        let labels = storage.description["parts"].as_array().cloned().unwrap_or_default();
        let parts: Vec<Value> = asset
            .parts
            .iter()
            .zip(&files)
            .enumerate()
            .map(|(index, ((elem, len), (_, bytes)))| json!({"part":index,"label":labels.get(index),"elem":elem,"len":len,"bytes":bytes}))
            .collect();
        let mut own_bytes = 0;
        for (identity, bytes) in files {
            if self.counted.insert(identity) {
                own_bytes += bytes;
            }
        }
        self.used_bytes = self.used_bytes.saturating_add(own_bytes);
        self.assets.push(CountedAsset { name: storage.package.name.clone(), package: storage.package_id, asset: id, own_bytes, parts });
        Ok(())
    }
}

/// The serving storage of the library (see the module documentation), as it will stand once new versions of the names
/// `replacing` are registered: every admitted storage version `policy` allows that is its name's current version, or
/// that an admitted query package reads; apart, the superseded versions no admitted query reads. In an engine library
/// with a selected engine version: exactly the storages that version reads ([`engine_serving_storages`]); a new version
/// of a name replaces nothing there, since being current does not make a version serve.
pub fn serving_storages(
    store: &ObjectStore,
    capture: &CurrentCapture,
    schema: &[TableDef],
    policy: &StoredDataPolicy,
    replacing: &BTreeSet<String>,
) -> Result<(Vec<AdmittedStorage>, Vec<AdmittedStorage>), AdmissionError> {
    if let Some(selected) = records::selected_engine(store).map_err(AdmissionError::tool)? {
        let uses: BTreeSet<ContentId> = selected.package.storage_uses.iter().map(|u| u.package).collect();
        return engine_serving_storages(store, capture, schema, policy, &uses);
    }
    let served = served_storage_packages(store)?;
    let (mut serving, mut superseded) = (vec![], vec![]);
    for storage in catalog::admitted_storages(store, capture, schema)? {
        if policy.ineligible(store, storage.package_id, &storage.package.name)?.is_some() {
            continue;
        }
        let current = storage.current && !replacing.contains(&storage.package.name);
        if current || served.contains(&storage.package_id) {
            serving.push(storage);
        } else {
            superseded.push(storage);
        }
    }
    Ok((serving, superseded))
}

/// The serving storage of an engine library once an engine version reading the storage packages `uses` is selected:
/// exactly those admitted versions (the ones `policy` allows); apart, as superseded, every other admitted version. The
/// storages they extend are not listed: their part files lie inside the extensions' assets by hard link, and
/// `storage::payload` adds them as holders.
pub fn engine_serving_storages(
    store: &ObjectStore,
    capture: &CurrentCapture,
    schema: &[TableDef],
    policy: &StoredDataPolicy,
    uses: &BTreeSet<ContentId>,
) -> Result<(Vec<AdmittedStorage>, Vec<AdmittedStorage>), AdmissionError> {
    let (mut serving, mut superseded) = (vec![], vec![]);
    for storage in catalog::admitted_storages(store, capture, schema)? {
        if policy.ineligible(store, storage.package_id, &storage.package.name)?.is_some() {
            continue;
        }
        if uses.contains(&storage.package_id) {
            serving.push(storage);
        } else {
            superseded.push(storage);
        }
    }
    Ok((serving, superseded))
}

/// Every storage package an admitted query package (over stored data) reads.
fn served_storage_packages(store: &ObjectStore) -> Result<BTreeSet<ContentId>, AdmissionError> {
    let mut served = BTreeSet::new();
    for object in store.list_kind(records::VERUS_PACKAGE_ADMISSION_V2_KIND).map_err(AdmissionError::tool)? {
        let admission: records::VerusPackageAdmissionV2 = object.decode().map_err(AdmissionError::tool)?;
        let package: records::VerusQueryPackageV3 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        served.extend(package.storage_uses.iter().map(|u| u.package));
    }
    Ok(served)
}

/// `((device, inode), bytes)` of every part file of a parts directory (`part-NNNN.bin`, in part order). Metadata only.
fn part_files(directory: &Path) -> Result<Vec<((u64, u64), u64)>, AdmissionError> {
    let mut files = vec![];
    for index in 0.. {
        let path = directory.join(format!("part-{index:04}.bin"));
        match std::fs::metadata(&path) {
            Ok(meta) => files.push(((meta.dev(), meta.ino()), meta.len())),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => break,
            Err(error) => return Err(AdmissionError::tool(format!("{}: {error}", path.display()))),
        }
    }
    Ok(files)
}
