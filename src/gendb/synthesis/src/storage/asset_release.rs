//! The general engine line's storage assets on a shared host : what the run library keeps,
//! what it releases, and the free space every asset build leaves. The schema and per-query lines use none of this
//! (their benches have no [`AssetUpkeep`]; nothing is released there).
//!
//! - **Kept.** Every asset of every head, at every capture: the main-line head's and each branch head's storages
//!   (`engine::asset_upkeep` names them). That is what the next evaluation reads without a rebuild: its parent's assets
//!   at the current scale and, at a later scale, the first scale's for its variants. Only derived storages (built from
//!   admitted storages: the storages an engine author adds) are ever released; the plain storages (the seeded flat
//!   storages, built from source columns) and any other storage that is not derived never are, and neither is a part
//!   file a derived asset shares by hard link (an extension's inherited flat parts lose only that asset's name for them).
//! - **Released** ([`release_superseded_assets`]): every published asset of a derived storage that admitted versions
//!   read and no head reads, at every capture; and a derived storage's asset whose directory is missing (removed
//!   outside GenDB, or a release stopped between its rename and its record), so its next use builds it instead of being
//!   refused. A storage that no admitted version reads (one registered by an admission still in progress) is never
//!   released. A release (`gendb_artifacts::verus::release_storage_asset`) removes the asset's directory and ends its
//!   key's stream with a release record (key, asset, bytes, reason, time): the key then has no asset, while the
//!   package, its stored builder, its sources and every version record stay.
//! - **Rebuilt.** A later use of a released asset (the final evaluation of an older version, a re-evaluation, a scale
//!   move, an author's trial) finds no asset and builds it again with the package's stored verified builder, its
//!   derivation sources' assets first (`storage::build::build_library_asset`, `storage::build::ensure_source_assets`).
//! - **Floor** ([`AssetUpkeep`]): before any asset build (a trial, an admitted storage's asset, a diagnostic build) the
//!   filesystem must keep the build's estimate plus [`SHARED_HOST_FLOOR_BYTES`] free; the session's disposable trials
//!   are reclaimed first, then the build is refused with `insufficient_storage`, stating the free space, the floor and
//!   the head's derived bytes ([`check_free_space`]). The facts show the same numbers ([`storage_assets_facts`]).

use crate::controller::records::now_unix_ms;
use crate::engine::tree::version_id;
use crate::query::assets::{SpaceNeed, check_free_storage, free_bytes_at};
use gendb_artifacts::verus::{
    self as records, VERUS_STORAGE_ASSET_KIND, VerusStorageAssetV1, VerusStorageUseV1, engine_versions, lock_storage_asset, release_storage_asset,
    resolve_admitted_storage, resolve_storage_asset, selected_engine, storage_asset_directory,
};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_verification::admission::AdmissionError;
use serde::Serialize;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::os::unix::fs::MetadataExt;
use std::path::Path;

/// The free space every asset build on the general line leaves besides its size estimate: 20 GiB, the user's rule for
/// this shared host (the run's operator pauses the run when `/` has less than 20 GB free, `df -B1G`), so GenDB never
/// takes the disk below it. Shown in the facts and in every refusal.
pub const SHARED_HOST_FLOOR_BYTES: u64 = 20 << 30;

/// The rule the facts state (CURRENT FACTS, Storage).
pub const KEEP_RULE: &str = "GenDB keeps the head's storage assets; older versions' derived assets are released and rebuilt by their verified builders when needed.";

/// How a general-line bench keeps the library's storage assets on the shared host (module documentation):
/// `BenchConfig::asset_upkeep`, `None` on the other lines.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct AssetUpkeep {
    /// The free space every asset build leaves besides its estimate.
    pub floor_bytes: u64,
}

impl AssetUpkeep {
    /// The general line's upkeep: the shared-host floor.
    pub const GENERAL_LINE: AssetUpkeep = AssetUpkeep { floor_bytes: SHARED_HOST_FLOOR_BYTES };
}

/// The free-space guard of one asset build writing under `path` (`query::assets::check_free_storage`; `need` carries
/// the floor when `upkeep` is set; `reclaim`: what the session freed first). On the general line a refusal also states
/// what the library `library` keeps: the head's derived storage assets and the rule.
pub fn check_free_space(upkeep: Option<&AssetUpkeep>, library: &Path, path: &Path, need: &SpaceNeed, reclaim: &Value) -> Result<(), AdmissionError> {
    match (upkeep, check_free_storage(path, need, reclaim)) {
        (Some(upkeep), Err(error)) => Err(AdmissionError::new(error.class, format!("{}. {}", error.message, kept_note(upkeep, library)))),
        (_, outcome) => outcome,
    }
}

/// What a refusal of the floor adds: the floor, what the library holds for the head, and the rule.
fn kept_note(upkeep: &AssetUpkeep, library: &Path) -> String {
    let floor = format!("GenDB keeps {} bytes ({} GiB) free on this shared host besides each build's estimate", upkeep.floor_bytes, upkeep.floor_bytes >> 30);
    let head = ObjectStore::open_existing(library).map_err(|e| e.to_string()).and_then(|store| head_assets(&store).map_err(|e| e.to_string()));
    let held = match head {
        Ok(HeadAssets { head: Some(head), bytes, assets, .. }) => format!("the library holds {bytes} bytes of the head {head}'s derived storage assets ({assets} assets, every scale)"),
        Ok(_) => "the library holds no engine version yet".to_string(),
        Err(error) => format!("the head's derived storage assets could not be measured ({error})"),
    };
    format!("{floor}; {held}. {KEEP_RULE}")
}

/// The derived storage assets the library holds for its selected engine version (the main-line head).
#[derive(Clone, Debug, Default, Serialize)]
pub struct HeadAssets {
    /// The head (`v003`); `None` before an engine version is admitted.
    pub head: Option<String>,
    /// The derived storages it reads.
    pub derived_storages: Vec<String>,
    /// Their published assets, at every capture.
    pub assets: usize,
    /// Their files (parts and manifest), each once by filesystem identity, without the files they share with an
    /// extended storage that is not derived (an extension's linked flat parts). Metadata only.
    pub bytes: u64,
}

/// [`HeadAssets`] of the library `store`.
pub fn head_assets(store: &ObjectStore) -> Result<HeadAssets, AdmissionError> {
    let Some(head) = selected_engine(store).map_err(AdmissionError::tool)? else { return Ok(HeadAssets::default()) };
    let mut derived: BTreeMap<ContentId, records::VerusStoragePackageV1> = BTreeMap::new();
    for storage_use in &head.package.storage_uses {
        let record = resolve_admitted_storage(store, storage_use.package).map_err(AdmissionError::tool)?;
        if record.derived_from.is_some() {
            derived.insert(storage_use.package, record);
        }
    }
    // The non-derived storages an extension links: their part files are not the head's derived bytes.
    let extended: BTreeSet<ContentId> = derived
        .values()
        .filter_map(|record| record.derived_from.as_ref().and_then(|d| d.extends.map(|k| d.sources[k].package)))
        .filter(|package| !derived.contains_key(package))
        .collect();
    let packages: BTreeSet<ContentId> = derived.keys().chain(&extended).copied().collect();
    let published = published_assets(store, &packages)?;
    let mut shared: BTreeSet<(u64, u64)> = BTreeSet::new();
    for (_, asset) in published.iter().filter(|(_, a)| extended.contains(&a.key.storage_package)) {
        for (identity, _) in part_files(&storage_asset_directory(store, asset).map_err(AdmissionError::tool)?) {
            shared.insert(identity);
        }
    }
    let (mut assets, mut bytes) = (0, 0u64);
    let mut seen = shared;
    for (_, asset) in published.iter().filter(|(_, a)| derived.contains_key(&a.key.storage_package)) {
        assets += 1;
        for (identity, len) in part_files(&storage_asset_directory(store, asset).map_err(AdmissionError::tool)?) {
            if seen.insert(identity) {
                bytes += len;
            }
        }
    }
    Ok(HeadAssets { head: Some(version_id(head.version - 1)), derived_storages: derived.values().map(|r| r.name.clone()).collect(), assets, bytes })
}

/// The facts of CURRENT FACTS, Storage (one line): the head's derived storage assets, the free space of the library's
/// filesystem now, the floor and the rule. A failure is stated in the value, never raised.
pub fn storage_assets_facts(library: &Path) -> Value {
    let head = ObjectStore::open_existing(library).map_err(|e| e.to_string()).and_then(|store| head_assets(&store).map_err(|e| e.to_string()));
    let mut facts = json!({"free_bytes":free_bytes_at(library),"floor_bytes":SHARED_HOST_FLOOR_BYTES,"rule":KEEP_RULE,"measured_unix_ms":now_unix_ms()});
    match head {
        Ok(head) => {
            facts["head"] = json!(head.head);
            facts["head_derived_bytes"] = json!(head.bytes);
            facts["head_derived_assets"] = json!(head.assets);
            facts["head_derived_storages"] = json!(head.derived_storages);
        }
        Err(error) => facts["error"] = json!(error),
    }
    facts
}

/// One head whose storage assets stay: its version and the storages it reads.
#[derive(Clone, Debug, Serialize)]
pub struct KeptHead {
    pub version: String,
    pub uses: Vec<VerusStorageUseV1>,
}

/// Release the library's superseded derived storage assets (module documentation): every published asset of a
/// derived storage that admitted versions read and none of `heads` reads, and a derived storage's asset whose
/// directory is missing, each under its key's lock with the reason (`why`: what triggered this pass). Returns the
/// pass's record: the heads, every release (storage, package, asset, the capture of its key, stored bytes, the bytes
/// its directory held and freed, the release record) and the totals.
pub fn release_superseded_assets(store: &ObjectStore, heads: &[KeptHead], why: &str) -> Result<Value, AdmissionError> {
    let kept: BTreeSet<ContentId> = heads.iter().flat_map(|h| h.uses.iter().map(|u| u.package)).collect();
    let head_names: Vec<&str> = heads.iter().map(|h| h.version.as_str()).collect();
    // The derived storages admitted versions read, with the versions that read them.
    let mut read_by: BTreeMap<ContentId, (String, Vec<String>)> = BTreeMap::new();
    for version in engine_versions(store).map_err(AdmissionError::tool)? {
        for storage_use in &version.package.storage_uses {
            let record = resolve_admitted_storage(store, storage_use.package).map_err(AdmissionError::tool)?;
            if record.derived_from.is_some() {
                read_by.entry(storage_use.package).or_insert_with(|| (record.name.clone(), vec![])).1.push(version_id(version.version - 1));
            }
        }
    }
    let at = now_unix_ms();
    let mut released = vec![];
    let (mut file_bytes, mut freed_bytes) = (0u64, 0u64);
    for (id, asset) in published_assets(store, &read_by.keys().copied().collect::<BTreeSet<_>>())? {
        let package = asset.key.storage_package;
        let (name, readers) = &read_by[&package];
        let missing = !storage_asset_directory(store, &asset).map_err(AdmissionError::tool)?.join("parts.json").is_file();
        let reason = match (kept.contains(&package), missing) {
            (false, _) => format!("superseded ({why}): derived storage {name}, read by {}, is read by no head ({})", readers.join(", "), head_names.join(", ")),
            (true, true) => format!("directory missing ({why}): derived storage {name}'s asset has no complete directory; its next use builds it again"),
            (true, false) => continue,
        };
        let lock = lock_storage_asset(store, asset.key.clone()).map_err(AdmissionError::tool)?;
        let Some(done) = release_storage_asset(store, &lock, id, &reason, at).map_err(AdmissionError::tool)? else { continue };
        file_bytes += done.file_bytes;
        freed_bytes += done.freed_bytes;
        released.push(json!({"storage":name,"package":package,"asset":id,"release":done.release,"capture":asset.key.tables,
            "storage_bytes":asset.storage_bytes,"file_bytes":done.file_bytes,"freed_bytes":done.freed_bytes,"reason":reason}));
    }
    Ok(json!({"at_unix_ms":at,"why":why,"rule":KEEP_RULE,"heads":heads,"released":released,"released_assets":released.len(),
        "file_bytes":file_bytes,"freed_bytes":freed_bytes,
        "meaning":"each released asset's directory is removed and its key's stream ends with a release record in the library; the package, its stored builder and every version record stay, and a later use builds the asset again"}))
}

/// The published assets (each its key's current asset) of the storage packages `packages`, at every capture.
fn published_assets(store: &ObjectStore, packages: &BTreeSet<ContentId>) -> Result<Vec<(ContentId, VerusStorageAssetV1)>, AdmissionError> {
    let mut published = vec![];
    for object in store.list_kind(VERUS_STORAGE_ASSET_KIND).map_err(AdmissionError::tool)? {
        let asset: VerusStorageAssetV1 = object.decode().map_err(AdmissionError::tool)?;
        if packages.contains(&asset.key.storage_package)
            && resolve_storage_asset(store, &asset.key).map_err(AdmissionError::tool)?.is_some_and(|(current, _)| current == object.id)
        {
            published.push((object.id, asset));
        }
    }
    Ok(published)
}

/// The files of an asset directory with their filesystem identity and length (none when it is missing).
fn part_files(directory: &Path) -> Vec<((u64, u64), u64)> {
    let Ok(entries) = std::fs::read_dir(directory) else { return vec![] };
    entries.flatten().filter_map(|entry| entry.metadata().ok()).filter(|meta| meta.is_file()).map(|meta| ((meta.dev(), meta.ino()), meta.len())).collect()
}

#[cfg(test)]
pub(crate) mod tests;
