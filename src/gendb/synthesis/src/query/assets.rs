//! Stored-asset space and the trial assets of one author session.
//!
//! **Free space.** Before an asset build (only when the key has no asset: a reuse needs no space) the filesystem it
//! writes to must hold the 4 GiB margin (on the general engine line its shared-host floor instead,
//! `storage::asset_release`) plus a size estimate, refused by name (`insufficient_storage`) before anything is built. The estimate is, in this order: the exact size of an earlier build of the same key (`prior_same_key`), the
//! measured size of the newest earlier build of the same storage name in this session or library
//! (`same_storage_measured`), or the declared columns at their ABI widths (`canonical_columns`). While the build
//! writes, the parts writer keeps the same margin free, chunk by chunk (`gendb_storage::io::PartFilesWriter`); a build
//! stopped there, or one that still runs out of space, fails cleanly (`admission::storage::disk_full_evidence`).
//!
//! **Trial assets.** The asset of a storage that is not admitted yet is built into `<session>/trial-assets/<key id>/`,
//! outside the library, and enters the library only when the storage is registered (promotion by rename, same asset
//! id). The ledger `<session>/trial-assets.json` records every trial before anything uses it, so a trial directory it
//! does not name was never used. Only this session's `Present` trials are ever removed, and only when all hold:
//! not protected (an eligible evaluation used it: recorded here before the evaluation record is written, and
//! reconciled from the session's durable evaluation records and controller ledger on every reclaim; an unreadable
//! record reclaims nothing), not used by the job asking for space, not the newest build of its storage name in this
//! session (the current candidate's asset: only superseded builds are disposable under pressure), its key not published
//! and its package not admitted in the library. When: under disk pressure before a build (least recently used first), at session close
//! (all but the kept ones), or by [`reclaim_ended_session`] for a session whose controller has ended. A removed trial
//! needed again is rebuilt by the same stored library and reported. Build records, evaluations and every library
//! object stay. On the general line an admission also promotes the session's builds of its new storages at other
//! captures (the first scale's, for the variants) into the library ([`TrialAssets::promote_admitted`]).
//!
//! **Libraries.** One session of a run of several workloads builds trials for every workload's library (its bench
//! views one workload at a time, `engine::stage::WorkloadBench`), and a storage-family instance has the family's name
//! in every library. A trial belongs to the library that holds its package: the package is published there before its
//! trial is built (`storage::build::check_storage`). So every lookup by storage name sees only the trials of the
//! library it is asked for (the newest build's measured bytes, the present trials an equal builder reuses, the newest
//! build that pressure keeps), and pressure from one library's build never removes another library's trial.

use crate::controller::Trial;
use crate::controller::records::{now_unix_ms, read_json, write_json_atomic};
use crate::file_lock::FileLock;
use gendb_artifacts::asset_directory::remove_build_directory;
use gendb_artifacts::verus::{self as records, VerusStorageAssetKeyV1, VerusStoragePackageV1};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::storage::{TrialAsset, promote_trial_asset};
pub use gendb_verification::admission::storage::{STORAGE_MARGIN_BYTES, free_bytes_at};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// The session directory of trial assets.
pub const TRIAL_ASSETS_DIRECTORY: &str = "trial-assets";
const LEDGER_FILE: &str = "trial-assets.json";
const LEDGER_FORMAT: u32 = 1;

/// What one asset build needs free (see the module documentation).
#[derive(Clone, Debug, Serialize)]
pub struct SpaceNeed {
    /// `prior_same_key`, `same_storage_measured`, `canonical_columns` or `unknown`.
    pub basis: &'static str,
    pub estimate_bytes: Option<u64>,
    /// The free space the build must leave besides its estimate when it is more than the margin: the general engine
    /// line's shared-host floor (`storage::asset_release::AssetUpkeep`); absent (and not recorded) elsewhere.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub floor_bytes: Option<u64>,
}

impl SpaceNeed {
    /// The estimate from the first available basis: an earlier build of the same key, the newest measured build of the
    /// same storage name, the canonical column bytes.
    pub fn new(prior_same_key: Option<u64>, same_storage: Option<u64>, canonical: Option<u64>) -> Self {
        let (basis, estimate_bytes) = match (prior_same_key, same_storage, canonical) {
            (Some(bytes), _, _) => ("prior_same_key", Some(bytes)),
            (None, Some(bytes), _) => ("same_storage_measured", Some(bytes)),
            (None, None, Some(bytes)) => ("canonical_columns", Some(bytes)),
            (None, None, None) => ("unknown", None),
        };
        Self { basis, estimate_bytes, floor_bytes: None }
    }

    /// The same need with `floor` (when given) kept free besides the estimate, in place of the margin.
    pub fn with_floor(mut self, floor: Option<u64>) -> Self {
        self.floor_bytes = floor;
        self
    }

    /// What the build leaves free besides its estimate: the floor, at least the margin.
    pub fn floor(&self) -> u64 {
        self.floor_bytes.map_or(STORAGE_MARGIN_BYTES, |floor| floor.max(STORAGE_MARGIN_BYTES))
    }

    /// Free bytes the build requires (and reclaim aims for): the floor (else the margin) plus the estimate.
    pub fn required_bytes(&self) -> u64 {
        self.floor().saturating_add(self.estimate_bytes.unwrap_or(0))
    }
}

/// Free bytes on the filesystem of `path` (its nearest existing ancestor).
fn free_at(path: &Path) -> Option<u64> {
    free_bytes_at(path.ancestors().find(|p| p.exists()).unwrap_or(path))
}

/// The free-space guard before one asset build writing under `path`; `reclaim`: what the session freed first.
pub fn check_free_storage(path: &Path, need: &SpaceNeed, reclaim: &Value) -> Result<(), AdmissionError> {
    let free = free_at(path).unwrap_or(u64::MAX);
    if free < need.required_bytes() {
        let kept = match need.floor_bytes {
            None => format!("margin {STORAGE_MARGIN_BYTES}"),
            Some(_) => format!("the shared host's floor {}", need.floor()),
        };
        return Err(AdmissionError::tool(format!(
            "insufficient_storage: {free} bytes free on the filesystem of {}; this build requires {} ({kept} + estimate {:?}, basis {}); session trial reclaim: {reclaim} (refused before building; no candidate is implicated)",
            path.display(),
            need.required_bytes(),
            need.estimate_bytes,
            need.basis,
        )));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum TrialState {
    /// Its directory holds the sealed build.
    Present,
    /// Registered: its directory was renamed into the library.
    Promoted,
    /// Removed by its session.
    Reclaimed,
}

/// One key's trial in the ledger.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct TrialEntry {
    package: ContentId,
    /// The storage name of the package (empty in ledgers written before names were recorded: never superseded).
    #[serde(default)]
    name: String,
    /// The ledger's use counter when this build was recorded: the newest build of a name is its current candidate's.
    #[serde(default)]
    built: u64,
    trial: TrialAsset,
    state: TrialState,
    last_use: u64,
    /// Why it is kept (an eligible evaluation); pressure never removes a protected trial.
    protected: BTreeSet<String>,
    /// Earlier builds of this key that were removed: `{asset, bytes, reason, unix_ms}`.
    reclaimed: Vec<Value>,
}

impl TrialEntry {
    fn bytes(&self) -> u64 {
        self.trial.asset.storage_bytes
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct TrialLedger {
    format_version: u32,
    /// Use counter (least recently used order).
    uses: u64,
    /// By key id.
    trials: BTreeMap<String, TrialEntry>,
}

/// The trial assets of one session (see the module documentation).
pub struct TrialAssets {
    session: PathBuf,
    ledger: TrialLedger,
}

impl TrialAssets {
    /// The ledger of the session at `session` (empty when absent). An unreadable ledger is refused.
    pub fn open(session: &Path) -> Result<Self, AdmissionError> {
        let path = session.join(LEDGER_FILE);
        let ledger = if path.exists() {
            let ledger: TrialLedger = read_json(&path).map_err(|e| AdmissionError::tool(format!("unreadable trial-asset ledger (nothing is reclaimed or reused): {e}")))?;
            if ledger.format_version != LEDGER_FORMAT {
                return Err(AdmissionError::tool(format!("trial-asset ledger {} has format {}", path.display(), ledger.format_version)));
            }
            ledger
        } else {
            TrialLedger { format_version: LEDGER_FORMAT, uses: 0, trials: BTreeMap::new() }
        };
        Ok(Self { session: session.to_path_buf(), ledger })
    }

    /// `<session>/trial-assets`.
    pub fn root(&self) -> PathBuf {
        self.session.join(TRIAL_ASSETS_DIRECTORY)
    }

    fn save(&self) -> Result<(), AdmissionError> {
        write_json_atomic(&self.session.join(LEDGER_FILE), &self.ledger).map_err(AdmissionError::tool)
    }

    fn touch(&mut self, key: &str) {
        self.ledger.uses += 1;
        if let Some(entry) = self.ledger.trials.get_mut(key) {
            entry.last_use = self.ledger.uses;
        }
    }

    /// The present trial of `key` (its sealed directory complete), marked used. A ledger entry whose directory is gone
    /// becomes `Reclaimed`; a directory the ledger does not name was never used and is removed.
    pub fn present(&mut self, key: &VerusStorageAssetKeyV1) -> Result<Option<TrialAsset>, AdmissionError> {
        let name = key_name(key)?;
        let entry = self.ledger.trials.get(&name).map(|e| (e.state, e.trial.clone()));
        match entry {
            Some((TrialState::Present, trial)) if trial.directory.join("parts.json").is_file() => {
                self.touch(&name);
                self.save()?;
                Ok(Some(trial))
            }
            Some((TrialState::Present, _)) => {
                self.mark_reclaimed(&name, "directory_absent", 0)?;
                Ok(None)
            }
            Some(_) => Ok(None),
            None => {
                remove_build_directory(&self.root().join(&name)).map_err(AdmissionError::tool)?;
                Ok(None)
            }
        }
    }

    /// Exact stored bytes of an earlier, removed build of `key` (the reliable estimate), if any.
    pub fn prior_bytes(&self, key: &VerusStorageAssetKeyV1) -> Option<u64> {
        let entry = self.ledger.trials.get(&key_name(key).ok()?)?;
        entry.reclaimed.last().and_then(|r| r["bytes"].as_u64()).or((entry.state == TrialState::Reclaimed).then(|| entry.bytes()))
    }

    /// Measured stored bytes of the newest build of storage `name` of the library `store` in this session, if any.
    pub fn newest_bytes_of(&self, store: &ObjectStore, name: &str) -> Option<u64> {
        self.of_name_in(store, name).max_by_key(|e| e.built).map(TrialEntry::bytes)
    }

    /// The present trials of storage `name` of the library `store` in this session: `(package, trial)`, newest build
    /// first.
    pub fn present_of_name(&self, store: &ObjectStore, name: &str) -> Vec<(ContentId, TrialAsset)> {
        let mut found: Vec<&TrialEntry> =
            self.of_name_in(store, name).filter(|e| e.state == TrialState::Present && e.trial.directory.join("parts.json").is_file()).collect();
        found.sort_by_key(|e| std::cmp::Reverse(e.built));
        found.into_iter().map(|e| (e.package, e.trial.clone())).collect()
    }

    /// Whether the trial `entry` of the library `store` is the newest build of its storage name there (the current
    /// candidate's asset).
    fn is_newest_of_name(&self, store: &ObjectStore, entry: &TrialEntry) -> bool {
        entry.name.is_empty() || !self.of_name_in(store, &entry.name).any(|other| other.built > entry.built)
    }

    /// The ledger's trials of storage `name` (none for an empty name: ledgers written before names were recorded)
    /// whose package the library `store` holds (module documentation, "Libraries").
    fn of_name_in<'a>(&'a self, store: &'a ObjectStore, name: &'a str) -> impl Iterator<Item = &'a TrialEntry> {
        self.ledger.trials.values().filter(move |e| !name.is_empty() && e.name == name && holds_package(store, e))
    }

    /// Record a new trial of `package` (storage `name`) before anything uses it.
    pub fn record_built(&mut self, package: ContentId, name: &str, trial: &TrialAsset) -> Result<(), AdmissionError> {
        let key = key_name(&trial.asset.key)?;
        let reclaimed = self.ledger.trials.remove(&key).map(|e| e.reclaimed).unwrap_or_default();
        self.ledger.uses += 1;
        let entry = TrialEntry {
            package,
            name: name.to_string(),
            built: self.ledger.uses,
            trial: trial.clone(),
            state: TrialState::Present,
            last_use: 0,
            protected: BTreeSet::new(),
            reclaimed,
        };
        self.ledger.trials.insert(key.clone(), entry);
        self.touch(&key);
        self.save()
    }

    /// Record that the trial `asset` was registered (its directory is now the library's).
    pub fn record_promoted(&mut self, asset: ContentId) -> Result<(), AdmissionError> {
        for entry in self.ledger.trials.values_mut().filter(|e| e.trial.id == asset) {
            entry.state = TrialState::Promoted;
        }
        self.save()
    }

    /// Publish this session's present trials of the admitted packages `packages` into the library: the general line's
    /// fix of the first-scale leak. A session at a later scale builds a new storage's trial at the first scale too (for
    /// its variants); once the storage is admitted, that build is its asset there, exactly as a scale move would build
    /// it (the same stored builder over the same input), so it is promoted by rename with the same asset id instead of
    /// being kept in the session and built a second time into the library. A key the library already holds keeps the
    /// library's asset, and the trial is removed. Returns what was promoted and removed.
    pub fn promote_admitted(&mut self, store: &ObjectStore, packages: &BTreeSet<ContentId>) -> Result<Value, AdmissionError> {
        let names: Vec<String> =
            self.ledger.trials.iter().filter(|(_, e)| e.state == TrialState::Present && packages.contains(&e.package)).map(|(k, _)| k.clone()).collect();
        let (mut promoted, mut removed) = (vec![], vec![]);
        for name in names {
            let trial = self.ledger.trials[&name].trial.clone();
            if !trial.directory.join("parts.json").is_file() {
                self.mark_reclaimed(&name, "directory_absent", 0)?;
                continue;
            }
            match promote_trial_asset(store, &trial) {
                Ok(asset) => {
                    self.record_promoted(trial.id)?;
                    promoted.push(json!({"asset":asset.id,"bytes":asset.asset.storage_bytes,"directory":asset.directory,"key":asset.asset.key}));
                }
                Err(error) if error.message.starts_with("asset_key_already_published") => removed.push(self.remove(&name, "library_holds_the_key")?),
                Err(error) => return Err(error),
            }
        }
        Ok(json!({"promoted":promoted,"removed":removed}))
    }

    /// Protect the trials among `assets` for `reason` (an eligible evaluation); durable before the caller records it.
    pub fn protect(&mut self, assets: &BTreeSet<ContentId>, reason: &str) -> Result<(), AdmissionError> {
        for entry in self.ledger.trials.values_mut().filter(|e| assets.contains(&e.trial.id)) {
            entry.protected.insert(reason.to_string());
        }
        self.save()
    }

    /// Under disk pressure before a build writing under the trial root: remove disposable trials (superseded builds,
    /// see the module documentation), least recently used first, until the filesystem has the need's required bytes
    /// free or none is left. `store`: the library of the build (only its trials are disposable here); `keep`: the
    /// asking job's assets.
    pub fn reclaim_for(&mut self, store: &ObjectStore, need: &SpaceNeed, keep: &BTreeSet<ContentId>) -> Result<Value, AdmissionError> {
        let target = need.required_bytes();
        let free_before = free_at(&self.root());
        if free_before.is_none_or(|free| free >= target) {
            return Ok(json!({"free_bytes":free_before,"target_bytes":target,"reclaimed":[]}));
        }
        let durable = match durable_eligible_assets(&self.session) {
            Ok(durable) => durable,
            Err(error) => return Ok(json!({"free_bytes":free_before,"target_bytes":target,"reclaimed":[],"refused":error.to_string()})),
        };
        let mut order: Vec<(u64, String)> = self.ledger.trials.iter().filter(|(_, e)| e.state == TrialState::Present).map(|(k, e)| (e.last_use, k.clone())).collect();
        order.sort();
        let (mut reclaimed, mut held) = (vec![], vec![]);
        for (_, name) in order {
            if free_at(&self.root()).is_some_and(|free| free >= target) {
                break;
            }
            let entry = &self.ledger.trials[&name];
            let hold = if !entry.protected.is_empty() {
                Some(format!("protected: {:?}", entry.protected))
            } else if durable.contains(&entry.trial.id) {
                Some("used by an eligible evaluation of this session".into())
            } else if keep.contains(&entry.trial.id) {
                Some("used by the job asking for space".into())
            } else if !holds_package(store, entry) {
                Some("a trial of another library (another workload of the run): only that library's builds reclaim it".into())
            } else if self.is_newest_of_name(store, entry) {
                Some(format!("the newest build of storage {} of this library in this session (the current candidate's)", entry.name))
            } else {
                library_hold(store, entry)
            };
            match hold {
                Some(reason) => held.push(json!({"asset":entry.trial.id,"bytes":entry.bytes(),"held":reason})),
                None => reclaimed.push(self.remove(&name, "disk_pressure_superseded")?),
            }
        }
        Ok(json!({"free_bytes_before":free_before,"free_bytes_after":free_at(&self.root()),"target_bytes":target,"reclaimed":reclaimed,"held":held}))
    }

    /// At session close (qualification and serving done): remove every present trial except those among `keep`
    /// (the best eligible candidate's when nothing qualified) and those the library holds.
    pub fn release_at_close(&mut self, store: &ObjectStore, keep: &BTreeSet<ContentId>) -> Result<Value, AdmissionError> {
        let names: Vec<String> = self.ledger.trials.iter().filter(|(_, e)| e.state == TrialState::Present).map(|(k, _)| k.clone()).collect();
        let (mut reclaimed, mut kept) = (vec![], vec![]);
        for name in names {
            let entry = &self.ledger.trials[&name];
            let hold = if keep.contains(&entry.trial.id) { Some("best eligible candidate (nothing qualified)".to_string()) } else { library_hold(store, entry) };
            match hold {
                Some(reason) => kept.push(json!({"asset":entry.trial.id,"bytes":entry.bytes(),"directory":entry.trial.directory,"kept":reason})),
                None => reclaimed.push(self.remove(&name, "session_closed")?),
            }
        }
        Ok(json!({"reclaimed":reclaimed,"kept":kept}))
    }

    /// Remove the present trial `name`'s directory and record it.
    fn remove(&mut self, name: &str, reason: &str) -> Result<Value, AdmissionError> {
        let directory = self.ledger.trials[name].trial.directory.clone();
        let bytes = remove_build_directory(&directory).map_err(AdmissionError::tool)?;
        self.mark_reclaimed(name, reason, bytes)?;
        Ok(json!({"asset":self.ledger.trials[name].trial.id,"bytes":bytes,"directory":directory,"reason":reason}))
    }

    fn mark_reclaimed(&mut self, name: &str, reason: &str, bytes: u64) -> Result<(), AdmissionError> {
        let entry = self.ledger.trials.get_mut(name).expect("a ledger entry");
        entry.state = TrialState::Reclaimed;
        entry.reclaimed.push(json!({"asset":entry.trial.id,"bytes":entry.trial.asset.storage_bytes,"removed_bytes":bytes,"reason":reason,"unix_ms":now_unix_ms()}));
        self.save()
    }
}

fn key_name(key: &VerusStorageAssetKeyV1) -> Result<String, AdmissionError> {
    Ok(key.identity().map_err(AdmissionError::tool)?.to_hex())
}

/// Whether the library `store` holds the package of the trial `entry`, so the trial is that library's (module
/// documentation, "Libraries").
fn holds_package(store: &ObjectStore, entry: &TrialEntry) -> bool {
    store.object_path(entry.package).is_file()
}

/// Why the library holds a trial (fail closed: an unreadable record holds it too): its key is published or its
/// package admitted. Every admission path (storage registration, workload and query qualification) publishes the
/// asset first, and a query package can name only a published asset.
fn library_hold(store: &ObjectStore, entry: &TrialEntry) -> Option<String> {
    let check = || -> Result<Option<String>, String> {
        if records::resolve_storage_asset(store, &entry.trial.asset.key).map_err(|e| e.to_string())?.is_some() {
            return Ok(Some("its key is published in the library".into()));
        }
        let package: VerusStoragePackageV1 = store.read(entry.package).and_then(|o| o.decode()).map_err(|e| e.to_string())?;
        let admitted = records::storage_versions(store, &package.name).map_err(|e| e.to_string())?.iter().any(|(_, a)| a.package == entry.package);
        Ok(admitted.then(|| "its package is admitted".into()))
    };
    check().unwrap_or_else(|error| Some(format!("library records unreadable: {error}")))
}

/// Every asset an eligible evaluation of the session at `session` used, from its durable records: the controller
/// ledger and every evaluation record under `iterations/` (a `"asset"` id anywhere inside an object with
/// `"eligible": true`). An unreadable record is an error, so nothing is reclaimed.
pub fn durable_eligible_assets(session: &Path) -> Result<BTreeSet<ContentId>, AdmissionError> {
    let mut files = vec![session.join("ledger.json")];
    evaluation_records(&session.join("iterations"), &mut files)?;
    let mut assets = BTreeSet::new();
    for file in files.iter().filter(|f| f.exists()) {
        let value: Value = read_json(file).map_err(|e| AdmissionError::tool(format!("unreadable session record, nothing reclaimed: {e}")))?;
        collect_eligible_assets(&value, false, &mut assets);
    }
    Ok(assets)
}

/// Every asset id an evaluation names (`"asset"` ids at any depth).
pub fn evaluation_assets(evaluation: &Value) -> BTreeSet<ContentId> {
    let mut assets = BTreeSet::new();
    collect_eligible_assets(evaluation, true, &mut assets);
    assets
}

/// The trial assets a session keeps at close: none when a candidate qualified (its storages are registered, so in
/// the library), else the assets of its best eligible evaluation (lowest score).
pub fn close_keep(trials: &[Trial], qualified: bool) -> BTreeSet<ContentId> {
    if qualified {
        return BTreeSet::new();
    }
    let best = trials.iter().filter(|t| t.eligible()).min_by(|a, b| a.score_ns().total_cmp(&b.score_ns()));
    best.map(|t| evaluation_assets(&t.evaluation)).unwrap_or_default()
}

fn evaluation_records(directory: &Path, out: &mut Vec<PathBuf>) -> Result<(), AdmissionError> {
    let entries = match std::fs::read_dir(directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(AdmissionError::tool(format!("{}: {error}", directory.display()))),
    };
    for entry in entries {
        let entry = entry.map_err(|e| AdmissionError::tool(format!("{}: {e}", directory.display())))?;
        let (path, name) = (entry.path(), entry.file_name().to_string_lossy().to_string());
        if entry.file_type().map_err(AdmissionError::tool)?.is_dir() {
            evaluation_records(&path, out)?;
        } else if name.ends_with(".json") && name.contains("evaluation") {
            out.push(path);
        }
    }
    Ok(())
}

fn collect_eligible_assets(value: &Value, eligible: bool, out: &mut BTreeSet<ContentId>) {
    match value {
        Value::Object(fields) => {
            let eligible = eligible || fields.get("eligible") == Some(&Value::Bool(true));
            for (name, field) in fields {
                if let (true, "asset", Some(Ok(id))) = (eligible, name.as_str(), field.as_str().map(ContentId::parse_hex)) {
                    out.insert(id);
                }
                collect_eligible_assets(field, eligible, out);
            }
        }
        Value::Array(items) => items.iter().for_each(|item| collect_eligible_assets(item, eligible, out)),
        _ => {}
    }
}

/// The explicit command for a session whose controller has ended: list (and with `apply`, remove) its present
/// trials that are not protected, not used by an eligible evaluation, not among `keep` and not held by the library,
/// plus leftover `<key>.building` directories. Refused while any process holds the session's `controller.lock`
/// (which it holds for the whole command). Never touches the library.
pub fn reclaim_ended_session(session: &Path, library: &Path, keep: &BTreeSet<ContentId>, apply: bool) -> Result<Value, AdmissionError> {
    let _lock = hold_ended_controller_lock(session)?;
    let store = ObjectStore::open_existing(library).map_err(AdmissionError::tool)?;
    let durable = durable_eligible_assets(session)?;
    let mut trials = TrialAssets::open(session)?;
    let names: Vec<String> = trials.ledger.trials.iter().filter(|(_, e)| e.state == TrialState::Present).map(|(k, _)| k.clone()).collect();
    let (mut candidates, mut held) = (vec![], vec![]);
    for name in names {
        let entry = &trials.ledger.trials[&name];
        let hold = if !entry.protected.is_empty() || durable.contains(&entry.trial.id) {
            Some("used by an eligible evaluation of this session".to_string())
        } else if keep.contains(&entry.trial.id) {
            Some("kept by the command".into())
        } else {
            library_hold(&store, entry)
        };
        match hold {
            Some(reason) => held.push(json!({"asset":entry.trial.id,"bytes":entry.bytes(),"held":reason})),
            None => candidates.push(name),
        }
    }
    let building: Vec<PathBuf> = match std::fs::read_dir(trials.root()) {
        Ok(entries) => entries.filter_map(|e| e.ok()).map(|e| e.path()).filter(|p| p.extension().is_some_and(|x| x == "building")).collect(),
        Err(_) => vec![],
    };
    let mut removed = vec![];
    if apply {
        for name in &candidates {
            removed.push(trials.remove(name, "ended_session_command")?);
        }
        for path in &building {
            removed.push(json!({"directory":path,"bytes":remove_build_directory(path).map_err(AdmissionError::tool)?,"reason":"interrupted_build"}));
        }
    }
    let listed: Vec<Value> = candidates.iter().map(|n| json!({"asset":trials.ledger.trials[n].trial.id,"bytes":trials.ledger.trials[n].bytes(),"directory":trials.ledger.trials[n].trial.directory})).collect();
    Ok(json!({"session":session,"applied":apply,"disposable":listed,"interrupted_builds":building,"held":held,"removed":removed,
        "scope":"only this session's run-local trial assets; the library is never modified"}))
}

/// Hold `<session>/controller.lock` exclusively without waiting (the controller holds it while it runs).
fn hold_ended_controller_lock(session: &Path) -> Result<FileLock, AdmissionError> {
    let path = session.join("controller.lock");
    if !path.is_file() {
        return Err(AdmissionError::missing_input(format!("{} is not an author session directory (no controller.lock)", session.display())));
    }
    let file = std::fs::OpenOptions::new().read(true).write(true).open(&path).map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))?;
    FileLock::acquire(file, libc::LOCK_EX | libc::LOCK_NB)
        .map_err(|_| AdmissionError::refusal(format!("the session's controller is running ({} is held); nothing reclaimed", path.display())))
}

#[cfg(test)]
mod tests;
