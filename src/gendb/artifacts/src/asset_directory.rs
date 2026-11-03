//! Stored asset directories inside a library: `assets/<name>/` holds the parts a storage builder wrote
//! (`part-NNNN.bin` and `parts.json`), immutable once placed. Records name such a directory only by its
//! library-relative path `assets/<64 hex>`, so a library can be moved or renamed as a whole and never depends on a run's
//! output directory.
//!
//! A build writes into a fresh staging directory `assets/.staging/<name>.<pid>-<n>/` (same filesystem, outside
//! `objects/`, so record discovery never reads payload). Placement renames it to its final name (no copy, no rewrite),
//! refuses an existing name, makes the directory read-only (0555; part files are written 0444) and syncs the parent. A
//! failed build's staging directory is removed by its builder; one left by a crash is removed under the name's lock
//! before the next build of that name ([`ObjectStore::remove_stale_asset_staging`]). The build of a storage that is
//! not admitted yet is written outside the library, into its session's trial directory, and placed by the same rename
//! only when the storage is registered ([`ObjectStore::place_trial_asset_directory`]). A crash after the rename and
//! before the owning record leaves a directory no record names: it is never served, and a later placement under that
//! name is refused (`unrecorded_asset_directory`) rather than overwritten. The release of an asset (its record's
//! caller decides it) moves its directory into the staging directory under the same name form and removes it there
//! ([`ObjectStore::retire_asset_directory`], [`ObjectStore::remove_retired_asset_directory`]); a removal a crash
//! interrupted is a stale staged build of that name.
//!
//! One builder per asset name: [`ObjectStore::lock_asset_name`] takes an exclusive advisory lock
//! (`assets/.locks/<name>.lock`, `flock`) that callers hold from the lookup of an asset until its publication, across
//! processes and threads; other names are never blocked. Lock files are empty and stay in place.
//!
//! Nothing here reads, hashes or rescans part payload.

use crate::content_id::ContentId;
use crate::object_store::{ObjectStore, StoreError};
use std::fs::File;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// Directory of stored assets under a library root.
pub const ASSETS_DIRECTORY: &str = "assets";
const STAGING_DIRECTORY: &str = ".staging";
const LOCKS_DIRECTORY: &str = ".locks";
/// The commit point a builder writes last; a staged directory without it is not a complete build.
const PARTS_MANIFEST: &str = "parts.json";

fn refused(path: &Path, reason: &str) -> StoreError {
    StoreError::AssetDirectory { path: path.to_owned(), reason: reason.to_string() }
}

/// The exclusive lock of one asset name, held until dropped (see the module documentation).
#[derive(Debug)]
pub struct AssetNameLock {
    name: ContentId,
    _file: File,
}

impl AssetNameLock {
    /// The asset name this lock serializes.
    pub fn name(&self) -> ContentId {
        self.name
    }
}

impl ObjectStore {
    /// Wait for, then hold, the exclusive lock of asset name `name` (for example an asset key identity).
    pub fn lock_asset_name(&self, name: ContentId) -> Result<AssetNameLock, StoreError> {
        let locks = self.root().join(ASSETS_DIRECTORY).join(LOCKS_DIRECTORY);
        std::fs::create_dir_all(&locks).map_err(|error| StoreError::io(&locks, error))?;
        let path = locks.join(format!("{}.lock", name.to_hex()));
        let file = std::fs::OpenOptions::new()
            .create(true)
            .truncate(false)
            .write(true)
            .open(&path)
            .map_err(|error| StoreError::io(&path, error))?;
        file.lock().map_err(|error| StoreError::io(&path, error))?;
        Ok(AssetNameLock { name, _file: file })
    }

    /// Whether an asset directory of name `name` has been placed (recorded or not). Metadata only.
    pub fn asset_directory_exists(&self, name: ContentId) -> bool {
        self.root().join(ASSETS_DIRECTORY).join(name.to_hex()).exists()
    }

    /// A fresh, not yet existing staging directory for one build of the locked name, `<name>.<pid>-<n>`; its parent
    /// exists. The builder creates it.
    pub fn fresh_asset_staging_directory(&self, lock: &AssetNameLock) -> Result<PathBuf, StoreError> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let staging = self.root().join(ASSETS_DIRECTORY).join(STAGING_DIRECTORY);
        std::fs::create_dir_all(&staging).map_err(|error| StoreError::io(&staging, error))?;
        loop {
            let path = staging.join(format!("{}.{}-{}", lock.name.to_hex(), std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
            if !path.exists() {
                return Ok(path);
            }
        }
    }

    /// Remove every staged build of the locked name (`.staging/<name>.*`): under the name's lock no builder of that
    /// name is running, so each is a failed or crashed build that no record names. Returns the bytes removed (file
    /// metadata). Staging directories of other names and of the earlier unnamed form (`<pid>-<n>`) are never touched.
    pub fn remove_stale_asset_staging(&self, lock: &AssetNameLock) -> Result<u64, StoreError> {
        let staging = self.root().join(ASSETS_DIRECTORY).join(STAGING_DIRECTORY);
        let prefix = format!("{}.", lock.name.to_hex());
        let entries = match std::fs::read_dir(&staging) {
            Ok(entries) => entries,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(0),
            Err(error) => return Err(StoreError::io(&staging, error)),
        };
        let mut removed = 0;
        for entry in entries {
            let path = entry.map_err(|error| StoreError::io(&staging, error))?.path();
            if path.file_name().and_then(|n| n.to_str()).is_some_and(|n| n.starts_with(&prefix)) {
                removed += remove_build_directory(&path)?;
            }
        }
        Ok(removed)
    }

    /// Place the complete staged build `staged` (a directory directly under this library's asset staging directory,
    /// with its `parts.json`) as the immutable asset directory named `name`; returns its library-relative path.
    pub fn place_asset_directory(&self, staged: &Path, name: ContentId) -> Result<String, StoreError> {
        let assets = self.root().join(ASSETS_DIRECTORY);
        if staged.parent() != Some(assets.join(STAGING_DIRECTORY).as_path()) || !staged.is_dir() {
            return Err(refused(staged, "not a staged asset build of this library"));
        }
        if !staged.join(PARTS_MANIFEST).is_file() {
            return Err(refused(staged, "staged asset build has no parts.json (incomplete build)"));
        }
        self.place_by_rename(staged, name)
    }

    /// Place the complete, sealed build `trial` of an unadmitted storage (a session's run-local trial directory,
    /// outside this library, with its `parts.json`) as the immutable asset directory named `name`: the same rename,
    /// never a copy, so the placed parts are the very files the session tested. A trial on another filesystem is
    /// refused (`trial_asset_other_filesystem`) and left in place.
    pub fn place_trial_asset_directory(&self, trial: &Path, name: ContentId) -> Result<String, StoreError> {
        let root = self.root().canonicalize().map_err(|error| StoreError::io(self.root(), error))?;
        let inside = trial.canonicalize().map(|path| path.starts_with(&root)).map_err(|error| StoreError::io(trial, error))?;
        if inside || !trial.is_dir() {
            return Err(refused(trial, "not a trial asset build outside this library"));
        }
        if !trial.join(PARTS_MANIFEST).is_file() {
            return Err(refused(trial, "trial asset build has no parts.json (incomplete build)"));
        }
        // Moving a directory to another parent rewrites its `..` entry, which needs write permission on it.
        std::fs::set_permissions(trial, std::fs::Permissions::from_mode(0o755)).map_err(|error| StoreError::io(trial, error))?;
        self.place_by_rename(trial, name).inspect_err(|_| {
            let _ = std::fs::set_permissions(trial, std::fs::Permissions::from_mode(0o555));
        })
    }

    /// Rename `built` to `assets/<name>` (refusing an existing name), seal it (0555, files 0444) and sync `assets/`.
    fn place_by_rename(&self, built: &Path, name: ContentId) -> Result<String, StoreError> {
        let assets = self.root().join(ASSETS_DIRECTORY);
        let relative = format!("{ASSETS_DIRECTORY}/{}", name.to_hex());
        let target = self.root().join(&relative);
        if target.exists() {
            return Err(refused(&target, "unrecorded_asset_directory: an asset directory of this name already exists"));
        }
        std::fs::create_dir_all(&assets).map_err(|error| StoreError::io(&assets, error))?;
        std::fs::rename(built, &target).map_err(|error| match error.kind() {
            std::io::ErrorKind::CrossesDevices => {
                refused(built, "trial_asset_other_filesystem: the trial build and the library are on different filesystems; it is not copied")
            }
            _ => StoreError::io(&target, error),
        })?;
        for entry in std::fs::read_dir(&target).map_err(|error| StoreError::io(&target, error))? {
            let path = entry.map_err(|error| StoreError::io(&target, error))?.path();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o444)).map_err(|error| StoreError::io(&path, error))?;
        }
        std::fs::set_permissions(&target, std::fs::Permissions::from_mode(0o555)).map_err(|error| StoreError::io(&target, error))?;
        std::fs::File::open(&assets).and_then(|directory| directory.sync_all()).map_err(|error| StoreError::io(&assets, error))?;
        Ok(relative)
    }

    /// Move the placed asset directory of the locked name out of `assets/` for its release (one rename into the staging
    /// directory, as `<name>.<pid>-<n>`, the form [`ObjectStore::remove_stale_asset_staging`] removes under the name's
    /// lock): the staged path, or `None` when the name has no placed directory. Nothing is read or removed yet
    /// ([`ObjectStore::remove_retired_asset_directory`]).
    pub fn retire_asset_directory(&self, lock: &AssetNameLock) -> Result<Option<PathBuf>, StoreError> {
        let placed = self.root().join(ASSETS_DIRECTORY).join(lock.name.to_hex());
        if !placed.exists() {
            return Ok(None);
        }
        let staged = self.fresh_asset_staging_directory(lock)?;
        // Moving a directory to another parent rewrites its `..` entry, which needs write permission on the sealed
        // directory (0555); its files keep their modes.
        std::fs::set_permissions(&placed, std::fs::Permissions::from_mode(0o755)).map_err(|error| StoreError::io(&placed, error))?;
        std::fs::rename(&placed, &staged).map_err(|error| {
            let _ = std::fs::set_permissions(&placed, std::fs::Permissions::from_mode(0o555));
            StoreError::io(&placed, error)
        })?;
        let assets = self.root().join(ASSETS_DIRECTORY);
        std::fs::File::open(&assets).and_then(|directory| directory.sync_all()).map_err(|error| StoreError::io(&assets, error))?;
        Ok(Some(staged))
    }

    /// Remove a directory [`ObjectStore::retire_asset_directory`] moved away: `(file bytes, freed bytes)`, the bytes of
    /// its files and of those among them whose last link it removed (metadata read before the removal). A file shared by
    /// hard link keeps its other names and its content; only this directory's entry for it goes.
    pub fn remove_retired_asset_directory(&self, staged: &Path) -> Result<(u64, u64), StoreError> {
        use std::os::unix::fs::MetadataExt;
        let staging = self.root().join(ASSETS_DIRECTORY).join(STAGING_DIRECTORY);
        if staged.parent() != Some(staging.as_path()) {
            return Err(refused(staged, "not a retired asset directory of this library"));
        }
        let mut freed = 0;
        for entry in std::fs::read_dir(staged).map_err(|error| StoreError::io(staged, error))? {
            let entry = entry.map_err(|error| StoreError::io(staged, error))?;
            let meta = entry.metadata().map_err(|error| StoreError::io(&entry.path(), error))?;
            if meta.nlink() == 1 {
                freed += meta.len();
            }
        }
        Ok((remove_build_directory(staged)?, freed))
    }

    /// The absolute directory of the library-relative asset path `relative`, which must be exactly
    /// `assets/<64 lower-case hex>` (no absolute path, no `..`, nothing else). Nothing is read.
    pub fn asset_directory(&self, relative: &str) -> Result<PathBuf, StoreError> {
        let name = relative.strip_prefix(ASSETS_DIRECTORY).and_then(|rest| rest.strip_prefix('/'));
        match name.map(ContentId::parse_hex) {
            Some(Ok(_)) => Ok(self.root().join(relative)),
            _ => Err(refused(Path::new(relative), "not a library-relative asset directory (assets/<64 hex>)")),
        }
    }
}

/// Remove the unplaced build directory `path` (flat: part files and `parts.json`); returns the bytes its files held
/// (metadata). A missing directory removes nothing.
pub fn remove_build_directory(path: &Path) -> Result<u64, StoreError> {
    let entries = match std::fs::read_dir(path) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(0),
        Err(error) => return Err(StoreError::io(path, error)),
    };
    let mut bytes = 0;
    for entry in entries {
        let entry = entry.map_err(|error| StoreError::io(path, error))?;
        bytes += entry.metadata().map_err(|error| StoreError::io(&entry.path(), error))?.len();
    }
    // A sealed directory (0555) must be writable for its entries to be unlinked.
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).map_err(|error| StoreError::io(path, error))?;
    std::fs::remove_dir_all(path).map_err(|error| StoreError::io(path, error))?;
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    const PARTS_MANIFEST_TEXT: &str = r#"{"format_version":2}"#;

    fn library(name: &str) -> ObjectStore {
        let lane = PathBuf::from(std::env::var_os("TMPDIR").expect("a scratch TMPDIR is required; /tmp is forbidden"));
        let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        ObjectStore::open(lane.join("gendb-artifacts-tests").join(format!("{name}-{}-{nanos}", std::process::id()))).unwrap()
    }

    fn staged_build(store: &ObjectStore, lock: &AssetNameLock, complete: bool) -> PathBuf {
        let staged = store.fresh_asset_staging_directory(lock).unwrap();
        std::fs::create_dir(&staged).unwrap();
        std::fs::write(staged.join("part-0000.bin"), [1u8, 0, 0, 0]).unwrap();
        if complete {
            std::fs::write(staged.join(PARTS_MANIFEST), PARTS_MANIFEST_TEXT).unwrap();
        }
        staged
    }

    /// A held name lock excludes a second holder of that name (another open file description, as in another process)
    /// and does not block any other name.
    #[test]
    fn asset_name_locks_are_per_name() {
        let store = library("asset-locks");
        let (a, b) = (ContentId::from_bytes([1; 32]), ContentId::from_bytes([2; 32]));
        let held = store.lock_asset_name(a).unwrap();
        let path = |n: ContentId| store.root().join("assets/.locks").join(format!("{}.lock", n.to_hex()));
        assert!(File::open(path(a)).unwrap().try_lock().is_err(), "the held name is exclusive");
        let other = store.lock_asset_name(b).unwrap();
        assert_eq!((held.name(), other.name()), (a, b));
        drop(held);
        assert!(File::open(path(a)).unwrap().try_lock().is_ok(), "released on drop");
    }

    /// Placement renames a complete staged build to `assets/<name>`, seals it and refuses incomplete builds, foreign
    /// directories, an existing name and non-canonical relative paths.
    #[test]
    fn asset_directories_are_placed_once_sealed_and_named_relatively() {
        let store = library("asset-directory");
        let name = ContentId::from_bytes([7; 32]);
        let lock = store.lock_asset_name(name).unwrap();
        let incomplete = staged_build(&store, &lock, false);
        assert!(store.place_asset_directory(&incomplete, name).unwrap_err().to_string().contains("incomplete"));
        let foreign = store.root().join("elsewhere");
        std::fs::create_dir(&foreign).unwrap();
        std::fs::write(foreign.join(PARTS_MANIFEST), b"{}").unwrap();
        assert!(store.place_asset_directory(&foreign, name).unwrap_err().to_string().contains("not a staged"));

        let staged = staged_build(&store, &lock, true);
        let relative = store.place_asset_directory(&staged, name).unwrap();
        assert_eq!(relative, format!("assets/{}", name.to_hex()));
        let placed = store.asset_directory(&relative).unwrap();
        assert!(!staged.exists() && placed.join("part-0000.bin").is_file());
        assert_eq!(std::fs::metadata(&placed).unwrap().permissions().mode() & 0o777, 0o555);
        assert_eq!(std::fs::metadata(placed.join(PARTS_MANIFEST)).unwrap().permissions().mode() & 0o777, 0o444);
        let again = staged_build(&store, &lock, true);
        assert!(store.place_asset_directory(&again, name).unwrap_err().to_string().contains("unrecorded_asset_directory"));
        for bad in ["/abs/assets/x", "assets/../objects", "assets/abc", &format!("objects/{}", name.to_hex())] {
            assert!(store.asset_directory(bad).is_err(), "{bad}");
        }
    }

    /// Under a name's lock its leftover staged builds are removed (bytes counted); other names' builds, the earlier
    /// unnamed form and placed directories stay.
    #[test]
    fn stale_staged_builds_are_removed_only_for_the_locked_name() {
        let store = library("asset-staging");
        let (a, b) = (ContentId::from_bytes([3; 32]), ContentId::from_bytes([4; 32]));
        let (lock_a, lock_b) = (store.lock_asset_name(a).unwrap(), store.lock_asset_name(b).unwrap());
        let left = [staged_build(&store, &lock_a, false), staged_build(&store, &lock_a, true)];
        let other = staged_build(&store, &lock_b, true);
        let unnamed = store.root().join("assets/.staging/123-0");
        std::fs::create_dir(&unnamed).unwrap();
        let placed = store.asset_directory(&store.place_asset_directory(&staged_build(&store, &lock_a, true), a).unwrap()).unwrap();
        let removed = store.remove_stale_asset_staging(&lock_a).unwrap();
        assert_eq!(removed, 4 + 4 + PARTS_MANIFEST_TEXT.len() as u64, "file bytes of both leftovers");
        assert!(left.iter().all(|p| !p.exists()) && other.is_dir() && unnamed.is_dir() && placed.join(PARTS_MANIFEST).is_file());
        assert_eq!(store.remove_stale_asset_staging(&lock_a).unwrap(), 0);
    }
}
