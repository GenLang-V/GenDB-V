//! Storage versions for the current prepared data: which admitted storages apply to it, and the stored asset of each
//! storage use for it.
//!
//! The current data is a [`CurrentCapture`]: per captured table its source version, row-order identity, row count and
//! captured ordinals (metadata of a [`PreparedSource`], nothing read). An asset applies exactly when its key equals the
//! key of the current capture ([`CurrentCapture::asset_key`]); all uses of one execution are resolved against one
//! capture, so every stored table they share relates to one row sequence (`same_capture`). Applicability of a storage
//! version here is decided from declared data only: the stored tables are captured, a storage whose builder assumes
//! declared integrity constraints (storage entry v2) assumes exactly the run's declaration set
//! (`storage_assumes_declared_constraints`; every other storage assumes none and applies in every run), and (when
//! given) the storage was checked with the current check configuration. Whether it stores the same content over the
//! run's schema, and whether its generated framework text is current, is decided by content, not by text, in
//! `synthesis::storage::reverify` (a storage over another framework text is re-verified, never refused for it). Nothing
//! interprets a description, and nothing is hashed or rescanned.

use crate::import::PreparedSource;
use gendb_artifacts::verus::{
    RecordError, VerusCheckConfigurationV1, VerusStorageAssetKeyV1, VerusStorageAssetTableV1, VerusStorageAssetV1,
    VerusStoragePackageV1, AdmittedStorage, admitted_storages, resolve_storage_asset, storage_asset_directory,
};
use gendb_artifacts::{ContentId, ObjectStore};
use std::fmt;
use std::path::PathBuf;

/// One captured table of the current data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapturedTable {
    pub table: String,
    pub source_version: String,
    pub row_order: String,
    pub rows: u64,
    /// Captured ordinals, ascending.
    pub ordinals: Vec<usize>,
}

/// The current data storages are resolved against.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentCapture {
    pub tables: Vec<CapturedTable>,
}

impl CurrentCapture {
    /// The captured tables of a prepared source (metadata only).
    pub fn of(source: &PreparedSource) -> Result<Self, VersionError> {
        let tables = source
            .coverage()
            .into_iter()
            .map(|(table, ordinals)| {
                let missing = |what: &str| VersionError::Capture(format!("{what} of captured table {table} absent"));
                Ok(CapturedTable {
                    source_version: source.source_version(&table).ok_or_else(|| missing("source version"))?.to_string(),
                    row_order: source.row_order_identity(&table).ok_or_else(|| missing("row-order identity"))?,
                    rows: source.row_count(&table).ok_or_else(|| missing("row count"))? as u64,
                    table,
                    ordinals,
                })
            })
            .collect::<Result<Vec<_>, VersionError>>()?;
        Ok(Self { tables })
    }

    pub fn table(&self, name: &str) -> Option<&CapturedTable> {
        self.tables.iter().find(|t| t.table == name)
    }

    /// The asset key of storage package `package_id` for this capture: every stored table with its current source
    /// version, row-order identity and row count. A stored table that is not captured has no key here. The stored
    /// columns need not be captured: the key names the table's rows, not its column set, so an asset built earlier
    /// (or one built from admitted storages) applies without reading those columns again; a build from source columns
    /// extends the capture by its missing columns first (`synthesis::storage::capture`).
    pub fn asset_key(&self, package_id: ContentId, package: &VerusStoragePackageV1) -> Result<VerusStorageAssetKeyV1, VersionError> {
        let tables = package
            .tables
            .iter()
            .map(|stored| {
                let captured = self
                    .table(&stored.table)
                    .ok_or_else(|| VersionError::NotCaptured { storage: package.name.clone(), table: stored.table.clone() })?;
                Ok(VerusStorageAssetTableV1 {
                    table: stored.table.clone(),
                    source_version: captured.source_version.clone(),
                    row_order: captured.row_order.clone(),
                    rows: captured.rows,
                })
            })
            .collect::<Result<Vec<_>, VersionError>>()?;
        Ok(VerusStorageAssetKeyV1 { storage_package: package_id, tables })
    }

    /// The `(source version, row count)` view of the saved v3 route (`gendb_artifacts::verus::CurrentSource`).
    pub fn source_versions(&self) -> impl Fn(&str) -> Result<(String, usize), String> + '_ {
        move |table: &str| {
            let captured = self.table(table).ok_or_else(|| format!("current source version of {table} absent"))?;
            Ok((captured.source_version.clone(), captured.rows as usize))
        }
    }
}

/// The stored asset of one storage use for the current capture.
#[derive(Clone, Debug)]
pub struct ResolvedStorageAsset {
    pub name: String,
    pub package: ContentId,
    pub asset_id: ContentId,
    pub asset: VerusStorageAssetV1,
    /// The asset's parts directory in the library (absolute).
    pub directory: PathBuf,
}

/// The asset of every storage use `(name, package id, package)` for `capture`, in use order; the first use without a
/// published asset for it is `NoAsset` (build it offline), a stored table not captured is `NotCaptured`.
pub fn resolve_storage_assets<'a>(
    store: &ObjectStore,
    uses: impl IntoIterator<Item = (&'a str, ContentId, &'a VerusStoragePackageV1)>,
    capture: &CurrentCapture,
) -> Result<Vec<ResolvedStorageAsset>, VersionError> {
    uses.into_iter()
        .map(|(name, package_id, package)| {
            let key = capture.asset_key(package_id, package)?;
            let (asset_id, asset) = resolve_storage_asset(store, &key)?.ok_or_else(|| VersionError::NoAsset { storage: name.to_string() })?;
            let directory = storage_asset_directory(store, &asset)?;
            Ok(ResolvedStorageAsset { name: name.to_string(), package: package_id, asset_id, asset, directory })
        })
        .collect()
}

/// One admitted storage version as a candidate for the current data.
#[derive(Clone, Debug)]
pub struct StorageVersion {
    pub package_id: ContentId,
    pub package: VerusStoragePackageV1,
    /// Whether this is its name's current (head) admitted version; older versions stay usable by exact package id.
    pub current: bool,
    /// `Ok` when it applies to the current data; otherwise the named reason.
    pub applicability: Result<(), String>,
    /// Its published asset for the current capture, if built.
    pub asset: Option<(ContentId, VerusStorageAssetV1)>,
}

/// Every distinct admitted storage version (by name, newest first within a name; `current` marks each name's head),
/// with its applicability to `capture` under the run's declared integrity constraints `declared`
/// (`declared_constraints_digest` of the run's `gendb_constraints.rs`; `None`: the run declares none) and, when given,
/// the check configuration of the current toolchain. Older variants of a name are listed too: they remain reusable by
/// exact package id.
pub fn storage_versions_for(
    store: &ObjectStore,
    capture: &CurrentCapture,
    declared: Option<ContentId>,
    configuration: Option<&VerusCheckConfigurationV1>,
) -> Result<Vec<StorageVersion>, VersionError> {
    let mut versions = vec![];
    for AdmittedStorage { package_id, package, current } in admitted_storages(store)? {
        let applicability = applicability(capture, declared, configuration, package_id, &package);
        let asset = match capture.asset_key(package_id, &package) {
            Ok(key) => resolve_storage_asset(store, &key)?,
            Err(_) => None,
        };
        versions.push(StorageVersion { package_id, package, current, applicability, asset });
    }
    Ok(versions)
}

fn applicability(
    capture: &CurrentCapture,
    declared: Option<ContentId>,
    configuration: Option<&VerusCheckConfigurationV1>,
    package_id: ContentId,
    package: &VerusStoragePackageV1,
) -> Result<(), String> {
    package.check_declared_constraints(declared).map_err(|e| e.to_string())?;
    capture.asset_key(package_id, package).map_err(|e| e.to_string())?;
    if configuration.is_some_and(|current| current != &package.configuration) {
        return Err("storage_configuration_differs: the storage was checked with another toolchain or configuration".into());
    }
    Ok(())
}

/// Why a storage version or asset could not be resolved.
#[derive(Debug)]
pub enum VersionError {
    Records(RecordError),
    /// The prepared source lacks metadata of a captured table.
    Capture(String),
    /// A stored table is not in the current capture.
    NotCaptured { storage: String, table: String },
    /// No asset of the storage is published for the current capture.
    NoAsset { storage: String },
}

impl fmt::Display for VersionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Records(error) => error.fmt(f),
            Self::Capture(reason) => f.write_str(reason),
            Self::NotCaptured { storage, table } => {
                write!(f, "storage_not_captured: storage {storage} stores table {table}, which the current data does not capture")
            }
            Self::NoAsset { storage } => write!(
                f,
                "no_storage_asset: storage {storage} has no asset for the current source versions and row order; build it offline"
            ),
        }
    }
}

impl std::error::Error for VersionError {}

impl From<RecordError> for VersionError {
    fn from(error: RecordError) -> Self {
        Self::Records(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gendb_artifacts::verus::{VerusCheckConfigurationV1, VerusStoredTableV1};

    fn package(ordinals: Vec<usize>) -> VerusStoragePackageV1 {
        VerusStoragePackageV1 {
            name: "s".into(),
            build: ContentId::default(),
            entry_identity: String::new(),
            assumed_constraints: None,
            tables: vec![VerusStoredTableV1 { table: "t".into(), table_id: 0, ordinals }],
            declaration: serde_json::Value::Null,
            schema_ddl: ContentId::default(),
            frontend: serde_json::Value::Null,
            closure: vec![],
            configuration: VerusCheckConfigurationV1 { provider_identity: String::new(), options: vec![], environment: Default::default() },
            readers: vec![],
            theorems: vec![],
            workers: (1, 1),
            tcb: ContentId::default(),
            derived_from: None,
        }
    }

    fn capture(row_order: &str, ordinals: Vec<usize>) -> CurrentCapture {
        CurrentCapture { tables: vec![CapturedTable { table: "t".into(), source_version: "v1".into(), row_order: row_order.into(), rows: 3, ordinals }] }
    }

    /// The key holds per table only source version, row order and rows: capturing more or fewer columns of the same
    /// read keeps it, another read changes it, and a table the capture lacks has no key.
    #[test]
    fn asset_keys_follow_the_row_order_not_the_column_set() {
        let id = ContentId::from_bytes([1; 32]);
        let stored = package(vec![0, 2]);
        let key = capture("r1", vec![0, 2]).asset_key(id, &stored).unwrap();
        assert_eq!(capture("r1", vec![0, 1, 2, 3]).asset_key(id, &stored).unwrap(), key);
        assert_eq!(capture("r1", vec![0, 1]).asset_key(id, &stored).unwrap(), key, "an uncaptured stored column keeps the key");
        assert_ne!(capture("r2", vec![0, 2]).asset_key(id, &stored).unwrap(), key);
        let other = CurrentCapture { tables: vec![CapturedTable { table: "u".into(), source_version: "v1".into(), row_order: "r1".into(), rows: 3, ordinals: vec![0] }] };
        let missing = other.asset_key(id, &stored).unwrap_err();
        assert!(matches!(missing, VersionError::NotCaptured { ref table, .. } if table == "t"), "{missing}");
        assert_eq!(capture("r1", vec![0]).source_versions()("t").unwrap(), ("v1".to_string(), 3));
    }

    /// Applicability under declared constraints: a storage that assumes none applies in every run; one that assumes a
    /// declaration set applies only to a run with exactly that set, and is otherwise listed as not applicable with the
    /// named reason (never offered), before any capture fact.
    #[test]
    fn constraint_dependent_storages_apply_only_to_their_exact_set() {
        let (set, other) = (ContentId::from_bytes([7; 32]), ContentId::from_bytes([8; 32]));
        let capture = capture("r1", vec![0, 2]);
        let plain = package(vec![0, 2]);
        let id = ContentId::from_bytes([1; 32]);
        for declared in [None, Some(set), Some(other)] {
            assert_eq!(applicability(&capture, declared, None, id, &plain), Ok(()), "{declared:?}");
        }
        let dependent = VerusStoragePackageV1 { assumed_constraints: Some(set), ..plain };
        assert_eq!(applicability(&capture, Some(set), None, id, &dependent), Ok(()));
        for declared in [None, Some(other)] {
            let reason = applicability(&capture, declared, None, id, &dependent).unwrap_err();
            assert!(reason.starts_with("storage_assumes_declared_constraints: storage s assumes"), "{reason}");
        }
    }
}
