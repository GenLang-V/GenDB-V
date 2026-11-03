//! The run's current prepared capture, shared by every author session of one controller process, and its extension
//! by columns a new storage declares.
//!
//! A storage may store a column no statement delivers (for example a query author's new variant). Such a column is
//! imported once, alone: `import::prepare_source` extends the current prepared root into a fresh root
//! `<run>/data-extension-<ms>` that links the base capture and reads only the missing columns. The extension keeps the
//! row-order identity of every base table (`PreparedSource::row_order_identity`), so the assets of storages over
//! unchanged tables keep their keys and are not rebuilt. `<run>/data-current.json` names the newest root, so a
//! resumed controller reopens it instead of preparing again. Nothing is rescanned or hashed.

use crate::controller::records::{self, RecordError, now_unix_ms};
use gendb_storage::import::{ColumnDemand, DatasetSpec, PreparationRequest, PreparedSource, prepare_source};
use gendb_verification::admission::AdmissionError;
use gendb_verification::obligations::DeclaredSource;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Instant;

/// Pointer to the run's newest prepared root (written when a capture is extended).
pub const CURRENT_DATA_POINTER: &str = "data-current.json";

/// The newest prepared root of the run `run_root`, when an extension replaced the first one.
pub fn current_data_root(run_root: &Path) -> Result<Option<PathBuf>, RecordError> {
    let pointer = run_root.join(CURRENT_DATA_POINTER);
    if !pointer.exists() {
        return Ok(None);
    }
    let record: Value = records::read_json(&pointer)?;
    let root = record["root"].as_str().map(PathBuf::from).filter(|root| root.is_absolute());
    root.map(Some).ok_or_else(|| RecordError::new(&pointer, "the current-data pointer must name an absolute prepared root"))
}

/// Where extensions of the run's capture are prepared.
#[derive(Clone, Debug)]
pub struct CaptureSetting {
    pub dataset: DatasetSpec,
    /// Registrations of prepared roots (`<library>.prepared-workloads`).
    pub registry: PathBuf,
    /// The run directory (extension roots and the current-data pointer live here).
    pub run_root: PathBuf,
}

/// The current capture, shared between sessions; extensions are serialized by its lock.
#[derive(Clone)]
pub struct SharedCapture {
    setting: Arc<CaptureSetting>,
    current: Arc<Mutex<Arc<PreparedSource>>>,
}

impl SharedCapture {
    pub fn new(setting: CaptureSetting, source: Arc<PreparedSource>) -> Self {
        Self { setting: Arc::new(setting), current: Arc::new(Mutex::new(source)) }
    }

    /// The dataset the capture is prepared from.
    pub fn dataset(&self) -> &DatasetSpec {
        &self.setting.dataset
    }

    /// The current prepared source.
    pub fn current(&self) -> Arc<PreparedSource> {
        self.current.lock().expect("capture lock").clone()
    }

    /// The current prepared source holding every stored column of `declaration`: the current one when it already
    /// does, else an extension by exactly the missing columns (its record is the second value).
    pub fn covering(&self, declaration: &DeclaredSource) -> Result<(Arc<PreparedSource>, Option<Value>), AdmissionError> {
        let mut demand = ColumnDemand::default();
        for table in &declaration.tables {
            let ordinals: Vec<usize> = table.columns.iter().map(|c| c.ordinal).collect();
            if ordinals.is_empty() {
                continue;
            }
            demand.add_columns(&self.setting.dataset, &table.name, &ordinals).map_err(AdmissionError::tool)?;
        }
        self.covering_demand(&demand)
    }

    /// The current prepared source holding every column of `demand`: the current one when it already does, else an
    /// extension by exactly the missing columns (its record is the second value).
    pub fn covering_demand(&self, demand: &ColumnDemand) -> Result<(Arc<PreparedSource>, Option<Value>), AdmissionError> {
        let mut current = self.current.lock().map_err(|_| AdmissionError::tool("capture lock poisoned"))?;
        let coverage = current.coverage();
        let missing = demand.missing_from(&coverage);
        if missing.is_empty() {
            return Ok((current.clone(), None));
        }
        let (extended, record) = self.extend(&current, &coverage, &missing)?;
        *current = extended.clone();
        Ok((extended, Some(record)))
    }

    /// Prepare a new root over `base` with the captured columns plus `missing`, and point the run at it.
    fn extend(&self, base: &PreparedSource, coverage: &[(String, Vec<usize>)], missing: &[(String, Vec<usize>)]) -> Result<(Arc<PreparedSource>, Value), AdmissionError> {
        let setting = &self.setting;
        let mut demand = ColumnDemand::default();
        for (table, ordinals) in coverage.iter().chain(missing) {
            demand.add_columns(&setting.dataset, table, ordinals).map_err(AdmissionError::tool)?;
        }
        let root = setting.run_root.join(format!("data-extension-{}", now_unix_ms()));
        let started = Instant::now();
        let (source, report) = prepare_source(&PreparationRequest {
            dataset: &setting.dataset,
            demand: &demand,
            base: Some(base.root()),
            registry: &setting.registry,
            root: &root,
        })
        .map_err(|e| AdmissionError::tool(format!("capture extension: {e}")))?;
        let record = json!({"format_version":1,"base":base.root(),"root":root,"added_columns":missing,"preparation":report,
            "preparation_ns":started.elapsed().as_nanos(),"source_version":source.source_snapshot(),
            "scope":"only the missing columns were read from the original files; every base table keeps its row-order identity, so assets over unchanged tables stay valid"});
        records::write_new_json(&setting.run_root.join(format!("capture-extension-{}.json", now_unix_ms())), &record).map_err(AdmissionError::tool)?;
        records::write_json_atomic(&setting.run_root.join(CURRENT_DATA_POINTER), &json!({"format_version":1,"root":root})).map_err(AdmissionError::tool)?;
        Ok((Arc::new(source), record))
    }
}
