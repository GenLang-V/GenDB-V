//! `gendb prepare-flat-storage REQUEST RUN_DIR`: the one-time preparation of the fixed flat storages of a
//! `storage_policy` `fixed_flat` request (`storage::flat`), in a run directory of its own (route
//! `flat_storage_preparation`). It translates the request's statements (for the dataset schema), prepares the capture of
//! every column of every table (reused or extended as for any run: `preparation::prepare_flat_capture`), and prepares
//! one flat storage per table: verified and compiled whole, its asset published from the capture's column files, and
//! registered. No preflight, reference, author or builder run on the full data. A rerun reuses everything prepared.
//! Its record is `<run>/flat-storage.json` (also the run's summary).

use super::lifecycle::{Route, publish_summary, record_request, record_route};
use super::preparation::prepare_flat_capture;
use super::WorkloadError;
use crate::controller::crash_dumps;
use crate::controller::records::{self, RecordError};
use crate::controller::request::WorkloadRequest;
use crate::storage::flat::{FlatPreparation, prepare_flat_storages};
use gendb_frontend::parser::SqlParser;
use gendb_verification::admission::storage::StorageSchema;
use serde_json::json;
use std::path::Path;
use std::time::Instant;

/// Prepare the flat storages of `request` (read from `request_path`) in `run_dir`; returns the preparation record.
pub fn prepare_flat_storage(request_path: &Path, run_dir: &Path) -> Result<serde_json::Value, WorkloadError> {
    let _ = crash_dumps::contain();
    let started = Instant::now();
    let request = WorkloadRequest::read(request_path)?;
    request.validate()?;
    if !request.storage_policy.is_fixed_flat() {
        return Err(WorkloadError::invalid("prepare-flat-storage prepares the storages of a request with storage_policy fixed_flat"));
    }
    records::create_dir(run_dir)?;
    let root = run_dir.canonicalize().map_err(|e| RecordError::new(run_dir, e))?;
    record_route(&root, Route::FlatPreparation)?;
    record_request(&root, &serde_json::to_value(&request).map_err(|e| WorkloadError::invalid(e.to_string()))?)?;
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let (statement, data) = prepare_flat_capture(&request, &root, &parser)?;
    let source = data.capture.current();
    let preparation = FlatPreparation {
        library: &request.library,
        locks: &request.host_locks,
        schema: StorageSchema { tables: &statement.instance.doc.tables, ddl: &statement.schema_ddl, frontend: &statement.instance.doc.frontend },
        source: &source,
        out: &root.join("flat-storage"),
        registered_by: json!({"route":"prepare-flat-storage","run":root}),
    };
    let mut record = prepare_flat_storages(&preparation).map_err(|e| WorkloadError::invalid(format!("flat storage preparation: {e}")))?;
    record["status"] = json!("closed");
    record["wall_ns"] = json!(started.elapsed().as_nanos() as u64);
    record["data_preparation"] = json!({"record":data.record,"preparation_ns":data.preparation_ns as u64,"report":data.report});
    records::write_new_json(&records::next_free_record(&root, "flat-storage.json", "flat-storage"), &record)?;
    publish_summary(&root, &record)?;
    Ok(record)
}
