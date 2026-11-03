//! After evaluation: the close of a query session. The admitted package is served again from the library through the
//! serving route (v4: its storage assets for the current capture) at every admission binding and worker count and
//! compared with the references; for the execution-time objective the served package is measured again at every
//! benchmark binding and worker count in timing windows of its own. No author call and no build.

use super::session::QuerySession;
use gendb_artifacts::ObjectStore;
use gendb_storage::import::PreparedSource;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::served::{FinalCellError, SERVING_PATH, check_served_bindings, final_served_cell};
use gendb_verification::admission::StatementInputs;
use serde_json::{Value, json};
use std::path::Path;
use std::sync::Arc;

/// Recorded status of a close whose final comparison found a served answer the SQL does not allow.
pub const SERVED_NOT_ALLOWED: &str = "served_answer_not_allowed";

impl QuerySession {
    /// Serve the admitted package again from `library` records (fresh resolution, worker child) at every admission
    /// binding and configured worker count and compare with the prepared-data reference; for the execution-time
    /// objective also the final measurement. `qualified_admissions`: the admissions of this session.
    pub fn close<Lease>(
        &self,
        library: &Path,
        source: Arc<PreparedSource>,
        work: &Path,
        qualified_admissions: Vec<Value>,
        timing_lease: impl Fn() -> Result<Lease, String>,
    ) -> Result<Value, AdmissionError> {
        let store = ObjectStore::open_existing(library).map_err(AdmissionError::tool)?;
        let inputs = self.inputs_over(source);
        let served = check_served_bindings(&store, &self.runner, &self.preflight, &inputs, &self.references, &self.worker_counts, work)?;
        let final_measurement = if self.performance {
            match self.final_measurement(&store, &inputs, work, timing_lease) {
                Ok(measurement) => measurement,
                Err(FinalCellError::NotAllowed(error)) => {
                    crate::controller::records::write_new_json(
                        &work.join("final-measurement-failure.json"),
                        &json!({"status":SERVED_NOT_ALLOWED,"error":format!("{SERVED_NOT_ALLOWED}: {error}")}),
                    )
                    .map_err(AdmissionError::tool)?;
                    return Err(AdmissionError::execution(format!("{SERVED_NOT_ALLOWED}: {}", error.message)));
                }
                Err(FinalCellError::Failed(error)) => json!({"status":"failed","error":error.to_string(),"claim":"no final runtime"}),
            }
        } else {
            Value::Null
        };
        Ok(json!({"status":"verified_package_served","statement_key":self.statement().key_v4_id,"final_measurement":final_measurement,
            "qualified_admissions":qualified_admissions,"served":served,"serving_path":SERVING_PATH,"evidence":work}))
    }

    /// Per benchmark binding and configured worker count, under its own host timing lease: the served package at that
    /// binding (1 warm + 3 hot calls, each compared with the binding's reference). These are the same cells the
    /// submissions were scored on; this is GenDB's final hot runtime; no other system is measured in the window, so it
    /// supports no comparison claim by itself.
    fn final_measurement<Lease>(&self, store: &ObjectStore, inputs: &StatementInputs, work: &Path, timing_lease: impl Fn() -> Result<Lease, String>) -> Result<Value, FinalCellError> {
        let statement = self.statement();
        let mut cells = vec![];
        for &binding in &statement.benchmark {
            let name = &statement.bindings[binding].name;
            let reference = self.references.get(binding).ok_or_else(|| FinalCellError::Failed(AdmissionError::tool("reference absent")))?;
            for workers in &self.worker_counts {
                let _lease = timing_lease().map_err(|e| FinalCellError::Failed(AdmissionError::tool(e)))?;
                let window = format!("final-measurement-{name}-{workers}-{}", crate::controller::records::now_unix_ms());
                let gendb = final_served_cell(store, &self.runner, &self.preflight, inputs, binding, reference, *workers, work)?;
                cells.push(json!({"binding":name,"arguments":statement.bindings[binding].texts,"workers":workers,"window":window,"gendb":gendb}));
            }
        }
        Ok(json!({"protocol":"per benchmark binding and worker count one exclusive host timing lease: the served verified package at that binding (1 warm + 3 hot, each call compared with the binding's independent reference, or under the validation policy formal_proofs with its saved answers of other engines where given); no other system measured in the window","cells":cells,
            "validation":self.preflight.validation.record()}))
    }
}
