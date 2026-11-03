//! The workload submission: `verus-storages.json` names one or more storage manifests of the author workspace. Its
//! freeze freezes every storage into `<frozen>/storages/<name>` and records one frozen candidate whose `modules` list
//! every storage's author files (so unchanged-resubmission detection compares their bytes) and whose other fields
//! carry no path.

use crate::controller::author::{CandidateSubmission, resolve_candidate_manifest};
use crate::controller::records::write_new_json;
use crate::query::candidate::inside;
use crate::storage::freeze::{FrozenStorage, freeze_storage, read_frozen_storage, read_manifest};
use gendb_frontend::ast::TableDef;
use gendb_verification::admission::AdmissionError;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

/// Conventional file name of the workload submission.
pub const SUBMISSION_FILE: &str = "verus-storages.json";
/// `kind` of a frozen workload storage candidate.
pub const CANDIDATE_KIND: &str = "verus_storages";

/// `verus-storages.json`: the storages of one submission, relative to this file's directory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkloadSubmission {
    pub format_version: u32,
    pub storages: Vec<PathBuf>,
}

impl WorkloadSubmission {
    pub fn schema() -> Value {
        json!({"type":"object","additionalProperties":false,"required":["format_version","storages"],"properties":{
            "format_version":{"const":1},
            "storages":{"type":"array","minItems":1,"items":{"type":"string"},"description":"verus-storage.json files of this workspace, relative to this file's directory; distinct storage names"}}})
    }

    pub fn example() -> Self {
        Self { format_version: 1, storages: vec!["storages/<name>/verus-storage.json".into()] }
    }
}

/// One storage module of the frozen workload candidate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenWorkloadModule {
    /// `<storage name>/<file relative to src/>`.
    pub file: String,
    pub role: String,
    pub items: Vec<String>,
    pub source: PathBuf,
}

/// `candidate.json` of a frozen workload submission.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenWorkloadCandidate {
    pub kind: String,
    pub format_version: u32,
    /// Storage names in submission order (each frozen under `<frozen>/storages/<name>`).
    pub storages: Vec<String>,
    /// Per storage: the manifest and declaration as frozen (no paths).
    pub declarations: Vec<Value>,
    pub modules: Vec<FrozenWorkloadModule>,
}

impl FrozenWorkloadCandidate {
    /// The frozen storages, in submission order: `(frozen dir, storage)`.
    pub fn storages(&self, frozen_dir: &Path) -> Result<Vec<(PathBuf, FrozenStorage)>, AdmissionError> {
        self.storages
            .iter()
            .map(|name| {
                let dir = frozen_dir.join("storages").join(name);
                Ok((dir.clone(), read_frozen_storage(&dir)?))
            })
            .collect()
    }
}

/// Freeze the workload submission into the fresh directory `frozen_dir`.
pub fn freeze_workload(workspace: &Path, frozen_dir: &Path, submission: &CandidateSubmission, schema: &[TableDef], store: Option<&gendb_artifacts::ObjectStore>) -> Result<FrozenWorkloadCandidate, AdmissionError> {
    let workspace = workspace.canonicalize().map_err(AdmissionError::tool)?;
    let (path, _) = resolve_candidate_manifest(&workspace, &submission.candidate_manifest)
        .map_err(|e| AdmissionError::missing_input(format!("{}: {e}", submission.candidate_manifest.display())))?;
    let bytes = fs::read(&path).map_err(|e| AdmissionError::missing_input(format!("{}: {e}", path.display())))?;
    let listed: WorkloadSubmission = serde_json::from_slice(&bytes).map_err(|e| AdmissionError::refusal(format!("verus-storages submission: {e}")))?;
    if listed.format_version != 1 || listed.storages.is_empty() {
        return Err(AdmissionError::refusal("a workload submission has format_version 1 and at least one storage manifest"));
    }
    let base = path.parent().ok_or_else(|| AdmissionError::missing_input("submission directory absent"))?;
    fs::create_dir(frozen_dir).map_err(AdmissionError::tool)?;
    fs::create_dir(frozen_dir.join("storages")).map_err(AdmissionError::tool)?;
    let (mut names, mut declarations, mut modules) = (vec![], vec![], vec![]);
    let mut distinct = BTreeSet::new();
    for manifest in &listed.storages {
        let manifest = inside(base, manifest)?;
        let relative = manifest.strip_prefix(&workspace).map_err(AdmissionError::tool)?;
        let (declared, _) = read_manifest(&workspace, relative)?;
        let name = declared.name.clone();
        if !distinct.insert(name.clone()) {
            return Err(AdmissionError::refusal(format!("storage {name} is submitted twice")));
        }
        let dir = frozen_dir.join("storages").join(&name);
        let storage = freeze_storage(&workspace, relative, &dir, schema, store, &Default::default())?;
        declarations.push(json!({"name":name,"manifest":storage.manifest,"declaration":storage.declaration,"compiler":storage.compiler}));
        modules.extend(storage.modules.iter().map(|m| FrozenWorkloadModule {
            file: format!("{name}/{}", m.file),
            role: json!(m.role).as_str().unwrap_or_default().to_string(),
            items: m.items.clone(),
            source: m.source.clone(),
        }));
        names.push(name);
    }
    let candidate = FrozenWorkloadCandidate { kind: CANDIDATE_KIND.into(), format_version: 1, storages: names, declarations, modules };
    let record = |file: &str, value: Value| write_new_json(&frozen_dir.join(file), &value).map_err(AdmissionError::tool);
    record("candidate.json", json!(candidate))?;
    record("decision.json", json!(submission))?;
    record("submission.json", json!(listed))?;
    Ok(candidate)
}
