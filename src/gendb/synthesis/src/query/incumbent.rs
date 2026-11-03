//! A query session's incumbent (`queries[].continue_from`): the candidate a closed query session of an earlier run
//! admitted, written into this session's author workspace before the first author call, so that the controller can
//! freeze it with the current framework and evaluate it afresh (`controller::run`, `Session::establish_incumbent`).
//!
//! What is written, and nothing else:
//! - the manifest the source froze (`frozen/manifest.json`, the author's `verus-query.json`) at the workspace path the
//!   source submission named, with every storage use pinned to the admitted package the source admission reads
//!   (`qualification.json` `storage_uses`; a workspace storage of the source was registered by that admission), so the
//!   incumbent reads exactly the storages of the admitted package;
//! - the query crate's author files (`src/agent/**`) of the frozen crate, under the manifest's `crate_dir`.
//!
//! The framework files are not copied: the freeze generates them for this run. The source author's latest notes (the
//! source workspace's `NOTES.md`, else the admitted submission's copy) are copied beside the incumbent
//! (`iterations/0000/NOTES.md`), never into the workspace's own notes. The source session is only read, and nothing is
//! written to any library.

use super::candidate::{FrozenCandidate, QueryManifest};
use crate::controller::author::CandidateSubmission;
use crate::controller::layout::{INCUMBENT_ITERATION, RunLayout};
use crate::controller::ledger::LedgerState;
use crate::controller::records::read_json;
use crate::controller::role::SeededIncumbent;
use gendb_artifacts::ContentId;
use gendb_verification::admission::AdmissionError;
use serde_json::{Value, json};
use std::fs;
use std::path::{Component, Path, PathBuf};

/// The class of every refusal of a continuation source.
pub const SOURCE_REFUSAL: &str = "continue_source_invalid";

/// The candidate a closed session admitted, as its records name it.
pub struct AdmittedCandidate {
    /// Its iteration in the source session.
    pub iteration: u32,
    /// `<source>/iterations/NNNN/frozen`.
    pub frozen: PathBuf,
    /// The source submission (manifest path, rationale, data access analysis).
    pub submission: CandidateSubmission,
    /// The source session's current evaluation record of it.
    pub evaluation: PathBuf,
    /// Its qualification record (`qualified: true`: admission, package, storage uses).
    pub qualification: Value,
}

/// The candidate the closed session `source` admitted: its qualified iteration (a session qualifies at most one; the
/// incumbent of a session that itself continued from another counts, so continuations chain) with a retained frozen
/// candidate. Refused by name (`continue_source_invalid`) otherwise. Reads the source's records only.
pub fn admitted_candidate(source: &Path) -> Result<AdmittedCandidate, String> {
    let refused = |what: String| format!("{SOURCE_REFUSAL}: {}: {what}", source.display());
    let layout = RunLayout::new(source);
    let state: LedgerState = read_json(&layout.ledger()).map_err(|e| refused(format!("the source session's ledger: {e}")))?;
    let competing = state.competing_trials();
    let qualified: Vec<(u32, Value)> = competing
        .iter()
        .filter_map(|trial| read_json::<Value>(&layout.qualification(trial.iteration)).ok().map(|q| (trial.iteration, q)))
        .filter(|(_, qualification)| qualification["qualified"] == true)
        .collect();
    let [(iteration, qualification)] = qualified.as_slice() else {
        return Err(refused(format!("the source session admitted {} candidates; it must have admitted exactly one", qualified.len())));
    };
    let trial = competing.iter().find(|trial| trial.iteration == *iteration).expect("found among the trials");
    // An incumbent's recorded candidate is its submission plus its provenance (`incumbent`).
    let mut candidate = trial.candidate.clone();
    if let Some(fields) = candidate.as_object_mut() {
        fields.remove("incumbent");
    }
    let submission: CandidateSubmission =
        serde_json::from_value(candidate).map_err(|e| refused(format!("the submission of iteration {iteration}: {e}")))?;
    submission.validate().map_err(|e| refused(format!("the submission of iteration {iteration}: {e}")))?;
    let frozen = layout.frozen(*iteration);
    for record in ["candidate.json", "manifest.json"] {
        if !frozen.join(record).is_file() {
            return Err(refused(format!("iteration {iteration} does not retain its frozen {record}")));
        }
    }
    let evaluation = trial.evaluation_record.clone().unwrap_or_else(|| layout.evaluation(*iteration));
    Ok(AdmittedCandidate { iteration: *iteration, frozen, submission, evaluation, qualification: qualification.clone() })
}

/// Write the candidate the closed session `source` admitted into the author `workspace` (module documentation) and
/// return the submission that freezes it, with its provenance. The workspace's session directory must hold the
/// incumbent's iteration directory (created by the controller), where the source author's notes are copied.
pub fn seed_workspace(source: &Path, workspace: &Path) -> Result<SeededIncumbent, AdmissionError> {
    let admitted = admitted_candidate(source).map_err(AdmissionError::refusal)?;
    let refused = |what: String| AdmissionError::refusal(format!("{SOURCE_REFUSAL}: {}: {what}", source.display()));
    let mut manifest: QueryManifest = read_json(&admitted.frozen.join("manifest.json")).map_err(|e| refused(format!("frozen manifest: {e}")))?;
    let frozen: FrozenCandidate = read_json(&admitted.frozen.join("candidate.json")).map_err(|e| refused(format!("frozen candidate: {e}")))?;
    let admitted_uses: Vec<(String, ContentId)> = serde_json::from_value(admitted.qualification["storage_uses"].clone())
        .map(|uses: Vec<Value>| uses.iter().filter_map(|u| Some((u["name"].as_str()?.to_string(), ContentId::parse_hex(u["package"].as_str()?).ok()?))).collect())
        .map_err(|e| refused(format!("the admission's storage uses: {e}")))?;
    if admitted_uses.len() != manifest.storage_uses.len() {
        return Err(refused(format!("the manifest names {} storage uses, the admission {}", manifest.storage_uses.len(), admitted_uses.len())));
    }
    for storage_use in &mut manifest.storage_uses {
        let (_, package) = admitted_uses
            .iter()
            .find(|(name, _)| *name == storage_use.name)
            .ok_or_else(|| refused(format!("the admission reads no storage named {}", storage_use.name)))?;
        storage_use.admitted = Some(*package);
        storage_use.workspace = None;
    }
    let manifest_path = workspace.join(&admitted.submission.candidate_manifest);
    let manifest_dir = manifest_path.parent().ok_or_else(|| refused("the submitted manifest path has no directory".into()))?;
    if !is_plain_relative(&manifest.crate_dir) {
        return Err(refused(format!("crate_dir {} is not a plain relative path", manifest.crate_dir.display())));
    }
    let crate_src = manifest_dir.join(&manifest.crate_dir).join("src");
    // No author call precedes the seed (the controller seeds before the search), so the agent directory is replaced.
    let agent = crate_src.join("agent");
    if agent.exists() {
        fs::remove_dir_all(&agent).map_err(|e| AdmissionError::tool(format!("{}: {e}", agent.display())))?;
    }
    for file in &frozen.author_files {
        if !is_plain_relative(Path::new(file)) || !file.starts_with("agent/") {
            return Err(refused(format!("frozen author file {file} is not under agent/")));
        }
        copy(&admitted.frozen.join("crate/src").join(file), &crate_src.join(file))?;
    }
    let text = serde_json::to_vec_pretty(&manifest).map_err(AdmissionError::tool)?;
    fs::create_dir_all(manifest_dir).and_then(|_| fs::write(&manifest_path, text)).map_err(|e| AdmissionError::tool(format!("{}: {e}", manifest_path.display())))?;
    let session = workspace.parent().ok_or_else(|| AdmissionError::tool("the author workspace has no session directory"))?;
    // The source author's latest notes (its workspace's, which also cover attempts after the admitted one), else the
    // notes as they were at the admitted submission.
    let latest_notes = RunLayout::new(source).workspace().join(crate::controller::layout::NOTES_FILE);
    let admitted_notes = admitted.frozen.parent().map(|iteration| iteration.join(crate::controller::layout::NOTES_FILE));
    let notes = match [Some(latest_notes), admitted_notes].into_iter().flatten().find(|notes| notes.is_file()) {
        Some(from) => {
            let to = RunLayout::new(session).iteration_notes(INCUMBENT_ITERATION);
            copy(&from, &to)?;
            Some(to)
        }
        None => None,
    };
    let provenance = json!({"source_session":source,"source_iteration":admitted.iteration,"source_frozen":admitted.frozen,
        "source_admission":admitted.qualification["admission"],"source_package":admitted.qualification["package"],
        "source_evaluation":admitted.evaluation,"manifest":manifest_path,"crate_src":crate_src,"author_files":frozen.author_files,
        "pinned_storage_uses":manifest.storage_uses,"source_notes":notes,
        "written":"the source manifest with its storage uses pinned to the admitted packages, and the crate's author files (src/agent/**); framework files are generated by the freeze"});
    Ok(SeededIncumbent { submission: admitted.submission, source_evaluation: admitted.evaluation, provenance })
}

/// Only normal components (no root, `.` or `..`).
fn is_plain_relative(path: &Path) -> bool {
    path.components().all(|c| matches!(c, Component::Normal(_)))
}

/// Copy one file, creating its directory.
fn copy(from: &Path, to: &Path) -> Result<(), AdmissionError> {
    let failed = |e: std::io::Error| AdmissionError::tool(format!("copy {} -> {}: {e}", from.display(), to.display()));
    if let Some(parent) = to.parent() {
        fs::create_dir_all(parent).map_err(failed)?;
    }
    fs::copy(from, to).map(drop).map_err(failed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::ledger::{Trial, TrialStatus};
    use crate::controller::limits::tests::limits;
    use crate::controller::records::{create_dir, write_json_atomic};
    use crate::controller::test_support::scratch_root;

    const PACKAGE: &str = "92c00534c363b0c07635ee9d65f69cbf0ef782b0bef8785ae7cf4556d6c669bc";

    /// A closed source session shaped like the controller's records: iteration 2 admitted, reading storage `facts`
    /// (named as a workspace storage in its manifest, registered by the admission), with notes and an older
    /// unqualified iteration 1.
    fn source_session(root: &Path) -> PathBuf {
        let source = root.join("earlier/queries/query-0003");
        let layout = RunLayout::new(&source);
        let submission = json!({"candidate_manifest":"q/verus-query.json","rationale":"r","data_access_analysis":"d"});
        let trial = |iteration: u32| Trial { iteration, call_id: u64::from(iteration), candidate: submission.clone(), status: TrialStatus::Evaluated,
            evaluation: json!({"eligible":true}), framework_elapsed_ms: None, directory: None, recovery_records: vec![], evaluation_record: None };
        create_dir(&source).unwrap();
        write_json_atomic(&layout.ledger(), &json!({"format_version":1,"request":{},"session_id":"s","limits":limits(),"iterations":2,"calls":[],
            "trials":[trial(1), trial(2)],"closed":{"status":"closed"}})).unwrap();
        create_dir(&layout.iteration(1)).unwrap();
        write_json_atomic(&layout.qualification(1), &json!({"qualified":false,"error":"slower"})).unwrap();
        let frozen = layout.frozen(2);
        for (file, text) in [("crate/src/agent/mod.rs", "// entry"), ("crate/src/agent/common/topk.rs", "// helper"), ("crate/src/query.rs", "// framework")] {
            fs::create_dir_all(frozen.join(file).parent().unwrap()).unwrap();
            fs::write(frozen.join(file), text).unwrap();
        }
        write_json_atomic(&frozen.join("manifest.json"), &json!({"format_version":2,"crate_dir":"verus","modules":[{"file":"mod.rs","role":"entry","items":["query"]}],
            "storage_uses":[{"name":"facts","workspace":"../storages/facts/verus-storage.json"}],"compiler":null,"notes":""})).unwrap();
        write_json_atomic(&frozen.join("candidate.json"), &json!({"kind":"verus_rust_stored","format_version":2,"statement_key":"k","sql":"q","entry_identity":"e",
            "storage_uses":[],"compiler":{"opt_level":3,"target_cpu":null},"modules":[],"author_files":["agent/common/topk.rs","agent/mod.rs"],
            "framework_files":["query.rs"],"notes":""})).unwrap();
        write_json_atomic(&layout.qualification(2), &json!({"qualified":true,"admission":"a","package":"p","storage_uses":[{"name":"facts","package":PACKAGE}]})).unwrap();
        fs::write(layout.iteration_notes(2), "the notes at the admitted submission").unwrap();
        fs::create_dir_all(layout.workspace()).unwrap();
        fs::write(layout.workspace().join("NOTES.md"), "the earlier author's latest notes").unwrap();
        source
    }

    /// The admitted candidate's manifest (uses pinned to the admitted packages) and author files land in the workspace
    /// at the submitted paths; no framework file is copied; the notes go beside the incumbent; a source that admitted
    /// nothing is refused by name.
    #[test]
    fn the_admitted_candidate_is_written_into_the_workspace_with_pinned_storage_uses() {
        let root = scratch_root("incumbent-seed");
        let source = source_session(&root);
        let session = root.join("now/queries/query-0000");
        let workspace = session.join("author");
        create_dir(&RunLayout::new(&session).iteration(INCUMBENT_ITERATION)).unwrap();
        fs::create_dir_all(workspace.join("q/verus/src/agent")).unwrap();
        fs::write(workspace.join("q/verus/src/agent/stale.rs"), "// replaced").unwrap();
        let seeded = seed_workspace(&source, &workspace).unwrap();
        assert_eq!(seeded.submission.candidate_manifest, Path::new("q/verus-query.json"));
        assert_eq!(seeded.source_evaluation, RunLayout::new(&source).evaluation(2));
        let manifest: QueryManifest = read_json(&workspace.join("q/verus-query.json")).unwrap();
        assert_eq!((manifest.storage_uses[0].admitted, &manifest.storage_uses[0].workspace), (Some(ContentId::parse_hex(PACKAGE).unwrap()), &None));
        assert_eq!(fs::read_to_string(workspace.join("q/verus/src/agent/common/topk.rs")).unwrap(), "// helper");
        assert!(!workspace.join("q/verus/src/agent/stale.rs").exists() && !workspace.join("q/verus/src/query.rs").exists());
        assert_eq!(fs::read_to_string(RunLayout::new(&session).iteration_notes(INCUMBENT_ITERATION)).unwrap(), "the earlier author's latest notes");
        assert_eq!(seeded.provenance["source_iteration"], 2);
        fs::remove_file(RunLayout::new(&source).qualification(2)).unwrap();
        let error = admitted_candidate(&source).err().unwrap();
        assert!(error.starts_with(SOURCE_REFUSAL) && error.contains("admitted 0 candidates"), "{error}");
        fs::remove_dir_all(root).unwrap();
    }

    /// A session that continued from another and kept its incumbent admitted is itself a source (continuations chain):
    /// the incumbent's recorded candidate (its submission plus provenance) names the submission.
    #[test]
    fn an_admitted_incumbent_is_the_admitted_candidate_of_its_session() {
        let root = scratch_root("incumbent-chain");
        let source = root.join("e4/queries/query-0006");
        let layout = RunLayout::new(&source);
        let incumbent = json!({"iteration":0,"call_id":0,"status":"evaluated","evaluation":{"eligible":true},
            "candidate":{"candidate_manifest":"verus-query.json","rationale":"r","data_access_analysis":"d","incumbent":{"source_session":"/earlier"}}});
        create_dir(&layout.frozen(INCUMBENT_ITERATION)).unwrap();
        write_json_atomic(&layout.ledger(), &json!({"format_version":1,"request":{},"session_id":"s","limits":limits(),"iterations":1,"calls":[],
            "trials":[{"iteration":1,"call_id":1,"status":"evaluated","evaluation":{"eligible":true},"candidate":{"candidate_manifest":"c.json","rationale":"r","data_access_analysis":"d"}}],
            "incumbent":incumbent,"closed":{"status":"closed"}})).unwrap();
        for record in ["candidate.json", "manifest.json"] {
            write_json_atomic(&layout.frozen(INCUMBENT_ITERATION).join(record), &json!({})).unwrap();
        }
        write_json_atomic(&layout.qualification(INCUMBENT_ITERATION), &json!({"qualified":true})).unwrap();
        let admitted = admitted_candidate(&source).unwrap();
        assert_eq!((admitted.iteration, admitted.submission.candidate_manifest.as_path()), (0, Path::new("verus-query.json")));
        fs::remove_dir_all(root).unwrap();
    }
}
