//! `gendb engine final-evaluation REQUEST RUN_DIR VERSION [SCALE [WORKLOAD]]` (run by the operator, never
//! automatically): the full protocol ([`super::protocol::FINAL`]) of one admitted version of a general-line run at one
//! scale of its ladder (default: the run's current scale; `-` names the default), for reporting the final numbers. In a
//! run of several workloads (`engine::stage`: a stage run, or `engine.workloads`) `WORKLOAD` names the workload
//! (default: the goal, the primary): the version is evaluated in that workload's library over its request's scales
//! (default: its last scale, where the run times it), with its inputs prepared under the run's records of that
//! workload (`engine/kept/<name>/scales/<scale>/` for a stage run's kept one, `engine/workloads/<name>/scales/<scale>/`
//! for a member of `engine.workloads`). A check workload is never timed: its final evaluation is refused. The run's own
//! timings are the development plan's (1 warm + 1 hot call per cell); this one:
//! 1. resolves the version's admitted storages at the scale (`EngineBench::admitted_runnable`: a derived storage's asset
//!    built by its verified builder when missing; a flat storage's must exist, `gendb prepare-flat-storage`);
//! 2. times it alone over every official cell, 1 warm + 3 hot calls at every worker count, the cell's time the median
//!    hot call (`EngineBench::official_matrix`), and scores it (`engine::score`);
//! 3. checks the templates not unfinished there (`EngineBench::finished_checks` under the final plan): one call at every
//!    visible binding at 64 workers, and the variants of the templates finished at every worker count timed at the
//!    scale (1 warm + 1 hot), with the variant/template ratio report (`engine::timing::variant_ratios`, no threshold);
//! 4. profiles it (`EngineBench::profile_runnable`): every template at the worker count of its largest gap.
//!
//! It reuses the run's functions and adds no protocol of its own. Records go under
//! `RUN_DIR/engine/final/<version>-<scale>[-N]/` (in a run of several workloads `<version>-<workload>-<scale>[-N]/`; a
//! fresh directory per evaluation): `official-matrix.json`, `score.json`,
//! `qualification/`, `variant-matrix.json`, `variant-ratios.json`, `PROFILE.md`, `profile/` and `final-evaluation.json`
//! (the plan, the score, the checks, the profile, each step's wall time; every cell's load average is in its matrix).
//! A failed cell or a refused answer of the admitted version is an incident: the record names it under `incidents` and
//! the command ends with an error naming the record.
//!
//! The run's other records are only read (the version tree, its cells and the main line stay as the run timed them).
//! The scale's inputs are prepared as the run prepares them (`engine::rounds::prepare_engine_scale`, reusing its records
//! under `engine/scales/<scale>/`). Every cell holds the host's timing lease, so it never overlaps another timing on
//! the host. The user's stop (`process_stop`) is not installed: the run directory's process records stay the run
//! controller's.

use super::acceptance::{CheckedEngine, StepTimes, fresh_directory};
use super::branches::{LadderState, framework_error, framework_role, open_run};
use super::protocol::FINAL;
use super::role::write_matrix;
use super::rounds::{PreparedEngine, engine_directory, member_directory, prepare_scale_in};
use super::timing::{EngineMatrix, variant_ratios};
use super::tree::VersionTree;
use crate::controller::records::{now_unix_ms, read_json, write_json_atomic};
use crate::controller::request::{MemberRole, WorkloadForm, WorkloadRequest};
use crate::controller::workload_run::WorkloadError;
use gendb_frontend::parser::SqlParser;
use gendb_verification::admission::AdmissionError;
use serde_json::{Value, json};
use std::path::Path;

/// The record file of one final evaluation in its directory.
pub const FINAL_EVALUATION_FILE: &str = "final-evaluation.json";

/// The final evaluation of `version` at `scale` on `workload` (module documentation). Returns its record; an incident
/// is an error after the record is written.
pub async fn final_evaluation(request: &WorkloadRequest, run_dir: &Path, version: &str, scale: Option<&str>, workload: Option<&str>, framework_executable: &Path) -> Result<Value, WorkloadError> {
    let (root, _) = open_run(request, run_dir)?;
    let engine_dir = engine_directory(&root);
    if VersionTree::read(&engine_dir)?.version(version).is_none() {
        return Err(WorkloadError::invalid(format!("{version} is not an accepted version of the run {}", root.display())));
    }
    // The workload's request and the directory of its preparation records: the run's own, or another workload's.
    let set = request.workload_set()?;
    let (subject, records, workload) = match set.form {
        WorkloadForm::One => match workload {
            None => (request.clone(), engine_dir.clone(), None),
            Some(name) => return Err(WorkloadError::invalid(format!("workload {name}: final-evaluation takes WORKLOAD in a run of several workloads only (engine.stage, engine.workloads)"))),
        },
        form => {
            let primary = &set.members[0];
            match workload.filter(|name| *name != primary.name) {
                None => (request.clone(), engine_dir.clone(), Some(primary.name.clone())),
                Some(name) => {
                    let member = set.member(name).ok_or_else(|| WorkloadError::invalid(format!("workload {name} is not a workload of the run ({})", set.names().join(", "))))?;
                    if member.role == MemberRole::Check {
                        return Err(WorkloadError::invalid(format!("workload {name} is a check workload: it is never timed (its answers are checked with every submission), so it has no final evaluation")));
                    }
                    (member.request.clone(), member_directory(&root, form, name), Some(name.to_string()))
                }
            }
        }
    };
    let scales = &subject.engine()?.scales;
    let index = match scale {
        Some(name) => scales.iter().position(|s| s.name == name).ok_or_else(|| {
            WorkloadError::invalid(format!("{name} is not a scale of the ladder ({})", scales.iter().map(|s| s.name.as_str()).collect::<Vec<_>>().join(", ")))
        })?,
        // A run of several workloads times every workload at its last scale; a run with one workload is at its ladder's
        // current one.
        None if workload.is_some() => scales.len() - 1,
        None => LadderState::read(&engine_dir)?.current,
    };
    let scale_name = scales[index].name.clone();
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let prepared = prepare_scale_in(&subject, index, &records, &parser, framework_executable).await?;
    let label = match &workload {
        Some(name) => format!("{version}-{name}-{scale_name}"),
        None => format!("{version}-{scale_name}"),
    };
    let dir = fresh_directory(&engine_dir.join("final"), &label).map_err(framework_error)?;
    let started_unix_ms = now_unix_ms();
    let mut record = evaluate(&subject, &prepared, &engine_dir, version, &dir).map_err(framework_error)?;
    record["version"] = json!(version);
    record["scale"] = json!(scale_name);
    if let Some(name) = &workload {
        record["workload"] = json!(name);
        record["library"] = json!(subject.library);
    }
    record["directory"] = json!(dir);
    record["window"] = json!({"start_unix_ms":started_unix_ms,"end_unix_ms":now_unix_ms()});
    let file = dir.join(FINAL_EVALUATION_FILE);
    write_json_atomic(&file, &record)?;
    match record["incidents"].as_array().filter(|incidents| !incidents.is_empty()) {
        Some(incidents) => Err(framework_error(AdmissionError::execution(format!(
            "incident: admitted version {version} failed its final evaluation at {scale_name} ({}); record {}",
            incidents.iter().filter_map(Value::as_str).collect::<Vec<_>>().join("; "),
            file.display()
        )))),
        None => Ok(record),
    }
}

/// Steps 1-4 of the module documentation under `dir`: the record without its identity fields. A framework failure is an
/// `Err`; a failed cell or a refused answer of the version is recorded under `incidents`.
fn evaluate(request: &WorkloadRequest, prepared: &PreparedEngine, engine_dir: &Path, version: &str, dir: &Path) -> Result<Value, AdmissionError> {
    let plan = &FINAL;
    let mut role = framework_role(request, prepared, engine_dir, dir)?;
    let mut bench = role.view();
    let mut steps = StepTimes::default();
    let mut incidents: Vec<String> = vec![];
    let run = steps.time("storages", || bench.admitted_runnable(version, &dir.join("storages")))?;
    let matrix = steps.time("timing", || bench.official_matrix(&run, plan.cell_calls, &dir.join("timing")))?;
    let official = write_matrix(&matrix, &dir.join("official-matrix.json"))?;
    let scored = match bench.score_matrix(&matrix) {
        Ok(scored) => Some(scored),
        Err(error) => {
            incidents.push(format!("the official cells have no score: {error}"));
            None
        }
    };
    let (score, checks, ratios, profile) = match &scored {
        Some(scored) => {
            write_json_atomic(&dir.join("score.json"), &json!(scored)).map_err(AdmissionError::tool)?;
            let subject = CheckedEngine { library: &run.library, inputs: &run.inputs, frozen: None };
            let checks = steps.time("checks", || bench.finished_checks(plan, &subject, scored, dir)).unwrap_or_else(|reason| {
                incidents.push(format!("the finished templates' checks: {reason}"));
                json!({"status":"failed","error":reason})
            });
            let ratios = variant_ratio_report(&matrix, &checks, dir)?;
            let profile = steps.time("profile", || bench.profile_runnable(version, &run.library, &run.inputs, scored, dir));
            (json!(scored), checks, ratios, profile)
        }
        None => {
            let reason = json!({"status":"not_run","reason":"the official cells have no score (an incident above)"});
            (Value::Null, reason.clone(), reason.clone(), reason)
        }
    };
    Ok(json!({"format_version":1,"plan":plan.record(),"official":official,"score":score,"finished_checks":checks,"variant_ratios":ratios,"profile":profile,
        "storages":run.inputs.iter().map(|u| json!({"name":u.name,"parts":u.parts_directory})).collect::<Vec<_>>(),
        "steps":steps.record(),"incidents":incidents,
        "meaning":"the final evaluation of an admitted version for reporting (the full protocol); the run's development evaluations decide acceptance and the main line, never this record"}))
}

/// The variant/template ratio report of the timed variants of `checks` against the official medians of `official`,
/// written as `variant-ratios.json` (no threshold; `Null` when no variant matrix was written).
fn variant_ratio_report(official: &EngineMatrix, checks: &Value, dir: &Path) -> Result<Value, AdmissionError> {
    let Some(file) = checks["variants"]["file"].as_str().map(Path::new).filter(|f| f.is_file()) else { return Ok(Value::Null) };
    let variants: EngineMatrix = read_json(file).map_err(AdmissionError::tool)?;
    let report = variant_ratios(official, &variants);
    let out = dir.join("variant-ratios.json");
    write_json_atomic(&out, &json!(report)).map_err(AdmissionError::tool)?;
    Ok(json!({"summary":report.summary,"without_template":report.without_template,"note":report.note,"file":out}))
}
