//! Tests of runs of several workloads, with
//! canned steps and fixture libraries: no Verus, no timing, no data. A stage run's kept part, the admissions in lockstep
//! and the selection in every library, a stage version's folder, the stage view against its stage fixture, the
//! stage root with a canned framework, and the tools' `workload` argument; then a run of several workloads
//! (`engine.workloads`): the order of a submission's evaluation and the combined decision, the root with one side per
//! workload, its folder, a version's records and the workloads view against the workloads fixture, the workspace
//! of a session, the export round trip and the check of a seed.

use super::members::{MemberStatuses, MemberSteps, RaceScores, evaluate_members};
use super::records::{MemberPart, MemberTiming, StorageFacts, WorkloadPart, combined_record, general_record, stage_seed_manifest, write_member, write_stage_code, write_workload};
use super::root::{OutOfTheBox, OutOfTheBoxStatus, RootPlan, RootWork, SideAdmission, SideFacts, SideKeep, SideSource, seed_root};
use super::view::{ViewMember, ViewWorkload, stage_view, workloads_view};
use super::*;
use crate::controller::request::{MemberRole, Seed, WorkloadForm};
use crate::engine::acceptance::{AdmissionIntent, NOT_BETTER_REASON, select_version};
use crate::engine::score::{CellStatus, NormalizedTime, Score};
use crate::engine::submission::members::{MemberModule, MemberRecord, write_source_root};
use crate::engine::submission::{EngineManifest, FrozenWorkload};
use crate::engine::tree::{MainLineChange, NodeKind, TreeNode, append_main_line, findings_markdown, write_node};
use crate::prompts::engine_facts::general::stage::{FIXTURE, fixture_shape_errors};
use crate::storage::engine_library::tests::{Fixture, payload, remove_scratch};
use gendb_artifacts::ContentId;
use gendb_artifacts::verus::{VerusStorageUseV1, engine_selections};
use std::collections::BTreeMap;

fn scratch(name: &str) -> PathBuf {
    let root = crate::controller::test_support::scratch_root(name);
    fs::create_dir_all(&root).unwrap();
    root
}

/// The stage fixture with `<run>` as `run`.
fn fixture(run: &Path) -> Value {
    serde_json::from_str(&FIXTURE.replace("<run>", &run.display().to_string())).unwrap()
}

/// The workloads fixture with `<run>` as `run`.
fn members_fixture(run: &Path) -> Value {
    serde_json::from_str(&crate::prompts::engine_facts::general::workloads::FIXTURE.replace("<run>", &run.display().to_string())).unwrap()
}

fn recorded(scale: &str, finished: usize, cells: usize, billionths: u64, record: &Path) -> RecordedScore {
    RecordedScore { scale: scale.into(), score: Score { finished, normalized_time: NormalizedTime::from_billionths(billionths) }, cells, beats_both: false, record: record.to_path_buf() }
}

fn finished(template: &str, workers: usize, median_ns: u64) -> super::super::score::CellResult {
    super::super::score::CellResult { template: template.into(), workers, status: CellStatus::Finished { median_ns } }
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn write_value(path: &Path, value: &Value) {
    write(path, &serde_json::to_string_pretty(value).unwrap());
}

/// A kept workload's preparation as its steps would leave it, its race report at `<dir>/race.json`.
fn kept_keep(name: &str, dir: &Path, race: &Value) -> MemberKeep {
    fs::create_dir_all(dir).unwrap();
    write_value(&dir.join("race.json"), race);
    MemberKeep { name: name.into(), frozen: dir.join("frozen"), evaluation: dir.to_path_buf(), build: json!({}), evidence: vec![],
        record: json!({"role":"kept","scale":"sf100","race":dir.join("race.json")}) }
}

// ------------------------------------------------------------------------------------------------ a stage run: the evaluation

/// After the goal decided a submission was better, every kept workload runs in order and its timing
/// never decides: a kept workload slower than the parent, with an unfinished cell, is recorded `timed` and the
/// submission goes on to its admission. A kept workload's Verus failure refuses the submission (its reason names the
/// workload; the goal's score is kept; the later kept workloads stay `not_run` and never run); a wrong answer refuses it
/// and is flagged; a framework failure stays the framework's. A goal not better leaves every kept workload `not_run`.
#[test]
fn kept_workloads_run_after_the_goal_and_never_decide() {
    let root = scratch("stage-kept-evaluation");
    let names = vec!["tpch".to_string(), "ssb".to_string()];
    let goal_score = recorded("sf3", 17, 18, 128_456_566_853, &root.join("race.json"));
    // Slower and unfinished on a kept workload: recorded, never deciding.
    let slower = json!({"candidate_better":false,"pairs":[{"template":"Q01","workers":1,"candidate_over_parent":1.4}],
        "candidate_score":{"cells":[{"template":"Q01","workers":1,"status":{"status":"unfinished","reason":"over_time_limit"}}]}});
    let accepted = root.join("accepted");
    let mut ran = vec![];
    let kept = evaluate_kept_workloads(&names, &accepted, |name| {
        ran.push(name.to_string());
        Ok(kept_keep(name, &kept_evaluation_dir(&accepted, name), &slower))
    })
    .unwrap_or_else(|_| panic!("a slower kept workload never refuses"));
    assert_eq!((ran.as_slice(), kept.len()), (names.as_slice(), 2));
    let statuses = kept_statuses(&accepted, &names);
    assert!(statuses.iter().all(|s| s.status == "timed" && s.reason.is_none()), "{statuses:?}");
    assert_eq!(statuses[0].race.as_deref(), Some(kept_evaluation_dir(&accepted, "tpch").join("race.json").as_path()));
    // The stage fixture's shape of the evaluation's kept part.
    let evaluation = json!({"kept_workloads":statuses});
    assert_eq!(fixture_shape_errors(&evaluation, &fixture(&root)["evaluation"]), Vec::<String>::new());

    // A Verus failure on the first kept workload: refused, named, the goal's score kept, the second not run.
    let refused_dir = root.join("verus");
    let mut ran = vec![];
    let outcome = evaluate_kept_workloads(&names, &refused_dir, |name| {
        ran.push(name.to_string());
        Err(Failure::Candidate { reason: "proof_failure: Verus: 2 errors in agent/workload/open.rs".into(), flagged: false, score: None }.of_kept(name, &goal_score))
    });
    match outcome {
        Err(Failure::Candidate { reason, flagged: false, score: Some(score) }) => {
            assert!(reason.starts_with("workload tpch: proof_failure"), "{reason}");
            assert_eq!(score, goal_score, "an attempt keeps the goal's score");
        }
        _ => panic!("a kept workload's Verus failure refuses the submission"),
    }
    assert_eq!(ran, ["tpch"], "the later kept workloads do not run");
    let statuses = kept_statuses(&refused_dir, &names);
    assert_eq!((statuses[0].status.as_str(), statuses[1].status.as_str()), ("refused", "not_run"));
    assert!(statuses[0].reason.as_deref().unwrap().starts_with("workload tpch:"));

    // A wrong answer on the second: refused and flagged; the first was timed.
    let wrong_dir = root.join("wrong");
    let outcome = evaluate_kept_workloads(&names, &wrong_dir, |name| match name {
        "tpch" => Ok(kept_keep(name, &kept_evaluation_dir(&wrong_dir, name), &slower)),
        _ => Err(Failure::Candidate { reason: "refusal: an answer in the interleaved timing was refused (Q3 at 64 workers)".into(), flagged: true, score: None }.of_kept(name, &goal_score)),
    });
    assert!(matches!(outcome, Err(Failure::Candidate { flagged: true, .. })), "a kept workload's wrong answer is flagged");
    let statuses = kept_statuses(&wrong_dir, &names);
    assert_eq!((statuses[0].status.as_str(), statuses[1].status.as_str()), ("timed", "refused"));

    // A framework failure (an admitted parent's incident) stays the framework's.
    let framework = evaluate_kept_workloads(&names, &root.join("framework"), |name| Err(Failure::Framework(AdmissionError::tool("incident: admitted parent v003 failed")).of_kept(name, &goal_score)));
    assert!(matches!(framework, Err(Failure::Framework(ref e)) if e.message.starts_with("workload tpch: incident")));

    // A goal not better: no kept step ran, every kept workload is `not_run`.
    let statuses = kept_statuses(&root.join("not-better"), &names);
    assert!(statuses.iter().all(|s| s.status == "not_run" && s.race.is_none()), "{statuses:?}");
    fs::remove_dir_all(&root).unwrap();
}

/// An accepted submission is admitted in every
/// library as the same library version, and the main line selects it in every library; a library out of step is a
/// framework error.
#[test]
fn every_crate_is_admitted_in_lockstep_and_selected_in_every_library() {
    let root = scratch("stage-lockstep");
    let lineage = |kind: &str, parents: Vec<ContentId>| Some(gendb_artifacts::verus::VerusEngineLineageV1 { branch: "main".into(), kind: kind.into(), parents });
    let mut libraries: Vec<Fixture> = ["library-tpch", "library-sec", "library-anyschema"].iter().map(|name| Fixture::new(&root, name)).collect();
    // Each library's storage (an engine reads at least one), and its root as its first version.
    let mut uses = vec![];
    let mut roots = vec![];
    for library in &mut libraries {
        let flat = library.storage("flat_lineitem", &[(0, &[0, 1])], payload("lineitem", &["l_a", "l_b"]), None, 2);
        let root_version = library.engine_with_lineage(&[("flat_lineitem", flat)], lineage("framework_generated", vec![]));
        assert_eq!(root_version.version, 1, "every root is its library's first version");
        uses.push(flat);
        roots.push(root_version.package_id);
    }
    // v001: the primary's library admits it as version 2; every other crate must take version 2 too.
    let primary_v1 = libraries[0].engine_with_lineage(&[("flat_lineitem", uses[0])], lineage("branch", vec![roots[0]]));
    let keeps = [kept_keep("sec", &root.join("evaluation/workloads/sec"), &json!({})), kept_keep("anyschema", &root.join("evaluation/workloads/anyschema"), &json!({}))];
    let mut admitted_packages = BTreeMap::new();
    let admitted = admit_in_lockstep(primary_v1.version, &keeps, |keep| {
        let index = if keep.name == "sec" { 1 } else { 2 };
        let version = libraries[index].engine_with_lineage(&[("flat_lineitem", uses[index])], lineage("branch", vec![roots[index]]));
        admitted_packages.insert(keep.name.clone(), version.package_id);
        Ok(json!({"library_version":version.version,"package":version.package_id}))
    })
    .unwrap();
    assert_eq!(admitted.iter().map(|(n, a)| (n.as_str(), a["library_version"].as_u64())).collect::<Vec<_>>(), [("sec", Some(2)), ("anyschema", Some(2))]);
    // The main line selects v001 in every library.
    for library in &libraries {
        select_version(&library.store, "v001", "race", None).unwrap();
    }
    assert_eq!(engine_selections(&libraries[0].store).unwrap().first().map(|(_, s)| s.package), Some(primary_v1.package_id));
    assert_eq!(engine_selections(&libraries[1].store).unwrap().first().map(|(_, s)| s.package), admitted_packages.get("sec").copied());
    assert_eq!(engine_selections(&libraries[2].store).unwrap().first().map(|(_, s)| s.package), admitted_packages.get("anyschema").copied());
    // A library one version ahead (an admission the primary's library does not have) breaks the lockstep.
    let broken = admit_in_lockstep(primary_v1.version, &keeps[..1], |_| {
        let version = libraries[1].engine_with_lineage(&[("flat_lineitem", uses[1])], lineage("branch", vec![roots[1]]));
        Ok(json!({"library_version":version.version}))
    });
    assert!(broken.unwrap_err().message.starts_with("library_lockstep_broken: workload sec"));
    remove_scratch(&root);
}

// ------------------------------------------------------------------------------------------------ a stage run: the root

/// A seed version of another run under `<root>/seed-run`: its code, manifest, notebook and the run's tree and findings.
fn seed_run(root: &Path) -> SeedVersion {
    let run = root.join("seed-run");
    let version = run.join("engine/versions/v016");
    write(&version.join("code/agent/mod.rs"), "//! The seed engine.\nverus! {\npub fn engine() {}\n}\n");
    write(&version.join("code/agent/tables.rs"), "//! Its tables.\n");
    write(&version.join("node.json"), "{\"accepted\":true}");
    let manifest = EngineManifest::example(&[("narrowpack".into(), ContentId::from_bytes([3; 32]))]);
    write_value(&version.join("seed-manifest.json"), &json!(manifest));
    write(&version.join("NOTES.md"), "# Notes\n\nThe seed's notebook.\n");
    write(&run.join("engine/TREE.md"), "# Version tree\n");
    write(&run.join("engine/FINDINGS.md"), "# Findings\n");
    SeedVersion { run, version: "v016".into() }
}

/// The frozen crate a canned side leaves under `<dir>/frozen` (its candidate record with `member`, its manifest over
/// the workload alone, its shared engine and, for an own module, its module).
fn canned_crate(dir: &Path, workload: &str, member: Option<MemberRecord>) -> PathBuf {
    let frozen = dir.join("frozen");
    write(&frozen.join("crate/src/agent/mod.rs"), &format!("//! The side of {workload}.\n"));
    // Its frozen family instance (the same storage name in every workload).
    write(&frozen.join("storages/colpack/storage.json"), &format!("{{\"workload\":\"{workload}\"}}"));
    if member.as_ref().is_some_and(|m| m.module == MemberModule::Own) {
        write(&frozen.join("crate/src/agent/workload/mod.rs"), &format!("//! The module of {workload}.\n"));
    }
    let engine = FrozenEngine {
        kind: "verus_engine".into(),
        format_version: 1,
        entry_identity: "gendb-verus-engine-entry-v1".into(),
        toolkit_digest: "t".into(),
        storage_uses: vec![],
        compiler: Default::default(),
        modules: vec![],
        author_files: vec![],
        framework_files: vec![],
        notes: String::new(),
        rule_set: Value::Null,
        workload: Some(FrozenWorkload { name: workload.into(), module_files: vec![], flat_access: gendb_verification::obligations::FlatAccess::Uniform, module_report: json!({"lines":0}), member }),
    };
    write_value(&frozen.join("candidate.json"), &json!(engine));
    let manifest = EngineManifest { storage_uses: vec![], workloads: vec![crate::engine::submission::WorkloadModules { name: workload.into(), storage_uses: vec![], modules: vec![] }],
        ..EngineManifest::example(&[]) };
    write_value(&frozen.join("manifest.json"), &json!(manifest));
    frozen
}

/// The root's work with canned steps: a fixture crate and evaluation per side, one library per workload (its admitted
/// frozen crates, adopted again on resume), and counts of what ran. `check` names the check workloads (answered, never
/// timed); `admissible` the workloads whose seed's code is admissible out of the box.
struct CannedRoot {
    admissible: Vec<String>,
    check: Vec<String>,
    libraries: BTreeMap<String, Vec<PathBuf>>,
    admissions: BTreeMap<String, u32>,
    evaluated: Vec<(String, SideSource)>,
    tried: Vec<String>,
    crash_after_admitting: Option<String>,
    selections: u32,
}

impl CannedRoot {
    fn new(admissible: &[&str]) -> Self {
        Self { admissible: admissible.iter().map(|s| s.to_string()).collect(), check: vec![], libraries: BTreeMap::new(), admissions: BTreeMap::new(), evaluated: vec![], tried: vec![],
            crash_after_admitting: None, selections: 0 }
    }

    /// A frozen crate and the evaluation of a side under `dir`, and the intent of its admission.
    fn side(&self, dir: &Path, workload: &str, source: SideSource, scale: &str, cells: usize) -> AdmissionIntent {
        let member = MemberRecord { module: if workload == "anyschema" { MemberModule::None } else { MemberModule::Own }, families: vec![], family_storages: vec![], plain_storages: vec![],
            inherited_storages: if workload == "anyschema" { vec![] } else { vec![format!("{workload}pack")] }, own_module_lines: if workload == "anyschema" { 0 } else { 100 }, plan_lines: 0,
            shared_sources_digest: format!("{workload}-digest") };
        let frozen = canned_crate(dir, workload, Some(member));
        let evaluation = dir.join("evaluation");
        let check = self.check.iter().any(|c| c == workload);
        let (score, check_record) = if check {
            write_value(&evaluation.join("check.json"), &json!({"calls":12,"agreed":12}));
            (None, Some(json!({"calls":12,"agreed":12,"file":evaluation.join("check.json")})))
        } else {
            write_value(&evaluation.join("score.json"), &json!({"score":{"finished":cells,"normalized_time":"2.500000000"}}));
            write_value(&evaluation.join("official-matrix.json"), &json!({"cells":[]}));
            (Some(recorded(scale, cells, cells, 2_500_000_000, &evaluation.join("score.json"))), None)
        };
        let keep = SideKeep { source, frozen, score, cells: if check { vec![] } else { vec![finished("Q1", 1, 5)] }, checks: json!({"variants":{"run":"answers_at_first_scale"}}),
            storage_policy: json!({"serving_bytes":1000,"budget_decision":"plain storage only at sf3"}), check: check_record };
        AdmissionIntent { evaluation, build: json!({"verification":{"errors":0,"verified":1500},"wall_ns":7}), evidence: vec![], keep: json!(keep), written_unix_ms: 1 }
    }

    fn scale_of(workload: &str) -> &'static str {
        match workload {
            "tpch" => "sf100",
            "anyschema" => "tiny",
            _ => "sf3",
        }
    }
}

impl RootWork for CannedRoot {
    fn out_of_the_box(&mut self, workload: &str, dir: &Path) -> Result<(OutOfTheBox, Option<AdmissionIntent>), AdmissionError> {
        self.tried.push(workload.to_string());
        if !self.admissible.iter().any(|a| a == workload) {
            let error = AdmissionError::refusal("Verus rejected: rustc\nerror[E0433]: failed to resolve: could not find `narrowpack` in `stores`\n   --> src/agent/tables.rs:214:36\nmore");
            let (status, step) = super::root::blocked_at_build(&error);
            let oob = OutOfTheBox { status, step: step.into(), first_errors: super::root::first_errors(&error.message), score: None, record: PathBuf::new(),
                directory: dir.to_path_buf(), admissible: false, at_unix_ms: 1 };
            return Ok((oob, None));
        }
        // A stage run's goal (`sec` in its tests) is the seed's side; a run of several workloads' member its own kind.
        let source = if workload == "sec" { SideSource::Seed } else { SideSource::OutOfTheBox };
        let intent = self.side(dir, workload, source, Self::scale_of(workload), 18);
        let keep: SideKeep = serde_json::from_value(intent.keep.clone()).unwrap();
        let step = if keep.check.is_some() { "answers" } else { "timing" };
        let oob = OutOfTheBox { status: OutOfTheBoxStatus::Verified, step: step.into(), first_errors: vec![], score: keep.score, record: PathBuf::new(),
            directory: dir.to_path_buf(), admissible: true, at_unix_ms: 1 };
        Ok((oob, Some(intent)))
    }

    fn evaluate_side(&mut self, workload: &str, source: SideSource, dir: &Path) -> Result<AdmissionIntent, AdmissionError> {
        self.evaluated.push((workload.to_string(), source));
        Ok(self.side(dir, workload, source, Self::scale_of(workload), if workload == "tpch" { 12 } else { 18 }))
    }

    fn admit_side(&mut self, workload: &str, intent: &AdmissionIntent) -> Result<Value, AdmissionError> {
        let keep: SideKeep = serde_json::from_value(intent.keep.clone()).unwrap();
        let library = self.libraries.entry(workload.to_string()).or_default();
        // The library holds this frozen crate's admission already: adopted, not admitted again.
        let version = match library.iter().position(|f| *f == keep.frozen) {
            Some(index) => index + 1,
            None => {
                library.push(keep.frozen.clone());
                *self.admissions.entry(workload.to_string()).or_default() += 1;
                if self.crash_after_admitting.as_deref() == Some(workload) {
                    self.crash_after_admitting = None;
                    return Err(AdmissionError::tool("the controller stopped after the library admission"));
                }
                library.len()
            }
        };
        let package = match workload {
            "tpch" => ContentId::from_bytes([2; 32]),
            "anyschema" => ContentId::from_bytes([3; 32]),
            _ => ContentId::from_bytes([1; 32]),
        };
        Ok(json!({"library_version":version,"package":package,"uses":[VerusStorageUseV1 { name: format!("{workload}_flat"), package: ContentId::from_bytes([9; 32]) }]}))
    }

    fn profile_side(&mut self, _workload: &str, _side: &SideAdmission) -> Value {
        json!({"status":"profiled"})
    }

    fn select_root(&mut self) -> Result<ContentId, AdmissionError> {
        self.selections += 1;
        Ok(ContentId::from_bytes([7; 32]))
    }
}

/// The plan of a stage root over the goal `sec` at sf3 and the kept `tpch` at sf100.
fn plan<'a>(engine_dir: &'a Path, seed: &SeedVersion, branches: &'a [String]) -> RootPlan<'a> {
    let facts = |name: &str, role: WorkloadRole, scale: &str| SideFacts { name: name.into(), role, member: if role == WorkloadRole::Goal { MemberRole::Counted } else { MemberRole::Kept },
        primary: role == WorkloadRole::Goal, seed: None, scale: scale.into(), library: PathBuf::from(format!("/libraries/{name}")), budget_bytes: 5_439_582_957, plain_storage_bytes: 7_746_659_210 };
    RootPlan { engine_dir, form: WorkloadForm::Stage, seed: Some(Seed::Run { version: seed.clone(), workload: None }), workloads: vec![facts("sec", WorkloadRole::Goal, "sf3"), facts("tpch", WorkloadRole::Kept, "sf100")], branches }
}

/// An out-of-the-box failure is recorded (status, step, first errors, the markdown) and the root is
/// seeded per workload: version 0 on the goal, the seed on the kept workload, each admitted once in its library as its
/// first version, then selected and on the main line; the folder holds the seed's code, notebook and history, a
/// stage-form manifest with every workload's uses, and every workload's records (`version.json` `workloads` in the stage
/// fixture's shape).
#[test]
fn an_out_of_the_box_refusal_is_recorded_and_the_root_is_seeded_per_workload() {
    let root = scratch("stage-root-refused");
    let engine_dir = root.join("run/engine");
    let seed = seed_run(&root);
    let branches = ["b1".to_string()];
    let mut work = CannedRoot::new(&[]);
    let record = seed_root(&mut work, &plan(&engine_dir, &seed, &branches)).unwrap();
    assert_eq!((record["status"].as_str(), record["one_engine"].as_bool()), (Some("admitted"), Some(false)));
    assert_eq!(work.evaluated, [("sec".to_string(), SideSource::VersionZero), ("tpch".to_string(), SideSource::Seed)]);
    assert_eq!((work.admissions["sec"], work.admissions["tpch"], work.selections), (1, 1, 1));
    let oob = OutOfTheBox::read(&engine_dir).unwrap();
    assert_eq!((oob.status, oob.step.as_str()), (OutOfTheBoxStatus::NotAssembled, "compile"));
    assert_eq!(oob.first_errors, ["error[E0433]: failed to resolve: could not find `narrowpack` in `stores`", "   --> src/agent/tables.rs:214:36"]);
    let markdown = fs::read_to_string(&oob.record).unwrap();
    assert!(markdown.contains("not assembled: rustc stopped it") && markdown.contains("version 0 over its flat storage"), "{markdown}");
    let v0 = engine_dir.join("versions/v000");
    let node: TreeNode = read_json(&v0.join("node.json")).unwrap();
    assert_eq!((node.kind, node.scale.as_str(), node.parents.len()), (NodeKind::StageSeed, "sf3", 0));
    assert_eq!(fs::read_to_string(v0.join("code/agent/tables.rs")).unwrap(), "//! Its tables.\n", "the first session continues from the seed's code");
    assert!(v0.join("code-view/agent/mod.rs.md").is_file() && v0.join("stage1/TREE.md").is_file() && v0.join("stage1/FINDINGS.md").is_file() && v0.join("NOTES.md").is_file());
    assert!(v0.join("workloads/sec/code/agent/mod.rs").is_file(), "the goal's version 0 code is kept beside");
    let manifest: EngineManifest = read_json(&v0.join("seed-manifest.json")).unwrap();
    assert!(manifest.storage_uses.is_empty() && manifest.workloads.iter().map(|w| (w.name.as_str(), w.storage_uses[0].name.as_str(), w.modules.len())).eq([("sec", "sec_flat", 0), ("tpch", "tpch_flat", 0)]));
    assert_eq!(manifest.modules[0].file, "mod.rs", "the seed's module list");
    let version: Value = read_json(&v0.join("version.json")).unwrap();
    assert_eq!(fixture_shape_errors(&version["workloads"], &fixture(&root)["version"]["workloads"]), Vec::<String>::new());
    assert_eq!(version["origin"]["out_of_the_box"]["status"], "not_assembled");
    for file in ["workloads/tpch/score.json", "workloads/tpch/cells/sf100.json", "workloads/tpch/admission.json", "workloads/tpch/workload.json", "workloads/sec/workload.json",
        "cells/sf3.json", "score.json", "admission.json"] {
        assert!(v0.join(file).is_file(), "{file}");
    }
    let tree = VersionTree::read(&engine_dir).unwrap();
    assert_eq!((tree.main_line_head(), tree.main_line[0].reason.as_str()), (Some("v000"), "stage_seed"));
    assert_eq!(tree.workload_score("v000", "tpch").and_then(|w| w.score.as_ref()).map(|s| (s.scale.as_str(), s.score.finished)), Some(("sf100", 12)));
    assert_eq!(tree.workload_score("v000", "tpch").map(|w| w.role.as_str()), Some("kept"));
    // Idempotent: a second preparation finds the root.
    assert_eq!(seed_root(&mut work, &plan(&engine_dir, &seed, &branches)).unwrap()["status"], "present");
    assert_eq!((work.admissions["sec"], work.admissions["tpch"], work.selections), (1, 1, 1));
    fs::remove_dir_all(&root).unwrap();
}

/// A seed admissible out of the box is the goal's side (no version 0 is generated): the root is one
/// engine.
#[test]
fn an_admissible_seed_out_of_the_box_makes_the_root_one_engine() {
    let root = scratch("stage-root-one-engine");
    let engine_dir = root.join("run/engine");
    let seed = seed_run(&root);
    let branches = ["b1".to_string()];
    let mut work = CannedRoot::new(&["sec"]);
    let record = seed_root(&mut work, &plan(&engine_dir, &seed, &branches)).unwrap();
    assert_eq!(record["one_engine"], true);
    assert_eq!(work.evaluated, [("tpch".to_string(), SideSource::Seed)], "the goal's side is the out-of-the-box seed");
    let version: Value = read_json(&engine_dir.join("versions/v000/version.json")).unwrap();
    assert_eq!((version["origin"]["one_engine"].as_bool(), version["origin"]["goal_side"].as_str()), (Some(true), Some("seed")));
    assert!(!engine_dir.join("versions/v000/workloads/sec/code").exists());
    let oob = OutOfTheBox::read(&engine_dir).unwrap();
    assert!(oob.admissible && oob.view()["score"]["score"]["finished"] == 18);
    fs::remove_dir_all(&root).unwrap();
}

/// A preparation stopped after a library admission and before its record resumes from the intents:
/// nothing is evaluated again and every library holds its root once.
#[test]
fn a_resumed_root_admits_once_per_library() {
    let root = scratch("stage-root-resume");
    let engine_dir = root.join("run/engine");
    let seed = seed_run(&root);
    let branches = ["b1".to_string()];
    let mut work = CannedRoot::new(&[]);
    work.crash_after_admitting = Some("tpch".into());
    assert!(seed_root(&mut work, &plan(&engine_dir, &seed, &branches)).is_err(), "the stop after the kept library's admission");
    assert!(!engine_dir.join("versions/v000").exists() && engine_dir.join("seed/tpch/admitting.json").is_file());
    seed_root(&mut work, &plan(&engine_dir, &seed, &branches)).unwrap();
    assert_eq!(work.evaluated.iter().map(|(w, _)| w.as_str()).collect::<Vec<_>>(), ["sec", "tpch"], "no side is evaluated twice");
    assert_eq!((work.admissions["sec"], work.admissions["tpch"]), (1, 1), "every library holds its root once");
    assert_eq!(work.libraries.values().map(Vec::len).collect::<Vec<_>>(), [1, 1]);
    assert!(engine_dir.join("versions/v000/node.json").is_file());
    fs::remove_dir_all(&root).unwrap();
}

// ------------------------------------------------------------------------------------------------ a stage run: a version and the view

/// A frozen crate of workload `name` under `<frozen>`: the shared engine and that workload's module.
fn frozen_crate(frozen: &Path, name: &str) {
    write(&frozen.join("crate/src/agent/mod.rs"), "//! The shared engine.\npub mod workload;\n");
    write(&frozen.join("crate/src/agent/plan.rs"), "//! Shared planning.\n");
    write(&frozen.join(format!("crate/src/agent/{}/mod.rs", super::super::submission::WORKLOAD_MODULE)), &format!("//! The {name} module.\nfn open() {{}}\n"));
}

/// An accepted stage version's folder holds the shared engine once and every workload's
/// module, a stage-form manifest, the goal's records at its top and the kept workload's under `workloads/tpch/`; its
/// `version.json` `workloads` has the interface's shape; the tree shows the kept score beside the goal's and the
/// findings the kept effect; and the stage view over these records (goal and kept entries, the out-of-the-box record,
/// the kept workload's last race and reference) has the fixture's keys.
#[test]
fn a_stage_version_folder_holds_every_workload_and_the_view_matches_the_interface() {
    let root = scratch("stage-version-folder");
    let engine_dir = root.join("run/engine");
    let seed = seed_run(&root);
    let branches = ["b1".to_string()];
    seed_root(&mut CannedRoot::new(&[]), &plan(&engine_dir, &seed, &branches)).unwrap();
    // The frozen crates of v001 and their evaluation's records.
    let frozen = root.join("session/iterations/0001/frozen");
    frozen_crate(&frozen, "sec");
    frozen_crate(&kept_frozen_dir(&frozen, "tpch"), "tpch");
    let evaluation = root.join("session/iterations/0001/frozen/evaluation-0");
    let kept_race = kept_evaluation_dir(&evaluation, "tpch").join("race.json");
    write_value(&kept_race, &json!({"parent":"v000","pairs":[{"template":"Q01","workers":1,"candidate_over_parent":0.98}],
        "parent_score":{"score":{"finished":12,"normalized_time":"2.316701349"}},"candidate_score":{"score":{"finished":12,"normalized_time":"2.314361561"}}}));
    write_value(&evaluation.join("race.json"), &json!({"parent":"v000"}));
    let target = engine_dir.join("versions/v001");
    let staging = engine_dir.join("versions/.staging-v001");
    write_stage_code(&staging, &[("sec", &frozen), ("tpch", &kept_frozen_dir(&frozen, "tpch"))]).unwrap();
    assert_eq!(fs::read_to_string(staging.join("code/workloads/tpch/mod.rs")).unwrap(), "//! The tpch module.\nfn open() {}\n");
    assert!(staging.join("code/workloads/sec/mod.rs").is_file() && staging.join("code/agent/plan.rs").is_file() && !staging.join("code/agent/workload").exists());
    assert!(staging.join("code-view/workloads/tpch/mod.rs.md").is_file() && staging.join("code-view/agent/plan.rs.md").is_file());
    let uses = |name: &str| vec![VerusStorageUseV1 { name: name.into(), package: ContentId::from_bytes([4; 32]) }];
    let manifest = EngineManifest { workloads: vec![super::super::submission::WorkloadModules { name: "tpch".into(), storage_uses: vec![],
        modules: vec![crate::query::candidate::ModuleDeclaration { file: "mod.rs".into(), role: crate::query::candidate::ModuleRole::Helper, items: vec![] }] }],
        ..EngineManifest::example(&[]) };
    let seed_manifest = stage_seed_manifest(&manifest, &[("sec".into(), uses("encoded")), ("tpch".into(), uses("narrowpack"))]);
    assert!(seed_manifest.storage_uses.is_empty() && seed_manifest.workloads[1].modules.len() == 1 && seed_manifest.workloads[0].storage_uses[0].admitted.is_some());
    // The goal at the top, the kept workload under workloads/tpch/.
    let goal_cells = vec![finished("Q1", 1, 3_100_000_000)];
    let kept_cells = vec![finished("Q01", 1, 10_790_000_000)];
    write_value(&staging.join("cells/sf3.json"), &json!(goal_cells));
    let goal_score = recorded("sf3", 17, 18, 128_456_566_853, &evaluation.join("race.json"));
    let kept_score = recorded("sf100", 12, 12, 2_314_361_561, &kept_race);
    let build = json!({"verification":{"errors":0,"verified":5733},"wall_ns":271_000_000_000u64});
    let admission = |package: u8| json!({"library_version":2,"package":ContentId::from_bytes([package; 32]),"uses":uses("x")});
    let storage = |serving: u64| StorageFacts { serving_bytes: Some(serving), budget_bytes: 5_439_582_957, plain_storage_bytes: 7_746_659_210,
        decision: json!("changed storage within the original data size at sf3") };
    let (goal_admission, kept_admission) = (admission(1), admission(2));
    let (goal_library, kept_library) = (PathBuf::from("/libraries/sec"), PathBuf::from("/libraries/tpch"));
    let goal_part = WorkloadPart { name: "sec", role: WorkloadRole::Goal, scale: "sf3", cells: &goal_cells, score: &goal_score, timing: &target.join("race.json"), raced: true,
        parent: Some("v000"), copies: vec![], admission: &goal_admission, library: &goal_library, storage: storage(4_987_654_321), build: &build, module_lines: 3 };
    let kept_part = WorkloadPart { name: "tpch", role: WorkloadRole::Kept, scale: "sf100", cells: &kept_cells, score: &kept_score, timing: &kept_race, raced: true,
        parent: Some("v000"), copies: vec![], admission: &kept_admission, library: &kept_library, storage: storage(90_766_134_568), build: &build, module_lines: 2 };
    let mut workloads = serde_json::Map::new();
    workloads.insert("sec".into(), write_workload(&staging, &target, "v001", &goal_part, true).unwrap());
    workloads.insert("tpch".into(), write_workload(&staging, &target, "v001", &kept_part, false).unwrap());
    let workloads = Value::Object(workloads);
    assert_eq!(fixture_shape_errors(&workloads, &fixture(&root)["version"]["workloads"]), Vec::<String>::new());
    assert_eq!(workloads["tpch"]["times"]["sf100"]["race"], json!(target.join("workloads/tpch/race.json")));
    let node = TreeNode { format_version: 1, id: "v001".into(), accepted: true, kind: NodeKind::Branch, branch: "b1".into(), parents: vec!["v000".into()], scale: "sf3".into(),
        score: Some(goal_score), reason: None, session: None, iteration: Some(1), direction: Some("general encodings".into()), rationale: None, created_unix_ms: 2 };
    write_value(&staging.join("node.json"), &json!(node));
    fs::rename(&staging, &target).unwrap();
    for file in ["workloads/tpch/race.json", "workloads/tpch/cells/sf100.json", "workloads/tpch/admission.json", "workloads/tpch/workload.json", "workloads/sec/workload.json"] {
        assert!(target.join(file).is_file(), "{file}");
    }
    write_node(&engine_dir, &node).unwrap();
    append_main_line(&engine_dir, &MainLineChange { version: "v001".into(), previous: Some("v000".into()), reason: "race".into(), scale: "sf3".into(), race: None, adopted: None,
        selection: ContentId::from_bytes([8; 32]), at_unix_ms: 2 }).unwrap();
    // The tree and its views show the kept workload's score; the findings its effect.
    let tree = VersionTree::read(&engine_dir).unwrap();
    assert_eq!(tree.workload_score("v001", "tpch").and_then(|w| w.score.as_ref()).map(|s| s.score.finished), Some(12));
    let markdown = tree.markdown(&branches);
    assert!(markdown.contains("| Direction | Kept workloads (recorded, not deciding) |") && markdown.contains("| tpch sf100 12/12 finished, G 2.314361561 |"), "{markdown}");
    let findings = findings_markdown(&[json!({"node":"v001","branch":"b1","parent":"v000","accepted":true,"change":"general encodings",
        "workloads":{"tpch":{"role":"kept","scale":"sf100","effect":{"parent_finished":12,"finished":12,"parent_normalized_time":"2.316701349","normalized_time":"2.314361561","cells_faster":1,"cells_slower":0}}}}),
        json!({"node":"b1-a001","branch":"b1","parent":"v001","accepted":false,"reason":"workload tpch: proof_failure","change":"c","kept_workloads":[{"name":"tpch","status":"refused","reason":"workload tpch: proof_failure"}]})]);
    assert!(findings.contains("- Kept tpch at sf100 (recorded, not deciding): F 12 -> 12, G 2.316701349 -> 2.314361561; cells faster 1, slower 0") && findings.contains("- Kept tpch refused it: workload tpch: proof_failure"), "{findings}");
    // The stage view (the stage fixture's shape) over these records.
    let fixture = fixture(&root);
    let entry = |index: usize, role: WorkloadRole| {
        let w = &fixture["context"]["stage"]["workloads"][index];
        ViewWorkload { name: w["name"].as_str().unwrap().into(), role, scale: w["scale"].as_str().unwrap().into(), first_scale: w["first_scale"].as_str().unwrap().into(),
            library: PathBuf::from(w["library"].as_str().unwrap()), training: w["training"].clone(), budget_bytes: 5_439_582_957, plain_storage_bytes: 7_746_659_210,
            plain_storages: [ContentId::from_bytes([9; 32])].into(), original_data_record: PathBuf::from("/record.json") }
    };
    let view = stage_view(&engine_dir, "sec", &seed, &[entry(0, WorkloadRole::Goal), entry(1, WorkloadRole::Kept)]);
    assert_eq!(fixture_shape_errors(&view, &fixture["context"]["stage"]), Vec::<String>::new());
    assert_eq!(fixture_shape_errors(&view["workloads"][1], &fixture["context"]["stage"]["workloads"][1]), Vec::<String>::new(), "the kept entry too");
    assert_eq!((view["workloads"][0]["head"].as_str(), view["workloads"][0]["module_lines"].as_u64(), view["workloads"][0]["storage"]["serving_bytes"].as_u64()), (Some("v001"), Some(3), Some(4_987_654_321)));
    assert_eq!(view["workloads"][1]["last_race"], json!({"version":"v001","parent":"v000","record":target.join("workloads/tpch/race.json")}));
    assert_eq!((view["workloads"][1]["reference"]["version"].as_str(), view["workloads"][1]["reference"]["score"]["scale"].as_str()), (Some("v000"), Some("sf100")));
    assert_eq!(view["workloads"][1]["cells"][0]["template"], "Q01");
    assert_eq!((view["seed"]["out_of_the_box"]["status"].as_str(), view["seed"]["version"].as_str()), (Some("not_assembled"), Some("v016")));
    assert_eq!(view["workloads"][0]["storage"]["reads_only_plain"], false);
    fs::remove_dir_all(&root).unwrap();
}

// ------------------------------------------------------------------------------------------------ tools

/// In a run of several workloads every tool takes `workload` (absent or the own workload's name: the
/// role's own; another workload's name: that workload's side, whose bench view carries its library); in a run of one
/// workload, or naming no workload, it is refused. The tools' schema offers it only then, with every workload's
/// templates and bindings; a run with one workload lists its tools as before. A run of several workloads' description
/// names each workload's role and the primary (a check workload is a tool workload too).
#[test]
fn tools_take_the_workload_in_a_run_of_several_workloads_only() {
    use crate::engine::role::named_kept_workload;
    use crate::tools::{AuthorRole, LocalJobArguments, LocalToolContext, ToolAction, ToolWorkload, tool_list};
    let stage = Some(("sec", ["tpch", "ssb"].as_slice()));
    assert_eq!(named_kept_workload(stage, &json!({"job_name":"t"})).unwrap(), None, "absent: the goal");
    assert_eq!(named_kept_workload(stage, &json!({"workload":"sec"})).unwrap(), None, "the goal named");
    assert_eq!(named_kept_workload(stage, &json!({"workload":"ssb"})).unwrap(), Some(1));
    assert!(named_kept_workload(stage, &json!({"workload":"tpcds"})).unwrap_err().message.contains("is not a workload of this run (sec, tpch, ssb)"));
    assert!(named_kept_workload(None, &json!({"workload":"sec"})).unwrap_err().message.contains("stage run"));
    assert_eq!(named_kept_workload(None, &json!({"job_name":"t"})).unwrap(), None, "a run with one workload as before");
    // Every action accepts it (catalog too); its value is checked by the role.
    for (action, arguments) in [(ToolAction::Trial, json!({"candidate":"verus-engine.json","job_name":"t","workload":"tpch","templates":["Q01"]})),
        (ToolAction::StorageRegister, json!({"storage":"new-storages/x/verus-storage.json","job_name":"r","workload":"tpch"})), (ToolAction::Catalog, json!({"job_name":"c","workload":"tpch"}))] {
        let parsed: LocalJobArguments = serde_json::from_value(arguments).unwrap();
        assert!(parsed.check(action).is_ok() && parsed.workload.as_deref() == Some("tpch"), "{action:?}");
    }
    let mut context = LocalToolContext { format_version: crate::tools::CONTEXT_FORMAT, role: AuthorRole::Engine, author_workspace: PathBuf::from("/w"),
        session_service: crate::controller::session::LocalSessionEndpoint { format_version: 1, socket: "/s.sock".into(), token: "t".into(), query_root: "/q".into(), service_record: "/s.json".into() },
        worker_counts: vec![1, 32, 64], statements: vec![], author_contract: PathBuf::from("/w/contract/engine/index.json"), fixed_flat: false, engine_bindings: vec!["v0".into()], workloads: vec![] };
    let one = tool_list(&context);
    assert!(one.as_array().unwrap().iter().all(|t| t["inputSchema"]["properties"].get("workload").is_none()), "a run with one workload: no workload argument");
    context.workloads = vec![ToolWorkload { name: "sec".into(), templates: vec!["Q1".into(), "Q24".into()], bindings: vec!["v0".into(), "v1".into()], role: None },
        ToolWorkload { name: "tpch".into(), templates: vec!["Q01".into()], bindings: vec!["v0".into(), "v2".into()], role: None }];
    let staged = tool_list(&context);
    for tool in staged.as_array().unwrap().iter().filter(|t| t["name"] != crate::tools::WAIT_TOOL) {
        assert_eq!(tool["inputSchema"]["properties"]["workload"]["enum"], json!(["sec", "tpch"]), "{}", tool["name"]);
        assert!(tool["inputSchema"]["properties"]["workload"]["description"].as_str().unwrap().contains("absent: the goal workload sec"));
    }
    let trial = staged.as_array().unwrap().iter().find(|t| t["name"] == "trial").unwrap();
    assert_eq!(trial["inputSchema"]["properties"]["templates"]["items"]["enum"], json!(["Q1", "Q24", "Q01"]));
    assert_eq!(trial["inputSchema"]["properties"]["binding"]["enum"], json!(["v0", "v1", "v2"]));
    assert!(serde_json::to_value(&context.workloads[0]).unwrap().get("role").is_none(), "a stage run's tool context keeps its JSON identity");
    // A run of several workloads: each workload's role, the primary by default, the check workload a tool workload too.
    context.workloads = vec![ToolWorkload { name: "tpch".into(), templates: vec!["Q01".into()], bindings: vec!["v0".into()], role: Some("counted".into()) },
        ToolWorkload { name: "anyschema".into(), templates: vec!["X01".into()], bindings: vec!["v0".into(), "v1".into()], role: Some("check".into()) }];
    let members = tool_list(&context);
    let trial = members.as_array().unwrap().iter().find(|t| t["name"] == "trial").unwrap();
    let description = trial["inputSchema"]["properties"]["workload"]["description"].as_str().unwrap();
    assert!(description.contains("tpch (counted), anyschema (check)") && description.contains("absent: the primary workload tpch"), "{description}");
    assert_eq!(trial["inputSchema"]["properties"]["workload"]["enum"], json!(["tpch", "anyschema"]));
}

/// The kept workloads' statuses read back by an evaluation are what the steps wrote (`kept-workloads.json`).
#[test]
fn kept_statuses_round_trip() {
    let root = scratch("stage-statuses");
    let names = vec!["tpch".to_string()];
    let statuses = vec![KeptStatus { name: "tpch".into(), status: "timed".into(), reason: None, race: Some(root.join("race.json")) }];
    write_json_atomic(&root.join(KEPT_STATUS_FILE), &statuses).unwrap();
    assert_eq!(kept_statuses(&root, &names), statuses);
    assert_eq!(json!(statuses[0]), json!({"name":"tpch","status":"timed","reason":null,"race":root.join("race.json")}));
    fs::remove_dir_all(&root).unwrap();
}

// ------------------------------------------------------------------------------------------------ a run of several workloads: the order

/// Canned steps of a submission's workloads: what each race scores (`(parent G, candidate G)` in billionths, every
/// cell finished but the candidate's `unfinished` ones), which step of which workload fails (and whether flagged), and
/// every call in order.
struct CannedSteps {
    dir: PathBuf,
    races: BTreeMap<&'static str, (u64, u64, usize)>,
    unfinished: BTreeMap<&'static str, usize>,
    fail: Option<(&'static str, &'static str, bool)>,
    calls: Vec<String>,
}

impl CannedSteps {
    fn new(dir: &Path, races: &[(&'static str, u64, u64, usize)]) -> Self {
        Self { dir: dir.to_path_buf(), races: races.iter().map(|(n, p, c, cells)| (*n, (*p, *c, *cells))).collect(), unfinished: BTreeMap::new(), fail: None, calls: vec![] }
    }

    /// Record the call `step` of `name`; its failure when the canned failure names it.
    fn step(&mut self, step: &str, name: &str) -> Result<(), Failure> {
        self.calls.push(format!("{step}:{name}"));
        match self.fail {
            Some((s, n, flagged)) if s == step && n == name => Err(Failure::Candidate { reason: format!("refusal: canned {step} failure"), flagged, score: None }),
            _ => Ok(()),
        }
    }
}

impl MemberSteps for CannedSteps {
    fn verus(&mut self, name: &str) -> Result<(), Failure> {
        self.step("verus", name)
    }

    fn storages(&mut self, name: &str) -> Result<(), Failure> {
        self.step("storages", name)
    }

    fn answers(&mut self, name: &str) -> Result<Value, Failure> {
        self.step("answers", name)?;
        Ok(json!({"calls":12,"agreed":12,"file":self.dir.join(name).join("check.json")}))
    }

    fn race(&mut self, name: &str) -> Result<RaceScores, Failure> {
        self.step("race", name)?;
        let (parent, candidate, cells) = self.races.get(name).copied().unwrap_or((1_000_000_000, 1_000_000_000, 1));
        let score = |finished: usize, g: u64| Score { finished, normalized_time: NormalizedTime::from_billionths(g) };
        let finished = cells - self.unfinished.get(name).copied().unwrap_or(0);
        Ok(RaceScores { file: self.dir.join(name).join("race.json"), parent: score(cells, parent), candidate: score(finished, candidate), cells })
    }

    fn variants(&mut self, name: &str) -> Result<(), Failure> {
        self.step("variants", name)
    }
}

/// The workloads of the order's tests: the primary `tpch` and `sec` counted, `anyschema` check, `ssb` kept.
fn members() -> Vec<(String, MemberRole)> {
    vec![("tpch".into(), MemberRole::Counted), ("sec".into(), MemberRole::Counted), ("anyschema".into(), MemberRole::Check), ("ssb".into(), MemberRole::Kept)]
}

fn parent() -> Parent {
    Parent { id: "v000".into(), chosen: "the branch head" }
}

/// The statuses of an evaluation by workload: `(status, step)`.
fn statuses_of(dir: &Path) -> BTreeMap<String, (String, Option<String>)> {
    MemberStatuses::read(dir, &members()).into_iter().map(|s| (s.name, (s.status, s.step))).collect()
}

/// A submission better in sum while worse on one counted workload is accepted, with both counted
/// races and the combined decision recorded; the order is every crate's Verus, then every workload's storages, then the
/// check workload's answers before any timing, then the counted races (the primary's first), the decision, the kept
/// workload's race (it never decides: slower there is accepted) and every workload's variants. The evaluation's parts
/// have the workloads fixture's shape (`evaluation`).
#[test]
fn better_in_sum_while_worse_on_one_workload_is_accepted_with_every_race_recorded() {
    let root = scratch("members-better-in-sum");
    let dir = root.join("evaluation");
    // tpch slower (2.5 -> 2.6), sec faster by more (15.3 -> 13.9), ssb (kept) much slower.
    let mut steps = CannedSteps::new(&dir, &[("tpch", 2_545_797_717, 2_600_000_000, 12), ("sec", 15_343_889_487, 13_948_990_443, 18), ("ssb", 1_000_000_000, 9_000_000_000, 6)]);
    let mut statuses = MemberStatuses::start(&dir, &members()).unwrap();
    let combined = evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &dir, None).unwrap_or_else(|_| panic!("better in sum is accepted"));
    assert_eq!(steps.calls, ["verus:tpch", "verus:sec", "verus:anyschema", "verus:ssb", "storages:tpch", "storages:sec", "storages:anyschema", "storages:ssb", "answers:anyschema",
        "race:tpch", "race:sec", "race:ssb", "variants:tpch", "variants:sec", "variants:anyschema", "variants:ssb"]);
    assert_eq!((combined["better"].as_bool(), combined["workloads"].clone()), (Some(true), json!(["tpch", "sec"])), "the kept workload is not summed");
    assert_eq!((combined["parent"]["score"]["normalized_time"].as_str(), combined["candidate"]["score"]["normalized_time"].as_str()), (Some("17.889687204"), Some("16.548990443")));
    assert_eq!(read_json::<Value>(&dir.join(super::members::COMBINED_FILE)).unwrap(), combined);
    let by_name = statuses_of(&dir);
    assert_eq!(by_name["tpch"].0, "timed");
    assert_eq!(by_name["sec"].0, "timed");
    assert_eq!(by_name["anyschema"].0, "checked");
    assert_eq!(by_name["ssb"].0, "timed");
    let parts = json!({"members":statuses.statuses(),"combined":combined});
    assert_eq!(fixture_shape_errors(&parts, &members_fixture(&root)["evaluation"]), Vec::<String>::new());
    let fixture = members_fixture(&root);
    assert_eq!(fixture_shape_errors(&json!(statuses.statuses()[2]), &fixture["evaluation"]["members"][2]), Vec::<String>::new(), "the check entry too");
    fs::remove_dir_all(&root).unwrap();
}

/// Worse in sum (faster on the primary, slower on another counted workload by more) is an attempt
/// with both races recorded and the combined decision `better: false`; no variant and no kept step runs (the kept
/// workload stays `not_run`).
#[test]
fn worse_in_sum_is_an_attempt_and_the_kept_workload_never_runs() {
    let root = scratch("members-worse-in-sum");
    let dir = root.join("evaluation");
    let mut steps = CannedSteps::new(&dir, &[("tpch", 2_545_797_717, 2_000_000_000, 12), ("sec", 15_343_889_487, 16_000_000_000, 18)]);
    let mut statuses = MemberStatuses::start(&dir, &members()).unwrap();
    match evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &dir, None) {
        Err(Failure::Candidate { reason, flagged: false, .. }) => {
            assert!(reason.starts_with(NOT_BETTER_REASON) && reason.contains("by the combined score over tpch, sec"), "{reason}");
            assert!(reason.contains("normalized time 17.889687204 vs 18.000000000"), "{reason}");
        }
        _ => panic!("worse in sum is an attempt"),
    }
    assert_eq!(steps.calls.last().map(String::as_str), Some("race:sec"), "nothing runs after the decision: {:?}", steps.calls);
    let by_name = statuses_of(&dir);
    assert_eq!((by_name["tpch"].0.as_str(), by_name["sec"].0.as_str(), by_name["anyschema"].0.as_str(), by_name["ssb"].0.as_str()), ("timed", "timed", "checked", "not_run"));
    assert_eq!(super::members::recorded_combined(&dir)["better"], false);
    fs::remove_dir_all(&root).unwrap();
}

/// A check workload's wrong answer refuses the submission, flagged, before any race (no timing runs);
/// its Verus failure refuses it too, before any storage, answer or race.
#[test]
fn a_check_workload_gates_before_any_race() {
    let root = scratch("members-check-gates");
    let wrong = root.join("wrong");
    let mut steps = CannedSteps::new(&wrong, &[]);
    steps.fail = Some(("answers", "anyschema", true));
    let mut statuses = MemberStatuses::start(&wrong, &members()).unwrap();
    match evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &wrong, None) {
        Err(Failure::Candidate { reason, flagged: true, .. }) => assert!(reason.starts_with("workload anyschema: refusal: canned answers failure"), "{reason}"),
        _ => panic!("a check workload's wrong answer refuses the submission, flagged"),
    }
    assert!(!steps.calls.iter().any(|c| c.starts_with("race:")), "no race runs: {:?}", steps.calls);
    assert_eq!(statuses_of(&wrong)["anyschema"], ("refused".to_string(), Some("answers".to_string())));
    assert!(!wrong.join(super::members::COMBINED_FILE).exists(), "no combined decision was reached");

    let verus = root.join("verus");
    let mut steps = CannedSteps::new(&verus, &[]);
    steps.fail = Some(("verus", "anyschema", false));
    let mut statuses = MemberStatuses::start(&verus, &members()).unwrap();
    match evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &verus, None) {
        Err(Failure::Candidate { reason, flagged: false, .. }) => assert!(reason.starts_with("workload anyschema: "), "{reason}"),
        _ => panic!("a check workload's Verus failure refuses the submission"),
    }
    assert_eq!(steps.calls, ["verus:tpch", "verus:sec", "verus:anyschema"], "nothing runs after the refusal (the kept crate's Verus neither)");
    let by_name = statuses_of(&verus);
    assert_eq!(by_name["anyschema"], ("refused".to_string(), Some("verus".to_string())));
    assert!(by_name.iter().filter(|(n, _)| *n != "anyschema").all(|(_, (s, _))| s == "not_run"));
    fs::remove_dir_all(&root).unwrap();
}

/// A kept workload never decides: its wrong answer after an accepting decision refuses the
/// submission (flagged) at its timing, while the counted workloads are recorded `timed` and the decision `better`.
#[test]
fn a_kept_workload_never_decides_but_its_wrong_answer_refuses() {
    let root = scratch("members-kept");
    let dir = root.join("evaluation");
    let mut steps = CannedSteps::new(&dir, &[("tpch", 2_000_000_000, 1_900_000_000, 12), ("sec", 15_000_000_000, 15_000_000_000, 18)]);
    steps.fail = Some(("race", "ssb", true));
    let mut statuses = MemberStatuses::start(&dir, &members()).unwrap();
    assert!(matches!(evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &dir, None), Err(Failure::Candidate { flagged: true, .. })));
    assert_eq!(super::members::recorded_combined(&dir)["better"], true, "the counted workloads decided before the kept one ran");
    assert_eq!(statuses_of(&dir)["ssb"], ("refused".to_string(), Some("timing".to_string())));
    // A framework failure (an admitted parent's incident) stays the framework's.
    let framework = root.join("framework");
    struct Incident(CannedSteps);
    impl MemberSteps for Incident {
        fn verus(&mut self, name: &str) -> Result<(), Failure> {
            self.0.verus(name)
        }
        fn storages(&mut self, name: &str) -> Result<(), Failure> {
            self.0.storages(name)
        }
        fn answers(&mut self, name: &str) -> Result<Value, Failure> {
            self.0.answers(name)
        }
        fn race(&mut self, name: &str) -> Result<RaceScores, Failure> {
            if name == "sec" { Err(Failure::Framework(AdmissionError::tool("incident: admitted parent v000 failed"))) } else { self.0.race(name) }
        }
        fn variants(&mut self, name: &str) -> Result<(), Failure> {
            self.0.variants(name)
        }
    }
    let mut statuses = MemberStatuses::start(&framework, &members()).unwrap();
    let outcome = evaluate_members(&members(), &mut Incident(CannedSteps::new(&framework, &[])), &mut statuses, &parent(), &framework, None);
    assert!(matches!(outcome, Err(Failure::Framework(ref e)) if e.message.starts_with("workload sec: incident")), "the framework's");
    assert_eq!(statuses_of(&framework)["sec"].0, "not_run", "a framework failure is no workload's refusal");
    fs::remove_dir_all(&root).unwrap();
}

// ------------------------------------------------------------------------------------------------ the one-engine rule

/// The one-engine rule of the order's tests: the submission one engine or not (own modules and inherited storages of
/// `tpch` and `sec`), the parent one engine or not.
fn one_engine_rule(candidate_one_engine: bool, parent_one_engine: bool) -> super::one_engine::OneEngineRule {
    let candidate = if candidate_one_engine {
        json!({"one_engine":true,"own_modules":[],"inherited_storages":[],"shared_digest":"5555"})
    } else {
        json!({"one_engine":false,"own_modules":["sec","tpch"],"inherited_storages":[{"workload":"tpch","storages":["narrowpack"]},{"workload":"sec","storages":["dictpack"]}],"shared_digest":"5555"})
    };
    super::one_engine::OneEngineRule { candidate, parent_one_engine }
}

/// With the rule set, a submission that is not one engine is refused before any build or timing: no step runs, each
/// workload that breaks the rule is refused at `one_engine` (the others stay `not_run`), and no combined decision is
/// written. The reason names the rule, every own module and every inherited storage.
#[test]
fn a_submission_that_is_not_one_engine_is_refused_before_any_build_or_timing() {
    let root = scratch("members-not-one-engine");
    let dir = root.join("evaluation");
    let mut steps = CannedSteps::new(&dir, &[("tpch", 2_000_000_000, 1_000_000_000, 12), ("sec", 15_000_000_000, 10_000_000_000, 18)]);
    let mut statuses = MemberStatuses::start(&dir, &members()).unwrap();
    match evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &dir, Some(&one_engine_rule(false, false))) {
        Err(Failure::Candidate { reason, flagged: false, score: None }) => {
            assert!(reason.starts_with("refusal: not_one_engine: ") && reason.contains("engine.workloads.require_one_engine"), "{reason}");
            assert!(reason.contains("workloads/sec/, workloads/tpch/") && reason.contains("tpch (narrowpack), sec (dictpack)"), "{reason}");
        }
        _ => panic!("a submission that is not one engine is refused, even when it is faster"),
    }
    assert!(steps.calls.is_empty(), "nothing was built or timed: {:?}", steps.calls);
    let by_name = statuses_of(&dir);
    assert_eq!((by_name["tpch"].clone(), by_name["sec"].clone()), (("refused".to_string(), Some("one_engine".to_string())), ("refused".to_string(), Some("one_engine".to_string()))));
    assert_eq!((by_name["anyschema"].0.as_str(), by_name["ssb"].0.as_str()), ("not_run", "not_run"));
    assert!(!dir.join(super::members::COMBINED_FILE).exists());
    fs::remove_dir_all(&root).unwrap();
}

/// With the rule set and a parent that is not one engine, the first one-engine submission is accepted although its
/// combined score is worse, when every counted cell finished: the combined decision says `better: false` and records
/// `one_engine_transition` with every counted race; the kept race and every workload's variants still run. With a
/// counted cell unfinished it is an attempt that says why the transition did not apply.
#[test]
fn the_first_one_engine_version_is_accepted_although_slower_when_every_counted_cell_finished() {
    let root = scratch("members-one-engine-transition");
    let dir = root.join("evaluation");
    let races = [("tpch", 2_000_000_000, 2_500_000_000, 12), ("sec", 3_000_000_000, 9_000_000_000, 18), ("ssb", 1_000_000_000, 1_000_000_000, 6)];
    let mut steps = CannedSteps::new(&dir, &races);
    let mut statuses = MemberStatuses::start(&dir, &members()).unwrap();
    let combined = evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &dir, Some(&one_engine_rule(true, false))).unwrap_or_else(|_| panic!("the first one-engine version is accepted"));
    assert_eq!(combined["better"], false, "its combined score is worse: {combined}");
    let transition = &combined[super::one_engine::ONE_ENGINE_TRANSITION];
    assert_eq!((transition["parent"].as_str(), transition["counted_cells"].as_array().map(Vec::len)), (Some("v000"), Some(2)), "{transition}");
    assert_eq!(read_json::<Value>(&dir.join(super::members::COMBINED_FILE)).unwrap(), combined);
    assert_eq!(super::one_engine::CombinedVerdict::of_record(&combined), Some(super::one_engine::CombinedVerdict::OneEngineTransition), "the main line adopts it as the head");
    assert_eq!(steps.calls[steps.calls.len() - 5..], ["race:ssb", "variants:tpch", "variants:sec", "variants:anyschema", "variants:ssb"], "the kept race and the variants still run");
    assert_eq!(statuses_of(&dir)["ssb"].0, "timed");

    let unfinished = root.join("unfinished");
    let mut steps = CannedSteps::new(&unfinished, &races);
    steps.unfinished.insert("tpch", 1);
    let mut statuses = MemberStatuses::start(&unfinished, &members()).unwrap();
    match evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &unfinished, Some(&one_engine_rule(true, false))) {
        Err(Failure::Candidate { reason, flagged: false, .. }) => {
            assert!(reason.starts_with(NOT_BETTER_REASON) && reason.contains("one_engine_transition not applied") && reason.contains("tpch finished 11 of 12 cells"), "{reason}");
        }
        _ => panic!("a one-engine version with an unfinished counted cell is not accepted by the transition"),
    }
    assert!(super::members::recorded_combined(&unfinished).get(super::one_engine::ONE_ENGINE_TRANSITION).is_none());
    assert_eq!(statuses_of(&unfinished)["ssb"].0, "not_run");
    fs::remove_dir_all(&root).unwrap();
}

/// After the transition (the parent is one engine) the combined score decides as without the rule: worse in sum is an
/// attempt, better is accepted with no transition record; and a submission that is not one engine is still refused.
#[test]
fn after_the_transition_the_combined_score_decides() {
    let root = scratch("members-one-engine-after");
    let worse = root.join("worse");
    let mut steps = CannedSteps::new(&worse, &[("tpch", 2_000_000_000, 2_500_000_000, 12), ("sec", 3_000_000_000, 9_000_000_000, 18)]);
    let mut statuses = MemberStatuses::start(&worse, &members()).unwrap();
    match evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &worse, Some(&one_engine_rule(true, true))) {
        Err(Failure::Candidate { reason, .. }) => assert!(reason.starts_with(NOT_BETTER_REASON) && !reason.contains("one_engine_transition"), "{reason}"),
        _ => panic!("worse in sum is an attempt once the head is one engine"),
    }
    let better = root.join("better");
    let mut steps = CannedSteps::new(&better, &[("tpch", 2_000_000_000, 1_900_000_000, 12), ("sec", 3_000_000_000, 3_000_000_000, 18)]);
    let mut statuses = MemberStatuses::start(&better, &members()).unwrap();
    let combined = evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &better, Some(&one_engine_rule(true, true))).unwrap_or_else(|_| panic!("better in sum is accepted"));
    assert_eq!((combined["better"].as_bool(), combined.get(super::one_engine::ONE_ENGINE_TRANSITION)), (Some(true), None));
    let refused = root.join("refused");
    let mut steps = CannedSteps::new(&refused, &[]);
    let mut statuses = MemberStatuses::start(&refused, &members()).unwrap();
    assert!(matches!(evaluate_members(&members(), &mut steps, &mut statuses, &parent(), &refused, Some(&one_engine_rule(false, true))), Err(Failure::Candidate { .. })) && steps.calls.is_empty());
    fs::remove_dir_all(&root).unwrap();
}

// ------------------------------------------------------------------------------------------------ a run of several workloads: the root

/// A tree node of a seed run's version.
fn seed_node(id: &str, parents: &[&str]) -> Value {
    json!(TreeNode { format_version: 1, id: id.into(), accepted: true, kind: if parents.is_empty() { NodeKind::FrameworkGenerated } else { NodeKind::Branch }, branch: "b1".into(),
        parents: parents.iter().map(|p| p.to_string()).collect(), scale: "sf1".into(), score: None, reason: None, session: None, iteration: None, direction: None, rationale: None,
        created_unix_ms: 1 })
}

/// Two seed runs descending from one ancestor (`<root>/ancestor` v016): `seed-a` v004 (one workload) and `seed-b` v001 (a version of
/// several workloads with `sec`), each with its code, notebook and storage author files.
fn member_seed_runs(root: &Path) -> (SeedVersion, SeedVersion, SeedVersion) {
    let ancestor = SeedVersion { run: root.join("ancestor"), version: "v016".into() };
    let ancestor_dir = ancestor.directory();
    write_value(&ancestor_dir.join("node.json"), &seed_node("v016", &[]));
    write(&ancestor_dir.join("code/agent/mod.rs"), "//! The common ancestor.\n");
    for (run, version) in [("seed-a", "v004"), ("seed-b", "v001")] {
        let dir = root.join(run).join("engine/versions");
        write_value(&dir.join("v000/node.json"), &seed_node("v000", &[]));
        write_value(&dir.join("v000/version.json"), &json!({"origin":{"seed":{"run":ancestor.run,"version":"v016"}}}));
        write_value(&dir.join(version).join("node.json"), &seed_node(version, &["v000"]));
        write(&dir.join(version).join("code/agent/mod.rs"), &format!("//! {run} {version}.\n"));
        write(&dir.join(version).join("NOTES.md"), &format!("# Notes of {run}\n"));
        write(&dir.join(version).join("code/storages/pack/crate/src/builder/mod.rs"), "//! A packed storage's builder.\n");
    }
    (SeedVersion { run: root.join("seed-a"), version: "v004".into() }, SeedVersion { run: root.join("seed-b"), version: "v001".into() }, ancestor)
}

/// The plan of a run of several workloads' root: `tpch` (counted, the primary, seeded from seed-a v004), `sec` (counted,
/// seeded from seed-b v001's `sec`), `anyschema` (check, no seed: the primary seed out of the box, else version 0).
fn members_plan<'a>(engine_dir: &'a Path, seed_a: &SeedVersion, seed_b: &SeedVersion, branches: &'a [String]) -> RootPlan<'a> {
    let primary_seed = Seed::Run { version: seed_a.clone(), workload: None };
    let facts = |name: &str, member: MemberRole, seed: Option<Seed>, scale: &str| SideFacts { name: name.into(), role: if name == "tpch" { WorkloadRole::Goal } else { WorkloadRole::Kept }, member,
        primary: name == "tpch", seed, scale: scale.into(), library: PathBuf::from(format!("/libraries/{name}")), budget_bytes: 5_439_582_957, plain_storage_bytes: 7_746_659_210 };
    RootPlan { engine_dir, form: WorkloadForm::Workloads, seed: Some(primary_seed.clone()), workloads: vec![
        facts("tpch", MemberRole::Counted, Some(primary_seed), "sf100"),
        facts("sec", MemberRole::Counted, Some(Seed::Run { version: seed_b.clone(), workload: Some("sec".into()) }), "sf3"),
        facts("anyschema", MemberRole::Check, None, "tiny"),
    ], branches }
}

/// The root of a run of several workloads has one side per workload: an explicit seed per member
/// (tpch from a continued run's v004, sec from a stage run's v001's sec), and for the member without one the primary seed's code out of the box,
/// which did not assemble, then version 0 (the check workload answered, not timed); every side admitted once in its
/// library as its first version, selected and on the main line (`workload_seed`). The folder: the primary's code,
/// notebook and a seed manifest with every workload's uses; every side's records with its origin (`SIDE.md`,
/// `OUT_OF_THE_BOX.md`, the check's answers); the other sides' code, notebook, manifest and storage author files under
/// `root-sides/<name>/`; the seeds' common ancestor's code under `root-sides/ancestor/`; `version.json` in the
/// workloads fixture's shape (`version_root`) with the combined score of the counted workloads and the one-engine record.
#[test]
fn the_root_has_one_side_per_workload_with_seeds_out_of_the_box_and_version_zero() {
    let root = scratch("members-root");
    let engine_dir = root.join("run/engine");
    let (seed_a, seed_b, ancestor) = member_seed_runs(&root);
    let branches = ["b1".to_string()];
    let mut work = CannedRoot::new(&[]);
    work.check = vec!["anyschema".into()];
    let record = seed_root(&mut work, &members_plan(&engine_dir, &seed_a, &seed_b, &branches)).unwrap();
    assert_eq!(record["status"], "admitted", "{record:#}");
    assert_eq!(work.evaluated, [("tpch".to_string(), SideSource::Seed), ("sec".to_string(), SideSource::Seed), ("anyschema".to_string(), SideSource::VersionZero)]);
    assert_eq!(work.tried, ["anyschema"], "only the member without a seed is tried out of the box");
    assert_eq!((work.admissions["tpch"], work.admissions["sec"], work.admissions["anyschema"], work.selections), (1, 1, 1, 1));
    let v0 = engine_dir.join("versions/v000");
    let node: TreeNode = read_json(&v0.join("node.json")).unwrap();
    assert_eq!((node.kind, node.scale.as_str(), node.score.as_ref().map(|s| s.score.finished)), (NodeKind::WorkloadSeed, "sf100", Some(12)));
    assert_eq!(fs::read_to_string(v0.join("code/agent/mod.rs")).unwrap(), "//! The side of tpch.\n", "the first session continues from the primary side's code");
    assert!(v0.join("code/workloads/tpch/mod.rs").is_file(), "the primary's own module");
    assert_eq!(fs::read_to_string(v0.join("NOTES.md")).unwrap(), "# Notes of seed-a\n");
    let manifest: EngineManifest = read_json(&v0.join("seed-manifest.json")).unwrap();
    assert_eq!(manifest.workloads.iter().map(|w| (w.name.as_str(), w.storage_uses[0].name.as_str())).collect::<Vec<_>>(), [("tpch", "tpch_flat"), ("sec", "sec_flat"), ("anyschema", "anyschema_flat")]);
    for file in ["workloads/tpch/SIDE.md", "workloads/sec/SIDE.md", "workloads/anyschema/SIDE.md", "workloads/anyschema/OUT_OF_THE_BOX.md", "workloads/anyschema/check.json",
        "workloads/sec/score.json", "workloads/sec/cells/sf3.json", "workloads/sec/admission.json", "workloads/tpch/workload.json", "score.json", "cells/sf100.json", "admission.json",
        "root-sides/sec/code/agent/mod.rs", "root-sides/sec/code/workloads/sec/mod.rs", "root-sides/sec/manifest.json", "root-sides/sec/NOTES.md",
        "root-sides/sec/storages/pack/crate/src/builder/mod.rs", "root-sides/anyschema/code/agent/mod.rs", "root-sides/ancestor/code/agent/mod.rs", "root-sides/ancestor/ANCESTOR.md"] {
        assert!(v0.join(file).is_file(), "{file}");
    }
    assert!(!v0.join("root-sides/tpch").exists(), "the primary's side is the workspace's code");
    assert_eq!(fs::read_to_string(v0.join("code/instances/tpch/colpack/storage.json")).unwrap(), "{\"workload\":\"tpch\"}", "the primary's frozen instances, kept per workload");
    let version: Value = read_json(&v0.join("version.json")).unwrap();
    let fixture = members_fixture(&root);
    for (key, expected) in [("workloads", &fixture["version_root"]["workloads"]), ("combined_score", &fixture["version_root"]["combined_score"]), ("general", &fixture["version_root"]["general"])] {
        assert_eq!(fixture_shape_errors(&version[key], expected), Vec::<String>::new(), "{key}");
    }
    for name in ["sec", "anyschema"] {
        assert_eq!(fixture_shape_errors(&version["workloads"][name], &fixture["version_root"]["workloads"][name]), Vec::<String>::new(), "{name}");
    }
    assert_eq!((version["workloads"]["tpch"]["origin"]["kind"].as_str(), version["workloads"]["sec"]["origin"]["seed"]["workload"].as_str()), (Some("seed"), Some("sec")));
    assert_eq!(version["workloads"]["anyschema"]["origin"]["kind"], "version_0");
    assert_eq!(version["workloads"]["anyschema"]["origin"]["out_of_the_box"]["status"], "not_assembled");
    assert_eq!((version["workloads"]["anyschema"]["score"].clone(), version["workloads"]["anyschema"]["check"]["calls"].as_u64()), (Value::Null, Some(12)));
    assert_eq!(version["workloads"]["anyschema"]["storage"]["budget_bytes"], Value::Null, "a check workload is exempt");
    assert_eq!((version["combined_score"]["score"]["finished"].as_u64(), version["combined_score"]["workloads"].clone()), (Some(30), json!(["tpch", "sec"])));
    assert_eq!((version["general"]["one_engine"].as_bool(), version["general"]["own_modules"].clone()), (Some(false), json!(["sec", "tpch"])));
    assert_eq!(version["origin"]["ancestor"]["version"], "v016");
    assert_eq!(version["origin"]["ancestor"]["run"], json!(ancestor.run));
    let tree = VersionTree::read(&engine_dir).unwrap();
    assert_eq!((tree.main_line_head(), tree.main_line[0].reason.as_str()), (Some("v000"), "workload_seed"));
    assert!(tree.is_run_of_several_workloads());
    assert_eq!(tree.combined_score("v000").map(|c| (c.score.finished, c.workloads)), Some((30, vec!["tpch".to_string(), "sec".to_string()])));
    let markdown = tree.markdown(&branches);
    assert!(markdown.contains("| Combined (counted workloads) | Other workloads |") && markdown.contains("anyschema checked (check)"), "{markdown}");
    // The search index offers the other sides' and the ancestor's code (read-only, marked root-side).
    let workspace = root.join("workspace");
    fs::create_dir_all(&workspace).unwrap();
    let store = gendb_artifacts::ObjectStore::open(root.join("index-library")).unwrap();
    let index = crate::prompts::brief::search_index::write_engine_search_index(&store, &[], &crate::prompts::brief::search_index::EngineRecords { engine_dir: &engine_dir }, &workspace,
        &Default::default()).unwrap();
    let index: Value = read_json(&index).unwrap();
    let sides: Vec<(&str, &str)> = index["entries"].as_array().unwrap().iter().filter(|e| e["origin"]["status"] != "accepted version")
        .map(|e| (e["origin"]["status"].as_str().unwrap(), e["path"].as_str().unwrap())).collect();
    assert!(sides.contains(&("root side", "agent/mod.rs")) && sides.contains(&("seeds' common ancestor", "agent/mod.rs")), "{sides:?}");
    assert!(fs::read_to_string(workspace.join("search-index.txt")).unwrap().contains("root-side engine_module module"));
    // Idempotent: a second preparation finds the root.
    assert_eq!(seed_root(&mut work, &members_plan(&engine_dir, &seed_a, &seed_b, &branches)).unwrap()["status"], "present");
    assert_eq!((work.admissions["tpch"], work.admissions["sec"], work.admissions["anyschema"], work.selections), (1, 1, 1, 1));
    fs::remove_dir_all(&root).unwrap();
}

/// A member without a seed whose primary seed's code is admissible out of the box gets that side
/// (no version 0), recorded as `out_of_the_box`; and a preparation stopped after one library's admission resumes
/// without evaluating or admitting any side twice.
#[test]
fn an_admissible_out_of_the_box_side_and_a_resumed_root_admit_once_per_library() {
    let root = scratch("members-root-resume");
    let engine_dir = root.join("run/engine");
    let (seed_a, seed_b, _) = member_seed_runs(&root);
    let branches = ["b1".to_string()];
    let mut work = CannedRoot::new(&["anyschema"]);
    work.check = vec!["anyschema".into()];
    work.crash_after_admitting = Some("sec".into());
    assert!(seed_root(&mut work, &members_plan(&engine_dir, &seed_a, &seed_b, &branches)).is_err(), "the stop after sec's admission");
    assert!(engine_dir.join("seed/sec/admitting.json").is_file() && !engine_dir.join("versions/v000").exists());
    seed_root(&mut work, &members_plan(&engine_dir, &seed_a, &seed_b, &branches)).unwrap();
    assert_eq!(work.evaluated.iter().map(|(w, _)| w.as_str()).collect::<Vec<_>>(), ["tpch", "sec"], "no side is evaluated twice; anyschema's side is out of the box");
    assert_eq!(work.tried, ["anyschema"]);
    assert_eq!((work.admissions["tpch"], work.admissions["sec"], work.admissions["anyschema"]), (1, 1, 1), "every library holds its root once");
    let version: Value = read_json(&engine_dir.join("versions/v000/version.json")).unwrap();
    assert_eq!(version["workloads"]["anyschema"]["origin"]["kind"], "out_of_the_box");
    assert_eq!(version["workloads"]["anyschema"]["origin"]["out_of_the_box"]["status"], "verified");
    let side = fs::read_to_string(engine_dir.join("versions/v000/workloads/anyschema/SIDE.md")).unwrap();
    assert!(side.contains("the primary seed's code, admissible here out of the box") && side.contains("12 of 12 calls agreed"), "{side}");
    fs::remove_dir_all(&root).unwrap();
}

/// A session's workspace of a run of several workloads gets the version's modules (own and default),
/// families and plans writable, the manifest's family sources at their workspace paths, and the root's other sides
/// read-only under `root-sides/`.
#[test]
fn a_session_workspace_gets_families_plans_and_read_only_root_sides() {
    use std::os::unix::fs::PermissionsExt;
    let root = scratch("members-workspace");
    let engine_dir = root.join("run/engine");
    let v0 = engine_dir.join("versions/v000");
    write(&v0.join("node.json"), "{\"accepted\":true}");
    for file in ["code/agent/mod.rs", "code/workloads/default/mod.rs", "code/workloads/tpch/mod.rs", "code/families/colpack/verus-family.json", "code/families/colpack/default_plan.rs",
        "code/plans/tpch/colpack.rs", "root-sides/sec/code/agent/mod.rs", "root-sides/ancestor/code/agent/mod.rs"] {
        write(&v0.join(file), &format!("// {file}\n"));
        fs::set_permissions(v0.join(file), fs::Permissions::from_mode(0o444)).unwrap();
    }
    let manifest = EngineManifest { families: vec![crate::engine::submission::FamilyDeclaration { name: "colpack".into(), source: "families/colpack/verus-family.json".into() }],
        ..EngineManifest::example(&[]) };
    let workspace = root.join("workspace");
    write_value(&workspace.join("verus-engine.json"), &json!(manifest));
    let mut record = json!({});
    seed_stage_workspace(&workspace, &engine_dir, "v000", WorkloadForm::Workloads, &mut record).unwrap();
    let mode = |path: &Path| fs::metadata(path).unwrap().permissions().mode() & 0o777;
    for writable in ["engine/workloads/default/mod.rs", "engine/workloads/tpch/mod.rs", "storages/colpack/verus-family.json", "engine/plans/tpch/colpack.rs"] {
        assert_ne!(mode(&workspace.join(writable)) & 0o200, 0, "{writable}: the author can write it");
    }
    for read_only in ["root-sides/sec/code/agent/mod.rs", "root-sides/ancestor/code/agent/mod.rs"] {
        assert_eq!(mode(&workspace.join(read_only)) & 0o222, 0, "{read_only}: read-only");
    }
    let seeded: EngineManifest = read_json(&workspace.join("verus-engine.json")).unwrap();
    assert_eq!(seeded.families[0].source, PathBuf::from("storages/colpack/verus-family.json"));
    assert_eq!((record["stage"]["root_sides"].as_str().map(PathBuf::from), record["stage"]["families"].is_string()), (Some(workspace.join("root-sides")), true));
    // Seeded again (a stop interrupted it): the same files, nothing refused.
    seed_stage_workspace(&workspace, &engine_dir, "v000", WorkloadForm::Workloads, &mut record).unwrap();
    fs::remove_dir_all(&root).unwrap();
}

// ------------------------------------------------------------------------------------------------ a run of several workloads: a version and the view

/// The crate record of a workload of the workloads fixture (`general`).
fn fixture_member(general: &Value, digest: &str) -> MemberRecord {
    let names = |key: &str| general[key].as_array().unwrap().iter().map(|n| n.as_str().unwrap().to_string()).collect::<Vec<_>>();
    let own = general["own_module_lines"].as_u64().unwrap();
    MemberRecord { module: if own > 0 { MemberModule::Own } else { MemberModule::Default }, families: vec![], family_storages: names("family_storages"), plain_storages: vec![],
        inherited_storages: names("inherited_storages"), own_module_lines: own, plan_lines: general["plan_lines"].as_u64().unwrap(), shared_sources_digest: digest.into() }
}

/// The baselines of a workload of the fixture (its training facts' saved cells), as `targets.json` reads them.
fn fixture_baselines(training: &Value) -> super::super::totals::Baselines {
    let mut targets = serde_json::Map::new();
    for t in training["templates"].as_array().unwrap() {
        let mut bindings = serde_json::Map::new();
        for b in t["baselines"].as_array().unwrap() {
            let ms = |ns: &Value| ns.as_u64().map(|ns| json!(ns as f64 / 1e6));
            bindings.entry(b["binding"].as_str().unwrap().to_string()).or_insert_with(|| json!({}))[b["workers"].to_string()] =
                json!({"duckdb_ms":ms(&b["duckdb_ns"]),"umbra_ms":ms(&b["umbra_ns"]),"target_ms":ms(&b["umbra_ns"]),"agreement":b["agreement"]});
        }
        targets.insert(t["name"].as_str().unwrap().to_string(), Value::Object(bindings));
    }
    super::super::totals::Baselines::from_targets_json(&Value::Object(targets).to_string()).unwrap()
}

/// An accepted version of a run of several workloads records every workload's entry (the primary's
/// timing at the folder's top, the other counted workload's race and the check workload's answers under
/// `workloads/<name>/`), the combined score and the one-engine record in the fixture's shape (`version`); the tree and
/// its findings show them; and the workloads view over these records (each workload's head, side origin, cells, score,
/// totals against the targets, budget, serving bytes, own code, last race or last check) and the combined score have
/// the fixture's keys (`context.workloads`, `context.combined_score`).
#[test]
fn a_version_of_several_workloads_and_the_workloads_view_match_the_interface() {
    let root = scratch("members-version");
    let engine_dir = root.join("run/engine");
    let fixture = members_fixture(&root.join("run"));
    // The root, as the preparation seeds it.
    let (seed_a, seed_b, _) = member_seed_runs(&root);
    let branches = ["b1".to_string()];
    let mut work = CannedRoot::new(&[]);
    work.check = vec!["anyschema".into()];
    seed_root(&mut work, &members_plan(&engine_dir, &seed_a, &seed_b, &branches)).unwrap();
    // v001: its evaluation's records and its folder.
    let evaluation = root.join("session/iterations/0001/frozen/evaluation-0");
    let fx = &fixture["context"]["workloads"];
    let cells = |w: &Value| serde_json::from_value::<Vec<super::super::score::CellResult>>(w["cells"].clone()).unwrap();
    let score = |w: &Value| serde_json::from_value::<RecordedScore>(w["score"].clone()).unwrap();
    let (tpch, sec, anyschema) = (&fx[0], &fx[1], &fx[2]);
    write_value(&evaluation.join("race.json"), &json!({"parent":"v000"}));
    write_value(&evaluation.join("workloads/sec/race.json"), &json!({"parent":"v000","pairs":[],"parent_score":{"score":{"finished":18,"normalized_time":"15.343889487"}},
        "candidate_score":{"score":{"finished":18,"normalized_time":"13.948990443"}}}));
    write_value(&evaluation.join("workloads/anyschema/check.json"), &json!({"calls":12,"agreed":12}));
    let target = engine_dir.join("versions/v001");
    let staging = engine_dir.join("versions/.staging-v001");
    let (tpch_cells, sec_cells) = (cells(tpch), cells(sec));
    write_value(&staging.join("cells/sf100.json"), &json!(tpch_cells));
    let (tpch_score, sec_score) = (score(tpch), score(sec));
    let build = json!({"verification":{"errors":0,"verified":5790},"wall_ns":268_000_000_000u64});
    let admission = |package: u8| json!({"library_version":2,"package":ContentId::from_bytes([package; 32]),"uses":[{"name":"x","package":ContentId::from_bytes([package; 32])}]});
    let (tpch_admission, sec_admission, any_admission) = (admission(1), admission(2), admission(3));
    let storage = |w: &Value| StorageFacts { serving_bytes: w["serving_bytes"].as_u64(), budget_bytes: w["budget"]["budget_bytes"].as_u64().unwrap_or(0),
        plain_storage_bytes: w["budget"]["plain_storage_bytes"].as_u64().unwrap(), decision: json!("changed storage within the original data size") };
    let members: Vec<MemberRecord> = [tpch, sec, anyschema].iter().map(|w| fixture_member(&w["general"], "5555")).collect();
    let (tpch_race, sec_race) = (target.join("race.json"), evaluation.join("workloads/sec/race.json"));
    let check = json!({"calls":12,"agreed":12,"file":evaluation.join("workloads/anyschema/check.json")});
    let library = |w: &Value| PathBuf::from(w["library"].as_str().unwrap());
    let (tpch_library, sec_library, any_library) = (library(tpch), library(sec), library(anyschema));
    let parts = [
        MemberPart { name: "tpch", role: MemberRole::Counted, primary: true, scale: "sf100", timing: Some(MemberTiming { cells: &tpch_cells, score: &tpch_score, timing: &tpch_race, raced: true, parent: Some("v000") }),
            check: None, copies: vec![], admission: &tpch_admission, library: &tpch_library, storage: storage(tpch), build: &build, member: Some(&members[0]), origin: Value::Null },
        MemberPart { name: "sec", role: MemberRole::Counted, primary: false, scale: "sf3", timing: Some(MemberTiming { cells: &sec_cells, score: &sec_score, timing: &sec_race, raced: true, parent: Some("v000") }),
            check: None, copies: vec![], admission: &sec_admission, library: &sec_library, storage: storage(sec), build: &build, member: Some(&members[1]), origin: Value::Null },
        MemberPart { name: "anyschema", role: MemberRole::Check, primary: false, scale: "tiny", timing: None, check: Some(&check), copies: vec![], admission: &any_admission,
            library: &any_library, storage: storage(anyschema), build: &build, member: Some(&members[2]), origin: Value::Null },
    ];
    let mut workloads = serde_json::Map::new();
    for part in &parts {
        workloads.insert(part.name.to_string(), write_member(&staging, &target, "v001", part).unwrap());
    }
    let order = ["tpch".to_string(), "sec".to_string(), "anyschema".to_string()];
    let combined = combined_record(&workloads, &order);
    let general = general_record(&[("tpch", Some(&members[0])), ("sec", Some(&members[1])), ("anyschema", Some(&members[2]))], true);
    for (key, value) in [("workloads", Value::Object(workloads.clone())), ("combined_score", combined.clone()), ("general", general.clone())] {
        assert_eq!(fixture_shape_errors(&value, &fixture["version"][key]), Vec::<String>::new(), "{key}");
    }
    for name in ["sec", "anyschema"] {
        assert_eq!(fixture_shape_errors(&workloads[name], &fixture["version"]["workloads"][name]), Vec::<String>::new(), "{name}");
    }
    assert_eq!((combined["score"]["finished"].as_u64(), combined["score"]["normalized_time"].as_str(), combined["cells"].as_u64()), (Some(30), Some("16.263352004"), Some(30)));
    assert_eq!(general, json!({"one_engine":false,"own_modules":["sec","tpch"],"inherited_storages":fixture["version"]["general"]["inherited_storages"],"shared_digest":"5555"}));
    assert_eq!(workloads["anyschema"]["times"]["tiny"]["check"], json!(target.join("workloads/anyschema/check.json")));
    assert_eq!(workloads["sec"]["times"]["sf3"]["race"], json!(target.join("workloads/sec/race.json")));
    let node = TreeNode { format_version: 1, id: "v001".into(), accepted: true, kind: NodeKind::Branch, branch: "b1".into(), parents: vec!["v000".into()], scale: "sf100".into(),
        score: Some(RecordedScore { record: tpch_race.clone(), ..tpch_score.clone() }), reason: None, session: None, iteration: Some(1), direction: Some("one engine".into()), rationale: None, created_unix_ms: 2 };
    write_value(&staging.join("version.json"), &json!({"version":"v001","workloads":Value::Object(workloads),"combined_score":combined,"general":general}));
    write_value(&staging.join("node.json"), &json!(node));
    fs::rename(&staging, &target).unwrap();
    for file in ["workloads/sec/race.json", "workloads/sec/cells/sf3.json", "workloads/sec/admission.json", "workloads/anyschema/check.json", "workloads/anyschema/workload.json",
        "workloads/tpch/workload.json"] {
        assert!(target.join(file).is_file(), "{file}");
    }
    write_node(&engine_dir, &node).unwrap();
    append_main_line(&engine_dir, &MainLineChange { version: "v001".into(), previous: Some("v000".into()), reason: "race".into(), scale: "sf100".into(), race: None, adopted: None,
        selection: ContentId::from_bytes([8; 32]), at_unix_ms: 2 }).unwrap();
    let tree = VersionTree::read(&engine_dir).unwrap();
    assert_eq!(tree.combined_score("v001").map(|c| (c.score.finished, c.score.normalized_time.to_string())), Some((30, "16.263352004".to_string())));
    assert!(tree.markdown(&branches).contains("| F 30/30, G 16.263352004 | anyschema checked (check); sec sf3 18/18 finished, G 13.948990443 (counted) |"), "{}", tree.markdown(&branches));
    let findings = findings_markdown(&[json!({"node":"v001","branch":"b1","parent":"v000","accepted":true,"change":"merged",
        "combined":fixture["evaluation"]["combined"],"workloads":{"sec":{"role":"counted","scale":"sf3","effect":{"parent_finished":18,"finished":18,"parent_normalized_time":"15.343889487",
        "normalized_time":"13.948990443","cells_faster":18,"cells_slower":0}},"anyschema":{"role":"check","scale":"tiny","effect":null,"check":{"calls":12,"agreed":12}}}}),
        json!({"node":"b1-a001","branch":"b1","parent":"v001","accepted":false,"reason":"workload anyschema: refusal","change":"c",
            "members":[{"name":"anyschema","role":"check","status":"refused","step":"answers","reason":"workload anyschema: refusal: a wrong answer"}]})]);
    assert!(findings.contains("- Combined over tpch, sec: F 30 -> 30, G 17.889687204 -> 16.263352004 (better)"), "{findings}");
    assert!(findings.contains("- Counted sec at sf3 (in the combined score): F 18 -> 18") && findings.contains("- Check anyschema at tiny: 12 of 12 answers agreed"), "{findings}");
    assert!(findings.contains("- Workload anyschema (check) refused it at answers: workload anyschema: refusal: a wrong answer"), "{findings}");
    // The workloads view (the workloads fixture's shape) over these records.
    let view_member = |w: &Value, role: MemberRole, primary: bool| ViewMember {
        base: ViewWorkload { name: w["name"].as_str().unwrap().into(), role: if primary { WorkloadRole::Goal } else { WorkloadRole::Kept }, scale: w["scale"].as_str().unwrap().into(),
            first_scale: w["first_scale"].as_str().unwrap().into(), library: PathBuf::from(w["library"].as_str().unwrap()), training: w["training"].clone(),
            budget_bytes: w["budget"]["budget_bytes"].as_u64().unwrap_or(0), plain_storage_bytes: w["budget"]["plain_storage_bytes"].as_u64().unwrap(),
            plain_storages: [ContentId::from_bytes([9; 32])].into(), original_data_record: PathBuf::from(w["budget"]["original_data_record"].as_str().unwrap_or("/record.json")) },
        role,
        primary,
        baselines: if role == MemberRole::Check { Default::default() } else { fixture_baselines(&w["training"]) },
        timing_binding: "v0".into(),
        workers: vec![1, 32, 64],
        call_limit_ns: 60_000_000_000,
    };
    let (view, combined_view) = workloads_view(&engine_dir, &[view_member(tpch, MemberRole::Counted, true), view_member(sec, MemberRole::Counted, false), view_member(anyschema, MemberRole::Check, false)]);
    assert_eq!(fixture_shape_errors(&view, &fixture["context"]["workloads"]), Vec::<String>::new());
    for index in 0..3 {
        assert_eq!(fixture_shape_errors(&view[index], &fixture["context"]["workloads"][index]), Vec::<String>::new(), "entry {index}");
    }
    assert_eq!(fixture_shape_errors(&combined_view, &fixture["context"]["combined_score"]), Vec::<String>::new());
    assert_eq!((combined_view["head"].as_str(), combined_view["score"]["normalized_time"].as_str()), (Some("v001"), Some("16.263352004")));
    assert_eq!((view[0]["head"].as_str(), view[0]["primary"].as_bool(), view[0]["general"]["own_module_lines"].as_u64()), (Some("v001"), Some(true), Some(1657)));
    assert_eq!(view[0]["totals_ms"], tpch["totals_ms"], "the head's totals as the score counts them");
    assert_eq!(view[0]["targets_ms"], tpch["targets_ms"], "the faster baseline's totals");
    assert_eq!(view[1]["last_race"], json!({"version":"v001","parent":"v000","record":target.join("workloads/sec/race.json")}));
    assert_eq!(view[2]["last_check"], json!({"version":"v001","calls":12,"agreed":12,"record":target.join("workloads/anyschema/check.json")}));
    assert_eq!((view[2]["cells"].clone(), view[2]["score"].clone(), view[2]["budget"]["rule"].as_str()), (Value::Null, Value::Null, Some("exempt")));
    assert_eq!(view[1]["side_origin"]["seed"]["workload"], "sec", "the root's record of the side");
    assert_eq!(view[2]["side_origin"]["kind"], "version_0");
    fs::remove_dir_all(&root).unwrap();
}

// ------------------------------------------------------------------------------------------------ export

/// A version of a run of several workloads is exported (shared engine, default module, families,
/// plans, the engine's manifest without storage uses, README and record; no own module), refused into an existing
/// folder, and a side's workspace is written from the export (`seed: {source}`) for the exporting run's workload (its
/// plans) and for a new one (none), with one family use per family; no Verus.
#[test]
fn an_exported_version_round_trips_into_a_source_root() {
    let root = scratch("members-export");
    let run = root.join("run");
    let engine_dir = run.join("engine");
    let v1 = engine_dir.join("versions/v001");
    for file in ["code/agent/mod.rs", "code/agent/plan.rs", "code/workloads/default/mod.rs", "code/workloads/tpch/mod.rs", "code/families/colpack/verus-family.json",
        "code/families/colpack/default_plan.rs", "code/families/colpack/crate/src/builder/mod.rs", "code/plans/tpch/colpack.rs", "NOTES.md"] {
        write(&v1.join(file), &format!("// {file}\n"));
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(v1.join(file), fs::Permissions::from_mode(0o444)).unwrap();
    }
    let manifest = EngineManifest {
        families: vec![crate::engine::submission::FamilyDeclaration { name: "colpack".into(), source: "families/colpack/verus-family.json".into() }],
        default_modules: vec![crate::query::candidate::ModuleDeclaration { file: "mod.rs".into(), role: crate::query::candidate::ModuleRole::Helper, items: vec![] }],
        workloads: vec![crate::engine::submission::WorkloadModules { name: "tpch".into(), storage_uses: vec![crate::query::candidate::StorageUseDeclaration::admitted("colpack", ContentId::from_bytes([5; 32]))], modules: vec![] }],
        storage_uses: vec![],
        ..EngineManifest::example(&[])
    };
    write_value(&v1.join("seed-manifest.json"), &json!(manifest));
    write_value(&v1.join("version.json"), &json!({"workloads":{"tpch":{"role":"counted","proof":{"errors":0,"verified":5790,"wall_ns":1},"admission":{"library":"/libraries/tpch","package":"11"}}},
        "general":{"one_engine":true,"own_modules":[],"inherited_storages":[]}}));
    let node = TreeNode { format_version: 1, id: "v001".into(), accepted: true, kind: NodeKind::Branch, branch: "b1".into(), parents: vec!["v000".into()], scale: "sf1".into(),
        score: None, reason: None, session: None, iteration: Some(1), direction: None, rationale: None, created_unix_ms: 2 };
    write_value(&v1.join("node.json"), &json!(node));
    let out = root.join("exported");
    let record = crate::engine::export::export_version(&run, "v001", &out).unwrap();
    for file in ["agent/mod.rs", "agent/plan.rs", "workloads/default/mod.rs", "storages/colpack/verus-family.json", "storages/colpack/crate/src/builder/mod.rs", "plans/tpch/colpack.rs",
        "manifest.json", "README.md", "export.json"] {
        assert!(out.join(file).is_file(), "{file}");
    }
    assert!(!out.join("workloads/tpch").exists(), "an own module is not exported");
    let exported: EngineManifest = read_json(&out.join("manifest.json")).unwrap();
    assert!(exported.storage_uses.is_empty() && exported.workloads.is_empty() && exported.default_modules.len() == 1);
    assert_eq!(exported.families[0].source, PathBuf::from("storages/colpack/verus-family.json"));
    assert!(record["files"].as_array().unwrap().iter().all(|f| f["sha256"].as_str().is_some_and(|s| s.len() == 64)), "{record:#}");
    assert!(fs::read_to_string(out.join("README.md")).unwrap().contains("| tpch | counted | 0 | 5790 | /libraries/tpch | 11 |"));
    assert!(crate::engine::export::export_version(&run, "v001", &out).unwrap_err().message.contains("exists"), "an existing folder is refused");
    assert!(crate::engine::export::export_version(&run, "v009", &root.join("other")).is_err(), "only an accepted version");
    // A side's workspace from the export: the exporting run's workload gets its plans, a new one none.
    let workspace = root.join("workspace-tpch");
    fs::create_dir_all(&workspace).unwrap();
    write_source_root(&workspace, &out, "tpch", &[]).unwrap();
    for file in ["engine/src/agent/mod.rs", "engine/workloads/default/mod.rs", "storages/colpack/verus-family.json", "engine/plans/tpch/colpack.rs"] {
        assert!(workspace.join(file).is_file(), "{file}");
    }
    let side: EngineManifest = read_json(&workspace.join("verus-engine.json")).unwrap();
    assert_eq!((side.workloads.len(), side.workloads[0].name.as_str(), side.workloads[0].storage_uses[0].family.as_deref()), (1, "tpch", Some("colpack")));
    let fresh = root.join("workspace-new");
    fs::create_dir_all(&fresh).unwrap();
    write_source_root(&fresh, &out, "newschema", &[]).unwrap();
    assert!(!fresh.join("engine/plans").exists() && fresh.join("engine/workloads/default/mod.rs").is_file());
    fs::remove_dir_all(&root).unwrap();
}

/// `gendb engine check-request`'s check of a seed: an accepted version folder with its code and manifest (the workload
/// named among a version of several), or an exported folder; every other is a problem named.
#[test]
fn check_request_names_every_problem_of_a_seed() {
    let root = scratch("members-check-seed");
    let (seed_a, seed_b, _) = member_seed_runs(&root);
    write_value(&seed_a.directory().join("seed-manifest.json"), &json!(EngineManifest::example(&[])));
    let several = EngineManifest { workloads: vec![crate::engine::submission::WorkloadModules { name: "sec".into(), storage_uses: vec![], modules: vec![] }], ..EngineManifest::example(&[]) };
    write_value(&seed_b.directory().join("seed-manifest.json"), &json!(several));
    let check = |seed: Seed| {
        let mut found = vec![];
        super::super::rounds::check_seed(&seed, &mut found);
        found
    };
    assert_eq!(check(Seed::Run { version: seed_a.clone(), workload: None }), Vec::<String>::new());
    assert_eq!(check(Seed::Run { version: seed_b.clone(), workload: Some("sec".into()) }), Vec::<String>::new());
    assert!(check(Seed::Run { version: seed_b.clone(), workload: None })[0].contains("the seed names its workload"));
    assert!(check(Seed::Run { version: seed_b.clone(), workload: Some("tpch".into()) })[0].contains("no workload tpch"));
    assert!(check(Seed::Run { version: seed_a.clone(), workload: Some("tpch".into()) })[0].contains("a version of one workload"));
    assert!(check(Seed::Run { version: SeedVersion { run: root.join("nowhere"), version: "v001".into() }, workload: None }).len() >= 2);
    assert!(check(Seed::Source { source: root.join("nowhere") })[0].contains("not an exported engine folder"));
    fs::remove_dir_all(&root).unwrap();
}
