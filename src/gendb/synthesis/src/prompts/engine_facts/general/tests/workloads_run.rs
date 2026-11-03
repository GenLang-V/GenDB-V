//! A scripted run of several workloads on disk (the fixture `workloads-fixture.json`) for
//! the prompt, facts, contract and output tests (no provider, no Verus, no timing): `tpch` (counted, the primary) at
//! sf100, `sec` (counted) at sf3 and `anyschema` (check) at `tiny`. The root `v000` has one side per workload (the
//! fixture's `version_root`); session 1's first submission is accepted as `v001` with the primary's race, `sec`'s race,
//! `anyschema`'s check and the evaluation's `members` and `combined`; and the prepared context of session 1 before and
//! after that submission. The numbers are the fixture's (every v000 cell is the v001 cell x 11 / 10, the rule of
//! the fixture's generator): they say nothing about any engine.

use super::stage_run::{race, scored};
use super::*;
use crate::prompts::engine_facts::general::workloads::FIXTURE;

/// A scripted run of several workloads: its engine directory, session 1 and the fixture with `<run>` resolved.
pub(crate) struct WorkloadsRun {
    pub engine_dir: PathBuf,
    pub session_one: PathBuf,
    pub fixture: Value,
}

impl WorkloadsRun {
    /// The fixture's workloads view (`context.workloads`).
    pub(crate) fn workloads(&self) -> &Value {
        &self.fixture["context"]["workloads"]
    }

    /// The fixture's workload `name` in the workloads view.
    pub(crate) fn workload(&self, name: &str) -> &Value {
        self.workloads().as_array().unwrap().iter().find(|w| w["name"] == name).unwrap()
    }

    /// The scripted run as the shared fixture's helpers take it (session 2 is not used here).
    fn scripted(&self) -> ScriptedRun {
        ScriptedRun { engine_dir: self.engine_dir.clone(), session_one: self.session_one.clone(), session_two: crate::engine::sessions::session_directory(&self.engine_dir, "b1", 2) }
    }
}

/// The workloads fixture, parsed, with `<run>` resolved to `run_dir`.
pub(crate) fn fixture_at(run_dir: &Path) -> Value {
    serde_json::from_str(&FIXTURE.replace("<run>", &run_dir.display().to_string())).unwrap()
}

/// v000's cells of a counted workload: the head's (v001's) finished medians x 11 / 10, the fixture's rule.
fn root_cells(head_cells: &Value) -> Value {
    let cells: Vec<Value> = head_cells.as_array().unwrap().iter().map(|c| {
        let status = match c["status"]["median_ns"].as_u64() {
            Some(ns) => finished(ns * 11 / 10),
            None => c["status"].clone(),
        };
        json!({"template":c["template"],"workers":c["workers"],"status":status})
    }).collect();
    json!(cells)
}

/// The head's totals of `cells` in ms per worker count, keyed by the worker count as text (the workloads fixture `totals_ms`).
fn totals_ms(training: &Value, cells: &Value) -> Value {
    let cells: Vec<CellResult> = serde_json::from_value(cells.clone()).unwrap();
    let totals: serde_json::Map<String, Value> = training_workers(training).iter()
        .map(|w| (w.to_string(), json!(total_over(training, &cells, *w, LIMIT_NS).unwrap() as f64 / 1e6))).collect();
    Value::Object(totals)
}

/// A recorded score of the fixture (`engine::tree::RecordedScore` as JSON) as the tree's type.
fn recorded_score(score: &Value) -> RecordedScore {
    serde_json::from_value(score.clone()).unwrap()
}

/// A version folder of the run: code, notes, the primary's cells at sf100, `extra` records, its README and node.
fn member_version(engine: &Path, node: &TreeNode, cells: &Value, extra: &[(&str, Value)], code: &str) {
    let dir = node_directory(engine, &node.id, true);
    write(&dir.join("code/agent/mod.rs"), code);
    write(&dir.join("NOTES.md"), "# Notes\n\n## Direction\n\nOne engine for every workload.\n");
    write_value(&dir.join("cells/sf100.json"), cells);
    for (name, value) in extra {
        write_value(&dir.join(name), value);
    }
    write(&dir.join("README.md"), &format!("# Engine version {}\n", node.id));
    write_node(engine, node).unwrap();
}

/// A run right after `gendb engine prepare`: the root `v000` with one side per workload (the fixture's
/// `version_root`: `tpch` and `sec` timed alone from their seeds, `anyschema` answered by version 0) on the main line,
/// the ladder, no session yet.
pub(crate) fn workloads_run(root: &Path) -> WorkloadsRun {
    let run_dir = root.join("run");
    let engine = run_dir.join("engine");
    fs::create_dir_all(&engine).unwrap();
    let fixture = fixture_at(&run_dir);
    let run = WorkloadsRun { engine_dir: engine.clone(), session_one: crate::engine::sessions::session_directory(&engine, "b1", 1), fixture };
    let root_record = &run.fixture["version_root"];
    let (tpch, sec) = (run.workload("tpch"), run.workload("sec"));
    let v0_dir = node_directory(&engine, "v000", true);
    let tpch_score = &root_record["workloads"]["tpch"]["score"];
    let mut v0 = node("v000", true, NodeKind::FrameworkGenerated, tree::MAIN, &[], Some(recorded_score(tpch_score)), 1);
    v0.scale = "sf100".into();
    v0.direction = Some("root: one side per workload (the seeds' sides timed alone, the check workload answered by version 0)".into());
    let tpch_cells = root_cells(&tpch["cells"]);
    let sec_cells = root_cells(&sec["cells"]);
    let tpch_g = tpch_score["score"]["normalized_time"].as_str().unwrap();
    let sec_g = root_record["workloads"]["sec"]["score"]["score"]["normalized_time"].as_str().unwrap();
    member_version(&engine, &v0, &tpch_cells, &[("score.json", scored(&tpch["training"], &tpch_cells, tpch_g)), ("workloads/sec/score.json", scored(&sec["training"], &sec_cells, sec_g)),
        ("workloads/anyschema/check.json", json!({"calls":12,"agreed":12,"version":"v000"})),
        ("version.json", json!({"version":"v000","workloads":root_record["workloads"],"combined_score":root_record["combined_score"],"general":root_record["general"]}))],
        "//! The root's primary side.\nverus! {\n/// Answers one query.\npub fn engine() {}\n}\n");
    for (name, text) in [("tpch", "the seed v004 of the run continued/run, timed alone at sf100"), ("sec", "the seed v001 of the run stage/run (its workload sec), timed alone at sf3"),
        ("anyschema", "version 0 over its plain storage, answered at tiny")] {
        write(&v0_dir.join("workloads").join(name).join("SIDE.md"), &format!("# The side of `{name}`\n\n{text}.\n"));
    }
    write(&v0_dir.join("workloads/anyschema/OUT_OF_THE_BOX.md"), "# Out of the box\n\nnot assembled.\n");
    append_main_line(&engine, &MainLineChange { version: "v000".into(), previous: None, reason: "version_0".into(), scale: "sf100".into(), race: None, adopted: None,
        selection: gendb_artifacts::ContentId::from_bytes([11; 32]), at_unix_ms: 1 }).unwrap();
    VersionTree::read(&engine).unwrap().write_views(&engine, &["b1".to_string()]).unwrap();
    records::write_json_atomic(&engine.join(crate::engine::branches::LADDER_FILE), &LadderState { format_version: 1, current: 1, moves: vec![] }).unwrap();
    run
}

/// Session 1's first submission accepted as `v001`: `anyschema` checked, the races of `tpch` (the
/// evaluation's own `race.json`) and `sec` (`workloads/sec/race.json`) against `v000`'s sides, the combined decision, the
/// main line, the findings entry and the session ledger's evaluated call with the fixture's `members` and `combined`.
pub(crate) fn workloads_first_submission(run: &WorkloadsRun) {
    let engine = &run.engine_dir;
    let (tpch, sec) = (run.workload("tpch"), run.workload("sec"));
    let root_record = &run.fixture["version_root"]["workloads"];
    let g = |w: &Value| w["score"]["score"]["normalized_time"].as_str().unwrap().to_string();
    let v1_dir = node_directory(engine, "v001", true);
    let tpch_race = race(&tpch["training"], "v000", (&root_cells(&tpch["cells"]), &g(&root_record["tpch"])), (&tpch["cells"], &g(tpch)), 980_000);
    let sec_race = race(&sec["training"], "v000", (&root_cells(&sec["cells"]), &g(&root_record["sec"])), (&sec["cells"], &g(sec)), 61_000);
    let mut v1 = node("v001", true, NodeKind::Branch, "b1", &["v000"], Some(recorded_score(&tpch["score"])), 2);
    v1.scale = "sf100".into();
    v1.session = Some(run.session_one.clone());
    v1.iteration = Some(1);
    v1.direction = Some("one engine: the two sides merged, one shared engine with a module per workload".into());
    v1.rationale = Some("merged the sides' join and grouping paths; JOIN ... ON chains flattened once for every workload".into());
    member_version(engine, &v1, &tpch["cells"], &[("race.json", tpch_race), ("workloads/sec/race.json", sec_race),
        ("workloads/anyschema/check.json", json!({"calls":12,"agreed":12,"version":"v001"})),
        ("version.json", json!({"version":"v001","workloads":run.fixture["version"]["workloads"],"combined_score":run.fixture["version"]["combined_score"],"general":run.fixture["version"]["general"]}))],
        "//! One engine for every workload: the merged sides.\nverus! {\n/// Answers one query.\npub fn engine() {}\n}\n");
    append_main_line(engine, &MainLineChange { version: "v001".into(), previous: Some("v000".into()), reason: "race".into(), scale: "sf100".into(), race: Some(v1_dir.join("race.json")),
        adopted: None, selection: gendb_artifacts::ContentId::from_bytes([12; 32]), at_unix_ms: 3 }).unwrap();
    let combined = &run.fixture["evaluation"]["combined"];
    append_finding(engine, &json!({"node":"v001","branch":"b1","parent":"v000","accepted":true,"change":v1.rationale,
        "effect":{"parent_finished":combined["parent"]["score"]["finished"],"finished":combined["candidate"]["score"]["finished"],
            "parent_normalized_time":combined["parent"]["score"]["normalized_time"],"normalized_time":combined["candidate"]["score"]["normalized_time"],"cells_faster":30,"cells_slower":0},
        "findings":[],"direction":v1.direction})).unwrap();
    VersionTree::read(engine).unwrap().write_views(engine, &["b1".to_string()]).unwrap();
    write_session_record(&run.session_one, 1, "v000", None);
    let mut ledger = Ledger::open(&run.session_one, ledger_identity(), limits()).unwrap();
    submitted_call(&mut ledger, "88.75", 5_400_000, json!({"eligible":true,"accepted":true,"status":"version_accepted","node":"v001","directory":v1_dir,"parents":["v000"],"branch":"b1",
        "score":v1.score,"main_line":{"changed":true,"head":"v001","reason":"its combined score beat the head's in one interleaved timing per counted workload"},
        "members":run.fixture["evaluation"]["members"],"combined":combined,
        "next_call":{"provider_session":"continue","context":{"calls":[1],"context_tokens":250_000,"peak_context_tokens":270_000,"compactions":0}}}));
}

/// The TPC-H flat packages of the fixture's plain storage (invented ids).
fn tpch_plain_storages() -> Vec<String> {
    ["1a", "1b", "1c", "1d", "1e", "1f", "2a", "2b"].iter().map(|b| b.repeat(32)).collect()
}

/// The prepared context of session 1 of the run (one line, `emphasis` `co_optimization`), before its first submission
/// (`after_first_submission` false: every workload's head is `v000` with its side's numbers, no race yet) or after it
/// (the fixture as it stands: head `v001`).
pub(crate) fn workloads_context(run: &WorkloadsRun, after_first_submission: bool) -> Value {
    let mut context = session_context(&run.scripted(), 1);
    let mut workloads = run.workloads().clone();
    let mut combined = run.fixture["context"]["combined_score"].clone();
    if !after_first_submission {
        let root_record = &run.fixture["version_root"];
        for w in workloads.as_array_mut().unwrap() {
            let name = w["name"].as_str().unwrap().to_string();
            w["head"] = json!("v000");
            w["last_race"] = Value::Null;
            if w["role"] == "check" {
                w["last_check"]["version"] = json!("v000");
                w["last_check"]["record"] = json!(node_directory(&run.engine_dir, "v000", true).join("workloads/anyschema/check.json"));
            } else {
                w["cells"] = root_cells(&w["cells"]);
                w["score"] = root_record["workloads"][&name]["score"].clone();
                w["totals_ms"] = totals_ms(&w["training"], &w["cells"]);
            }
        }
        combined = root_record["combined_score"].clone();
        combined["head"] = json!("v000");
    }
    let primary = workloads[0].clone();
    let contract = Path::new(context["files"]["author_contract"].as_str().unwrap()).parent().unwrap().to_path_buf();
    // The files of each workload as the contract writes them (`prompts::engine_contract::workloads::members_files`): every
    // workload but the primary has its own storages catalog, a check workload no baselines.
    let mut workload_files = serde_json::Map::new();
    for w in workloads.as_array().unwrap() {
        let name = w["name"].as_str().unwrap();
        workload_files.insert(name.into(), crate::prompts::engine_contract::stage::member_files(&contract, name, w["primary"] != true, w["role"] != "check"));
    }
    context["files"]["workloads_record"] = json!(contract.join(crate::prompts::engine_contract::WORKLOADS_FILE));
    context["files"]["workloads"] = Value::Object(workload_files);
    context["engine"]["training"] = primary["training"].clone();
    context["general"]["branches"] = json!([context["general"]["branches"][0].clone()]);
    context["general"]["emphasis"] = json!("co_optimization");
    context["general"]["scale"] = json!({"name":"sf100","index":1,"of":2,"last":true,"plain_storage_bytes":primary["budget"]["plain_storage_bytes"],"plain_storages":tpch_plain_storages(),
        "original_data_bytes":primary["budget"]["budget_bytes"],"original_data_record":primary["budget"]["original_data_record"]});
    let used_by: Vec<Value> = ["narrowpack", "narrowpack2", "narrowpack3", "narrowpack4", "narrowpack5", "narrowpack6"].iter().enumerate()
        .map(|(i, name)| json!({"name":name,"package":format!("3{i}").repeat(32),"counted_bytes":15_000_000_000u64})).collect();
    context["storage_budget"]["used_bytes"] = primary["serving_bytes"].clone();
    context["storage_budget"]["used_by"] = json!(used_by);
    context["integrity_constraints"]["declarations"] = json!([{"table":"lineitem","sql":"PRIMARY KEY (l_orderkey, l_linenumber)"},{"table":"orders","sql":"PRIMARY KEY (o_orderkey)"}]);
    context["general"]["storage_assets"]["head"] = json!(if after_first_submission { "v001" } else { "v000" });
    context["general"]["workloads"] = workloads;
    context["general"]["combined_score"] = combined;
    context
}

/// The feedback events of session 1 after its first submission (accepted as `v001`), as the controller keeps them.
pub(crate) fn workloads_feedback_after_first_submission(run: &WorkloadsRun) -> Vec<Value> {
    let ledger: LedgerState = records::read_json(&RunLayout::new(&run.session_one).ledger()).unwrap();
    let trial = &ledger.trials[0];
    vec![json!({"call":1,"iteration":1,"attempt":1,"author_outcome":"success","provider_reported_cost_usd":"88.75"}),
        json!({"iteration":trial.iteration,"call_id":trial.call_id,"candidate":trial.candidate,"status":"evaluated","evaluation":trial.evaluation,"framework_elapsed_ms":2_400_000,
            "directory":run.session_one.join("iterations/0001")})]
}

/// The ledger view of session 1's next call.
pub(crate) fn workloads_ledger_view(run: &WorkloadsRun) -> Value {
    ledger_view(&run.session_one)
}
