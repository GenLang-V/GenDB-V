//! A scripted stage run on disk (the fixture `stage-fixture.json`) for the stage prompt,
//! facts, contract and output tests (no provider, no Verus, no timing): the goal workload `sec` at sf3 and the kept
//! workload `tpch` at sf100; the root version `v000` (the goal's version 0 and the seed's timing on the kept workload),
//! then session 1's first submission accepted as `v001` with the goal's race, the kept workload's race and the
//! evaluation's kept part; and the prepared context of session 1 before and after that submission. The numbers are the
//! fixture's: they say nothing about any engine.

use super::*;
use crate::prompts::engine_facts::general::stage::FIXTURE;

/// A scripted stage run: its engine directory, session 1 and the fixture with `<run>` resolved to the run's directory.
pub(crate) struct StageRun {
    pub engine_dir: PathBuf,
    pub session_one: PathBuf,
    pub fixture: Value,
}

impl StageRun {
    /// The stage view of the fixture (`context.stage`).
    pub(crate) fn stage(&self) -> &Value {
        &self.fixture["context"]["stage"]
    }

    /// The fixture's workload `name` in the stage view.
    fn workload(&self, name: &str) -> &Value {
        self.stage()["workloads"].as_array().unwrap().iter().find(|w| w["name"] == name).unwrap()
    }

    /// The scripted run as the shared fixture's helpers take it (session 2 is not used here).
    fn scripted(&self) -> ScriptedRun {
        ScriptedRun { engine_dir: self.engine_dir.clone(), session_one: self.session_one.clone(), session_two: crate::engine::sessions::session_directory(&self.engine_dir, "b1", 2) }
    }
}

/// The stage fixture, parsed, with `<run>` resolved to `run_dir`.
pub(crate) fn fixture_at(run_dir: &Path) -> Value {
    serde_json::from_str(&FIXTURE.replace("<run>", &run_dir.display().to_string())).unwrap()
}

/// The goal's version 0 at sf3: its first template finishes (one serial interpreter call), every other cell reaches the
/// call limit.
fn goal_version_zero_cells(training: &Value) -> Value {
    let mut cells = vec![];
    for (i, t) in training["templates"].as_array().unwrap().iter().enumerate() {
        for w in WORKERS {
            let status = if i == 0 { finished(41_200_000_000) } else { over_time() };
            cells.push(json!({"template":t["name"],"workers":w,"status":status}));
        }
    }
    json!(cells)
}

/// A score record (`engine::score::ScaleScore` as JSON) of `cells` over `training` with G `g`.
pub(super) fn scored(training: &Value, cells: &Value, g: &str) -> Value {
    let faster = |template: &Value, w: &Value| -> u64 {
        let t = training["templates"].as_array().unwrap().iter().find(|t| t["name"] == *template).unwrap();
        let b = t["baselines"].as_array().unwrap().iter().find(|b| b["binding"] == "v0" && b["workers"] == *w).unwrap();
        b["umbra_ns"].as_u64().unwrap().min(b["duckdb_ns"].as_u64().unwrap())
    };
    let scored: Vec<Value> = cells.as_array().unwrap().iter().map(|c| {
        let time = c["status"]["median_ns"].as_u64().unwrap_or(LIMIT_NS).min(LIMIT_NS);
        json!({"template":c["template"],"workers":c["workers"],"status":c["status"],"time_ns":time,"faster_baseline_ns":faster(&c["template"], &c["workers"])})
    }).collect();
    let finished_count = cells.as_array().unwrap().iter().filter(|c| c["status"]["status"] == "finished").count();
    let totals: Vec<Value> = training["baseline_totals"].as_array().unwrap().iter().map(|t| json!({"workers":t["workers"],"umbra_ns":t["umbra_ns"],"duckdb_ns":t["duckdb_ns"],
        "target_ns":t["target_ns"],"target_engine":t["target_engine"]})).collect();
    json!({"binding":"v0","call_limit_ns":LIMIT_NS,"score":{"finished":finished_count,"normalized_time":g},"cells_total":cells.as_array().unwrap().len(),"workers":totals,"cells":scored,
        "beats_both":false,"rule":crate::engine::score::SCORE_RULE})
}

/// A race report (`engine::race`, `race.json`) of `parent` against `candidate` cells over `training`, in a window of
/// `window_ms`.
pub(super) fn race(training: &Value, parent_name: &str, parent: (&Value, &str), candidate: (&Value, &str), window_ms: u64) -> Value {
    let pairs: Vec<Value> = candidate.0.as_array().unwrap().iter().enumerate().map(|(i, c)| {
        let p = parent.0.as_array().unwrap().iter().find(|p| p["template"] == c["template"] && p["workers"] == c["workers"]).unwrap();
        let ratio = c["status"]["median_ns"].as_f64().zip(p["status"]["median_ns"].as_f64()).map(|(a, b)| a / b);
        let source = if p["status"]["status"] == "unfinished" { "parent_record" } else { "measured" };
        json!({"template":c["template"],"binding":"v0","workers":c["workers"],"run_order":if i % 2 == 0 { json!(["parent","candidate"]) } else { json!(["candidate","parent"]) },
            "load_average":{"one_minute":4.0 + i as f64 / 10.0,"five_minutes":4.5,"fifteen_minutes":5.0,"line":"4.0 4.5 5.0 3/900 1"},
            "parent":{"status":p["status"],"source":source},"candidate":{"status":c["status"],"source":"measured"},"candidate_over_parent":ratio})
    }).collect();
    json!({"parent":parent_name,"candidate":"b1 iteration 1","binding":"v0","calls_per_cell":2,"window_start_unix_ms":1_000_000,"window_end_unix_ms":1_000_000 + window_ms,"pairs":pairs,
        "parent_score":scored(training, parent.0, parent.1),"candidate_score":scored(training, candidate.0, candidate.1),"candidate_better":true,"rule":crate::engine::race::RACE_RULE})
}

/// A version folder of the stage run: code, notes, the goal's cells at sf3 and `extra` records, its README and node.
fn stage_version(engine: &Path, node: &TreeNode, cells: &Value, extra: &[(&str, Value)], code: &str) {
    let dir = node_directory(engine, &node.id, true);
    write(&dir.join("code/agent/mod.rs"), code);
    write(&dir.join("NOTES.md"), "# Notes\n\n## Direction\n\nOne engine for both workloads.\n");
    write_value(&dir.join("cells/sf3.json"), cells);
    for (name, value) in extra {
        write_value(&dir.join(name), value);
    }
    write(&dir.join("README.md"), &format!("# Engine version {}\n", node.id));
    write_node(engine, node).unwrap();
}

/// A recorded score at sf3 of the goal (`engine::tree::RecordedScore`).
fn recorded_at_sf3(finished: usize, g: &str, record: &Path) -> RecordedScore {
    let billionths = (g.parse::<f64>().unwrap() * 1e9).round() as u64;
    RecordedScore { scale: "sf3".into(), score: Score { finished, normalized_time: NormalizedTime::from_billionths(billionths) }, cells: 18, beats_both: false, record: record.to_path_buf() }
}

/// A stage run right after `gendb engine prepare`: the root `v000` (the goal's version 0 timed alone at
/// sf3) on the main line, the ladder, no session yet.
pub(crate) fn stage_run(root: &Path) -> StageRun {
    let run_dir = root.join("run");
    let engine = run_dir.join("engine");
    fs::create_dir_all(&engine).unwrap();
    let fixture = fixture_at(&run_dir);
    let training = &fixture["context"]["stage"]["workloads"][0]["training"];
    let v0_cells = goal_version_zero_cells(training);
    let v0_score = scored(training, &v0_cells, "1185.104912800");
    let v0_dir = node_directory(&engine, "v000", true);
    let v0_recorded = recorded_at_sf3(3, "1185.104912800", &v0_dir.join("score.json"));
    let mut v0 = node("v000", true, NodeKind::FrameworkGenerated, tree::MAIN, &[], Some(v0_recorded.clone()), 1);
    v0.scale = "sf3".into();
    v0.direction = Some("stage root: the goal's version 0 over its plain storage; the seed timed alone on the kept workload".into());
    // The root's records per workload: the goal's version 0 timed alone, the seed timed alone on the
    // kept workload (its score record is the fixture's reference).
    let kept = fixture["context"]["stage"]["workloads"][1].clone();
    let kept_score = scored(&kept["training"], &kept["reference"]["cells"], kept["reference"]["score"]["score"]["normalized_time"].as_str().unwrap());
    let mut workloads = fixture["version"]["workloads"].clone();
    workloads["sec"]["score"] = json!(v0_recorded);
    workloads["sec"]["times"] = json!({"sf3":{"race":null}});
    workloads["sec"]["storage"]["serving_bytes"] = workloads["sec"]["storage"]["plain_storage_bytes"].clone();
    workloads["sec"]["module_lines"] = json!(0);
    workloads["tpch"]["score"] = kept["reference"]["score"].clone();
    workloads["tpch"]["times"] = json!({"sf100":{"race":null}});
    workloads["tpch"]["module_lines"] = json!(0);
    stage_version(&engine, &v0, &v0_cells, &[("score.json", v0_score), ("workloads/tpch/score.json", kept_score), ("version.json", json!({"version":"v000","workloads":workloads}))],
        "//! The stage root.\nverus! {\n/// Answers one query.\npub fn engine() {}\n}\n");
    append_main_line(&engine, &MainLineChange { version: "v000".into(), previous: None, reason: "version_0".into(), scale: "sf3".into(), race: None, adopted: None,
        selection: gendb_artifacts::ContentId::from_bytes([9; 32]), at_unix_ms: 1 }).unwrap();
    VersionTree::read(&engine).unwrap().write_views(&engine, &["b1".to_string()]).unwrap();
    records::write_json_atomic(&engine.join(crate::engine::branches::LADDER_FILE), &LadderState { format_version: 1, current: 0, moves: vec![] }).unwrap();
    let session_one = crate::engine::sessions::session_directory(&engine, "b1", 1);
    StageRun { engine_dir: engine, session_one, fixture }
}

/// Session 1's first submission accepted as `v001`: the goal's race against `v000` at sf3, the kept
/// workload's race against the seed's timing at sf100 (`versions/v001/workloads/tpch/race.json`), the main line, the
/// findings entry and the session ledger's evaluated call, whose evaluation carries the fixture's `kept_workloads`.
pub(crate) fn stage_first_submission(run: &StageRun) {
    let engine = &run.engine_dir;
    let goal = run.workload("sec");
    let kept = run.workload("tpch");
    let v0_cells: Value = records::read_json(&node_directory(engine, "v000", true).join("cells/sf3.json")).unwrap();
    let v1_dir = node_directory(engine, "v001", true);
    let goal_g = goal["score"]["score"]["normalized_time"].as_str().unwrap();
    let goal_race = race(&goal["training"], "v000", (&v0_cells, "1185.104912800"), (&goal["cells"], goal_g), 380_000);
    let kept_race = race(&kept["training"], "v000", (&kept["reference"]["cells"], kept["reference"]["score"]["score"]["normalized_time"].as_str().unwrap()),
        (&kept["cells"], kept["score"]["score"]["normalized_time"].as_str().unwrap()), 930_000);
    let mut v1 = node("v001", true, NodeKind::Branch, "b1", &["v000"], Some(recorded_at_sf3(17, goal_g, &v1_dir.join("race.json"))), 2);
    v1.scale = "sf3".into();
    v1.session = Some(run.session_one.clone());
    v1.iteration = Some(1);
    v1.direction = Some("general column store: one schema-driven encoding plan per workload".into());
    v1.rationale = Some("general dictionary and frame-of-reference encodings from a per-workload plan; hash joins on text keys".into());
    let version = json!({"version":"v001","workloads":run.fixture["version"]["workloads"]});
    stage_version(engine, &v1, &goal["cells"], &[("race.json", goal_race), ("workloads/tpch/race.json", kept_race), ("version.json", version)],
        "//! One engine for every workload: a planner over encoded column blocks.\nverus! {\n/// Answers one query.\npub fn engine() {}\n}\n");
    append_main_line(engine, &MainLineChange { version: "v001".into(), previous: Some("v000".into()), reason: "race".into(), scale: "sf3".into(), race: Some(v1_dir.join("race.json")),
        adopted: None, selection: gendb_artifacts::ContentId::from_bytes([10; 32]), at_unix_ms: 3 }).unwrap();
    append_finding(engine, &json!({"node":"v001","branch":"b1","parent":"v000","accepted":true,"change":v1.rationale,
        "effect":{"parent_finished":3,"finished":17,"parent_normalized_time":"1185.104912800","normalized_time":goal_g,"cells_faster":15,"cells_slower":0},"findings":[],"direction":v1.direction})).unwrap();
    VersionTree::read(engine).unwrap().write_views(engine, &["b1".to_string()]).unwrap();
    write_session_record(&run.session_one, 1, "v000", None);
    let mut ledger = Ledger::open(&run.session_one, ledger_identity(), limits()).unwrap();
    submitted_call(&mut ledger, "64.25", 5_400_000, json!({"eligible":true,"accepted":true,"status":"version_accepted","node":"v001","directory":v1_dir,"parents":["v000"],"branch":"b1",
        "score":v1.score,"main_line":{"changed":true,"head":"v001","reason":"it beat the head in one interleaved timing"},
        "kept_workloads":run.fixture["evaluation"]["kept_workloads"],
        "next_call":{"provider_session":"continue","context":{"calls":[1],"context_tokens":240_000,"peak_context_tokens":260_000,"compactions":0}}}));
}

/// The SEC-EDGAR flat packages of the fixture's plain storage (invented ids).
fn sec_plain_storages() -> Vec<String> {
    ["0a", "0b", "0c", "0d"].iter().map(|b| b.repeat(32)).collect()
}

/// The prepared context of session 1 of the stage run (one line, `emphasis` `co_optimization`), before its first
/// submission (`after_first_submission` false: both workloads' head is `v000`, no kept race yet, no workload module) or
/// after it (the fixture as it stands: head `v001`).
pub(crate) fn stage_context(run: &StageRun, after_first_submission: bool) -> Value {
    let mut context = session_context(&run.scripted(), 1);
    let mut stage = run.stage().clone();
    if !after_first_submission {
        let v0_cells: Value = records::read_json(&node_directory(&run.engine_dir, "v000", true).join("cells/sf3.json")).unwrap();
        for w in stage["workloads"].as_array_mut().unwrap() {
            w["head"] = json!("v000");
            w["module_lines"] = json!(0);
            w["last_race"] = Value::Null;
            if w["role"] == "goal" {
                w["cells"] = v0_cells.clone();
                w["score"] = json!(recorded_at_sf3(3, "1185.104912800", &node_directory(&run.engine_dir, "v000", true).join("score.json")));
                w["storage"]["serving_bytes"] = w["storage"]["plain_storage_bytes"].clone();
                w["storage"]["reads_only_plain"] = json!(true);
            } else {
                w["cells"] = w["reference"]["cells"].clone();
                w["score"] = w["reference"]["score"].clone();
            }
        }
    }
    let goal = stage["workloads"][0].clone();
    let contract = Path::new(context["files"]["author_contract"].as_str().unwrap()).parent().unwrap().to_path_buf();
    // The files of each workload as the stage contract writes them (`prompts::engine_contract::stage`).
    let mut workload_files = serde_json::Map::new();
    for w in stage["workloads"].as_array().unwrap() {
        let name = w["name"].as_str().unwrap();
        workload_files.insert(name.into(), crate::prompts::engine_contract::stage::workload_files(&contract, name, w["role"] == "kept"));
    }
    context["files"]["workloads"] = Value::Object(workload_files);
    context["files"]["stage"] = json!(contract.join(crate::prompts::engine_contract::STAGE_FILE));
    context["engine"]["training"] = goal["training"].clone();
    context["general"]["branches"] = json!([context["general"]["branches"][0].clone()]);
    context["general"]["emphasis"] = json!("co_optimization");
    context["general"]["scale"] = json!({"name":"sf3","index":0,"of":1,"last":true,"plain_storage_bytes":goal["storage"]["plain_storage_bytes"],"plain_storages":sec_plain_storages(),
        "original_data_bytes":goal["storage"]["budget_bytes"],"original_data_record":goal["storage"]["original_data_record"]});
    let used_by: Vec<Value> = if goal["storage"]["reads_only_plain"] == true {
        ["flat_sub", "flat_num", "flat_tag", "flat_pre"].iter().zip(sec_plain_storages()).map(|(name, package)| json!({"name":name,"package":package,"counted_bytes":1})).collect()
    } else {
        vec![json!({"name":"encoded_columns","package":"0e".repeat(32),"counted_bytes":goal["storage"]["serving_bytes"]})]
    };
    context["storage_budget"]["used_bytes"] = goal["storage"]["serving_bytes"].clone();
    context["storage_budget"]["used_by"] = json!(used_by);
    context["integrity_constraints"]["declarations"] = json!([{"table":"sub","sql":"PRIMARY KEY (adsh)"},{"table":"tag","sql":"PRIMARY KEY (tag, version)"},
        {"table":"num","sql":"FOREIGN KEY (adsh) REFERENCES sub (adsh)"},{"table":"pre","sql":"FOREIGN KEY (adsh) REFERENCES sub (adsh)"}]);
    context["general"]["storage_assets"]["head"] = json!(if after_first_submission { "v001" } else { "v000" });
    context["general"]["stage"] = stage;
    context
}

/// The feedback events of session 1 after its first submission (accepted as `v001`), as the controller keeps them.
pub(crate) fn stage_feedback_after_first_submission(run: &StageRun) -> Vec<Value> {
    let ledger: LedgerState = records::read_json(&RunLayout::new(&run.session_one).ledger()).unwrap();
    let trial = &ledger.trials[0];
    vec![json!({"call":1,"iteration":1,"attempt":1,"author_outcome":"success","provider_reported_cost_usd":"64.25"}),
        json!({"iteration":trial.iteration,"call_id":trial.call_id,"candidate":trial.candidate,"status":"evaluated","evaluation":trial.evaluation,"framework_elapsed_ms":1_260_000,
            "directory":run.session_one.join("iterations/0001")})]
}

/// The ledger view of session 1's next call.
pub(crate) fn stage_ledger_view(run: &StageRun) -> Value {
    ledger_view(&run.session_one)
}
