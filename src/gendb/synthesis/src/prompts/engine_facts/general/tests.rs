//! A scripted general-line run on disk for the prompt, contract and output tests (no provider, no Verus, no timing):
//! version 0 and one accepted branch version with their cells, races, profiles and notes, two attempts (one verified,
//! one refused at freeze), the findings log, the main line, the ladder, and branch `b1`'s first two sessions with
//! their ledgers; and the prepared context of a session as `engine::acceptance::prepare_session` writes it. The
//! numbers are invented for the fixture: they say nothing about any engine.

use super::*;
use crate::controller::ledger::{Ledger, Receipt, Tokens, UsageScope};
use crate::controller::limits::{Limits, Money, UNSET_COUNT};
use crate::controller::records;
use crate::engine::branches::LadderState;
use crate::engine::sessions::RunSpend;
use crate::engine::profile::{FunctionSamples, ProfileStop, ProfiledCall, StatementProfile, write_profile};
use crate::engine::score::{NormalizedTime, Score};
use crate::engine::tree::{MainLineChange, NodeKind, RecordedScore, TreeNode, append_finding, append_main_line, write_node};
use gendb_runtime::abi::CallStatus;
use serde_json::json;
use std::fs;

/// The fixture's worker counts.
pub(crate) const WORKERS: [u64; 3] = [1, 32, 64];
const LIMIT_NS: u64 = 60_000_000_000;

/// A scripted run: its engine directory and the sessions of branch `b1`.
pub(crate) struct ScriptedRun {
    pub engine_dir: PathBuf,
    pub session_one: PathBuf,
    pub session_two: PathBuf,
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn write_value(path: &Path, value: &Value) {
    write(path, &format!("{}\n", serde_json::to_string_pretty(value).unwrap()));
}

fn finished(ns: u64) -> Value {
    json!({"status":"finished","median_ns":ns})
}

fn over_time() -> Value {
    json!({"status":"unfinished","reason":"over_time_limit"})
}

/// The training facts of the fixture (as `engine::facts::training_facts` writes them): three templates with both
/// baselines at the timing binding and every worker count, their totals and the variants.
pub(crate) fn training() -> Value {
    let baseline = |umbra: [u64; 3], duckdb: [u64; 3]| -> Vec<Value> {
        WORKERS.iter().enumerate().map(|(i, w)| json!({"binding":"v0","workers":w,"umbra_ns":umbra[i],"duckdb_ns":duckdb[i],"agreement":"exact-order"})).collect()
    };
    let templates = json!([
        {"name":"Q01","tables":["lineitem"],"sql":"SELECT 1","parameters":[],"bindings":[{"name":"v0","arguments":[]},{"name":"v1","arguments":[]}],
            "baselines":baseline([30_000_000, 2_000_000, 2_500_000], [40_000_000, 3_000_000, 2_800_000])},
        {"name":"Q06","tables":["lineitem"],"sql":"SELECT 6","parameters":[],"bindings":[{"name":"v0","arguments":[]}],
            "baselines":baseline([10_000_000, 800_000, 900_000], [12_000_000, 700_000, 1_000_000])},
        {"name":"Q09","tables":["lineitem","orders","part","partsupp","supplier","nation"],"sql":"SELECT 9","parameters":[],"bindings":[{"name":"v0","arguments":[]}],
            "baselines":baseline([300_000_000, 20_000_000, 25_000_000], [400_000_000, 30_000_000, 28_000_000])}]);
    let totals: Vec<Value> = WORKERS
        .iter()
        .enumerate()
        .map(|(i, w)| {
            let sum = |engine: &str| -> u64 { templates.as_array().unwrap().iter().map(|t| t["baselines"][i][engine].as_u64().unwrap()).sum() };
            let (umbra, duckdb) = (sum("umbra_ns"), sum("duckdb_ns"));
            json!({"binding":"v0","workers":w,"umbra_ns":umbra,"duckdb_ns":duckdb,"target_ns":umbra.min(duckdb),"target_engine":if umbra <= duckdb { "umbra" } else { "duckdb" }})
        })
        .collect();
    json!({"timing_binding":"v0","workers":WORKERS,"other_bindings":["v1"],"templates":templates,"baseline_totals":totals,
        "variants":{"kinds":["wrapped_tables","commuted_comparisons"],"frozen":6,"timed":4,"not_timed":2}})
}

/// Cells of one version: per template its status at each worker count.
fn cells(per_template: &[(&str, [Value; 3])]) -> Value {
    let mut out = vec![];
    for (template, statuses) in per_template {
        for (w, status) in WORKERS.iter().zip(statuses) {
            out.push(json!({"template":template,"workers":w,"status":status}));
        }
    }
    json!(out)
}

/// A scale score record (`engine::score::ScaleScore` as JSON) of `cells` against the fixture's baselines.
fn scale_score(cells: &Value, finished_count: usize, g: &str) -> Value {
    let training = training();
    let scored: Vec<Value> = cells
        .as_array()
        .unwrap()
        .iter()
        .map(|c| {
            let template = training["templates"].as_array().unwrap().iter().find(|t| t["name"] == c["template"]).unwrap();
            let i = WORKERS.iter().position(|w| c["workers"] == *w).unwrap();
            let faster = template["baselines"][i]["umbra_ns"].as_u64().unwrap().min(template["baselines"][i]["duckdb_ns"].as_u64().unwrap());
            let time = c["status"]["median_ns"].as_u64().unwrap_or(LIMIT_NS).min(LIMIT_NS);
            json!({"template":c["template"],"workers":c["workers"],"status":c["status"],"time_ns":time,"faster_baseline_ns":faster})
        })
        .collect();
    let totals: Vec<Value> = training["baseline_totals"].as_array().unwrap().iter().map(|t| json!({"workers":t["workers"],"umbra_ns":t["umbra_ns"],"duckdb_ns":t["duckdb_ns"],
        "target_ns":t["target_ns"],"target_engine":t["target_engine"]})).collect();
    json!({"binding":"v0","call_limit_ns":LIMIT_NS,"score":{"finished":finished_count,"normalized_time":g},"cells_total":9,"workers":totals,"cells":scored,"beats_both":false,
        "rule":crate::engine::score::SCORE_RULE})
}

fn recorded(finished: usize, g_billionths: u64, record: &Path) -> RecordedScore {
    RecordedScore { scale: "sf1".into(), score: Score { finished, normalized_time: NormalizedTime::from_billionths(g_billionths) }, cells: 9, beats_both: false, record: record.to_path_buf() }
}

fn profile(statement: &str, workers: usize, stopped: bool, functions: &[(&str, u64)]) -> StatementProfile {
    let total: u64 = functions.iter().map(|(_, s)| s).sum();
    StatementProfile {
        statement: statement.into(),
        template: statement.into(),
        binding: "v0".into(),
        workers,
        calls: vec![ProfiledCall { repetition: 0, status: CallStatus::Ok, wall_ns: 1_200_000_000, process_cpu_ns: 1_100_000_000, caller_cpu_ns: 1_000_000_000,
            peak_anon_bytes: Some(2_000_000_000), read_bytes: Some(0), threads_spawned: 0, threads_joined: 0 }],
        stopped: stopped.then_some(ProfileStop { reason: UnfinishedReason::OverTimeLimit, repetition: Some(1), elapsed_ns: Some(LIMIT_NS), peak_anon_bytes: Some(30_000_000_000) }),
        sampled_call: Some(1),
        interval_us: 1000,
        samples_taken: total,
        samples_dropped: 0,
        samples_unmapped: 0,
        functions: functions.iter().map(|(f, s)| FunctionSamples { function: f.to_string(), object: "libgendb_engine.so".into(), self_samples: *s, self_permille: s * 1000 / total.max(1) }).collect(),
        method: crate::engine::profile::PROFILE_METHOD.into(),
        evidence: PathBuf::from("/fixture/profile-work"),
    }
}

/// A version folder (`versions/<id>/`) with its code, notes, cells, score record, profile, receipts and node.
fn version_folder(engine: &Path, node: &TreeNode, cells_value: &Value, extra: &[(&str, Value)], code: &str, notes: &str, profiles: &[StatementProfile]) {
    let dir = node_directory(engine, &node.id, true);
    write(&dir.join("code/agent/mod.rs"), code);
    write(&dir.join("code-view/agent/mod.rs.md"), &crate::output::code_view(code));
    write(&dir.join("NOTES.md"), notes);
    write_value(&dir.join("cells/sf1.json"), cells_value);
    for (name, value) in extra {
        write_value(&dir.join(name), value);
    }
    write_profile(&dir, &format!("{} at sf1", node.id), profiles).unwrap();
    write(&dir.join("README.md"), &format!("# Engine version {}\n", node.id));
    write_node(engine, node).unwrap();
}

fn node(id: &str, accepted: bool, kind: NodeKind, branch: &str, parents: &[&str], score: Option<RecordedScore>, at: u64) -> TreeNode {
    TreeNode {
        format_version: 1,
        id: id.into(),
        accepted,
        kind,
        branch: branch.into(),
        parents: parents.iter().map(|p| p.to_string()).collect(),
        scale: "sf1".into(),
        score,
        reason: None,
        session: None,
        iteration: None,
        direction: None,
        rationale: None,
        created_unix_ms: at,
    }
}

fn limits() -> Limits {
    Limits { max_iterations: UNSET_COUNT, max_cost_usd: Money::parse("1000").unwrap(), ..crate::controller::limits::tests::limits() }
}

/// One settled and submitted call of `ledger` with `evaluation` recorded for its iteration.
fn submitted_call(ledger: &mut Ledger, cost: &str, elapsed_ms: u64, evaluation: Value) {
    let call = ledger.begin_call().unwrap();
    let call = ledger.assign_provider_session(call.id, |_| true).unwrap();
    let session = call.provider_session.clone().unwrap();
    let output = json!({"candidate_manifest":"verus-engine.json","rationale":"r","data_access_analysis":"d"});
    ledger
        .settle(Receipt { call_id: call.id, session_id: session, ended_unix_ms: u64::MAX, elapsed_ms, reported_cost_usd: Some(Money::parse(cost).unwrap()), billed_cost_usd: None,
            tokens: Some(Tokens::default()), outcome: "success".into(), raw_result: Some(json!({"total_cost_usd":cost})), output: Some(output.clone()), usage_scope: Some(UsageScope::Session) })
        .unwrap();
    ledger.submit(call.id, output).unwrap();
    let trial = ledger.state.trials.last_mut().unwrap();
    trial.status = crate::controller::ledger::TrialStatus::Evaluated;
    trial.evaluation = evaluation;
    // The controller's measure of the whole evaluation (the fixture's evaluations record no step times).
    trial.framework_elapsed_ms = Some(1_260_000);
    ledger.save().unwrap();
}

/// A run right after `gendb engine prepare`: version 0 timed alone, the main line and the ladder, no session yet.
pub(crate) fn version_zero_run(root: &Path) -> ScriptedRun {
    let engine = root.join("run/engine");
    fs::create_dir_all(&engine).unwrap();
    let v0_code = "//! Version 0, generated by GenDB: the verified SQLSpec interpreter over the flat storage of every table.\nuse vstd::prelude::*;\nverus! {\n/// Answers one query with the interpreter.\npub fn engine() {}\n}\n";
    // Version 0: timed alone.
    let v0_cells = cells(&[("Q01", [finished(25_000_000_000), finished(25_100_000_000), finished(25_200_000_000)]), ("Q06", [finished(8_000_000_000), finished(8_100_000_000), finished(8_050_000_000)]),
        ("Q09", [over_time(), over_time(), json!({"status":"unfinished","reason":"over_memory_limit"})])]);
    let v0_dir = node_directory(&engine, "v000", true);
    let v0_score_file = v0_dir.join("score.json");
    let mut v0 = node("v000", true, NodeKind::FrameworkGenerated, tree::MAIN, &[], Some(recorded(6, 2_934_123_456_789, &v0_score_file)), 1);
    v0.direction = Some("version 0: the verified interpreter over the flat storage (framework generated)".into());
    let v0_profiles = [profile("Q01", 1, false, &[("exec::relational::rows::clone_row", 400), ("exec::relational::group::group_members_exec", 300), ("alloc::raw_vec::RawVec::grow_one", 100)]),
        profile("Q06", 32, false, &[("exec::relational::ops::exec_filter", 500), ("flat_tables::materialize_table", 200)]),
        profile("Q09", 64, true, &[("exec::relational::ops::product_rows_exec", 900), ("exec::relational::rows::concat_rows", 100)])];
    version_folder(&engine, &v0, &v0_cells, &[("score.json", scale_score(&v0_cells, 6, "2934.123456789")),
        ("version.json", json!({"version":"v000","storage":{"budget_rule":"version 0 reads only the plain storage, allowed as is at every scale"}}))], v0_code,
        "# Notes\n\n## Direction\n\nVersion 0 (framework generated).\n", &v0_profiles);
    append_main_line(&engine, &MainLineChange { version: "v000".into(), previous: None, reason: "version_0".into(), scale: "sf1".into(), race: None, adopted: None,
        selection: gendb_artifacts::ContentId::from_bytes([7; 32]), at_unix_ms: 1 }).unwrap();
    VersionTree::read(&engine).unwrap().write_views(&engine, &["b1".to_string(), "b2".to_string(), "b3".to_string()]).unwrap();
    records::write_json_atomic(&engine.join(crate::engine::branches::LADDER_FILE), &LadderState { format_version: 1, current: 0, moves: vec![] }).unwrap();
    let session_one = crate::engine::sessions::session_directory(&engine, "b1", 1);
    let session_two = crate::engine::sessions::session_directory(&engine, "b1", 2);
    ScriptedRun { engine_dir: engine, session_one, session_two }
}

/// The scripted run (module documentation): version 0, then branch `b1`'s first session with an accepted version, a
/// verified attempt and a refusal, and the start of its second session.
pub(crate) fn scripted_run(root: &Path) -> ScriptedRun {
    let run = version_zero_run(root);
    first_submission(&run);
    rest_of_session_one(&run);
    run
}

/// The ledger's identity of the scripted sessions.
fn ledger_identity() -> Value {
    json!({"request":{"task":"general"}})
}

/// `session.json` of branch `b1`'s session `number` at sf1, as `engine::branches` writes it (the facts read its number
/// and scale).
fn write_session_record(dir: &Path, number: u32, seed: &str, previous: Option<&Path>) {
    write_value(&dir.join(crate::engine::sessions::SESSION_FILE), &json!({"format_version":1,"branch":"b1","number":number,"kind":"branch","seed":seed,"scale":"sf1",
        "previous":previous,"request":{"format_version":1,"task":{},"limits":{}},"started_unix_ms":1}));
}

/// Session 1's first submission: accepted as `v001` (its folder, race and profile), the main-line change it won, its
/// finding, and the session ledger's first call with its evaluation (receipt: the provider session's total, $12.50).
pub(crate) fn first_submission(run: &ScriptedRun) {
    let (engine, session_one) = (run.engine_dir.clone(), run.session_one.clone());
    let v0_cells: Value = records::read_json(&node_directory(&engine, "v000", true).join("cells/sf1.json")).unwrap();
    let v1_code = "//! A vectorized engine with hash joins and the interpreter behind it.\nuse vstd::prelude::*;\nverus! {\n/// Answers one query.\npub fn engine() {}\n/// Joins two batches on one key column.\npub fn hash_join(k: u64) -> (r: bool) ensures r == (k > 0), { k > 0 }\n}\n";
    // b1's session 1: an accepted version, then a verified attempt (slower), then a refusal at freeze.
    let v1_cells = cells(&[("Q01", [finished(900_000_000), finished(60_000_000), finished(55_000_000)]), ("Q06", [finished(150_000_000), finished(9_000_000), finished(8_000_000)]),
        ("Q09", [finished(9_000_000_000), finished(700_000_000), finished(650_000_000)])]);
    let v1_dir = node_directory(&engine, "v001", true);
    let pairs: Vec<Value> = v1_cells
        .as_array()
        .unwrap()
        .iter()
        .zip(v0_cells.as_array().unwrap())
        .enumerate()
        .map(|(i, (c, p))| {
            let ratio = c["status"]["median_ns"].as_f64().zip(p["status"]["median_ns"].as_f64()).map(|(a, b)| a / b);
            let parent_source = if p["status"]["status"] == "unfinished" { "parent_record" } else { "measured" };
            json!({"template":c["template"],"binding":"v0","workers":c["workers"],"run_order":if i % 2 == 0 { json!(["parent","candidate"]) } else { json!(["candidate","parent"]) },
                "load_average":{"one_minute":5.0 + i as f64 / 10.0,"five_minutes":5.5,"fifteen_minutes":6.0,"line":"5.0 5.5 6.0 3/900 1"},
                "parent":{"status":p["status"],"source":parent_source},"candidate":{"status":c["status"],"source":"measured"},"candidate_over_parent":ratio})
        })
        .collect();
    let race = json!({"parent":"v000","candidate":"b1 iteration 1","binding":"v0","window_start_unix_ms":10,"window_end_unix_ms":20,"pairs":pairs,
        "parent_score":scale_score(&v0_cells, 6, "2934.123456789"),"candidate_score":scale_score(&v1_cells, 9, "41.250000000"),"candidate_better":true,
        "children_run":15,"parent_children_skipped":3,"rule":crate::engine::race::RACE_RULE});
    let mut v1 = node("v001", true, NodeKind::Branch, "b1", &["v000"], Some(recorded(9, 41_250_000_000, &v1_dir.join("race.json"))), 2);
    v1.session = Some(session_one.clone());
    v1.iteration = Some(1);
    v1.direction = Some("vectorized operators over column slices with hash joins and decorrelated subqueries; the interpreter stays behind every fast path".into());
    v1.rationale = Some("hash joins instead of products; subqueries evaluated once".into());
    let v1_profiles = [profile("Q01", 1, false, &[("agent::agg::hash_aggregate", 600), ("agent::scan::filter_slice", 300)]),
        profile("Q06", 32, false, &[("agent::scan::filter_slice", 800)]), profile("Q09", 1, false, &[("agent::join::hash_join", 700), ("agent::join::build_table", 200)])];
    version_folder(&engine, &v1, &v1_cells, &[("race.json", race.clone()), ("receipts.json", json!({"known_provider_reported_cost_usd":"12.5","complete":true})),
        ("version.json", json!({"version":"v001","storage":{"serving_bytes":1_000_000_000u64,"budget_bytes":1_100_693_130u64,"budget":"the original data size at this scale, the bound on changed storage",
            "plain_storage_bytes":1_586_435_879u64,"decision":"changed storage within the original data size at sf1: 1000000000 serving bytes of 1100693130, 100693130 bytes left"}}))],
        v1_code, "# Notes\n\n## Direction\n\nVectorized operators.\n\n## Design\n\nHash joins.\n\n## Tried\n\n- hash join: Q09 finishes (9.0 s at 1 worker).\n\n## Ideas\n\n- radix partitioning.\n\n## Proof notes\n\n- bag equality for joins.\n", &v1_profiles);
    append_main_line(&engine, &MainLineChange { version: "v001".into(), previous: Some("v000".into()), reason: "race".into(), scale: "sf1".into(), race: Some(v1_dir.join("race.json")), adopted: None,
        selection: gendb_artifacts::ContentId::from_bytes([8; 32]), at_unix_ms: 3 }).unwrap();
    append_finding(&engine, &json!({"node":"v001","branch":"b1","parent":"v000","accepted":true,"change":"hash joins instead of products; subqueries evaluated once",
        "effect":{"parent_finished":6,"finished":9,"parent_normalized_time":"2934.123456789","normalized_time":"41.250000000","cells_faster":6,"cells_slower":0},
        "findings":["materializing every table dominated version 0 at every worker count"],"direction":v1.direction})).unwrap();
    VersionTree::read(&engine).unwrap().write_views(&engine, &["b1".to_string(), "b2".to_string(), "b3".to_string()]).unwrap();
    write_session_record(&session_one, 1, "v000", None);
    let mut ledger = Ledger::open(&session_one, ledger_identity(), limits()).unwrap();
    submitted_call(&mut ledger, "12.5", 3_600_000, json!({"eligible":true,"accepted":true,"status":"version_accepted","node":"v001","directory":v1_dir,"parents":["v000"],"branch":"b1",
        "score":v1.score,"main_line":{"changed":true,"head":"v001","reason":"it beat the main-line head in one interleaved timing"},
        "next_call":{"provider_session":"continue","context":{"calls":[1],"context_tokens":180_000,"peak_context_tokens":210_000,"compactions":0}}}));
}

/// The rest of session 1: a verified attempt (not better) and a refusal at freeze, their findings, the ledger's calls 2
/// and 3 in the same provider session (receipts: the session's totals so far, $32.50 and $55.50), and session 2's
/// directory.
pub(crate) fn rest_of_session_one(run: &ScriptedRun) {
    let (engine, session_one) = (run.engine_dir.clone(), run.session_one.clone());
    // The verified attempt b1-a001 (not better), whose Verus run passed.
    let evaluation_dir = session_one.join("iterations/0002/evaluation-1");
    write_value(&evaluation_dir.join("verus-build/run.json"), &json!({"verification":{"success":true,"errors":0,"verified":2100,"is-verifying-entire-crate":true},"wall_ns":80_000_000_000u64}));
    let attempt_dir = node_directory(&engine, "b1-a001", false);
    write(&attempt_dir.join("code/agent/mod.rs"), "//! Radix-partitioned hash joins (slower here).\nverus! {\n/// Partitions one key column.\npub fn radix_partition() {}\n}\n");
    let mut a1 = node("b1-a001", false, NodeKind::Branch, "b1", &["v001"], Some(recorded(9, 45_000_000_000, &attempt_dir.join("race.json"))), 4);
    a1.reason = Some("not better than its parent v001 (the branch head) in one interleaved timing: finished cells 9 vs 9, normalized time 41.250000000 vs 45.000000000 (parent first)".into());
    a1.session = Some(session_one.clone());
    a1.iteration = Some(2);
    write_value(&attempt_dir.join("attempt.json"), &json!({"attempt":"b1-a001","accepted":false,"evaluation":evaluation_dir,"reason":a1.reason}));
    write_value(&attempt_dir.join("race.json"), &json!({"parent":"v001","candidate":"b1 iteration 2","pairs":[],"parent_score":{"score":{"finished":9,"normalized_time":"41.250000000"}},
        "candidate_score":{"score":{"finished":9,"normalized_time":"45.000000000"},"cells_total":9}}));
    write_node(&engine, &a1).unwrap();
    let a2_dir = node_directory(&engine, "b1-a002", false);
    let mut a2 = node("b1-a002", false, NodeKind::Branch, "b1", &["v001"], None, 5);
    a2.reason = Some("refusal: schema_name: agent/plan.rs:12 names column l_shipdate".into());
    write_value(&a2_dir.join("attempt.json"), &json!({"attempt":"b1-a002","accepted":false,"reason":a2.reason}));
    write_node(&engine, &a2).unwrap();
    // The findings log and the views.
    append_finding(&engine, &json!({"node":"b1-a001","branch":"b1","parent":"v001","accepted":false,"reason":a1.reason,"change":"radix-partitioned joins",
        "effect":{"parent_finished":9,"finished":9,"parent_normalized_time":"41.250000000","normalized_time":"45.000000000","cells_faster":2,"cells_slower":7},"findings":[]})).unwrap();
    append_finding(&engine, &json!({"node":"b1-a002","branch":"b1","parent":"v001","accepted":false,"reason":a2.reason,"change":"a planner over named columns"})).unwrap();
    VersionTree::read(&engine).unwrap().write_views(&engine, &["b1".to_string(), "b2".to_string(), "b3".to_string()]).unwrap();
    // The ledger's calls 2 and 3 continue call 1's provider session, so each receipt reports the session's total so far.
    let mut ledger = Ledger::open(&session_one, ledger_identity(), limits()).unwrap();
    submitted_call(&mut ledger, "32.5", 1_800_000, json!({"eligible":false,"accepted":false,"status":"attempt","node":"b1-a001","directory":attempt_dir,"parents":["v001"],"branch":"b1","score":a1.score,
        "error":a1.reason,"failure_class":"attempt","flagged_for_root":false,"next_call":{"provider_session":"continue","context":{"calls":[1,2],"context_tokens":420_000,"peak_context_tokens":450_000,"compactions":0}}}));
    submitted_call(&mut ledger, "55.5", 900_000, json!({"eligible":false,"accepted":false,"status":"attempt","node":"b1-a002","directory":a2_dir,"parents":["v001"],"branch":"b1","error":a2.reason,
        "failure_class":"attempt","flagged_for_root":false,"next_call":{"provider_session":"fresh","session_end":"provider_compacted: the provider compacted this session's context 1 time(s)",
            "context":{"calls":[1,2,3],"context_tokens":90_000,"peak_context_tokens":960_000,"compactions":1}}}));
    write_session_record(&run.session_two, 2, "v001", Some(&run.session_one));
}

/// The ledger view of the next call of the session in `session_dir` (`LedgerState::author_view`, with the call it would
/// begin), as the controller computes it before a call; the ledger is opened (created when new) but not changed.
pub(crate) fn ledger_view(session_dir: &Path) -> Value {
    let ledger = Ledger::open(session_dir, ledger_identity(), limits()).unwrap();
    let next = ledger.state.calls.len() as u64 + 1;
    let mut view = ledger.state.author_view(next, &RunLayout::new(session_dir).ledger()).unwrap();
    view["this_call"] = json!({"call":next,"iteration":ledger.state.trials.len() + 1,"attempt":1});
    view
}

/// The ledger view of call `call`, which the ledger of the session in `session_dir` already holds (begun, its provider
/// session assigned), as the controller computes it before the call.
pub(crate) fn ledger_view_of(session_dir: &Path, call: u64) -> Value {
    let ledger = Ledger::open(session_dir, ledger_identity(), limits()).unwrap();
    ledger.state.author_view(call, &RunLayout::new(session_dir).ledger()).unwrap()
}

/// The outcome of the scripted stopped call's rebuilt receipt.
pub(crate) const STOPPED_OUTCOME: &str = "controller_loss_recovery: provider_error: error_during_execution result with is_error";

/// The next call of the session in `session_dir`, stopped from outside: begun in a fresh provider session, its receipt
/// rebuilt after the controller was lost (no output; `controller-loss-recovery.json` beside it, as the transport writes
/// it), then its retry begun, which resumes the same provider session (as `controller::run` assigns it). Returns the
/// stopped call's id and the retry's.
pub(crate) fn stopped_call_and_retry(session_dir: &Path) -> (u64, u64) {
    let mut ledger = Ledger::open(session_dir, ledger_identity(), limits()).unwrap();
    let call = ledger.begin_call().unwrap();
    let call = ledger.assign_provider_session(call.id, |_| true).unwrap();
    let session = call.provider_session.clone().unwrap();
    ledger
        .settle(Receipt { call_id: call.id, session_id: session.clone(), ended_unix_ms: u64::MAX, elapsed_ms: 25_008_640, reported_cost_usd: Some(Money::parse("255.63").unwrap()),
            billed_cost_usd: None, tokens: Some(Tokens::default()), outcome: STOPPED_OUTCOME.into(), raw_result: Some(json!({"total_cost_usd":"255.63","subtype":"error_during_execution"})),
            output: None, usage_scope: Some(UsageScope::Session) })
        .unwrap();
    write_value(&RunLayout::new(session_dir).call(call.id).join(crate::providers::claude_code::CONTROLLER_LOSS_RECOVERY_FILE),
        &json!({"format_version":1,"kind":"controller_loss_receipt_recovery","call_id":call.id,"session_id":session,"output_accepted":false}));
    let retry = ledger.begin_call().unwrap();
    let retry = ledger.assign_provider_session(retry.id, |_| true).unwrap();
    assert!(retry.resumes_provider_session && retry.provider_session.as_deref() == Some(session.as_str()), "the retry resumes the stopped call's provider session");
    (call.id, retry.id)
}

/// The prepared context of `session` (1 or 2) of branch `b1` over the scripted run, as `prepare_session` writes it.
pub(crate) fn session_context(run: &ScriptedRun, session: u32) -> Value {
    let dir = if session == 1 { &run.session_one } else { &run.session_two };
    let workspace = dir.join("author");
    let contract = workspace.join("contract/engine");
    let seed = if session == 1 { "v000" } else { "v001" };
    let record = json!({"format_version":1,"branch":"b1","number":session,"kind":"branch","seed":seed,"scale":"sf1",
        "previous":if session == 1 { Value::Null } else { json!(run.session_one) },"request":{"format_version":1,"task":{},"limits":{}},"started_unix_ms":1});
    let notes = if session == 1 { "# Notes\n\n## Direction\n\nVersion 0 (framework generated).\n" } else { "# Notes\n\n## Direction\n\nVectorized operators.\n\n## Tried\n\n- hash join: Q09 finishes.\n" };
    // The run's spend as the session role computes it (`RunSpend` over every session ledger), at preparation and refreshed
    // before each call (`run_spend`).
    let budget = Money::parse("1000").unwrap();
    let now = RunSpend::new(&run.engine_dir, budget).now().unwrap();
    let spend = json!({"spent_usd":now.spent,"reserved_usd":now.reserved,"complete":now.complete,"budget_usd":budget,"left_usd":budget.remaining_after(now.spent)});
    let directions = json!([{"branch":"b1","head":seed,"direction":if session == 1 { Value::Null } else { json!("vectorized operators over column slices") }},
        {"branch":"b2","head":"v000","direction":null},{"branch":"b3","head":"v000","direction":null}]);
    json!({
        "files":{"workspace":workspace,"author_contract":contract.join("index.json"),"engine_manifest":workspace.join("verus-engine.json"),"engine_crate":workspace.join("engine"),
            "engine_map":workspace.join("ENGINE_MAP.md"),"notes":workspace.join("NOTES.md"),"versions":workspace.join("versions"),"templates":contract.join("templates.md"),
            "toolkit":contract.join("toolkit.md"),"versions_detail":contract.join("versions.md"),"data":contract.join("data.json"),"toolchain":contract.join("toolchain.json"),
            "search_index":workspace.join("search-index.json"),"new_storages":workspace.join("new-storages"),"submission_example":workspace.join("verus-engine-example.json"),
            "full_context":dir.join("context.json"),"versions_records":run.engine_dir.join("versions"),"tree":run.engine_dir.join("TREE.md"),"findings":run.engine_dir.join("FINDINGS.md")},
        "scope":"verus_general_engine","authoring":"verus_rust_engine","storage_policy":{"kind":"physical_only"},"run_spend":spend,
        "storage_budget":{"budget_bytes":null,"used_bytes":1_000_000_000u64,"left_bytes":null,
            "used_by":[{"name":"keys_sorted","package":"0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a","counted_bytes":600_000_000u64},{"name":"flat_orders","package":"0707070707070707070707070707070707070707070707070707070707070707","counted_bytes":400_000_000u64}],
            "file":contract.join("storage-budget.json"),"meaning":"all serving storage together stays within budget_bytes (null: no budget)"},
        "performance":{"free_bytes_at_prepare":190_000_000_000u64,"evaluation_timing":"official cells: 1 warm + 3 hot calls in one fresh child per (template, worker count), the median hot call"},
        "integrity_constraints":{"declarations":[{"table":"lineitem","sql":"PRIMARY KEY (l_orderkey, l_linenumber)"}],"in_words":"the engine entry states bound_db with these declarations",
            "trust":"user_declared","basis":"request","details":contract.join("integrity-constraints.json")},
        "hardware":{"threads":WORKERS},
        "observed_hardware":{"cpu_model":"Fixture CPU","packages_in_affinity":2,"physical_cores_in_affinity":32,"logical_cpus_in_affinity":64,"affinity_cpu_list":"0-63"},
        "round":{"number":session,"seed":{"kind":"version","description":format!("b1 session {session} (Branch), seeded from {seed}"),"version":seed},"notes":{"file":workspace.join("NOTES.md"),"text":notes}},
        "engine":{"training":training(),"versions":[],"rounds":[],"limits":{"max_iterations":"unset","max_cost_usd":"1000"},
            "stop_rule":"none: the general line stops only when its budget is used or the user stops it; beating both baselines at a scale is a milestone"},
        "general":{"line":"general","session":record,"seed_record":dir.join("seed.json"),
            "seeded":{"notes_from":node_directory(&run.engine_dir, seed, true).join("NOTES.md"),"notes_text":notes,"merge":null},
            "branch":{"name":"b1","head":seed,"direction":if session == 1 { Value::Null } else { json!("vectorized operators over column slices") },"direction_required":session == 1},
            "branches":directions,"main_line_head":seed,
            "scale":{"name":"sf1","index":0,"of":3,"last":false,"plain_storage_bytes":1_586_435_879u64,"plain_storages":["0707070707070707070707070707070707070707070707070707070707070707","0808080808080808080808080808080808080808080808080808080808080808"],"original_data_bytes":1_100_693_130u64,"original_data_record":"/data/sf1/generation/generation.json"},
            "budget_rule":crate::prompts::engine_contract::BUDGET_RULE_TEXT,
            "limits":{"call_limit_seconds":60,"anon_memory_limit_bytes":154_618_822_656u64,"meaning":"framework limits"},
            "spend":spend.clone(),
            "library_bytes":{"bytes":4_200_000_000u64,"asset_bytes":4_100_000_000u64,"record_bytes":100_000_000u64},
            "storage_assets":{"head":"v001","head_derived_bytes":600_000_000u64,"head_derived_assets":3,"head_derived_storages":["keys_sorted"],
                "free_bytes":176_000_000_000u64,"floor_bytes":crate::storage::asset_release::SHARED_HOST_FLOOR_BYTES,"rule":crate::storage::asset_release::KEEP_RULE},
            "files":{"tree":run.engine_dir.join("tree.json"),"tree_markdown":run.engine_dir.join("TREE.md"),"findings":run.engine_dir.join("FINDINGS.md"),
                "versions":run.engine_dir.join("versions"),"attempts":run.engine_dir.join("attempts"),"previous_session":record["previous"]}}})
}

/// The feedback events of session 1 after its first submission (iteration 1 accepted as `v001`), as the controller
/// keeps them: the call event and the evaluated trial.
pub(crate) fn feedback_after_first_submission(run: &ScriptedRun) -> Vec<Value> {
    let ledger: LedgerState = records::read_json(&RunLayout::new(&run.session_one).ledger()).unwrap();
    let trial = &ledger.trials[0];
    vec![json!({"call":1,"iteration":1,"attempt":1,"author_outcome":"success","provider_reported_cost_usd":"12.5"}),
        json!({"call":1,"iteration":1,"local_jobs":{"jobs":3,"by_action":{"trial":2,"verify":1},"failed_jobs":0,"latest":{"job_id":3,"action":"trial","status":"completed"}},
            "session_local_jobs":{"jobs":3,"by_action":{"trial":2,"verify":1},"failed_jobs":0}}),
        json!({"iteration":trial.iteration,"call_id":trial.call_id,"candidate":trial.candidate,"status":"evaluated","evaluation":trial.evaluation,"framework_elapsed_ms":1_260_000,
            "directory":run.session_one.join("iterations/0001")})]
}

pub(crate) fn scratch(name: &str) -> PathBuf {
    crate::controller::test_support::scratch_root(name)
}

pub(crate) mod stage_run;
pub(crate) mod workloads_run;

/// A stage run's facts: the goal's own sections as before, then the
/// workloads side by side, the out-of-the-box record and each kept workload's totals, cells, last race, reference,
/// storage and module; a continued call's facts keep the workloads' lines; the evaluation of the accepted submission
/// shows the kept workload's race.
#[test]
fn a_stage_run_shows_every_workload_the_out_of_the_box_record_and_the_kept_race() {
    use stage_run::*;
    let root = scratch("general-stage-facts");
    let run = stage_run(&root);
    stage_first_submission(&run);
    let context = stage_context(&run, true);
    let view = GeneralView::read(&context, None);
    let text = general_facts(&context, &view, None, &stage_ledger_view(&run)).join("\n");
    let order = ["## Scale", "## Score at sf3", "## Per template at sf3", "## Workloads", "## Out of the box: the seed on `sec`", "## Kept workload `tpch` at sf100", "## Versions",
        "## Storage at sf3", "## Budget and session"];
    let mut at = 0;
    for heading in order {
        let found = text[at..].find(heading).unwrap_or_else(|| panic!("{heading} missing or out of order:\n{text}"));
        at += found + heading.len();
    }
    assert!(text.contains("One engine serves 2 workloads: the goal's score decides every submission (Goal); every kept workload is verified, timed against the parent and shown, never deciding (Stage 2). Totals in ms at 1 / 32 / 64 workers"), "{text}");
    assert!(text.contains("- `sec` (goal) at sf3: head v001, F 17/18 finished, G 128.457. Totals 127500 / 58540 / 46885 against 11411 / 772 / 1131; below neither baseline's total. Storage: 4.99 GB with changed storage, within its 5.44 GB budget. The workload module `workloads/sec/`: 214 lines."), "{text}");
    assert!(text.contains("- `tpch` (kept) at sf100: head v001, F 12/12 finished, G 2.314. Totals 46910 / 3506 / 2858 against 60837 / 3997 / 4290; below Umbra at 1, 32 and 64 workers; below DuckDB at 1, 32 and 64 workers. Storage: 90.77 GB with changed storage, within its 114.64 GB budget. The workload module `workloads/tpch/`: 388 lines."), "{text}");
    assert!(text.contains("When this run was prepared, GenDB froze the seed v016 (`/path/to/runs/general/general-engine`) for `sec` over its plain storage under this run's rules: not assembled: rustc stopped it (step `compile`)."), "{text}");
    assert!(text.contains("```text\nerror[E0433]: failed to resolve: could not find `narrowpack` in `stores`\n") && text.contains("Record: `seed/out-of-the-box/OUT_OF_THE_BOX.md` (beside `files.versions_records`)."), "{text}");
    assert!(text.contains("Head v001: F 12/12 finished, G 2.314 (recorded and shown; it does not decide). Variants: 19 frozen rewrites, 15 with AST bytes of their own, checked at sf1 for every accepted version."), "{text}");
    assert!(text.contains("- 1 worker: Umbra 60837 (the target), DuckDB 114360; v001 (head) 46910, 4/4 finished, ratio 0.771."), "{text}");
    assert!(text.contains("- Q09 (lineitem, orders, part, partsupp, supplier, nation): 30150 / 1677 / 1815; v001 18100 / 1402 / 1121"), "{text}");
    assert!(text.contains("- The last accepted version against its parent here (v001 against v000, one window at sf100): parent F 12/12, G 2.317 vs yours F 12/12, G 2.314; totals 47714 → 46910 / 3444 → 3506 / 2878 → 2858 ms (yours / parent 0.98 / 1.02 / 0.99); 6 cells faster, 6 cells slower; the timing took 15.5 min. Record: `files.versions_records`/v001/workloads/tpch/race.json."), "{text}");
    assert!(text.contains("- Reference: the seed v016 (`/path/to/runs/general/general-engine`), timed alone at sf100 when this run was prepared, as v000: F 12/12 finished, G 2.317; totals 47714 / 3444 / 2878 ms."), "{text}");
    assert!(text.contains("- Storage at sf100 (its library `/path/to/runs/stage/library-tpch`): the head serves 90.77 GB (90766134568 bytes), with changed storage, room left 23.88 GB (23875484294 bytes)"), "{text}");
    assert!(text.contains("- Its workload module `workloads/tpch/`: 388 lines."), "{text}");
    assert!(!text.contains("| "), "no table: {text}");
    // A continued call's facts keep the workloads' lines, not the per-template cells of the kept workload.
    let changed = changed_facts(&context, &view, None, &stage_ledger_view(&run)).join("\n");
    assert!(changed.contains("## Workloads") && changed.contains("- `tpch` (kept) at sf100: head v001") && !changed.contains("## Kept workload") && !changed.contains("## Out of the box"), "{changed}");
    // The evaluation of the accepted submission: the goal's race, then the kept workload's line and race table.
    let ledger: LedgerState = records::read_json(&RunLayout::new(&run.session_one).ledger()).unwrap();
    let evaluation = evaluation_section(&context, &view, &ledger.trials[0]).join("\n");
    assert!(evaluation.contains("## Interleaved timing per template\n") && evaluation.contains("- Kept workload `tpch`: verified, its storages checked, and timed against the parent's `tpch` side at sf100 (recorded, not deciding): parent F 12/12, G 2.317 vs yours F 12/12, G 2.314;"), "{evaluation}");
    assert!(evaluation.contains("## Interleaved timing per template on `tpch` at sf100 (recorded, not deciding)") && evaluation.contains("- Q18: 16345 / 1358 / 1207 → 16200 / 1371 / 1188 (0.99 / 1.01 / 0.98)"), "{evaluation}");
    // Before the first submission (both heads v000): no race yet, and the reference is the head's own timing.
    let before = stage_context(&run, false);
    let first = general_facts(&before, &GeneralView::read(&before, None), None, &stage_ledger_view(&run)).join("\n");
    assert!(first.contains("- No accepted version of this run has been timed against its parent here yet.") && first.contains("The workload module `workloads/sec/`: none yet."), "{first}");
    assert!(first.contains("- `sec` (goal) at sf3: head v000, F 3/18 finished, G 1185.105.") && first.contains("Storage: 7.75 GB of plain storage only (allowed as is)."), "{first}");
    // The other kept outcomes, and a seed that verified on the goal and was timed.
    let not_run = stage::kept_evaluation(&context, &json!({"kept_workloads":[{"name":"tpch","status":"not_run","reason":null,"race":null}]})).join("\n");
    assert_eq!(not_run, "- Kept workload `tpch`: not verified or timed: a submission not better on the goal workload is not evaluated further.");
    let refused = stage::kept_evaluation(&context, &json!({"kept_workloads":[{"name":"tpch","status":"refused","reason":"Verus: 2 errors in agent/workload/open.rs\nmore","race":null}]})).join("\n");
    assert_eq!(refused, "- Kept workload `tpch`: it refused the submission: Verus: 2 errors in agent/workload/open.rs.");
    let mut verified = context.clone();
    verified["general"]["stage"]["seed"]["out_of_the_box"] = json!({"status":"verified","step":"timing","first_errors":[],"score":run.stage()["workloads"][0]["score"],"record":"/r/OUT_OF_THE_BOX.md"});
    let record = stage::out_of_the_box(&verified).join("\n");
    assert!(record.contains(": verified, then timed alone: F 17/18 finished, G 128.457 (step `timing`).") && !record.contains("First errors"), "{record}");
    // Without a stage view nothing of it is rendered.
    let plain = session_context(&scripted_run(&root.join("plain")), 2);
    assert!(stage::workloads(&plain).is_empty() && stage::kept_workloads(&plain).is_empty() && stage::out_of_the_box(&plain).is_empty() && stage::kept_evaluation(&plain, &json!({})).is_empty());
    fs::remove_dir_all(&root).unwrap();
}

/// The stage fixture: it matches its own shape, a stage context of the scripted run matches it, and a record with a
/// missing key, an extra key or another type is named field by field (the stage tests of its context use the same check).
#[test]
fn the_stage_fixture_names_every_key_of_the_interface() {
    use super::stage::{FIXTURE, fixture_shape_errors};
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    for part in ["context", "evaluation", "version"] {
        assert!(fixture_shape_errors(&fixture[part], &fixture[part]).is_empty(), "{part}");
    }
    let root = scratch("general-stage-fixture");
    let run = stage_run::stage_run(&root);
    let context = stage_run::stage_context(&run, false);
    assert_eq!(fixture_shape_errors(&context["general"]["stage"], &fixture["context"]["stage"]), Vec::<String>::new());
    let mut changed = fixture["context"]["stage"].clone();
    changed["workloads"][0]["storage"].as_object_mut().unwrap().remove("serving_bytes");
    changed["workloads"][0]["module_lines"] = json!("214");
    changed["seed"]["extra"] = json!(1);
    assert_eq!(fixture_shape_errors(&changed, &fixture["context"]["stage"]),
        [".seed.extra: not in the fixture", ".workloads[0].module_lines: a string where the fixture has a number", ".workloads[0].storage.serving_bytes: missing"]);
    fs::remove_dir_all(&root).unwrap();
}

/// The facts of session 2's first call (after session 1): scale and ladder, the score of the main-line head (v001
/// after the race, also the branch head), the per-template cells, the profile, the branches, the storage numbers and
/// the run's budget, each on compact lines; the rules they relate to (the budget rule, the limits) are not repeated.
#[test]
fn first_call_facts_show_scale_score_profile_branches_and_budget() {
    let root = scratch("general-facts");
    let run = scripted_run(&root);
    let context = session_context(&run, 2);
    let view = GeneralView::read(&context, None);
    let text = general_facts(&context, &view, None, &ledger_view(&run.session_two)).join("\n");
    assert!(text.starts_with("## Scale\n\nScale **sf1** (1 of 3 on the ladder; earlier moves: none)."), "{text}");
    assert!(text.contains("Main-line head v001: F 9/9 finished, G 41.250."), "{text}");
    // The last evaluation timed at sf1 is session 1's verified attempt (submission 3 was refused at freeze, untimed).
    assert!(text.contains("\n\nEvaluation time at sf1: the last evaluation timed here (session 1, submission 2) took 21.0 min (no step times recorded).\n\n## Score at sf1"), "{text}");
    // Totals at 1 worker: v001's cells 900 + 150 + 9000 ms; the faster baseline total is Umbra's 340 ms.
    assert!(text.contains("- 1 worker: Umbra 340 (the target), DuckDB 452; v001 (main line) 10050, 3/3 finished, ratio 29.559."), "{text}");
    assert!(text.contains("- Q09 (lineitem, orders, part, partsupp, supplier, nation): 300 / 20 / 25; v001 9000 / 700 / 650"), "{text}");
    assert!(text.contains("## Profile of v001") && text.contains("- Q09 at 1 worker: finished, 1200 ms; `agent::join::hash_join` 77.7%, `agent::join::build_table` 22.2%"), "{text}");
    assert!(text.contains("- b1 (yours): head v001, 1 version, 2 attempts; direction: vectorized operators over column slices"), "{text}");
    assert!(text.contains("- b2: head v000, 0 versions, 0 attempts; direction: not stated yet"), "{text}");
    assert!(text.contains("- Budget for a version with a storage change: the original data size, 1.10 GB (1100693130 bytes). The plain storage (allowed as is): 1.59 GB, 1.44 times the original."), "{text}");
    assert_eq!(text.matches("1.59 GB").count(), 1, "the plain storage's size once: {text}");
    assert!(text.contains("- Main-line head v001 serves 1.00 GB (1000000000 bytes), with changed storage, room left 100.69 MB (100693130 bytes)"), "{text}");
    assert!(text.contains("\n- Disk: the run's library holds 4.20 GB, of which the main-line head v001's derived storage assets take 600.00 MB (3 assets, every scale); 176.00 GB free now; an asset build needs its estimated size plus 21.47 GB (20 GiB) free, else it is refused. GenDB keeps the head's storage assets; older versions' derived assets are released and rebuilt by their verified builders when needed.\n"), "{text}");
    // Without the refreshed asset facts (a context prepared before them): the free space at preparation, and the rule.
    let mut older = context.clone();
    older["general"].as_object_mut().unwrap().remove("storage_assets");
    let older_text = general_facts(&older, &view, None, &ledger_view(&run.session_two)).join("\n");
    assert!(older_text.contains("\n- Disk: the run's library holds 4.20 GB; 190.00 GB were free when this session was prepared (not refreshed). GenDB keeps the head's storage assets;"), "{older_text}");
    assert!(text.contains("- Run budget: $1000.00 of provider-reported cost for every branch's calls together. Spent so far: $55.50 ($0.00 of it by this session's earlier calls); left: $944.50."), "{text}");
    assert!(text.contains("- Submissions this session: 0 (no limit)."), "{text}");
    for repeated in ["- The rule:", "wall time", "The run stops when it is used", "the session ends at the next evaluation", ".000 "] {
        assert!(!text.contains(repeated), "a rule or a `.000` time repeated in the facts: {repeated}\n{text}");
    }
    assert!(!text.contains('{') && !text.contains("| "), "no raw JSON and no table: {text}");
    fs::remove_dir_all(&root).unwrap();
}

/// Rule 4 of the scale move: after b1's session 1 ended for the move to sf10 (its last evaluation's session
/// end, as `engine::sessions::session_end` writes it) and the run moved, the fresh session 2 at sf10 shows the new scale
/// and the move in its scale facts, is timed at sf10, and its handoff says in one line why the previous session ended.
#[test]
fn a_fresh_session_after_a_scale_move_shows_the_new_scale_and_why_the_last_ended() {
    use crate::engine::sessions::{DueScaleMove, ProviderContext, next_call, session_end};
    let root = scratch("general-scale-move");
    let run = scripted_run(&root);
    // Session 1's last evaluation ended it for the move.
    let end = session_end(None, &ProviderContext::default(), false, Some(DueScaleMove { head: "main-line head", from: "sf1", to: "sf10" })).unwrap();
    let mut ledger = Ledger::open(&run.session_one, ledger_identity(), limits()).unwrap();
    ledger.state.trials.last_mut().unwrap().evaluation["next_call"] = next_call(Some(end.as_str()), &ProviderContext::default());
    ledger.save().unwrap();
    drop(ledger);
    // The move: scale.json, and the head's score at sf10 recorded by the move's timing.
    records::write_json_atomic(&run.engine_dir.join(crate::engine::branches::LADDER_FILE),
        &LadderState { format_version: 1, current: 1, moves: vec![json!({"to":"sf10","main_line_head":"v001"})] }).unwrap();
    let mut at_sf10 = recorded(9, 52_000_000_000, &run.engine_dir.join("scale-moves/sf10/v001-score.json"));
    at_sf10.scale = "sf10".into();
    crate::engine::tree::record_scale_score(&run.engine_dir, "v001", &at_sf10, "scale_move").unwrap();
    // Session 2's context as the driver prepares it after the move: the inputs of sf10.
    let mut context = session_context(&run, 2);
    context["general"]["scale"] = json!({"name":"sf10","index":1,"of":3,"last":false,"plain_storage_bytes":15_864_358_790u64,"plain_storages":["0707070707070707070707070707070707070707070707070707070707070707","0808080808080808080808080808080808080808080808080808080808080808"],"original_data_bytes":11_006_931_300u64,"original_data_record":"/data/sf10/generation/generation.json"});
    context["general"]["session"]["scale"] = json!("sf10");
    let view = GeneralView::read(&context, None);
    let facts = general_facts(&context, &view, None, &ledger_view(&run.session_two)).join("\n");
    assert!(facts.starts_with("## Scale\n\nScale **sf10** (2 of 3 on the ladder; earlier moves: to sf10 (main-line head v001)). The run moves to the next scale when the main-line head finishes every cell here. Main-line head v001: F 9/9 finished, G 52.000."), "{facts}");
    assert!(facts.contains("## Storage at sf10\n\n- Budget for a version with a storage change: the original data size, 11.01 GB (11006931300 bytes). The plain storage (allowed as is): 15.86 GB, 1.44 times the original."), "{facts}");
    // A head reading only the plain storage is allowed as is: no room is computed for it.
    context["storage_budget"]["used_bytes"] = json!(15_864_358_790u64);
    context["storage_budget"]["used_by"] = json!([{"name":"flat_a","package":"07".repeat(32),"counted_bytes":10_000_000_000u64},{"name":"flat_b","package":"08".repeat(32),"counted_bytes":5_864_358_790u64}]);
    let plain_only = general_facts(&context, &view, None, &ledger_view(&run.session_two)).join("\n");
    assert!(plain_only.contains("- Main-line head v001 serves 15.86 GB (15864358790 bytes), plain storage only: allowed as is"), "{plain_only}");
    // Nothing was timed at sf10 yet: the facts estimate the evaluation time there (version 1 has no cells
    // recorded at sf10 in this fixture, and its evaluations recorded no Verus step), and the handoff gives the previous
    // session's last verdict without a time (the time per step is in the Scale facts).
    assert!(plain_only.contains("\n\nEvaluation time at sf10: no evaluation has been timed here yet. An estimate from GenDB's records, not a measurement: Verus on your whole crate (as long as your own whole-crate `verify`), then the interleaved timing: each of your 9 cells runs 1 warm + 3 hot calls (up to 4 × 60 s for a cell that does not finish); a storage you add is built at sf10 before the timing.\n\n## Score at sf10"), "{plain_only}");
    let handoff = branch_handoff(&context, &view).join("\n");
    assert!(handoff.contains("- Its last evaluation (submission 3): not accepted, recorded as attempt b1-a002: refusal: schema_name") && !handoff.contains("it took"), "{handoff}");
    assert!(handoff.contains("- Why it ended: scale_move: the main-line head finishes every cell at sf1; this session ends here and the run moves to sf10; a fresh session continues from your notebook."), "{handoff}");
    fs::remove_dir_all(&root).unwrap();
}

/// An evaluation's wall time in all and per step as the facts show it; a record without steps (an older
/// build's) shows its total, and a record with neither shows nothing.
#[test]
fn an_evaluation_shows_its_time_per_step() {
    let steps = json!({"steps":[{"step":"verus","elapsed_ms":720_000},{"step":"storages","elapsed_ms":30_000},{"step":"interleaved_timing","elapsed_ms":1_500_000},
        {"step":"variants","elapsed_ms":60_000},{"step":"admission","elapsed_ms":6_000}]});
    assert_eq!(evaluation_time(&steps, Some(2_400_000)).unwrap(), "40.0 min: Verus 12.0 min, storages 0.5 min, interleaved timing 25.0 min, variants at the first scale 1.0 min, admission 0.1 min");
    assert_eq!(evaluation_time(&json!({"framework_evaluation_ns":11_400_000_000_000u64}), None).unwrap(), "190.0 min (no step times recorded)");
    assert_eq!(evaluation_time(&json!({"steps":[]}), Some(60_000)).unwrap(), "1.0 min", "a submission refused at freeze ran no timed step");
    let short = json!({"steps":[{"step":"verus","elapsed_ms":186_000},{"step":"records","elapsed_ms":1_000},{"step":"main_line","elapsed_ms":0}]});
    assert_eq!(evaluation_time(&short, Some(190_000)).unwrap(), "3.2 min: Verus 3.1 min", "steps under 0.05 min are left out");
    assert!(evaluation_time(&json!({}), None).is_none());
}

/// A pair the race timed again is marked `(re-timed)` on both sides in the feedback's race lines, and the
/// text says why pairs are timed again and that the first result is kept in race.json (one line per
/// template, ms rounded, ratios with 2 decimals).
#[test]
fn a_retimed_pair_is_marked_in_the_race_table() {
    let context = json!({"engine":{"training":{"workers":[1],"templates":[{"name":"Q12"},{"name":"Q13"}]}}});
    let side = |status: Value, source: &str| json!({"status":status,"source":source});
    let unfinished = json!({"status":"unfinished","reason":"over_time_limit"});
    let race = json!({"parent":"v022","calls_per_cell":2,"pairs":[
        {"template":"Q12","workers":1,"run_order":["candidate","parent"],"parent":side(json!({"status":"finished","median_ns":7_100_000_000u64}), "measured"),
            "candidate":side(json!({"status":"finished","median_ns":7_000_000_000u64}), "measured"),"candidate_over_parent":0.986,
            "retimed":{"reason":"the candidate did not finish; …","first_pass":{"run_order":["candidate"],"parent":side(json!({"status":"finished","median_ns":7_179_771_339u64}), "parent_record"),
                "candidate":side(unfinished.clone(), "measured"),"candidate_over_parent":null}}},
        {"template":"Q13","workers":1,"run_order":["parent","candidate"],"parent":side(json!({"status":"finished","median_ns":17_000_000_000u64}), "measured"),
            "candidate":side(json!({"status":"finished","median_ns":15_000_000_000u64}), "measured"),"candidate_over_parent":0.882}]});
    let table = race_table(&context, &race).join("\n");
    assert!(table.contains("- Q12: 7100 (re-timed) → 7000 (re-timed) (0.99)"), "{table}");
    assert!(table.contains("- Q13: 17000 → 15000 (0.88)"), "{table}");
    assert!(table.contains("`(re-timed)`: 1 pair was timed again once at the end, because a side was much slower than the parent's recorded time (the host is shared with other services); the re-timed result counts, and the first is kept in race.json."), "{table}");
    assert!(table.contains("(each side 1 warm + 1 hot call, the hot call's time the cell's time)"), "a race recorded under the earlier development cell: {table}");
    let plain = json!({"parent":"v022","calls_per_cell":2,"pairs":[race["pairs"][1].clone()]});
    assert!(!race_table(&context, &plain).join("\n").contains("re-timed"), "no re-timed pair, no mention");
    let development = json!({"parent":"v022","calls_per_cell":4,"pairs":[race["pairs"][1].clone()]});
    let development = race_table(&context, &development).join("\n");
    assert!(development.contains("(each side 1 warm + 3 hot calls, the median hot call the cell's time)"), "the development plan's cell: {development}");
}

/// How long an evaluation takes at the current scale, in the Scale facts. Before any evaluation at a scale,
/// an estimate labelled as one: the head's recorded finished cells there (run again, 1 warm + 3 hot calls each) and the
/// branch's last whole-crate Verus run; after one, the last evaluation timed at the scale with its time per step, left
/// out when the evaluation section above shows that same evaluation.
#[test]
fn the_evaluation_time_is_the_last_one_timed_here_or_an_estimate() {
    let root = scratch("general-evaluation-time");
    let run = version_zero_run(&root);
    let one_line = |mut context: Value| {
        context["general"]["branches"] = json!([context["general"]["branches"][0].clone()]);
        context
    };
    // Session 1's first call: nothing evaluated yet; version 0 finished 6 of its 9 cells at sf1 (99.45 s together).
    let context = one_line(session_context(&run, 1));
    let facts = general_facts(&context, &GeneralView::read(&context, None), None, &ledger_view(&run.session_one)).join("\n");
    assert!(facts.contains("\n\nEvaluation time at sf1: no evaluation has been timed here yet. An estimate from GenDB's records, not a measurement: Verus on your whole crate (as long as your own whole-crate `verify`), then the interleaved timing: the head's 6 finished cells run again, 1 warm + 3 hot calls each (about 4 × 99.5 s = 6.6 min), and each of your 9 cells runs the same way (up to 4 × 60 s for a cell that does not finish); a storage you add is built at sf1 before the timing.\n\n## Score at sf1"), "{facts}");
    // A run with other timed calls (`engine.timed_calls`, the context's `general.timed_calls`) estimates with them.
    let mut once = context.clone();
    once["general"]["timed_calls"] = json!(1);
    let facts = general_facts(&once, &GeneralView::read(&once, None), None, &ledger_view(&run.session_one)).join("\n");
    assert!(facts.contains("the head's 6 finished cells run again, 1 warm + 1 hot call each (about 2 × 99.5 s = 3.3 min), and each of your 9 cells runs the same way (up to 2 × 60 s for a cell that does not finish)"), "{facts}");
    // After the first submission, timed at sf1, with its steps recorded (as `engine::acceptance` records them).
    first_submission(&run);
    let mut ledger = Ledger::open(&run.session_one, ledger_identity(), limits()).unwrap();
    ledger.state.trials[0].evaluation["steps"] = json!([{"step":"verus","elapsed_ms":133_490},{"step":"storages","elapsed_ms":1_259},{"step":"interleaved_timing","elapsed_ms":345_835},
        {"step":"variants","elapsed_ms":15_463},{"step":"admission","elapsed_ms":4_861}]);
    ledger.state.trials[0].framework_elapsed_ms = Some(503_322);
    ledger.save().unwrap();
    let trial = ledger.state.trials[0].clone();
    drop(ledger);
    let context = one_line(session_context(&run, 1));
    let view = GeneralView::read(&context, Some("v001"));
    let facts = general_facts(&context, &view, None, &ledger_view(&run.session_one)).join("\n");
    assert!(facts.contains("\n\nEvaluation time at sf1: the last evaluation timed here (your submission 1) took 8.4 min: Verus 2.2 min, interleaved timing 5.8 min, variants at the first scale 0.3 min, admission 0.1 min.\n\n"), "{facts}");
    // A fresh provider session inside the session leads with that evaluation, which states its own time: not repeated.
    let restarted = general_facts(&context, &view, Some(&trial), &ledger_view(&run.session_one)).join("\n");
    assert!(restarted.contains("- GenDB's evaluation took 8.4 min: Verus 2.2 min") && !restarted.contains("Evaluation time at sf1"), "{restarted}");
    // At sf10 after the move (version 1's cells there recorded by the move): an estimate with sf1's Verus run.
    let v1_sf10 = cells(&[("Q01", [finished(9_000_000_000), finished(600_000_000), finished(550_000_000)]), ("Q06", [finished(1_500_000_000), finished(90_000_000), finished(80_000_000)]),
        ("Q09", [over_time(), finished(7_000_000_000), finished(6_500_000_000)])]);
    write_value(&node_directory(&run.engine_dir, "v001", true).join("cells/sf10.json"), &v1_sf10);
    rest_of_session_one(&run);
    let mut context = one_line(session_context(&run, 2));
    context["general"]["scale"]["name"] = json!("sf10");
    let view = GeneralView::read(&context, None);
    let facts = general_facts(&context, &view, None, &ledger_view(&run.session_two)).join("\n");
    assert!(facts.contains("\n\nEvaluation time at sf10: no evaluation has been timed here yet. An estimate from GenDB's records, not a measurement: Verus on your whole crate (the last whole-crate run in an evaluation took 2.2 min, at sf1), then the interleaved timing: the head's 8 finished cells run again, 1 warm + 3 hot calls each (about 4 × 25.3 s = 1.7 min), and each of your 9 cells runs the same way"), "{facts}");
    // A continued call's facts leave it out: its evaluation section states the latest evaluation's time.
    assert!(!changed_facts(&context, &view, None, &ledger_view(&run.session_two)).join("\n").contains("Evaluation time"));
    fs::remove_dir_all(&root).unwrap();
}

/// A profiled call of `statement` at 32 workers whose samples are `functions` (`(function, object, samples)`, most
/// first) of `taken` samples in all.
fn sampled(statement: &str, stopped: bool, taken: u64, functions: &[(&str, &str, u64)]) -> StatementProfile {
    let mut p = profile(statement, 32, stopped, &[]);
    p.samples_taken = taken;
    p.functions = functions.iter().map(|(f, o, s)| FunctionSamples { function: f.to_string(), object: o.to_string(), self_samples: *s, self_permille: s * 1000 / taken }).collect();
    p
}

/// The profile facts merge the system libraries and the engine's allocation code into one share (libc and
/// allocator), list the engine crate's own functions in the slots the library frames took, and say once what the
/// templates share: the worker count, and the share of libc and the allocator where it leads in most templates (the
/// others show it on their line). The numbers are a run's version 0 at sf1, shortened.
#[test]
fn the_profile_merges_libc_and_the_allocator_and_keeps_engine_functions() {
    let engine = "0d0680057d4810849be35023fea51b3c016f049861b5175dd66e8fc3a3bd1366";
    let profiles = vec![
        sampled("Q02", true, 15_017, &[("[libc.so.6: no symbol]", "libc.so.6", 9285), ("malloc", "libc.so.6", 2758), ("realloc", "libc.so.6", 608), ("exec::relational::rows::concat_rows", engine, 605),
            ("exec::relational::rows::clone_row", engine, 600), ("exec::relational::ops::product_rows_exec", engine, 208), ("__rustc::__rdl_alloc", engine, 164),
            ("<alloc::raw_vec::RawVecInner>::finish_grow", engine, 143), ("[gendb-e6cf0896d352]", "gendb-e6cf0896d352", 3)]),
        sampled("Q06", false, 3_729, &[("[libc.so.6: no symbol]", "libc.so.6", 1880), ("malloc", "libc.so.6", 388), ("flat_tables::text_value", engine, 160),
            ("exec::relational::ops::exec_filter", engine, 120), ("[linux-vdso.so.1]", "linux-vdso.so.1", 1)]),
        sampled("Q15", true, 15_011, &[("exec::relational::group::exec_group_by", engine, 8887), ("[libc.so.6: no symbol]", "libc.so.6", 1937), ("exec::scalar::compare_exec", engine, 1891),
            ("exec::equality::distinct_rows_exec", engine, 660), ("malloc", "libc.so.6", 315)]),
    ];
    let view = GeneralView { profile: Some(("v000".into(), PathBuf::from("/run/engine/versions/v000/PROFILE.md"), profiles)), ..GeneralView::default() };
    let context = json!({"files":{"versions_records":"/run/engine/versions"}});
    let text = super::profile(&context, &view, None).join("\n");
    assert!(text.starts_with("## Profile of v000\n\nEach template at 32 workers, the worker count of its largest gap to the faster baseline (1 warm + 1 measured call)"), "{text}");
    assert!(text.contains("the engine crate's 3 top functions, and libc and the allocator as one share") && text.contains("Full report: `files.versions_records`/v000/PROFILE.md"), "{text}");
    assert!(text.contains("\n\nlibc and the allocator take the most samples in 2 of 3 templates (all but Q15): 60.8%–86.2% of each.\n\n"), "{text}");
    assert!(text.contains("\n- Q02: time limit; `exec::relational::rows::concat_rows` 4.0%, `exec::relational::rows::clone_row` 3.9%, `exec::relational::ops::product_rows_exec` 1.3%\n"), "{text}");
    assert!(text.contains("\n- Q06: finished, 1200 ms; `flat_tables::text_value` 4.2%, `exec::relational::ops::exec_filter` 3.2%\n"), "{text}");
    assert!(text.ends_with("\n- Q15: time limit; `exec::relational::group::exec_group_by` 59.2%, libc and allocator 15.0%, `exec::scalar::compare_exec` 12.5%, `exec::equality::distinct_rows_exec` 4.3%"), "{text}");
    for merged in ["no symbol]", "`malloc`", "`realloc`", "__rdl_alloc", "finish_grow", "[gendb-", "vdso", "after 60.0 s"] {
        assert!(!text.contains(merged), "{merged} is merged or left out:\n{text}");
    }
    // The classification: system libraries and allocation code; the engine library under either name is neither.
    assert!(is_system_library("libc.so.6") && is_system_library("ld-linux-x86-64.so.2") && is_system_library("linux-vdso.so.1") && is_system_library("libgcc_s.so.1"));
    assert!(!is_system_library("libgendb_engine.so") && !is_system_library(engine) && !is_system_library("gendb-e6cf0896d352"));
    assert!(is_allocation_code("__rustc::__rust_no_alloc_shim_is_unstable_v2") && is_allocation_code("<alloc::raw_vec::RawVec<exec::value::EVal>>::grow_one") && is_allocation_code("__rust_alloc"));
    assert!(!is_allocation_code("<alloc::vec::Vec<u8> as core::clone::Clone>::clone") && !is_allocation_code("exec::relational::rows::clone_row"));
}

/// Writes the profile facts of the version folder at `GENDB_REAL_VERSION` (read only: its `profile/` records, as
/// [`GeneralView::read`] reads them) under `GENDB_GENERAL_RENDER_DIR` as `real-profile.md` (a real version
/// 0's profile in the new summary).
#[test]
#[ignore = "writes under GENDB_GENERAL_RENDER_DIR; reads GENDB_REAL_VERSION"]
fn write_real_profile_render() {
    let out = PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
    let folder = PathBuf::from(std::env::var("GENDB_REAL_VERSION").expect("GENDB_REAL_VERSION"));
    let mut profiles: Vec<StatementProfile> =
        fs::read_dir(folder.join(PROFILE_DIRECTORY)).unwrap().flatten().map(|e| serde_json::from_str(&fs::read_to_string(e.path()).unwrap()).unwrap()).collect();
    profiles.sort_by(|a, b| (&a.template, a.workers).cmp(&(&b.template, b.workers)));
    let version = folder.file_name().unwrap().to_string_lossy().into_owned();
    let view = GeneralView { profile: Some((version, folder.join(PROFILE_FILE), profiles)), ..GeneralView::default() };
    let context = json!({"files":{"versions_records":folder.parent().unwrap()}});
    let text = super::profile(&context, &view, None).join("\n") + "\n";
    fs::create_dir_all(&out).unwrap();
    fs::write(out.join("real-profile.md"), &text).unwrap();
    println!("real-profile.md: {} lines, {} words", text.lines().count(), text.split_whitespace().count());
}

/// A run of several workloads' facts: the Scale facts lead with the
/// combined score, the workloads side by side follow, then the primary's own sections (their headings name it), the
/// root's sides and every other workload's section (counted: totals, cells, last race, storage, code; check: what is
/// checked, its last check, templates, storage, code); a continued call keeps the workloads' lines; the evaluation of
/// the accepted submission shows the combined decision, every workload's outcome and the other counted workload's race.
#[test]
fn a_run_of_several_workloads_shows_the_combined_score_every_workload_and_the_sides() {
    use workloads_run::*;
    let root = scratch("general-workloads-facts");
    let run = workloads_run(&root);
    workloads_first_submission(&run);
    let context = workloads_context(&run, true);
    let view = GeneralView::read(&context, None);
    let text = general_facts(&context, &view, None, &workloads_ledger_view(&run)).join("\n");
    let order = ["## Scale", "## Workloads", "## Score at sf100 on `tpch`", "## Per template at sf100 on `tpch`", "## The root's sides", "## Counted workload `sec` at sf3",
        "## Check workload `anyschema` at tiny", "## Versions", "## Storage at sf100 on `tpch`", "## Budget and session"];
    let mut at = 0;
    for heading in order {
        let found = text[at..].find(heading).unwrap_or_else(|| panic!("{heading} missing or out of order:\n{text}"));
        at += found + heading.len();
    }
    for said in [
        "Scale **sf100** of the primary workload `tpch`; every workload stays at its scale for the whole run (Workloads). Head v001 (the best version so far): combined F 30/30 finished, G 16.263 over `tpch` and `sec` (Workloads).",
        "One engine serves 3 workloads: the combined score over the counted workloads (the sums of their F and G; the head's: Scale) decides every submission (Goal); a check workload must verify and answer, never timed; a kept workload is timed and shown, never deciding (One engine for every workload). Totals in ms at 1 / 32 / 64 workers",
        "- `tpch` (counted, primary) at sf100: head v001, F 12/12 finished, G 2.314. Totals 46910 / 3506 / 2858 against 60837 / 3997 / 4290;",
        "Storage: 90.77 GB with changed storage, within its 114.64 GB budget. Code: its own module `workloads/tpch/` (1657 lines); inherited storages `narrowpack`, `narrowpack2`, `narrowpack3`, `narrowpack4`, `narrowpack5`, `narrowpack6` (to be replaced: One engine for every workload); no plan.",
        "- `sec` (counted) at sf3: head v001, F 18/18 finished, G 13.949.",
        "- `anyschema` (check) at tiny: head v001, 12 of 12 calls agreed (v001); never timed, not in the score. Storage: 1.05 MB of plain storage only (exempt from the budget). Code: no own module (it uses the default module `workloads/default/` where the version has one); no plan.",
        "One engine: not yet. Own modules: `tpch`, `sec`; inherited storages: `tpch`, `sec` (the transition, One engine for every workload).",
        "- `tpch` (counted, primary) at sf100: the seed v004 of the run `continued/run`: its code, module and storages, verified whole and timed alone at sf100 when this run was prepared. Your workspace starts from it, with its notebook. Record: `files.versions_records`/v000/workloads/tpch/SIDE.md.",
        "- `sec` (counted) at sf3: the seed v001 of the run `stage/run` (its workload `sec`): its code, module and storages, verified whole and timed alone at sf3 when this run was prepared. Read-only in your workspace: `root-sides/sec/`.",
        "- `anyschema` (check) at tiny: no seed; GenDB's version 0 (the verified interpreter over the plain storage), answered at tiny. Read-only in your workspace: `root-sides/anyschema/`.",
        "  The primary seed's code frozen for `anyschema` out of the box: not assembled: rustc stopped it (step `compile`). Record: `files.versions_records`/v000/workloads/anyschema/OUT_OF_THE_BOX.md.",
        "  ```text\n  error[E0433]: failed to resolve: could not find `narrowpack` in `stores`\n",
        "Head v001: F 18/18 finished, G 13.949 (part of the combined score). No variants.",
        "- The last accepted version against its parent here (v001 against v000, one window at sf3):",
        "Record: `files.versions_records`/v001/workloads/sec/race.json.",
        "- Storage at sf3 (its library `/path/to/runs/workloads/library-sec`): the head serves 2.12 GB (2123302469 bytes), with changed storage, room left 3.32 GB (3316280488 bytes)",
        "- Its code: its own module `workloads/sec/` (818 lines); inherited storages `dictpack`, `dictpack2`, `dictpack3`, `dictpack4` (to be replaced: One engine for every workload); no plan.",
        "Every submission verifies this workload's crate whole and answers each of its 3 templates at every visible binding (v0, v1) with the saved answers, before any timing (rule 12); it is never timed and not in the score. Head v001: 12 of 12 calls agreed at tiny (v001). Record: `files.versions_records`/v001/workloads/anyschema/check.json.",
        "- Templates (the tables each reads): X01 (ax_owner), X12 (ax_item), X20 (ax_item, ax_kind). SQL, parameters and bindings: `files.workloads.anyschema.templates`.",
        "- Storage at tiny (its library `/path/to/runs/workloads/library-anyschema`): the head serves 1.05 MB (1048576 bytes) of plain storage only; a check workload is exempt from the budget.",
    ] {
        assert!(text.contains(said), "{said}\n{text}");
    }
    assert!(!text.contains("| ") && !text.contains("## Out of the box") && !text.contains("## Kept workload"), "no table, no stage section: {text}");
    // A continued call's facts keep the workloads' lines, not the sides or the other workloads' sections.
    let changed = changed_facts(&context, &view, None, &workloads_ledger_view(&run)).join("\n");
    assert!(changed.contains("## Workloads") && changed.contains("- `sec` (counted) at sf3: head v001") && !changed.contains("## The root's sides") && !changed.contains("## Counted workload"), "{changed}");
    // The evaluation of the accepted submission: the primary's race, the combined decision, every workload's outcome and
    // the other counted workload's race table.
    let ledger: LedgerState = records::read_json(&RunLayout::new(&run.session_one).ledger()).unwrap();
    let evaluation = evaluation_section(&context, &view, &ledger.trials[0]).join("\n");
    for said in ["- Parent v000; interleaved timing on `tpch` at sf100: parent F 12, G 2.546; yours F 12, G 2.314 (of 12 cells).",
        "- Combined score over `tpch` and `sec` (the decision): parent F 30/30, G 17.890; yours F 30/30, G 16.263: better.",
        "- `tpch` (counted, primary) at sf100: timed against the parent's `tpch` side:",
        "- `sec` (counted) at sf3: timed against the parent's `sec` side: parent F 18/18, G 15.344 vs yours F 18/18, G 13.949;",
        "- `anyschema` (check) at tiny: verified and answered: 12 of 12 calls agreed. Record: `files.versions_records`/v001/workloads/anyschema/check.json.",
        "## Interleaved timing per template on `tpch` at sf100\n", "## Interleaved timing per template on `sec` at sf3\n"] {
        assert!(evaluation.contains(said), "{said}\n{evaluation}");
    }
    // Before the first submission: every head is v000 with its side's numbers, no race yet.
    let before = workloads_context(&run, false);
    let first = general_facts(&before, &GeneralView::read(&before, None), None, &workloads_ledger_view(&run)).join("\n");
    assert!(first.contains("Head v000 (the best version so far): combined F 30/30 finished, G 17.890 over `tpch` and `sec` (Workloads).")
        && first.contains("- No accepted version of this run has been timed against its parent here yet: the head's numbers are its side's, timed alone when the run was prepared."), "{first}");
    // The other outcomes of a submission's workloads.
    let outcomes = workloads::evaluation_lines(&context, &json!({"members":[{"name":"anyschema","role":"check","status":"refused","step":"answers","reason":"X12 at binding v1, 64 workers: the answer disagrees\nmore","race":null,"check":null},
        {"name":"sec","role":"counted","status":"not_run","step":null,"reason":null,"race":null,"check":null}],"combined":null})).join("\n");
    assert_eq!(outcomes, "- `anyschema` (check) at tiny: it refused the submission at step `answers`: X12 at binding v1, 64 workers: the answer disagrees.\n- `sec` (counted) at sf3: not evaluated.");
    // Without a workloads view nothing of it is rendered.
    let plain = session_context(&scripted_run(&root.join("plain")), 2);
    assert!(workloads::overview(&plain).is_empty() && workloads::sides(&plain).is_empty() && workloads::member_sections(&plain).is_empty()
        && workloads::evaluation_lines(&plain, &json!({})).is_empty() && workloads::scale_sentence(&plain).is_none() && workloads::on_primary(&plain).is_empty());
    fs::remove_dir_all(&root).unwrap();
}

/// The workloads fixture: the fixture matches its own shape, a context of the scripted run matches it before and after the first
/// submission, and the run's records (the evaluation and both version records) match theirs (the stage tests of its records
/// use the same check, `stage::fixture_shape_errors`).
#[test]
fn the_workloads_fixture_names_every_key_of_the_interface() {
    use super::stage::fixture_shape_errors;
    use super::workloads::FIXTURE;
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    for part in ["context", "evaluation", "version", "version_root"] {
        assert!(fixture_shape_errors(&fixture[part], &fixture[part]).is_empty(), "{part}");
    }
    assert!(fixture_shape_errors(&fixture["version_root"], &fixture["version"]).is_empty(), "v000's record has the same keys as v001's");
    let root = scratch("general-workloads-fixture");
    let run = workloads_run::workloads_run(&root);
    for after in [false, true] {
        let context = workloads_run::workloads_context(&run, after);
        assert_eq!(fixture_shape_errors(&context["general"]["workloads"], &fixture["context"]["workloads"]), Vec::<String>::new());
        assert_eq!(fixture_shape_errors(&context["general"]["combined_score"], &fixture["context"]["combined_score"]), Vec::<String>::new());
    }
    let mut changed = fixture["context"]["workloads"].clone();
    changed[0]["general"].as_object_mut().unwrap().remove("plan_lines");
    changed[0]["serving_bytes"] = json!("90766134568");
    changed[0]["side_origin"]["extra"] = json!(1);
    assert_eq!(fixture_shape_errors(&changed, &fixture["context"]["workloads"]),
        ["[0].general.plan_lines: missing", "[0].serving_bytes: a string where the fixture has a number", "[0].side_origin.extra: not in the fixture"]);
    fs::remove_dir_all(&root).unwrap();
}
