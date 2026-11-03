//! The public fixture integration of the storage-aware path: one `run_workload` of the public controller with the
//! workload storage phase and two query sessions, then the serving route, over a tiny Parquet dataset.
//!
//! The authors are scripted FIXTURE REPLAYS, not synthesis: they copy S1's hand-written framework test sources
//! (`verification/tests/fixtures/verus_storage`: storage `sensor_days` with a zone map of `day`, and a query over it)
//! into their workspaces and drive the normal tools through the session socket as an author would. Everything else is
//! the product path: request, preparation, preflight, roles, freeze, Verus, storage publication and asset build,
//! registration, query evaluation over the stored assets, v4 qualification, close and serving.
//!
//! Checks: storage tools run in the storage session (with a diagnostic query trial of statement 0 over the workspace
//! storage) and its submission reuses the checked storage (one asset build); query 0 reuses the workload's admitted asset
//! without building, and first runs an unverified diagnostic trial (`verification: "not_run"`) of the crate it then
//! submits, verified whole and admitted as usual; a query manifest whose storage lacks a
//! demanded column is refused (`storage_does_not_cover_demand`); query 1 creates a storage in its own session, which
//! qualification registers as a new version; per-role accounting; serving a new binding from the library. Query 0 runs
//! the execution-time objective of a template: two named benchmark bindings × both worker counts are measured and
//! scored (the other admission bindings are tested once, untimed), the user's early stop is decided on that whole
//! matrix of the one submission, and the final measurement serves the same cells.
//!
//! A second fixture runs the same public route under declared integrity constraints that hold on the fixture rows
//! (PRIMARY KEYs of site and sensor, sensor's FOREIGN KEY to site, a named CHECK on sensor's day): the workload storage
//! opts in to the storage entry v2 (its builder requires `source_witnessed` and derives distinct ids from it), the query
//! uses the entry v5 with a lemma reading the declared key, only certified tiny cases run, and serving takes the
//! constrained package only for a request declaring exactly that list (see its test).
//!
//! Needs the pinned frontend Python, the pinned Verus and the `gendb` executable as the worker (`GENDB_WORKER`);
//! run with `-- --ignored`.

use super::authors::WorkloadAuthors;
use super::*;
use crate::controller::author::{AuthorCall, AuthorTransport, CandidateSubmission, Capability};
use crate::controller::hardware::Hardware;
use crate::controller::ledger::{Receipt, Tokens};
use crate::controller::limits::tests::limits;
use crate::controller::limits::Limits;
use crate::controller::request::{QueryRequest, WorkloadStorageRequest};
use crate::controller::session::forward_job;
use crate::controller::test_support::{receipt, scratch_root};
use crate::query::host_locks::HostLocks;
use crate::tools::LocalToolContext;
use arrow::array::{ArrayRef, Date32Array, Decimal128Array, Int32Array, RecordBatch, StringArray};
use arrow::datatypes::{DataType, Field, Schema};
use gendb_artifacts::{ColType, ColumnSpec};
use gendb_frontend::params::ParamRequest;
use gendb_storage::import::{DataFormat, DatasetSpec, TableSpec};
use gendb_verification::admission::IntegrityConstraints;
use std::fs;
use std::sync::Arc;

/// S1's framework test fixture sources.
fn fixture(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../verification/tests/fixtures/verus_storage").join(name);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn write_file(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn write_parquet(path: &Path, batch: &RecordBatch) {
    let mut writer = parquet::arrow::ArrowWriter::try_new(fs::File::create(path).unwrap(), batch.schema(), None).unwrap();
    writer.write(batch).unwrap();
    writer.close().unwrap();
}

/// `site` (2 rows) and `sensor` (7 rows, days 2000-01-01 + 0..7 days, i.e. Date32 10957..10963).
pub(super) fn dataset(root: &Path) -> DatasetSpec {
    fs::create_dir_all(root).unwrap();
    let column = |name: &str, ty: ColType, nullable: bool| ColumnSpec { name: name.into(), ty, nullable };
    let site_fields = vec![column("code", ColType::Utf8, false), column("region", ColType::I32, false)];
    let sensor_fields = vec![
        column("id", ColType::I32, false),
        column("site", ColType::I32, false),
        column("reading", ColType::Decimal { p: 10, s: 2 }, false),
        column("day", ColType::Date32, false),
        column("tag", ColType::Utf8, false),
        column("note", ColType::Utf8, true),
    ];
    let site = RecordBatch::try_new(
        Arc::new(Schema::new(vec![Field::new("code", DataType::Utf8, false), Field::new("region", DataType::Int32, false)])),
        vec![Arc::new(StringArray::from(vec!["abc", "xyz"])) as ArrayRef, Arc::new(Int32Array::from(vec![1, 2]))],
    )
    .unwrap();
    let rows = 0..7i32;
    let sensor = RecordBatch::try_new(
        Arc::new(Schema::new(vec![
            Field::new("id", DataType::Int32, false),
            Field::new("site", DataType::Int32, false),
            Field::new("reading", DataType::Decimal128(10, 2), false),
            Field::new("day", DataType::Date32, false),
            Field::new("tag", DataType::Utf8, false),
            Field::new("note", DataType::Utf8, true),
        ])),
        vec![
            Arc::new(Int32Array::from(rows.clone().map(|i| 100 + i).collect::<Vec<_>>())) as ArrayRef,
            Arc::new(Int32Array::from(rows.clone().map(|i| i % 2 + 1).collect::<Vec<_>>())),
            Arc::new(Decimal128Array::from(rows.clone().map(|i| i as i128 * 125 - 200).collect::<Vec<_>>()).with_precision_and_scale(10, 2).unwrap()),
            Arc::new(Date32Array::from(rows.clone().map(|i| 10957 + i).collect::<Vec<_>>())),
            Arc::new(StringArray::from(rows.clone().map(|i| format!("t{i}")).collect::<Vec<_>>())),
            Arc::new(StringArray::from(rows.map(|i| (i % 3 == 0).then(|| format!("n{i}"))).collect::<Vec<_>>())),
        ],
    )
    .unwrap();
    write_parquet(&root.join("site.parquet"), &site);
    write_parquet(&root.join("sensor.parquet"), &sensor);
    let table = |name: &str, fields: Vec<ColumnSpec>| TableSpec { name: name.into(), fields, locations: vec![root.join(format!("{name}.parquet"))], format: DataFormat::Parquet };
    DatasetSpec { tables: vec![table("site", site_fields), table("sensor", sensor_fields)] }
}

fn parameters(max: &str) -> Vec<ParamRequest> {
    serde_json::from_value(json!([{"index":1,"type":"date","binding":{"free":{"min":"2000-01-01","max":max}}}])).unwrap()
}

/// One session's limits: one submission, no cost guard (fixture replays cost nothing), a long call bound.
fn session_limits() -> Limits {
    Limits { max_iterations: 1, max_cost_usd: Money::UNSET, author_timeout_seconds: 3600, ..limits() }
}

/// The storage crate of `sensor_days` (S1's fixture interface and builder, with zone-map blocks of `block` rows; the
/// fixture's proofs are generic in the block size) and its manifest under `dir`, storing `columns` of `sensor`: the
/// manifest path relative to the workspace.
fn write_storage(workspace: &Path, dir: &str, columns: &[&str], block: usize) -> String {
    let base = workspace.join(dir);
    let interface = fixture("interface.rs");
    let fixed = "pub const BLOCK: usize = 2;";
    assert!(interface.contains(fixed), "S1's interface fixture defines BLOCK");
    write_file(&base.join("crate/src/stores/sensor_days/interface/mod.rs"), &interface.replace(fixed, &format!("pub const BLOCK: usize = {block};")));
    write_file(&base.join("crate/src/builder/mod.rs"), &fixture("builder.rs"));
    let manifest = json!({"format_version":1,"name":"sensor_days","crate_dir":"crate","tables":[{"table":"sensor","columns":columns}],
        "parts":["block_min_day (Date32 per block)","block_max_day (Date32 per block)","id per row","reading coefficient (scale 2) per row","day (Date32) per row"],
        "layout":{"summary":format!("S1 framework test fixture: canonical row order with a zone map of day over blocks of {block} rows"),"units":format!("rows, blocks of {block} rows, Date32 days"),"choice":"fixture replay (not synthesized): exercises block skipping"},
        "modules":[{"file":"stores/sensor_days/interface/mod.rs","role":"interface","items":["represents","blocks_before"]},{"file":"builder/mod.rs","role":"builder","items":["build"]}],
        "notes":"copied from verification/tests/fixtures/verus_storage by the scripted fixture author"});
    let path = format!("{dir}/verus-storage.json");
    write_file(&workspace.join(&path), &manifest.to_string());
    path
}

/// What a scripted fixture author does in its one call.
#[derive(Clone, Copy, PartialEq)]
enum Script {
    /// Workload storage author: storage_check and storage_build of `sensor_days`, then submit it.
    Storage,
    /// Query author reusing the admitted workload storage; first a coverage refusal check.
    QueryReusingAdmitted,
    /// Query author creating a new `sensor_days` version (blocks of 3 rows) in its own session: storage_check,
    /// storage_build and storage_register through the query role's tools, then a submission over that workspace
    /// storage.
    QueryCreatingStorage,
    /// Workload storage author of a run declaring [`declared_constraints`]: `sensor_days` opting in to the storage entry
    /// v2 (`uses_declared_constraints`) with the witnessed-key builder; storage_check and storage_build, then submit it.
    DeclaredStorage,
    /// Query author of that run: the fixture query with the declared-key lemma (entry v5) over the admitted workload
    /// storage; check, then submit it.
    DeclaredQuery,
}

/// S1's builder made a storage entry v2 builder (T3's framework fixture variant): it requires the entry's
/// `source_witnessed` and calls the appended witnessed-key lemma.
fn witnessed_builder() -> String {
    let edits = [
        ("    requires source_wf(src@), in_domain(tables(src@)),\n", "    requires source_wf(src@), in_domain(tables(src@)), source_witnessed(src@),\n"),
        ("        assert(tables(v)[0] == t);\n",
         "        assert(tables(v)[0] == t);\n        if t.len() >= 2 {\n            lemma_delivered_ids_distinct(v, 0, 1);\n            assert(ids(pv)[0] != ids(pv)[1]);\n        }\n"),
    ];
    let mut builder = fixture("builder.rs");
    for (from, to) in edits {
        assert!(builder.contains(from), "S1's builder fixture has {from:?}");
        builder = builder.replace(from, to);
    }
    format!("{builder}{}", declared_lemma("witnessed_key.rs"))
}

/// A T2/T3 declared-key lemma fixture under [`declared_constraints`]: sensor declares three constraints (its PRIMARY
/// KEY first), where the lemma fixtures were written for its key alone.
fn declared_lemma(name: &str) -> String {
    let (one, three) = ("declared_schema()[1].constraints.len() == 1", "declared_schema()[1].constraints.len() == 3");
    let lemma = fixture(name);
    assert!(lemma.contains(one), "{name} states sensor's constraint count");
    lemma.replace(one, three)
}

/// A scripted author transport: each call runs its script against the real session (workspace and tools) and returns
/// the script's submission, with a zero-cost receipt that says it is a fixture replay.
struct FixtureReplayAuthor {
    script: Script,
}

impl FixtureReplayAuthor {
    fn job(context: &LocalToolContext, call_dir: &Path, action: &str, arguments: Value) -> Value {
        forward_job(&context.session_service, &call_dir.join("local-jobs"), action, arguments).unwrap()
    }

    fn run(&self, request: &AuthorCall) -> Result<CandidateSubmission, String> {
        let ws = request.workspace;
        let context: LocalToolContext = records::read_json(&ws.join(crate::tools::CONTEXT_FILE)).map_err(|e| e.to_string())?;
        fs::create_dir_all(request.call_dir.join("local-jobs")).map_err(|e| e.to_string())?;
        let mut jobs = vec![];
        let manifest = match self.script {
            Script::Storage => {
                let storage = write_storage(ws, "storages/sensor_days", &["id", "reading", "day"], 2);
                jobs.push(Self::job(&context, request.call_dir, "storage_check", json!({"storage":storage,"job_name":"check"})));
                jobs.push(Self::job(&context, request.call_dir, "storage_build", json!({"storage":storage,"job_name":"build"})));
                // A diagnostic query crate of statement 0 over the workspace storage (read/query cost before submitting).
                write_file(&ws.join("verus/src/agent/mod.rs"), &fixture("agent.rs"));
                write_file(&ws.join("verus-query-diagnostic.json"), &json!({"format_version":2,"crate_dir":"verus",
                    "storage_uses":[{"name":"sensor_days","workspace":storage}],"modules":[{"file":"mod.rs","role":"entry","items":["query"]}]}).to_string());
                jobs.push(Self::job(&context, request.call_dir, "trial", json!({"candidate":"verus-query-diagnostic.json","job_name":"diagnostic","statement":0,"workers":1})));
                write_file(&ws.join("verus-storages.json"), &json!({"format_version":1,"storages":[storage]}).to_string());
                "verus-storages.json".to_string()
            }
            Script::QueryReusingAdmitted | Script::QueryCreatingStorage => {
                write_file(&ws.join("verus/src/agent/mod.rs"), &fixture("agent.rs"));
                let narrow = write_storage(ws, "new-storages/narrow", &["id", "day"], 2);
                write_file(&ws.join("verus-query-narrow.json"), &json!({"format_version":2,"crate_dir":"verus",
                    "storage_uses":[{"name":"sensor_days","workspace":narrow}],"modules":[{"file":"mod.rs","role":"entry","items":["query"]}]}).to_string());
                jobs.push(Self::job(&context, request.call_dir, "check", json!({"candidate":"verus-query-narrow.json","job_name":"narrow"})));
                let storage_use = if self.script == Script::QueryReusingAdmitted {
                    let storages: Value = records::read_json(&ws.join("contract/verus/storages.json")).map_err(|e| e.to_string())?;
                    let admitted = storages["storages"].as_array().into_iter().flatten().find(|s| s["name"] == "sensor_days" && s["applicable"] == true).ok_or("no admitted sensor_days")?;
                    json!({"name":"sensor_days","admitted":admitted["package"]})
                } else {
                    let storage = write_storage(ws, "new-storages/sensor_days", &["id", "reading", "day"], 3);
                    for action in ["storage_check", "storage_build", "storage_register"] {
                        jobs.push(Self::job(&context, request.call_dir, action, json!({"storage":storage,"job_name":action})));
                    }
                    json!({"name":"sensor_days","workspace":storage})
                };
                write_file(&ws.join("verus-query.json"), &json!({"format_version":2,"crate_dir":"verus","storage_uses":[storage_use],
                    "modules":[{"file":"mod.rs","role":"entry","items":["query"]}]}).to_string());
                jobs.push(Self::job(&context, request.call_dir, "check", json!({"candidate":"verus-query.json","job_name":"check"})));
                if self.script == Script::QueryReusingAdmitted {
                    // An unverified diagnostic trial of exactly the crate submitted next.
                    jobs.push(Self::job(&context, request.call_dir, "trial", json!({"candidate":"verus-query.json","job_name":"unverified","workers":1,"verification":"not_run"})));
                }
                "verus-query.json".to_string()
            }
            Script::DeclaredStorage => {
                let storage = write_storage(ws, "storages/sensor_days", &["id", "reading", "day"], 2);
                let mut manifest: Value = records::read_json(&ws.join(&storage)).map_err(|e| e.to_string())?;
                manifest["uses_declared_constraints"] = json!(true);
                write_file(&ws.join(&storage), &manifest.to_string());
                write_file(&ws.join("storages/sensor_days/crate/src/builder/mod.rs"), &witnessed_builder());
                for action in ["storage_check", "storage_build"] {
                    jobs.push(Self::job(&context, request.call_dir, action, json!({"storage":storage,"job_name":action})));
                }
                write_file(&ws.join("verus-storages.json"), &json!({"format_version":1,"storages":[storage]}).to_string());
                "verus-storages.json".to_string()
            }
            Script::DeclaredQuery => {
                write_file(&ws.join("verus/src/agent/mod.rs"), &format!("{}{}", fixture("agent.rs"), declared_lemma("declared_key.rs")));
                let storages: Value = records::read_json(&ws.join("contract/verus/storages.json")).map_err(|e| e.to_string())?;
                let admitted = storages["storages"].as_array().into_iter().flatten().find(|s| s["name"] == "sensor_days" && s["applicable"] == true).ok_or("no applicable sensor_days")?;
                write_file(&ws.join("verus-query.json"), &json!({"format_version":2,"crate_dir":"verus","storage_uses":[{"name":"sensor_days","admitted":admitted["package"]}],
                    "modules":[{"file":"mod.rs","role":"entry","items":["query"]}]}).to_string());
                jobs.push(Self::job(&context, request.call_dir, "check", json!({"candidate":"verus-query.json","job_name":"check"})));
                "verus-query.json".to_string()
            }
        };
        records::write_new_json(&request.call_dir.join("fixture-jobs.json"), &jobs).map_err(|e| e.to_string())?;
        Ok(CandidateSubmission {
            candidate_manifest: manifest.into(),
            rationale: "fixture replay of S1's hand-written framework test sources (not synthesis)".into(),
            data_access_analysis: "zone map of day: the reader requests only blocks that can hold rows before the bound".into(),
        })
    }
}

impl AuthorTransport for FixtureReplayAuthor {
    fn capability(&self) -> Capability {
        Capability {
            transport: "fixture-replay".into(),
            executable: "fixture".into(),
            version: "1".into(),
            model: "none (scripted fixture replay)".into(),
            effort: "none".into(),
            persistent_sessions: true,
            hard_usd_cap: false,
            cost_semantics: "fixture replay: no provider, zero cost".into(),
        }
    }

    fn invoke(&mut self, request: &AuthorCall) -> Receipt {
        let mut settled = receipt(request.call, request.session_id, Some("0"));
        settled.tokens = Some(Tokens::default());
        settled.raw_result = Some(json!({"session_id":request.session_id,"fixture_replay":true}));
        match self.run(request) {
            Ok(submission) => {
                settled.outcome = "success".into();
                settled.output = Some(json!(submission));
            }
            Err(error) => settled.outcome = format!("fixture_script_failed: {error}"),
        }
        settled
    }
}

pub(super) fn request(root: &Path, dataset: DatasetSpec) -> WorkloadRequest {
    let sql = fixture("query.sql");
    let query = |max: &str| QueryRequest { name: None, sql: sql.clone(), limits: session_limits(), parameters: parameters(max), test_bindings: vec![], arguments: vec![], objective: Default::default(), preflight_from: None, reselect_from: None, continue_from: None };
    // Targets far above any fixture time (fixture provenance), so the one submission meets the 5x stop everywhere.
    let target = |binding: &str, workers: usize| json!({"binding":binding,"workers":workers,"median_ns":1_000_000_000_000u64,"provenance":"public fixture: not a measured system","timing_scope":"fixture"});
    let timed = serde_json::from_value(json!({"kind":"execution_time",
        "bindings":[{"name":"early_days","arguments":["2000-01-03"]},{"name":"late_days","arguments":["2000-01-06"]}],
        "targets":[target("early_days", 1), target("early_days", 2), target("late_days", 1), target("late_days", 2)],
        "early_stop":{"min_speedup":5}})).unwrap();
    WorkloadRequest {
        format_version: 2,
        dataset,
        queries: vec![QueryRequest { objective: timed, ..query("2030-12-31") }, query("2029-12-31")],
        hardware: Hardware { threads: vec![1, 2] },
        max_concurrent_queries: 1,
        max_concurrent_preparations: None,
        author_executable: "fixture".into(),
        author_model: Default::default(),
        library: root.join("library"),
        host_locks: HostLocks { activity_lock: root.join("locks/activity.lock"), build_lock: root.join("locks/build.lock"), race_lock: root.join("locks/race.lock") },
        prepared_workload: None,
        data_allowance: None,
        output_home: None,
        workload_storage: Some(WorkloadStorageRequest { limits: session_limits(), stop_before_queries: false }),
        part_access: None,
        storage_policy: Default::default(),
        integrity_constraints: None,
        validation: Default::default(),
        engine: None,
    }
}

fn job<'a>(jobs: &'a Value, name: &str) -> &'a Value {
    jobs.as_array().unwrap().iter().find(|j| j["paths"]["request"].as_str().is_some_and(|p| p.ends_with(&format!("-{name}/request.json")))).unwrap_or_else(|| panic!("job {name} in {jobs}"))
}

fn evaluation_of(session: &Value) -> Value {
    let record = session["trajectory"][0]["evaluation_record"].as_str().unwrap();
    records::read_json(Path::new(record)).unwrap()
}

#[tokio::test]
#[ignore = "runs the pinned Verus toolchain, frontend and the gendb worker; set GENDB_WORKER; -- --ignored"]
async fn public_controller_builds_shares_creates_and_serves_storages() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let root = scratch_root("s4-public-fixture");
    let dataset = dataset(&root.join("data-files"));
    let request = request(&root, dataset);
    // `WorkloadRequest::read` creates the lock files' directory; this request is built in place.
    fs::create_dir_all(root.join("locks")).unwrap();
    let run = root.join("run");
    let authors = WorkloadAuthors {
        storage: Some(FixtureReplayAuthor { script: Script::Storage }),
        queries: vec![FixtureReplayAuthor { script: Script::QueryReusingAdmitted }, FixtureReplayAuthor { script: Script::QueryCreatingStorage }],
    };
    let summary = run_workload(&request, &run, authors, &worker).await.unwrap();
    records::write_new_json(&root.join("summary-copy.json"), &summary).unwrap();
    assert_eq!(summary["status"], "closed", "{summary}");

    // Workload storage: tools built the storage once; the submission reused that checked storage; it was admitted.
    let storage = &summary["workload_storage"];
    assert_eq!(storage["resolution"]["status"], "storages_admitted", "{storage}");
    let admitted = &storage["resolution"]["storages"][0];
    let storage_jobs: Value = records::read_json(&run.join("workload-storage/session/calls/0001/fixture-jobs.json")).unwrap();
    assert_eq!(job(&storage_jobs, "check")["status"], "completed", "{storage_jobs}");
    let diagnostic = job(&storage_jobs, "diagnostic");
    assert_eq!((diagnostic["status"].as_str(), diagnostic["result"]["status"].as_str()), (Some("completed"), Some("allowed")), "{diagnostic}");
    assert_eq!(diagnostic["result"]["storage"][0]["asset_built_now"], false, "the trial reuses the session's checked storage: {diagnostic}");
    let built = &job(&storage_jobs, "build")["result"];
    assert_eq!((built["asset"]["built_now"].as_bool(), &built["asset"]["asset"]), (Some(true), &admitted["asset"]), "{built}");
    assert_eq!(evaluation_of(storage)["storages"][0]["reused_session_check"], true);

    // Query 0: the admitted workload asset is reused (nothing built), the narrow storage is refused by coverage.
    let reuse = &summary["queries"][0];
    assert_eq!(reuse["resolution"]["status"], "verified_package_served", "{reuse}");
    let query_jobs: Value = records::read_json(&run.join("queries/query-0000/calls/0001/fixture-jobs.json")).unwrap();
    let narrow = job(&query_jobs, "narrow");
    assert_eq!(narrow["failure_class"], "missing_input", "{narrow}");
    assert!(narrow["error"].as_str().unwrap().contains("storage_does_not_cover_demand"), "{narrow}");
    // Its unverified diagnostic trial ran the same crate (--no-verify) on the real data, labelled; the same code was
    // then submitted, verified whole and admitted (qualification refuses a build argv with --no-verify).
    let unverified = job(&query_jobs, "unverified");
    assert_eq!((unverified["status"].as_str(), unverified["verification"].as_str(), unverified["diagnostic_unverified"].as_bool()),
        (Some("completed"), Some("verification_not_run"), Some(true)), "{unverified}");
    let result = &unverified["result"];
    assert_eq!((result["status"].as_str(), result["real_data"]["cells"][0]["status"].as_str()), (Some("diagnostic_unverified"), Some("exact")), "{result}");
    assert_eq!((result["build"]["record"]["outcome"].as_str(), result["build"]["record"]["verification"].as_str()), (Some("compiled_unverified"), Some("verification_not_run")), "{result}");
    assert!(result["build"]["record"]["argv"].as_array().unwrap().contains(&json!("--no-verify")), "{result}");
    let evaluation = evaluation_of(reuse);
    assert_eq!((evaluation["storage"][0]["asset"].clone(), evaluation["storage"][0]["asset_built_now"].as_bool()), (admitted["asset"].clone(), Some(false)));
    let cell = &evaluation["measurements"][0];
    assert!(cell["storage_requests"][0]["bytes"].as_u64().is_some(), "{cell}");
    // Query 0's execution time: the benchmark matrix (2 bindings x 2 worker counts), scored as a whole; the other
    // admission bindings tested once; the early stop witnessed on every cell; the final measurement at the same cells.
    let cells: Vec<(String, u64)> = evaluation["measurements"].as_array().unwrap().iter().map(|m| (m["binding"].as_str().unwrap().to_string(), m["workers"].as_u64().unwrap())).collect();
    assert_eq!(cells, [("early_days".to_string(), 1), ("early_days".to_string(), 2), ("late_days".to_string(), 1), ("late_days".to_string(), 2)], "{evaluation}");
    assert!(evaluation["score_ns"].as_u64().is_some() && evaluation["measurements"].as_array().unwrap().iter().all(|m| m["status"] == "exact"), "{evaluation}");
    let jobs = &evaluation["real_data"]["jobs"];
    assert_eq!((jobs[0]["bindings"].clone(), jobs[0]["calls"].as_u64(), jobs[1]["calls"].as_u64()), (json!(["early_days", "late_days"]), Some(4), Some(1)), "{jobs}");
    assert!(jobs[1]["bindings"].as_array().is_some_and(|b| b.contains(&json!("minimum"))), "extrema are tested, not timed: {jobs}");
    assert_eq!(reuse["objective"]["early_stop"]["status"], "met", "{reuse}");
    assert_eq!(reuse["objective"]["early_stop"]["witness"]["cells"].as_array().map(Vec::len), Some(4), "{reuse}");
    let finals = reuse["resolution"]["final_measurement"]["cells"].as_array().unwrap_or_else(|| panic!("final measurement: {reuse}"));
    assert_eq!(finals.iter().map(|c| (c["binding"].as_str().unwrap().to_string(), c["workers"].as_u64().unwrap())).collect::<Vec<_>>(), cells, "{reuse}");
    assert!(finals.iter().all(|c| c["gendb"]["status"] == "allowed"), "{reuse}");

    // Query 1: the query role's storage tools check, build (once) and register a new sensor_days version, reopened
    // from the library; the submission over that workspace storage reuses the checked storage and its asset, and
    // qualification finds the version already admitted.
    let created = &summary["queries"][1];
    assert_eq!(created["resolution"]["status"], "verified_package_served", "{created}");
    let query_jobs: Value = records::read_json(&run.join("queries/query-0001/calls/0001/fixture-jobs.json")).unwrap();
    for action in ["narrow", "storage_check", "storage_build", "storage_register", "check"] {
        assert_eq!(job(&query_jobs, action)["status"], if action == "narrow" { "refused" } else { "completed" }, "{action}: {query_jobs}");
    }
    let tool_build = &job(&query_jobs, "storage_build")["result"];
    assert_eq!((tool_build["asset"]["built_now"].as_bool(), tool_build["build"]["reused"].as_bool()), (Some(true), Some(false)), "{tool_build}");
    let tool_registered = &job(&query_jobs, "storage_register")["result"];
    assert_eq!((tool_registered["build"]["reused"].as_bool(), tool_registered["asset"]["built_now"].as_bool()), (Some(true), Some(false)), "{tool_registered}");
    let registration = &tool_registered["registration"]["registration"];
    assert_eq!(registration["admitted_now"], true, "{tool_registered}");
    assert_ne!(registration["package"], admitted["package"], "a distinct verified version");
    assert_eq!(tool_registered["registration"]["reopened_from_library"][0]["asset"], tool_build["asset"]["asset"], "{tool_registered}");
    let evaluation = evaluation_of(created);
    assert_eq!((evaluation["storage"][0]["asset"].clone(), evaluation["storage"][0]["asset_built_now"].as_bool()), (tool_build["asset"]["asset"].clone(), Some(false)),
        "the session's checked storage (built by the tool job) is reused");
    let qualification: Value = records::read_json(Path::new(created["qualification"][0]["qualification_record"].as_str().unwrap())).unwrap();
    let registered = &qualification["registered_storages"][0];
    assert_eq!((&registered["package"], &registered["admitted_now"]), (&registration["package"], &json!(false)), "{qualification}");

    // Accounting per role; zero reported cost for the replays.
    let accounting = &summary["author_accounting"];
    assert_eq!(accounting["sessions"].as_array().unwrap().len(), 3, "{accounting}");
    assert_eq!(accounting["sessions"][0]["role"], "workload_storage");

    // Serving a new binding from the library through the v4 route, with the synthesis run directory moved away.
    fs::rename(&run, root.join("run-moved")).unwrap();
    let mut serve_request = request.clone();
    serve_request.prepared_workload = Some(root.join("run-moved/data"));
    serve_request.queries.truncate(1);
    serve_request.queries[0].arguments = vec![vec!["2000-01-04".into()]];
    let served = serving::serve_workload(&serve_request, &root.join("serve"), &worker).unwrap();
    records::write_new_json(&root.join("served-copy.json"), &served).unwrap();
    assert_eq!(served["status"], "executed", "{served}");
}

/// The declarations of the constrained fixture, in identity order (keys before the foreign key that references one).
fn declared_constraints() -> IntegrityConstraints {
    serde_json::from_value(json!({"trust":"user_declared","declarations":[
        {"table":"site","sql":"PRIMARY KEY (region)"},
        {"table":"sensor","sql":"PRIMARY KEY (id)"},
        {"table":"sensor","sql":"FOREIGN KEY (site) REFERENCES site (region)"},
        {"table":"sensor","sql":"CONSTRAINT sensor_day_from_2000 CHECK (day >= DATE '2000-01-01')"}]}))
    .unwrap()
}

/// The written fixture rows satisfy [`declared_constraints`]: read back from the two Parquet files (9 rows), keys
/// distinct, every sensor's site a site region, every day on or after 2000-01-01 (Date32 10957). No column is NULL.
fn assert_declarations_hold(dataset: &DatasetSpec) {
    use arrow::array::{Array, AsArray};
    use arrow::datatypes::{Date32Type, Int32Type};
    let read = |table: usize| {
        let file = fs::File::open(&dataset.tables[table].locations[0]).unwrap();
        let batches: Vec<RecordBatch> = parquet::arrow::arrow_reader::ParquetRecordBatchReaderBuilder::try_new(file).unwrap().build().unwrap().map(Result::unwrap).collect();
        arrow::compute::concat_batches(&batches[0].schema(), &batches).unwrap()
    };
    let (site, sensor) = (read(0), read(1));
    let ints = |batch: &RecordBatch, column: &str| -> Vec<i32> {
        let array = batch.column_by_name(column).unwrap().as_primitive::<Int32Type>();
        assert_eq!(array.null_count(), 0);
        array.values().to_vec()
    };
    let distinct = |values: &[i32]| values.iter().collect::<std::collections::BTreeSet<_>>().len() == values.len();
    let (regions, ids, sites) = (ints(&site, "region"), ints(&sensor, "id"), ints(&sensor, "site"));
    assert!(distinct(&regions) && distinct(&ids), "PRIMARY KEYs: {regions:?} {ids:?}");
    assert!(sites.iter().all(|s| regions.contains(s)), "FOREIGN KEY: {sites:?} in {regions:?}");
    let days = sensor.column_by_name("day").unwrap().as_primitive::<Date32Type>();
    assert!(days.null_count() == 0 && days.values().iter().all(|d| *d >= 10957), "CHECK: {days:?}");
    assert_eq!((site.num_rows(), sensor.num_rows()), (2, 7));
}

/// The paths of the files named `name` under `dir`.
fn files_named(dir: &Path, name: &str) -> Vec<PathBuf> {
    let mut found = vec![];
    for entry in fs::read_dir(dir).unwrap().map(Result::unwrap) {
        let path = entry.path();
        if entry.file_type().unwrap().is_dir() {
            found.extend(files_named(&path, name));
        } else if entry.file_name() == name {
            found.push(path);
        }
    }
    found
}

/// The public route under declared integrity constraints (one `run_workload`, scripted fixture replays, no LLM): the
/// statement check proves the declarations well formed (entry v5, `lemma_declared_schema`); only tiny cases the verified
/// evaluator certifies are kept, at least one with rows, the others counted by reason; both authors receive the
/// declarations; the workload storage opts in and is admitted under the storage entry v2 with exactly this list; the
/// query is admitted under the entry v5 over it. Serving a new binding with the same declarations takes that package
/// (`package: assumed`) and returns the exact rows; the same statement without declarations finds no package, and its
/// catalog lists the storage as not applicable.
#[tokio::test]
#[ignore = "runs the pinned Verus toolchain, frontend and the gendb worker; set GENDB_WORKER; -- --ignored"]
async fn public_controller_serves_declared_constraints_only_to_their_requests() {
    use crate::storage::catalog;
    use gendb_artifacts::ObjectStore;
    use gendb_artifacts::verus::{VERUS_ENTRY_V5_IDENTITY, VERUS_STORAGE_ENTRY_V2_IDENTITY};
    use gendb_frontend::parser::SqlParser;
    use gendb_runtime::serve::{AdmittedPackage, DeclaredConstraints, admitted_package};
    use gendb_storage::import::PreparedSource;
    use gendb_storage::versions::CurrentCapture;
    use gendb_verification::admission::prepare_statement;

    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let root = scratch_root("t5-declared-constraints-fixture");
    let dataset = dataset(&root.join("data-files"));
    assert_declarations_hold(&dataset);
    let mut request = request(&root, dataset.clone());
    request.queries.remove(0); // the correctness query over [2000-01-01, 2029-12-31]
    request.hardware = Hardware { threads: vec![1] };
    request.integrity_constraints = Some(declared_constraints());
    fs::create_dir_all(root.join("locks")).unwrap();
    let run = root.join("run");
    let authors = WorkloadAuthors { storage: Some(FixtureReplayAuthor { script: Script::DeclaredStorage }), queries: vec![FixtureReplayAuthor { script: Script::DeclaredQuery }] };
    let summary = run_workload(&request, &run, authors, &worker).await.unwrap();
    records::write_new_json(&root.join("summary-copy.json"), &summary).unwrap();
    assert_eq!(summary["status"], "closed", "{summary}");

    // The constrained statement (key with gendb_constraints.rs) and the same statement without declarations.
    let parser = SqlParser::from_environment().unwrap();
    let query = &request.queries[0];
    let prepare = |constraints: Option<&IntegrityConstraints>, dir: &str| {
        prepare_statement(&parser, &dataset, constraints, &query.sql, &query.parameters, &[], &[], &root.join(dir)).unwrap()
    };
    let declared = prepare(request.integrity_constraints.as_ref(), "statement-declared");
    let default = prepare(None, "statement-default");
    let digest = declared.key_v4.constraints_digest().expect("the constrained key carries its module");
    assert!(default.key_v4.constraints.is_none() && default.key_id != declared.key_id);

    // Preflight: the v5 statement check verified gendb_constraints.rs; certified cases only, at least one with rows.
    let preflight: Value = records::read_json(&run.join("queries/query-0000/verus-preflight/preflight.json")).unwrap();
    let check = &preflight["framework_check"];
    assert_eq!((check["entry_identity"].as_str(), check["outcome"].as_str(), preflight["constraints_assumed"].as_bool()),
        (Some(VERUS_ENTRY_V5_IDENTITY), Some("verified"), Some(true)), "{preflight}");
    assert!(check["files"].as_array().unwrap().iter().any(|f| f == "gendb_constraints.rs"), "{check}");
    let certification = &preflight["tiny_cases"]["certification"];
    assert!(certification["certified_with_rows"].as_u64().unwrap() > 0 && preflight["warnings"] == json!([]), "{preflight}");
    let skipped: u64 = certification["skipped"].as_object().unwrap().values().map(|n| n.as_u64().unwrap()).sum();
    assert_eq!(certification["generated"].as_u64().unwrap(), certification["certified"].as_u64().unwrap() + skipped, "{certification}");
    println!("tiny-case certification: {certification}");

    // Both authors received the declarations and the entries of the declared mode.
    let storage_author = run.join("workload-storage/session/author");
    let query_author = run.join("queries/query-0000/author");
    for (author, files) in [(&storage_author, ["integrity-constraints.json", "storage_entry_v2.rs"]), (&query_author, ["integrity-constraints.json", "query_entry.rs"])] {
        for file in files {
            assert!(!files_named(author, file).is_empty(), "{file} in {}", author.display());
        }
    }
    let fixed_entry = files_named(&query_author, "query_entry.rs").into_iter().find(|p| p.parent().is_some_and(|d| d.ends_with("fixed"))).expect("the fixed query entry");
    let query_entry = fs::read_to_string(fixed_entry).unwrap();
    assert!(query_entry.contains(VERUS_ENTRY_V5_IDENTITY) && query_entry.contains("constraints_hold(declared_db(db))"), "the query author's fixed entry is v5");

    // The workload storage: tools checked and built it (tiny builds over certified cases); admitted under entry v2
    // with exactly this declaration list.
    let storage = &summary["workload_storage"];
    assert_eq!(storage["resolution"]["status"], "storages_admitted", "{storage}");
    let storage_jobs: Value = records::read_json(&run.join("workload-storage/session/calls/0001/fixture-jobs.json")).unwrap();
    for action in ["storage_check", "storage_build"] {
        assert_eq!(job(&storage_jobs, action)["status"], "completed", "{action}: {storage_jobs}");
    }
    let store = ObjectStore::open_existing(&request.library).unwrap();
    let storage_id: gendb_artifacts::ContentId = serde_json::from_value(storage["resolution"]["storages"][0]["package"].clone()).unwrap();
    let (storage_package, _) = catalog::admitted_storage(&store, storage_id).unwrap();
    assert_eq!((storage_package.entry_identity.as_str(), storage_package.assumed_constraints), (VERUS_STORAGE_ENTRY_V2_IDENTITY, Some(digest)));

    // The query: admitted under entry v5 over that storage, found by the constrained key only.
    assert_eq!(summary["queries"][0]["resolution"]["status"], "verified_package_served", "{summary}");
    let Some(AdmittedPackage::StoredDataV4 { resolved, constraints, .. }) = admitted_package(&store, &declared.instance).unwrap() else { panic!("no v4 package for the declared statement") };
    assert_eq!((resolved.package.entry_identity.as_str(), constraints), (VERUS_ENTRY_V5_IDENTITY, DeclaredConstraints::Assumed { digest }));
    assert_eq!(resolved.package.storage_uses.iter().map(|u| u.package).collect::<Vec<_>>(), vec![storage_id]);
    assert!(admitted_package(&store, &default.instance).unwrap().is_none(), "no package serves the statement without declarations");

    // The catalog of the same capture: the v2 storage applies to the declared list, not to a run without declarations.
    let capture = CurrentCapture::of(&PreparedSource::open(&run.join("data"), &dataset).unwrap()).unwrap();
    let applicability = |tables| catalog::admitted_storages(&store, &capture, tables).unwrap().into_iter().find(|s| s.package_id == storage_id).unwrap().applicability;
    assert_eq!(applicability(&declared.instance.doc.tables), Ok(()));
    let refused = applicability(&default.instance.doc.tables).unwrap_err();
    assert!(refused.contains("storage_assumes_declared_constraints"), "{refused}");

    // Serving a new binding from the library, with the synthesis run directory moved away: the declaring request takes
    // the constrained package and its exact rows (days before 2000-01-04: sensors 100..102); the request without
    // declarations is refused (no package).
    fs::rename(&run, root.join("run-moved")).unwrap();
    let mut serve_request = request.clone();
    serve_request.prepared_workload = Some(root.join("run-moved/data"));
    serve_request.queries[0].arguments = vec![vec!["2000-01-04".into()]];
    let served = serving::serve_workload(&serve_request, &root.join("serve-declared"), &worker).unwrap();
    records::write_new_json(&root.join("served-declared-copy.json"), &served).unwrap();
    let cell = &served["queries"][0];
    assert_eq!((served["status"].as_str(), cell["integrity_constraints"]["package"].as_str(), cell["integrity_constraints"]["constraints_digest"].as_str()),
        (Some("executed"), Some("assumed"), Some(digest.to_hex().as_str())), "{served}");
    assert_eq!(cell["answer"], json!({"status":"ok","rows":[[100,"-2.00"],[101,"-0.75"],[102,"0.50"]]}), "{served}");
    serve_request.integrity_constraints = None;
    let refused = serving::serve_workload(&serve_request, &root.join("serve-default"), &worker).unwrap();
    records::write_new_json(&root.join("served-default-copy.json"), &refused).unwrap();
    assert_eq!(refused["status"], "unsupported", "{refused}");
    assert!(refused["queries"][0]["reason"].as_str().unwrap().starts_with("no admitted Verus package"), "{refused}");
}

/// Mid-session capture extension over the same tiny dataset (no Verus, no author): a storage that stores a column the
/// run's capture lacks extends it into a fresh root by exactly that column; the base table keeps its row-order
/// identity and source version (asset keys over it are unchanged); a second session sharing the capture sees the
/// extension without importing again; a resumed controller reopens the newest root (`data-current.json`) without
/// preparing again, and serving opens that root.
#[test]
fn capture_extension_imports_only_missing_columns_and_is_reopened_by_resume_and_serving() {
    use crate::storage::capture::{CaptureSetting, SharedCapture, current_data_root};
    use gendb_storage::import::{ColumnDemand, PreparationMethod, PreparationRequest, PreparedSource, prepare_source};
    use gendb_storage::versions::CurrentCapture;
    use gendb_verification::obligations::{DeclaredColumn, DeclaredSource, DeclaredTable, DeclaredType};

    let root = scratch_root("s4c-capture-extension");
    let dataset = dataset(&root.join("data-files"));
    let run = root.join("run");
    fs::create_dir_all(&run).unwrap();
    let run = run.canonicalize().unwrap();
    let registry = root.join("library.prepared-workloads");
    let mut demand = ColumnDemand::default();
    demand.add_columns(&dataset, "sensor", &[0, 3]).unwrap();
    let prepare = |root: &Path| prepare_source(&PreparationRequest { dataset: &dataset, demand: &demand, base: None, registry: &registry, root }).unwrap();
    let (base, _) = prepare(&run.join("data"));
    let before = CurrentCapture::of(&base).unwrap();
    let capture = SharedCapture::new(CaptureSetting { dataset: dataset.clone(), registry: registry.clone(), run_root: run.clone() }, Arc::new(base));
    let other_session = capture.clone();

    let column = |ordinal: usize, name: &str, ty: DeclaredType| DeclaredColumn { ordinal, name: name.into(), ty, row_count_only: false, nullable: false };
    let declaration = DeclaredSource {
        tables: vec![DeclaredTable {
            table_id: 1,
            name: "sensor".into(),
            columns: vec![column(0, "id", DeclaredType::Int4), column(2, "reading", DeclaredType::Numeric { precision: 10, scale: 2 }), column(3, "day", DeclaredType::Date)],
        }],
    };
    let (extended, record) = capture.covering(&declaration).unwrap();
    let record = record.expect("reading is not captured: the capture is extended");
    records::write_new_json(&root.join("extension-copy.json"), &record).unwrap();
    assert_eq!(record["added_columns"], json!([["sensor", [2]]]), "{record}");
    assert_eq!(record["preparation"]["imported_columns"], json!([["sensor", 2]]), "only the missing column is read: {record}");
    let after = CurrentCapture::of(&extended).unwrap();
    let (was, now) = (before.table("sensor").unwrap(), after.table("sensor").unwrap());
    assert_eq!((&now.row_order, &now.source_version, now.rows), (&was.row_order, &was.source_version, was.rows), "asset keys over sensor are unchanged");

    let (seen, again) = other_session.covering(&declaration).unwrap();
    assert!(again.is_none(), "the sharing session imports nothing");
    assert_eq!(seen.root(), extended.root());

    let current = current_data_root(&run).unwrap().expect("the run points at its newest root");
    assert_eq!(current.canonicalize().unwrap(), extended.root());
    let (resumed, report) = prepare(&current);
    assert_eq!(report.method, PreparationMethod::Resumed);
    assert!(resumed.coverage().iter().any(|(table, ordinals)| table == "sensor" && ordinals.contains(&2)));
    let served = PreparedSource::open(&current, &dataset).unwrap();
    assert_eq!(CurrentCapture::of(&served).unwrap().table("sensor").unwrap().row_order, was.row_order);
}
