//! Reuse of a completed preflight by a later run (`queries[].preflight_from`), over the public fixture's tiny dataset
//! and its query 0 (a date template with two benchmark bindings), through the public `preflight` route:
//! 1. run 1: preflight without targets (the stage before baselines);
//! 2. run 2: a new run whose request adds targets and an early stop and names run 1's statement directory: ready,
//!    with no Verus statement check, evaluator build or reference-mode directory of its own, the same exact
//!    reference rows at every admission binding, and `reused_from` in its preflight record;
//! 3. runs 3–5: a changed benchmark argument, a changed SQL text and a rewritten source table are each refused before
//!    any author call, naming the identity field that differs.
//!
//! Needs the pinned frontend Python and the pinned Verus; run with `-- --ignored`. No candidate is run.

use super::public_fixture::{dataset, request};
use super::*;
use crate::controller::request::{QueryObjective, QueryRequest};
use crate::controller::test_support::scratch_root;
use std::fs;

fn write_request(root: &Path, name: &str, request: &WorkloadRequest) -> PathBuf {
    let path = root.join(format!("{name}.json"));
    records::write_new_json(&path, request).unwrap();
    path
}

fn statement_directory(run: &Path) -> PathBuf {
    query_directory(run, 0).join(preparation::STATEMENT_DIRECTORY)
}

#[tokio::test]
#[ignore = "runs the pinned Verus toolchain and frontend; -- --ignored"]
async fn a_later_run_loads_a_completed_preflight_and_refuses_changed_evidence() {
    let root = scratch_root("preflight-reuse");
    let data_files = root.join("data-files");
    let fixture = request(&root, dataset(&data_files));
    let targeted = fixture.queries[0].clone();
    let QueryObjective::ExecutionTime { bindings, .. } = &targeted.objective else { panic!("fixture query 0 is timed") };
    let untargeted = QueryRequest { objective: QueryObjective::ExecutionTime { bindings: bindings.clone(), targets: vec![], early_stop: None }, ..targeted.clone() };
    let one = |query: QueryRequest| WorkloadRequest { queries: vec![query], workload_storage: None, ..fixture.clone() };
    let worker = Path::new("unused-worker");
    let run = |name: &str| root.join(name);

    let first = preflight(&write_request(&root, "request-1", &one(untargeted)), &run("run-1"), worker).await.unwrap();
    assert_eq!(first["queries"][0]["status"], "ready", "{first}");
    let evidence = statement_directory(&run("run-1"));
    assert!(evidence.join("preflight-evidence.json").is_file() && evidence.join("framework-check").is_dir());

    let from = |query: QueryRequest| QueryRequest { preflight_from: Some(evidence.clone()), ..query };
    let second = preflight(&write_request(&root, "request-2", &one(from(targeted.clone()))), &run("run-2"), worker).await.unwrap();
    assert_eq!(second["queries"][0]["status"], "ready", "{second}");
    let reused = statement_directory(&run("run-2"));
    for fresh_only in ["framework-check", "reference", "oracle"] {
        assert!(!reused.join(fresh_only).exists(), "run 2 created {fresh_only}/: no Verus check or evaluator build may run");
    }
    assert_eq!(second["queries"][0]["references"], first["queries"][0]["references"]);
    let bindings = first["queries"][0]["references"].as_array().unwrap();
    assert!(bindings.len() > 2 && bindings.iter().all(|b| b["reference"] == "exact"), "{first}");
    for binding in bindings {
        let rows = format!("prepared-reference-{}.rows", binding["binding"].as_str().unwrap());
        assert_eq!(fs::read(reused.join(&rows)).unwrap(), fs::read(evidence.join(&rows)).unwrap(), "{rows}");
    }
    let record: Value = records::read_json(&reused.join("preflight.json")).unwrap();
    assert_eq!(record["reused_from"]["directory"], json!(evidence));
    let first_record: Value = records::read_json(&evidence.join("preflight.json")).unwrap();
    assert_eq!(record["framework_check"], first_record["framework_check"], "the check shown is run 1's");
    assert!(reused.join("preflight-evidence.json").is_file() && reused.join("tiny-cases.json").is_file());
    eprintln!("preflight_ns: run 1 {} (fresh), run 2 {} (reused)", first_record["preflight_ns"], record["preflight_ns"]);

    let refused = |summary: &Value, field: &str| {
        let query = &summary["queries"][0];
        assert_eq!(query["status"], "unsupported_capability", "{summary}");
        let error = query["error"].as_str().unwrap();
        assert!(error.contains("preflight_reuse_refused") && error.contains(field), "{field}: {error}");
    };
    let mut other_binding = json!(from(targeted.clone()));
    other_binding["objective"]["bindings"][0]["arguments"][0] = json!("2000-01-04");
    let third = preflight(&write_request(&root, "request-3", &one(serde_json::from_value(other_binding).unwrap())), &run("run-3"), worker).await.unwrap();
    refused(&third, "identity.statement.record.admission_bindings");
    let other_sql = QueryRequest { sql: targeted.sql.replace("day < $1", "day <= $1"), ..from(targeted.clone()) };
    let fourth = preflight(&write_request(&root, "request-4", &one(other_sql)), &run("run-4"), worker).await.unwrap();
    refused(&fourth, "identity.statement.record");
    dataset(&data_files);
    let fifth = preflight(&write_request(&root, "request-5", &one(from(targeted))), &run("run-5"), worker).await.unwrap();
    refused(&fifth, "identity.data");
    for refused_run in ["run-3", "run-4", "run-5"] {
        assert!(!statement_directory(&run(refused_run)).join("framework-check").exists());
    }
}
