//! The schema-engine framework on tiny TPC-H data: the render of a round's first-call inputs and a scripted replay of
//! rounds and versions . FRAMEWORK TEST ONLY: no provider, no LLM, no SF100 data; the engine
//! is a test fixture (materialize every table, run the verified interpreter), never admitted outside this test's
//! own scratch library and never shown to authors.
//!
//! The fixture:
//! - the SF100 dataset's tables and column types with the 15 TPC-H integrity constraints, over one PostgreSQL-checked
//!   tiny FK-closed database (`sqlspec/tests/fixtures/pg_reference/tpch_all22_cases/q04.json`) written as Parquet;
//! - the fixed flat storage of every table prepared once into a fresh library (`gendb prepare-flat-storage`: verified
//!   whole, assets linked from the capture) and listed as eligible under `physical_only` (they hold each column once);
//! - the saved answers of the training templates at their visible bindings, computed by the verified SQLSpec reference
//!   evaluator on the same database (cached under the scratch root by the bound statement's echo).
//!
//! Its fixture helpers (the dataset, the Parquet writer, saved values, training entries, the worker) are shared with the
//! general line's trial (`engine::general_trial`).
//!
//! Tests (run with `-- --ignored`; `TMPDIR` a scratch directory; `GENDB_WORKER` the `gendb` executable built with
//! this test binary; `GENDB_FIXTURE_ENGINE` the fixture engine's `agent/mod.rs`, which is not part of this repository;
//! the pinned Verus and frontend; under the build lock):
//! - [`render_round_one_inputs`]: the 22 TPC-H templates with their visible bindings, the saved SF100 baselines and
//!   every frozen variant; the first call of round 1 rendered without a provider (`rounds::render_engine_inputs`); the
//!   rendered files are copied to `GENDB_RENDER_REVIEW_DIR` when it is set.
//! - [`scripted_rounds_keep_versions_and_restart_from_the_latest`]: templates Q01, Q04 and Q06 with their variants and
//!   baselines far below any time (the stop never holds). Round 1 submits the fixture engine (accepted as v1); round 2
//!   starts from v1 and its notes and submits again (v2); round 3 submits a crate with a `static` item (refused at
//!   freeze: an attempt); round 4 starts from v2, not from round 3's workspace, and ends without a submission; the rounds
//!   guard then stops the run. A second run with baselines far above any time accepts v1, meets the stop and times the
//!   other visible bindings. Since the evaluator rule applies to engines the fixture engine
//!   is refused at freeze (it calls `exec_ordered`), so this test's accepted-version path needs a fixture engine that
//!   does not reference the whole-statement evaluator before it can pass again.
//! - [`paused_rounds_resume_on_relaunch`]: `engine.pause_after_round`. Template Q06; round 1 submits the fixture engine
//!   (refused at freeze by the whole-statement evaluator rule: an attempt) and the run pauses for review; a relaunch of
//!   the same request runs round 2 (from round 1's workspace) and pauses again; a relaunch with the pause switched off
//!   (not part of the run's identity) runs round 3 and stops at the rounds guard.

use super::rounds::{self, EngineState, SeedKind, run_engine};
use crate::controller::author::{AuthorCall, AuthorTransport, CandidateSubmission, Capability};
use crate::controller::ledger::{Receipt, Tokens};
use crate::controller::limits::Money;
use crate::controller::records;
use crate::controller::request::WorkloadRequest;
use crate::controller::workload_run::flat_preparation::prepare_flat_storage;
use arrow::array::{ArrayRef, Date32Array, Decimal128Array, Int64Array, RecordBatch, StringArray};
use arrow::datatypes::{DataType, Field, Schema};
use gendb_artifacts::{ColType, ContentId};
use gendb_frontend::ast::{AstDocument, Translation};
use gendb_frontend::engine_encode::encode_binding;
use gendb_frontend::params::ParamRequest;
use gendb_frontend::parser::SqlParser;
use gendb_sqlspec::codec::{HostTables, HostValue, RunOutcome};
use gendb_sqlspec::evaluator::{EvaluatorLibrary, echo_text};
use gendb_sqlspec::fixtures::{Fixture, fixtures_dir};
use gendb_storage::import::DatasetSpec;
use gendb_verification::admission::{IntegrityConstraints, dataset_ddl};
use gendb_verification::reference::{BuildOptions, BuildStatus, build_evaluator};
use gendb_verification::verus::VerusToolchain;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// The SF100 dataset's tables and column types (the request of the completed SF100 runs), without locations.
pub(super) const TPCH_DATASET: &str = r#"{"tables": [
  {"name": "lineitem", "format": "Parquet", "locations": [], "fields": [
    {"name": "l_orderkey", "ty": "I64", "nullable": false}, {"name": "l_partkey", "ty": "I64", "nullable": false},
    {"name": "l_suppkey", "ty": "I64", "nullable": false}, {"name": "l_linenumber", "ty": "I64", "nullable": false},
    {"name": "l_quantity", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "l_extendedprice", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "l_discount", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "l_tax", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "l_returnflag", "ty": "Utf8", "nullable": false}, {"name": "l_linestatus", "ty": "Utf8", "nullable": false},
    {"name": "l_shipdate", "ty": "Date32", "nullable": false}, {"name": "l_commitdate", "ty": "Date32", "nullable": false},
    {"name": "l_receiptdate", "ty": "Date32", "nullable": false}, {"name": "l_shipinstruct", "ty": "Utf8", "nullable": false},
    {"name": "l_shipmode", "ty": "Utf8", "nullable": false}, {"name": "l_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "orders", "format": "Parquet", "locations": [], "fields": [
    {"name": "o_orderkey", "ty": "I64", "nullable": false}, {"name": "o_custkey", "ty": "I64", "nullable": false},
    {"name": "o_orderstatus", "ty": "Utf8", "nullable": false}, {"name": "o_totalprice", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "o_orderdate", "ty": "Date32", "nullable": false}, {"name": "o_orderpriority", "ty": "Utf8", "nullable": false},
    {"name": "o_clerk", "ty": "Utf8", "nullable": false}, {"name": "o_shippriority", "ty": "I64", "nullable": false},
    {"name": "o_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "customer", "format": "Parquet", "locations": [], "fields": [
    {"name": "c_custkey", "ty": "I64", "nullable": false}, {"name": "c_name", "ty": "Utf8", "nullable": false},
    {"name": "c_address", "ty": "Utf8", "nullable": false}, {"name": "c_nationkey", "ty": "I64", "nullable": false},
    {"name": "c_phone", "ty": "Utf8", "nullable": false}, {"name": "c_acctbal", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "c_mktsegment", "ty": "Utf8", "nullable": false}, {"name": "c_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "part", "format": "Parquet", "locations": [], "fields": [
    {"name": "p_partkey", "ty": "I64", "nullable": false}, {"name": "p_name", "ty": "Utf8", "nullable": false},
    {"name": "p_mfgr", "ty": "Utf8", "nullable": false}, {"name": "p_brand", "ty": "Utf8", "nullable": false},
    {"name": "p_type", "ty": "Utf8", "nullable": false}, {"name": "p_size", "ty": "I64", "nullable": false},
    {"name": "p_container", "ty": "Utf8", "nullable": false}, {"name": "p_retailprice", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "p_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "partsupp", "format": "Parquet", "locations": [], "fields": [
    {"name": "ps_partkey", "ty": "I64", "nullable": false}, {"name": "ps_suppkey", "ty": "I64", "nullable": false},
    {"name": "ps_availqty", "ty": "I64", "nullable": false}, {"name": "ps_supplycost", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "ps_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "supplier", "format": "Parquet", "locations": [], "fields": [
    {"name": "s_suppkey", "ty": "I64", "nullable": false}, {"name": "s_name", "ty": "Utf8", "nullable": false},
    {"name": "s_address", "ty": "Utf8", "nullable": false}, {"name": "s_nationkey", "ty": "I64", "nullable": false},
    {"name": "s_phone", "ty": "Utf8", "nullable": false}, {"name": "s_acctbal", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "s_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "nation", "format": "Parquet", "locations": [], "fields": [
    {"name": "n_nationkey", "ty": "I64", "nullable": false}, {"name": "n_name", "ty": "Utf8", "nullable": false},
    {"name": "n_regionkey", "ty": "I64", "nullable": false}, {"name": "n_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "region", "format": "Parquet", "locations": [], "fields": [
    {"name": "r_regionkey", "ty": "I64", "nullable": false}, {"name": "r_name", "ty": "Utf8", "nullable": false},
    {"name": "r_comment", "ty": "Utf8", "nullable": false}]}
]}"#;

/// The tiny database of every fixture run.
const CASE: &str = "pg_reference/tpch_all22_cases/q04.json";
/// The training templates of the replay.
const REPLAY_TEMPLATES: [&str; 3] = ["Q01", "Q04", "Q06"];

pub(super) fn repository() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).ancestors().nth(3).expect("<repository>/src/gendb/synthesis").to_path_buf()
}

/// The scratch directory (`TMPDIR`).
fn scratch() -> PathBuf {
    PathBuf::from(std::env::var_os("TMPDIR").expect("TMPDIR must name a scratch directory"))
}

pub(super) fn worker() -> PathBuf {
    PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable built with this test binary"))
}

pub(super) fn tpch_constraints() -> IntegrityConstraints {
    serde_json::from_str(&fs::read_to_string(repository().join("src/gendb/fixtures/tpch/integrity-constraints.json")).unwrap()).unwrap()
}

/// The prepared fixture: its dataset (Parquet), the tiny database, the flat library and capture, the schema's DDL.
struct TinyTpch {
    root: PathBuf,
    dataset: DatasetSpec,
    tables: HostTables,
    library: PathBuf,
    capture: PathBuf,
    /// The flat storage packages `(name, package)` in table order.
    flat: Vec<(String, ContentId)>,
    ddl: PathBuf,
    parser: SqlParser,
}

impl TinyTpch {
    /// Write the tiny database as Parquet, translate the schema and prepare the flat storages into a fresh library.
    fn prepare(root: &Path) -> TinyTpch {
        fs::create_dir_all(root.join("data")).unwrap();
        fs::create_dir_all(root.join("locks")).unwrap();
        let mut dataset: DatasetSpec = serde_json::from_str(TPCH_DATASET).unwrap();
        for table in &mut dataset.tables {
            table.locations = vec![root.join("data").join(format!("{}.parquet", table.name))];
        }
        let (ddl_text, omitted) = dataset_ddl(&dataset, Some(&tpch_constraints()));
        assert!(omitted.is_empty(), "{omitted:?}");
        let ddl = root.join("schema.sql");
        fs::write(&ddl, ddl_text).unwrap();
        let parser = SqlParser::from_environment().unwrap();
        let probe = root.join("probe.sql");
        fs::write(&probe, "SELECT r_regionkey FROM region").unwrap();
        let (_, translation) = parser.translate(&ddl, &probe, "postgres", &[]).unwrap();
        let Translation::Ok(doc) = translation else { panic!("schema probe refused: {translation:?}") };
        let tables = Fixture::load(&fixtures_dir().join(CASE)).unwrap().database_for(&doc).unwrap();
        for (spec, rows) in dataset.tables.iter().zip(&tables) {
            write_parquet(&spec.locations[0], &spec.fields, rows);
        }
        let library = root.join("library");
        let request = json!({"format_version":2,"dataset":dataset,"queries":[{"name":"schema","sql":"SELECT r_regionkey FROM region",
                "limits":{"max_iterations":1,"max_cost_usd":"1","spend_policy":"estimated_usd","max_retries_per_iteration":1,"author_timeout_seconds":60}}],
            "hardware":{"threads":[1,2]},"max_concurrent_queries":1,"author_executable":"fixture","library":library,
            "barriers":{"activity_lock":root.join("locks/activity.lock"),"build_lock":root.join("locks/build.lock"),"race_lock":root.join("locks/race.lock")},
            "storage_policy":{"kind":"fixed_flat"},"integrity_constraints":tpch_constraints(),
            "validation":{"kind":"formal_proofs","numeric_relative_tolerance":"1e-9","required_engines":[],"saved_answers":[]}});
        let request_path = root.join("flat-request.json");
        fs::write(&request_path, serde_json::to_vec_pretty(&request).unwrap()).unwrap();
        let record = prepare_flat_storage(&request_path, &root.join("flat-run")).unwrap();
        let mut flat: Vec<(String, ContentId)> = record["tables"]
            .as_array()
            .unwrap()
            .iter()
            .map(|t| (t["storage"].as_str().unwrap().to_string(), serde_json::from_value(t["package"].clone()).unwrap()))
            .collect();
        let order: Vec<String> = dataset.tables.iter().map(|t| format!("flat_{}", t.name)).collect();
        flat.sort_by_key(|(name, _)| order.iter().position(|o| o == name));
        TinyTpch { root: root.to_path_buf(), dataset, tables, library, capture: root.join("flat-run/data"), flat, ddl, parser }
    }

    /// The template's document (parameters still placeholders).
    fn template_doc(&self, sql_file: &Path, parameters: &[ParamRequest]) -> AstDocument {
        let placeholders: Vec<_> = parameters.iter().map(ParamRequest::placeholder).collect();
        let (_, translation) = self.parser.translate(&self.ddl, sql_file, "postgres", &placeholders).unwrap();
        let Translation::Ok(doc) = translation else { panic!("{}: refused: {translation:?}", sql_file.display()) };
        doc
    }

    /// The saved answers of `templates` (from the training `templates.json` entries) at every visible binding: the
    /// verified reference evaluator's rows on the tiny database, cached by the bound statement's echo.
    fn saved_answers(&self, templates: &[(String, Value)], visible: &Value) -> Vec<Value> {
        let toolchain = VerusToolchain::from_env().unwrap();
        let cache = scratch().join("replay-cache/answers");
        fs::create_dir_all(&cache).unwrap();
        let mut sources = vec![];
        for (name, entry) in templates {
            let parameters: Vec<ParamRequest> = serde_json::from_value(entry["parameters"].clone()).unwrap();
            let doc = self.template_doc(Path::new(entry["sql"].as_str().unwrap()), &parameters);
            for binding in visible["queries"][name].as_array().unwrap() {
                let id = binding["binding_id"].as_str().unwrap();
                let arguments: Vec<String> = binding["arguments"].as_array().unwrap().iter().map(|a| a.as_str().unwrap().to_string()).collect();
                let bound = encode_binding(&doc, &arguments).unwrap().document;
                let echo = echo_text(&bound);
                let key: String = Sha256::digest(echo.as_bytes()).iter().take(8).map(|b| format!("{b:02x}")).collect();
                let file = cache.join(format!("{name}-{id}-{key}.json"));
                if !file.is_file() {
                    let out = scratch().join("replay-cache/evaluators").join(format!("{name}-{id}-{key}-{}", records::now_unix_ms()));
                    let build = build_evaluator(&toolchain, &bound, &out.join("ast.json"), &out.join("build"), &BuildOptions::default()).unwrap();
                    assert_eq!(build.status, BuildStatus::Ok, "{name} {id}: reference build {}", build.record);
                    let outcome = EvaluatorLibrary::load(build.library.as_ref().unwrap()).unwrap().run(&self.tables).unwrap();
                    let RunOutcome::Rows(rows) = outcome else { panic!("{name} {id}: the reference answered {outcome:?}") };
                    let rows: Vec<Value> = rows.iter().map(|row| Value::Array(row.iter().map(saved_value).collect())).collect();
                    fs::write(&file, serde_json::to_vec_pretty(&json!({"echo":echo,"rows":rows,"engine":"verified SQLSpec reference evaluator","database":CASE})).unwrap()).unwrap();
                }
                sources.push(json!({"query":name,"binding":id,"engine":"reference","description":"the verified SQLSpec reference evaluator on the tiny fixture database",
                    "path":file,"rows_pointer":"/rows"}));
            }
        }
        sources
    }

    /// An engine request over the flat library: `templates` of the training set (entries of `templates.json` with
    /// absolute SQL files), every frozen variant of them, baselines of `baseline_ms` at every cell, `rounds` rounds, and
    /// with `saved` the reference evaluator's saved answers.
    fn engine_request(&self, dir: &Path, templates: &[(String, Value)], baseline_ms: &str, rounds: u32, saved: bool) -> PathBuf {
        fs::create_dir_all(dir).unwrap();
        let repo = repository();
        let index: serde_json::Map<String, Value> = templates.iter().cloned().collect();
        fs::write(dir.join("templates.json"), json!({"templates":index}).to_string()).unwrap();
        let manifest: Value = serde_json::from_str(&fs::read_to_string(repo.join("src/gendb/fixtures/tpch/engine-variants/manifest.json")).unwrap()).unwrap();
        let variants: Vec<Value> = manifest["variants"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|v| index.contains_key(v["template"].as_str().unwrap()))
            .map(|v| {
                let mut v = v.clone();
                v["file"] = json!(repo.join("src/gendb/fixtures/tpch/engine-variants").join(v["file"].as_str().unwrap()));
                v
            })
            .collect();
        fs::write(dir.join("manifest.json"), json!({"variants":variants}).to_string()).unwrap();
        let visible: Value = serde_json::from_str(&fs::read_to_string(repo.join("output/tpch-sf100/bindings/visible.json")).unwrap()).unwrap();
        let mut targets = serde_json::Map::new();
        for (name, _) in templates {
            let cells: serde_json::Map<String, Value> = ["1", "2", "64"].iter().map(|w| (w.to_string(), serde_json::from_str::<Value>(
                &format!(r#"{{"duckdb_ms":{baseline_ms},"umbra_ms":{baseline_ms},"target_ms":{baseline_ms},"agreement":"exact-order"}}"#)).unwrap())).collect();
            let bindings: serde_json::Map<String, Value> = ["v0", "v1", "v2"].iter().map(|b| (b.to_string(), Value::Object(cells.clone()))).collect();
            targets.insert(name.clone(), Value::Object(bindings));
        }
        fs::write(dir.join("targets.json"), Value::Object(targets).to_string()).unwrap();
        let saved = if saved { self.saved_answers(templates, &visible) } else { vec![] };
        let request = json!({"format_version":2,"dataset":self.dataset,"queries":[],"hardware":{"threads":[1,2]},"max_concurrent_queries":1,
            "max_concurrent_preparations":4,"author_executable":"fixture","library":self.library,
            "barriers":{"activity_lock":self.root.join("locks/activity.lock"),"build_lock":self.root.join("locks/build.lock"),"race_lock":self.root.join("locks/race.lock")},
            "prepared_workload":self.capture,"data_allowance":{"live_bytes":1_000_000_000_000u64},"output_home":dir.join("home"),
            "storage_policy":{"kind":"physical_only","eligible_storages":self.flat.iter().map(|(_, p)| json!({"package":p,"review":"framework fixture: each flat storage holds its own table's columns once"})).collect::<Vec<_>>()},
            "integrity_constraints":tpch_constraints(),
            "validation":{"kind":"formal_proofs","numeric_relative_tolerance":"1e-9","required_engines":[],"saved_answers":saved},
            "engine":{"templates":dir.join("templates.json"),"bindings":repo.join("output/tpch-sf100/bindings/visible.json"),"timing_binding":"v0",
                "targets":dir.join("targets.json"),"variants":dir.join("manifest.json"),
                "storage_seed":{"source_library":self.library,"packages":self.flat.iter().map(|(_, p)| p).collect::<Vec<_>>()},
                "limits":{"max_iterations":rounds,"max_cost_usd":"10","spend_policy":"estimated_usd","max_retries_per_iteration":1,"author_timeout_seconds":3600}}});
        let path = dir.join("request.json");
        fs::write(&path, serde_json::to_vec_pretty(&request).unwrap()).unwrap();
        path
    }
}

/// One output value as a saved answer (`admission::validation::SavedValue`): integers as numbers, numerics as `{"dec"}`,
/// dates as `{"date"}`, text as strings.
pub(super) fn saved_value(value: &HostValue) -> Value {
    let text = gendb_sqlspec::pg_text::value_json(value).unwrap_or(Value::Null);
    match value {
        HostValue::Num { .. } => json!({"dec":text}),
        HostValue::Date(_) | HostValue::Ts(_) => json!({"date":text}),
        _ => text,
    }
}

/// Write `rows` (the fixture's host values) as one Parquet file of `fields`.
pub(super) fn write_parquet(path: &Path, fields: &[gendb_artifacts::ColumnSpec], rows: &[Vec<HostValue>]) {
    let mut schema_fields = vec![];
    let mut columns: Vec<ArrayRef> = vec![];
    for (k, field) in fields.iter().enumerate() {
        let values = rows.iter().map(|r| &r[k]);
        match field.ty {
            ColType::I64 => {
                schema_fields.push(Field::new(&field.name, DataType::Int64, false));
                columns.push(Arc::new(Int64Array::from(values.map(|v| match v { HostValue::Int(x) => *x, other => panic!("{}: {other:?}", field.name) }).collect::<Vec<_>>())));
            }
            ColType::Decimal { p, s } => {
                schema_fields.push(Field::new(&field.name, DataType::Decimal128(p, s), false));
                let coefficients: Vec<i128> = values
                    .map(|v| match v {
                        HostValue::Num { coeff, scale } => coeff * 10i128.pow((s as u32).checked_sub(*scale).expect("a scale above the column's")),
                        HostValue::Int(x) => i128::from(*x) * 10i128.pow(s as u32),
                        other => panic!("{}: {other:?}", field.name),
                    })
                    .collect();
                columns.push(Arc::new(Decimal128Array::from(coefficients).with_precision_and_scale(p, s).unwrap()));
            }
            ColType::Date32 => {
                schema_fields.push(Field::new(&field.name, DataType::Date32, false));
                columns.push(Arc::new(Date32Array::from(values.map(|v| match v { HostValue::Date(d) => d + 10957, other => panic!("{}: {other:?}", field.name) }).collect::<Vec<_>>())));
            }
            ColType::Utf8 => {
                schema_fields.push(Field::new(&field.name, DataType::Utf8, false));
                columns.push(Arc::new(StringArray::from(
                    values.map(|v| match v { HostValue::Text(b) => String::from_utf8(b.clone()).unwrap(), other => panic!("{}: {other:?}", field.name) }).collect::<Vec<_>>(),
                )));
            }
            other => panic!("{}: unsupported fixture type {other:?}", field.name),
        }
    }
    let batch = RecordBatch::try_new(Arc::new(Schema::new(schema_fields)), columns).unwrap();
    let mut writer = parquet::arrow::ArrowWriter::try_new(fs::File::create(path).unwrap(), batch.schema(), None).unwrap();
    writer.write(&batch).unwrap();
    writer.close().unwrap();
}

/// The repository's `templates.json` entries of `names`, with absolute SQL files.
pub(super) fn training_entries(names: &[&str]) -> Vec<(String, Value)> {
    let dir = repository().join("src/gendb/fixtures/tpch/templates");
    let index: Value = serde_json::from_str(&fs::read_to_string(dir.join("templates.json")).unwrap()).unwrap();
    index["templates"]
        .as_object()
        .unwrap()
        .iter()
        .filter(|(name, _)| names.is_empty() || names.contains(&name.as_str()))
        .map(|(name, entry)| {
            let mut entry = entry.clone();
            entry["sql"] = json!(dir.join(entry["sql"].as_str().unwrap()));
            (name.clone(), entry)
        })
        .collect()
}

/// The fixture engine (`GENDB_FIXTURE_ENGINE`, an `agent/mod.rs` generated for the flat storages of the SF100 dataset
/// types; not part of this repository).
fn fixture_agent() -> String {
    let path = std::env::var_os("GENDB_FIXTURE_ENGINE").expect("GENDB_FIXTURE_ENGINE: the fixture engine's agent/mod.rs");
    fs::read_to_string(path).expect("the fixture engine")
}

/// What a scripted round does.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Script {
    /// Write the fixture engine and notes, submit.
    SubmitFixture,
    /// Record the seed, append to the notes, submit the same engine.
    ResubmitFromVersion,
    /// Write a crate with a `static` item and submit (refused at freeze).
    SubmitStatic,
    /// Record the seed and end without a submission.
    NoSubmission,
}

/// A scripted engine author: per round a [`Script`]; every call records what it saw in its workspace
/// (`replay-observation.json` in the call directory) and saves its prompt (`prompt.md`).
struct ReplayAuthor {
    script: Script,
    agent: String,
}

impl ReplayAuthor {
    fn observe(&self, workspace: &Path) -> Value {
        let read = |p: &str| fs::read_to_string(workspace.join(p)).ok();
        let versions: Vec<String> =
            fs::read_dir(workspace.join("versions")).into_iter().flatten().flatten().map(|e| e.file_name().to_string_lossy().into_owned()).collect();
        let read_only = fs::metadata(workspace.join("versions/v001/code/agent/mod.rs")).map(|m| m.permissions().readonly()).ok();
        json!({"agent_is_fixture":read("engine/src/agent/mod.rs").as_deref() == Some(self.agent.as_str()),"notes":read("NOTES.md"),"versions":versions,
            "v001_read_only":read_only,"engine_map":read("ENGINE_MAP.md").map(|m| m.lines().count()),"manifest":read("verus-engine.json").is_some(),
            "broken_file":workspace.join("engine/src/agent/state.rs").exists()})
    }

    /// Act on the workspace; `Some` is the manifest submitted.
    fn act(&self, workspace: &Path) -> Option<&'static str> {
        let agent = workspace.join("engine/src/agent");
        match self.script {
            Script::SubmitFixture => {
                fs::create_dir_all(&agent).unwrap();
                fs::write(agent.join("mod.rs"), &self.agent).unwrap();
                fs::write(workspace.join("NOTES.md"), "# Notes\nround 1: the fixture engine (materialize + interpreter).\n").unwrap();
                Some("verus-engine.json")
            }
            Script::ResubmitFromVersion => {
                let notes = fs::read_to_string(workspace.join("NOTES.md")).unwrap_or_default();
                fs::write(workspace.join("NOTES.md"), format!("{notes}round 2: resubmitted from v1.\n")).unwrap();
                Some("verus-engine.json")
            }
            Script::SubmitStatic => {
                fs::write(agent.join("state.rs"), "use vstd::prelude::*;\nverus! {\npub static CALLS: u64 = 0;\n}\n").unwrap();
                let mut manifest: Value = serde_json::from_str(&fs::read_to_string(workspace.join("verus-engine.json")).unwrap()).unwrap();
                manifest["modules"].as_array_mut().unwrap().push(json!({"file":"state.rs","role":"helper","items":[]}));
                fs::write(workspace.join("verus-engine.json"), manifest.to_string()).unwrap();
                fs::write(workspace.join("NOTES.md"), "round 3: a static counter (refused).\n").unwrap();
                Some("verus-engine.json")
            }
            Script::NoSubmission => None,
        }
    }
}

impl AuthorTransport for ReplayAuthor {
    fn capability(&self) -> Capability {
        Capability {
            transport: "scripted-replay".into(),
            executable: "none".into(),
            version: "1".into(),
            model: "none (scripted test author; no provider)".into(),
            effort: "none".into(),
            persistent_sessions: true,
            hard_usd_cap: false,
            cost_semantics: "fixture: 0.01 per call".into(),
        }
    }

    fn invoke(&mut self, request: &AuthorCall) -> Receipt {
        fs::create_dir_all(request.call_dir).unwrap();
        fs::write(request.call_dir.join("prompt.md"), request.prompt).unwrap();
        fs::write(request.call_dir.join("replay-observation.json"), self.observe(request.workspace).to_string()).unwrap();
        let manifest = self.act(request.workspace);
        Receipt {
            call_id: request.call.id,
            session_id: request.session_id.into(),
            ended_unix_ms: records::now_unix_ms(),
            elapsed_ms: 1,
            reported_cost_usd: Some(Money::parse("0.01").unwrap()),
            billed_cost_usd: None,
            tokens: Some(Tokens::default()),
            outcome: if manifest.is_some() { "success".into() } else { "error: scripted round ends without a submission".into() },
            raw_result: Some(json!({"session_id":request.session_id,"scripted":true})),
            output: manifest.map(|m| json!(CandidateSubmission { candidate_manifest: m.into(), rationale: "scripted replay".into(), data_access_analysis: "fixture engine".into() })),
            usage_scope: None,
        }
    }
}

/// The observation of round `round`'s first call.
fn observation(engine_dir: &Path, round: u32) -> Value {
    let path = rounds::round_directory(engine_dir, round).join("calls/0001/replay-observation.json");
    serde_json::from_str(&fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))).unwrap()
}

#[test]
#[ignore = "runs the pinned frontend and Verus (flat storages, the templates' statement checks); TMPDIR a scratch directory; -- --ignored"]
fn render_round_one_inputs() {
    let root = crate::controller::test_support::scratch_root("engine-render");
    let tiny = TinyTpch::prepare(&root.join("fixture"));
    let repo = repository();
    // The real training set: every template, the SF100 baselines, every frozen variant; no saved answer is needed to render.
    let dir = root.join("training");
    fs::create_dir_all(&dir).unwrap();
    let request_path = {
        let path = tiny.engine_request(&dir, &training_entries(&["Q06"]), "1", 1, false);
        let mut request: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        request["engine"]["templates"] = json!(repo.join("src/gendb/fixtures/tpch/templates/templates.json"));
        request["engine"]["targets"] = json!(repo.join("output/tpch-sf100/baselines/targets.json"));
        request["engine"]["variants"] = json!(repo.join("src/gendb/fixtures/tpch/engine-variants/manifest.json"));
        request["hardware"]["threads"] = json!([1, 32, 64]);
        request.as_object_mut().unwrap().remove("output_home");
        fs::write(&path, serde_json::to_vec_pretty(&request).unwrap()).unwrap();
        path
    };
    let out = root.join("render");
    let runtime = tokio::runtime::Runtime::new().unwrap();
    let record = runtime.block_on(rounds::render_engine_inputs(&request_path, &out, None, &worker())).unwrap();
    assert_eq!(record["rendered_call"], true, "{record}");
    let prompt = fs::read_to_string(out.join("rendered/prompt.md")).unwrap();
    for heading in ["# Task", "# Goal", "# Generality rules", "# Storage: seeded, with a budget", "# Rounds and versions", "## Totals against the targets (binding v0)", "## Training set at binding v0"] {
        assert!(prompt.contains(heading), "{heading}");
    }
    assert!(prompt.contains("| Q09 |") && prompt.contains("| 1 | 165848.718 | 375456.388 | 165848.718 (umbra) |") && prompt.contains("No version yet"), "the real templates and SF100 baselines");
    // The operator reviews the rendered inputs here.
    let Some(review) = std::env::var_os("GENDB_RENDER_REVIEW_DIR").map(PathBuf::from) else { return };
    if review.exists() {
        fs::remove_dir_all(&review).unwrap();
    }
    super::role::copy_tree(&out.join("rendered"), &review, false).unwrap();
    fs::write(review.join("render.json"), serde_json::to_vec_pretty(&record).unwrap()).unwrap();
    eprintln!("rendered: {}", review.display());
}

#[test]
#[ignore = "runs the pinned frontend, Verus and the gendb worker on tiny data; set GENDB_WORKER and TMPDIR; -- --ignored. Fails at round 1 since the whole-statement evaluator rule applies to engines (the fixture engine calls exec_ordered): needs an admissible fixture engine"]
fn scripted_rounds_keep_versions_and_restart_from_the_latest() {
    let root = crate::controller::test_support::scratch_root("engine-replay");
    let tiny = TinyTpch::prepare(&root.join("fixture"));
    let agent = fixture_agent();
    let training = training_entries(&REPLAY_TEMPLATES);
    let runtime = tokio::runtime::Runtime::new().unwrap();

    // Run A: baselines of 1 us (never beaten): four scripted rounds, then the rounds guard.
    let request_a = WorkloadRequest::read(&tiny.engine_request(&root.join("run-a-inputs"), &training, "0.001", 4, true)).unwrap();
    let scripts = [Script::SubmitFixture, Script::ResubmitFromVersion, Script::SubmitStatic, Script::NoSubmission];
    let authors = |round: u32, _: &Path| -> Result<ReplayAuthor, String> { Ok(ReplayAuthor { script: scripts[round as usize - 1], agent: agent.clone() }) };
    let run_a = root.join("run-a");
    let summary = runtime.block_on(run_engine(&request_a, &run_a, authors, &worker())).unwrap();
    eprintln!("run A: {}", serde_json::to_string_pretty(&summary).unwrap());
    assert_eq!((summary["status"].as_str(), summary["reason"].as_str()), (Some("stopped"), Some("round_limit")), "{summary}");
    let engine_dir = rounds::engine_directory(&run_a.canonicalize().unwrap());
    let state = EngineState::read(&engine_dir).unwrap();
    let outcomes: Vec<&str> = state.rounds.iter().map(|r| r["outcome"].as_str().unwrap()).collect();
    assert_eq!(outcomes, ["version", "version", "attempt", "attempt"], "{:?}", state.rounds);
    assert_eq!(state.versions.iter().map(|v| (v["version"].as_str().unwrap(), v["round"].as_u64().unwrap())).collect::<Vec<_>>(), [("v1", 1), ("v2", 2)]);
    assert!(state.rounds[2]["error"].as_str().unwrap().contains("static"), "round 3 is refused for its static item: {}", state.rounds[2]);
    assert_eq!(state.rounds[3]["reason"], "retry_limit", "round 4 ends without a submission");
    // Seeds: round 2 from v1 with its notes; round 4 from v2 (not round 3's workspace), with v2's notes.
    let seed = |round: u32| -> rounds::RoundRecord { records::read_json(&rounds::round_directory(&engine_dir, round).join("round.json")).unwrap() };
    assert_eq!((seed(1).seed.kind, seed(2).seed.kind, seed(3).seed.kind, seed(4).seed.kind), (SeedKind::Empty, SeedKind::Version, SeedKind::Version, SeedKind::Version));
    assert_eq!((seed(2).seed.version.as_deref(), seed(4).seed.version.as_deref()), (Some("v1"), Some("v2")));
    assert!(seed(1).request.limits.max_iterations == 1 && seed(4).request.limits.max_iterations == 1, "one submission per round");
    let round_two = observation(&engine_dir, 2);
    assert_eq!(round_two["agent_is_fixture"], true, "{round_two}");
    assert!(round_two["notes"].as_str().unwrap().contains("round 1:") && round_two["versions"] == json!(["v001"]) && round_two["v001_read_only"] == true, "{round_two}");
    let round_four = observation(&engine_dir, 4);
    assert_eq!((round_four["agent_is_fixture"].as_bool(), round_four["broken_file"].as_bool()), (Some(true), Some(false)), "{round_four}");
    assert!(round_four["notes"].as_str().unwrap().contains("round 2: resubmitted from v1."), "{round_four}");
    let mut seen_versions: Vec<&str> = round_four["versions"].as_array().unwrap().iter().map(|v| v.as_str().unwrap()).collect();
    seen_versions.sort();
    assert_eq!(seen_versions, ["v001", "v002"]);
    // Every version folder is complete.
    for number in [1, 2] {
        let dir = rounds::version_directory(&engine_dir, number);
        for file in ["version.json", "README.md", "code/agent/mod.rs", "code-view/agent/mod.rs.md", "manifest.json", "seed-manifest.json", "NOTES.md", "admission.json",
            "evaluation.json", "timing.json", "totals.json", "official-matrix.json", "qualification-cells.json", "variant-matrix.json", "variant-ratios.json", "variants.md", "receipts.json"]
        {
            assert!(dir.join(file).is_file(), "{} lacks {file}", dir.display());
        }
        let version: Value = records::read_json(&dir.join("version.json")).unwrap();
        assert_eq!(version["totals"]["workers"].as_array().unwrap().len(), 2, "{version}");
        assert!(version["totals"]["templates"].as_array().unwrap().iter().all(|t| t["engine"]["checked"] == true), "every official cell agreed with its saved answers");
        assert_eq!(version["stop"]["stop"], false);
        assert_eq!(version["admission"]["admitted"], true, "{}", version["admission"]);
    }
    assert!(root.join("run-a-inputs/home/engine/versions/v002/README.md").is_file() && root.join("run-a-inputs/home/engine/README.md").is_file(), "the output home");
    // The round 2 prompt leads its facts with v1's totals and carries v1's notes.
    let prompt = fs::read_to_string(rounds::round_directory(&engine_dir, 2).join("calls/0001/prompt.md")).unwrap();
    assert!(prompt.contains("## Totals against the targets (binding v0)") && prompt.contains("v1 total") && prompt.contains("round 1: the fixture engine"), "round 2 prompt");

    // Run B: baselines of 1e9 ms (always beaten): v1 meets the stop, and its other bindings are timed.
    let request_b = WorkloadRequest::read(&tiny.engine_request(&root.join("run-b-inputs"), &training, "1000000000", 3, true)).unwrap();
    let authors = |_: u32, _: &Path| -> Result<ReplayAuthor, String> { Ok(ReplayAuthor { script: Script::SubmitFixture, agent: agent.clone() }) };
    let run_b = root.join("run-b");
    let summary = runtime.block_on(run_engine(&request_b, &run_b, authors, &worker())).unwrap();
    eprintln!("run B: {}", serde_json::to_string_pretty(&summary).unwrap());
    assert_eq!((summary["status"].as_str(), summary["reason"].as_str()), (Some("stopped"), Some("target_met")), "{summary}");
    let state = EngineState::read(&rounds::engine_directory(&run_b.canonicalize().unwrap())).unwrap();
    assert_eq!(state.rounds.len(), 1);
    let v1 = &state.versions[0];
    assert_eq!(v1["stop"]["stop"], true);
    let other: Vec<&str> = v1["other_bindings"].as_array().unwrap().iter().map(|o| o["binding"].as_str().unwrap()).collect();
    assert_eq!(other, ["v1", "v2"], "the stopping version is timed at the other visible bindings");
    let evidence = json!({"run_a":run_a,"run_b":run_b,"fixture":root.join("fixture"),"versions_a":EngineState::read(&engine_dir).unwrap().versions,"run_b_v1":v1});
    fs::write(root.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", root.join("evidence.json").display());
}

#[test]
#[ignore = "runs the pinned frontend and Verus (flat storages, one template's statement check) on tiny data; set GENDB_WORKER and TMPDIR; -- --ignored"]
fn paused_rounds_resume_on_relaunch() {
    let root = crate::controller::test_support::scratch_root("engine-pause");
    let tiny = TinyTpch::prepare(&root.join("fixture"));
    let agent = fixture_agent();
    let path = tiny.engine_request(&root.join("inputs"), &training_entries(&["Q06"]), "0.001", 3, false);
    let set_pause = |pause: bool| {
        let mut request: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        request["engine"]["pause_after_round"] = json!(pause);
        fs::write(&path, serde_json::to_vec_pretty(&request).unwrap()).unwrap();
        WorkloadRequest::read(&path).unwrap()
    };
    let runtime = tokio::runtime::Runtime::new().unwrap();
    let run = root.join("run");
    let launch = |request: &WorkloadRequest, script: Script| {
        let authors = |_: u32, _: &Path| -> Result<ReplayAuthor, String> { Ok(ReplayAuthor { script, agent: agent.clone() }) };
        let summary = runtime.block_on(run_engine(request, &run, authors, &worker())).unwrap();
        eprintln!("summary: {}", serde_json::to_string_pretty(&summary).unwrap());
        summary
    };

    // Launch 1: round 1 submits the fixture engine; the whole-statement evaluator rule refuses it at freeze; the run pauses.
    let first = launch(&set_pause(true), Script::SubmitFixture);
    assert_eq!((first["status"].as_str(), first["reason"].as_str()), (Some(rounds::PAUSED), Some(rounds::PAUSED_FOR_REVIEW)), "{first}");
    assert_eq!((first["pause"]["paused_after_round"].as_u64(), first["pause"]["next_round"].as_u64()), (Some(1), Some(2)), "{first}");
    let engine_dir = rounds::engine_directory(&run.canonicalize().unwrap());
    let state = EngineState::read(&engine_dir).unwrap();
    assert_eq!(state.rounds.len(), 1);
    assert_eq!(state.rounds[0]["outcome"], "attempt");
    let error = state.rounds[0]["error"].as_str().unwrap_or_default();
    assert!(error.contains("whole_statement_evaluator") && error.contains("relational::entry"), "round 1 is refused by the evaluator rule: {}", state.rounds[0]);

    // Launch 2: the same request resumes with round 2 (from round 1's workspace: no version yet) and pauses again.
    let second = launch(&set_pause(true), Script::NoSubmission);
    assert_eq!((second["status"].as_str(), second["pause"]["paused_after_round"].as_u64()), (Some(rounds::PAUSED), Some(2)), "{second}");
    let seed: rounds::RoundRecord = records::read_json(&rounds::round_directory(&engine_dir, 2).join("round.json")).unwrap();
    assert_eq!(seed.seed.kind, SeedKind::PreviousRound);

    // Launch 3: the pause switched off (not part of the run's identity): round 3 runs, then the rounds guard stops the run.
    let third = launch(&set_pause(false), Script::NoSubmission);
    assert_eq!((third["status"].as_str(), third["reason"].as_str()), (Some("stopped"), Some("round_limit")), "{third}");
    assert!(third.get("pause").is_none());
    let state = EngineState::read(&engine_dir).unwrap();
    assert_eq!(state.rounds.iter().map(|r| r["outcome"].as_str().unwrap()).collect::<Vec<_>>(), ["attempt", "attempt", "attempt"]);
    let summaries: Vec<String> = fs::read_dir(run.canonicalize().unwrap()).unwrap().flatten().map(|e| e.file_name().to_string_lossy().into_owned()).filter(|n| n.starts_with("summary")).collect();
    let evidence = json!({"run":run,"launches":[first, second, third],"summaries":summaries,"rounds":state.rounds});
    fs::write(root.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", root.join("evidence.json").display());
}
