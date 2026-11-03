//! In-process checks of the worker's input delivery and request rules. Nothing here loads a library (see
//! `tests/worker_process.rs` for the child process). Scratch lives under a scratch `TMPDIR`, never `/tmp`.

use super::inputs::retained_columns;
use super::*;
use crate::abi::StatementArgument;
use arrow::array::{ArrayRef, Decimal128Array, Int64Array, StringArray};
use arrow::datatypes::{Field, Schema};
use arrow::record_batch::RecordBatch;
use gendb_artifacts::{ColType, ColumnSpec};
use gendb_storage::io::{
    NATIVE_TYPE_I32, NATIVE_TYPE_I64, NATIVE_TYPE_I128, NATIVE_TYPE_UTF8, ProjectedTable, SourceColumns,
};
use std::path::{Path, PathBuf};
use std::sync::Arc;

fn scratch(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let path = std::env::temp_dir().join(format!("gendb-runtime-worker-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

fn table(name: &str, fields: Vec<(usize, ColumnSpec, ArrayRef)>) -> ProjectedTable {
    let rows = fields[0].2.len();
    let schema = Arc::new(Schema::new(
        fields
            .iter()
            .map(|(_, spec, array)| Field::new(&spec.name, array.data_type().clone(), spec.nullable))
            .collect::<Vec<_>>(),
    ));
    let batch = RecordBatch::try_new(schema, fields.iter().map(|(_, _, array)| array.clone()).collect()).unwrap();
    ProjectedTable {
        table: name.into(),
        original_indices: fields.iter().map(|(ordinal, _, _)| *ordinal).collect(),
        fields: fields.into_iter().map(|(_, spec, _)| spec).collect(),
        batches: vec![batch],
        row_count: rows,
    }
}

fn spec(name: &str, ty: ColType) -> ColumnSpec {
    ColumnSpec { name: name.into(), ty, nullable: false }
}

/// The multi-table build input: two source tables with different row counts, projected from one prepared archive
/// (mapped column files) in the requested table order, each to its own ordinals; every column keeps its table's row
/// count. A table named twice is refused.
#[test]
fn tables_input_projects_every_table_with_its_own_row_count() {
    let root = scratch("tables");
    let orders = table(
        "orders",
        vec![
            (0, spec("o_key", ColType::I64), Arc::new(Int64Array::from(vec![1, 2, 3])) as ArrayRef),
            (2, spec("o_flag", ColType::Utf8), Arc::new(StringArray::from(vec!["a", "\u{e9}t\u{e9}", ""])) as ArrayRef),
        ],
    );
    let lines = table(
        "lines",
        vec![
            (0, spec("l_key", ColType::I64), Arc::new(Int64Array::from(vec![3, 3, 1, 9, 2])) as ArrayRef),
            (
                4,
                spec("l_price", ColType::Decimal { p: 15, s: 2 }),
                Arc::new(Decimal128Array::from(vec![100, -5, 7, 0, 12]).with_precision_and_scale(15, 2).unwrap())
                    as ArrayRef,
            ),
        ],
    );
    let archive = root.join("archive");
    let captured = SourceColumns::from_projected(vec![orders, lines]).unwrap();
    captured.write_archive(&archive).unwrap();
    captured.write_and_map_column_files(&archive).unwrap();
    let input = WorkerInput::Tables {
        path: archive.clone(),
        tables: vec![
            TableColumns { table: "lines".into(), ordinals: vec![0, 4] },
            TableColumns { table: "orders".into(), ordinals: vec![2] },
        ],
    };
    let columns = retained_columns(&input).unwrap();
    let shape: Vec<(i32, i64)> = columns.iter().map(|c| (c.type_tag, c.len)).collect();
    assert_eq!(shape, [(NATIVE_TYPE_I64, 5), (NATIVE_TYPE_I128, 5), (NATIVE_TYPE_UTF8, 3)]);
    // SAFETY: the columns are retained for the rest of this test process.
    let keys = unsafe { std::slice::from_raw_parts(columns[0].values.cast::<i64>(), 5) };
    assert_eq!(keys, [3, 3, 1, 9, 2]);
    let offsets = unsafe { std::slice::from_raw_parts(columns[2].offsets, 4) };
    let bytes = unsafe { std::slice::from_raw_parts(columns[2].bytes, offsets[3] as usize) };
    assert_eq!(&bytes[offsets[1] as usize..offsets[2] as usize], "\u{e9}t\u{e9}".as_bytes());
    let twice = WorkerInput::Tables {
        path: archive,
        tables: vec![
            TableColumns { table: "lines".into(), ordinals: vec![0] },
            TableColumns { table: "lines".into(), ordinals: vec![4] },
        ],
    };
    assert!(matches!(retained_columns(&twice), Err(WorkerError::Storage(_))));
}

/// Inline fixture columns: exact values in host order, Utf8 bytes with `len + 1` offsets from 0; a value outside its
/// element type is refused.
#[test]
fn inline_columns_are_exact() {
    let column = |elem, values: &[&str]| InlineColumn { elem, values: values.iter().map(|v| v.to_string()).collect(), validity: None };
    let input = WorkerInput::Inline {
        columns: vec![
            column(InlineElem::I32, &["-2147483648", "7"]),
            column(InlineElem::I128, &["-170141183460469231731687303715884105728"]),
            column(InlineElem::Utf8, &["ab", "", "\u{e9}"]),
        ],
    };
    let columns = retained_columns(&input).unwrap();
    let shape: Vec<(i32, i64)> = columns.iter().map(|c| (c.type_tag, c.len)).collect();
    assert_eq!(shape, [(NATIVE_TYPE_I32, 2), (NATIVE_TYPE_I128, 1), (NATIVE_TYPE_UTF8, 3)]);
    // SAFETY: the columns are retained for the rest of this test process.
    unsafe {
        assert_eq!(std::slice::from_raw_parts(columns[0].values.cast::<i32>(), 2), [i32::MIN, 7]);
        assert_eq!(*columns[1].values.cast::<i128>(), i128::MIN);
        assert_eq!(std::slice::from_raw_parts(columns[2].offsets, 4), [0, 2, 2, 4]);
        assert_eq!(std::slice::from_raw_parts(columns[2].bytes, 4), "ab\u{e9}".as_bytes());
    }
    for (elem, value) in [(InlineElem::I32, "2147483648"), (InlineElem::I64, "1.5")] {
        let input = WorkerInput::Inline { columns: vec![column(elem, &[value])] };
        assert!(matches!(retained_columns(&input), Err(WorkerError::Inline(_))), "{value}");
    }
}

/// The request rules, and the earlier version's JSON form of a v3 query request (only the build identity differs).
#[test]
fn request_rules_and_json_form() {
    let library = Path::new("library.so");
    let query = WorkerRequest::for_query(
        library,
        Some(Path::new("parts")),
        vec![vec![StatementArgument::Int(24)]],
        vec![1, 32],
        4,
        64,
    );
    assert_eq!(query.check_shape(), Ok(()));
    let build = WorkerRequest::for_build(library, WorkerInput::None, Path::new("out"), 64, 64);
    assert_eq!(build.check_shape(), Ok(()));
    let refusals = [
        WorkerRequest { workers: vec![], ..query.clone() },
        WorkerRequest { repetitions: 0, ..query.clone() },
        WorkerRequest { bindings: vec![], ..query.clone() },
        WorkerRequest { input: WorkerInput::Inline { columns: vec![] }, ..query.clone() },
        WorkerRequest { workers: vec![1, 2], ..build.clone() },
        WorkerRequest { repetitions: 2, ..build.clone() },
        WorkerRequest { bindings: vec![vec![]], ..build.clone() },
    ];
    for request in refusals {
        assert!(request.check_shape().is_err(), "{request:?}");
    }
    let saved_form = serde_json::json!({
        "abi": "v3", "build": {"runtime": crate::identity::runtime_build_identity()},
        "library": "library.so", "purpose": "candidate", "input": "none",
        "job": {"query": {"parts_directory": "parts"}}, "bindings": [[{"int": 24}]],
        "workers": [1, 32], "repetitions": 4, "range_capacity": 64
    });
    assert_eq!(serde_json::to_value(&query).unwrap(), saved_form);
    assert_eq!(serde_json::from_value::<WorkerRequest>(saved_form).unwrap(), query);
}

/// v4 requests: the job's ABI version must be the marker's, build/query rules as in v3, distinct storage-use names;
/// the serialized form (the record S3/S4 write) names every use in order and the explicit kernel advice.
#[test]
fn storage_request_rules_and_json_form() {
    use gendb_storage::io::{PartAccess, ReadAdvice};
    let library = Path::new("query.so");
    let use_of = |name: &str| StorageUseInput { name: name.into(), parts_directory: PathBuf::from(format!("assets/{name}")) };
    let access = PartAccess { read_advice: ReadAdvice::Random, drop_cached_pages: false };
    let query = WorkerRequest::for_storage_query(library, vec![use_of("lineitem_by_date")], access, vec![vec![]], vec![1], 2, 64);
    assert_eq!(query.check_shape(), Ok(()));
    let build = WorkerRequest::for_storage_build(Path::new("storage.so"), WorkerInput::None, Path::new("asset"), 8, 64);
    assert_eq!(build.check_shape(), Ok(()));
    let refusals = [
        WorkerRequest { abi: RequestAbi::V3, ..query.clone() },
        WorkerRequest { abi: RequestAbi::V4, ..WorkerRequest::for_query(library, None, vec![vec![]], vec![1], 1, 64) },
        WorkerRequest { job: WorkerJob::StorageQuery { storage_uses: vec![use_of("a"), use_of("a")], access }, ..query.clone() },
        WorkerRequest { job: WorkerJob::StorageQuery { storage_uses: vec![use_of("")], access }, ..query.clone() },
        WorkerRequest { bindings: vec![], ..query.clone() },
        WorkerRequest { input: WorkerInput::Inline { columns: vec![] }, ..query.clone() },
        WorkerRequest { workers: vec![1, 2], ..build.clone() },
        WorkerRequest { bindings: vec![vec![]], ..build.clone() },
    ];
    for request in refusals {
        assert!(request.check_shape().is_err(), "{request:?}");
    }
    let form = serde_json::json!({
        "abi": "v4", "build": {"runtime": crate::identity::runtime_build_identity()},
        "library": "query.so", "purpose": "candidate", "input": "none",
        "job": {"storage_query": {"storage_uses": [{"name": "lineitem_by_date", "parts_directory": "assets/lineitem_by_date"}],
            "access": {"read_advice": "random", "drop_cached_pages": false}}},
        "bindings": [[]], "workers": [1], "repetitions": 2, "range_capacity": 64
    });
    assert_eq!(serde_json::to_value(&query).unwrap(), form);
    assert_eq!(serde_json::from_value::<WorkerRequest>(form).unwrap(), query);
    assert_eq!(serde_json::to_value(&build).unwrap()["job"], serde_json::json!({"storage_build": {"output_directory": "asset"}}));
}

/// A child that refused a write at the storage reserve is recognized by its exit code and last stderr line only.
#[test]
fn storage_reserve_stop_is_the_refusal_as_last_line_with_exit_1() {
    let refusal = gendb_storage::io::StorageIoError::StorageReserve { path: "asset".into(), free: 5, reserve: 4, write: 2 }.to_string();
    let failure = |exit_code, stderr: &str| ChildFailure { exit_code, signal: None, stderr: stderr.into() };
    assert!(failure(Some(1), &format!("warning\n{refusal}\n")).stopped_at_storage_reserve());
    assert!(!failure(Some(1), &format!("{refusal}\nlater output")).stopped_at_storage_reserve());
    assert!(!failure(None, &refusal).stopped_at_storage_reserve(), "a signal is no refusal");
    assert!(!failure(Some(1), "asset/part-0001.bin: No space left on device (os error 28)").stopped_at_storage_reserve());
}

/// Limits and sampling: engine jobs only, positive values, absent from the JSON when unset (earlier requests keep
/// their form); [`CallLimits::GENERAL_ENGINE`] is 60 s and 144 GiB.
#[test]
fn engine_limits_and_sampling_rules_and_json_form() {
    use gendb_storage::io::PartAccess;
    let engine = WorkerRequest::for_engine_query(Path::new("engine.so"), vec![], PartAccess::default(), &[vec![1, 2]], vec![1], 4, 64);
    let plain = serde_json::to_value(&engine).unwrap();
    for field in ["call_limit_ns", "anon_memory_limit_bytes", "sampling"] {
        assert!(plain.get(field).is_none(), "{field} is absent when unset");
    }
    assert_eq!(CallLimits::GENERAL_ENGINE, CallLimits { call_limit_ns: 60_000_000_000, anon_memory_limit_bytes: 154_618_822_656 });
    let limited = engine.clone().with_call_limits(CallLimits::GENERAL_ENGINE).with_sampling(SamplingRequest { interval_us: 1000 });
    assert_eq!(limited.check_shape(), Ok(()));
    assert!(limited.is_limited() && !engine.is_limited());
    let form = serde_json::to_value(&limited).unwrap();
    assert_eq!((form["call_limit_ns"].as_u64(), form["anon_memory_limit_bytes"].as_u64()), (Some(60_000_000_000), Some(154_618_822_656)));
    assert_eq!(form["sampling"], serde_json::json!({"interval_us": 1000}));
    assert_eq!(serde_json::from_value::<WorkerRequest>(form).unwrap(), limited);
    let query = WorkerRequest::for_query(Path::new("q.so"), None, vec![vec![]], vec![1], 1, 64);
    let refusals = [
        WorkerRequest { call_limit_ns: Some(1), ..query.clone() },
        WorkerRequest { sampling: Some(SamplingRequest { interval_us: 1 }), ..query.clone() },
        WorkerRequest { call_limit_ns: Some(0), ..engine.clone() },
        WorkerRequest { anon_memory_limit_bytes: Some(0), ..engine.clone() },
        WorkerRequest { sampling: Some(SamplingRequest { interval_us: 0 }), ..engine.clone() },
    ];
    for request in refusals {
        assert!(request.check_shape().is_err(), "{request:?}");
    }
}

/// An `Ok` call returning `rows` (its exact wire, no usage).
fn ok_outcome(rows: &[Vec<gendb_sqlspec::codec::HostValue>]) -> crate::abi::CallOutcome {
    crate::abi::CallOutcome {
        status: crate::abi::CallStatus::Ok,
        sql_error: None,
        result_wire: Some(gendb_sqlspec::codec::encode_result_rows(rows)),
        parts_delivered: 0,
        dispatch: crate::abi::DispatchEvidence::default(),
        usage: crate::abi::CallUsage::default(),
        storage_requests: vec![],
    }
}

/// The child's observation of a call with a large answer (an author's own statement): under the answer bound it
/// holds the first 100 rows, the row count and the wire's SHA-256 and size, and no wire, so the observation the child
/// writes is small; without a bound (a compared cell) it holds every row and the exact wire, as before.
#[test]
fn the_childs_observation_stores_a_large_answer_bounded_only_under_a_bound() {
    use gendb_sqlspec::codec::HostValue;
    let rows: Vec<Vec<HostValue>> = (0..20_000).map(|i| vec![HostValue::Int(i), HostValue::Text(b"a text value".to_vec())]).collect();
    let outcome = ok_outcome(&rows);
    let wire_bytes = outcome.result_wire.as_ref().map(Vec::len).unwrap() as u64;
    let bounded = super::child::observed_query(0, 32, 1, outcome.clone(), None, Some(AnswerBound::STORED)).unwrap();
    let stored = bounded.stored_answer.as_ref().expect("over the bound");
    assert_eq!((stored.rows, stored.stored_rows, stored.wire_bytes, stored.wire_sha256.len()), (20_000, 100, wire_bytes, 64));
    assert_eq!(bounded.rows.as_ref().map(Vec::len), Some(100));
    assert!(bounded.outcome.result_wire.is_none());
    let written = serde_json::to_vec_pretty(&bounded).unwrap().len();
    let full = super::child::observed_query(0, 32, 1, outcome, None, None).unwrap();
    assert!(full.stored_answer.is_none() && full.rows.as_ref().map(Vec::len) == Some(20_000) && full.outcome.result_wire.is_some());
    let written_full = serde_json::to_vec_pretty(&full).unwrap().len();
    assert!(written < 20_000 && written_full > 1_000_000, "bounded {written} bytes, full {written_full} bytes");
}

/// The stored-answer bound belongs to engine jobs and is absent from the JSON when unset. The caller's bounded store
/// rewrites a result file with each answer over the bound cut to its summary and first rows (read back as a result, the
/// other fields unchanged), and leaves a result within the bound as the child wrote it.
#[test]
fn answer_bound_rules_and_the_callers_bounded_store() {
    use crate::answer::rows_json;
    use gendb_sqlspec::codec::HostValue;
    use gendb_storage::io::PartAccess;
    let engine = WorkerRequest::for_engine_query(Path::new("engine.so"), vec![], PartAccess::default(), &[vec![1]], vec![1], 2, 64);
    assert!(serde_json::to_value(&engine).unwrap().get("answer_bound").is_none(), "absent when unset");
    let bounded = engine.with_answer_bound(AnswerBound::STORED);
    assert_eq!(bounded.check_shape(), Ok(()));
    assert_eq!(serde_json::to_value(&bounded).unwrap()["answer_bound"], serde_json::json!({"rows": 100, "row_text_bytes": 1_048_576}));
    let query = WorkerRequest::for_query(Path::new("q.so"), None, vec![vec![]], vec![1], 1, 64);
    assert!(WorkerRequest { answer_bound: Some(AnswerBound::STORED), ..query }.check_shape().is_err(), "engine jobs only");

    let rows: Vec<Vec<HostValue>> = (0..250).map(|i| vec![HostValue::Int(i)]).collect();
    let observation = |repetition, rows: &[Vec<HostValue>]| CallObservation {
        binding: Some(0),
        workers: 1,
        repetition,
        outcome: ok_outcome(rows),
        rows: Some(rows_json(rows).unwrap()),
        sql_error: None,
        process_io: None,
        peak_anon_bytes: None,
        samples: None,
        stored_answer: None,
    };
    let result = WorkerResult {
        abi: RequestAbi::V4,
        purpose: RunPurpose::Candidate,
        library: "engine.so".into(),
        input_columns: 0,
        column_rows: vec![],
        bindings: vec![],
        observations: vec![observation(0, &rows), observation(1, &rows[..3])],
        parts: None,
        storage_uses: vec![],
        echoes: vec!["SELECT 1".into()],
        unfinished: None,
    };
    let work = scratch("bounded-store");
    let file = work.join("verus-run.result.json");
    std::fs::write(&file, serde_json::to_vec_pretty(&result).unwrap()).unwrap();
    assert_eq!(store_bounded_result(&work, &result, AnswerBound::STORED).unwrap(), 1);
    let stored: WorkerResult = serde_json::from_slice(&std::fs::read(&file).unwrap()).unwrap();
    let summary = stored.observations[0].stored_answer.as_ref().expect("cut");
    assert_eq!((summary.rows, summary.stored_rows, stored.observations[0].rows.as_ref().map(Vec::len)), (250, 100, Some(100)));
    assert!(stored.observations[0].outcome.result_wire.is_none());
    assert_eq!(stored.observations[1], result.observations[1], "an answer within the bound is kept in full");
    assert_eq!((stored.echoes, stored.abi, stored.library), (result.echoes.clone(), result.abi, result.library.clone()));
    let within = WorkerResult { observations: vec![observation(0, &rows[..3])], ..result };
    std::fs::write(&file, b"as the child wrote it").unwrap();
    assert_eq!(store_bounded_result(&work, &within, AnswerBound::STORED).unwrap(), 0);
    assert_eq!(std::fs::read(&file).unwrap(), b"as the child wrote it");
    assert!(!work.join("verus-run.result.json.bounded").exists());
    std::fs::remove_dir_all(&work).unwrap();
}

/// The unfinished record: its reason is the JSON tag, a stopped call carries its identity and measurements, and a
/// child failure carries the OS report; both read back unchanged.
#[test]
fn unfinished_results_read_back() {
    let stopped = Unfinished::OverTimeLimit(StoppedCall {
        statement: 1,
        workers: 4,
        repetition: 0,
        elapsed_ns: 1_000_100_000,
        limit: 1_000_000_000,
        anon_bytes: Some(1 << 20),
        peak_anon_bytes: Some(2 << 20),
        samples: None,
    });
    let json = serde_json::to_value(&stopped).unwrap();
    assert_eq!((json["reason"].as_str(), json["statement"].as_u64(), json["limit"].as_u64()), (Some("over_time_limit"), Some(1), Some(1_000_000_000)));
    assert_eq!(serde_json::from_value::<Unfinished>(json).unwrap(), stopped);
    let failed = Unfinished::ChildFailure(ChildFailure { exit_code: None, signal: Some(9), stderr: String::new() });
    let json = serde_json::to_value(&failed).unwrap();
    assert_eq!(json, serde_json::json!({"reason": "child_failure", "exit_code": null, "signal": 9, "stderr": ""}));
    assert_eq!(serde_json::from_value::<Unfinished>(json).unwrap(), failed);
    assert_eq!((stopped.reason(), failed.reason()), (UnfinishedReason::OverTimeLimit, UnfinishedReason::ChildFailure));
    assert!(stopped.stopped().is_some() && failed.stopped().is_none());
}

/// Serving never arms the sampler or a limit and never bounds an answer: the engine serving route builds its request
/// with `WorkerRequest::for_engine_query` only (no sampling, no limit, no answer bound), and no serving source names the
/// sampling, limit or answer-bound builders.
#[test]
fn serving_never_arms_the_sampler() {
    use gendb_storage::io::PartAccess;
    let request = WorkerRequest::for_engine_query(Path::new("engine.so"), vec![], PartAccess::default(), &[vec![0]], vec![1], 1, 64);
    assert!(request.sampling.is_none() && !request.is_limited() && request.answer_bound.is_none());
    let serving = [
        ("runtime/src/serve.rs", include_str!("../serve.rs")),
        ("runtime/src/serve/engine.rs", include_str!("../serve/engine.rs")),
        ("runtime/src/serve/executor.rs", include_str!("../serve/executor.rs")),
        ("runtime/src/serve/statement.rs", include_str!("../serve/statement.rs")),
        ("runtime/src/serve/asset.rs", include_str!("../serve/asset.rs")),
        ("synthesis/src/engine/serving.rs", include_str!("../../../synthesis/src/engine/serving.rs")),
    ];
    for (path, text) in serving {
        for word in ["with_sampling", "SamplingRequest", "sampling:", "with_call_limits", "call_limit_ns", "with_answer_bound", "answer_bound"] {
            assert!(!text.contains(word), "{path} names {word}");
        }
    }
    assert!(include_str!("../serve/engine.rs").contains("WorkerRequest::for_engine_query("), "the engine serving route builds its request here");
}
