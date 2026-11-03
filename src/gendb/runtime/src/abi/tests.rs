//! Scoped checks of the ABI host, plus one ignored check that loads saved Verus libraries
//! (`saved_libraries_round_trip`). Scratch lives under a scratch `TMPDIR`, never `/tmp`.

use super::*;
use gendb_storage::io::{
    NATIVE_TYPE_I32, NATIVE_TYPE_I64, NATIVE_TYPE_I128, NATIVE_TYPE_UTF8, NativeColumn, PartAccess, PartElem,
    PartFilesWriter, PartsFormat, ProjectedTable, SourceColumns,
};

/// Every status/error/wire combination: each SQL error code survives exactly (call record and wire must agree),
/// `Capacity` and `Ok` need their wires, statuses without result carry neither wire nor code.
#[test]
fn status_error_and_wire_agree() {
    let wire = |tail: &[u8]| [RESULT_MAGIC.as_slice(), tail].concat();
    let rows = wire(&[0, 0, 0, 0, 0, 0, 0, 0, 0]);
    for code in SQL_ERROR_CODES {
        assert_eq!(check_query_wire(CallStatus::SqlError, code as u32, Some(&wire(&[1, code]))).unwrap(), Some(code));
        let other = if code == 8 { 1 } else { code + 1 };
        assert!(check_query_wire(CallStatus::SqlError, code as u32, Some(&wire(&[1, other]))).is_err(), "codes differ");
        assert!(check_query_wire(CallStatus::Ok, code as u32, Some(&rows)).is_err(), "code without SqlError");
    }
    for bad in [0u32, 9, 256 + 1] {
        assert!(matches!(
            check_query_wire(CallStatus::SqlError, bad, Some(&wire(&[1, bad as u8]))),
            Err(AbiError::WireMismatch { status: CallStatus::SqlError, .. })
        ));
    }
    assert!(check_query_wire(CallStatus::SqlError, 1, None).is_err());
    assert_eq!(check_query_wire(CallStatus::Capacity, 0, Some(&wire(&[2]))).unwrap(), None);
    assert!(check_query_wire(CallStatus::Capacity, 0, Some(&wire(&[2, 0]))).is_err());
    assert!(check_query_wire(CallStatus::Capacity, 0, Some(&wire(&[1, 1]))).is_err());
    assert_eq!(check_query_wire(CallStatus::Ok, 0, Some(&rows)).unwrap(), None);
    assert!(check_query_wire(CallStatus::Ok, 0, None).is_err());
    assert!(check_query_wire(CallStatus::Ok, 0, Some(b"GSQLRS2\0\x00")).is_err(), "magic");
    for status in [CallStatus::ParamRefused, CallStatus::Refused, CallStatus::WorkerFailed, CallStatus::AbiRefused, CallStatus::InvalidInput] {
        assert_eq!(check_query_wire(status, 0, None).unwrap(), None);
        assert!(check_query_wire(status, 0, Some(&wire(&[2]))).is_err());
    }
    for (code, status) in CallStatus::CODES {
        assert_eq!(CallStatus::from_code(code).unwrap(), status);
    }
    assert!(matches!(CallStatus::from_code(8), Err(AbiError::UnknownStatus(8))));
}

/// Argument descriptors: the shim reads `kind` and the value fields (i128 split in two's complement halves); JSON
/// keeps i128 exact as text and matches the saved request form.
#[test]
fn arguments_encode_exactly() {
    let n = StatementArgument::Num(-12_345_678_901_234_567_890_123_456_789i128).descriptor();
    assert_eq!((n.kind, ((n.num_hi as u128) << 64 | n.num_lo as u128) as i128), (2, -12_345_678_901_234_567_890_123_456_789i128));
    let d = StatementArgument::Date { y: 1996, m: 2, d: 29 }.descriptor();
    assert_eq!((d.kind, d.y, d.m, d.d, d.int, d.num_lo), (3, 1996, 2, 29, 0, 0));
    assert_eq!((StatementArgument::Int(-7).descriptor().kind, StatementArgument::Int(-7).descriptor().int), (1, -7));
    let args = vec![StatementArgument::Num(i128::MIN), StatementArgument::Int(i64::MAX), StatementArgument::Date { y: 1992, m: 1, d: 1 }];
    let text = serde_json::to_string(&args).unwrap();
    assert!(text.contains(&format!("{{\"num\":\"{}\"}}", i128::MIN)), "{text}");
    assert_eq!(serde_json::from_str::<Vec<StatementArgument>>(&text).unwrap(), args);
    let saved = r#"[{"date":{"y":1994,"m":1,"d":1}},{"num":"6"},{"int":24}]"#;
    assert_eq!(
        serde_json::from_str::<Vec<StatementArgument>>(saved).unwrap(),
        [StatementArgument::Date { y: 1994, m: 1, d: 1 }, StatementArgument::Num(6), StatementArgument::Int(24)]
    );
}

/// The call outcome keeps the earlier version's JSON form (lowercase hex wire, snake_case status).
#[test]
fn outcome_json_is_unchanged() {
    let saved = r#"{"status":"ok","sql_error":null,"result_wire":"4753514c52533100000100000000000000010000000000000000","parts_delivered":0,"dispatch":{"spawned":0,"joined":0,"ranges":[],"ranges_reported":0},"usage":{"wall_ns":14694,"process_user_ns":8000,"process_system_ns":5000,"caller_cpu_ns":13000}}"#;
    let outcome: CallOutcome = serde_json::from_str(saved).unwrap();
    assert_eq!((outcome.status, outcome.result_wire.as_ref().unwrap().len()), (CallStatus::Ok, 26));
    assert_eq!(serde_json::to_string(&outcome).unwrap(), saved);
    let error = CallOutcome { status: CallStatus::SqlError, sql_error: Some(4), result_wire: Some(b"GSQLRS1\0\x01\x04".to_vec()), ..outcome };
    let text = serde_json::to_string(&error).unwrap();
    assert!(text.contains(r#""status":"sql_error","sql_error":4,"result_wire":"4753514c525331000104""#), "{text}");
    assert_eq!(serde_json::from_str::<CallOutcome>(&text).unwrap(), error);
    assert!(serde_json::from_str::<CallOutcome>(&saved.replace("4753", "475")).is_err(), "odd hex length");
}

/// The layout record is the one saved v3 libraries report (x86-64): any record change refuses every saved library.
#[test]
fn layout_record_is_pinned() {
    assert_eq!(expected_layout(), [3, 48, 24, 48, 56, 16, 16, 64, 16, 64]);
}

/// The v4 layout record (x86-64): version 4, the v3 records' sizes, storage use 16, v4 query inputs 40, v4 query
/// record 88 (v3 call record 64 + use count, counts reported, counter pointer).
#[test]
fn layout_v4_record_is_pinned() {
    assert_eq!(expected_layout_v4(), [4, 48, 24, 48, 56, 16, 40, 16, 16, 64, 88, 16, 64]);
    assert_eq!(REQUEST_COUNT_WORDS, 3);
    let missing = std::env::temp_dir().join(format!("gendb-abi-v4-missing-{}.so", std::process::id()));
    // SAFETY: the file does not exist, so no code is loaded.
    assert!(matches!(unsafe { StorageQueryLibrary::load(&missing) }, Err(AbiError::Open { .. })));
    assert!(matches!(unsafe { StorageBuildLibrary::load(&missing) }, Err(AbiError::Open { .. })));
}

/// Every trusted shim repeats the host's codes (it is copied into crates and cannot import them): v3, and both v4
/// kinds (shared v4 records plus the entry of the kind, which names only its own symbol).
#[test]
fn shim_constants_equal_host_codes() {
    fn check_codes(shim: &str, version: u64) {
        let declares = |name: &str, ty: &str, value: String| {
            let line = format!("const {name}: {ty} = {value};");
            assert!(shim.contains(&line), "shim lacks `{line}`");
        };
        declares("ABI_VERSION", "u64", version.to_string());
        declares("MAX_WORKERS", "u64", MAX_WORKERS.to_string());
        for (code, status) in CallStatus::CODES {
            let name = format!("STATUS_{}", serde_json::to_value(status).unwrap().as_str().unwrap().to_uppercase());
            declares(&name, "u32", code.to_string());
        }
        for elem in PartElem::ALL {
            let name = format!("PART_{}", serde_json::to_value(elem).unwrap().as_str().unwrap().to_uppercase());
            declares(&name, "u32", elem.code().to_string());
        }
        for (name, tag) in [("I32", NATIVE_TYPE_I32), ("I64", NATIVE_TYPE_I64), ("I128", NATIVE_TYPE_I128), ("UTF8", NATIVE_TYPE_UTF8)] {
            declares(&format!("NATIVE_TYPE_{name}"), "i32", tag.to_string());
        }
        for (name, argument) in [("INT", StatementArgument::Int(0)), ("NUM", StatementArgument::Num(0)), ("DATE", StatementArgument::Date { y: 0, m: 0, d: 0 })] {
            declares(&format!("ARGUMENT_{name}"), "u32", argument.descriptor().kind.to_string());
        }
    }
    let defines = |shim: &str, symbol: &str| shim.contains(&format!("fn {symbol}("));
    check_codes(GENDB_SHIM_SOURCE, ABI_VERSION);
    assert!(defines(GENDB_SHIM_SOURCE, LAYOUT_SYMBOL) && defines(GENDB_SHIM_SOURCE, QUERY_SYMBOL) && defines(GENDB_SHIM_SOURCE, BUILD_SYMBOL));
    assert!(GENDB_ABI_SOURCE.contains("ParamRefused"));
    for shim in [GENDB_STORAGE_SHIM_SOURCE, GENDB_QUERY_SHIM_V4_SOURCE] {
        check_codes(shim, ABI_V4_VERSION);
        assert!(shim.contains(&format!("const REQUEST_COUNT_WORDS: usize = {REQUEST_COUNT_WORDS};")));
        assert!(defines(shim, LAYOUT_V4_SYMBOL) && !defines(shim, QUERY_SYMBOL) && !defines(shim, BUILD_SYMBOL));
    }
    assert!(defines(GENDB_STORAGE_SHIM_SOURCE, STORAGE_BUILD_SYMBOL) && !defines(GENDB_STORAGE_SHIM_SOURCE, STORAGE_QUERY_SYMBOL));
    assert!(defines(GENDB_QUERY_SHIM_V4_SOURCE, STORAGE_QUERY_SYMBOL) && !defines(GENDB_QUERY_SHIM_V4_SOURCE, STORAGE_BUILD_SYMBOL));
    assert!(GENDB_STORAGE_SHIM_SOURCE.contains("crate::gendb_entry::abi_build_storage(&columns, workers)"));
    assert!(GENDB_QUERY_SHIM_V4_SOURCE.contains("crate::gendb_entry::abi_query(uses, &arguments, workers)"));
    // Text arguments exist only in v4 query crates: the query shim declares the kind, the shared v4 records, the
    // storage shim and the v3 shim do not (their texts are unchanged, so every admitted storage stays reusable).
    let text_kind = format!("const ARGUMENT_TEXT: u32 = {};", StatementArgument::Text(String::new()).descriptor().kind);
    assert!(GENDB_QUERY_SHIM_V4_SOURCE.contains(&text_kind));
    assert!(!GENDB_STORAGE_SHIM_SOURCE.contains("ARGUMENT_TEXT") && !GENDB_SHIM_SOURCE.contains("ARGUMENT_TEXT"));
    assert!(GENDB_ARGUMENTS_SOURCE.contains("Text(&'static [u8])") && !GENDB_ABI_SOURCE.contains("Text(&'static"));
}

/// A text argument's descriptor points at the argument's own bytes with their length (what the query shim turns into
/// `QueryArg::Text`): exact for the empty text, multi-byte UTF-8 and an embedded NUL (which the verified binder, not
/// the host, refuses); its JSON form is `{"text": ...}`.
#[test]
fn text_arguments_reach_the_shim_as_their_bytes() {
    for text in ["", "Brand#45", "MEDIUM POLISHED%", "%Customer%Complaints%", "\u{e9}t\u{e9} \u{65e5}\u{672c} \u{1F600}", "a\0b"] {
        let argument = StatementArgument::Text(text.to_string());
        let record = argument.descriptor();
        assert_eq!((record.kind, record.int, record.y, record.m, record.d), (4, 0, 0, 0, 0));
        let bytes = match record.num_hi {
            0 => &[][..],
            // SAFETY: the record points into `argument`, alive here, as the shim reads it during a call.
            len => unsafe { std::slice::from_raw_parts(record.num_lo as usize as *const u8, len as usize) },
        };
        assert_eq!(bytes, text.as_bytes());
        let json = serde_json::to_string(&argument).unwrap();
        assert_eq!(serde_json::from_str::<StatementArgument>(&json).unwrap(), argument, "{json}");
    }
    assert_eq!(serde_json::to_string(&StatementArgument::Text("x".into())).unwrap(), r#"{"text":"x"}"#);
}

/// Text arguments through real v4 query shims (run explicitly, tiny calls, no data): `GENDB_ABI_TEXT_PROBE=<new>,<saved>`
/// names two query libraries of one statement without free parameters over one storage use, compiled with the
/// current query shim and with the saved (pre-text) one. With an empty part list the verified entry refuses every
/// non-empty argument list in `bind_params`, before any author code or part read (`ParamRefused`), so the status shows
/// what each shim decoded: the current shim hands text arguments (empty, multi-byte, with a NUL) to the verified
/// binder like an integer; the saved shim refuses the unknown kind 4 before any verified code runs (`AbiRefused`).
#[test]
#[ignore = "needs GENDB_ABI_TEXT_PROBE=<current query library>,<saved query library>"]
fn text_arguments_cross_the_query_shim() {
    let paths = std::env::var("GENDB_ABI_TEXT_PROBE").expect("GENDB_ABI_TEXT_PROBE");
    let (current, saved) = paths.split_once(',').expect("two library paths");
    let status = |path: &str, argument: StatementArgument| {
        // SAFETY: the library path is the caller's; no part is passed, so no host memory beyond the argument is read.
        let library = unsafe { StorageQueryLibrary::load(std::path::Path::new(path)) }.unwrap();
        unsafe { library.call_query(&[&[]], &[argument], 1, 0) }.unwrap().status
    };
    for text in ["", "Brand#45", "\u{e9}t\u{e9} \u{1F600}", "a\0b"] {
        assert_eq!(status(current, StatementArgument::Text(text.into())), CallStatus::ParamRefused, "{text:?}");
        assert_eq!(status(saved, StatementArgument::Text(text.into())), CallStatus::AbiRefused, "{text:?}");
    }
    for library in [current, saved] {
        assert_eq!(status(library, StatementArgument::Int(24)), CallStatus::ParamRefused);
    }
}

#[test]
fn missing_library_is_an_open_error() {
    let path = std::env::temp_dir().join(format!("gendb-abi-missing-{}.so", std::process::id()));
    // SAFETY: the file does not exist, so no code is loaded.
    assert!(matches!(unsafe { VerusLibrary::load(&path) }, Err(AbiError::Open { .. })));
}

/// Saved-library check (run explicitly; tiny inputs only). `GENDB_ABI_SAVED_CHECK` names a JSON file:
/// `{"libraries": [{"name", "library", "cases": [case directory…], "parameter_refusals": optional directory,
///   "refused_binding": [argument…]}], "v2_library": path, "scratch": directory, "report": path}`.
/// A case directory is a saved tiny case (`build/`, `parts/`, `query/` with `verus-run.{request,result}.json`). For
/// every library:
/// - every case: the saved inline build columns are normalized by `SourceColumns` (the storage seam) and passed to
///   the build entry; the outcome (status, parts, dispatch) equals the saved build observation and the stored part
///   files equal the saved ones byte for byte. The freshly stored parts are mapped and every saved binding runs at
///   every saved worker count; status, SQL error code, result wire and dispatch equal the saved observation (the
///   outcome JSON without usage is identical);
/// - saved parameter refusals return `ParamRefused` for every binding, as saved;
/// - controls on the first case: worker counts 0 and 65 (shim `AbiRefused`, no wire), `refused_binding`
///   (`ParamRefused`), a build missing its last column (binder `Refused`), a nullable column (shim `AbiRefused`) and a
///   first value 10^20 outside `numeric(15, 2)` (verified domain check, `InvalidInput`).
///
/// Each saved SF1 build request in the optional `input_archives` list is checked as ABI columns without reading values
/// ([`SourceColumns::map_archive`] + `project`). A saved ABI v2 library is refused for lacking the v3 layout symbol.
/// Inputs, mappings and libraries are leaked:
/// the shim's `&'static` slices must stay valid until the process exits.
#[test]
#[ignore = "loads saved Verus libraries; set GENDB_ABI_SAVED_CHECK"]
fn saved_libraries_round_trip() {
    use serde_json::{Value, json};
    use std::path::{Path, PathBuf};

    let config: Value = read_json(Path::new(&std::env::var("GENDB_ABI_SAVED_CHECK").expect("GENDB_ABI_SAVED_CHECK")));
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    // Parts are written once: every run stores into its own directory.
    let scratch = PathBuf::from(config["scratch"].as_str().unwrap()).join(format!("run-{}-{nanos}", std::process::id()));
    let mut report = vec![];
    for entry in config["libraries"].as_array().unwrap() {
        let name = entry["name"].as_str().unwrap();
        let library_path = Path::new(entry["library"].as_str().unwrap());
        // SAFETY: a framework Verus build of a frozen crate; loaded in this test process only.
        let library: &'static VerusLibrary = Box::leak(Box::new(unsafe { VerusLibrary::load(library_path) }.unwrap()));
        let cases: Vec<&Path> = entry["cases"].as_array().unwrap().iter().map(|c| Path::new(c.as_str().unwrap())).collect();
        let stored_parts = |case: &Path| scratch.join(name).join(case.file_name().unwrap());
        for case in &cases {
            let build = check_saved_build(library, case, &stored_parts(case));
            let calls = check_saved_queries(library, &case.join("query"), &stored_parts(case));
            report.push(json!({"library": name, "case": case, "build": build, "query_calls": calls}));
        }
        if let Some(refusals) = entry["parameter_refusals"].as_str() {
            let calls = check_saved_queries(library, Path::new(refusals), &stored_parts(cases[0]));
            report.push(json!({"library": name, "parameter_refusals": refusals, "query_calls": calls}));
        }
        let refused_binding: Vec<StatementArgument> = serde_json::from_value(entry["refused_binding"].clone()).unwrap();
        let controls = check_controls(library, cases[0], &stored_parts(cases[0]), refused_binding);
        report.push(json!({"library": name, "controls": controls}));
    }
    for request in config["input_archives"].as_array().into_iter().flatten() {
        report.push(check_saved_input_archive(Path::new(request.as_str().unwrap())));
    }
    let v2 = Path::new(config["v2_library"].as_str().unwrap());
    // SAFETY: a saved framework Verus build (ABI v2); only its missing v3 layout symbol is observed.
    let refusal = match unsafe { VerusLibrary::load(v2) } {
        Err(error @ AbiError::MissingSymbol { symbol: LAYOUT_SYMBOL, .. }) => error.to_string(),
        other => panic!("ABI v2 library not refused: {:?}", other.err()),
    };
    report.push(json!({"v2_library": v2, "refused": refusal}));
    std::fs::write(config["report"].as_str().unwrap(), serde_json::to_vec_pretty(&report).unwrap()).unwrap();

    /// Build from the saved inline columns through `SourceColumns`, store the parts, compare with the saved case.
    fn check_saved_build(library: &VerusLibrary, case: &Path, stored: &Path) -> Value {
        let request = read_json(&case.join("build/verus-run.request.json"));
        let saved = read_json(&case.join("build/verus-run.result.json"));
        let columns = leaked_source_columns(&inline_columns(&request), false);
        let workers = request["workers"][0].as_u64().unwrap() as usize;
        let capacity = request["range_capacity"].as_u64().unwrap() as usize;
        let writer = PartFilesWriter::new(stored, PartsFormat::SavedV3).unwrap();
        // SAFETY: `columns` is leaked, so its read-only buffers stay mapped until the process exits.
        let (outcome, manifest) = unsafe { library.call_build(columns.descriptors(), workers, capacity, writer) }.unwrap();
        assert_eq!(without_usage(&outcome), without_usage_value(&saved["observations"][0]["outcome"]), "{}", case.display());
        let manifest = manifest.unwrap();
        assert_eq!(serde_json::to_value(&manifest).unwrap(), saved["parts"]);
        for index in 0..manifest.parts.len() {
            let file = format!("part-{index:04}.bin");
            assert_eq!(std::fs::read(stored.join(&file)).unwrap(), std::fs::read(case.join("parts").join(&file)).unwrap(), "{file}");
        }
        json!({"status": outcome.status, "parts": manifest, "dispatch": outcome.dispatch})
    }

    /// The saved SF1 build input (a prepared archive projected to the source tables), mapped as ABI columns without
    /// reading values: every descriptor is a NOT NULL column with a tag the shim accepts, and the row counts equal
    /// the saved build result's. The build itself is not rerun (it would rebuild the stored SF1 asset).
    fn check_saved_input_archive(build_request: &Path) -> Value {
        let request = read_json(build_request);
        let saved = read_json(&build_request.with_file_name("verus-run.result.json"));
        let input = &request["input"]["tables"];
        let projection: Vec<(String, Vec<usize>)> = input["tables"]
            .as_array()
            .unwrap()
            .iter()
            .map(|t| (t["table"].as_str().unwrap().to_string(), serde_json::from_value(t["ordinals"].clone()).unwrap()))
            .collect();
        let archive = Path::new(input["path"].as_str().unwrap());
        let columns = SourceColumns::map_archive(archive).unwrap().project(&projection).unwrap();
        let shape: Vec<(i32, i32, u64)> = columns.descriptors().iter().map(|c| (c.type_tag, c.nullable, c.len as u64)).collect();
        let accepted = [NATIVE_TYPE_I32, NATIVE_TYPE_I64, NATIVE_TYPE_I128, NATIVE_TYPE_UTF8];
        assert!(shape.iter().all(|(tag, nullable, _)| accepted.contains(tag) && *nullable == 0), "{shape:?}");
        let rows: Vec<u64> = shape.iter().map(|s| s.2).collect();
        assert_eq!(serde_json::to_value(&rows).unwrap(), saved["column_rows"]);
        json!({"input_archive": archive, "projection": projection, "descriptors": shape, "capture_identity": columns.capture_identity()})
    }

    /// Run every saved binding at every saved worker count over `parts`; compare with the saved observations.
    fn check_saved_queries(library: &VerusLibrary, query: &Path, parts: &Path) -> Vec<Value> {
        let request = read_json(&query.join("verus-run.request.json"));
        let saved = read_json(&query.join("verus-run.result.json"));
        let bindings: Vec<Vec<StatementArgument>> = serde_json::from_value(request["bindings"].clone()).unwrap();
        let mapped = leaked_parts(parts);
        let capacity = request["range_capacity"].as_u64().unwrap() as usize;
        let mut calls = vec![];
        for observation in saved["observations"].as_array().unwrap().iter().filter(|o| o["repetition"] == 0) {
            let binding = observation["binding"].as_u64().unwrap() as usize;
            let workers = observation["workers"].as_u64().unwrap() as usize;
            let arguments = leaked_arguments(bindings[binding].clone());
            // SAFETY: parts, arguments and the library are leaked and stay mapped until the process exits.
            let outcome = unsafe { library.call_query(mapped.descriptors(), arguments, workers, capacity) }.unwrap();
            assert_eq!(without_usage(&outcome), without_usage_value(&observation["outcome"]), "{} binding {binding}", query.display());
            calls.push(json!({"binding": binding, "workers": workers, "status": outcome.status, "sql_error": outcome.sql_error,
                "wire_bytes": outcome.result_wire.as_ref().map(Vec::len), "spawned": outcome.dispatch.spawned}));
        }
        calls
    }

    /// Refusals decided by the shim, the verified binder, the verified parameter binder and the verified source
    /// domain check, each through the real library.
    fn check_controls(library: &VerusLibrary, case: &Path, parts: &Path, refused_binding: Vec<StatementArgument>) -> Vec<Value> {
        let query_request = read_json(&case.join("query/verus-run.request.json"));
        let binding: Vec<StatementArgument> = serde_json::from_value(query_request["bindings"][0].clone()).unwrap();
        let mapped = leaked_parts(parts);
        let mut controls = vec![];
        let mut expect = |what: &str, outcome: CallOutcome, status: CallStatus| {
            assert_eq!((outcome.status, outcome.sql_error, outcome.result_wire.is_none()), (status, None, true), "{what}");
            controls.push(json!({"control": what, "status": outcome.status}));
        };
        for workers in [0, MAX_WORKERS + 1] {
            let arguments = leaked_arguments(binding.clone());
            // SAFETY: leaked parts and arguments.
            let outcome = unsafe { library.call_query(mapped.descriptors(), arguments, workers, 64) }.unwrap();
            expect(&format!("query at {workers} workers"), outcome, CallStatus::AbiRefused);
        }
        let arguments = leaked_arguments(refused_binding);
        // SAFETY: leaked parts and arguments.
        let outcome = unsafe { library.call_query(mapped.descriptors(), arguments, 1, 64) }.unwrap();
        expect("binding outside the parameter declaration", outcome, CallStatus::ParamRefused);

        let columns = inline_columns(&read_json(&case.join("build/verus-run.request.json")));
        let refused_parts = parts.with_file_name("refused-build-parts");
        let build = |columns: &[(String, Vec<String>)], nullable_first: bool, workers: usize| {
            let source = leaked_source_columns(columns, nullable_first);
            let writer = PartFilesWriter::new(&refused_parts, PartsFormat::SavedV3).unwrap();
            // SAFETY: leaked source columns.
            let (outcome, manifest) = unsafe { library.call_build(source.descriptors(), workers, 64, writer) }.unwrap();
            assert!(manifest.is_none() && !refused_parts.exists(), "a refused build writes nothing");
            outcome
        };
        expect("build at 65 workers", build(&columns, false, MAX_WORKERS + 1), CallStatus::AbiRefused);
        expect("build with a nullable column", build(&columns, true, 1), CallStatus::AbiRefused);
        expect("build missing its last column", build(&columns[..columns.len() - 1], false, 1), CallStatus::Refused);
        let mut out_of_domain = columns.clone();
        out_of_domain[0].1[0] = "100000000000000000000".into();
        expect("build with a value outside numeric(15, 2)", build(&out_of_domain, false, 1), CallStatus::InvalidInput);
        controls
    }

    fn leaked_parts(directory: &Path) -> &'static MappedParts {
        Box::leak(Box::new(MappedParts::open(directory, &PartAccess::default()).unwrap()))
    }

    fn leaked_arguments(arguments: Vec<StatementArgument>) -> &'static [StatementArgument] {
        Box::leak(arguments.into_boxed_slice())
    }

    fn without_usage(outcome: &CallOutcome) -> Value {
        without_usage_value(&serde_json::to_value(outcome).unwrap())
    }

    fn without_usage_value(outcome: &Value) -> Value {
        let mut outcome = outcome.clone();
        outcome.as_object_mut().unwrap().remove("usage");
        outcome
    }

    fn read_json(path: &Path) -> Value {
        serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap()
    }

    /// `(element, decimal texts)` of every inline column of a saved build request, in ABI order.
    fn inline_columns(build_request: &Value) -> Vec<(String, Vec<String>)> {
        build_request["input"]["inline"]["columns"]
            .as_array()
            .unwrap()
            .iter()
            .map(|c| {
                let texts = c["values"].as_array().unwrap().iter().map(|v| v.as_str().unwrap().to_string()).collect();
                (c["elem"].as_str().unwrap().to_string(), texts)
            })
            .collect()
    }

    /// One table holding `columns` (all of one length) in ABI order, normalized read-only by `SourceColumns`.
    fn leaked_source_columns(columns: &[(String, Vec<String>)], nullable_first: bool) -> &'static SourceColumns {
        use arrow::array::{ArrayRef, Date32Array, Decimal128Array, Int64Array, StringArray};
        use arrow::datatypes::{Field, Schema};
        use arrow::record_batch::RecordBatch;
        use gendb_artifacts::{ColType, ColumnSpec};
        use std::sync::Arc;

        let mut fields = vec![];
        let mut arrays: Vec<ArrayRef> = vec![];
        for (index, (elem, texts)) in columns.iter().enumerate() {
            let parsed = |t: &String| t.parse::<i128>().unwrap();
            let (ty, array): (ColType, ArrayRef) = match elem.as_str() {
                "i32" => (ColType::Date32, Arc::new(Date32Array::from(texts.iter().map(|t| parsed(t) as i32).collect::<Vec<_>>()))),
                "i64" => (ColType::I64, Arc::new(Int64Array::from(texts.iter().map(|t| parsed(t) as i64).collect::<Vec<_>>()))),
                "i128" => (
                    ColType::Decimal { p: 38, s: 0 },
                    Arc::new(Decimal128Array::from(texts.iter().map(parsed).collect::<Vec<_>>()).with_precision_and_scale(38, 0).unwrap()),
                ),
                "utf8" => (ColType::Utf8, Arc::new(StringArray::from(texts.clone()))),
                other => panic!("inline element {other}"),
            };
            fields.push(ColumnSpec { name: format!("c{index}"), ty, nullable: nullable_first && index == 0 });
            arrays.push(array);
        }
        let rows = arrays.first().map_or(0, |a| a.len());
        assert!(arrays.iter().all(|a| a.len() == rows), "one table: every inline column has the same length");
        let schema = Arc::new(Schema::new(
            fields.iter().zip(&arrays).map(|(f, a)| Field::new(&f.name, a.data_type().clone(), f.nullable)).collect::<Vec<_>>(),
        ));
        let table = ProjectedTable {
            table: "t".into(),
            original_indices: (0..fields.len()).collect(),
            fields,
            batches: vec![RecordBatch::try_new(schema, arrays).unwrap()],
            row_count: rows,
        };
        let columns = SourceColumns::from_projected(vec![table]).unwrap().read_only().unwrap().0;
        let flags: Vec<i32> = columns.descriptors().iter().map(|c: &NativeColumn| c.nullable).collect();
        assert!(flags.iter().enumerate().all(|(i, &f)| f == i32::from(nullable_first && i == 0)), "{flags:?}");
        Box::leak(Box::new(columns))
    }
}
