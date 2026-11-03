//! PostgreSQL differential testing of the reference evaluator on tiny fixtures (nothing here is a proof). For every
//! case of a reference fixture: translate the SQL, build the evaluator through the same path as
//! [`build_evaluator`](super::build_evaluator), run it on the fixture database in a child process, and turn the
//! outcome into a candidate for the harness (`sqlspec/tests/postgres_reference.py compare`), which compares it with
//! PostgreSQL evidence recorded earlier (multiset for unordered cases; tie runs and LIMIT boundary ties for ordered
//! ones; exact SQLSTATE for errors). Parser/emitter refusals, build failures and `capacity` become candidates
//! `unsupported` / `refused` / `capacity`, which the harness never counts as a match.

use super::evaluator_build::{build_evaluator, BuildOptions, BuildStatus};
use super::{create_output_dir, read_json, write_json, write_text, ReferenceError};
use crate::verus::{FrozenCrate, VerusToolchain};
use gendb_frontend::ast::Translation;
use gendb_frontend::parser::SqlParser;
use gendb_sqlspec::fixtures::{postgres_harness, repository_root, CaseQuery, Fixture, FixtureCase};
use serde_json::{json, Map, Value};
use std::path::{Path, PathBuf};
use std::process::Command;

/// How a case's built evaluator is run in a child process: `<program> <args...> --build DIR --fixture FILE --out FILE`
/// must behave as [`run_evaluator`](super::run_evaluator) (for the `gendb` binary: `gendb sql run`). A child
/// process keeps an aborting shim or a loaded library from affecting the other cases.
#[derive(Clone, Debug)]
pub struct RunProcess {
    pub program: PathBuf,
    pub args: Vec<String>,
}

/// Summary of one fixture diff (also `<out>/diff.json`).
#[derive(Debug)]
pub struct FixtureDiff {
    pub summary: Value,
}

impl FixtureDiff {
    /// The harness compared every case and all matched.
    pub fn all_matched(&self) -> bool {
        self.summary["harness_exit"] == json!(0)
    }

    /// The summary with one short line per case instead of the full case records.
    pub fn brief(&self) -> Value {
        let mut brief = self.summary.clone();
        let cases = brief.as_object_mut().and_then(|o| o.remove("case_records")).unwrap_or_default();
        let lines: Vec<Value> = cases
            .as_array()
            .into_iter()
            .flatten()
            .map(|c| json!({ "case": c["case"], "stage": c["stage"], "candidate": c["candidate"]["status"], "compare": c["compare"], "refusal": c["refusal"]["reason"] }))
            .collect();
        brief["cases_brief"] = json!(lines);
        brief
    }
}

/// Crate name of a case build (lowercase ASCII, digits, `_`).
pub fn crate_name_for(fixture: &str, case: &str) -> String {
    let clean = |s: &str| s.chars().map(|c| if c.is_ascii_alphanumeric() { c.to_ascii_lowercase() } else { '_' }).collect::<String>();
    format!("gendb_sql_{}_{}", clean(fixture), clean(case))
}

/// Run every case of `fixture_path` and compare with `reference_path` (PostgreSQL evidence). Writes
/// `<out>/<case>/...`, `<out>/candidate.json`, `<out>/compare.txt` and `<out>/diff.json`; `out` must not exist.
/// `parser` translates the cases and its interpreter runs the harness.
pub fn diff_fixture(
    toolchain: &VerusToolchain,
    parser: &SqlParser,
    run_process: &RunProcess,
    fixture_path: &Path,
    reference_path: &Path,
    out: &Path,
    checked_library: Option<&FrozenCrate>,
) -> Result<FixtureDiff, ReferenceError> {
    let fixture = Fixture::load(fixture_path)?;
    create_output_dir(out)?;
    let mut candidates = Map::new();
    let mut cases = Vec::new();
    for case in &fixture.cases {
        let dir = out.join(&case.name);
        create_output_dir(&dir)?;
        let options = BuildOptions { crate_name: &crate_name_for(&fixture.name, &case.name), checked_library };
        let (record, candidate) = evaluate_case(toolchain, parser, run_process, &fixture, case, &dir, &options)?;
        candidates.insert(case.name.clone(), candidate);
        cases.push(record);
    }
    let candidate_path = out.join("candidate.json");
    write_json(&candidate_path, &json!({ "fixture": fixture.name, "cases": candidates }))?;
    let (harness_exit, verdicts) = compare_with_evidence(parser, reference_path, &candidate_path, out)?;
    for record in &mut cases {
        let name = record["case"].as_str().unwrap_or_default().to_owned();
        record["compare"] = verdicts.get(&name).cloned().unwrap_or(Value::Null);
    }
    let count = |f: &dyn Fn(&Value) -> bool| cases.iter().filter(|c| f(c)).count();
    let summary = json!({
        "kind": "gendb-sql-diff",
        "fixture": fixture.name,
        "fixture_path": fixture_path,
        "reference": reference_path,
        "harness_exit": harness_exit,
        "cases": cases.len(),
        "evaluated": count(&|c| c["stage"] == "run" && c["result_status"].is_string()),
        "matched": count(&|c| c["compare"]["verdict"] == "match"),
        "mismatched_evaluated": count(&|c| c["compare"]["verdict"] == "mismatch" && c["stage"] == "run"),
        "refused_frontend": count(&|c| c["stage"] == "translate"),
        "refused_build": count(&|c| c["stage"] == "build"),
        "case_records": cases,
    });
    write_json(&out.join("diff.json"), &summary)?;
    Ok(FixtureDiff { summary })
}

/// One case: its record and its harness candidate. The case's directory `dir` exists.
fn evaluate_case(
    toolchain: &VerusToolchain,
    parser: &SqlParser,
    run_process: &RunProcess,
    fixture: &Fixture,
    case: &FixtureCase,
    dir: &Path,
    options: &BuildOptions,
) -> Result<(Value, Value), ReferenceError> {
    let mut record = json!({ "case": case.name });
    let ast_path = dir.join("ast.json");
    let mut candidate = match translate_case(parser, fixture, &case.query, dir)? {
        Translation::Refused(r) => {
            record["stage"] = json!("translate");
            record["refusal"] = json!({ "reason": r.reason, "detail": r.detail, "path": r.path, "sql": r.sql });
            json!({ "status": "unsupported", "reason": r.reason })
        }
        Translation::Ok(doc) => {
            let build_dir = dir.join("build");
            let build = build_evaluator(toolchain, &doc, &ast_path, &build_dir, options)?;
            record["build"] = json!({ "status": build.status, "verification": build.record["run"]["verification"], "wall_ns": build.record["run"]["wall_ns"] });
            if build.status != BuildStatus::Ok {
                record["stage"] = json!("build");
                record["build_record"] = build.record.clone();
                let status = if build.status == BuildStatus::Refused { "unsupported" } else { "refused" };
                json!({ "status": status, "build": build.status })
            } else {
                record["stage"] = json!("run");
                run_case(run_process, &build_dir, &fixture.path, dir, &mut record)?
            }
        }
    };
    // The fixture's declared value-only numeric columns (plan-dependent representative scale) travel with the
    // candidate, so evidence recorded before the declaration existed still applies them.
    if let Some(columns) = case.raw.get("value_only_columns") {
        candidate["value_only_columns"] = columns.clone();
    }
    record["candidate"] = candidate.clone();
    Ok((record, candidate))
}

/// Translate one case against the fixture's DDL (written to `<dir>/schema.sql`); the document goes to `<dir>/ast.json`.
fn translate_case(parser: &SqlParser, fixture: &Fixture, query: &CaseQuery, dir: &Path) -> Result<Translation, ReferenceError> {
    let schema = dir.join("schema.sql");
    write_text(&schema, &fixture.ddl)?;
    let (text, translation) = match query {
        CaseQuery::Sql(sql) => {
            let file = dir.join("query.sql");
            write_text(&file, sql)?;
            parser.translate(&schema, &file, "postgres", &[])?
        }
        CaseQuery::Labelled { path, label } => parser.translate_labelled(&schema, path, label, "postgres")?,
    };
    write_text(&dir.join("ast.json"), &text)?;
    Ok(translation)
}

/// Run a built case in the child process; the candidate of its result (a failed child is a `refused` candidate).
fn run_case(run_process: &RunProcess, build_dir: &Path, fixture: &Path, dir: &Path, record: &mut Value) -> Result<Value, ReferenceError> {
    let result_path = dir.join("result.json");
    let output = Command::new(&run_process.program)
        .args(&run_process.args)
        .arg("--build")
        .arg(build_dir)
        .arg("--fixture")
        .arg(fixture)
        .arg("--out")
        .arg(&result_path)
        .output()
        .map_err(|e| ReferenceError::Process { program: run_process.program.clone(), message: e.to_string() })?;
    write_text(&dir.join("run.stderr.txt"), &String::from_utf8_lossy(&output.stderr))?;
    if !result_path.is_file() {
        record["run_failure"] = json!(format!("{}: {}", output.status, String::from_utf8_lossy(&output.stderr)));
        return Ok(json!({ "status": "refused", "detail": "run process failed" }));
    }
    let result = read_json(&result_path)?;
    record["result_status"] = result["status"].clone();
    Ok(candidate_of(&result))
}

/// Harness candidate for a run result record.
fn candidate_of(result: &Value) -> Value {
    match result["status"].as_str() {
        Some("rows") => json!({ "status": "rows", "rows": result["rows"] }),
        Some("sql_error") => json!({ "status": "sql_error", "sqlstate": result["sqlstate"], "error_kind": result["error_kind"] }),
        Some("capacity") => json!({ "status": "capacity" }),
        _ => json!({ "status": "refused", "detail": result["status"] }),
    }
}

/// `postgres_reference.py compare EVIDENCE CANDIDATE` with the parser's interpreter; writes `<out>/compare.txt`.
/// Returns the harness exit code and the verdict of every case it printed (`match` / `MISMATCH <name>: <detail>`).
fn compare_with_evidence(parser: &SqlParser, reference_path: &Path, candidate_path: &Path, out: &Path) -> Result<(Option<i32>, Map<String, Value>), ReferenceError> {
    let python = parser.python();
    let output = Command::new(python)
        .current_dir(repository_root())
        .env("PYTHONDONTWRITEBYTECODE", "1")
        .arg(postgres_harness())
        .arg("compare")
        .arg(reference_path)
        .arg(candidate_path)
        .output()
        .map_err(|e| ReferenceError::Process { program: python.to_path_buf(), message: e.to_string() })?;
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    write_text(&out.join("compare.txt"), &format!("{stdout}{}exit {:?}\n", String::from_utf8_lossy(&output.stderr), output.status.code()))?;
    let mut verdicts = Map::new();
    for line in stdout.lines() {
        let (verdict, rest) = match line.split_once(' ') {
            Some(("match", rest)) => ("match", rest),
            Some(("MISMATCH", rest)) => ("mismatch", rest),
            _ => continue,
        };
        if let Some((name, detail)) = rest.trim().split_once(": ") {
            verdicts.insert(name.to_owned(), json!({ "verdict": verdict, "detail": detail }));
        }
    }
    Ok((output.status.code(), verdicts))
}
