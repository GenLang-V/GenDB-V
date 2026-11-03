//! One statement through the reference evaluator: translate, build, run on a fixture database, or all three.

use super::evaluator_build::{build_evaluator, BuildOptions, BuildStatus, EvaluatorBuild};
use super::{create_output_dir, read_json, read_text, write_json, write_text, ReferenceError};
use crate::verus::VerusToolchain;
use gendb_frontend::ast::{self, AstDocument, Translation};
use gendb_frontend::parser::SqlParser;
use gendb_sqlspec::codec::RunOutcome;
use gendb_sqlspec::evaluator::{echo_text, EvaluatorLibrary};
use gendb_sqlspec::fixtures::Fixture;
use gendb_sqlspec::pg_text::result_json;
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Claim of a run whose outcome is rows or a SQL error, recorded with the result.
const EVALUATION_CLAIM: &str = "verified: rows/error == denote_top(db, query_spec()) for db = fixture rows under the query \
schema (db_wf and constraints_hold checked by verified code); TCB: pinned Verus/rustc/Z3, semantics definition, frontend \
meaning mapping, fixture input codec, wire codec, shim, loader";

/// The statement to translate: a SQL file, or the query headed `-- <label>:` in a query file.
#[derive(Clone, Debug)]
pub enum StatementSource {
    Sql(PathBuf),
    Labelled { file: PathBuf, label: String },
}

/// A translation and its record.
#[derive(Debug)]
pub struct Translated {
    pub record: Value,
    pub translation: Translation,
}

/// A run of an evaluator on a fixture database (or the reason nothing ran).
#[derive(Debug)]
pub struct Evaluation {
    pub record: Value,
    /// `None` when nothing was evaluated (translation refused, build not `Ok`).
    pub outcome: Option<RunOutcome>,
}

impl Evaluation {
    /// Rows or a SQL error: an outcome of the SQL meaning, comparable with PostgreSQL.
    pub fn is_sql_outcome(&self) -> bool {
        match &self.outcome {
            Some(RunOutcome::Rows(_)) => true,
            Some(RunOutcome::SqlError(kind)) => kind.sqlstate().is_some(),
            _ => false,
        }
    }
}

/// Translate `source` against the DDL file `schema` (PostgreSQL dialect) into `<out>/ast.json` and write
/// `<out>/translate.json`. `out` must not exist.
pub fn translate(parser: &SqlParser, schema: &Path, source: &StatementSource, out: &Path) -> Result<Translated, ReferenceError> {
    create_output_dir(out)?;
    let translated = translate_into(parser, schema, source, out)?;
    write_json(&out.join("translate.json"), &translated.record)?;
    Ok(translated)
}

/// Translate into `<dir>/ast.json` (the directory exists) and describe the result.
fn translate_into(parser: &SqlParser, schema: &Path, source: &StatementSource, dir: &Path) -> Result<Translated, ReferenceError> {
    let (text, translation) = match source {
        StatementSource::Sql(sql) => parser.translate(schema, sql, "postgres", &[])?,
        StatementSource::Labelled { file, label } => parser.translate_labelled(schema, file, label, "postgres")?,
    };
    let ast_path = dir.join("ast.json");
    write_text(&ast_path, &text)?;
    let (sql, query_file, label) = match source {
        StatementSource::Sql(sql) => (Some(sql), None, None),
        StatementSource::Labelled { file, label } => (None, Some(file), Some(label)),
    };
    let mut record = json!({ "kind": "gendb-sql-translate", "schema": schema, "sql": sql, "query_file": query_file,
        "label": label, "dialect": "postgres", "ast": ast_path });
    match &translation {
        Translation::Ok(doc) => {
            record["status"] = json!("ok");
            record["nodes"] = json!(doc.nodes.len());
            record["output"] = json!({ "names": doc.output.names, "pg_types": doc.output.pg_types });
        }
        Translation::Refused(r) => {
            record["status"] = json!("refused");
            record["refusal"] = json!({ "reason": r.reason, "detail": r.detail, "path": r.path, "sql": r.sql });
        }
    }
    Ok(Translated { record, translation })
}

/// Build the evaluator of the AST document in `ast_path` under `out`. A refused document builds nothing and writes
/// nothing; its record says so.
pub fn build_ast_file(
    toolchain: &VerusToolchain,
    ast_path: &Path,
    out: &Path,
    options: &BuildOptions,
) -> Result<EvaluatorBuild, ReferenceError> {
    match ast::decode(&read_text(ast_path)?)? {
        Translation::Ok(doc) => build_evaluator(toolchain, &doc, ast_path, out, options),
        Translation::Refused(r) => Ok(EvaluatorBuild {
            status: BuildStatus::Refused,
            library: None,
            record: json!({ "kind": "gendb-sql-query-build", "status": "refused", "refusal": r.reason }),
        }),
    }
}

/// Run the evaluator built in `build_dir` on the database of `fixture` and write the result record to `out_file`
/// (which must not exist). Only an `Ok` build runs, and only after its library's echo equals its `ast.json` again
/// (the library is the one the build verified and compiled from that document).
pub fn run_evaluator(build_dir: &Path, fixture: &Path, out_file: &Path) -> Result<Evaluation, ReferenceError> {
    if out_file.exists() {
        return Err(ReferenceError::OutputExists(out_file.to_path_buf()));
    }
    let evaluation = run_build(build_dir, fixture)?;
    write_json(out_file, &evaluation.record)?;
    Ok(evaluation)
}

fn run_build(build_dir: &Path, fixture: &Path) -> Result<Evaluation, ReferenceError> {
    let record_path = build_dir.join("build.json");
    let record = read_json(&record_path)?;
    let unusable = |message: String| ReferenceError::Record { path: record_path.clone(), message };
    if record["status"] != json!("ok") {
        return Err(unusable(format!("build has status {}; only verified, echo-checked builds are run", record["status"])));
    }
    let library = PathBuf::from(record["library"].as_str().ok_or_else(|| unusable("build record without library".into()))?);
    let ast_path = PathBuf::from(record["ast"].as_str().ok_or_else(|| unusable("build record without ast".into()))?);
    let doc = match ast::decode(&read_text(&ast_path)?)? {
        Translation::Ok(doc) => doc,
        Translation::Refused(_) => return Err(ReferenceError::Record { path: ast_path, message: "the AST document is a refusal".into() }),
    };
    let evaluator = EvaluatorLibrary::load(&library)?;
    if evaluator.echo()? != echo_text(&doc) {
        return Err(unusable("library echo differs from the AST document".into()));
    }
    let tables = Fixture::load(fixture)?.database_for(&doc)?;
    let outcome = evaluator.run(&tables)?;
    let mut r = result_json(&doc, &outcome)?;
    r["kind"] = json!("gendb-sql-run");
    r["library"] = json!(library);
    r["ast"] = json!(ast_path);
    r["fixture"] = json!(fixture);
    r["rows_per_table"] = json!(doc.tables.iter().zip(&tables).map(|(t, rows)| (t.name.clone(), rows.len())).collect::<BTreeMap<_, _>>());
    if matches!(outcome, RunOutcome::Rows(_) | RunOutcome::SqlError(_)) {
        r["claim"] = json!(EVALUATION_CLAIM);
    }
    Ok(Evaluation { record: r, outcome: Some(outcome) })
}

/// Translate, build and run one statement on one fixture under `out` (which must not exist): `ast.json`,
/// `build/`, `result.json` and the summary `eval.json`.
pub fn evaluate(
    toolchain: &VerusToolchain,
    parser: &SqlParser,
    schema: &Path,
    source: &StatementSource,
    fixture: &Path,
    out: &Path,
    options: &BuildOptions,
) -> Result<Evaluation, ReferenceError> {
    create_output_dir(out)?;
    let translated = translate_into(parser, schema, source, out)?;
    let mut record = json!({ "kind": "gendb-sql-eval", "translate": translated.record });
    let evaluation = match &translated.translation {
        Translation::Refused(_) => {
            record["status"] = json!("refused");
            Evaluation { record, outcome: None }
        }
        Translation::Ok(doc) => evaluate_document(toolchain, doc, fixture, out, options, record)?,
    };
    write_json(&out.join("eval.json"), &evaluation.record)?;
    Ok(evaluation)
}

fn evaluate_document(
    toolchain: &VerusToolchain,
    doc: &AstDocument,
    fixture: &Path,
    out: &Path,
    options: &BuildOptions,
    mut record: Value,
) -> Result<Evaluation, ReferenceError> {
    let build_dir = out.join("build");
    let build = build_evaluator(toolchain, doc, &out.join("ast.json"), &build_dir, options)?;
    record["build"] = json!({ "status": build.status, "record": build_dir.join("build.json"), "verification": build.record["run"]["verification"],
        "echo": build.record["echo"], "library_files_equal_checked": build.record["library_files_equal_checked"] });
    if build.status != BuildStatus::Ok {
        record["status"] = json!(build.status);
        return Ok(Evaluation { record, outcome: None });
    }
    let run = run_evaluator(&build_dir, fixture, &out.join("result.json"))?;
    record["status"] = run.record["status"].clone();
    record["result"] = run.record;
    Ok(Evaluation { record, outcome: run.outcome })
}
