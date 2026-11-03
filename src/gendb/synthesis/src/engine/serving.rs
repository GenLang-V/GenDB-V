//! Serving from an engine library (`gendb serve-engine REQUEST OUT_DIR`): every
//! requested statement is answered by an admitted engine version (the selected one unless the request names a package)
//! at every requested worker count, over the current capture's assets of the engine's storage uses. No synthesis,
//! proof, build or per-template package.
//!
//! A statement is SQL with its typed parameters and one binding, or AST bytes as given (`ast_hex`, whose meaning is
//! `decode_spec(bytes)`). SQL is translated by the frontend over exactly the DDL the engine was admitted with (its
//! package records it), the binding substituted after the constant check and the document encoded
//! (`gendb_frontend::engine_encode`); translation and encoding are untimed and their time is recorded apart. The call,
//! the echo comparison and the answer are `gendb_runtime::serve::engine`'s. Every cell records the AST digest and the
//! echo verdict.
//!
//! Missing support is a named refusal, never a fallback: a statement the frontend refuses or cannot encode, a library
//! without an engine version, a storage use the request's storage policy excludes (or, under `physical_only`, uses
//! holding a column twice), a use without an asset for the capture, an unequal echo. The engine's own refusals
//! (`Refused`, `Malformed`, `ParamRefused`) are answers with their checked meanings.

use crate::storage::payload::uses_holding_a_column_twice;
use crate::storage::policy::StoredDataPolicy;
use gendb_artifacts::verus::{ResolvedEngine, resolve_engine};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::Translation;
use gendb_frontend::engine_encode::encode_binding;
use gendb_frontend::params::ParamRequest;
use gendb_frontend::parser::SqlParser;
use gendb_runtime::serve::engine::{EngineExecutor, EngineStatement, serve_engine};
use gendb_runtime::worker::decode_hex;
use gendb_storage::import::{DatasetSpec, PreparedSource};
use gendb_storage::io::PartAccess;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::execution::{CHILD_TIMEOUT_SECONDS, RANGE_CAPACITY};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// A serving request (`gendb serve-engine`). JSON, unknown fields refused.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EngineServeRequest {
    /// The engine library.
    pub library: PathBuf,
    /// The engine package to serve (an admitted version); absent: the selected version.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub engine: Option<ContentId>,
    /// The dataset and its prepared capture: the current data the storage assets are resolved for.
    pub dataset: DatasetSpec,
    pub prepared_workload: PathBuf,
    /// A storage use this policy excludes is not served.
    #[serde(default)]
    pub storage_policy: StoredDataPolicy,
    /// Worker counts, each served in its own child.
    pub workers: Vec<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub part_access: Option<PartAccess>,
    pub statements: Vec<EngineServeStatement>,
}

/// One statement: `sql` (with its `parameters` and one binding, `arguments` in ascending `$index`), or `ast_hex`.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EngineServeStatement {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sql: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub parameters: Vec<ParamRequest>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub arguments: Vec<String>,
    /// AST bytes as lowercase hex (instead of `sql`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ast_hex: Option<String>,
}

/// Where statements are served: the library, the engine version, the current capture, the policy, the frontend, the
/// part advice, the worker executable and the evidence directory.
pub struct EngineServing<'a> {
    pub store: &'a ObjectStore,
    pub engine: &'a ResolvedEngine,
    pub capture: &'a CurrentCapture,
    pub policy: &'a StoredDataPolicy,
    pub parser: &'a SqlParser,
    pub access: PartAccess,
    pub worker: &'a Path,
    pub work: &'a Path,
}

/// Serve the request at `request_path` with `worker` (the gendb executable), evidence and `serving.json` under the new
/// or empty directory `out_dir`. Returns the serving record; `Err` only for a request or environment that cannot be
/// read.
pub fn serve_engine_request(request_path: &Path, out_dir: &Path, worker: &Path) -> Result<Value, String> {
    let text = std::fs::read_to_string(request_path).map_err(|e| format!("{}: {e}", request_path.display()))?;
    let request: EngineServeRequest = serde_json::from_str(&text).map_err(|e| format!("{}: {e}", request_path.display()))?;
    request.storage_policy.validate()?;
    if request.workers.is_empty() || request.statements.is_empty() {
        return Err("a serving request names at least one worker count and one statement".into());
    }
    if out_dir.exists() && std::fs::read_dir(out_dir).map_err(|e| format!("{}: {e}", out_dir.display()))?.next().is_some() {
        return Err(format!("{}: the output directory must be new or empty (evidence is written once)", out_dir.display()));
    }
    std::fs::create_dir_all(out_dir).map_err(|e| format!("{}: {e}", out_dir.display()))?;
    let store = ObjectStore::open_existing(&request.library).map_err(|e| format!("library {}: {e}", request.library.display()))?;
    let mut record = json!({"request":request,"route":"engine"});
    match resolve_engine(&store, request.engine).map_err(|e| e.to_string())? {
        None => {
            record["status"] = json!("unsupported");
            record["reason"] = json!("no_engine_version: the library has no admitted engine version (of the requested package)");
        }
        Some(engine) => {
            let source = PreparedSource::open(&request.prepared_workload, &request.dataset).map_err(|e| format!("prepared workload: {e}"))?;
            let capture = CurrentCapture::of(&source).map_err(|e| e.to_string())?;
            let parser = SqlParser::from_environment().map_err(|e| e.to_string())?;
            let serving = EngineServing {
                store: &store,
                engine: &engine,
                capture: &capture,
                policy: &request.storage_policy,
                parser: &parser,
                access: request.part_access.unwrap_or_default(),
                worker,
                work: out_dir,
            };
            let mut cells = vec![];
            for (index, statement) in request.statements.iter().enumerate() {
                cells.extend(serve_statement(&serving, statement, &request.workers, index)?);
            }
            let executed = cells.iter().all(|c| c["status"] == "executed");
            record["status"] = json!(if executed { "executed" } else { "unsupported" });
            record["engine"] = json!({"package":engine.version.package_id,"version":engine.version.version,"selected":engine.selected});
            record["cells"] = json!(cells);
            record["source_version"] = json!(source.source_snapshot());
        }
    }
    let path = out_dir.join("serving.json");
    std::fs::write(&path, serde_json::to_vec_pretty(&record).map_err(|e| e.to_string())?).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(record)
}

/// Serve statement `index` at every count of `workers`: one record per cell (`status` `executed` with the answer, or
/// `unsupported` with the named reason). `Err` only for a malformed request (bad hex, neither or both of sql and
/// ast_hex).
pub fn serve_statement(serving: &EngineServing<'_>, statement: &EngineServeStatement, workers: &[u32], index: usize) -> Result<Vec<Value>, String> {
    let work = serving.work.join(format!("statement-{index:04}"));
    let refused = |reason: String| Ok(vec![json!({"statement":index,"status":"unsupported","reason":reason})]);
    if let Some(reason) = policy_refusal(serving)? {
        return refused(reason);
    }
    let started = Instant::now();
    let (engine_statement, given) = match (&statement.sql, &statement.ast_hex) {
        (Some(sql), None) => match bound_statement(serving, sql, &statement.parameters, &statement.arguments, &work)? {
            Ok(bound) => (bound, json!({"sql":sql,"arguments":statement.arguments})),
            Err(reason) => return refused(reason),
        },
        (None, Some(hex)) => {
            let bytes = decode_hex(hex).ok_or_else(|| format!("statement {index}: ast_hex is not lowercase hex"))?;
            (EngineStatement::Bytes(bytes), json!({"ast_hex":hex}))
        }
        _ => return Err(format!("statement {index}: give exactly one of sql and ast_hex")),
    };
    let translation_ns = started.elapsed().as_nanos() as u64;
    let mut cells = vec![];
    for &w in workers {
        let executor = EngineExecutor { worker: serving.worker.to_owned(), work: work.clone(), timeout_seconds: CHILD_TIMEOUT_SECONDS, range_capacity: RANGE_CAPACITY, repetitions: 1 };
        let mut cell = match serve_engine(serving.store, serving.engine, &engine_statement, serving.capture, serving.access, &executor, w) {
            Ok(served) => {
                let mut record = served.record().map_err(|e| e.to_string())?;
                record["status"] = json!("executed");
                record
            }
            Err(reason) => json!({"status":"unsupported","reason":reason.to_string()}),
        };
        cell["statement"] = json!(index);
        cell["given"] = given.clone();
        cell["workers"] = json!(w);
        cell["part_access"] = json!(serving.access);
        cell["translation_and_encoding_ns"] = json!(translation_ns);
        cells.push(cell);
    }
    Ok(cells)
}

/// The named reason the request's storage policy refuses the engine's storage uses, if any.
fn policy_refusal(serving: &EngineServing<'_>) -> Result<Option<String>, String> {
    let uses = &serving.engine.version.package.storage_uses;
    if let Some(reason) = serving.policy.ineligible_use(serving.store, uses.iter().map(|u| (u.name.as_str(), u.package))).map_err(|e| e.to_string())? {
        return Ok(Some(reason));
    }
    if serving.policy.stores_columns_once() {
        return uses_holding_a_column_twice(serving.store, uses.iter().map(|u| (u.name.clone(), u.package)).collect()).map_err(|e| e.to_string());
    }
    Ok(None)
}

/// `sql` translated over the engine's recorded DDL with `parameters`, bound at `arguments` and encoded; `Ok(Err(reason))`
/// for a frontend refusal or an encoding refusal (named), `Err` for a framework failure.
fn bound_statement(serving: &EngineServing<'_>, sql: &str, parameters: &[ParamRequest], arguments: &[String], work: &Path) -> Result<Result<EngineStatement, String>, String> {
    std::fs::create_dir_all(work).map_err(|e| format!("{}: {e}", work.display()))?;
    let ddl = serving.store.read_blob(serving.engine.version.package.schema_ddl, None).map_err(|e| e.to_string())?;
    let (schema_file, sql_file) = (work.join("schema.sql"), work.join("query.sql"));
    std::fs::write(&schema_file, ddl).and_then(|()| std::fs::write(&sql_file, sql)).map_err(|e| format!("{}: {e}", work.display()))?;
    let placeholders: Vec<_> = parameters.iter().map(ParamRequest::placeholder).collect();
    let (_, translation) = serving.parser.translate(&schema_file, &sql_file, "postgres", &placeholders).map_err(|e| format!("frontend: {e}"))?;
    let document = match translation {
        Translation::Ok(document) => document,
        Translation::Refused(r) => return Ok(Err(format!("frontend_refusal: {} at {} ({})", r.reason, r.path, r.detail))),
    };
    Ok(encode_binding(&document, arguments).map(|ast| EngineStatement::Bound(Box::new(ast))).map_err(|e| format!("engine_ast_encoding: {e}")))
}
