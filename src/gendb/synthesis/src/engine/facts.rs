//! The engine run's training set, its encoded statements, and the training facts its authors and records read.
//!
//! - [`TrainingSet`]: the training templates (`engine.templates`: each template's SQL file and parameters), their
//!   visible bindings (`engine.bindings`), the timing binding, and the frozen meaning-preserving variants
//!   (`engine.variants`), read from the request's files. A variant file whose bytes differ from its manifest digest is
//!   refused: the variants are frozen.
//! - [`preparation_request`]: the templates as the statements of the run's ordinary data preparation
//!   (`controller::workload_run::preparation`), each named by its template and benchmarked at every visible binding.
//!   So every template has its statement, its preflight under `formal_proofs`, its saved answers per binding and the
//!   shared capture, and the session bench (storage tools, catalog, budget) works as for the other roles. No author is
//!   ever called for these statements. A template without free parameters (SEC-EDGAR's Q1) is one statement: it has
//!   exactly one visible binding (no arguments), is prepared as a concrete statement (its binding `statement`,
//!   `admission::bindings::CONCRETE_BINDING`), and its saved answers at its visible binding are read at that binding;
//!   every check names it by its visible binding (`admission::engine::TemplateCheck::statement_binding`).
//! - [`EngineChecks`]: the statement every engine cell is checked against (`admission::engine`): each
//!   template's prepared statement with its saved answers, and each frozen variant's statement checked against its
//!   template's saved answers;
//! - [`EncodedStatements`]: every template at every visible binding, and every timed variant at the timing binding, as
//!   engine AST bytes (`TemplateCheck::ast`: the binding substituted after the parser's constant check, then encoded),
//!   with the echo text the engine must return and the translation and encoding time of each, recorded apart from any
//!   timing. A variant whose bytes equal its template's or an earlier variant's is not timed
//!   (`admission::engine::distinct_variants`): it is listed with what it equals, and its count is reported.
//! - [`training_facts`]: what an author reads about the training set: per template the tables it reads, its parameters,
//!   its visible bindings and the saved baseline medians per binding and worker count, and the baselines' totals.
//!
//! Units: times in whole nanoseconds (`_ns`). Nothing here measures the engine.

use super::timing::{EngineStatement, VariantOf};
use super::totals::Baselines;
use crate::controller::limits::Limits;
use crate::controller::records;
use crate::controller::request::{QueryObjective, QueryRequest, WorkloadRequest};
use crate::query::QuerySession;
use gendb_frontend::engine_encode::ENGINE_AST_FORMAT;
use gendb_frontend::params::{BindingRequest, ParamRequest};
use gendb_frontend::parser::SqlParser;
use gendb_storage::import::DatasetSpec;
use gendb_verification::admission::engine::{TemplateCheck, VariantCheck, distinct_variants};
use gendb_verification::admission::bindings::CONCRETE_BINDING;
use gendb_verification::admission::{AdmissionError, BenchmarkBinding, IntegrityConstraints, ValidationPolicy};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

/// The file of the encoded statements in the engine directory of a run.
pub const STATEMENTS_FILE: &str = "statements.json";

/// One training template.
#[derive(Clone, Debug)]
pub struct TrainingTemplate {
    /// The template's name in `templates.json` (`Q01`); also its query name in the saved answers.
    pub name: String,
    pub sql_file: PathBuf,
    pub sql: String,
    /// Its parameters as `templates.json` declares them.
    pub parameters: Vec<ParamRequest>,
    /// Its visible bindings in file order: `(binding id, argument texts in slot order)`.
    pub bindings: Vec<(String, Vec<String>)>,
}

impl TrainingTemplate {
    /// The argument texts of binding `name`.
    pub fn arguments(&self, name: &str) -> Option<&[String]> {
        self.bindings.iter().find(|(id, _)| id == name).map(|(_, arguments)| arguments.as_slice())
    }

    /// Whether the template has no free parameter: it is one statement, prepared as a concrete statement.
    pub fn is_concrete(&self) -> bool {
        !self.parameters.iter().any(|p| matches!(p.binding, BindingRequest::Free { .. }))
    }

    /// Whether binding `name` is one of its visible bindings.
    pub fn has_binding(&self, name: &str) -> bool {
        self.arguments(name).is_some()
    }
}

/// One frozen variant of a training template (`fixtures/tpch/engine-variants/manifest.json`).
#[derive(Clone, Debug)]
pub struct VariantSpec {
    pub id: String,
    pub template: String,
    pub kind: String,
    pub file: PathBuf,
}

/// The training set of an engine run.
#[derive(Clone, Debug)]
pub struct TrainingSet {
    pub templates: Vec<TrainingTemplate>,
    /// The binding of the official matrix (`v0`).
    pub timing_binding: String,
    pub variants: Vec<VariantSpec>,
    /// The variants' transformation kinds.
    pub variant_kinds: BTreeSet<String>,
    /// SHA-256 over the three files read (templates, bindings, variant manifest): the training set's identity.
    pub identity: String,
}

fn read_text(path: &Path) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))
}

fn read_value(path: &Path) -> Result<(Value, String), String> {
    let text = read_text(path)?;
    let value = serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok((value, text))
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect()
}

impl TrainingSet {
    /// Read the training set the engine section names. Every template must have the timing binding with one argument
    /// per parameter; every variant must name a template and match its frozen digest.
    pub fn read(templates_file: &Path, bindings_file: &Path, variants_file: &Path, timing_binding: &str) -> Result<Self, String> {
        let (index, templates_text) = read_value(templates_file)?;
        let (visible, bindings_text) = read_value(bindings_file)?;
        let (manifest, manifest_text) = read_value(variants_file)?;
        let template_dir = templates_file.parent().unwrap_or(Path::new("/"));
        let mut templates = vec![];
        for (name, entry) in index["templates"].as_object().ok_or_else(|| format!("{}: no templates object", templates_file.display()))? {
            let sql_file = template_dir.join(entry["sql"].as_str().ok_or_else(|| format!("template {name}: no sql file"))?);
            let parameters: Vec<ParamRequest> = serde_json::from_value(entry["parameters"].clone()).map_err(|e| format!("template {name}: parameters: {e}"))?;
            let bindings: Vec<(String, Vec<String>)> = visible["queries"][name]
                .as_array()
                .ok_or_else(|| format!("{}: no visible bindings of {name}", bindings_file.display()))?
                .iter()
                .map(|b| {
                    let id = b["binding_id"].as_str().ok_or_else(|| format!("{name}: a binding without binding_id"))?.to_string();
                    let arguments = b["arguments"].as_array().ok_or_else(|| format!("{name} {id}: no arguments"))?;
                    let arguments = arguments.iter().map(|a| a.as_str().map(str::to_string).ok_or_else(|| format!("{name} {id}: an argument is not text"))).collect::<Result<Vec<_>, _>>()?;
                    if arguments.len() != parameters.len() {
                        return Err(format!("{name} {id}: {} arguments for {} parameters", arguments.len(), parameters.len()));
                    }
                    Ok((id, arguments))
                })
                .collect::<Result<_, String>>()?;
            if !bindings.iter().any(|(id, _)| id == timing_binding) {
                return Err(format!("template {name} has no visible binding {timing_binding} (engine.timing_binding)"));
            }
            let template = TrainingTemplate { name: name.clone(), sql: read_text(&sql_file)?, sql_file, parameters, bindings };
            if template.is_concrete() && template.bindings.len() != 1 {
                return Err(format!("template {name} has no free parameter, so it is one statement with exactly one visible binding (the timing binding), not {}", template.bindings.len()));
            }
            templates.push(template);
        }
        if templates.is_empty() {
            return Err(format!("{}: the training set has no template", templates_file.display()));
        }
        let variant_dir = variants_file.parent().unwrap_or(Path::new("/"));
        let mut variants = vec![];
        for entry in manifest["variants"].as_array().ok_or_else(|| format!("{}: no variants list", variants_file.display()))? {
            let field = |key: &str| entry[key].as_str().map(str::to_string).ok_or_else(|| format!("{}: a variant without {key}", variants_file.display()));
            let (id, template, kind, file, digest) = (field("id")?, field("template")?, field("kind")?, variant_dir.join(field("file")?), field("sha256")?);
            if !templates.iter().any(|t| t.name == template) {
                return Err(format!("variant {id} names {template}, which is not a training template"));
            }
            let bytes = std::fs::read(&file).map_err(|e| format!("{}: {e}", file.display()))?;
            if sha256_hex(&bytes) != digest {
                return Err(format!("variant {id}: {} differs from its frozen digest {digest}", file.display()));
            }
            variants.push(VariantSpec { id, template, kind, file });
        }
        let variant_kinds = variants.iter().map(|v| v.kind.clone()).collect();
        let identity = sha256_hex(format!("{templates_text}\u{0}{bindings_text}\u{0}{manifest_text}\u{0}{timing_binding}").as_bytes());
        Ok(Self { templates, timing_binding: timing_binding.to_string(), variants, variant_kinds, identity })
    }

    /// The visible bindings other than the timing binding, in the order the templates first name them (a template
    /// without free parameters has only the timing binding).
    pub fn other_bindings(&self) -> Vec<String> {
        let mut other: Vec<String> = vec![];
        for (id, _) in self.templates.iter().flat_map(|t| &t.bindings) {
            if *id != self.timing_binding && !other.contains(id) {
                other.push(id.clone());
            }
        }
        other
    }

    pub fn template(&self, name: &str) -> Option<&TrainingTemplate> {
        self.templates.iter().find(|t| t.name == name)
    }
}

/// The request whose ordinary preparation (`prepare_workload`) prepares the training templates: the engine request with
/// one query per template, named by it and benchmarked at every visible binding (its saved answers then apply), no
/// engine section and no output home. A template without free parameters is a concrete statement (no named benchmark
/// bindings; its one binding is `CONCRETE_BINDING`), so its saved answers at its one visible binding are named by that
/// binding here. No author ever runs on these queries; their `limits` (one submission under the user's cost guard)
/// only satisfy the execution-time objective's request rule.
pub fn preparation_request(request: &WorkloadRequest, engine_limits: &Limits, training: &TrainingSet) -> WorkloadRequest {
    let limits = Limits { max_iterations: 1, ..engine_limits.clone() };
    let queries = training
        .templates
        .iter()
        .map(|t| QueryRequest {
            name: Some(t.name.clone()),
            sql: t.sql.clone(),
            limits: limits.clone(),
            parameters: t.parameters.clone(),
            test_bindings: vec![],
            arguments: vec![],
            objective: QueryObjective::ExecutionTime {
                bindings: if t.is_concrete() {
                    vec![]
                } else {
                    t.bindings.iter().map(|(name, arguments)| BenchmarkBinding { name: name.clone(), arguments: arguments.clone() }).collect()
                },
                targets: vec![],
                early_stop: None,
            },
            preflight_from: None,
            reselect_from: None,
            continue_from: None,
        })
        .collect();
    let mut validation = request.validation.clone();
    if let ValidationPolicy::FormalProofs { saved_answers, .. } = &mut validation {
        for answer in saved_answers.iter_mut() {
            if training.template(&answer.query).is_some_and(|t| t.is_concrete() && t.has_binding(&answer.binding)) {
                answer.binding = CONCRETE_BINDING.into();
            }
        }
    }
    WorkloadRequest { queries, engine: None, workload_storage: None, output_home: None, validation, ..request.clone() }
}

/// The statements every engine cell is checked against (`admission::engine`): per training template its
/// prepared statement with its saved answers at every visible binding (`TemplateCheck`, from the template's session),
/// and per frozen variant its own statement checked against its template's saved answers (`VariantCheck`, translated
/// here; untimed, its translation time recorded).
pub struct EngineChecks {
    pub templates: Vec<TemplateCheck>,
    pub variants: Vec<VariantCheck>,
    /// Per variant id, the translation time of its statement in ns (untimed preparation).
    pub variant_translate_ns: BTreeMap<String, u64>,
}

/// What preparing the variants' statements reads from the request.
pub struct CheckSources<'a> {
    pub parser: &'a SqlParser,
    pub dataset: &'a DatasetSpec,
    pub constraints: Option<&'a IntegrityConstraints>,
    pub validation: &'a ValidationPolicy,
}

impl EngineChecks {
    /// The checks of every template (its session's preflight, benchmarked at every visible binding) and every frozen
    /// variant (statement records under `<dir>/variants/<id>`).
    pub fn prepare(training: &TrainingSet, sessions: &[(String, Arc<QuerySession>)], sources: &CheckSources<'_>, dir: &Path) -> Result<Self, AdmissionError> {
        let bindings = |template: &TrainingTemplate| -> Vec<BenchmarkBinding> {
            template.bindings.iter().map(|(name, arguments)| BenchmarkBinding { name: name.clone(), arguments: arguments.clone() }).collect()
        };
        let mut templates = vec![];
        for (name, session) in sessions {
            let template = training.template(name).ok_or_else(|| AdmissionError::tool(format!("{name} is not a training template")))?;
            templates.push(TemplateCheck { name: name.clone(), answers_of: name.clone(), preflight: session.preflight.clone(), bindings: bindings(template) });
        }
        let mut variants = vec![];
        let mut variant_translate_ns = BTreeMap::new();
        for spec in &training.variants {
            let template = training.template(&spec.template).ok_or_else(|| AdmissionError::tool(format!("variant {} names no template", spec.id)))?;
            let sql = std::fs::read_to_string(&spec.file).map_err(|e| AdmissionError::tool(format!("{}: {e}", spec.file.display())))?;
            let started = Instant::now();
            let directory = dir.join("variants").join(&spec.id);
            let check = TemplateCheck::prepare(sources.parser, sources.dataset, sources.constraints, sources.validation, &spec.id, &spec.template, &sql, &template.parameters, &bindings(template), &directory)?;
            variant_translate_ns.insert(spec.id.clone(), started.elapsed().as_nanos() as u64);
            variants.push(VariantCheck { id: spec.id.clone(), kind: spec.kind.clone(), template: spec.template.clone(), check });
        }
        Ok(Self { templates, variants, variant_translate_ns })
    }

    /// The check of a matrix statement: its variant's, else its template's.
    pub fn check_of(&self, statement: &EngineStatement) -> Option<&TemplateCheck> {
        match &statement.variant {
            Some(variant) => self.variants.iter().find(|v| v.id == variant.id).map(|v| &v.check),
            None => self.templates.iter().find(|t| t.name == statement.template),
        }
    }
}

/// One statement the engine is called with: its matrix statement, the echo text the engine must return for it, and its
/// untimed translation and encoding times.
#[derive(Clone, Debug)]
pub struct EncodedStatement {
    pub statement: EngineStatement,
    /// `gendb_sqlspec::evaluator::echo_text` of the bound document (what the engine's echo must equal).
    pub echo: String,
    /// Translation of the SQL text (a variant's; a template's translation is part of its preparation): 0 when not
    /// translated here.
    pub translate_ns: u64,
    pub encode_ns: u64,
}

impl EncodedStatement {
    fn record(&self) -> Value {
        let s = &self.statement;
        json!({"name":s.name(),"template":s.template,"variant":s.variant.as_ref().map(|v| json!({"id":v.id,"kind":v.kind})),"binding":s.binding,
            "ast_hex":hex(&s.ast),"ast_bytes":s.ast.len(),"ast_sha256":sha256_hex(&s.ast),"echo":self.echo,
            "translate_ns":self.translate_ns,"encode_ns":self.encode_ns})
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Every statement of the engine run's matrices.
#[derive(Clone, Debug)]
pub struct EncodedStatements {
    /// Every template at the timing binding: the official matrix.
    pub official: Vec<EncodedStatement>,
    /// Per other visible binding, every template at it (timed for a version whose official totals meet the stop).
    pub other_bindings: Vec<(String, Vec<EncodedStatement>)>,
    /// The timed variants: bytes different from their template's and from every earlier variant's.
    pub variants: Vec<EncodedStatement>,
    /// `statements.json`: every statement with its digest, echo and times, and every untimed variant with what it equals.
    pub record: Value,
}

impl EncodedStatements {
    /// Encode every template at every visible binding and keep the variants whose bytes at the timing binding are new
    /// (`admission::engine::distinct_variants`); record them in `<dir>/statements.json`.
    pub fn prepare(training: &TrainingSet, checks: &EngineChecks, dir: &Path) -> Result<Self, AdmissionError> {
        records::create_dir(dir).map_err(AdmissionError::tool)?;
        let started = Instant::now();
        let encode = |check: &TemplateCheck, template: &str, variant: Option<VariantOf>, binding: &str, translate_ns: u64| -> Result<EncodedStatement, AdmissionError> {
            let at = Instant::now();
            let ast = check.ast(binding)?;
            Ok(EncodedStatement {
                echo: gendb_sqlspec::evaluator::echo_text(&ast.document),
                statement: EngineStatement { template: template.to_string(), variant, binding: binding.to_string(), ast: ast.bytes },
                translate_ns,
                encode_ns: at.elapsed().as_nanos() as u64,
            })
        };
        let mut official = vec![];
        let mut other_bindings: Vec<(String, Vec<EncodedStatement>)> = training.other_bindings().into_iter().map(|b| (b, vec![])).collect();
        for check in &checks.templates {
            official.push(encode(check, &check.name, None, &training.timing_binding, 0)?);
            // Every template at each other visible binding it has (a template without free parameters has none).
            for (binding, encoded) in other_bindings.iter_mut().filter(|(binding, _)| check.bindings.iter().any(|b| b.name == *binding)) {
                encoded.push(encode(check, &check.name, None, binding, 0)?);
            }
        }
        let (distinct, untimed) = distinct_variants(&checks.templates, &checks.variants, &training.timing_binding)?;
        let variants = distinct
            .into_iter()
            .map(|(variant, _)| {
                let translate_ns = checks.variant_translate_ns.get(&variant.id).copied().unwrap_or(0);
                encode(&variant.check, &variant.template, Some(VariantOf { id: variant.id.clone(), kind: variant.kind.clone() }), &training.timing_binding, translate_ns)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut statements = Self { official, other_bindings, variants, record: Value::Null };
        statements.record = json!({"format_version":1,"training_set":training.identity,"ast_format":ENGINE_AST_FORMAT,"timing_binding":training.timing_binding,
            "official":statements.official.iter().map(EncodedStatement::record).collect::<Vec<_>>(),
            "other_bindings":statements.other_bindings.iter().map(|(b, s)| json!({"binding":b,"statements":s.iter().map(EncodedStatement::record).collect::<Vec<_>>()})).collect::<Vec<_>>(),
            "variants":{"frozen":training.variants.len(),"timed":statements.variants.len(),"not_timed":untimed.len(),
                "timed_statements":statements.variants.iter().map(EncodedStatement::record).collect::<Vec<_>>(),"not_timed_statements":untimed,
                "rule":"a variant is timed only when its encoded AST bytes differ from its template's at the timing binding and from every earlier variant's; an untimed variant's bytes are those of the statement it names, so its answer is that statement's"},
            "prepared_ns":started.elapsed().as_nanos() as u64,
            "timing":"translation and encoding are untimed: recorded here per statement, never part of a cell"});
        records::write_json_atomic(&dir.join(STATEMENTS_FILE), &statements.record).map_err(AdmissionError::tool)?;
        Ok(statements)
    }

    /// The statements of one other visible binding.
    pub fn at_binding(&self, binding: &str) -> Option<&[EncodedStatement]> {
        self.other_bindings.iter().find(|(b, _)| b == binding).map(|(_, s)| s.as_slice())
    }
}

/// What an author reads about the training set (`contract/engine/templates.json` and CURRENT FACTS): per template its
/// SQL file, the tables it reads, its parameters, its visible bindings and the saved baseline medians at every binding
/// and worker count; the baselines' totals per binding and worker count with the faster engine; the variant kinds and
/// counts. Saved records only: nothing is measured.
pub fn training_facts(training: &TrainingSet, sessions: &[(String, Arc<QuerySession>)], baselines: &Baselines, workers: &[usize], statements: &EncodedStatements) -> Result<Value, AdmissionError> {
    let mut templates = vec![];
    for (name, session) in sessions {
        let template = training.template(name).ok_or_else(|| AdmissionError::tool(format!("{name} is not a training template")))?;
        let tables: Vec<String> = session.demand()?.tables.iter().map(|t| t.name.clone()).collect();
        let baseline_cells: Vec<Value> = template
            .bindings
            .iter()
            .flat_map(|(binding, _)| workers.iter().map(move |w| (binding.clone(), *w)))
            .filter_map(|(binding, w)| {
                baselines.cell(name, &binding, w).map(|c| json!({"binding":binding,"workers":w,"duckdb_ns":c.duckdb_ns,"umbra_ns":c.umbra_ns,"agreement":c.agreement}))
            })
            .collect();
        templates.push(json!({"name":name,"sql_file":template.sql_file,"sql":template.sql,"tables":tables,
            "parameters":template.parameters.iter().map(|p| json!({"index":p.index,"name":p.name,"type":p.sql_type})).collect::<Vec<_>>(),
            "bindings":template.bindings.iter().map(|(b, a)| json!({"name":b,"arguments":a})).collect::<Vec<_>>(),
            "baselines":baseline_cells}));
    }
    let mut totals = vec![];
    for binding in std::iter::once(training.timing_binding.clone()).chain(training.other_bindings()) {
        // The templates with this visible binding (every template has the timing binding).
        let names: BTreeSet<&str> = training.templates.iter().filter(|t| t.has_binding(&binding)).map(|t| t.name.as_str()).collect();
        for &w in workers {
            if let Ok((duckdb_ns, umbra_ns)) = baselines.totals(&names, &binding, w) {
                let (target_ns, engine) = super::totals::target_of(duckdb_ns, umbra_ns);
                totals.push(json!({"binding":binding,"workers":w,"duckdb_ns":duckdb_ns,"umbra_ns":umbra_ns,"target_ns":target_ns,"target_engine":engine}));
            }
        }
    }
    let variants = &statements.record["variants"];
    Ok(json!({"timing_binding":training.timing_binding,"other_bindings":training.other_bindings(),"workers":workers,"templates":templates,"baseline_totals":totals,
        "variants":{"kinds":training.variant_kinds,"frozen":variants["frozen"],"timed":variants["timed"],"not_timed":variants["not_timed"]}}))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repository() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).ancestors().nth(3).expect("<repository>/src/gendb/synthesis").to_path_buf()
    }

    /// A template without free parameters (SEC-EDGAR's Q1): it reads with its one visible binding
    /// (a second one is refused), it is prepared as a concrete statement (no named benchmark binding, so the request
    /// validates) with its saved answers at its visible binding named by the concrete binding, and the other visible
    /// bindings are those the templates have.
    #[test]
    fn a_template_without_parameters_prepares_as_a_concrete_statement() {
        let scratch = crate::controller::test_support::scratch_root("engine-concrete-template");
        std::fs::create_dir_all(&scratch).unwrap();
        let free = json!([{"index":1,"type":"integer","binding":{"free":{}}}]);
        std::fs::write(scratch.join("templates.json"), json!({"templates":{"Q1":{"sql":"q1.sql","parameters":[]},"Q2":{"sql":"q2.sql","parameters":free}}}).to_string()).unwrap();
        std::fs::write(scratch.join("q1.sql"), "SELECT COUNT(*) FROM t").unwrap();
        std::fs::write(scratch.join("q2.sql"), "SELECT a FROM t WHERE a = $1").unwrap();
        std::fs::write(scratch.join("manifest.json"), json!({"variants":[]}).to_string()).unwrap();
        let visible = |q1: Value| json!({"queries":{"Q1":q1,"Q2":[{"binding_id":"v0","arguments":["1"]},{"binding_id":"v1","arguments":["2"]}]}}).to_string();
        std::fs::write(scratch.join("visible.json"), visible(json!([{"binding_id":"v0","arguments":[]}]))).unwrap();
        let training = TrainingSet::read(&scratch.join("templates.json"), &scratch.join("visible.json"), &scratch.join("manifest.json"), "v0").unwrap();
        let (q1, q2) = (training.template("Q1").unwrap(), training.template("Q2").unwrap());
        assert!(q1.is_concrete() && !q2.is_concrete() && q1.has_binding("v0") && !q1.has_binding("v1"));
        assert_eq!(training.other_bindings(), ["v1"], "the bindings the templates have, whatever the first template");
        std::fs::write(scratch.join("two.json"), visible(json!([{"binding_id":"v0","arguments":[]},{"binding_id":"v1","arguments":[]}]))).unwrap();
        let error = TrainingSet::read(&scratch.join("templates.json"), &scratch.join("two.json"), &scratch.join("manifest.json"), "v0").unwrap_err();
        assert!(error.contains("exactly one visible binding"), "{error}");

        let answer = |query: &str, binding: &str| json!({"query":query,"binding":binding,"engine":"duckdb","description":"d","path":"a.json","rows_pointer":""});
        let request: WorkloadRequest = serde_json::from_value(json!({"format_version":2,
            "dataset":{"tables":[{"name":"t","fields":[{"name":"a","ty":"I64","nullable":false}],"locations":[],"format":"Parquet"}]},
            "queries":[],"hardware":{"threads":[1,64]},"max_concurrent_queries":1,"author_executable":"claude","library":"library",
            "barriers":{"activity_lock":"/l/a","build_lock":"/l/b","race_lock":"/l/r"},"storage_policy":{"kind":"physical_only","eligible_storages":[]},
            "integrity_constraints":{"trust":"user_declared","declarations":[{"table":"t","sql":"PRIMARY KEY (a)"}]},
            "validation":{"kind":"formal_proofs","numeric_relative_tolerance":"1e-9","saved_answers":[answer("Q1", "v0"), answer("Q2", "v0"), answer("Q2", "v1")]}}))
        .unwrap();
        let limits = Limits { max_cost_usd: crate::controller::limits::Money::parse("10").unwrap(), ..crate::controller::limits::tests::limits() };
        let prepared = preparation_request(&request, &limits, &training);
        prepared.validate().unwrap_or_else(|e| panic!("{e}"));
        let (pq1, pq2) = (&prepared.queries[0], &prepared.queries[1]);
        assert_eq!((pq1.name.as_deref(), pq1.is_template(), pq1.objective.benchmark_bindings().len()), (Some("Q1"), false, 0));
        assert_eq!(pq2.objective.benchmark_bindings().iter().map(|b| b.name.as_str()).collect::<Vec<_>>(), ["v0", "v1"]);
        let ValidationPolicy::FormalProofs { saved_answers, .. } = &prepared.validation else { panic!("formal_proofs") };
        let named: Vec<(&str, &str)> = saved_answers.iter().map(|a| (a.query.as_str(), a.binding.as_str())).collect();
        assert_eq!(named, [("Q1", CONCRETE_BINDING), ("Q2", "v0"), ("Q2", "v1")]);
        std::fs::remove_dir_all(&scratch).ok();
    }

    /// The repository's training set reads whole: 22 templates with v0..v2, 107 frozen variants of six kinds whose
    /// digests match, and a changed variant file is refused.
    #[test]
    fn the_tpch_training_set_reads_and_refuses_a_changed_variant() {
        let repo = repository();
        let templates = repo.join("src/gendb/fixtures/tpch/templates/templates.json");
        let bindings = repo.join("output/tpch-sf100/bindings/visible.json");
        let variants = repo.join("src/gendb/fixtures/tpch/engine-variants/manifest.json");
        let training = TrainingSet::read(&templates, &bindings, &variants, "v0").unwrap();
        assert_eq!(training.templates.len(), 22);
        assert_eq!(training.other_bindings(), ["v1", "v2"]);
        assert_eq!((training.variants.len(), training.variant_kinds.len()), (107, 6));
        assert!(training.template("Q01").unwrap().sql.contains("lineitem"));
        assert!(TrainingSet::read(&templates, &bindings, &variants, "v9").unwrap_err().contains("no visible binding v9"));

        let scratch = crate::controller::test_support::scratch_root("engine-training");
        std::fs::create_dir_all(scratch.join("variants")).unwrap();
        let mut manifest: Value = serde_json::from_str(&std::fs::read_to_string(&variants).unwrap()).unwrap();
        let first = manifest["variants"][0]["file"].as_str().unwrap().to_string();
        std::fs::write(scratch.join(&first), "SELECT 1").unwrap();
        manifest["variants"] = json!([manifest["variants"][0].clone()]);
        std::fs::write(scratch.join("manifest.json"), manifest.to_string()).unwrap();
        let error = TrainingSet::read(&templates, &bindings, &scratch.join("manifest.json"), "v0").unwrap_err();
        assert!(error.contains("differs from its frozen digest"), "{error}");
        std::fs::remove_dir_all(&scratch).ok();
    }

}
