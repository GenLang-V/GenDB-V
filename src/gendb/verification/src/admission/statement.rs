//! The one statement instance of a query, fixed before data preparation and shared by every later stage: source
//! demand, author inputs, references, evaluation, records (statement key, claim) and serving.
//!
//! The SQL (with typed placeholders `$n`, each fixed or free with a declared domain) is translated once by the
//! frontend over the dataset's DDL; fixed parameters are substituted in the AST (`params::instantiate`, never in SQL
//! text). What the frontend translates and types, and what the ABI can bind, is supported; there is no query-shape
//! gate. Every refusal here is named and precedes data preparation and any author call.
//!
//! The request's declared integrity constraints, when present, are appended to the DDL as `ALTER TABLE ... ADD`
//! clauses and translated with it ([`super::integrity_constraints`]); the statement then carries them, and its v4 key
//! carries their generated module. Without declarations the DDL, document and keys are unchanged.

use super::bindings::{BenchmarkBinding, Binding, BindingError, admission_bindings, refusal_probes};
use super::integrity_constraints::IntegrityConstraints;
use super::records::{create_dir, now_unix_ms, write_new_json, write_text};
use super::{AdmissionError, Refused};
use gendb_artifacts::ColType;
use gendb_artifacts::verus::{VerusStatementKeyV1, VerusStatementKeyV2};
use gendb_frontend::ast::{AstDocument, Translation};
use gendb_frontend::columns::{self, ColumnDemand, SourceDeclaration};
use gendb_frontend::params::{self, Instance, ParamDecl, ParamDomain, ParamRequest, ParamType, ParamValue};
use gendb_frontend::parser::SqlParser;
use gendb_runtime::serve::{statement_key, statement_key_v4};
use gendb_storage::import::{DatasetSpec, PreparedSource};
use gendb_storage::io::SourceColumns;
use serde_json::{Value, json};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// The SQL dialect of every statement.
const DIALECT: &str = "postgres";

/// One statement instance with everything derived from it before data preparation.
#[derive(Clone)]
pub struct Statement {
    pub sql: String,
    /// The request's parameter declaration.
    pub parameters: Vec<ParamRequest>,
    /// Evidence directory (`<query directory>/verus-preflight`, or a fresh sibling when that one is used).
    pub directory: PathBuf,
    /// PostgreSQL DDL of the dataset's tables the statement was translated against (with the declared constraints).
    pub schema_ddl: String,
    /// The request's declared integrity constraints the statement was translated with; `None`: none declared.
    pub integrity_constraints: Option<IntegrityConstraints>,
    /// The translated statement with its placeholders.
    pub template: AstDocument,
    pub declarations: Vec<ParamDecl>,
    /// Fixed parameters substituted; `instance.free` are the free ones (`ps[slot]` of `query_spec_at`).
    pub instance: Instance,
    /// Layout and base-column demand of the instance.
    pub demand: ColumnDemand,
    /// The delivered source columns the verified entry binds.
    pub source: SourceDeclaration,
    pub key: VerusStatementKeyV1,
    /// Hex identity of `key`.
    pub key_id: String,
    /// The statement key of the query entry v4 over stored data (schema and statement texts as separate fields), the
    /// key request lookup computes the same way (`gendb_runtime::serve::statement_key_v4`).
    pub key_v4: VerusStatementKeyV2,
    /// Hex identity of `key_v4`.
    pub key_v4_id: String,
    /// Admission bindings (`admission_bindings`): every one is evaluated on the prepared data and the tiny cases; the
    /// first is the default of local jobs.
    pub bindings: Vec<Binding>,
    /// Indices into `bindings` of the measured (benchmark) bindings: the user's benchmark bindings in request order;
    /// without them the first binding (a concrete statement's one binding; for a template without benchmark bindings,
    /// which only the correctness objective allows, its timings are descriptive). Evaluations score these bindings at
    /// every configured worker count, and the final measurement serves them.
    pub benchmark: Vec<usize>,
    /// Just outside each declared bound (where the type allows): the verified entry must answer `ParamRefused`.
    pub refusal_probes: Vec<Binding>,
}

impl Statement {
    /// No free parameter.
    pub fn concrete(&self) -> bool {
        self.instance.free.is_empty()
    }

    /// The names of the benchmark bindings, in order.
    pub fn benchmark_names(&self) -> Vec<&str> {
        self.benchmark.iter().map(|&b| self.bindings[b].name.as_str()).collect()
    }

    /// Header identity of the generated framework files (comments only; the statement key is not repeated there).
    pub fn identity(&self) -> String {
        "this statement".to_string()
    }

    /// The same statement with every free parameter fixed at `binding` (substituted in the AST, never in SQL text).
    pub fn fixed_at(&self, binding: &Binding) -> Result<AstDocument, AdmissionError> {
        let mut declarations = self.declarations.clone();
        for free in &self.instance.free {
            let declaration = declarations
                .iter_mut()
                .find(|d| d.index == free.index)
                .ok_or_else(|| AdmissionError::tool("free parameter without declaration"))?;
            declaration.binding = params::Binding::Fixed(binding.values[free.slot].clone());
        }
        let fixed = params::instantiate(&self.template, &declarations).map_err(AdmissionError::tool)?;
        if !fixed.free.is_empty() {
            return Err(AdmissionError::tool("a fully fixed instance still has free parameters"));
        }
        Ok(fixed.doc)
    }

    /// Every declared parameter's value at `binding`, in placeholder-index order: `(index, type, value)`.
    pub fn all_values(&self, binding: &Binding) -> Vec<(u32, ParamType, ParamValue)> {
        self.declarations
            .iter()
            .map(|d| {
                let value = match &d.binding {
                    params::Binding::Fixed(value) => value.clone(),
                    params::Binding::Free { .. } => {
                        let free = self.instance.free.iter().find(|f| f.index == d.index).expect("a free declaration is a free parameter");
                        binding.values[free.slot].clone()
                    }
                };
                (d.index, d.ty, value)
            })
            .collect()
    }

    /// The free parameters as recorded: index, slot, type and domain (bound texts, or the text domain).
    pub fn free_json(&self) -> Value {
        json!(self.instance.free.iter().map(|f| {
            let mut record = json!({"index":f.index,"slot":f.slot,"type":f.ty.sql_name()});
            record.as_object_mut().expect("an object").extend(domain_json(f.ty, &f.domain));
            record
        }).collect::<Vec<_>>())
    }

    /// The full parameter declaration as recorded: fixed values and free domains (with their slots).
    pub fn declaration_json(&self) -> Value {
        json!(self.declarations.iter().map(|d| match &d.binding {
            params::Binding::Fixed(v) => json!({"index":d.index,"type":d.ty.sql_name(),"binding":{"fixed":d.ty.text(v)}}),
            params::Binding::Free { domain } => json!({"index":d.index,"type":d.ty.sql_name(),
                "binding":{"free":Value::Object(domain_json(d.ty, domain))},
                "slot":self.instance.free.iter().find(|f| f.index == d.index).map(|f| f.slot)}),
        }).collect::<Vec<_>>())
    }

    /// The declared integrity constraints as every record of the statement reports them: `"none"`, or the trust mode,
    /// the declarations and `constraints_digest` (the identity of the generated `gendb_constraints.rs`).
    pub fn integrity_constraints_json(&self) -> Value {
        match (&self.integrity_constraints, self.key_v4.constraints_digest()) {
            (Some(constraints), Some(digest)) => json!({"trust":constraints.trust,"declarations":constraints.declarations,
                "constraints_digest":digest.to_hex(),
                "basis":"assumed about the full source tables as declared by the user; never checked against the data"}),
            _ => json!("none"),
        }
    }

    /// `(table, delivered ordinals)` of every delivered source table, in declaration order.
    pub fn source_projection(&self) -> Vec<(String, Vec<usize>)> {
        self.source.tables.iter().map(|t| (t.name.clone(), t.columns.iter().map(|c| c.ordinal).collect())).collect()
    }
}

/// Translate, bind and analyze one statement, writing its evidence under `directory` (`schema.sql`, `query.sql`,
/// `parameters.json`, `ast.json`, `statement.json`). `constraints` are the request's declared integrity constraints:
/// validated here first (`IntegrityConstraints::validate`: the trusted mode and the structural rules, the same as at
/// request load), so every caller, including admission's fresh translation and serving, applies the same rules before
/// any translation; a violation is refused at stage `integrity_constraints`. `test_bindings` and `benchmark` are the
/// request's admission test bindings and the user's benchmark bindings (`admission_bindings`). Evidence is written
/// once: when `directory` already holds a statement (a resumed controller, a second serving run), a fresh sibling
/// `<name>-<unix ms>` is used.
#[allow(clippy::too_many_arguments)]
pub fn prepare_statement(
    parser: &SqlParser,
    dataset: &DatasetSpec,
    constraints: Option<&IntegrityConstraints>,
    sql: &str,
    parameters: &[ParamRequest],
    test_bindings: &[Vec<String>],
    benchmark: &[BenchmarkBinding],
    directory: &Path,
) -> Result<Statement, Refused> {
    if let Some(constraints) = constraints {
        constraints.validate(dataset).map_err(|error| Refused::at(AdmissionError::unsupported(format!("integrity_constraints: {error}")), json!({"stage":"integrity_constraints","error":error})))?;
    }
    let directory = fresh_evidence_directory(directory);
    let (schema_ddl, omitted_tables) = dataset_ddl(dataset, constraints);
    create_dir(&directory)?;
    let (schema_file, sql_file) = (directory.join("schema.sql"), directory.join("query.sql"));
    write_text(&schema_file, &schema_ddl)?;
    write_text(&sql_file, sql)?;
    write_new_json(&directory.join("parameters.json"), &parameters)?;
    let placeholders: Vec<_> = parameters.iter().map(ParamRequest::placeholder).collect();
    let (ast_text, translation) = parser
        .translate(&schema_file, &sql_file, DIALECT, &placeholders)
        .map_err(|e| AdmissionError::tool(format!("VERUS_SQL frontend: {e}")))?;
    let ast_file = directory.join("ast.json");
    write_text(&ast_file, &ast_text)?;
    let template = match translation {
        Translation::Ok(doc) => doc,
        Translation::Refused(r) => {
            return Err(Refused::at(
                AdmissionError::unsupported(format!("VERUS_SQL frontend refusal {} at {} ({})", r.reason, r.path, r.detail)),
                json!({"stage":"frontend","refusal":{"reason":r.reason,"detail":r.detail,"path":r.path},"omitted_tables":omitted_tables,"ast":ast_file}),
            ));
        }
    };
    let refuse = |stage: &str, error: String| {
        Refused::at(AdmissionError::unsupported(format!("{stage}: {error}")), json!({"stage":stage,"error":error}))
    };
    if let Some(constraints) = constraints {
        constraints.check_translation(&template.tables).map_err(|e| refuse("integrity_constraints", e))?;
    }
    let declarations = params::declare(&template, parameters).map_err(|e| refuse("parameters", e.to_string()))?;
    let instance = params::instantiate(&template, &declarations).map_err(|e| refuse("parameters", e.to_string()))?;
    let demand = columns::analyze(&instance.doc).map_err(|e| refuse("column_demand", e.to_string()))?;
    let source = columns::source_declaration(&instance.doc, &demand).map_err(|e| refuse("source_binding", e.to_string()))?;
    let key = statement_key(&instance).map_err(AdmissionError::tool)?;
    let key_id = key.identity().map_err(AdmissionError::tool)?.to_hex();
    let key_v4 = statement_key_v4(&instance).map_err(AdmissionError::tool)?;
    let key_v4_id = key_v4.identity().map_err(AdmissionError::tool)?.to_hex();
    let bindings = admission_bindings(&instance.free, test_bindings, benchmark).map_err(|e| match e {
        BindingError::TestBinding(reason) => refuse("bindings", reason),
        other => AdmissionError::tool(other).into(),
    })?;
    let refusal_probes = refusal_probes(&instance.free).map_err(AdmissionError::tool)?;
    let benchmark = if benchmark.is_empty() { vec![0] } else { (0..benchmark.len()).collect() };
    let statement = Statement {
        sql: sql.to_string(),
        parameters: parameters.to_vec(),
        directory,
        schema_ddl,
        integrity_constraints: constraints.cloned(),
        template,
        declarations,
        instance,
        demand,
        source,
        key,
        key_id,
        key_v4,
        key_v4_id,
        bindings,
        benchmark,
        refusal_probes,
    };
    write_new_json(&statement.directory.join("statement.json"), &json!({"format_version":1,"sql":statement.sql,
        "statement_key":statement.key_id,"statement_key_v4":statement.key_v4_id,"declaration":statement.declaration_json(),"free_parameters":statement.free_json(),
        "source_declaration":statement.source,"admission_bindings":statement.bindings,"benchmark_bindings":statement.benchmark_names(),"refusal_probes":statement.refusal_probes,
        "integrity_constraints":statement.integrity_constraints_json(),
        "note":"one statement instance: fixed parameters substituted in the AST; the same instance drives source demand, author inputs, references, evaluation, records and serving"}))?;
    Ok(statement)
}

fn fresh_evidence_directory(directory: &Path) -> PathBuf {
    if !directory.join("statement.json").exists() {
        return directory.to_owned();
    }
    let name = directory.file_name().map(|n| n.to_string_lossy().to_string()).unwrap_or_default();
    directory.with_file_name(format!("{name}-{}", now_unix_ms()))
}

/// A free domain as recorded: `{"min", "max"}` canonical texts (unchanged form), or `{"domain"}` for text, which has no
/// bounds.
fn domain_json(ty: ParamType, domain: &ParamDomain) -> serde_json::Map<String, Value> {
    let record = match domain {
        ParamDomain::Range { min, max } => json!({"min":ty.text(min),"max":ty.text(max)}),
        ParamDomain::AllText => json!({"domain":"every text value without a NUL byte (no bounds: text order depends on the collation)"}),
    };
    let Value::Object(fields) = record else { unreachable!("a JSON object") };
    fields
}

/// Identifier as PostgreSQL/DataFusion SQL text (quoted unless plain lower-case).
pub fn sql_ident(name: &str) -> String {
    let plain = name.chars().next().is_some_and(|c| c.is_ascii_lowercase() || c == '_')
        && name.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_');
    if plain { name.to_string() } else { format!("\"{}\"", name.replace('"', "\"\"")) }
}

/// PostgreSQL DDL of the dataset's declared tables, in dataset order (table id = position), and the tables left out.
/// A table with a column type outside SQLSpec's fragment is left out (listed); a statement reading it is then refused
/// by the frontend (`unknown_table`), never translated against a guessed type. After every CREATE TABLE, one
/// `ALTER TABLE <table> ADD <clause>;` per declared integrity constraint, in request order; without declarations the
/// text is the CREATE TABLEs alone, as before constraints could be declared.
pub fn dataset_ddl(dataset: &DatasetSpec, constraints: Option<&IntegrityConstraints>) -> (String, Vec<Value>) {
    let (mut ddl, mut omitted) = (String::new(), vec![]);
    'tables: for table in &dataset.tables {
        let mut columns = vec![];
        for c in &table.fields {
            let ty = match c.ty {
                ColType::Decimal { p, s } if s >= 0 && p >= 1 => format!("numeric({p},{s})"),
                ColType::Date32 => "date".into(),
                ColType::Bool => "boolean".into(),
                ColType::I32 => "integer".into(),
                ColType::I64 => "bigint".into(),
                ColType::Utf8 => "text".into(),
                other => {
                    omitted.push(json!({"table":table.name,"column":c.name,"type":format!("{other:?}")}));
                    continue 'tables;
                }
            };
            columns.push(format!("    {} {ty}{}", sql_ident(&c.name), if c.nullable { "" } else { " NOT NULL" }));
        }
        let _ = writeln!(ddl, "CREATE TABLE {} (\n{}\n);", sql_ident(&table.name), columns.join(",\n"));
    }
    for declaration in constraints.iter().flat_map(|c| &c.declarations) {
        let _ = writeln!(ddl, "ALTER TABLE {} ADD {};", sql_ident(&declaration.table), declaration.sql);
    }
    (ddl, omitted)
}

/// The statement's delivered columns in the shared prepared capture: a metadata-only read-only view, persisted once as
/// the view archive the worker maps for real-data builds.
#[derive(Clone)]
pub struct StatementInputs {
    pub source: Arc<PreparedSource>,
    pub columns: SourceColumns,
    /// `<query directory>/verus-inputs`.
    pub archive: PathBuf,
}

impl StatementInputs {
    /// Project the capture onto the statement's source declaration and write the view archive
    /// `<query_directory>/verus-inputs` unless it exists (no data copy or scan). A capture that lacks a delivered
    /// column is a tool failure naming the missing columns.
    pub fn project(statement: &Statement, source: Arc<PreparedSource>, query_directory: &Path) -> Result<Self, AdmissionError> {
        let columns = source
            .project_declaration(&statement.source)
            .map_err(|e| AdmissionError::tool(format!("the prepared capture does not cover the source declaration: {e}")))?;
        let archive = query_directory.join("verus-inputs");
        if !archive.exists() {
            columns.write_archive(&archive).map_err(AdmissionError::tool)?;
        }
        Ok(Self { source, columns, archive })
    }

    /// Captured row count of a delivered table.
    pub fn rows(&self, table: &str) -> Result<usize, AdmissionError> {
        self.columns
            .bindings()
            .iter()
            .find(|b| b.table == table)
            .map(|b| b.row_count)
            .ok_or_else(|| AdmissionError::missing_input(format!("prepared input for table {table} absent")))
    }
}
