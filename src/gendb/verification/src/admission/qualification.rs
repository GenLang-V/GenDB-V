//! Qualification: library records and admission of one evaluated candidate (ABI v3).
//!
//! In order: the TCB record; the build record of the candidate's one whole-crate verify-and-compile run (checked as
//! admissible evidence); its representation; the implementation records (the fixed entry and each author module);
//! the asset for the current source versions; then a fresh translation of the SQL must reproduce the statement key,
//! and its fresh framework generation is what admission compares byte for byte with the build's framework files;
//! finally the statement key, the SQL claim, the package and its admission.

use super::preflight::QueryPreflight;
use super::records::now_unix_ms;
use super::statement::{StatementInputs, prepare_statement};
use super::{AdmissionError, Refused};
use crate::obligations::{DeclaredSource, TrustedAssumption, ENTRY_IDENTITY, ENTRY_SOURCE, THEOREMS, TRUSTED_ASSUMPTIONS, candidate_framework_files};
use crate::verus::{FrozenCrate, VERUS_REFUSAL_RULES, VerusToolchain, verus_pin};
use gendb_artifacts::verus::{
    self as records, RecordError, VerusBuildInput, VerusBuildPurposeV1, VerusImplementationV1, VerusItemV1, VerusPackageAdmissionV1, VerusQueryPackageV2,
    VerusRepresentationV2, VerusSourceOwnerV1, VerusSourceTableV2, VerusSqlClaimInput, VerusTcbV1, VerusTrustedItemV1,
};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::{ABI_VERSION, MAX_WORKERS};
use gendb_runtime::identity::runtime_build_identity;
use gendb_runtime::serve::parameter_declaration;
use gendb_sqlspec::evaluator::CRATE_IDENTITY;
use gendb_storage::io::PartsManifest;
use serde::Serialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Gate identity of every package admission written here.
pub const GATE_IDENTITY: &str = "gendb.verus.integrated-qualification.v3";
/// Crate name of candidate builds (Verus `--crate-name`); item paths in records start with it.
const CANDIDATE_CRATE: &str = crate::obligations::CANDIDATE_CRATE_NAME;
/// Entry items recorded with their `requires`/`ensures` text in the entry's implementation record.
const RECORDED_ENTRY_ITEMS: [&str; 4] = ["abi_build", "abi_query", "theorem_end_to_end", "corollary_inside_capacity"];

/// Lexical `requires`/`ensures` clause text of the item `name` in a Verus source (`None` when not unique). Supplied by
/// the caller's item extractor; used for descriptive records only.
pub type ClauseText<'a> = &'a dyn Fn(&str, &str) -> Option<(Vec<String>, Vec<String>)>;

/// One author module of the frozen crate with the checked items it declared.
#[derive(Clone, Debug)]
pub struct CandidateModule {
    /// Relative to `src/agent/`.
    pub file: String,
    pub role: String,
    pub items: Vec<VerusItemV1>,
}

/// The asset qualification publishes: stored parts built by the candidate's builder over the current prepared data.
#[derive(Clone, Debug)]
pub struct AssetEvidence {
    pub parts: PathBuf,
    pub manifest: PartsManifest,
    pub build_wall_ns: u64,
    /// The asset's evaluation record (stored as build evidence).
    pub record: Value,
}

/// What qualification needs of one evaluated candidate.
pub struct QualificationInput<'a> {
    pub frozen: &'a FrozenCrate,
    /// The persisted record of the build's one verify-and-compile run (`VerusRun::record` keys: argv, environment,
    /// exit_code, stdout, wall_ns, artifact).
    pub verus_run: &'a Value,
    pub representation_name: String,
    /// One label per stored part, in builder output order.
    pub part_labels: Vec<String>,
    pub modules: Vec<CandidateModule>,
    pub asset: AssetEvidence,
    /// The evaluation record (`evaluation_record`, `real_data`, `boundary`, `parameter_refusals`, `verus`).
    pub evaluation: &'a Value,
    /// Framework helper names the agent sources mention (lexical, descriptive).
    pub helpers_referenced: Vec<String>,
    /// The request's live data allowance in bytes, if one was given.
    pub live_bytes_allowance: Option<u64>,
}

/// Where qualification runs: the admitted library, the statement's prepared inputs and the frontend.
pub struct QualificationContext<'a> {
    pub library: &'a Path,
    pub preflight: &'a QueryPreflight,
    pub inputs: &'a StatementInputs,
    pub parser: &'a SqlParser,
    pub clause_text: ClauseText<'a>,
}

/// Every record id of an admitted package.
#[derive(Clone, Debug, Serialize)]
pub struct Qualification {
    pub admission: ContentId,
    pub package: ContentId,
    pub statement: ContentId,
    pub claim: ContentId,
    pub build: ContentId,
    pub tcb: ContentId,
    pub representation: ContentId,
    pub implementations: Vec<ContentId>,
    pub asset: ContentId,
    pub qualification_evidence: ContentId,
    pub statement_key: String,
}

impl Qualification {
    /// Record form (the earlier version's qualification result).
    pub fn record(&self) -> Value {
        json!({"qualified":true,"kind":"verus","abi_version":ABI_VERSION,"admission":self.admission,"package":self.package,
            "statement":self.statement,"claim":self.claim,"build":self.build,"tcb":self.tcb,"representation":self.representation,
            "implementations":self.implementations,"asset":self.asset,"qualification_evidence":self.qualification_evidence,"statement_key":self.statement_key,
            "proof_link":"the build record stores the frozen sources, the raw Verus JSON (0 errors, entire crate, including gendb_entry::theorem_end_to_end over the actual entry and agent code) and the library compiled by that same invocation; the claim names that build and the statement key; admission compared every framework file byte-for-byte with a fresh generation from a fresh translation of the SQL"})
    }
}

/// A record the store refused: a broken publication or admission rule refuses the candidate; a store failure is the
/// framework's.
pub(super) fn record_error(e: RecordError) -> AdmissionError {
    match e {
        RecordError::BuildEvidence(_) | RecordError::Rejected(_) => AdmissionError::refusal(e),
        RecordError::CurrentSource(_) => AdmissionError::missing_input(e),
        _ => AdmissionError::tool(e),
    }
}

pub(super) fn store_error(e: impl std::fmt::Display) -> AdmissionError {
    AdmissionError::tool(e)
}

/// Publish every record of an evaluated candidate and admit its package.
pub fn qualify(context: &QualificationContext<'_>, input: QualificationInput<'_>) -> Result<Qualification, AdmissionError> {
    let statement = &context.preflight.statement;
    let store = ObjectStore::open(context.library).map_err(store_error)?;
    let toolchain = VerusToolchain::from_env().map_err(AdmissionError::tool)?;
    let tcb = store.put(1, records::VERUS_TCB_KIND, &tcb_record()?).map_err(store_error)?;
    let sources = input
        .frozen
        .framework_files
        .iter()
        .map(|p| (p.clone(), VerusSourceOwnerV1::Framework))
        .chain(input.frozen.agent_files.iter().map(|p| (format!("agent/{p}"), VerusSourceOwnerV1::Agent)))
        .collect();
    let build = publish_checked_build(&store, &toolchain, tcb, &input.frozen.root, sources, input.verus_run)?;
    let (representation, representation_record) = publish_representation(&store, build, context, &input)?;
    let implementations = publish_implementations(&store, build, context, &input)?;
    let asset = publish_asset(&store, representation, &representation_record, context, &input)?;
    let fresh_framework = fresh_framework(context)?;
    let statement_id = records::publish_statement_key(&store, &statement.key).map_err(record_error)?;
    let claim = records::publish_claim(&store, VerusSqlClaimInput {
        statement: statement_id,
        build,
        theorems: THEOREMS.iter().map(|t| t.to_string()).collect(),
        sql: statement.sql.clone(),
        frontend: statement.instance.doc.frontend.clone(),
        schema_ddl: &statement.schema_ddl,
        parameters: parameter_declaration(&statement.declarations),
        source: serde_json::to_value(DeclaredSource::of_statement(&statement.instance.doc, &statement.source).map_err(AdmissionError::tool)?)
            .map_err(AdmissionError::tool)?,
    })
    .map_err(record_error)?;
    let package = store
        .put(1, records::VERUS_QUERY_PACKAGE_V2_KIND, &VerusQueryPackageV2 {
            statement: statement_id,
            claim,
            entry_identity: ENTRY_IDENTITY.into(),
            build,
            representation,
            implementations: implementations.clone(),
            abi_version: ABI_VERSION,
            workers: (1, MAX_WORKERS as u32),
            tcb,
        })
        .map_err(store_error)?;
    let evaluation = input.evaluation;
    let qualification_evidence = store
        .put(1, "gendb.verus.qualification-evidence.v1", &json!({"evaluation_record":evaluation["evaluation_record"],
            "real_data":evaluation["real_data"],"tiny_cases":evaluation["boundary"],"parameter_refusals":evaluation["parameter_refusals"],"verus":evaluation["verus"],
            "framework_helpers_referenced":input.helpers_referenced,"statement":statement.directory.join("statement.json"),
            "preflight":statement.directory.join("preflight.json")}))
        .map_err(store_error)?;
    let expected: Vec<(&str, &str)> = fresh_framework.iter().map(|f| (f.path.as_str(), f.text.as_str())).collect();
    let admission = records::admit_package_v3(
        &store,
        &VerusPackageAdmissionV1 { package, gate_identity: GATE_IDENTITY.into(), qualification_evidence: vec![qualification_evidence], assets: vec![asset] },
        &expected,
    )
    .map_err(record_error)?;
    Ok(Qualification {
        admission,
        package,
        statement: statement_id,
        claim,
        build,
        tcb,
        representation,
        implementations,
        asset,
        qualification_evidence,
        statement_key: statement.key_id.clone(),
    })
}

/// The build record of one whole-crate verify-and-compile run over the frozen crate at `frozen_root` (`sources`:
/// every file relative to `src/` with its owner; `verus_run`: the persisted run record, `VerusRun::record` keys argv,
/// environment, exit_code, stdout, wall_ns, artifact), checked as admissible evidence.
pub(super) fn publish_checked_build(
    store: &ObjectStore,
    toolchain: &VerusToolchain,
    tcb: ContentId,
    frozen_root: &Path,
    sources: Vec<(String, VerusSourceOwnerV1)>,
    verus_run: &Value,
) -> Result<ContentId, AdmissionError> {
    let run = verus_run;
    let library = PathBuf::from(run["artifact"].as_str().ok_or_else(|| AdmissionError::tool("verus run has no library"))?);
    let argv: Vec<String> = serde_json::from_value(run["argv"].clone()).map_err(AdmissionError::tool)?;
    let environment: BTreeMap<String, String> = serde_json::from_value(run["environment"].clone()).map_err(AdmissionError::tool)?;
    let build = records::publish_build(store, VerusBuildInput {
        purpose: VerusBuildPurposeV1::Candidate,
        provider_identity: toolchain.version().map_err(AdmissionError::tool)?.to_string(),
        argv,
        environment,
        exit_code: run["exit_code"].as_i64().map(|c| c as i32),
        stdout: run["stdout"].as_str().unwrap_or_default(),
        frozen_directory: frozen_root,
        sources,
        library_path: &library,
        wall_ns: run["wall_ns"].as_u64().unwrap_or(0),
        tcb,
    })
    .map_err(record_error)?;
    records::check_build_evidence(store, build).map_err(record_error)?;
    Ok(build)
}

/// The representation record: the declared source tables with the dataset's field declarations.
fn publish_representation(
    store: &ObjectStore,
    build: ContentId,
    context: &QualificationContext<'_>,
    input: &QualificationInput<'_>,
) -> Result<(ContentId, VerusRepresentationV2), AdmissionError> {
    let dataset = context.inputs.source.dataset();
    let mut sources = vec![];
    for t in &context.preflight.statement.source.tables {
        let table = dataset.table(&t.name).ok_or_else(|| AdmissionError::missing_input("source schema absent"))?;
        let fields = t
            .columns
            .iter()
            .map(|c| table.fields.get(c.ordinal).cloned().map(|f| (c.ordinal, f)).ok_or_else(|| AdmissionError::missing_input("source field absent")))
            .collect::<Result<_, _>>()?;
        sources.push(VerusSourceTableV2 { table: t.name.clone(), fields });
    }
    let representation = VerusRepresentationV2 {
        build,
        name: input.representation_name.clone(),
        sources,
        parts: input.part_labels.clone(),
        decode_item: format!("{CANDIDATE_CRATE}::agent::decode"),
        builder_item: format!("{CANDIDATE_CRATE}::agent::build"),
    };
    let id = records::publish_representation_v2(store, &representation).map_err(record_error)?;
    Ok((id, representation))
}

/// The fixed entry's implementation record (its SQL operations and checked items) and one per author module.
fn publish_implementations(store: &ObjectStore, build: ContentId, context: &QualificationContext<'_>, input: &QualificationInput<'_>) -> Result<Vec<ContentId>, AdmissionError> {
    let entry_items = RECORDED_ENTRY_ITEMS
        .iter()
        .map(|name| {
            let (requires, ensures) = (context.clause_text)(ENTRY_SOURCE, name).ok_or_else(|| AdmissionError::tool("entry clause text absent"))?;
            Ok(VerusItemV1 { path: format!("{CANDIDATE_CRATE}::gendb_entry::{name}"), requires, ensures })
        })
        .collect::<Result<Vec<_>, AdmissionError>>()?;
    let entry = VerusImplementationV1 { build, module: "gendb_entry".into(), operations: statement_operations(context.preflight), items: entry_items };
    let mut implementations = vec![store.put(1, records::VERUS_IMPLEMENTATION_KIND, &entry).map_err(store_error)?];
    for module in &input.modules {
        let record = VerusImplementationV1 { build, module: format!("agent/{} ({})", module.file, module.role), operations: vec![], items: module.items.clone() };
        implementations.push(store.put(1, records::VERUS_IMPLEMENTATION_KIND, &record).map_err(store_error)?);
    }
    Ok(implementations)
}

/// The published asset for the current source versions, or a new publication of the evaluated one.
fn publish_asset(
    store: &ObjectStore,
    representation: ContentId,
    representation_record: &VerusRepresentationV2,
    context: &QualificationContext<'_>,
    input: &QualificationInput<'_>,
) -> Result<ContentId, AdmissionError> {
    let asset = &input.asset;
    if let Some(allowance) = input.live_bytes_allowance
        && asset.manifest.storage_bytes > allowance
    {
        return Err(AdmissionError::refusal(format!(
            "asset storage {} bytes exceeds the request's live data allowance {allowance}",
            asset.manifest.storage_bytes
        )));
    }
    let source = &context.inputs.source;
    let current = |table: &str| -> Result<(String, usize), String> {
        let version = source.source_version(table).ok_or_else(|| format!("missing_input: source version of {table} absent"))?;
        Ok((version.to_string(), context.inputs.rows(table).map_err(|e| e.to_string())?))
    };
    let key = records::VerusAssetKeyV2::current(representation, representation_record, &current).map_err(record_error)?;
    if let Some((id, _)) = records::resolve_asset_v2(store, &key).map_err(record_error)? {
        return Ok(id);
    }
    let evidence = store
        .put(1, "gendb.verus.asset-build-evidence.v1", &json!({"evaluation":input.evaluation["evaluation_record"],"asset":asset.record}))
        .map_err(store_error)?;
    records::publish_asset_v2(store, key, asset.parts.clone(), asset.build_wall_ns as u128, asset.manifest.storage_bytes, evidence).map_err(record_error)
}

/// The SQL translated again now: the fresh instance must have the same statement key; its framework generation is
/// what admission compares with the build's framework files.
fn fresh_framework(context: &QualificationContext<'_>) -> Result<Vec<crate::verus::FrameworkSource>, AdmissionError> {
    let statement = &context.preflight.statement;
    let directory = statement.directory.join(format!("admission-{}", now_unix_ms()));
    let constraints = statement.integrity_constraints.as_ref();
    let fresh = prepare_statement(context.parser, context.inputs.source.dataset(), constraints, &statement.sql, &statement.parameters, &[], &[], &directory)
        .map_err(|Refused { error, .. }| AdmissionError::refusal(format!("the SQL no longer translates at admission: {error}")))?;
    if fresh.key != statement.key {
        return Err(AdmissionError::refusal("the SQL no longer translates to the checked statement instance"));
    }
    candidate_framework_files(&fresh.instance, &fresh.source, &fresh.identity()).map_err(AdmissionError::tool)
}

/// SQL operations of the statement (from the AST, generic; a descriptive record of what the fixed entry covers).
pub fn statement_operations(preflight: &QueryPreflight) -> Vec<String> {
    let statement = &preflight.statement;
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for n in &statement.instance.doc.nodes {
        if matches!(n.tag.as_str(), "Table" | "Filter" | "Project" | "Product" | "LeftJoin" | "Aggregate" | "GroupBy" | "Distinct" | "Exists" | "AnyCmp" | "Subquery" | "OrderedQuery") {
            *counts.entry(n.tag.as_str()).or_default() += 1;
        }
    }
    let mut operations: Vec<String> = statement
        .source
        .tables
        .iter()
        .map(|t| format!("Scan {} columns [{}]", t.name, t.columns.iter().map(|c| c.name.as_str()).collect::<Vec<_>>().join(", ")))
        .collect();
    operations.extend(counts.iter().map(|(tag, n)| format!("{tag} x{n}")));
    if !statement.instance.free.is_empty() {
        operations.push(format!("free parameters {}", statement.instance.free.iter().map(|f| format!("${}", f.index)).collect::<Vec<_>>().join(", ")));
    }
    operations
}

/// The TCB record of the verified path (entry v3): every trusted item of the claim with its identity.
pub fn tcb_record() -> Result<VerusTcbV1, AdmissionError> {
    let runtime = runtime_build_identity();
    let mut items = framework_trusted_items();
    for (id, item) in gendb_runtime::trusted_items() {
        items.push(VerusTrustedItemV1 { id: id.into(), item: item.into(), identity: format!("verus abi v{ABI_VERSION} host ({runtime})"), reason: "host side of the v3 ABI".into() });
    }
    items.extend(entry_assumptions(TRUSTED_ASSUMPTIONS, ENTRY_IDENTITY));
    Ok(VerusTcbV1 { items, refusal_rules: serde_json::to_value(VERUS_REFUSAL_RULES).map_err(AdmissionError::tool)? })
}

/// The trusted items every entry's claim shares: toolchain, semantics, frontend, dataset DDL, column demand, canonical
/// data, result codec, storage immutability, OS and the framework's static checks.
pub(super) fn framework_trusted_items() -> Vec<VerusTrustedItemV1> {
    let pin = verus_pin();
    let runtime = runtime_build_identity();
    let verus = format!("{} ({})", pin.verus.version, pin.verus.commit);
    let rows: [(&str, &str, String, &str); 13] = [
        ("rustc_llvm", "rustc + LLVM + linker; Rust std/alloc/core", pin.rust.toolchain.clone(), "compiles the ghost-erased crate; implements Vec, slices and threads"),
        ("verus", "Verus driver (rust_verify), VIR, ghost erasure, lifetime checks and termination checks (decreases on every exec loop and recursive function, call-graph cycle checks). Soundness for author code also relies on the author-source scan (refusal list) refusing the forms where the pinned release misses call-graph edges, the known Verus cycle-check gaps: trait objects (Verus PR #3053), bounds on associated types (PR #3063), std/vstd calls into author trait impls without their preconditions or outside the call graph (issues #3138, #3139; Drop, PartialEq and other external trait impls), and opaque impl Trait return types; an unknown gap is not covered", verus.clone(), "decides validity of the whole crate and enforces termination of its verified code"),
        ("z3", "Z3 SMT solver used by Verus", pin.z3.version.clone(), "SMT solving"),
        ("vstd", "vstd specifications, including its own assume_specification/external_body items (thread spawn/join, Vec, slices, integer operations)", verus, "models of std"),
        ("sql_semantics_spec", "SQLSpec spec/** definitions (denote_body, ordered_ok, value/numeric/date/text semantics, db_wf) and the fixed source/answer definitions of link (gendb_verification::obligations::FIXED_LINK_DEFINITIONS, with the value view exec::value::{EVal, view_row}), embedded byte-for-byte into the crate (gendb_sqlspec::library)", CRATE_IDENTITY.into(), "the meaning of SQL the theorem is stated in"),
        ("sql_frontend", "SQLGlot + GenDB resolver (gendb_frontend::parser): SQL text with typed placeholders -> AST document (normalizations, types, PostgreSQL rules); fixed-parameter substitution in the AST (gendb_frontend::params::instantiate); the translator AST -> query.rs (query_spec_at, param_domain)", "gendb-sql-frontend (recorded in the claim's frontend field)".into(), "defines which AST the SQL denotes (trusted after review and focused tests; not a proved parser); well-typedness at every admitted binding is checked (lemma_query_wf_at)"),
        ("dataset_ddl", "gendb_verification::admission::dataset_ddl: declared dataset schema -> PostgreSQL DDL (Utf8 -> text, Decimal -> numeric(p,s), Date32 -> date, I32/I64 -> integer/bigint, nullability), then one ALTER TABLE <table> ADD <clause> per declared integrity constraint of the request, in request order (none without declarations)", "framework".into(), "the declared schema the claim is about"),
        ("column_demand", "gendb_frontend::columns: which source columns are delivered (the AST column demand). Not trusted for soundness: an omitted needed column makes the claim unprovable, never wrong", "gendb-frontend columns".into(), "decides provability and what the host binds"),
        ("canonical_data", "trusted import and canonical capture: Parquet/Arrow -> prepared capture (gendb_storage::import) -> native columns (gendb_storage::io::SourceColumns), including Utf8 offsets/bytes and UTF-8 validity (canonical_text) and each nullable column's per-row NULL validity (one byte per row: 1 valid, 0 NULL, from Arrow's null buffer)", runtime.to_string(), "supplies input rows"),
        ("result_codec", "GSQLRS1 result wire decoding (gendb_sqlspec::codec::decode_result) and PostgreSQL output text rendering (gendb_sqlspec::pg_text)", "gendb-sqlspec codec".into(), "the rows the host reports"),
        ("storage", "local artifact immutability (installed toolchain, frozen crate, stored objects, asset files); storage round trip of asset parts; source-version stamp (file metadata, no hashing)", "framework".into(), "no re-hashing by design"),
        ("os", "Linux/pthreads: thread creation, join happens-before, fair scheduling, mmap stability, abort on OOM/stack/thread-creation failure", "host".into(), "runtime assumptions"),
        ("framework_checks", "Verus --no-cheating behaviour, the refusal-list scanner, framework-file byte comparison at admission, lexical spec-text extraction for records", "framework".into(), "static checks, not proofs"),
    ];
    rows.into_iter()
        .map(|(id, item, identity, reason)| VerusTrustedItemV1 { id: id.into(), item: item.into(), identity, reason: reason.into() })
        .collect()
}

/// The named assumptions of the fixed entry `entry_identity` as TCB items (`entry_assumption:<id>`).
pub(super) fn entry_assumptions(assumptions: &[TrustedAssumption], entry_identity: &str) -> Vec<VerusTrustedItemV1> {
    assumptions
        .iter()
        .map(|assumption| VerusTrustedItemV1 {
            id: format!("entry_assumption:{}", assumption.id),
            item: assumption.statement.into(),
            identity: entry_identity.into(),
            reason: format!("relied on by {}", assumption.relied_on_by),
        })
        .collect()
}
