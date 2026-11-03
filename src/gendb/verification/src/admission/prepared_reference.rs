//! The independent exact reference on the prepared data, at every admission binding. Tests, not proof: the SQL meaning
//! is SQLSpec; DataFusion is neither a fallback engine nor a meaning.
//!
//! Chosen at preflight ([`choose_mode`]), before any author call:
//! - [`PreparedMode::Direct`]: every output column is exact-typed under DataFusion ([`direct::applicable`]): DataFusion
//!   executes the SQL with its own typed parameter binding at each binding, LIMIT/OFFSET removed; values convert
//!   exactly to the output types; rows are sorted by the ORDER BY keys.
//! - [`PreparedMode::Rewrite`]: a statement with a non-exact output: the SUM/COUNT rewrite (DataFusion aggregates
//!   exactly, with the same typed parameter binding at each binding) finalized by a verified evaluator that computes
//!   the scalar arithmetic over the aggregates ([`rewrite`]).
//! - otherwise the statement is refused before any author call (`no_independent_reference`).
//!
//! The SQLSpec interpreter itself is a reference for tiny inputs only; it is never run over the prepared data.
//! Every comparison accepts exactly the outputs `ordered_ok` allows; a binding without an exact reference is reported as
//! status-only, never as result correctness.

pub mod arrow_values;
pub mod direct;
pub mod rewrite;

use super::preflight::QueryPreflight;
use super::records::{create_dir, write_new_json, write_text};
use super::bindings::Binding;
use super::statement::Statement;
use super::{AdmissionError, Refused};
use crate::reference::{BuildOptions, BuildStatus, build_evaluator};
use crate::verus::VerusToolchain;
use datafusion::common::ScalarValue;
use gendb_frontend::ast::{AstDocument, PgType, Translation};
use gendb_frontend::parser::SqlParser;
use gendb_sqlspec::codec::{HostValue, RunOutcome};
use gendb_sqlspec::evaluator::EvaluatorLibrary;
use gendb_storage::import::SqlReference;
use rewrite::{FinalizationType, REWRITE_IDENTITY, RewritePlan};
use serde_json::{Value, json};
use std::fmt;
use std::path::{Path, PathBuf};
use std::time::Instant;

/// Crate name of the rewrite's finalization evaluator.
const FINALIZATION_CRATE_NAME: &str = "gendb_query_oracle";

/// How the prepared-data reference is computed.
#[derive(Clone, Debug)]
pub enum PreparedMode {
    /// DataFusion on the SQL with its own typed parameter binding (exact-typed outputs).
    Direct,
    /// Non-exact outputs: SUM/COUNT rewrite (bound at each binding) + verified finalization (`library`).
    Rewrite { plan: Box<RewritePlan>, types: Vec<FinalizationType>, library: PathBuf },
    /// No reference is computed: the run's validation policy is `formal_proofs` ([`super::validation`]).
    NotComputed,
}

impl PreparedMode {
    /// Recorded name of the mode.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Direct => "datafusion_direct",
            Self::Rewrite { .. } => "sum_count_rewrite",
            Self::NotComputed => "not_computed_validation_policy",
        }
    }
}

/// The exact full ordered body at one binding (ORDER BY applied, OFFSET/LIMIT not applied) and how it was computed.
#[derive(Clone, Debug)]
pub struct ExactReference {
    pub rows: Vec<Vec<HostValue>>,
    pub record: Value,
}

/// Why a binding has no exact reference (recorded; results there are status-only).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NoReference(pub String);

impl fmt::Display for NoReference {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// The prepared-data reference of one admission binding.
pub type BindingReference = Result<ExactReference, NoReference>;

/// Choose the reference mode of `statement` (a rewrite is planned, translated and its finalization evaluator built
/// under `<statement directory>/oracle`). `Err` refuses the statement: no exact reference exists.
pub async fn choose_mode(statement: &Statement, reference: &SqlReference, toolchain: &VerusToolchain, parser: &SqlParser) -> Result<PreparedMode, Refused> {
    let why = match direct::applicable(&statement.instance.doc) {
        Ok(()) => return Ok(PreparedMode::Direct),
        Err(why) => why,
    };
    let refuse = |detail: String| {
        Refused::at(AdmissionError::unsupported(format!("no_independent_reference: {why}; {detail}")), json!({"stage":"prepared_reference"}))
    };
    // Planned with the declared parameter types only; each binding's values are bound at execution.
    let parameter_types = parameter_types(statement).map_err(refuse)?;
    let derived = rewrite::derive(&statement.sql).map_err(refuse)?;
    let value_columns = match derived.value_columns_sql() {
        Some(sql) => reference.result_columns(&sql, &parameter_types).await.map_err(|e| refuse(format!("the rewrite's value columns do not plan: {e}")))?,
        None => vec![],
    };
    let plan = derived.resolve(&value_columns).map_err(refuse)?;
    let aggregation = reference
        .result_columns(&plan.aggregation_sql, &parameter_types)
        .await
        .map_err(|e| refuse(format!("the SUM/COUNT rewrite does not plan: {e}")))?;
    let types = rewrite::column_types(&plan, &aggregation).map_err(refuse)?;
    let (ddl, sql) = rewrite::finalization(&plan, &types);
    let directory = statement.directory.join("oracle");
    let doc = translate_finalization(parser, &ddl, &sql, &directory).map_err(|e| refuse(e.to_string()))?;
    same_value_kinds(&doc, &statement.instance.doc).map_err(refuse)?;
    let (library, _) = build_verified_evaluator(toolchain, &doc, &directory.join("ast.json"), &directory.join("build"), FINALIZATION_CRATE_NAME)
        .map_err(|e| refuse(e.to_string()))?;
    write_new_json(&directory.join("oracle.json"), &json!({"identity":REWRITE_IDENTITY,"plan":plan,"types":types,
        "finalization_ddl":ddl,"finalization_sql":sql,"library":library}))?;
    Ok(PreparedMode::Rewrite { plan: Box::new(plan), types, library })
}

/// The reference at every admission binding: one DataFusion execution of the SQL, or of the rewrite's aggregation
/// followed by its verified finalization, per binding. Each result is also written to
/// `<statement directory>/prepared-reference-<binding>.json`.
pub async fn prepared_references(preflight: &QueryPreflight, reference: &SqlReference) -> Vec<BindingReference> {
    let statement = &preflight.statement;
    let references = match &preflight.prepared {
        PreparedMode::Rewrite { plan, types, library } => rewrite_references(statement, plan, types, library, reference).await,
        PreparedMode::Direct => direct_references(preflight, reference).await,
        PreparedMode::NotComputed => statement.bindings.iter().map(|_| Err(NoReference(super::validation::NO_REFERENCE_BY_POLICY.into()))).collect(),
    };
    write_descriptive_copies(statement, &references);
    references
}

/// `<statement directory>/prepared-reference-<binding>.json` per binding. Descriptive copies (text values that are not
/// UTF-8 are shown as null); the references in memory are what later steps use, and a completed preflight keeps them
/// exactly in its evidence ([`super::preflight::reuse`]).
pub(crate) fn write_descriptive_copies(statement: &Statement, references: &[BindingReference]) {
    for (binding, result) in statement.bindings.iter().zip(references) {
        let path = statement.directory.join(format!("prepared-reference-{}.json", binding.name));
        let _ = write_new_json(&path, &match result {
            Ok(exact) => json!({"status":"exact","record":exact.record,"rows":super::comparison::rows_text(&exact.rows)}),
            Err(reason) => json!({"status":"no_reference","reason":reason.0}),
        });
    }
}

async fn direct_references(preflight: &QueryPreflight, reference: &SqlReference) -> Vec<BindingReference> {
    let statement = &preflight.statement;
    let sql = match rewrite::unsliced_sql(&statement.sql) {
        Ok(sql) => sql,
        Err(e) => return statement.bindings.iter().map(|_| Err(NoReference(format!("no_independent_reference: {e}")))).collect(),
    };
    let mut out = vec![];
    for binding in &statement.bindings {
        let started = Instant::now();
        let result = async {
            let parameters = bound_parameters(statement, binding)?;
            let batches = reference.execute_bound(&sql, &parameters).await.map_err(|e| format!("reference_error: DataFusion: {e}"))?;
            let columns = &statement.instance.doc.output.columns;
            let mut rows = arrow_values::batch_rows(&batches)?
                .iter()
                .map(|row| {
                    if row.len() != columns.len() {
                        return Err(format!("reference row arity {} differs from {} output columns", row.len(), columns.len()));
                    }
                    row.iter().zip(columns).map(|(x, c)| direct::output_value(x, c)).collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
            preflight.window.sort_body(&mut rows);
            let record = json!({"method":"DataFusion executes the SQL unchanged with its own typed parameter binding (PREPARE with the declared types, then with_param_values), LIMIT/OFFSET removed through sqlparser; values converted exactly to the output columns' static types; rows sorted by the ORDER BY keys (test infrastructure; OFFSET/LIMIT applied by the tie-aware comparison); tests, not proof",
                "sql":sql,"binding":binding,"parameters":parameters.iter().map(|(t, v)| json!({"type":t,"value":v.to_string()})).collect::<Vec<_>>(),
                "rows":rows.len(),"first_rows":super::comparison::rows_text(&rows[..rows.len().min(20)]),"reference_ns":started.elapsed().as_nanos()});
            Ok(ExactReference { rows, record })
        }
        .await;
        out.push(result.map_err(NoReference));
    }
    out
}

/// DataFusion's `PREPARE` types of the statement's parameters `$1..$n` (fixed and free, [`direct::parameter_type`]).
/// `Err` when the placeholder indices have gaps: DataFusion binds positional parameters `$1..$n` only.
fn parameter_types(statement: &Statement) -> Result<Vec<String>, String> {
    let mut types = vec![];
    for (i, declaration) in statement.declarations.iter().enumerate() {
        if declaration.index as usize != i + 1 {
            return Err("DataFusion binds positional parameters $1..$n without gaps".into());
        }
        types.push(direct::parameter_type(declaration.ty));
    }
    Ok(types)
}

/// Every parameter's DataFusion type and value at `binding` (fixed and free), in placeholder order.
fn bound_parameters(statement: &Statement, binding: &Binding) -> Result<Vec<(String, ScalarValue)>, String> {
    parameter_types(statement).map_err(|e| format!("no_independent_reference: {e}"))?;
    statement.all_values(binding).iter().map(|(_, t, v)| direct::parameter(*t, v)).collect()
}

/// The rewrite at every admission binding: its aggregation over the prepared columns with the binding's typed
/// parameters, then the verified finalization of the aggregated rows (the evaluator is loaded once).
async fn rewrite_references(statement: &Statement, plan: &RewritePlan, types: &[FinalizationType], library: &Path, reference: &SqlReference) -> Vec<BindingReference> {
    let library = match EvaluatorLibrary::load(library) {
        Ok(library) => library,
        Err(e) => return statement.bindings.iter().map(|_| Err(NoReference(format!("tool_failure: {e}")))).collect(),
    };
    let mut out = vec![];
    for binding in &statement.bindings {
        out.push(rewrite_reference(statement, binding, plan, types, &library, reference).await);
    }
    out
}

/// One DataFusion SUM/COUNT aggregation over the prepared columns at `binding`, then the verified finalization of its
/// few rows.
async fn rewrite_reference(
    statement: &Statement,
    binding: &Binding,
    plan: &RewritePlan,
    types: &[FinalizationType],
    library: &EvaluatorLibrary,
    reference: &SqlReference,
) -> BindingReference {
    let started = Instant::now();
    let parameters = bound_parameters(statement, binding).map_err(NoReference)?;
    let batches = reference.execute_bound(&plan.aggregation_sql, &parameters).await.map_err(|e| NoReference(format!("reference_error: DataFusion: {e}")))?;
    let aggregated = arrow_values::batch_rows(&batches).map_err(NoReference)?;
    let aggregation_ns = started.elapsed().as_nanos();
    let table = rewrite::finalization_rows(plan, types, &aggregated).map_err(NoReference)?;
    let finalized = Instant::now();
    let outcome = library.run(&vec![table]).map_err(|e| NoReference(format!("tool_failure: {e}")))?;
    let rows = match outcome {
        RunOutcome::Rows(rows) => rows,
        // The output arithmetic over this binding's exact aggregates raises (e.g. division by a zero SUM): no rows to
        // compare with, status-only like every binding without a reference.
        RunOutcome::SqlError(error) => {
            return Err(NoReference(format!("no_independent_reference: the verified finalization of the aggregated rows raises the SQL error {error:?} at this binding")));
        }
        other => return Err(NoReference(format!("tool_failure: verified finalization of the independent aggregation returned {other:?}"))),
    };
    let record = json!({"identity":REWRITE_IDENTITY,"aggregation_sql":plan.aggregation_sql,"binding":binding,
        "parameters":parameters.iter().map(|(t, v)| json!({"type":t,"value":v.to_string()})).collect::<Vec<_>>(),
        "aggregated_groups":aggregated.len(),"aggregation_ns":aggregation_ns,"finalization_ns":finalized.elapsed().as_nanos(),"rows":rows.len(),
        "scale_checks":plan.scale_checks.len(),
        "method":"one DataFusion SUM/COUNT aggregation over the prepared columns at this binding, parameters bound by DataFusion's own typed binding (PREPARE with the declared types, then with_param_values) (AVG -> SUM and COUNT; value-dependent SUM display scales checked), then the verified VERUS_SQL evaluator computes the output arithmetic over the aggregated rows and orders them (the full ordered body; OFFSET/LIMIT are applied by the tie-aware comparison); tests, not proof"});
    Ok(ExactReference { rows, record })
}

/// Verify and compile the SQLSpec evaluator crate of `doc` into the new directory `out` (`note`: the file naming the
/// document in the build record). Returns the library and the build record.
pub(crate) fn build_verified_evaluator(toolchain: &VerusToolchain, doc: &AstDocument, note: &Path, out: &Path, crate_name: &str) -> Result<(PathBuf, Value), AdmissionError> {
    let build = build_evaluator(toolchain, doc, note, out, &BuildOptions { crate_name, checked_library: None }).map_err(AdmissionError::tool)?;
    match (build.status, build.library) {
        (BuildStatus::Ok, Some(library)) => Ok((library, build.record)),
        (status, _) => Err(AdmissionError::unsupported(format!(
            "the verified reference evaluator could not be built ({status:?}); record {}",
            out.join("build.json").display()
        ))),
    }
}

/// `Ok` iff every finalization output has the value kind of the statement's output at the same position (integer,
/// numeric, text, date, boolean, timestamp): the finalization re-types each output's arithmetic over the aggregates.
fn same_value_kinds(finalization: &AstDocument, statement: &AstDocument) -> Result<(), String> {
    let kind = |t: &PgType| match t {
        PgType::Int4 | PgType::Int8 => "integer",
        PgType::Numeric { .. } => "numeric",
        PgType::Text | PgType::Varchar { .. } | PgType::Bpchar { .. } => "text",
        PgType::Date => "date",
        PgType::Bool => "boolean",
        PgType::Timestamp => "timestamp",
    };
    let (ours, theirs) = (&finalization.output.columns, &statement.output.columns);
    if ours.len() != theirs.len() {
        return Err(format!("the finalization has {} outputs, the statement {}", ours.len(), theirs.len()));
    }
    for (i, (a, b)) in ours.iter().zip(theirs).enumerate() {
        if kind(&a.ty) != kind(&b.ty) {
            return Err(format!("finalization output {i} is {}, the statement's output is {}", kind(&a.ty), kind(&b.ty)));
        }
    }
    Ok(())
}

/// Translate the rewrite's parameter-free finalization query over its DDL, in `directory`.
fn translate_finalization(parser: &SqlParser, ddl: &str, sql: &str, directory: &Path) -> Result<AstDocument, AdmissionError> {
    create_dir(directory)?;
    let (schema_file, sql_file) = (directory.join("schema.sql"), directory.join("query.sql"));
    write_text(&schema_file, ddl)?;
    write_text(&sql_file, sql)?;
    let (text, translation) = parser.translate(&schema_file, &sql_file, "postgres", &[]).map_err(|e| AdmissionError::tool(format!("VERUS_SQL frontend: {e}")))?;
    write_text(&directory.join("ast.json"), &text)?;
    match translation {
        Translation::Ok(doc) => Ok(doc),
        Translation::Refused(r) => Err(AdmissionError::unsupported(format!("VERUS_SQL frontend refusal {} at {} ({})", r.reason, r.path, r.detail))),
    }
}

#[cfg(test)]
mod tests {
    //! End to end on a tiny prepared capture: the rewrite (DataFusion aggregation and scale checks, verified
    //! finalization of the output arithmetic) returns exactly what the whole statement's verified SQLSpec evaluator
    //! returns on the same rows, at every admission binding of a template, and a value-dependent SUM display scale that
    //! differs from DataFusion's is no reference (at that binding only).
    use super::*;
    use crate::admission::statement::prepare_statement;
    use arrow::array::{ArrayRef, Date32Array, Decimal128Array, Int32Array, Int64Array, StringArray};
    use arrow::datatypes::{DataType, Field, Schema};
    use arrow::record_batch::RecordBatch;
    use gendb_artifacts::{ColType, ColumnSpec};
    use gendb_frontend::params::ParamRequest;
    use gendb_sqlspec::codec::HostTables;
    use gendb_storage::import::{ColumnDemand, DataFormat, DatasetSpec, PreparationRequest, TableSpec, prepare_source};
    use std::sync::Arc;

    // sale(partkey, price, disc, qty, note, day, big) and part(pkey, ptype); prices and discounts at scale 2. The two
    // PROMO BRASS rows (partkey 1) have `big` values whose bigint sum overflows (exact as numeric).
    const PARTKEY: [i64; 8] = [1, 2, 1, 3, 2, 4, 4, 2];
    const PRICE: [i128; 8] = [10000, 25050, 3333, 1234, 99999, 100, 777, 1];
    const DISC: [i128; 8] = [5, 10, 0, 7, 2, 10, 3, 1];
    const QTY: [i32; 8] = [3, 7, 1, 2, 5, 4, 9, 1];
    const NOTE: [Option<&str>; 8] = [Some("a"), None, None, Some("b"), Some("c"), None, None, None];
    const DAY: [i32; 8] = [10961, 10962, 10963, 10964, 10965, 10000, 10966, 10967];
    const BIG: [i64; 8] = [i64::MAX - 1, -3, i64::MAX, 5, 7, 11, -13, 17];
    const PART: [(i64, &str); 4] = [(1, "PROMO BRASS"), (2, "STANDARD PLATED"), (3, "PROMO X"), (4, "ECONOMY")];

    fn dataset(dir: &Path) -> DatasetSpec {
        std::fs::create_dir_all(dir).unwrap();
        let write = |path: &Path, fields: Vec<Field>, columns: Vec<ArrayRef>| {
            let batch = RecordBatch::try_new(Arc::new(Schema::new(fields)), columns).unwrap();
            let mut writer = datafusion::parquet::arrow::ArrowWriter::try_new(std::fs::File::create(path).unwrap(), batch.schema(), None).unwrap();
            writer.write(&batch).unwrap();
            writer.close().unwrap();
        };
        let decimal = |v: &[i128]| Arc::new(Decimal128Array::from(v.to_vec()).with_precision_and_scale(15, 2).unwrap()) as ArrayRef;
        let (sale, part) = (dir.join("sale.parquet"), dir.join("part.parquet"));
        write(
            &sale,
            vec![Field::new("partkey", DataType::Int64, false), Field::new("price", DataType::Decimal128(15, 2), false),
                Field::new("disc", DataType::Decimal128(15, 2), false), Field::new("qty", DataType::Int32, false), Field::new("note", DataType::Utf8, true),
                Field::new("day", DataType::Date32, false), Field::new("big", DataType::Int64, false)],
            vec![Arc::new(Int64Array::from(PARTKEY.to_vec())), decimal(&PRICE), decimal(&DISC), Arc::new(Int32Array::from(QTY.to_vec())),
                Arc::new(StringArray::from(NOTE.to_vec())), Arc::new(Date32Array::from(DAY.to_vec())), Arc::new(Int64Array::from(BIG.to_vec()))],
        );
        write(
            &part,
            vec![Field::new("pkey", DataType::Int64, false), Field::new("ptype", DataType::Utf8, false)],
            vec![Arc::new(Int64Array::from(PART.map(|p| p.0).to_vec())), Arc::new(StringArray::from(PART.map(|p| p.1).to_vec()))],
        );
        let column = |name: &str, ty: ColType, nullable: bool| ColumnSpec { name: name.into(), ty, nullable };
        let decimal_type = || ColType::Decimal { p: 15, s: 2 };
        let table = |name: &str, fields, location: &Path| TableSpec { name: name.into(), fields, locations: vec![location.to_owned()], format: DataFormat::Parquet };
        DatasetSpec {
            tables: vec![
                table("sale", vec![column("partkey", ColType::I64, false), column("price", decimal_type(), false), column("disc", decimal_type(), false),
                    column("qty", ColType::I32, false), column("note", ColType::Utf8, true), column("day", ColType::Date32, false),
                    column("big", ColType::I64, false)], &sale),
                table("part", vec![column("pkey", ColType::I64, false), column("ptype", ColType::Utf8, false)], &part),
            ],
        }
    }

    /// The tiny rows as the whole statement's evaluator database (tables in the document's order).
    fn host_tables(doc: &AstDocument) -> HostTables {
        let sale: Vec<Vec<HostValue>> = (0..8)
            .map(|i| {
                vec![HostValue::Int(PARTKEY[i]), HostValue::Num { coeff: PRICE[i], scale: 2 }, HostValue::Num { coeff: DISC[i], scale: 2 },
                    HostValue::Int(QTY[i] as i64), NOTE[i].map_or(HostValue::Null, |n| HostValue::Text(n.as_bytes().to_vec())),
                    HostValue::Date(DAY[i] - crate::admission::cases::DAYS_1970_TO_2000), HostValue::Int(BIG[i])]
            })
            .collect();
        let part: Vec<Vec<HostValue>> = PART.iter().map(|(k, t)| vec![HostValue::Int(*k), HostValue::Text(t.as_bytes().to_vec())]).collect();
        doc.tables.iter().map(|t| if t.name == "sale" { sale.clone() } else { part.clone() }).collect()
    }

    #[test]
    #[ignore = "runs the pinned Verus toolchain, the frontend and DataFusion; -- --ignored"]
    fn arithmetic_over_aggregates_matches_the_whole_statement_evaluator() {
        let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let work = std::env::temp_dir().join(format!("gendb-aggregate-reference-{}-{nanos}", std::process::id()));
        let (parser, toolchain) = (SqlParser::from_environment().unwrap(), VerusToolchain::from_env().unwrap());
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let dataset = dataset(&work.join("data"));
        let mut demand = ColumnDemand::default();
        demand.add_columns(&dataset, "sale", &[0, 1, 2, 3, 4, 5, 6]).unwrap();
        demand.add_columns(&dataset, "part", &[0, 1]).unwrap();
        let request = PreparationRequest { dataset: &dataset, demand: &demand, base: None, registry: &work.join("registry"), root: &work.join("prepared") };
        let reference = SqlReference::new(Arc::new(prepare_source(&request).unwrap().0)).unwrap();
        let template = |name: &str, sql: &str, parameters: Value, test_bindings: &[Vec<String>]| {
            let parameters: Vec<ParamRequest> = serde_json::from_value(parameters).unwrap();
            let statement =
                prepare_statement(&parser, &dataset, None, sql, &parameters, test_bindings, &[], &work.join(name)).unwrap_or_else(|r| panic!("{name}: {}", r.error));
            let mode = runtime.block_on(choose_mode(&statement, &reference, &toolchain, &parser)).unwrap_or_else(|r| panic!("{name}: {} {}", r.error, r.detail));
            let PreparedMode::Rewrite { plan, types, library } = mode else { panic!("{name}: expected the rewrite") };
            (runtime.block_on(rewrite_references(&statement, &plan, &types, &library, &reference)), statement)
        };
        let rewrite = |name: &str, sql: &str| {
            let (mut references, statement) = template(name, sql, json!([]), &[]);
            assert_eq!(references.len(), 1, "{name}: a concrete statement has one binding");
            (references.remove(0), statement)
        };
        let whole_statement = |name: &str, statement: &Statement, binding: usize| {
            let doc = &statement.fixed_at(&statement.bindings[binding]).unwrap();
            let dir = work.join(name).join(format!("whole-{binding}"));
            let (library, _) = build_verified_evaluator(&toolchain, doc, &dir.join("note.json"), &dir.join("build"), "gendb_whole_statement").unwrap();
            match EvaluatorLibrary::load(&library).unwrap().run(&host_tables(doc)).unwrap() {
                RunOutcome::Rows(rows) => rows,
                other => panic!("{name}: whole statement returned {other:?}"),
            }
        };
        let q14 = "SELECT 100.00 * SUM(CASE WHEN ptype LIKE 'PROMO%' THEN price * (1 - disc) ELSE 0 END) / SUM(price * (1 - disc)) AS promo \
            FROM sale, part WHERE partkey = pkey AND day >= DATE '2000-01-01'";
        let grouped = "SELECT ptype, AVG(price) AS avg_price, -(SUM(qty) + 2 * COUNT(*)) / 3 AS x, 2 * SUM(CASE WHEN qty >= 7 THEN price END) AS large, \
            SUM(price) / COUNT(*) AS per_row FROM sale, part WHERE partkey = pkey GROUP BY ptype ORDER BY ptype";
        // SUM(int8) is numeric: the PROMO BRASS sum is 2^64 - 3, beyond bigint, and must not wrap.
        let bigint_sum = "SELECT ptype, SUM(big) AS total, AVG(big) AS mean, SUM(big) - SUM(qty) AS diff FROM sale, part WHERE partkey = pkey \
            GROUP BY ptype ORDER BY ptype";
        let mut evidence = vec![];
        for (name, sql) in [("ratio", q14), ("grouped", grouped), ("bigint-sum", bigint_sum)] {
            let (reference_rows, statement) = rewrite(name, sql);
            let reference_rows = reference_rows.unwrap_or_else(|e| panic!("{name}: {e}"));
            let expected = whole_statement(name, &statement, 0);
            assert_eq!(reference_rows.rows, expected, "{name}: the rewrite differs from the whole statement's evaluator");
            evidence.push(json!({"query":name,"sql":sql,"rows":super::super::comparison::rows_text(&expected),"record":reference_rows.record}));
        }
        // Only non-PROMO rows qualify: every promo CASE value is the integer 0 (scale 0), so the SQLSpec SUM has scale 0
        // while DataFusion carries it at 4; the binding has no exact reference.
        let (no_promo, _) = rewrite("no-promo", &q14.replace("day >= DATE '2000-01-01'", "ptype NOT LIKE 'PROMO%'"));
        let NoReference(why) = no_promo.unwrap_err();
        assert!(why.starts_with("no_independent_reference: the SUM in gendb_a0 has display scale 0"), "{why}");
        evidence.push(json!({"query":"no-promo","no_reference":why}));
        // Templates: every admission binding (request, minimum, maximum, interior) is its own DataFusion aggregation
        // with DataFusion's typed binding, finalized by the one verified evaluator, and equals the whole statement's
        // evaluator with the parameters fixed at that binding. The date template has distinct results, an empty one at
        // its minimum; the second has a text parameter in a CASE condition (Q8's position), a free date and a fixed
        // integer, and its empty text matches no part type, so only ELSE 0 is summed: no reference at that binding.
        let date = json!([{"index":1,"type":"date","binding":{"free":{}}}]);
        let avg_template = "SELECT ptype, AVG(price) AS avg_price, SUM(qty) AS qty, COUNT(*) AS n FROM sale, part \
            WHERE partkey = pkey AND day <= $1 GROUP BY ptype ORDER BY ptype";
        let share_template = "SELECT 100.00 * SUM(CASE WHEN ptype = $1 THEN price * (1 - disc) ELSE 0 END) / SUM(price * (1 - disc)) AS share \
            FROM sale, part WHERE partkey = pkey AND day >= $2 AND qty <= $3";
        let share = json!([{"index":1,"type":"text","binding":{"free":{}}},{"index":2,"type":"date","binding":{"free":{}}},
            {"index":3,"type":"integer","binding":{"fixed":"9"}}]);
        let cases = [
            ("avg-template", avg_template, date, vec![vec!["2000-01-06".to_string()]]),
            ("share-template", share_template, share, vec![vec!["PROMO BRASS".into(), "2000-01-01".into()], vec!["STANDARD PLATED".into(), "2000-01-06".into()]]),
        ];
        let mut rows_at = std::collections::BTreeMap::new();
        for (name, sql, parameters, test_bindings) in cases {
            let (references, statement) = template(name, sql, parameters, &test_bindings);
            let names: Vec<&str> = statement.bindings.iter().map(|b| b.name.as_str()).collect();
            assert_eq!(names.len(), references.len(), "{name}");
            for (b, reference) in references.iter().enumerate() {
                let key = format!("{name}/{}", names[b]);
                match reference {
                    Ok(exact) => {
                        assert_eq!(exact.rows, whole_statement(name, &statement, b), "{key}: the rewrite differs from the whole statement's evaluator");
                        assert_eq!(exact.record["binding"]["name"], names[b], "{key}");
                        evidence.push(json!({"query":key,"sql":sql,"rows":super::super::comparison::rows_text(&exact.rows),"record":exact.record}));
                        rows_at.insert(key, Some(exact.rows.clone()));
                    }
                    Err(NoReference(why)) => {
                        evidence.push(json!({"query":key,"no_reference":why}));
                        rows_at.insert(key, None);
                    }
                }
            }
        }
        let rows = |key: &str| rows_at[key].clone().unwrap_or_else(|| panic!("{key} has no exact reference"));
        assert!(rows("avg-template/minimum").is_empty(), "no row is on or before 0001-01-01");
        assert!(!rows("avg-template/request_0").is_empty() && rows("avg-template/request_0") != rows("avg-template/maximum"), "distinct bindings, distinct results");
        assert_eq!(rows("share-template/maximum"), [vec![HostValue::Null]], "no qualifying row: NULL sums");
        assert_ne!(rows("share-template/request_0"), rows("share-template/request_1"));
        assert_eq!(rows_at["share-template/minimum"], None, "only ELSE 0 summed: display scale 0, not 4");
        std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
        eprintln!("evidence: {}", work.join("evidence.json").display());
    }

    /// Q8's shape on the tiny capture: a derived table (merged), an EXTRACT(YEAR) group key typed numeric, a text
    /// parameter in the outer CASE condition and a date parameter in the derived WHERE. At every admission binding the
    /// rewrite is either exactly the whole statement's verified evaluator fixed at that binding (which evaluates the
    /// derived table and EXTRACT itself) or a named NoReference. `day` spans 1997 and 2000: two year groups.
    #[test]
    #[ignore = "runs the pinned Verus toolchain, the frontend and DataFusion; -- --ignored"]
    fn derived_table_template_matches_the_whole_statement_evaluator() {
        let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let work = std::env::temp_dir().join(format!("gendb-derived-reference-{}-{nanos}", std::process::id()));
        let (parser, toolchain) = (SqlParser::from_environment().unwrap(), VerusToolchain::from_env().unwrap());
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let dataset = dataset(&work.join("data"));
        let mut demand = ColumnDemand::default();
        demand.add_columns(&dataset, "sale", &[0, 1, 2, 3, 4, 5, 6]).unwrap();
        demand.add_columns(&dataset, "part", &[0, 1]).unwrap();
        let request = PreparationRequest { dataset: &dataset, demand: &demand, base: None, registry: &work.join("registry"), root: &work.join("prepared") };
        let reference = SqlReference::new(Arc::new(prepare_source(&request).unwrap().0)).unwrap();
        let sql = "SELECT yr, SUM(CASE WHEN ptype = $1 THEN vol ELSE 0 END) / SUM(vol) AS share \
            FROM (SELECT EXTRACT(YEAR FROM day) AS yr, price * (1 - disc) AS vol, ptype FROM sale, part WHERE partkey = pkey AND day >= $2) AS d \
            GROUP BY yr ORDER BY yr";
        let parameters: Vec<ParamRequest> = serde_json::from_value(json!([{"index":1,"type":"text","binding":{"free":{}}},
            {"index":2,"type":"date","binding":{"free":{}}}])).unwrap();
        let test_bindings = [vec!["ECONOMY".to_string(), "1997-01-01".into()], vec!["PROMO BRASS".into(), "2000-01-01".into()]];
        let statement = prepare_statement(&parser, &dataset, None, sql, &parameters, &test_bindings, &[], &work.join("derived")).unwrap_or_else(|r| panic!("{}", r.error));
        let mode = runtime.block_on(choose_mode(&statement, &reference, &toolchain, &parser)).unwrap_or_else(|r| panic!("{} {}", r.error, r.detail));
        let PreparedMode::Rewrite { plan, types, library } = mode else { panic!("expected the rewrite") };
        assert_eq!(plan.key_types, [rewrite::KeyType::Extract { year: true }]);
        let references = runtime.block_on(rewrite_references(&statement, &plan, &types, &library, &reference));
        let mut evidence = vec![json!({"sql":sql,"aggregation_sql":plan.aggregation_sql})];
        let mut rows_at = std::collections::BTreeMap::new();
        for (b, (binding, result)) in statement.bindings.iter().zip(&references).enumerate() {
            match result {
                Ok(exact) => {
                    let doc = statement.fixed_at(binding).unwrap();
                    let dir = work.join("derived").join(format!("whole-{b}"));
                    let (whole, _) = build_verified_evaluator(&toolchain, &doc, &dir.join("note.json"), &dir.join("build"), "gendb_whole_statement").unwrap();
                    let RunOutcome::Rows(expected) = EvaluatorLibrary::load(&whole).unwrap().run(&host_tables(&doc)).unwrap() else { panic!("{}", binding.name) };
                    assert_eq!(exact.rows, expected, "{}: the rewrite differs from the whole statement's evaluator", binding.name);
                    evidence.push(json!({"binding":binding.name,"rows":super::super::comparison::rows_text(&exact.rows),"record":exact.record}));
                    rows_at.insert(binding.name.clone(), Some(exact.rows.clone()));
                }
                Err(NoReference(why)) => {
                    evidence.push(json!({"binding":binding.name,"no_reference":why}));
                    rows_at.insert(binding.name.clone(), None);
                }
            }
        }
        let rows = |name: &str| rows_at[name].clone().unwrap_or_else(|| panic!("{name} has no exact reference"));
        assert_eq!(rows("request_0").len(), 2, "ECONOMY matches in 1997 and in 2000");
        assert_eq!(rows("request_1").len(), 1, "only 2000 qualifies from 2000-01-01");
        assert!(rows("maximum").is_empty(), "no row on or after the greatest date");
        assert_eq!(rows_at["minimum"], None, "the empty text matches no part type: only ELSE 0 is summed, display scale 0, not 4");
        std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
        eprintln!("evidence: {}", work.join("evidence.json").display());
    }
}
