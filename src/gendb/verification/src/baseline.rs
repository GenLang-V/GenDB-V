//! Exact qualification of a recorded baseline-engine answer at one binding of a statement (`gendb baseline`).
//!
//! A DuckDB/Umbra timing may become a runtime target only when the engine ran the bound statement and its answer is
//! one the SQL allows. This module:
//! - renders the literal-bound SQL and the baseline-runner session of one binding ([`StatementEvidence::session`]):
//!   every `$n` becomes `CAST('<canonical text>' AS <declared type>)`, PostgreSQL's meaning of a parameter of that type;
//! - judges a runner's recorded answer ([`StatementEvidence::qualify`]): the session must be that rendering, and the
//!   answer (`canonical_json`, every value converted exactly to the output types by the runner) is compared with the
//!   run's exact prepared reference of the binding by [`Window::allowed_output`], the acceptance admission applies to
//!   candidates (values and display scales, ORDER BY key sequence, tie classes, OFFSET/LIMIT boundary ties).
//!
//! Verdicts: `exact` (the reference window, in order), `allowed` (another output the SQL allows: a peer permutation or
//! a different tied row at the LIMIT boundary), `unqualified` (not an allowed output given the reference; the
//! DataFusion reference is test infrastructure, so this does not by itself say which side is wrong), `refused` (not
//! judgeable here). Test infrastructure, not proof. Numeric-only agreement (engine DOUBLE or rounded decimals) is a
//! separate, explicitly labeled criterion (`tools/baseline_numeric_qualification.py`) and is never produced here.

use crate::admission::Window;
use crate::admission::cases::DAYS_1970_TO_2000;
use datafusion::sql::sqlparser::dialect::PostgreSqlDialect;
use datafusion::sql::sqlparser::tokenizer::{Location, Token, Tokenizer};
use gendb_frontend::ast::{AstDocument, ColType, PgType, Translation, decode};
use gendb_sqlspec::codec::HostValue;
use gendb_sqlspec::pg_text::parse_date;
use serde::Deserialize;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

/// Identity of this qualification procedure (recorded).
pub const TOOL: &str = "gendb-baseline-exact-qualification-v1";

const LABEL: &str = "exact qualification of a baseline answer against the binding's exact prepared reference with \
    admission's acceptance (Window::allowed_output); test infrastructure, not proof; never numeric-only agreement";

/// Hot samples per runner block (one warm qualification execution, then three hot executions).
const HOT_SAMPLES: usize = 3;

/// Verdicts from best to worst; a file's verdict is its worst execution's.
const VERDICTS: [&str; 4] = ["exact", "allowed", "refused", "unqualified"];

/// Why an input cannot be judged or rendered (recorded, never a pass) or could not be read (a failure).
#[derive(Debug)]
pub enum BaselineError {
    Refused(String),
    Failure(String),
}

fn refused<T>(why: impl Into<String>) -> Result<T, BaselineError> {
    Err(BaselineError::Refused(why.into()))
}

/// The small records of one statement evidence directory (`.../queries/query-NNNN/verus-preflight`).
pub struct StatementEvidence {
    directory: PathBuf,
    query_sql: String,
    statement: Value,
    doc: AstDocument,
}

impl StatementEvidence {
    /// Read `query.sql`, `statement.json` and `ast.json` of `directory`.
    pub fn open(directory: &Path) -> Result<StatementEvidence, BaselineError> {
        let read = |name: &str| {
            std::fs::read_to_string(directory.join(name)).map_err(|e| BaselineError::Failure(format!("{}: {e}", directory.join(name).display())))
        };
        let statement = serde_json::from_str(&read("statement.json")?).map_err(|e| BaselineError::Failure(format!("statement.json: {e}")))?;
        let doc = match decode(&read("ast.json")?) {
            Ok(Translation::Ok(doc)) => doc,
            Ok(Translation::Refused(r)) => return Err(BaselineError::Failure(format!("ast.json is a frontend refusal ({})", r.reason))),
            Err(e) => return Err(BaselineError::Failure(format!("ast.json: {e}"))),
        };
        Ok(StatementEvidence { directory: directory.to_owned(), query_sql: read("query.sql")?, statement, doc })
    }

    /// The admission binding `name` of the statement record.
    fn binding(&self, name: &str) -> Result<&Value, BaselineError> {
        let bindings = self.statement["admission_bindings"].as_array().map(Vec::as_slice).unwrap_or_default();
        match bindings.iter().find(|b| b["name"] == name) {
            Some(binding) => Ok(binding),
            None => refused(format!("no admission binding {name:?} in statement.json")),
        }
    }

    /// Whether `name` is a benchmark binding (records before benchmark bindings existed: the concrete `statement`).
    fn is_benchmark(&self, name: &str) -> bool {
        match self.statement["benchmark_bindings"].as_array() {
            Some(names) => names.iter().any(|n| n == name),
            None => name == "statement",
        }
    }

    /// `(declared type, argument text)` of placeholder `index` at `binding`: a fixed declaration's value, or the
    /// binding's canonical text of the free slot.
    fn argument(&self, binding: &Value, index: u64) -> Result<(String, String), BaselineError> {
        let declarations = self.statement["declaration"].as_array().map(Vec::as_slice).unwrap_or_default();
        let Some(declaration) = declarations.iter().find(|d| d["index"] == index) else {
            return refused(format!("placeholder ${index} has no declaration"));
        };
        let ty = declaration["type"].as_str().unwrap_or_default().to_string();
        let text = match (&declaration["binding"]["fixed"], declaration["slot"].as_u64()) {
            (Value::String(fixed), _) => Some(fixed.clone()),
            (_, Some(slot)) => binding["texts"].get(slot as usize).and_then(Value::as_str).map(String::from),
            _ => None,
        };
        match text {
            Some(text) => Ok((ty, text)),
            None => refused(format!("no argument text for ${index} at binding {}", binding["name"])),
        }
    }

    /// The SQL a baseline engine runs at `binding` ([`bind_placeholders`] of `query.sql`).
    pub fn bound_sql(&self, binding: &str) -> Result<String, BaselineError> {
        let binding = self.binding(binding)?;
        bind_placeholders(&self.query_sql, |index| self.argument(binding, index))
    }

    /// The runner `fields` of the statement's output columns (exact types; the runner converts every engine value to
    /// them or reports `exact_conversion_error`).
    pub fn runner_fields(&self) -> Result<Vec<Value>, BaselineError> {
        let output = &self.doc.output;
        output.names.iter().zip(&output.columns).map(|(name, column)| Ok(json!({"name":name,"ty":runner_type(name, column)?,"nullable":column.nullable}))).collect()
    }

    /// The baseline-runner session of `binding` (one JSON value per line): PREPARE of the bound SQL, one qualified warm
    /// execution with the output fields, three hot executions, close.
    pub fn session(&self, binding: &str, statement_name: &str) -> Result<Vec<Value>, BaselineError> {
        let (sql, fields) = (self.bound_sql(binding)?, self.runner_fields()?);
        let hot = json!({"statement":statement_name});
        Ok(vec![json!({"statement":statement_name,"sql":sql}), json!({"statement":statement_name,"result":true,"fields":fields}),
            hot.clone(), hot.clone(), hot, json!({"close":true})])
    }

    /// The qualification record of one runner block (`engine_output`, run from `session` with `workers`) at `binding`.
    /// `Err` only when an input cannot be read; every judgement is in the record.
    pub fn qualify(&self, binding: &str, session: &Path, engine_output: &Path, workers: u64) -> Result<Value, BaselineError> {
        let session_lines = jsonl(session)?;
        let engine_lines = jsonl(engine_output)?;
        let recorded_binding = self.binding(binding).ok();
        let benchmark = self.is_benchmark(binding);
        let mut record = json!({"tool":TOOL,"label":LABEL,"statement":{"directory":self.directory,"statement_key":self.statement["statement_key"]},
            "binding":{"name":binding,"origin":recorded_binding.map(|b| b["origin"].clone()),"texts":recorded_binding.map(|b| b["texts"].clone()),
                "benchmark":benchmark},
            "session":session,"engine_output":engine_output,"workers":workers,"header":engine_lines.first()});
        let identity = self.session_identity(binding, &session_lines, &engine_lines, workers);
        let (verdict, executions) = match identity {
            Ok(sql) => {
                record["bound_sql"] = json!(sql);
                self.judge_executions(binding, &engine_lines, &mut record)?
            }
            Err(BaselineError::Refused(why)) => ("refused", vec![json!({"verdict":"refused","reason":why})]),
            Err(failure) => return Err(failure),
        };
        record["executions"] = json!(executions);
        let timing = hot_timing(&engine_lines);
        record["verdict"] = json!(verdict);
        let eligible = matches!(verdict, "exact" | "allowed") && timing.is_ok() && benchmark;
        record["target_eligible"] = json!(eligible);
        match timing {
            Ok((hot_ns, median_ns, boundary)) => {
                record["timing"] = json!({"hot_ns":hot_ns,"median_ns":median_ns,"timing_scope":boundary});
                if eligible {
                    let header = engine_lines.first().cloned().unwrap_or_default();
                    let concrete = recorded_binding.is_some_and(|b| b["origin"] == "concrete");
                    let mut target = json!({"workers":workers,"median_ns":median_ns,
                        "provenance":format!("{} {} at binding {binding}, {} hot samples of {}; exact qualification {TOOL} ({verdict})",
                            header["version"].as_str().unwrap_or("unknown engine version"), header_workers_text(&header), HOT_SAMPLES, engine_output.display()),
                        "timing_scope":boundary});
                    if !concrete {
                        target["binding"] = json!(binding);
                    }
                    record["target"] = target;
                }
            }
            Err(why) => record["timing"] = json!({"refused":why}),
        }
        if !benchmark {
            record["not_a_target_because"] = json!("the binding is not a benchmark binding of the statement");
        }
        Ok(record)
    }

    /// The bound SQL when the session is this binding's rendering and the runner block matches it and `workers`.
    fn session_identity(&self, binding: &str, session: &[Value], engine: &[Value], workers: u64) -> Result<String, BaselineError> {
        let sql = self.bound_sql(binding)?;
        let fields = self.runner_fields()?;
        let session_sql: Vec<_> = session.iter().filter_map(|l| l.get("sql")).collect();
        let session_fields: Vec<_> = session.iter().filter_map(|l| l.get("fields")).collect();
        if session_sql != [&json!(sql)] {
            return refused("the session's SQL is not this binding's bound SQL (gendb baseline session)");
        }
        if session_fields != [&json!(fields)] {
            return refused(format!("the session's fields are not the statement's output fields {}", json!(fields)));
        }
        let header = engine.first().ok_or_else(|| BaselineError::Refused("empty engine output".into()))?;
        if header.get("original_sql").is_some_and(|s| *s != json!(sql)) {
            return refused("the engine header's original_sql is not the bound SQL");
        }
        let recorded = header.get("threads").and_then(Value::as_u64).or_else(|| header.get("debug.parallel").and_then(Value::as_str).and_then(|p| p.parse().ok()));
        match recorded {
            Some(w) if w == workers => Ok(sql),
            Some(w) => refused(format!("the engine header records {w} workers, not {workers}")),
            None => refused("the engine header records no worker setting (threads / debug.parallel)"),
        }
    }

    /// Verdict of every qualification execution against the binding's exact reference, and the file's verdict.
    fn judge_executions(&self, binding: &str, engine: &[Value], record: &mut Value) -> Result<(&'static str, Vec<Value>), BaselineError> {
        let path = self.directory.join(format!("prepared-reference-{binding}.json"));
        let reference: Value = serde_json::from_str(&std::fs::read_to_string(&path).map_err(|e| BaselineError::Failure(format!("{}: {e}", path.display())))?)
            .map_err(|e| BaselineError::Failure(format!("{}: {e}", path.display())))?;
        let window = Window::of(&self.doc);
        record["reference"] = json!({"file":path,"status":reference["status"],"method":reference["record"]["method"],
            "reference_ns":reference["record"]["reference_ns"],"body_rows":reference["rows"].as_array().map(Vec::len),"window":window});
        let full = match (reference["status"].as_str(), reference["rows"].as_array()) {
            (Some("exact"), Some(rows)) => match rows.iter().map(|r| reference_row(r, &self.doc.output.columns)).collect::<Result<Vec<_>, _>>() {
                Ok(rows) => rows,
                Err(why) => return Ok(("refused", vec![json!({"verdict":"refused","reason":format!("reference rows: {why}")})])),
            },
            _ => return Ok(("refused", vec![json!({"verdict":"refused","reason":format!("no exact prepared reference ({})", reference["reason"])})])),
        };
        let executions: Vec<Value> = engine
            .iter()
            .enumerate()
            .filter(|(_, line)| line["qualification_execution"] == true)
            .map(|(i, line)| {
                let mut out = json!({"line":i + 1});
                let judged = match line["canonical_json"].as_str() {
                    None => Err(format!("no canonical answer (runner: {}); the engine answer is not exactly representable at the output types, \
                        so exact qualification does not apply (numeric-only agreement is a separate, explicitly labeled criterion)", line["exact_conversion_error"])),
                    Some(text) => engine_rows(text, &self.doc.output.columns),
                };
                match judged {
                    Err(why) => {
                        out["verdict"] = json!("refused");
                        out["reason"] = json!(why);
                    }
                    Ok(rows) => {
                        let (verdict, detail) = judge(&window, &full, &rows);
                        out["rows"] = json!(rows.len());
                        out["verdict"] = json!(verdict);
                        out[if verdict == "unqualified" { "reason" } else { "rule" }] = json!(detail);
                    }
                }
                out
            })
            .collect();
        if executions.is_empty() {
            return Ok(("refused", vec![json!({"verdict":"refused","reason":"no qualification execution in the engine output"})]));
        }
        let worst = executions.iter().filter_map(|e| VERDICTS.iter().position(|v| e["verdict"] == *v)).max().unwrap_or(2);
        Ok((VERDICTS[worst], executions))
    }
}

/// `sql` with every placeholder `$n` (found by the PostgreSQL tokenizer, so never inside a literal or comment)
/// replaced by the [`typed_literal`] of `argument(n)`; all other bytes unchanged; trimmed of its final `;` like the
/// reference's SQL. A statement without placeholders is returned unchanged apart from that trim.
pub fn bind_placeholders(sql: &str, argument: impl Fn(u64) -> Result<(String, String), BaselineError>) -> Result<String, BaselineError> {
    let tokens = Tokenizer::new(&PostgreSqlDialect {}, sql)
        .tokenize_with_location()
        .map_err(|e| BaselineError::Failure(format!("the SQL does not tokenize: {e}")))?;
    let (mut out, mut copied) = (String::new(), 0);
    for token in tokens {
        let Token::Placeholder(placeholder) = &token.token else { continue };
        let Some(index) = placeholder.strip_prefix('$').filter(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit())) else {
            return refused(format!("placeholder {placeholder} is not $n"));
        };
        let index: u64 = index.parse().map_err(|_| BaselineError::Refused(format!("placeholder {placeholder} out of range")))?;
        let Some(start) = byte_offset(sql, token.span.start).filter(|s| sql[*s..].starts_with(placeholder.as_str())) else {
            return Err(BaselineError::Failure(format!("placeholder {placeholder}: the tokenizer location does not match the SQL")));
        };
        let (ty, text) = argument(index)?;
        out.push_str(&sql[copied..start]);
        out.push_str(&typed_literal(&ty, &text)?);
        copied = start + placeholder.len();
    }
    out.push_str(&sql[copied..]);
    Ok(out.trim().trim_end_matches(';').trim_end().to_string())
}

/// Verdict of an engine answer given the exact full ordered body: `exact` (the window, in order), `allowed` (another
/// allowed output, with admission's rule) or `unqualified` (with the first difference).
fn judge(window: &Window, full: &[Vec<HostValue>], rows: &[Vec<HostValue>]) -> (&'static str, String) {
    match window.allowed_output(full, rows) {
        Ok(_) if rows == window_rows(window, full) => ("exact", "identical to the reference window in order".into()),
        Ok(rule) => ("allowed", rule.into()),
        Err(why) => ("unqualified", why),
    }
}

/// `CAST(<text>' AS <type>)`: a value of the declared type, as a PostgreSQL parameter of that type is. A text
/// containing `\` is refused: PostgreSQL's LIKE default escape is `\`, other engines' conventions differ.
fn typed_literal(ty: &str, text: &str) -> Result<String, BaselineError> {
    if ty.is_empty() || !ty.chars().all(|c| c.is_ascii_alphanumeric() || " (),".contains(c)) {
        return refused(format!("declared type {ty:?} is not a plain SQL type name"));
    }
    if text.contains('\\') || text.contains('\0') {
        return refused(format!("argument {text:?} contains a backslash or NUL: baseline engines' LIKE escape conventions differ from PostgreSQL's default"));
    }
    Ok(format!("CAST('{}' AS {ty})", text.replace('\'', "''")))
}

/// Byte offset of a tokenizer location (1-based line and character column).
fn byte_offset(text: &str, at: Location) -> Option<usize> {
    let line_start = if at.line <= 1 { 0 } else { text.match_indices('\n').nth(at.line as usize - 2)?.0 + 1 };
    let line = &text[line_start..];
    let column = line.char_indices().nth((at.column as usize).checked_sub(1)?).map(|(i, _)| i).unwrap_or(line.len());
    Some(line_start + column)
}

/// The runner field type of one output column.
fn runner_type(name: &str, column: &ColType) -> Result<Value, BaselineError> {
    Ok(match &column.ty {
        PgType::Bool => json!("Bool"),
        PgType::Int4 => json!("I32"),
        PgType::Int8 => json!("I64"),
        PgType::Date => json!("Date32"),
        PgType::Text | PgType::Varchar { .. } => json!("Utf8"),
        PgType::Numeric { typmod } => match column.dscale {
            // The precision is the runner's range check: the typmod's, else the largest exact decimal (i128).
            Some(scale) if column.dscale_exact => json!({"Decimal":{"p":typmod.map_or(38, |(p, _)| p),"s":scale}}),
            _ => return refused(format!("column {name}: value-dependent numeric display scale; exact qualification does not apply")),
        },
        PgType::Timestamp | PgType::Bpchar { .. } => return refused(format!("column {name}: output type not supported by baseline qualification")),
    })
}

/// A runner canonical cell (`duckdb_baseline.py::value`).
#[derive(Deserialize)]
enum RunnerCell {
    Null,
    Bool(bool),
    I32(i64),
    I64(i64),
    Dec { v: i128, s: u32 },
    Text(String),
    /// Days since 1970-01-01.
    Date32(i64),
}

/// The runner's canonical answer as values of the output columns.
fn engine_rows(canonical: &str, columns: &[ColType]) -> Result<Vec<Vec<HostValue>>, String> {
    let rows: Vec<Vec<RunnerCell>> = serde_json::from_str(canonical).map_err(|e| format!("canonical answer: {e}"))?;
    let cell = |c: RunnerCell, column: &ColType| -> Result<HostValue, String> {
        Ok(match (c, &column.ty) {
            (RunnerCell::Null, _) if column.nullable => HostValue::Null,
            (RunnerCell::Bool(b), PgType::Bool) => HostValue::Bool(b),
            (RunnerCell::I32(x), PgType::Int4) | (RunnerCell::I64(x), PgType::Int8) => HostValue::Int(x),
            (RunnerCell::Dec { v, s }, PgType::Numeric { .. }) if Some(s as u64) == column.dscale => HostValue::Num { coeff: v, scale: s },
            (RunnerCell::Text(t), PgType::Text | PgType::Varchar { .. }) => HostValue::Text(t.into_bytes()),
            (RunnerCell::Date32(d), PgType::Date) => HostValue::Date(i32::try_from(d - DAYS_1970_TO_2000 as i64).map_err(|_| "date out of range")?),
            _ => return Err(format!("a runner cell does not have the output column's type {:?} (session fields differ?)", column.ty)),
        })
    };
    rows.into_iter()
        .map(|row| {
            if row.len() != columns.len() {
                return Err(format!("row width {} differs from the output's {}", row.len(), columns.len()));
            }
            row.into_iter().zip(columns).map(|(c, column)| cell(c, column)).collect()
        })
        .collect()
}

/// One reference row from its PostgreSQL output text (`comparison::rows_text`), typed by the output columns.
fn reference_row(row: &Value, columns: &[ColType]) -> Result<Vec<HostValue>, String> {
    let cells = row.as_array().filter(|r| r.len() == columns.len()).ok_or("reference row width differs from the output's")?;
    cells
        .iter()
        .zip(columns)
        .map(|(v, column)| {
            Ok(match (v, &column.ty) {
                (Value::Null, _) => HostValue::Null,
                (Value::Bool(b), PgType::Bool) => HostValue::Bool(*b),
                (Value::Number(n), PgType::Int4 | PgType::Int8) => HostValue::Int(n.as_i64().ok_or("integer out of range")?),
                (Value::String(s), PgType::Numeric { .. }) => numeric(s).ok_or_else(|| format!("numeric text {s:?}"))?,
                (Value::String(s), PgType::Date) => HostValue::Date(parse_date(s).and_then(|d| i32::try_from(d).ok()).ok_or_else(|| format!("date text {s:?}"))?),
                (Value::String(s), PgType::Text | PgType::Varchar { .. }) => HostValue::Text(s.as_bytes().to_vec()),
                _ => return Err(format!("reference value {v} is not of the output type {:?}", column.ty)),
            })
        })
        .collect()
}

/// `-?digits[.digits]` as a coefficient and its display scale (the inverse of `pg_text::numeric_text`).
fn numeric(text: &str) -> Option<HostValue> {
    let (negative, body) = text.strip_prefix('-').map_or((false, text), |b| (true, b));
    let (int, frac) = body.split_once('.').unwrap_or((body, ""));
    let digits = [int, frac].concat();
    if int.is_empty() || (body.contains('.') && frac.is_empty()) || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let coeff: i128 = digits.parse().ok()?;
    Some(HostValue::Num { coeff: if negative { -coeff } else { coeff }, scale: frac.len() as u32 })
}

/// The OFFSET/LIMIT window of the full ordered body (as `Window::allowed_output` takes it).
fn window_rows<'a>(window: &Window, full: &'a [Vec<HostValue>]) -> &'a [Vec<HostValue>] {
    let offset = (window.offset as usize).min(full.len());
    let end = window.limit.map_or(full.len(), |l| offset.saturating_add(l as usize).min(full.len()));
    &full[offset..end]
}

/// `(hot samples, median, timing scope)` of a runner block: exactly three hot samples, one boundary, no error line.
fn hot_timing(engine: &[Value]) -> Result<(Vec<u64>, u64, String), String> {
    if let Some(error) = engine.iter().find(|l| l.get("error").is_some()) {
        return Err(format!("the engine output has an error line: {}", error["error"]));
    }
    let hot: Vec<&Value> = engine.iter().filter(|l| l.get("execute_fetch_drop_ns").is_some()).collect();
    let samples: Option<Vec<u64>> = hot.iter().map(|l| l["execute_fetch_drop_ns"].as_u64()).collect();
    let boundaries: std::collections::BTreeSet<_> = hot.iter().map(|l| l["boundary"].as_str().unwrap_or_default()).collect();
    match (samples, boundaries.into_iter().collect::<Vec<_>>().as_slice()) {
        (Some(mut samples), [boundary]) if samples.len() == HOT_SAMPLES && !boundary.is_empty() => {
            let recorded = samples.clone();
            samples.sort_unstable();
            Ok((recorded, samples[HOT_SAMPLES / 2], boundary.to_string()))
        }
        _ => Err(format!("expected exactly {HOT_SAMPLES} hot samples with one timing boundary")),
    }
}

/// The worker setting as the runner recorded it.
fn header_workers_text(header: &Value) -> String {
    match (header.get("threads"), header.get("debug.parallel")) {
        (Some(t), _) => format!("threads={t}"),
        (_, Some(p)) => format!("debug.parallel={}", p.as_str().unwrap_or_default()),
        _ => "workers unrecorded".into(),
    }
}

fn jsonl(path: &Path) -> Result<Vec<Value>, BaselineError> {
    let text = std::fs::read_to_string(path).map_err(|e| BaselineError::Failure(format!("{}: {e}", path.display())))?;
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).map_err(|e| BaselineError::Failure(format!("{}: {e}", path.display()))))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn column(ty: PgType, dscale: Option<u64>) -> ColType {
        ColType { ty, nullable: false, dscale, dscale_exact: true }
    }

    fn text(s: &str) -> HostValue {
        HostValue::Text(s.as_bytes().to_vec())
    }

    fn window(keys: &[(usize, bool)], limit: Option<u64>) -> Window {
        Window { keys: keys.iter().map(|(c, d)| (*c, *d, *d)).collect(), offset: 0, limit }
    }

    fn arguments(index: u64) -> Result<(String, String), BaselineError> {
        match index {
            1 => Ok(("text".into(), "Brand#45".into())),
            2 => Ok(("text".into(), "it's%".into())),
            10 => Ok(("integer".into(), "-3".into())),
            _ => refused(format!("no ${index}")),
        }
    }

    /// Placeholders become typed literals; `$n` inside a literal or comment and every other byte stay as written.
    #[test]
    fn binding_renders_typed_literals_only_at_placeholders() {
        let sql = "SELECT '$1' AS a -- $2\nFROM t WHERE b <> $1 AND c LIKE $2 AND d IN ($10, $1);\n";
        let bound = bind_placeholders(sql, arguments).unwrap();
        assert_eq!(bound, "SELECT '$1' AS a -- $2\nFROM t WHERE b <> CAST('Brand#45' AS text) AND c LIKE CAST('it''s%' AS text) \
            AND d IN (CAST('-3' AS integer), CAST('Brand#45' AS text))");
        assert_eq!(bind_placeholders("SELECT 1 FROM t ORDER BY 1;\n", arguments).unwrap(), "SELECT 1 FROM t ORDER BY 1", "fixed query");
        let backslash = bind_placeholders("SELECT 1 WHERE a LIKE $1", |_| Ok(("text".into(), "a\\%".into())));
        assert!(matches!(backslash, Err(BaselineError::Refused(_))));
        assert!(matches!(bind_placeholders("SELECT $3", arguments), Err(BaselineError::Refused(_))));
    }

    /// Exact integer/text answers: identical passes, any differing value is unqualified.
    #[test]
    fn exact_rows_pass_and_differing_values_do_not() {
        let full = vec![vec![text("a"), HostValue::Int(3)], vec![text("b"), HostValue::Int(2)]];
        let w = window(&[(1, true), (0, false)], None);
        assert_eq!(judge(&w, &full, &full).0, "exact");
        let int = vec![vec![text("a"), HostValue::Int(3)], vec![text("b"), HostValue::Int(1)]];
        assert_eq!(judge(&w, &full, &int).0, "unqualified");
        let txt = vec![vec![text("a"), HostValue::Int(3)], vec![text("c"), HostValue::Int(2)]];
        assert_eq!(judge(&w, &full, &txt).0, "unqualified");
        assert_eq!(judge(&w, &full, &full[..1]).0, "unqualified", "row count");
    }

    /// ORDER BY value DESC with equal values: a peer permutation is allowed, an order of distinct keys is not; at a
    /// LIMIT boundary any tied row of the full body is allowed, a row outside the tie class is not.
    #[test]
    fn peers_and_limit_boundary_follow_admission_acceptance() {
        let row = |k: i64, v: i128| vec![HostValue::Int(k), HostValue::Num { coeff: v, scale: 2 }];
        let full = vec![row(1, 900), row(2, 500), row(3, 500), row(4, 100)];
        let w = window(&[(1, true)], None);
        assert_eq!(judge(&w, &full, &[row(1, 900), row(3, 500), row(2, 500), row(4, 100)]).0, "allowed");
        assert_eq!(judge(&w, &full, &[row(3, 500), row(1, 900), row(2, 500), row(4, 100)]).0, "unqualified");
        let w = window(&[(1, true)], Some(2));
        assert_eq!(judge(&w, &full, &[row(1, 900), row(2, 500)]).0, "exact");
        assert_eq!(judge(&w, &full, &[row(1, 900), row(3, 500)]).0, "allowed");
        assert_eq!(judge(&w, &full, &[row(1, 900), row(5, 500)]).0, "unqualified");
        assert_eq!(judge(&w, &full, &[row(1, 900), row(2, 50)]).0, "unqualified", "display scale is part of the value");
    }

    /// Runner cells decode exactly (38-digit decimals, dates) and must have the output column's type.
    #[test]
    fn runner_cells_decode_exactly_at_the_output_types() {
        let columns = [column(PgType::Numeric { typmod: None }, Some(2)), column(PgType::Date, None), column(PgType::Int8, None)];
        let big = "99999999999999999999999999999999999999";
        let rows = engine_rows(&format!(r#"[[{{"Dec":{{"v":{big},"p":38,"s":2}}}},{{"Date32":9204}},{{"I64":7}}]]"#), &columns).unwrap();
        assert_eq!(rows[0][0], HostValue::Num { coeff: big.parse().unwrap(), scale: 2 });
        let reference = reference_row(&json!([format!("{}.{}", &big[..36], &big[36..]), "1995-03-15", 7]), &columns).unwrap();
        assert_eq!(rows[0], reference);
        assert!(engine_rows(r#"[[{"Dec":{"v":1,"p":38,"s":3}},{"Date32":0},{"I64":1}]]"#, &columns).is_err(), "scale differs");
        assert!(engine_rows(r#"[["Null",{"Date32":0},{"I64":1}]]"#, &columns).is_err(), "NULL in a non-nullable column");
        assert!(engine_rows(r#"[[{"I64":1},{"Date32":0},{"I64":1}]]"#, &columns).is_err(), "type differs");
        let avg = ColType { dscale_exact: false, ..column(PgType::Numeric { typmod: None }, Some(6)) };
        assert!(matches!(runner_type("avg", &avg), Err(BaselineError::Refused(_))));
    }

    /// Timing comes from exactly three hot samples of one boundary, without an error line.
    #[test]
    fn timing_needs_three_hot_samples_and_no_error() {
        let hot = |ns: u64| json!({"rows":1,"execute_fetch_drop_ns":ns,"boundary":"b"});
        let lines = [json!({"threads":1}), json!({"qualification_execution":true}), hot(30), hot(10), hot(20), json!({"restored":true})];
        assert_eq!(hot_timing(&lines).unwrap(), (vec![30, 10, 20], 20, "b".to_string()));
        assert!(hot_timing(&lines[..4]).is_err(), "two hot samples");
        assert!(hot_timing(&[lines.as_slice(), &[json!({"error":"x"})]].concat()).is_err());
    }
}
