//! The run's validation policy (request `validation`): which checks, besides the Verus proof of every submitted crate
//! against its fixed entry claim, establish a candidate before admission.
//!
//! - [`ValidationPolicy::TestsAndReferences`] (default, the historical behaviour): every statement's preflight builds a
//!   verified SQLSpec evaluator per admission binding, generates and labels tiny cases, and computes an independent
//!   DataFusion reference on the full prepared data at every admission binding; every evaluation compares exactly.
//! - [`ValidationPolicy::FormalProofs`]: the proofs are the correctness evidence. No tiny case, evaluator build or
//!   reference engine runs; the generated domain bindings (minimum, maximum, interior) are not queried on the full data.
//!   Full-data results at a benchmark binding are compared with the saved answers of other engines the request supplies
//!   ([`SavedAnswerSource`]; `required_engines` names the engines every benchmark binding must have): agreement under
//!   typed rules ([`compare_with_saved`]), recorded per engine. It checks the trusted base and the environment; it is
//!   never a proof and never a second meaning. A result that agrees with no saved answer is not admitted. Workload
//!   storages have no query result: their admission is the verified builder/readers, a successful full-data build,
//!   complete column coverage and the storage budget.
//!
//! Saved answers are read once, when a statement's session opens; their timings are never used.

use super::comparison::Window;
use super::statement::Statement;
use super::AdmissionError;
use gendb_runtime::answer::QueryAnswer;
use gendb_sqlspec::codec::HostValue;
use gendb_sqlspec::pg_text::value_json;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::path::PathBuf;

/// Name of the formal policy in records.
pub const FORMAL_PROOFS: &str = "formal_proofs";
/// Name of the historical policy in records.
pub const TESTS_AND_REFERENCES: &str = "tests_and_references";

/// Why a binding has no prepared-data reference under [`ValidationPolicy::FormalProofs`].
pub const NO_REFERENCE_BY_POLICY: &str =
    "not computed: validation policy formal_proofs (no reference engine run; the Verus proof against the fixed SQLSpec entry is the correctness claim)";

/// The request's validation policy. JSON: absent or `{"kind": "tests_and_references"}`, or `{"kind": "formal_proofs",
/// "numeric_relative_tolerance": "1e-9", "required_engines": [...], "saved_answers": [...]}`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ValidationPolicy {
    #[default]
    TestsAndReferences,
    FormalProofs {
        /// Relative tolerance of numeric agreement between non-integer values (decimal text, e.g. `"1e-9"`; `"0"`:
        /// exact only): other engines may return floating point (AVG) or another decimal scale. Integers always
        /// compare exactly.
        numeric_relative_tolerance: String,
        /// Engines (`SavedAnswerSource::engine`) that must have a saved answer at every benchmark binding of every
        /// query; a missing one refuses the query before any author call. Empty: no requirement, and a benchmark
        /// binding without a saved answer is recorded `not_compared`.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        required_engines: Vec<String>,
        /// Saved results of other engines at benchmark bindings.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        saved_answers: Vec<SavedAnswerSource>,
    },
}

/// One saved answer: the result another engine returned for a request query at one of its benchmark bindings.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SavedAnswerSource {
    /// The request query's `name`.
    pub query: String,
    /// The benchmark binding's name (`objective.bindings[].name`).
    pub binding: String,
    /// Short engine identifier (e.g. `duckdb`), as `required_engines` names it.
    pub engine: String,
    /// The engine's version and settings (descriptive).
    pub description: String,
    /// A JSON file holding the rows.
    pub path: PathBuf,
    /// JSON pointer to the rows array in `path` (`""`: the whole file). Each row is an array of values: JSON null,
    /// bool, integer or string (text), or `{"dec": text}` (exact decimal), `{"f64": text}` (floating point),
    /// `{"date": "YYYY-MM-DD"}`.
    pub rows_pointer: String,
}

impl ValidationPolicy {
    pub fn is_default(&self) -> bool {
        *self == ValidationPolicy::TestsAndReferences
    }

    pub fn name(&self) -> &'static str {
        match self {
            ValidationPolicy::TestsAndReferences => TESTS_AND_REFERENCES,
            ValidationPolicy::FormalProofs { .. } => FORMAL_PROOFS,
        }
    }

    /// Structural checks before any preparation: a finite non-negative tolerance and at most one saved answer per
    /// (query, binding, engine).
    pub fn validate(&self) -> Result<(), String> {
        let ValidationPolicy::FormalProofs { numeric_relative_tolerance, saved_answers, .. } = self else { return Ok(()) };
        let tolerance: f64 = numeric_relative_tolerance.parse().map_err(|e| format!("numeric_relative_tolerance {numeric_relative_tolerance:?}: {e}"))?;
        if !(tolerance.is_finite() && tolerance >= 0.0) {
            return Err("numeric_relative_tolerance must be a finite non-negative number".into());
        }
        let mut seen = std::collections::BTreeSet::new();
        for answer in saved_answers {
            if !seen.insert((&answer.query, &answer.binding, &answer.engine)) {
                return Err(format!("saved answer ({}, {}, {}) is given twice", answer.query, answer.binding, answer.engine));
            }
        }
        Ok(())
    }

    /// The statement-level view of this policy for request query `query_name`: its saved answers read per admission
    /// binding. Refused (missing input) when a saved answer names a binding that is not a benchmark binding, cannot be
    /// read, or a required engine has no saved answer at some benchmark binding.
    pub fn for_statement(&self, query_name: Option<&str>, statement: &Statement) -> Result<StatementValidation, AdmissionError> {
        let ValidationPolicy::FormalProofs { numeric_relative_tolerance, required_engines, saved_answers } = self else {
            return Ok(StatementValidation::default());
        };
        let tolerance = numeric_relative_tolerance.parse().map_err(AdmissionError::missing_input)?;
        let mut answers: Vec<Vec<SavedAnswer>> = statement.bindings.iter().map(|_| vec![]).collect();
        for source in saved_answers.iter().filter(|a| Some(a.query.as_str()) == query_name) {
            let index = statement.benchmark.iter().copied().find(|&b| statement.bindings[b].name == source.binding).ok_or_else(|| {
                AdmissionError::missing_input(format!("saved answer of {}: {} is not a benchmark binding {:?}", source.query, source.binding, statement.benchmark_names()))
            })?;
            answers[index].push(SavedAnswer::read(source)?);
        }
        for &b in &statement.benchmark {
            for engine in required_engines {
                if !answers[b].iter().any(|a| &a.engine == engine) {
                    return Err(AdmissionError::missing_input(format!(
                        "validation.required_engines: no saved answer of {engine} for query {query_name:?} at benchmark binding {}",
                        statement.bindings[b].name
                    )));
                }
            }
        }
        Ok(StatementValidation { formal: true, answers, tolerance, required_engines: required_engines.clone() })
    }
}

/// The validation policy as one statement uses it.
#[derive(Clone, Debug, Default)]
pub struct StatementValidation {
    /// [`ValidationPolicy::FormalProofs`]: no tiny cases, evaluators or references; only benchmark bindings are queried
    /// on the full data.
    pub formal: bool,
    /// Per admission binding (same index): the saved answers of other engines.
    pub answers: Vec<Vec<SavedAnswer>>,
    pub tolerance: f64,
    pub required_engines: Vec<String>,
}

impl StatementValidation {
    pub fn policy_name(&self) -> &'static str {
        if self.formal { FORMAL_PROOFS } else { TESTS_AND_REFERENCES }
    }

    /// The saved answers at admission binding `binding` (empty: none).
    pub fn answers_at(&self, binding: usize) -> &[SavedAnswer] {
        self.answers.get(binding).map(Vec::as_slice).unwrap_or_default()
    }

    /// What the policy checks and skips (preflight and prompt records).
    pub fn record(&self) -> Value {
        if !self.formal {
            return json!({"policy":TESTS_AND_REFERENCES,"checks":"Verus proof of every submitted crate; tiny cases labelled by verified SQLSpec evaluators; exact comparison with independent prepared-data references at every admission binding"});
        }
        let saved = self.answers.iter().map(Vec::len).sum::<usize>();
        json!({"policy":FORMAL_PROOFS,"numeric_relative_tolerance":tolerance_text(self.tolerance),"required_engines":self.required_engines,"saved_answers":saved,
            "checks":"Verus proof of every submitted crate against its fixed entry claim (the correctness claim); full-data runs at the benchmark bindings; agreement of those results with the saved answers of other engines, reported per engine",
            "not_run":"tiny cases, verified evaluator builds, reference engine (DataFusion) runs, full-data runs at the generated domain bindings (minimum, maximum, interior)"})
    }

    /// Judge `answer` at admission binding `binding`, which has no exact reference (`no_reference`: why): under
    /// `formal_proofs` its agreement with the binding's saved answers (`saved_answers_agree`: every engine agrees;
    /// `saved_answers_agree_partly`: some do, the others' verdicts recorded), or `not_compared` when none are given;
    /// under the historical policy `status_only`. `Err` (`saved_answer_disagreement`, an execution failure) when saved
    /// answers exist and none agrees, or the answer has no rows where they have rows.
    pub fn judge_without_reference(&self, window: &Window, binding: usize, answer: &QueryAnswer, what: &str, no_reference: &str) -> Result<(&'static str, String), AdmissionError> {
        let answers = self.answers_at(binding);
        let name = |answer: &QueryAnswer| match answer {
            QueryAnswer::Rows(rows) => format!("{} rows", rows.len()),
            QueryAnswer::SqlError(e) => format!("SQL error {}", e.name),
            QueryAnswer::Capacity => "Capacity".into(),
            QueryAnswer::ParamRefused => "ParamRefused".into(),
        };
        if answers.is_empty() {
            return Ok(self.without_saved_answer(no_reference, &name(answer)));
        }
        let QueryAnswer::Rows(rows) = answer else {
            let engines: Vec<&str> = answers.iter().map(|a| a.engine.as_str()).collect();
            return Err(AdmissionError::execution(format!("saved_answer_disagreement: {what} returned {}, the saved answers of {engines:?} have rows", name(answer))));
        };
        let (status, record) = compare_with_saved(window, answers, rows, self.tolerance).map_err(|detail| AdmissionError::execution(format!("saved_answer_disagreement: {what}: {detail}")))?;
        Ok((status, record.to_string()))
    }

    /// Judge a rows answer stored bounded (`gendb_runtime::worker::StoredAnswer`; `returned`: its description) at
    /// admission binding `binding`, which has no exact reference (`no_reference`: why): `not_compared` (or `status_only`)
    /// with the same words as [`Self::judge_without_reference`]. A binding with saved answers is a tool failure: a cell
    /// that compares answers stores them in full.
    pub fn judge_stored(&self, binding: usize, returned: &str, what: &str, no_reference: &str) -> Result<(&'static str, String), AdmissionError> {
        if !self.answers_at(binding).is_empty() {
            return Err(AdmissionError::tool(format!(
                "{what}: the answer was stored bounded ({returned}), but this binding has saved answers to compare it with: a compared cell stores its answers in full"
            )));
        }
        Ok(self.without_saved_answer(no_reference, returned))
    }

    /// The verdict of an answer (`returned`: its description) at a binding with no exact reference and no saved answer.
    fn without_saved_answer(&self, no_reference: &str, returned: &str) -> (&'static str, String) {
        if self.formal {
            ("not_compared", format!("{no_reference}; no saved answer at this binding; the candidate returned {returned}"))
        } else {
            ("status_only", format!("no exact reference at this binding ({no_reference}); the candidate returned {returned}; result correctness untested"))
        }
    }

    /// The admission bindings queried on the full data: every one, or under `formal_proofs` the benchmark bindings only
    /// (the generated domain bindings exist for references and tiny cases, which this policy does not run).
    pub fn full_data_bindings(&self, statement: &Statement) -> Vec<usize> {
        if self.formal { statement.benchmark.clone() } else { (0..statement.bindings.len()).collect() }
    }
}

/// Whether a measured cell's result was checked: equal to an exact reference (`exact`, policy tests_and_references)
/// or agreeing with saved answers of other engines (policy formal_proofs). Only such cells count for the user's early
/// stop and a trial's `met_bar`; `status_only` and `not_compared` cells never do.
pub fn checked_cell_status(status: &Value) -> bool {
    matches!(status.as_str(), Some("exact" | "saved_answers_agree" | "saved_answers_agree_partly"))
}

/// A saved answer read from its file.
#[derive(Clone, Debug)]
pub struct SavedAnswer {
    pub engine: String,
    pub description: String,
    pub path: PathBuf,
    pub rows: Vec<Vec<SavedValue>>,
}

impl SavedAnswer {
    fn read(source: &SavedAnswerSource) -> Result<Self, AdmissionError> {
        let what = |detail: String| AdmissionError::missing_input(format!("saved answer {} ({}, {}): {detail}", source.path.display(), source.query, source.binding));
        let bytes = std::fs::read(&source.path).map_err(|e| what(e.to_string()))?;
        let document: Value = serde_json::from_slice(&bytes).map_err(|e| what(e.to_string()))?;
        let rows = document.pointer(&source.rows_pointer).and_then(Value::as_array).ok_or_else(|| what(format!("no rows array at {:?}", source.rows_pointer)))?;
        let rows = rows
            .iter()
            .map(|row| row.as_array().ok_or_else(|| what("a row is not an array".into()))?.iter().map(|v| SavedValue::of(v).map_err(&what)).collect())
            .collect::<Result<_, _>>()?;
        Ok(Self { engine: source.engine.clone(), description: source.description.clone(), path: source.path.clone(), rows })
    }
}

/// One value of a saved answer, or of our answer in the same terms. Numerics keep their kind: integers compare
/// exactly; decimals and floating point may agree within the tolerance.
#[derive(Clone, Debug, PartialEq)]
pub enum SavedValue {
    Null,
    Bool(bool),
    Int(String),
    Decimal(String),
    Float(String),
    Text(String),
    Date(String),
}

impl SavedValue {
    fn of(value: &Value) -> Result<Self, String> {
        Ok(match value {
            Value::Null => SavedValue::Null,
            Value::Bool(b) => SavedValue::Bool(*b),
            Value::Number(n) if n.is_i64() || n.is_u64() => SavedValue::Int(n.to_string()),
            Value::String(s) => SavedValue::Text(s.clone()),
            Value::Object(o) if o.len() == 1 => match o.iter().next() {
                Some((k, Value::String(s))) if k == "dec" => SavedValue::Decimal(s.clone()),
                Some((k, Value::String(s))) if k == "f64" => SavedValue::Float(s.clone()),
                Some((k, Value::String(s))) if k == "date" => SavedValue::Date(s.clone()),
                _ => return Err(format!("unsupported saved value {value}")),
            },
            other => return Err(format!("unsupported saved value {other}")),
        })
    }

    /// Our value in the same terms (numerics and dates as PostgreSQL text).
    fn of_host(value: &HostValue) -> SavedValue {
        match (value, value_json(value)) {
            (HostValue::Null, _) => SavedValue::Null,
            (HostValue::Bool(b), _) => SavedValue::Bool(*b),
            (HostValue::Int(x), _) => SavedValue::Int(x.to_string()),
            (HostValue::Num { .. }, Ok(Value::String(text))) => SavedValue::Decimal(text),
            (HostValue::Date(_), Ok(Value::String(text))) => SavedValue::Date(text),
            (_, Ok(Value::String(text))) => SavedValue::Text(text),
            (_, other) => SavedValue::Text(format!("{other:?}")),
        }
    }

    fn numeric(&self) -> Option<(&str, bool)> {
        match self {
            SavedValue::Int(t) => Some((t, true)),
            SavedValue::Decimal(t) | SavedValue::Float(t) => Some((t, false)),
            _ => None,
        }
    }

    /// The part compared exactly when grouping rows (numerics, which may agree within the tolerance, are left out).
    fn exact_key(&self) -> String {
        match self.numeric() {
            Some(_) => "#".into(),
            None => format!("{self:?}"),
        }
    }
}

/// How two values agree: exactly (`Some(false)`), within the numeric tolerance only (`Some(true)`), or not (`None`).
/// Numerics agree exactly when equal as decimals; approximately only when neither is an integer, both are finite and
/// the relative difference is within a positive tolerance.
fn values_agree(a: &SavedValue, b: &SavedValue, tolerance: f64) -> Option<bool> {
    match (a.numeric(), b.numeric()) {
        (Some((x, x_int)), Some((y, y_int))) => {
            if let (Some(p), Some(q)) = (exact_decimal(x), exact_decimal(y))
                && p == q
            {
                return Some(false);
            }
            if x_int || y_int || tolerance <= 0.0 {
                return None;
            }
            let (p, q): (f64, f64) = (x.parse().ok()?, y.parse().ok()?);
            (p.is_finite() && q.is_finite() && (p - q).abs() <= tolerance * p.abs().max(q.abs())).then_some(true)
        }
        _ => (a == b).then_some(false),
    }
}

/// A plain decimal text as (coefficient, scale) with trailing fractional zeros removed; `None` for anything else
/// (exponents, non-finite values, overflow).
fn exact_decimal(text: &str) -> Option<(i128, u32)> {
    let (sign, digits) = match text.strip_prefix('-') {
        Some(rest) => (-1, rest),
        None => (1, text.strip_prefix('+').unwrap_or(text)),
    };
    let (int, frac) = digits.split_once('.').unwrap_or((digits, ""));
    if int.is_empty() && frac.is_empty() || !int.bytes().chain(frac.bytes()).all(|b| b.is_ascii_digit()) {
        return None;
    }
    let frac = frac.trim_end_matches('0');
    let coeff: i128 = format!("0{int}{frac}").parse().ok()?;
    Some((if coeff == 0 { 0 } else { sign * coeff }, if coeff == 0 { 0 } else { frac.len() as u32 }))
}

/// How two rows agree (as [`values_agree`]); `None` for different arity.
fn rows_agree(a: &[SavedValue], b: &[SavedValue], tolerance: f64) -> Option<bool> {
    if a.len() != b.len() {
        return None;
    }
    let mut approximate = false;
    for (x, y) in a.iter().zip(b) {
        approximate |= values_agree(x, y, tolerance)?;
    }
    Some(approximate)
}

/// The same multiset of rows: rows grouped by their exactly compared values, numerics matched within the tolerance.
/// `Some(approximate)` when they are.
fn multiset_agree(saved: &[Vec<SavedValue>], ours: &[Vec<SavedValue>], tolerance: f64) -> Option<bool> {
    if saved.len() != ours.len() {
        return None;
    }
    let key = |row: &Vec<SavedValue>| row.iter().map(SavedValue::exact_key).collect::<Vec<_>>().join("|");
    let mut pool: BTreeMap<String, Vec<&Vec<SavedValue>>> = BTreeMap::new();
    for row in saved {
        pool.entry(key(row)).or_default().push(row);
    }
    let mut approximate = false;
    for row in ours {
        let candidates = pool.get_mut(&key(row))?;
        let found = candidates.iter().position(|c| rows_agree(c, row, tolerance).is_some())?;
        approximate |= rows_agree(candidates[found], row, tolerance)?;
        candidates.swap_remove(found);
    }
    Some(approximate)
}

/// One engine's verdict on our rows.
struct Verdict {
    /// `exact_order`; `tie_order_differs` (rows of an ORDER BY tie class in another order); `multiset` (no ORDER BY);
    /// `multiset_order_unchecked` (an ORDER BY key is not an output column, so order is not compared).
    order: &'static str,
    /// Some numeric agreed within the tolerance only.
    approximate: bool,
    /// With LIMIT: rows of the last tie class that are another choice of that class than the saved answer's (their
    /// membership in the full result is not checked here; the proof covers it).
    limit_boundary_rows: usize,
}

/// Compare one saved answer with our rows (`ours_host`: the same rows as host values, already in ORDER BY order). Row
/// counts and arity must be equal. With ORDER BY keys among the output columns, the key sequence must agree row by row
/// and every tie class (equal keys) must hold the same multiset of rows, except the last class under LIMIT, where only
/// its count and keys are compared. `Err` explains the first difference.
fn agreement(window: &Window, saved: &[Vec<SavedValue>], ours: &[Vec<SavedValue>], ours_host: &[Vec<HostValue>], tolerance: f64) -> Result<Verdict, String> {
    if saved.len() != ours.len() {
        return Err(format!("{} rows, the saved answer has {}", ours.len(), saved.len()));
    }
    if let Some(i) = saved.iter().zip(ours).position(|(a, b)| a.len() != b.len()) {
        return Err(format!("row {i} has {} columns, the saved answer's has {}", ours[i].len(), saved[i].len()));
    }
    let positional: Option<Vec<bool>> = saved.iter().zip(ours).map(|(a, b)| rows_agree(a, b, tolerance)).collect();
    let keys_visible = keys_visible(window, ours);
    if window.keys.is_empty() || !keys_visible {
        let order = if window.keys.is_empty() { "multiset" } else { "multiset_order_unchecked" };
        if let Some(flags) = &positional {
            return Ok(Verdict { order: if window.keys.is_empty() { "exact_order" } else { order }, approximate: flags.iter().any(|f| *f), limit_boundary_rows: 0 });
        }
        let approximate = multiset_agree(saved, ours, tolerance).ok_or("the rows are not the same multiset")?;
        return Ok(Verdict { order, approximate, limit_boundary_rows: 0 });
    }
    if let Some(flags) = positional {
        return Ok(Verdict { order: "exact_order", approximate: flags.iter().any(|f| *f), limit_boundary_rows: 0 });
    }
    for (i, (a, b)) in saved.iter().zip(ours).enumerate() {
        if window.keys.iter().any(|(c, _, _)| values_agree(&a[*c], &b[*c], tolerance).is_none()) {
            return Err(format!("the ORDER BY key sequence differs at row {i}: saved {a:?}, ours {b:?}"));
        }
    }
    let mut verdict = Verdict { order: "exact_order", approximate: false, limit_boundary_rows: 0 };
    // Only a window that actually cuts the ordered result has boundary tie classes: the last class when LIMIT binds
    // (the window holds LIMIT rows), the first when OFFSET skips rows.
    let limit_binds = window.limit.is_some_and(|limit| ours.len() as u64 == limit);
    let offset_cuts = window.offset > 0;
    let mut start = 0;
    while start < ours.len() {
        let end = (start + 1..ours.len()).find(|&j| window.row_order(&ours_host[start], &ours_host[j]) != Ordering::Equal).unwrap_or(ours.len());
        match multiset_agree(&saved[start..end], &ours[start..end], tolerance) {
            Some(approximate) => {
                verdict.approximate |= approximate;
                if rows_agree_all(&saved[start..end], &ours[start..end], tolerance).is_none() {
                    verdict.order = "tie_order_differs";
                }
            }
            None if (end == ours.len() && limit_binds) || (start == 0 && offset_cuts) => verdict.limit_boundary_rows += end - start,
            None => return Err(format!("rows {start}..{end} (one ORDER BY tie class) are not the same multiset as the saved answer's")),
        }
        start = end;
    }
    Ok(verdict)
}

/// The tolerance as decimal text (for example `1e-9`): records holding it are content-addressed, where floats are refused.
fn tolerance_text(tolerance: f64) -> String {
    format!("{tolerance:e}")
}

/// Every ORDER BY key names a column of every row (else the order cannot be compared from the output rows).
fn keys_visible(window: &Window, rows: &[Vec<SavedValue>]) -> bool {
    rows.iter().all(|row| window.keys.iter().all(|(c, _, _)| *c < row.len()))
}

fn rows_agree_all(saved: &[Vec<SavedValue>], ours: &[Vec<SavedValue>], tolerance: f64) -> Option<bool> {
    saved.iter().zip(ours).try_fold(false, |approximate, (a, b)| Some(approximate | rows_agree(a, b, tolerance)?))
}

/// Compare our full-data rows at one binding with that binding's saved answers, one verdict per engine. `Ok((status,
/// record))` when at least one engine agrees: status `saved_answers_agree` (every engine) or
/// `saved_answers_agree_partly` (the others' differences recorded). `Err(record)` when none agrees, or our rows are not
/// in ORDER BY order. Not a proof: agreement with other engines under the declared rules.
pub fn compare_with_saved(window: &Window, answers: &[SavedAnswer], ours: &[Vec<HostValue>], tolerance: f64) -> Result<(&'static str, Value), String> {
    if let Some(first) = ours.first()
        && let Some(i) = ours.iter().position(|row| row.len() != first.len())
    {
        return Err(format!("our row {i} has {} columns, row 0 has {}", ours[i].len(), first.len()));
    }
    let values: Vec<Vec<SavedValue>> = ours.iter().map(|row| row.iter().map(SavedValue::of_host).collect()).collect();
    let keys_visible = keys_visible(window, &values);
    if keys_visible {
        window.check_ordered(ours).map_err(|detail| format!("our rows are not in ORDER BY order: {detail}"))?;
    }
    let mut engines = vec![];
    let mut agreeing = 0;
    for answer in answers {
        engines.push(match agreement(window, &answer.rows, &values, ours, tolerance) {
            Ok(verdict) => {
                agreeing += 1;
                let mut record = json!({"engine":answer.engine,"description":answer.description,"path":answer.path,"verdict":"agrees","order":verdict.order,
                    "numeric_within_tolerance_only":verdict.approximate});
                if verdict.limit_boundary_rows > 0 {
                    record["limit_boundary"] = json!({"rows":verdict.limit_boundary_rows,
                        "meaning":"a tie class cut by the window (the last one when LIMIT binds, the first one under OFFSET) holds another choice of that class than this engine's: count and keys agree; whether these rows belong to the full result is not checked here (the proof covers it)"});
                }
                record
            }
            Err(detail) => json!({"engine":answer.engine,"description":answer.description,"path":answer.path,"verdict":"disagrees","detail":detail}),
        });
    }
    let status = if agreeing == answers.len() { "saved_answers_agree" } else { "saved_answers_agree_partly" };
    let record = json!({"status":if agreeing == 0 { "disagrees" } else { status },"agreeing_engines":agreeing,"engines":engines,"numeric_relative_tolerance":tolerance_text(tolerance),
        "order_checked":keys_visible,
        "meaning":"agreement with saved results of other engines (text, integers and dates exactly; other numerics as decimals or within the relative tolerance; ORDER BY tie classes in any order; the last tie class under LIMIT by count and keys only): a check of the trusted base and environment, not a proof; the Verus proof against the fixed SQLSpec entry is the correctness claim"});
    if agreeing == 0 { Err(record.to_string()) } else { Ok((status, record)) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn window(limit: Option<u64>) -> Window {
        Window { keys: vec![(1, true, false)], offset: 0, limit }
    }

    fn row(name: &str, value: &str) -> (Vec<SavedValue>, Vec<HostValue>) {
        let (int, frac) = value.split_once('.').unwrap_or((value, ""));
        let host = HostValue::Num { coeff: format!("{int}{frac}").parse().unwrap(), scale: frac.len() as u32 };
        (vec![SavedValue::Text(name.into()), SavedValue::Decimal(value.into())], vec![HostValue::Text(name.as_bytes().to_vec()), host])
    }

    fn check(w: &Window, saved: &[(Vec<SavedValue>, Vec<HostValue>)], ours: &[(Vec<SavedValue>, Vec<HostValue>)]) -> Result<Verdict, String> {
        let saved: Vec<_> = saved.iter().map(|r| r.0.clone()).collect();
        let values: Vec<_> = ours.iter().map(|r| r.0.clone()).collect();
        let host: Vec<_> = ours.iter().map(|r| r.1.clone()).collect();
        agreement(w, &saved, &values, &host, 1e-9)
    }

    #[test]
    fn agreement_covers_ties_tolerance_integers_and_limit_boundary() {
        let w = window(None);
        let saved = [row("a", "2.0"), row("b", "1.00"), row("c", "1")];
        assert_eq!(check(&w, &saved, &[row("a", "2"), row("b", "1"), row("c", "1")]).unwrap().order, "exact_order");
        assert_eq!(check(&w, &saved, &[row("a", "2"), row("c", "1"), row("b", "1")]).unwrap().order, "tie_order_differs");
        assert!(check(&w, &saved, &[row("b", "1"), row("a", "2"), row("c", "1")]).is_err(), "a permutation across tie classes");
        assert!(check(&w, &saved, &[row("a", "2.0000000001"), row("b", "1"), row("c", "1")]).unwrap().approximate);
        assert!(check(&w, &saved, &[row("a", "2.1"), row("b", "1"), row("c", "1")]).is_err());
        let limited = window(Some(2));
        assert_eq!(check(&limited, &saved[..2], &[row("a", "2"), row("c", "1")]).unwrap().limit_boundary_rows, 1);
        assert!(check(&window(Some(5)), &saved[..2], &[row("a", "2"), row("c", "1")]).is_err(), "LIMIT does not bind: the class is complete");
        assert!(check(&limited, &saved[..2], &[row("a", "2"), row("d", "0.5")]).is_err());
        let int = |t: &str| SavedValue::Int(t.into());
        assert_eq!(values_agree(&int("1000000000"), &int("1000000001"), 1e-9), None, "integers compare exactly");
        assert_eq!(values_agree(&int("7"), &SavedValue::Decimal("7.00".into()), 1e-9), Some(false));
        assert_eq!(values_agree(&SavedValue::Float("inf".into()), &SavedValue::Float("inf".into()), 1e-9), None);
        assert_eq!(values_agree(&SavedValue::Decimal("0.1".into()), &SavedValue::Decimal("0.10000000000000001".into()), 0.0), None);
    }
}
