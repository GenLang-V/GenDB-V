//! Engine totals and the stop decision of a schema-engine run, computed purely from saved records: no measurement, no
//! baseline rerun.
//!
//! Inputs:
//! - the saved DuckDB and Umbra baselines ([`Baselines`], `output/tpch-sf100/baselines/targets.json`): per template,
//!   binding and worker count, each engine's hot median and the DuckDB/Umbra answer agreement;
//! - one engine version's hot medians at the timing binding ([`EngineMedians`]), from its official matrix
//!   (`super::timing::EngineMatrix::medians`).
//!
//! Output ([`TotalsReport`]), per worker count: the engine's total (the sum of its per-template hot medians), DuckDB's
//! and Umbra's totals, the gap to the faster engine's total, the ratios, and the margin reached; per template the medians
//! and agreement; the qualifications as data; and the stop decision:
//! **stop exactly when, at every worker count, every template has a checked engine median and the engine's total is
//! below both Umbra's and DuckDB's totals** (stop margin 1.0: below, not by a factor; the margin reached is reported).
//!
//! Units: every time is whole nanoseconds (`_ns`). Saved millisecond values are converted exactly from their decimal
//! text (at most 6 fractional digits); ratios and margins are reported as `f64` and decide nothing: the stop compares
//! integers. Nothing here is a performance claim; it is arithmetic over recorded medians.

use serde::Serialize;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::Path;

/// The stop margin: the engine's total must be below each baseline total, i.e.
/// `margin > 1.0`. It is a fixed part of the stop rule, not a tuning knob.
pub const STOP_MARGIN: f64 = 1.0;

/// The stop rule as recorded with every decision.
pub const STOP_RULE: &str = "stop when, at every worker count, every template has a checked engine hot median at the timing binding and \
the engine's total (sum of the template medians) is below Umbra's total and below DuckDB's total (stop margin 1.0; the margin reached \
is min over worker counts of min(Umbra, DuckDB total) / engine total); other bindings' totals are reported, never a stop condition";

/// A saved record that cannot be read as this module needs it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TotalsError(pub String);

impl fmt::Display for TotalsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for TotalsError {}

/// The saved baseline medians of one template, binding and worker count.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BaselineCell {
    pub duckdb_ns: u64,
    /// Umbra's median; `None` when Umbra did not time this statement (`umbra_ms` absent: a statement measured on DuckDB
    /// alone after Umbra's TPC-H store was deleted). DuckDB is always measured.
    pub umbra_ns: Option<u64>,
    /// DuckDB/Umbra agreement of their answers (`exact-order`, `order-only`, `decimal-scale`; baselines README), or what
    /// the saved answer is when only DuckDB ran (`duckdb_only`).
    pub agreement: String,
}

impl BaselineCell {
    /// The faster measured baseline's median.
    pub fn faster_ns(&self) -> u64 {
        self.umbra_ns.map_or(self.duckdb_ns, |u| u.min(self.duckdb_ns))
    }
}

/// The faster baseline total and its engine from DuckDB's total and Umbra's (`None`: Umbra did not time every template,
/// so its total is not comparable and DuckDB's is the target).
pub fn target_of(duckdb_ns: u64, umbra_ns: Option<u64>) -> (u64, &'static str) {
    match umbra_ns {
        Some(umbra) if umbra <= duckdb_ns => (umbra, "umbra"),
        _ => (duckdb_ns, "duckdb"),
    }
}

/// The saved baselines: `(template, binding, workers)` -> cell.
#[derive(Clone, Debug, Default)]
pub struct Baselines {
    cells: BTreeMap<(String, String, usize), BaselineCell>,
}

impl Baselines {
    /// Read `targets.json` (`{template: {binding: {workers: {duckdb_ms, umbra_ms, target_ms, agreement}}}}`; `umbra_ms`
    /// absent or null where Umbra did not time the statement).
    pub fn read(path: &Path) -> Result<Self, TotalsError> {
        let text = std::fs::read_to_string(path).map_err(|e| TotalsError(format!("{}: {e}", path.display())))?;
        Self::from_targets_json(&text).map_err(|e| TotalsError(format!("{}: {e}", path.display())))
    }

    pub fn from_targets_json(text: &str) -> Result<Self, TotalsError> {
        let root: Value = serde_json::from_str(text).map_err(|e| TotalsError(format!("not JSON: {e}")))?;
        let mut cells = BTreeMap::new();
        for (template, bindings) in object(&root, "targets")? {
            for (binding, by_workers) in object(bindings, template)? {
                for (workers, cell) in object(by_workers, binding)? {
                    let at = format!("{template}/{binding}/{workers}");
                    let workers: usize = workers.parse().map_err(|_| TotalsError(format!("{at}: worker count is not a number")))?;
                    let agreement = cell["agreement"].as_str().ok_or_else(|| TotalsError(format!("{at}: agreement missing")))?.to_string();
                    let umbra_ns = if cell.get("umbra_ms").is_none_or(Value::is_null) { None } else { Some(ms_field(cell, "umbra_ms", &at)?) };
                    let cell = BaselineCell { duckdb_ns: ms_field(cell, "duckdb_ms", &at)?, umbra_ns, agreement };
                    cells.insert((template.clone(), binding.clone(), workers), cell);
                }
            }
        }
        Ok(Self { cells })
    }

    pub fn cell(&self, template: &str, binding: &str, workers: usize) -> Option<&BaselineCell> {
        self.cells.get(&(template.to_string(), binding.to_string(), workers))
    }

    /// Number of (template, binding, workers) cells.
    pub fn cell_count(&self) -> usize {
        self.cells.len()
    }

    /// Every template with a baseline cell, in name order.
    pub fn templates(&self) -> BTreeSet<&str> {
        self.cells.keys().map(|(t, _, _)| t.as_str()).collect()
    }

    /// The baseline totals of one binding and worker count over `templates`: (DuckDB, Umbra), Umbra's `None` unless it
    /// timed every one of them. A missing cell is an error (every saved baseline cell exists: 198/198 in the baselines
    /// README).
    pub fn totals(&self, templates: &BTreeSet<&str>, binding: &str, workers: usize) -> Result<(u64, Option<u64>), TotalsError> {
        let (mut duckdb, mut umbra) = (0u64, Some(0u64));
        for template in templates {
            let cell = self.cell(template, binding, workers).ok_or_else(|| TotalsError(format!("no baseline cell {template}/{binding}/{workers}")))?;
            duckdb += cell.duckdb_ns;
            umbra = umbra.zip(cell.umbra_ns).map(|(total, cell)| total + cell);
        }
        Ok((duckdb, umbra))
    }
}

fn object<'a>(value: &'a Value, at: &str) -> Result<&'a serde_json::Map<String, Value>, TotalsError> {
    value.as_object().ok_or_else(|| TotalsError(format!("{at}: not an object")))
}

fn ms_field(cell: &Value, field: &str, at: &str) -> Result<u64, TotalsError> {
    let number = cell.get(field).filter(|v| v.is_number()).ok_or_else(|| TotalsError(format!("{at}: {field} missing")))?;
    ms_text_to_ns(&number.to_string()).map_err(|e| TotalsError(format!("{at}: {field}: {e}")))
}

/// Exact conversion of a recorded millisecond value (decimal text, at most 6 fractional digits, no exponent, not
/// negative) to whole nanoseconds.
pub fn ms_text_to_ns(text: &str) -> Result<u64, TotalsError> {
    let refuse = || TotalsError(format!("{text} is not a non-negative millisecond value with at most 6 fractional digits"));
    let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
    let digits = |s: &str| s.bytes().all(|b| b.is_ascii_digit());
    if whole.is_empty() || !digits(whole) || !digits(fraction) || fraction.len() > 6 {
        return Err(refuse());
    }
    let whole: u64 = whole.parse().map_err(|_| refuse())?;
    let fraction: u64 = if fraction.is_empty() { 0 } else { format!("{fraction:0<6}").parse().map_err(|_| refuse())? };
    whole.checked_mul(1_000_000).and_then(|ns| ns.checked_add(fraction)).ok_or_else(refuse)
}

/// One engine median: the hot median of a template at one worker count and whether its answer was checked (equal to
/// a reference or agreeing with the saved answers: `admission::validation::checked_cell_status`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct EngineMedian {
    pub median_ns: u64,
    pub checked: bool,
}

/// One engine version's hot medians at one binding: `(template, workers)` -> median.
#[derive(Clone, Debug, Default)]
pub struct EngineMedians {
    pub binding: String,
    cells: BTreeMap<(String, usize), EngineMedian>,
}

impl EngineMedians {
    pub fn new(binding: impl Into<String>) -> Self {
        Self { binding: binding.into(), cells: BTreeMap::new() }
    }

    /// Record one cell; a second value for the same cell is an error (a matrix has one median per cell).
    pub fn insert(&mut self, template: &str, workers: usize, median: EngineMedian) -> Result<(), TotalsError> {
        match self.cells.insert((template.to_string(), workers), median) {
            None => Ok(()),
            Some(_) => Err(TotalsError(format!("two medians for {template} at {workers} workers"))),
        }
    }

    pub fn get(&self, template: &str, workers: usize) -> Option<EngineMedian> {
        self.cells.get(&(template.to_string(), workers)).copied()
    }
}

/// The totals of one worker count.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct WorkerTotals {
    pub workers: usize,
    /// Sum of the engine's template medians; `None` unless every template has a median.
    pub engine_ns: Option<u64>,
    pub duckdb_ns: u64,
    pub umbra_ns: u64,
    /// The faster baseline total, `min(duckdb_ns, umbra_ns)`, and its engine (`umbra` or `duckdb`).
    pub target_ns: u64,
    pub target_engine: &'static str,
    /// `engine_ns - target_ns` (negative: below the faster baseline total).
    pub gap_ns: Option<i128>,
    pub ratio_to_umbra: Option<f64>,
    pub ratio_to_duckdb: Option<f64>,
    /// `target_ns / engine_ns`: how many times below the faster baseline total the engine is (above 1.0: below it).
    pub margin: Option<f64>,
    /// Every template has a checked median and the total is below both baseline totals.
    pub below_both: bool,
    /// Templates without an engine median at this worker count.
    pub missing_templates: Vec<String>,
    /// Templates whose median's answer was not checked (`EngineMedian::checked` false).
    pub unchecked_templates: Vec<String>,
}

/// One template at one worker count.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct TemplateRow {
    pub template: String,
    pub workers: usize,
    pub engine: Option<EngineMedian>,
    pub duckdb_ns: u64,
    pub umbra_ns: u64,
    pub agreement: String,
    /// Engine median over the faster baseline median of this template (report only).
    pub ratio_to_faster: Option<f64>,
    /// This template's share of Umbra's total at this worker count, in permille rounded to the nearest ("where the time
    /// is").
    pub umbra_share_permille: u64,
}

/// A qualification of the comparison, as data from the saved baselines (never hand-listed).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Qualification {
    pub template: String,
    pub binding: String,
    pub workers: Vec<usize>,
    pub agreement: String,
    pub meaning: &'static str,
}

/// The stop decision.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct StopDecision {
    pub stop: bool,
    pub stop_margin: f64,
    /// Min over worker counts of the margin; `None` unless every worker count has a total.
    pub margin_reached: Option<f64>,
    pub rule: &'static str,
    /// Why not (empty when `stop`).
    pub reasons: Vec<String>,
}

/// Totals, qualifications and the stop decision of one engine version at one binding.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct TotalsReport {
    pub binding: String,
    pub templates_counted: usize,
    pub workers: Vec<WorkerTotals>,
    pub templates: Vec<TemplateRow>,
    pub qualifications: Vec<Qualification>,
    pub stop: StopDecision,
    pub boundary: &'static str,
}

const BOUNDARY: &str = "arithmetic over recorded hot medians (engine: the official matrix, 1 warm + 3 hot calls per cell; baselines: saved \
runs, not rerun); Umbra's time includes client transfer; no performance claim";

/// What a DuckDB/Umbra agreement other than `exact-order` means for the comparison (baselines README, "Agreement").
fn agreement_meaning(agreement: &str) -> &'static str {
    match agreement {
        "decimal-scale" => "Umbra divides NUMERIC to scale 6 and DuckDB returns DOUBLE, so neither returns the exact SQL answer (they agree within one unit at scale 6): a qualified timing comparison",
        "order-only" => "the baselines return the same rows with equal ORDER BY keys (ties) in another order",
        _ => "see the baselines README (Agreement)",
    }
}

/// The totals of `engine` against `baselines` at the engine's binding, over every template with a baseline cell, at
/// each count of `workers`. The stop decision is the run's stop rule only at the timing binding (`v0`); for the other
/// visible bindings (`v1`, `v2`) the same report is information for the stopping version, never a stop condition.
pub fn totals(baselines: &Baselines, engine: &EngineMedians, workers: &[usize]) -> Result<TotalsReport, TotalsError> {
    let templates = baselines.templates();
    let binding = engine.binding.as_str();
    let mut rows = Vec::new();
    let mut per_workers = Vec::new();
    for &w in workers {
        let (duckdb_ns, umbra_ns) = baselines.totals(&templates, binding, w)?;
        // The schema line's stop rule compares with both engines: every template needs both baselines.
        let umbra_ns = umbra_ns.ok_or_else(|| TotalsError(format!("the schema line's totals need Umbra's baseline of every template at {binding}/{w}")))?;
        let (target_ns, target_engine) = target_of(duckdb_ns, Some(umbra_ns));
        let (mut sum, mut missing, mut unchecked) = (0u64, Vec::new(), Vec::new());
        for template in &templates {
            let cell = baselines.cell(template, binding, w).expect("checked by Baselines::totals");
            let cell_umbra_ns = cell.umbra_ns.expect("Umbra's total exists, so every template has its Umbra cell");
            let median = engine.get(template, w);
            match median {
                None => missing.push(template.to_string()),
                Some(m) => {
                    sum += m.median_ns;
                    if !m.checked {
                        unchecked.push(template.to_string());
                    }
                }
            }
            rows.push(TemplateRow {
                template: template.to_string(),
                workers: w,
                engine: median,
                duckdb_ns: cell.duckdb_ns,
                umbra_ns: cell_umbra_ns,
                agreement: cell.agreement.clone(),
                ratio_to_faster: median.map(|m| m.median_ns as f64 / cell.faster_ns().max(1) as f64),
                umbra_share_permille: ((u128::from(cell_umbra_ns) * 2000 + u128::from(umbra_ns)) / (2 * u128::from(umbra_ns.max(1)))) as u64,
            });
        }
        let engine_ns = missing.is_empty().then_some(sum);
        let ratio = |base: u64| engine_ns.map(|e| e as f64 / base.max(1) as f64);
        per_workers.push(WorkerTotals {
            workers: w,
            engine_ns,
            duckdb_ns,
            umbra_ns,
            target_ns,
            target_engine,
            gap_ns: engine_ns.map(|e| i128::from(e) - i128::from(target_ns)),
            ratio_to_umbra: ratio(umbra_ns),
            ratio_to_duckdb: ratio(duckdb_ns),
            margin: engine_ns.map(|e| target_ns as f64 / e.max(1) as f64),
            below_both: engine_ns.is_some_and(|e| e < umbra_ns && e < duckdb_ns) && unchecked.is_empty(),
            missing_templates: missing,
            unchecked_templates: unchecked,
        });
    }
    let stop = stop_decision(&per_workers);
    Ok(TotalsReport {
        binding: binding.to_string(),
        templates_counted: templates.len(),
        workers: per_workers,
        qualifications: qualifications(baselines, &templates, binding, workers),
        templates: rows,
        stop,
        boundary: BOUNDARY,
    })
}

/// Every template whose baselines do not agree exactly at `binding`, with the worker counts where that holds.
fn qualifications(baselines: &Baselines, templates: &BTreeSet<&str>, binding: &str, workers: &[usize]) -> Vec<Qualification> {
    let mut found: BTreeMap<(String, String), Vec<usize>> = BTreeMap::new();
    for template in templates {
        for &w in workers {
            if let Some(cell) = baselines.cell(template, binding, w).filter(|c| c.agreement != "exact-order") {
                found.entry((template.to_string(), cell.agreement.clone())).or_default().push(w);
            }
        }
    }
    found
        .into_iter()
        .map(|((template, agreement), workers)| Qualification { meaning: agreement_meaning(&agreement), template, binding: binding.to_string(), workers, agreement })
        .collect()
}

fn stop_decision(per_workers: &[WorkerTotals]) -> StopDecision {
    let mut reasons = Vec::new();
    for t in per_workers {
        match t.engine_ns {
            None => reasons.push(format!("{} workers: no engine median for {}", t.workers, t.missing_templates.join(", "))),
            Some(_) if !t.unchecked_templates.is_empty() => {
                reasons.push(format!("{} workers: unchecked answers for {}", t.workers, t.unchecked_templates.join(", ")))
            }
            Some(e) => {
                for (name, base) in [("Umbra", t.umbra_ns), ("DuckDB", t.duckdb_ns)] {
                    if e >= base {
                        reasons.push(format!("{} workers: engine total {e} ns is not below {name}'s {base} ns", t.workers));
                    }
                }
            }
        }
    }
    let margins: Option<Vec<f64>> = per_workers.iter().map(|t| t.margin).collect();
    let margin_reached = margins.filter(|m| !m.is_empty()).map(|m| m.into_iter().fold(f64::INFINITY, f64::min));
    if per_workers.is_empty() {
        reasons.push("no worker count".into());
    }
    StopDecision { stop: reasons.is_empty(), stop_margin: STOP_MARGIN, margin_reached, rule: STOP_RULE, reasons }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TARGETS: &str = r#"{
        "Q01": {"v0": {"1": {"duckdb_ms": 10.5, "umbra_ms": 8.25, "target_ms": 8.25, "agreement": "exact-order"},
                       "32": {"duckdb_ms": 2, "umbra_ms": 3, "target_ms": 2, "agreement": "exact-order"}}},
        "Q08": {"v0": {"1": {"duckdb_ms": 20.000001, "umbra_ms": 4, "target_ms": 4, "agreement": "decimal-scale"},
                       "32": {"duckdb_ms": 1, "umbra_ms": 1, "target_ms": 1, "agreement": "decimal-scale"}}}
    }"#;

    fn medians(cells: &[(&str, usize, u64, bool)]) -> EngineMedians {
        let mut m = EngineMedians::new("v0");
        for &(t, w, ns, checked) in cells {
            m.insert(t, w, EngineMedian { median_ns: ns, checked }).unwrap();
        }
        m
    }

    #[test]
    fn milliseconds_convert_exactly() {
        assert_eq!(ms_text_to_ns("21010.746").unwrap(), 21_010_746_000);
        assert_eq!(ms_text_to_ns("781.569993").unwrap(), 781_569_993);
        assert_eq!(ms_text_to_ns("2").unwrap(), 2_000_000);
        for bad in ["1.0000001", "-1", "1e3", "", ".5", "1.2.3"] {
            assert!(ms_text_to_ns(bad).is_err(), "{bad}");
        }
    }

    /// The stop needs every template checked and the total strictly below both baseline totals at every worker count.
    #[test]
    fn stop_needs_every_total_below_both_baselines() {
        let baselines = Baselines::from_targets_json(TARGETS).unwrap();
        // Totals: 1 worker DuckDB 30.500001 ms, Umbra 12.25 ms; 32 workers DuckDB 3 ms, Umbra 4 ms.
        let below = medians(&[("Q01", 1, 6_000_000, true), ("Q08", 1, 6_000_000, true), ("Q01", 32, 1_000_000, true), ("Q08", 32, 1_000_000, true)]);
        let r = totals(&baselines, &below, &[1, 32]).unwrap();
        assert!(r.stop.stop, "{:?}", r.stop);
        assert_eq!((r.workers[0].duckdb_ns, r.workers[0].umbra_ns, r.workers[0].target_engine), (30_500_001, 12_250_000, "umbra"));
        assert_eq!((r.workers[1].target_ns, r.workers[1].target_engine, r.workers[1].gap_ns), (3_000_000, "duckdb", Some(-1_000_000)));
        assert_eq!(r.stop.margin_reached, Some(12.25 / 12.0), "1 worker is the tighter margin");

        let equal = medians(&[("Q01", 1, 6_250_000, true), ("Q08", 1, 6_000_000, true), ("Q01", 32, 1_000_000, true), ("Q08", 32, 1_000_000, true)]);
        let r = totals(&baselines, &equal, &[1, 32]).unwrap();
        assert!(!r.stop.stop && r.stop.reasons[0].contains("not below Umbra"), "{:?}", r.stop);

        let unchecked = medians(&[("Q01", 1, 1, true), ("Q08", 1, 1, false), ("Q01", 32, 1, true), ("Q08", 32, 1, true)]);
        let r = totals(&baselines, &unchecked, &[1, 32]).unwrap();
        assert!(!r.stop.stop && r.workers[0].unchecked_templates == ["Q08"], "{:?}", r.stop);

        let missing = medians(&[("Q01", 1, 1, true), ("Q01", 32, 1, true), ("Q08", 32, 1, true)]);
        let r = totals(&baselines, &missing, &[1, 32]).unwrap();
        assert!(!r.stop.stop && r.workers[0].engine_ns.is_none() && r.stop.margin_reached.is_none());
        assert!(totals(&baselines, &missing, &[64]).is_err(), "no baseline at 64 workers");
    }

    /// A statement timed on DuckDB alone (`umbra_ms` absent or null): its cell has no Umbra median
    /// and DuckDB is its faster baseline; Umbra's total over a set with such a statement does not exist, so DuckDB's is
    /// the target; a set where Umbra timed every template keeps both. The schema line's stop rule needs both engines and
    /// refuses such a set by name.
    #[test]
    fn a_statement_timed_on_duckdb_alone() {
        let text = r#"{
            "Q01": {"v0": {"1": {"duckdb_ms": 10, "umbra_ms": 8, "target_ms": 8, "agreement": "exact-order"}}},
            "U07": {"v0": {"1": {"duckdb_ms": 5, "target_ms": 5, "agreement": "duckdb_only"}}},
            "U12": {"v0": {"1": {"duckdb_ms": 2.5, "umbra_ms": null, "target_ms": 2.5, "agreement": "duckdb_only"}}}
        }"#;
        let baselines = Baselines::from_targets_json(text).unwrap();
        let u07 = baselines.cell("U07", "v0", 1).unwrap();
        assert_eq!((u07.duckdb_ns, u07.umbra_ns, u07.faster_ns()), (5_000_000, None, 5_000_000));
        assert_eq!(baselines.cell("U12", "v0", 1).unwrap().umbra_ns, None, "null is absent");
        assert_eq!(baselines.cell("Q01", "v0", 1).unwrap().faster_ns(), 8_000_000);
        assert_eq!(baselines.totals(&baselines.templates(), "v0", 1).unwrap(), (17_500_000, None));
        assert_eq!(baselines.totals(&BTreeSet::from(["Q01"]), "v0", 1).unwrap(), (10_000_000, Some(8_000_000)));
        assert_eq!(target_of(17_500_000, None), (17_500_000, "duckdb"));
        assert_eq!((target_of(10, Some(8)), target_of(10, Some(12))), ((8, "umbra"), (10, "duckdb")));
        assert!(totals(&baselines, &EngineMedians::new("v0"), &[1]).unwrap_err().0.contains("need Umbra's baseline of every template"));
        assert!(Baselines::from_targets_json(r#"{"U07": {"v0": {"1": {"duckdb_ms": 5, "umbra_ms": "x", "agreement": "duckdb_only"}}}}"#).is_err(), "a present Umbra time is a number");
    }

    #[test]
    fn qualifications_come_from_the_saved_agreement() {
        let baselines = Baselines::from_targets_json(TARGETS).unwrap();
        let r = totals(&baselines, &EngineMedians::new("v0"), &[1, 32]).unwrap();
        assert_eq!(r.qualifications.len(), 1);
        let q = &r.qualifications[0];
        assert_eq!((q.template.as_str(), q.agreement.as_str(), q.workers.clone()), ("Q08", "decimal-scale", vec![1, 32]));
        assert_eq!(r.templates.iter().find(|t| t.template == "Q08" && t.workers == 1).unwrap().umbra_share_permille, 327);
    }

    /// The saved records reproduce every value of a recorded summary table (and the v1/v2 and
    /// "where the time is" values below it). The expected values are copied from that table; the code computes
    /// them from `targets.json` and the two earlier runs' `review/FINAL_MATRIX.json` (their saved per-template medians).
    #[test]
    #[ignore = "reads saved SF100 run records under output/ that are not part of this repository"]
    fn saved_records_reproduce_the_design_table() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
        let baselines = Baselines::read(&root.join("output/tpch-sf100/baselines/targets.json")).unwrap();
        assert_eq!(baselines.cell_count(), 198, "no saved baseline cell is missing: 22 templates x 3 bindings x 3 worker counts");
        let seconds = |ns: u64| {
            let ms = (ns + 500_000) / 1_000_000;
            format!("{}.{:03}", ms / 1000, ms % 1000)
        };
        let factor = |m: Option<f64>| format!("{:.1}x", m.unwrap());
        let mut found = Vec::new();
        for (storage, file) in [("single-copy", "output/tpch-sf100-single-copy/review/FINAL_MATRIX.json"), ("flat", "output/tpch-sf100-flat-storage/review/FINAL_MATRIX.json")] {
            let report = totals(&baselines, &final_matrix_medians(&root.join(file), "v0"), &[1, 32, 64]).unwrap();
            assert_eq!(report.templates_counted, 22);
            for t in &report.workers {
                found.push(format!("v0 {} workers: DuckDB {} Umbra {} target {} ({}) {storage} {} headroom {}", t.workers, seconds(t.duckdb_ns),
                    seconds(t.umbra_ns), seconds(t.target_ns), t.target_engine, seconds(t.engine_ns.unwrap()), factor(t.margin)));
            }
            if storage == "single-copy" {
                let quals: Vec<String> = report.qualifications.iter().map(|q| format!("{} {} {:?}", q.template, q.agreement, q.workers)).collect();
                assert_eq!(quals, ["Q08 decimal-scale [1, 32, 64]", "Q11 order-only [1, 32, 64]", "Q14 decimal-scale [1, 32, 64]"]);
                // "Where the time is": the six largest Umbra shares at 1 worker, each at 1 / 32 / 64 workers.
                let share = |t: &str, w: usize| report.templates.iter().find(|r| r.template == t && r.workers == w).unwrap().umbra_share_permille;
                let mut largest: Vec<(u64, &str)> = report.templates.iter().filter(|r| r.workers == 1).map(|r| (r.umbra_share_permille, r.template.as_str())).collect();
                largest.sort_by(|a, b| b.cmp(a));
                for (_, t) in &largest[..6] {
                    let cells: Vec<String> = [1, 32, 64].iter().map(|&w| format!("{}.{}%", share(t, w) / 10, share(t, w) % 10)).collect();
                    found.push(format!("Umbra share {t}: {}", cells.join(" / ")));
                }
                assert!(report.stop.stop, "the per-template programs beat both totals");
            }
        }
        for binding in ["v1", "v2"] {
            for w in [1, 32, 64] {
                let (d, u) = baselines.totals(&baselines.templates(), binding, w).unwrap();
                let u = u.unwrap();
                found.push(format!("{binding} {w} workers: Umbra {} DuckDB {}", seconds(u), seconds(d)));
            }
        }
        let expected = [
            "v0 1 workers: DuckDB 375.456 Umbra 165.849 target 165.849 (umbra) single-copy 21.361 headroom 7.8x",
            "v0 32 workers: DuckDB 21.566 Umbra 9.987 target 9.987 (umbra) single-copy 1.594 headroom 6.3x",
            "v0 64 workers: DuckDB 16.353 Umbra 11.647 target 11.647 (umbra) single-copy 1.334 headroom 8.7x",
            "Umbra share Q09: 18.2% / 16.8% / 15.6%",
            "Umbra share Q21: 13.2% / 11.6% / 10.4%",
            "Umbra share Q18: 10.6% / 14.7% / 13.1%",
            "Umbra share Q13: 9.6% / 9.5% / 8.8%",
            "Umbra share Q01: 7.6% / 8.0% / 7.5%",
            "Umbra share Q10: 6.3% / 6.0% / 5.9%",
            "v0 1 workers: DuckDB 375.456 Umbra 165.849 target 165.849 (umbra) flat 50.750 headroom 3.3x",
            "v0 32 workers: DuckDB 21.566 Umbra 9.987 target 9.987 (umbra) flat 4.496 headroom 2.2x",
            "v0 64 workers: DuckDB 16.353 Umbra 11.647 target 11.647 (umbra) flat 3.975 headroom 2.9x",
            "v1 1 workers: Umbra 171.040 DuckDB 363.663",
            "v1 32 workers: Umbra 10.309 DuckDB 21.036",
            "v1 64 workers: Umbra 12.245 DuckDB 16.799",
            "v2 1 workers: Umbra 173.422 DuckDB 364.403",
            "v2 32 workers: Umbra 10.332 DuckDB 21.173",
            "v2 64 workers: Umbra 12.046 DuckDB 17.067",
        ];
        assert_eq!(found, expected, "computed:\n{}", found.join("\n"));
    }

    /// The saved per-template GenDB medians of one run at `binding` (`queries[].cells[]`: `binding`, `workers`,
    /// `gendb_ms`, `status`).
    fn final_matrix_medians(path: &Path, binding: &str) -> EngineMedians {
        let matrix: Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
        let mut medians = EngineMedians::new(binding);
        for query in matrix["queries"].as_array().unwrap() {
            for cell in query["cells"].as_array().unwrap().iter().filter(|c| c["binding"] == binding) {
                let median_ns = ms_text_to_ns(&cell["gendb_ms"].to_string()).unwrap();
                let checked = gendb_verification::admission::validation::checked_cell_status(&cell["status"]);
                medians.insert(query["query"].as_str().unwrap(), cell["workers"].as_u64().unwrap() as usize, EngineMedian { median_ns, checked }).unwrap();
            }
        }
        medians
    }
}
