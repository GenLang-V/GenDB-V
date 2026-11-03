//! Admission bindings of a statement's free parameters: the argument lists at which a candidate is tested on the
//! prepared data and the tiny cases, and the out-of-domain probes the verified entry must refuse.
//!
//! A concrete statement has one empty binding. A template has the user's benchmark bindings of the execution-time
//! objective (named; measured and scored, see [`BenchmarkBinding`]), then the request's test bindings (each inside its
//! declared domain), then the framework's minimum, maximum and interior bindings of the declared domains, each list
//! once. Every binding is tested the same way; none of them is the proof domain, which is the declared domain. A probe
//! puts one parameter one unit (integer, coefficient or day) outside one bound, the others at the interior. A `text`
//! parameter has no bound: the framework bindings give it a non-empty text, the first non-empty value a requested
//! (benchmark, then test) binding gives that parameter, else `A` (an empty text makes most predicates degenerate: an
//! equality or LIKE that matches no row), and its probe is a text holding a NUL byte, outside the text domain (the
//! host's parser refuses such a request text, so only a probe passes it to the verified binder).

use gendb_frontend::params::{FreeParam, ParamType, ParamValue, parse_arguments};
use gendb_runtime::abi::StatementArgument;
use gendb_runtime::serve::{StatementError, statement_arguments};
use serde::{Deserialize, Serialize};
use std::fmt;

/// Name of the one binding of a concrete statement (its benchmark binding, and the binding a target without a
/// `binding` names).
pub const CONCRETE_BINDING: &str = "statement";

/// One user benchmark binding of the execution-time objective: the argument texts of the free parameters in slot
/// order, named. Its name identifies it in runtime targets, measurement cells and records. It is a sample at which a
/// candidate is measured (and, like every binding, tested); it neither narrows nor stands for the proof domain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BenchmarkBinding {
    pub name: String,
    pub arguments: Vec<String>,
}

impl BenchmarkBinding {
    /// Why `name` cannot name a benchmark binding: 1..=64 of `[a-z0-9_]` (it names records and files), and not a name
    /// the framework gives its own bindings.
    pub fn name_refusal(name: &str) -> Option<String> {
        let portable = (1..=64).contains(&name.len()) && name.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_');
        if !portable {
            return Some(format!("benchmark binding name {name:?} must be 1..=64 characters of [a-z0-9_]"));
        }
        let framework = [CONCRETE_BINDING, "minimum", "maximum", "interior"].contains(&name) || name.starts_with("request_") || name.starts_with("outside_");
        framework.then(|| format!("benchmark binding name {name:?} is a framework binding name (statement, minimum, maximum, interior, request_<n>, outside_<...>)"))
    }
}

/// Where an argument binding comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BindingOrigin {
    /// The statement has no free parameter.
    Concrete,
    /// The user's benchmark bindings (execution-time objective).
    Benchmark,
    /// The request's `test_bindings`.
    Request,
    /// Framework bindings from the declared domain.
    Minimum,
    Maximum,
    Interior,
    /// A refusal probe just outside the declared domain.
    OutsideDomain,
}

/// One argument binding of the free parameters (slot order = ascending placeholder index of the free parameters).
#[derive(Clone, Debug, Serialize)]
pub struct Binding {
    pub name: String,
    pub origin: BindingOrigin,
    /// Canonical argument texts.
    pub texts: Vec<String>,
    pub values: Vec<ParamValue>,
    /// The ABI arguments passed to a query entry.
    pub abi: Vec<StatementArgument>,
}

/// Why admission bindings could not be formed.
#[derive(Debug)]
pub enum BindingError {
    /// A request test binding is not a binding of the declared parameters (recorded as the `bindings` refusal).
    TestBinding(String),
    /// Exact parameter values without ABI arguments (never produced by exact parsing).
    Arguments(StatementError),
}

impl fmt::Display for BindingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TestBinding(reason) => f.write_str(reason),
            Self::Arguments(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for BindingError {}

fn binding(free: &[FreeParam], name: String, origin: BindingOrigin, values: Vec<ParamValue>) -> Result<Binding, BindingError> {
    let texts = free.iter().zip(&values).map(|(f, v)| f.ty.text(v)).collect();
    let abi = statement_arguments(&values).map_err(BindingError::Arguments)?;
    Ok(Binding { name, origin, texts, values, abi })
}

/// The user's `benchmark` bindings, then the request's test bindings, then the minimum, maximum and interior
/// bindings; every requested binding must lie in the declared domain, and a binding with the same values as an earlier
/// one is left out (a test binding equal to a benchmark binding is tested as that benchmark binding). Two benchmark
/// bindings with equal values are refused: they would be one measured cell under two names. A concrete statement has
/// the one empty binding `statement` and neither test nor benchmark bindings.
pub fn admission_bindings(free: &[FreeParam], test_bindings: &[Vec<String>], benchmark: &[BenchmarkBinding]) -> Result<Vec<Binding>, BindingError> {
    if free.is_empty() {
        if test_bindings.iter().any(|b| !b.is_empty()) {
            return Err(BindingError::TestBinding("test_bindings name arguments, but the statement has no free parameter".into()));
        }
        if !benchmark.is_empty() {
            return Err(BindingError::TestBinding(format!("benchmark bindings are given, but the statement has no free parameter (its one binding is `{CONCRETE_BINDING}`)")));
        }
        return Ok(vec![binding(free, CONCRETE_BINDING.into(), BindingOrigin::Concrete, vec![])?]);
    }
    let mut out: Vec<Binding> = vec![];
    let mut requested_texts: Vec<Vec<ParamValue>> = vec![];
    for requested in benchmark {
        let what = format!("benchmark binding {}", requested.name);
        let values = requested_values(free, &requested.arguments, &what)?;
        if let Some(same) = out.iter().find(|b| b.values == values || b.name == requested.name) {
            return Err(BindingError::TestBinding(format!("{what} repeats benchmark binding {} (same name or values)", same.name)));
        }
        requested_texts.push(values.clone());
        out.push(binding(free, requested.name.clone(), BindingOrigin::Benchmark, values)?);
    }
    let mut tests = vec![];
    for (i, texts) in test_bindings.iter().enumerate() {
        let values = requested_values(free, texts, &format!("test binding {i}"))?;
        requested_texts.push(values.clone());
        tests.push(binding(free, format!("request_{i}"), BindingOrigin::Request, values)?);
    }
    let seeds = text_seeds(free, &requested_texts);
    let mut push_new = |b: Binding| {
        if !out.iter().any(|x| x.values == b.values) {
            out.push(b);
        }
    };
    for test in tests {
        push_new(test);
    }
    push_new(binding(free, "minimum".into(), BindingOrigin::Minimum, free.iter().zip(&seeds).map(|(f, s)| lower_end(f, s)).collect())?);
    push_new(binding(free, "maximum".into(), BindingOrigin::Maximum, free.iter().zip(&seeds).map(|(f, s)| upper_end(f, s)).collect())?);
    push_new(binding(free, "interior".into(), BindingOrigin::Interior, free.iter().zip(&seeds).map(|(f, s)| midpoint(f, s)).collect())?);
    Ok(out)
}

/// The exact values of requested argument texts, each inside its parameter's declared domain.
fn requested_values(free: &[FreeParam], texts: &[String], what: &str) -> Result<Vec<ParamValue>, BindingError> {
    let values = parse_arguments(free, texts).map_err(|e| BindingError::TestBinding(format!("{what}: {e}")))?;
    for (f, v) in free.iter().zip(&values) {
        if !f.admits(v) {
            return Err(BindingError::TestBinding(format!("{what}: ${} = {} is outside its declared domain {}", f.index, f.ty.text(v), f.domain_text())));
        }
    }
    Ok(values)
}

/// One binding just below and one just above each declared bound (the other parameters interior), where the
/// parameter's type has such a value; for a text parameter one binding with a NUL byte.
pub fn refusal_probes(free: &[FreeParam]) -> Result<Vec<Binding>, BindingError> {
    let seeds = text_seeds(free, &[]);
    let interior: Vec<ParamValue> = free.iter().zip(&seeds).map(|(f, s)| midpoint(f, s)).collect();
    let mut out = vec![];
    for f in free {
        let outside = match f.bounds() {
            Some((min, max)) => vec![("below", step(f.ty, min, -1)), ("above", step(f.ty, max, 1))],
            None => vec![("nul", Some(ParamValue::Text("\0".into())))],
        };
        for (side, outside) in outside {
            if let Some(outside) = outside {
                let mut values = interior.clone();
                values[f.slot] = outside;
                out.push(binding(free, format!("outside_${}_{side}", f.index), BindingOrigin::OutsideDomain, values)?);
            }
        }
    }
    Ok(out)
}

/// Per free parameter, the text its framework bindings take (meaningful for text parameters only): the first non-empty
/// value of that slot among the `requested` bindings, else `A`.
fn text_seeds(free: &[FreeParam], requested: &[Vec<ParamValue>]) -> Vec<ParamValue> {
    free.iter()
        .map(|f| {
            requested
                .iter()
                .filter_map(|values| values.get(f.slot))
                .find(|v| matches!(v, ParamValue::Text(t) if !t.is_empty()))
                .cloned()
                .unwrap_or_else(|| ParamValue::Text("A".into()))
        })
        .collect()
}

/// The least value of the declared domain (`text` for a text parameter, which has no bound).
fn lower_end(f: &FreeParam, text: &ParamValue) -> ParamValue {
    f.bounds().map_or_else(|| text.clone(), |(min, _)| min.clone())
}

/// The greatest value of the declared domain (`text` for a text parameter).
fn upper_end(f: &FreeParam, text: &ParamValue) -> ParamValue {
    f.bounds().map_or_else(|| text.clone(), |(_, max)| max.clone())
}

/// The value halfway between the bounds (rounded down; a date domain gives a valid date; `text` for a text parameter).
fn midpoint(f: &FreeParam, text: &ParamValue) -> ParamValue {
    let Some((min, max)) = f.bounds() else { return text.clone() };
    match (min, max) {
        (ParamValue::Int(a), ParamValue::Int(b)) => ParamValue::Int(((*a as i128 + *b as i128).div_euclid(2)) as i64),
        (ParamValue::Num(a), ParamValue::Num(b)) => ParamValue::Num(a / 2 + b / 2 + (a % 2 + b % 2) / 2),
        (a, b) => match (days_since_1970(a), days_since_1970(b)) {
            (Some(x), Some(y)) => date_at((x + y).div_euclid(2)).unwrap_or_else(|| a.clone()),
            _ => a.clone(),
        },
    }
}

/// `value + delta` units of type `ty` (integer, numeric coefficient or day), if it is a value of the type.
fn step(ty: ParamType, value: &ParamValue, delta: i64) -> Option<ParamValue> {
    let (lo, hi) = ty.range()?;
    let out = match value {
        ParamValue::Int(x) => ParamValue::Int(x.checked_add(delta)?),
        ParamValue::Num(c) => ParamValue::Num(c.checked_add(delta as i128)?),
        ParamValue::Date { .. } => date_at(days_since_1970(value)? + delta)?,
        ParamValue::Text(_) => return None,
    };
    (lo <= out && out <= hi).then_some(out)
}

/// Days since 1970-01-01 of a date value (proleptic Gregorian).
pub(crate) fn days_since_1970(value: &ParamValue) -> Option<i64> {
    match value {
        ParamValue::Date { y, m, d } => Some(days_from_civil(*y as i64, *m as i64, *d as i64)),
        _ => None,
    }
}

/// The date `days` after 1970-01-01, if it is a PostgreSQL-range year (1..=9999).
fn date_at(days: i64) -> Option<ParamValue> {
    let (y, m, d) = civil_from_days(days);
    (1..=9999).contains(&y).then_some(ParamValue::Date { y: y as i32, m: m as u32, d: d as u32 })
}

/// Civil date -> days since 1970-01-01 (Howard Hinnant's algorithm; eras of 400 years).
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let year_of_era = y - era * 400;
    let month_from_march = (m + 9) % 12;
    let day_of_year = (153 * month_from_march + 2) / 5 + d - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146097 + day_of_era - 719468
}

/// Days since 1970-01-01 -> civil date `(year, month, day)`.
fn civil_from_days(z: i64) -> (i64, i64, i64) {
    let z = z + 719468;
    let era = z.div_euclid(146097);
    let day_of_era = z - era * 146097;
    let year_of_era = (day_of_era - day_of_era / 1460 + day_of_era / 36524 - day_of_era / 146096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_from_march = (5 * day_of_year + 2) / 153;
    let d = day_of_year - (153 * month_from_march + 2) / 5 + 1;
    let m = if month_from_march < 10 { month_from_march + 3 } else { month_from_march - 9 };
    (year_of_era + era * 400 + if m <= 2 { 1 } else { 0 }, m, d)
}

#[cfg(test)]
mod tests {
    use super::*;
    use gendb_frontend::params::ParamDomain;

    fn range(index: u32, slot: usize, ty: ParamType, min: ParamValue, max: ParamValue) -> FreeParam {
        FreeParam { index, slot, ty, domain: ParamDomain::Range { min, max } }
    }

    /// Civil dates round-trip; steps stay inside the type; the interior of a date domain is a valid date; bindings and
    /// probes follow the declared domains.
    #[test]
    fn parameter_domain_arithmetic() {
        for (y, m, d) in [(1970, 1, 1), (2000, 2, 29), (1992, 1, 1), (1998, 12, 31), (1, 1, 1), (9999, 12, 31)] {
            assert_eq!(civil_from_days(days_from_civil(y, m, d)), (y, m, d));
        }
        assert_eq!(days_from_civil(1970, 1, 1), 0);
        assert_eq!(days_from_civil(2000, 1, 1), 10957);
        let date = |y, m, d| ParamValue::Date { y, m, d };
        assert_eq!(step(ParamType::Date, &date(1992, 1, 1), -1), Some(date(1991, 12, 31)));
        assert_eq!(step(ParamType::Date, &date(9999, 12, 31), 1), None);
        assert_eq!(step(ParamType::Int4, &ParamValue::Int(i32::MAX as i64), 1), None);
        assert_eq!(step(ParamType::Numeric { precision: 3, scale: 2 }, &ParamValue::Num(100), 1), Some(ParamValue::Num(101)));
        assert_eq!(step(ParamType::Numeric { precision: 3, scale: 2 }, &ParamValue::Num(999), 1), None);
        let f = range(1, 0, ParamType::Date, date(1992, 1, 1), date(1998, 12, 31));
        assert_eq!(midpoint(&f, &ParamValue::Text("A".into())), date(1995, 7, 2));
        let g = range(3, 1, ParamType::Int4, ParamValue::Int(i32::MIN as i64), ParamValue::Int(i32::MAX as i64));
        assert_eq!(midpoint(&g, &ParamValue::Text("A".into())), ParamValue::Int(-1));
        let free = [f, g];
        let bindings = admission_bindings(&free, &[vec!["1994-01-01".into(), "24".into()]], &[]).unwrap();
        assert_eq!(bindings.iter().map(|b| b.name.as_str()).collect::<Vec<_>>(), ["request_0", "minimum", "maximum", "interior"]);
        let outside = admission_bindings(&free, &[vec!["1991-12-31".into(), "24".into()]], &[]).unwrap_err().to_string();
        assert!(outside.contains("is outside its declared domain [1992-01-01, 1998-12-31]"), "{outside}");
        let probes = refusal_probes(&free).unwrap();
        assert_eq!(probes.iter().map(|b| b.texts.clone()).collect::<Vec<_>>(), [["1991-12-31", "-1"], ["1999-01-01", "-1"]], "no int4 probe outside the type");
    }

    /// A text parameter (next to an integer one): its framework bindings take the first non-empty requested text (else
    /// `A`), never the empty text; requested texts are
    /// kept exactly (empty, multi-byte, pattern characters), a NUL is refused, and its probe is a text with a NUL.
    #[test]
    fn text_parameters_have_bindings_and_a_nul_probe() {
        let text = FreeParam { index: 1, slot: 0, ty: ParamType::Text, domain: ParamDomain::AllText };
        let free = [text, range(2, 1, ParamType::Int4, ParamValue::Int(1), ParamValue::Int(50))];
        let pair = |a: &str, b: &str| vec![a.to_string(), b.to_string()];
        let requested = [pair("MEDIUM POLISHED%", "49"), pair("\u{e9}t\u{e9}", "3"), pair("", "1")];
        let bindings = admission_bindings(&free, &requested, &[]).unwrap();
        let listed: Vec<(&str, Vec<String>)> = bindings.iter().map(|b| (b.name.as_str(), b.texts.clone())).collect();
        let expected = [("request_0", pair("MEDIUM POLISHED%", "49")), ("request_1", pair("\u{e9}t\u{e9}", "3")), ("request_2", pair("", "1")),
            ("minimum", pair("MEDIUM POLISHED%", "1")), ("maximum", pair("MEDIUM POLISHED%", "50")), ("interior", pair("MEDIUM POLISHED%", "25"))];
        assert_eq!(listed, expected);
        assert_eq!(bindings[1].abi[0], StatementArgument::Text("\u{e9}t\u{e9}".into()));
        assert!(admission_bindings(&free, &[pair("a\0", "1")], &[]).unwrap_err().to_string().contains("NUL"));
        let probes = refusal_probes(&free).unwrap();
        let named: Vec<(&str, Vec<String>)> = probes.iter().map(|b| (b.name.as_str(), b.texts.clone())).collect();
        assert_eq!(named, [("outside_$1_nul", pair("\0", "25")), ("outside_$2_below", pair("A", "0")), ("outside_$2_above", pair("A", "51"))]);
    }

    /// Benchmark bindings come first under the user's names; an equal test or framework binding is covered by them;
    /// out-of-domain, repeated or concrete-statement benchmark bindings are refused; a concrete statement is unchanged.
    #[test]
    fn benchmark_bindings_are_named_first_and_checked() {
        let size = [range(1, 0, ParamType::Int4, ParamValue::Int(1), ParamValue::Int(50))];
        let bench = |name: &str, x: &str| BenchmarkBinding { name: name.into(), arguments: vec![x.into()] };
        let bindings = admission_bindings(&size, &[vec!["7".into()], vec!["49".into()]], &[bench("qgen", "49"), bench("small", "+3")]).unwrap();
        let names: Vec<&str> = bindings.iter().map(|b| b.name.as_str()).collect();
        assert_eq!(names, ["qgen", "small", "request_0", "minimum", "maximum", "interior"], "request_1 equals qgen; interior 25 is new");
        assert_eq!(bindings[1].texts, ["3"], "canonical texts");
        assert!(bindings[..2].iter().all(|b| b.origin == BindingOrigin::Benchmark));
        let refused = |benchmark: &[BenchmarkBinding]| admission_bindings(&size, &[], benchmark).unwrap_err().to_string();
        assert!(refused(&[bench("big", "51")]).contains("outside its declared domain"));
        assert!(refused(&[bench("a", "3"), bench("b", "03")]).contains("repeats"), "equal values under two names");
        assert!(refused(&[bench("a", "3"), bench("a", "4")]).contains("repeats"));
        let concrete = admission_bindings(&[], &[], &[]).unwrap();
        assert_eq!((concrete.len(), concrete[0].name.as_str(), concrete[0].origin), (1, CONCRETE_BINDING, BindingOrigin::Concrete));
        assert!(admission_bindings(&[], &[], &[bench("a", "3")]).is_err());
        assert!(BenchmarkBinding::name_refusal("qgen_default").is_none());
        for name in ["", "Brand", "a-b", "statement", "minimum", "request_0", "outside_x"] {
            assert!(BenchmarkBinding::name_refusal(name).is_some(), "{name:?}");
        }
    }
}
