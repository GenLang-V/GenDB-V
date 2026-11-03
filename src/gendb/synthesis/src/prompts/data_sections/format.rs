//! Text forms shared by the data sections: units (ms with 3 decimals, sizes in GB/MB), Markdown tables and fenced
//! blocks. Display only: every decision is made on the recorded values (ns, bytes) before they are formatted.

use serde_json::Value;

/// A recorded number: a JSON number or a decimal string (GenDB writes large or exact values as strings).
pub fn number(value: &Value) -> Option<f64> {
    value.as_f64().or_else(|| value.as_str().and_then(|text| text.parse().ok()))
}

/// Nanoseconds as milliseconds with 3 decimals (1 us resolution); `-` when not recorded.
pub fn ms(ns: &Value) -> String {
    number(ns).map_or_else(|| "-".to_string(), |ns| format!("{:.3}", ns / 1e6))
}

/// Nanoseconds as milliseconds at a resolution that fits their size (whole ms from 100 ms, 1 decimal from 10 ms,
/// 2 from 1 ms, else 3), trailing zeros dropped: `31198.578` -> `31199`, `45.299` -> `45.3`, `0.700` -> `0.7`; `-`
/// when not recorded. The general line's facts use it for long lists of cells.
pub fn ms_rounded(ns: &Value) -> String {
    let Some(ms) = number(ns).map(|ns| ns / 1e6) else { return "-".to_string() };
    let decimals = match ms.abs() {
        m if m >= 100.0 => 0,
        m if m >= 10.0 => 1,
        m if m >= 1.0 => 2,
        _ => 3,
    };
    let text = format!("{ms:.decimals$}");
    if text.contains('.') { text.trim_end_matches('0').trim_end_matches('.').to_string() } else { text }
}

/// A decimal number (a recorded score's G, a ratio) with `decimals` decimals; the recorded text when it is not a number.
pub fn decimal(value: &Value, decimals: usize) -> String {
    number(value).map_or_else(|| plain(value), |n| format!("{n:.decimals$}"))
}

/// Nanoseconds as seconds with 1 decimal; `-` when not recorded.
pub fn seconds(ns: &Value) -> String {
    number(ns).map_or_else(|| "-".to_string(), |ns| format!("{:.1} s", ns / 1e9))
}

/// Bytes in GB (2 decimals) from 1 GB, MB from 1 MB, else bytes; `-` when not recorded.
pub fn size(bytes: &Value) -> String {
    match number(bytes) {
        None => "-".to_string(),
        Some(b) if b >= 1e9 => format!("{:.2} GB", b / 1e9),
        Some(b) if b >= 1e6 => format!("{:.2} MB", b / 1e6),
        Some(b) => format!("{b} B"),
    }
}

/// US dollars with 2 decimals; `-` when not recorded.
pub fn dollars(usd: &Value) -> String {
    number(usd).map_or_else(|| "-".to_string(), |usd| format!("${usd:.2}"))
}

/// A recorded value as plain text: a string without quotes, other values as JSON, `-` for null.
pub fn plain(value: &Value) -> String {
    match value {
        Value::Null => "-".to_string(),
        Value::String(text) => text.clone(),
        other => other.to_string(),
    }
}

/// A CPU list such as `0,2,4,...,62` written as `0-62 step 2` when it is one arithmetic progression of at least three
/// CPUs; any other list unchanged.
pub fn cpu_list(text: &str) -> String {
    let cpus: Option<Vec<i64>> = text.split(',').map(|cpu| cpu.trim().parse().ok()).collect();
    let Some(cpus) = cpus.filter(|cpus| cpus.len() >= 3) else { return text.to_string() };
    let step = cpus[1] - cpus[0];
    if step <= 0 || cpus.windows(2).any(|pair| pair[1] - pair[0] != step) {
        return text.to_string();
    }
    let (first, last) = (cpus[0], cpus[cpus.len() - 1]);
    if step == 1 { format!("{first}-{last}") } else { format!("{first}-{last} step {step}") }
}

/// A Markdown table: one header row, alignment per column (right-aligned for numbers), one line per row. Cell text
/// keeps its content; `|` and line breaks are escaped so a cell stays one cell.
pub fn table(header: &[(&str, Align)], rows: &[Vec<String>]) -> Vec<String> {
    let escape = |text: &str| text.replace('|', "\\|").replace('\n', " ");
    let mut lines = vec![
        format!("| {} |", header.iter().map(|(name, _)| escape(name)).collect::<Vec<_>>().join(" | ")),
        format!("|{}|", header.iter().map(|(_, align)| if *align == Align::Right { "---:" } else { "---" }).collect::<Vec<_>>().join("|")),
    ];
    lines.extend(rows.iter().map(|row| format!("| {} |", row.iter().map(|cell| escape(cell)).collect::<Vec<_>>().join(" | "))));
    lines
}

/// Column alignment of a [`table`].
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Align {
    Left,
    Right,
}

/// A fenced block of `text` in language `language`, with a fence longer than any backtick run inside it.
pub fn fenced(language: &str, text: &str) -> Vec<String> {
    let longest_run = text.split(|c| c != '`').map(str::len).max().unwrap_or(0);
    let fence = "`".repeat(longest_run.max(2) + 1);
    vec![format!("{fence}{language}"), text.trim_end().to_string(), fence]
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn units_and_lists_are_lossless_to_their_resolution() {
        assert_eq!((ms(&json!(626061000)), ms(&json!("29627668.4")), ms(&Value::Null)), ("626.061".into(), "29.628".into(), "-".into()));
        assert_eq!((size(&json!(114641618862u64)), size(&json!(61127925)), size(&json!(0))), ("114.64 GB".into(), "61.13 MB".into(), "0 B".into()));
        assert_eq!(cpu_list("0,2,4,6"), "0-6 step 2");
        let rounded: Vec<String> = [31_198_578_000u64, 803_087_000, 45_299_000, 1_500_000, 700_000, 0].iter().map(|ns| ms_rounded(&json!(ns))).collect();
        assert_eq!(rounded, ["31199", "803", "45.3", "1.5", "0.7", "0"]);
        assert_eq!((ms_rounded(&Value::Null), decimal(&json!("7.279588955"), 3), decimal(&json!("x"), 3)), ("-".into(), "7.280".into(), "x".into()));
        assert_eq!((cpu_list("0-63"), cpu_list("1,2,4")), ("0-63".into(), "1,2,4".into()));
        assert_eq!(fenced("markdown", "a ```b``` c")[0], "````markdown");
        assert_eq!(table(&[("a|b", Align::Left), ("n", Align::Right)], &[vec!["x\ny".into(), "1".into()]]), ["| a\\|b | n |", "|---|---:|", "| x y | 1 |"]);
    }
}
