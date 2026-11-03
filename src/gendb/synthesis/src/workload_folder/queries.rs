//! `queries/<name>.sql` of a workload folder: one statement per file, named by the file stem (case kept), with header
//! lines that declare its parameters.
//!
//! Header: the leading lines `-- $<n> <name> <type>`, each optionally followed by ` min <value>`, ` max <value>` (an
//! inclusive domain bound; absent: the whole type, which is the proof domain) or ` = <value>` (a fixed parameter). Types
//! are the frontend's parameter types (`integer`, `bigint`, `numeric(p,s)` written without spaces, `date`, `text`); a
//! `text` parameter has no bounds. They become the request's `parameters` (`ParamRequest`), in header order. The
//! statement's `sql` is the rest of the file, byte for byte. A file without header lines is a concrete statement.
//! Whether every `$n` is declared and used is the frontend's check (`WorkloadFolder::check_queries`).
//!
//! Order: the `queries` setting's list, else the natural order of the stems (`Q2` before `Q10`).

use super::FolderError;
use gendb_frontend::params::{BindingRequest, ParamRequest};
use std::cmp::Ordering;
use std::path::{Path, PathBuf};

/// One query file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FolderQuery {
    /// The file stem: the request query's `name`, its key in bindings, baselines and the output.
    pub name: String,
    pub parameters: Vec<ParamRequest>,
    /// The file's text after the header lines.
    pub sql: String,
    pub file: PathBuf,
}

impl FolderQuery {
    /// Some parameter is free: the statement is a template.
    pub fn is_template(&self) -> bool {
        self.parameters.iter().any(|p| matches!(p.binding, BindingRequest::Free { .. }))
    }
}

/// Read one query file's text, named `name`.
pub fn parse(name: &str, file: &Path, text: &str) -> Result<FolderQuery, FolderError> {
    let mut parameters: Vec<ParamRequest> = vec![];
    let mut rest = text;
    while rest.starts_with("-- $") {
        let end = rest.find('\n').map_or(rest.len(), |i| i + 1);
        let line = rest[..end].trim_end_matches(['\n', '\r']);
        let parameter = header_line(line).map_err(|why| FolderError::new("query_header", format!("{}: {line:?}: {why}", file.display())))?;
        if parameters.iter().any(|p| p.index == parameter.index) {
            return Err(FolderError::new("query_header", format!("{}: ${} is declared twice", file.display(), parameter.index)));
        }
        parameters.push(parameter);
        rest = &rest[end..];
    }
    Ok(FolderQuery { name: name.to_string(), parameters, sql: rest.to_string(), file: file.to_path_buf() })
}

/// One header line `-- $<n> <name> <type>[ min <v>][ max <v>]` or `-- $<n> <name> <type> = <v>`.
fn header_line(line: &str) -> Result<ParamRequest, String> {
    const FORM: &str = "write -- $<n> <name> <type>, optionally followed by min <value>, max <value> or = <value>";
    let body = line.strip_prefix("-- $").ok_or(FORM)?;
    let mut words = body.splitn(3, ' ');
    let index: u32 = words.next().and_then(|n| n.parse().ok()).filter(|n| *n > 0).ok_or(FORM)?;
    let name = words.next().filter(|n| is_name(n)).ok_or(FORM)?.to_string();
    let after_name = words.next().ok_or(FORM)?;
    let (sql_type, domain) = after_name.split_once(' ').unwrap_or((after_name, ""));
    let binding = if let Some(value) = domain.strip_prefix("= ") {
        BindingRequest::Fixed(value.to_string())
    } else {
        let (mut min, mut max) = (None, None);
        let mut words = domain.split(' ').filter(|w| !w.is_empty());
        while let Some(word) = words.next() {
            let slot = match word {
                "min" if min.is_none() && max.is_none() => &mut min,
                "max" if max.is_none() => &mut max,
                _ => return Err(FORM.into()),
            };
            *slot = Some(words.next().ok_or(FORM)?.to_string());
        }
        BindingRequest::Free { min, max }
    };
    Ok(ParamRequest { index, name: Some(name), sql_type: sql_type.to_string(), binding })
}

/// A parameter name: ASCII letters, digits and `_`, not starting with a digit.
fn is_name(text: &str) -> bool {
    text.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_') && text.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Every `queries/*.sql` file of `dir`, in the order of `selection` (each listed stem must exist) or else in the
/// natural order of the stems.
pub fn read_all(dir: &Path, selection: Option<&[String]>) -> Result<Vec<FolderQuery>, FolderError> {
    let entries = std::fs::read_dir(dir).map_err(|e| FolderError::new("folder_invalid", format!("{}: {e} (a workload folder has queries/<name>.sql files)", dir.display())))?;
    let mut files: Vec<(String, PathBuf)> = vec![];
    for entry in entries {
        let path = entry.map_err(|e| FolderError::new("folder_invalid", format!("{}: {e}", dir.display())))?.path();
        if path.extension().is_some_and(|e| e == "sql") {
            let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or_default().to_string();
            if stem.is_empty() || !stem.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-') {
                return Err(FolderError::new("query_name", format!("{}: a query file is named <name>.sql, the name of ASCII letters, digits, _ and -", path.display())));
            }
            files.push((stem, path));
        }
    }
    files.sort_by(|a, b| natural_order(&a.0, &b.0));
    let chosen: Vec<(String, PathBuf)> = match selection {
        None => files,
        Some(names) => {
            let mut chosen = vec![];
            for name in names {
                let file = files.iter().find(|(stem, _)| stem == name).ok_or_else(|| FolderError::new("query_missing", format!("the queries setting names {name}, but {} has no {name}.sql", dir.display())))?;
                if chosen.iter().any(|(stem, _): &(String, PathBuf)| stem == name) {
                    return Err(FolderError::new("settings_invalid", format!("the queries setting names {name} twice")));
                }
                chosen.push(file.clone());
            }
            chosen
        }
    };
    if chosen.is_empty() {
        return Err(FolderError::new("folder_invalid", format!("{} has no query file", dir.display())));
    }
    chosen
        .iter()
        .map(|(stem, path)| {
            let text = std::fs::read_to_string(path).map_err(|e| FolderError::new("folder_invalid", format!("{}: {e}", path.display())))?;
            parse(stem, path, &text)
        })
        .collect()
}

/// Natural order: runs of digits compare as numbers, everything else as text (`Q2` < `Q10`, `sf1` < `sf10` < `sf100`).
pub fn natural_order(a: &str, b: &str) -> Ordering {
    let chunks = |text: &str| -> Vec<(bool, String)> {
        let mut out: Vec<(bool, String)> = vec![];
        for c in text.chars() {
            let digit = c.is_ascii_digit();
            match out.last_mut() {
                Some((was_digit, chunk)) if *was_digit == digit => chunk.push(c),
                _ => out.push((digit, c.to_string())),
            }
        }
        out
    };
    let (x, y) = (chunks(a), chunks(b));
    for ((xd, xs), (yd, ys)) in x.iter().zip(&y) {
        let order = match (xd, yd) {
            (true, true) => {
                let (xt, yt) = (xs.trim_start_matches('0'), ys.trim_start_matches('0'));
                xt.len().cmp(&yt.len()).then_with(|| xt.cmp(yt)).then_with(|| xs.len().cmp(&ys.len()))
            }
            _ => xs.cmp(ys),
        };
        if order != Ordering::Equal {
            return order;
        }
    }
    x.len().cmp(&y.len())
}
