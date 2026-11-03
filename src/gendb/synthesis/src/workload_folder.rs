//! Workload folders: one folder per workload, read into the internal request (format 2, unchanged) that `gendb run`
//! drives through preparation, baselines, synthesis and serving.
//!
//! ```text
//! <folder>/
//!   schema.sql              tables, types, NOT NULL, keys and named CHECKs (`schema`)
//!   queries/<name>.sql      one statement per file; header lines declare its $n (`queries`)
//!   data/<scale>/           <table>.parquet, or <table>/*.parquet in name order; optional MANIFEST.json (`data`)
//!   setup_data.sh           optional: `setup_data.sh SCALE` writes data/SCALE/
//!   bindings.json           optional: example parameter values; bindings/<scale>.json wins for its scale
//!   variants/manifest.json  optional, engine mode: frozen meaning-preserving variants
//!   gendb.toml              optional: settings, each with a default (`settings`)
//! ```
//!
//! [`WorkloadFolder::read`] reads and refuses by name ([`FolderError`]); [`WorkloadFolder::check_queries`] translates
//! every query once with the frontend against the DDL GenDB writes from the request, so an unsupported constraint, a
//! CHECK outside the supported subset, or an undeclared or unused `$n` is refused before any data work or author call;
//! [`WorkloadFolder::check_data`] checks every Parquet file's footer against `schema.sql`. `requests` writes the
//! requests and input files of a run's work folder.
//!
//! `bindings.json` is `{"queries": {"<name>": [{"binding_id": "v0", "arguments": ["..", ..]}, ..]}}`: per query its
//! named argument lists (the free parameters' texts in slot order); other fields are kept and ignored. A concrete
//! statement needs no entry: its one binding is `v0` without arguments.

pub mod data;
pub mod queries;
pub mod requests;
pub mod schema;
pub mod settings;

#[cfg(test)]
mod tests;

use crate::controller::request::WorkloadRequest;
use gendb_frontend::ast::Translation;
use gendb_frontend::params;
use gendb_frontend::parser::SqlParser;
use gendb_verification::admission::dataset_ddl;
use queries::FolderQuery;
use schema::Schema;
use serde_json::{Value, json};
use settings::{Mode, Settings};
use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};

/// The schema file of a workload folder; a directory holding it is a workload folder.
pub const SCHEMA_FILE: &str = "schema.sql";
/// The data preparation script of a workload folder (`setup_data.sh SCALE` writes `data/SCALE/`).
pub const SETUP_SCRIPT: &str = "setup_data.sh";
/// The binding of a concrete statement in a bindings file (the request names it `statement`).
pub const CONCRETE_BINDING_ID: &str = "v0";

/// A named refusal of a workload folder: the reason and what to change.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FolderError {
    /// A stable reason name (`schema_syntax`, `query_header`, `frontend_refusal`, `data_schema`, ...).
    pub reason: &'static str,
    /// The file or setting, what is wrong and the fix.
    pub detail: String,
}

impl FolderError {
    pub fn new(reason: &'static str, detail: impl Into<String>) -> FolderError {
        FolderError { reason, detail: detail.into() }
    }
}

impl fmt::Display for FolderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.reason, self.detail)
    }
}

impl std::error::Error for FolderError {}

/// A workload folder as read: its schema, its queries (the settings' selection, in order) and its settings.
#[derive(Clone, Debug)]
pub struct WorkloadFolder {
    /// The folder (absolute).
    pub root: PathBuf,
    pub schema: Schema,
    pub queries: Vec<FolderQuery>,
    pub settings: Settings,
}

impl WorkloadFolder {
    /// Whether `path` is a workload folder (a directory holding `schema.sql`).
    pub fn is_folder(path: &Path) -> bool {
        path.join(SCHEMA_FILE).is_file()
    }

    /// Read the folder at `root` with `settings` (its `gendb.toml` with any overrides on top: [`Settings::read`] and
    /// [`Settings::overlay`]).
    pub fn read(root: &Path, settings: Settings) -> Result<WorkloadFolder, FolderError> {
        let root = std::path::absolute(root).map_err(|e| FolderError::new("folder_invalid", format!("{}: {e}", root.display())))?;
        let schema_file = root.join(SCHEMA_FILE);
        let text = std::fs::read_to_string(&schema_file).map_err(|e| FolderError::new("folder_invalid", format!("{}: {e} (a workload folder holds schema.sql)", schema_file.display())))?;
        let schema = schema::parse(&text)?;
        let queries = queries::read_all(&root.join("queries"), settings.queries.as_deref())?;
        Ok(WorkloadFolder { root, schema, queries, settings })
    }

    /// The scales under `data/` (its subdirectories), in natural order; empty when there is no `data/`.
    pub fn data_scales(&self) -> Vec<String> {
        let mut scales: Vec<String> = std::fs::read_dir(self.root.join("data"))
            .into_iter()
            .flatten()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().is_dir())
            .filter_map(|e| e.file_name().to_str().map(str::to_string))
            .collect();
        scales.sort_by(|a, b| queries::natural_order(a, b));
        scales
    }

    /// The scales of a run: templates mode one (`scale`, else the only one under `data/`), engine mode the ladder
    /// (`scales`, else every one under `data/`, in natural order).
    pub fn run_scales(&self) -> Result<Vec<String>, FolderError> {
        let found = self.data_scales();
        let scales = match self.settings.mode() {
            Mode::Templates => match (&self.settings.scale, found.as_slice()) {
                (Some(scale), _) => vec![scale.clone()],
                (None, [only]) => vec![only.clone()],
                (None, []) => return Err(FolderError::new("scale_invalid", format!("{}/data has no scale: write data/<scale>/ or set scale (setup_data.sh SCALE writes it)", self.root.display()))),
                (None, several) => return Err(FolderError::new("scale_invalid", format!("{}/data has several scales {several:?}: set scale (or --scale)", self.root.display()))),
            },
            Mode::Engine => match &self.settings.scales {
                Some(scales) if !scales.is_empty() => scales.clone(),
                _ if !found.is_empty() => found,
                _ => return Err(FolderError::new("scale_invalid", format!("{}/data has no scale: write data/<scale>/ or set scales", self.root.display()))),
            },
        };
        if let Some(bad) = scales.iter().find(|s| s.is_empty() || !s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')) {
            return Err(FolderError::new("scale_invalid", format!("scale {bad:?}: a scale name is ASCII letters, digits, _ and -")));
        }
        Ok(scales)
    }

    /// `data/<scale>/`.
    pub fn data_dir(&self, scale: &str) -> PathBuf {
        self.root.join("data").join(scale)
    }

    /// `setup_data.sh`, when the folder has one.
    pub fn setup_script(&self) -> Option<PathBuf> {
        Some(self.root.join(SETUP_SCRIPT)).filter(|p| p.is_file())
    }

    /// `variants/manifest.json`, when the folder has one.
    pub fn variants_manifest(&self) -> Option<PathBuf> {
        Some(self.root.join("variants/manifest.json")).filter(|p| p.is_file())
    }

    /// The source files of every table at `scale`.
    pub fn locations(&self, scale: &str) -> Result<BTreeMap<String, Vec<PathBuf>>, FolderError> {
        data::locations(&self.schema, &self.data_dir(scale))
    }

    /// Check every Parquet file at `scale` against `schema.sql` (footers only).
    pub fn check_data(&self, scale: &str) -> Result<(), FolderError> {
        data::check_files(&self.schema.dataset(&self.locations(scale)?))
    }

    /// The data size at `scale` (the storage budget; `data` module documentation).
    pub fn data_size(&self, scale: &str) -> Result<data::DataSize, FolderError> {
        let dataset = self.schema.dataset(&self.locations(scale)?);
        data::data_size(&self.data_dir(scale), &dataset, self.settings.storage_budget_bytes.map(|b| (b, self.root.as_path())))
    }

    /// The folder's bindings file for `scale` (`bindings/<scale>.json`, else `bindings.json`), if any.
    pub fn bindings_file(&self, scale: &str) -> Option<PathBuf> {
        [self.root.join("bindings").join(format!("{scale}.json")), self.root.join("bindings.json")].into_iter().find(|p| p.is_file())
    }

    /// The visible bindings of the selected queries at `scale`, in the request's bindings-file form
    /// (`{"kind": "visible", "queries": {..}}`): the folder's entries (each checked: a `binding_id` and one argument text
    /// per free parameter), plus `v0` without arguments for a concrete statement the folder lists none for. A template
    /// without an entry is absent.
    pub fn visible_bindings(&self, scale: &str) -> Result<Value, FolderError> {
        let given = match self.bindings_file(scale) {
            Some(file) => {
                let text = std::fs::read_to_string(&file).map_err(|e| FolderError::new("bindings_invalid", format!("{}: {e}", file.display())))?;
                let value: Value = serde_json::from_str(&text).map_err(|e| FolderError::new("bindings_invalid", format!("{}: {e}", file.display())))?;
                if !value["queries"].is_object() {
                    return Err(FolderError::new("bindings_invalid", format!("{}: write {{\"queries\": {{\"<name>\": [{{\"binding_id\", \"arguments\"}}]}}}}", file.display())));
                }
                Some((file, value))
            }
            None => None,
        };
        let mut out = serde_json::Map::new();
        for query in &self.queries {
            let free = query.parameters.iter().filter(|p| matches!(p.binding, params::BindingRequest::Free { .. })).count();
            let listed = given.as_ref().and_then(|(file, value)| value["queries"].get(&query.name).map(|l| (file, l)));
            match listed {
                Some((file, list)) => {
                    let entries = list.as_array().filter(|l| !l.is_empty()).ok_or_else(|| FolderError::new("bindings_invalid", format!("{}: {}: a non-empty list of bindings", file.display(), query.name)))?;
                    let mut seen = vec![];
                    for entry in entries {
                        let id = entry["binding_id"].as_str().filter(|id| !id.is_empty()).ok_or_else(|| FolderError::new("bindings_invalid", format!("{}: {}: a binding without binding_id", file.display(), query.name)))?;
                        let arguments = entry["arguments"].as_array().filter(|a| a.iter().all(Value::is_string));
                        let count = arguments.map(Vec::len).ok_or_else(|| FolderError::new("bindings_invalid", format!("{}: {} {id}: arguments is a list of texts", file.display(), query.name)))?;
                        if count != free {
                            return Err(FolderError::new("bindings_invalid", format!("{}: {} {id}: {count} arguments for {free} free parameters", file.display(), query.name)));
                        }
                        if seen.contains(&id) {
                            return Err(FolderError::new("bindings_invalid", format!("{}: {} {id}: binding_id given twice", file.display(), query.name)));
                        }
                        seen.push(id);
                    }
                    out.insert(query.name.clone(), Value::Array(entries.clone()));
                }
                None if !query.is_template() => {
                    out.insert(query.name.clone(), json!([{"binding_id": CONCRETE_BINDING_ID, "arguments": []}]));
                }
                None => {}
            }
        }
        Ok(json!({"kind": "visible", "queries": out}))
    }

    /// Translate every query with the frontend against the DDL GenDB writes from the request (`dataset_ddl`), with its
    /// declared parameters, and check the declared constraints against the translation; files go under `scratch`. The
    /// refusal lists every query that fails.
    pub fn check_queries(&self, parser: &SqlParser, scratch: &Path) -> Result<(), FolderError> {
        let io = |path: &Path, e: std::io::Error| FolderError::new("folder_invalid", format!("{}: {e}", path.display()));
        std::fs::create_dir_all(scratch).map_err(|e| io(scratch, e))?;
        let (ddl, _) = dataset_ddl(&self.schema.dataset(&BTreeMap::new()), self.schema.constraints.as_ref());
        let schema_file = scratch.join(SCHEMA_FILE);
        std::fs::write(&schema_file, ddl).map_err(|e| io(&schema_file, e))?;
        let mut refusals = vec![];
        for query in &self.queries {
            let sql_file = scratch.join(format!("{}.sql", query.name));
            std::fs::write(&sql_file, &query.sql).map_err(|e| io(&sql_file, e))?;
            let placeholders: Vec<_> = query.parameters.iter().map(params::ParamRequest::placeholder).collect();
            let (_, translation) = parser.translate(&schema_file, &sql_file, "postgres", &placeholders).map_err(|e| FolderError::new("frontend_failure", format!("{}: {e}", query.name)))?;
            let refusal = match translation {
                Translation::Refused(r) => Some(format!("{} at {} ({})", r.reason, r.path, r.detail)),
                Translation::Ok(document) => {
                    let constraints = self.schema.constraints.as_ref().map(|c| c.check_translation(&document.tables)).transpose().err();
                    constraints.or_else(|| params::declare(&document, &query.parameters).err().map(|e| e.to_string()))
                }
            };
            if let Some(refusal) = refusal {
                refusals.push(format!("{} ({}): {refusal}", query.name, query.file.display()));
            }
        }
        if refusals.is_empty() { Ok(()) } else { Err(FolderError::new("frontend_refusal", refusals.join("\n"))) }
    }
}

/// Write `request` as pretty JSON to `path` (directories created), for `gendb` commands to read.
pub fn write_request(path: &Path, request: &WorkloadRequest) -> Result<(), FolderError> {
    let text = serde_json::to_string_pretty(request).map_err(|e| FolderError::new("request_invalid", e.to_string()))?;
    write_text(path, &(text + "\n"))
}

/// Write `text` to `path`, creating its directory.
fn write_text(path: &Path, text: &str) -> Result<(), FolderError> {
    let io = |e: std::io::Error| FolderError::new("folder_invalid", format!("{}: {e}", path.display()));
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).map_err(io)?;
    }
    std::fs::write(path, text).map_err(io)
}
