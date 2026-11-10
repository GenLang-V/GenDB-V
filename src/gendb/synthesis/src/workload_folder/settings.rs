//! `gendb.toml` of a workload folder: the run's settings, every one optional with a default. The values come from the
//! folder's `gendb.toml`, then a `--config FILE`, then command-line flags; a later source wins per setting
//! ([`Settings::overlay`]). Relative paths resolve against the directory of the file that sets them.
//!
//! | setting | default | sets |
//! |---|---|---|
//! | `name` | the folder name, lower case, other characters `_` | `engine.workloads.name`, a member's name |
//! | `mode` | `"templates"` | `queries[]` (templates) or an `engine` section, line `general` (engine) |
//! | `queries` | every query file, natural order | which query files, in this order |
//! | `scale` | the only scale under `data/` | templates: the dataset's locations, capture and storage budget |
//! | `scales` | every scale under `data/`, natural order | engine: the scale ladder |
//! | `threads` | `[1]` | `hardware.threads` |
//! | `goal` | `"fast"` | `fast`: the execution-time objective; `correct`: the correctness objective, bindings as `test_bindings` |
//! | `storage` | `"designed"` | `designed`: `physical_only` with a storage session; `plain`: `fixed_flat` |
//! | `storage_budget_bytes` | the data size | `data_allowance.live_bytes` (and an engine scale's data size) |
//! | `max_submissions` | `3` | each session's `max_iterations` |
//! | `session_budget_usd` | unset | each query session's `max_cost_usd` |
//! | `budget_usd` | none; required in engine mode | `engine.limits.max_cost_usd` |
//! | `speedup` | `5` | `early_stop.min_speedup` (only with targets) |
//! | `compare_with` | `"duckdb"` | `duckdb`: targets and saved answers from the DuckDB helper; `none`: neither |
//! | `baselines` | none | a saved baselines folder (`baselines.json`) used instead of measuring |
//! | `numeric_tolerance` | `"1e-9"` | `validation.numeric_relative_tolerance` |
//! | `parallel_queries` | `5` | `max_concurrent_queries` |
//! | `parallel_preparations` | `1` | `max_concurrent_preparations` |
//! | `model` | `claude-opus-5-5` | `author_model` |
//! | `start_from` | none | engine: `RUN:VERSION` (`engine.seed_version`) or an exported engine folder (the primary seed); templates: a work folder |
//! | `capture` | the run's own | `prepared_workload` (another run's capture) |
//! | `timing_binding`, `branches`, `call_limit_seconds`, `memory_limit_bytes`, `emphasis`, `one_engine`, `reuse` | `v0`, `1`, `60`, the host's memory, none, false, none | the engine section's fields of the same meaning |
//! | `timed_calls` | `3` | `engine.timed_calls`: the hot calls of every timed cell during the run (a cell's time is their median) |
//! | `[[members]]` `folder`, `role`, `start_from` | none | `engine.workloads.members[]` |

use super::FolderError;
use crate::controller::request::{EngineEmphasis, MemberRole};
use serde::Deserialize;
use std::path::{Path, PathBuf};

/// The settings file of a workload folder.
pub const SETTINGS_FILE: &str = "gendb.toml";

/// What a run makes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Mode {
    /// One verified program per query file.
    Templates,
    /// One verified engine for every query on the schema, made fast on the query files.
    Engine,
}

/// What a template session optimizes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Goal {
    Fast,
    Correct,
}

/// Which storage the programs read.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Storage {
    /// Storages the authors design and prove (`physical_only`).
    Designed,
    /// GenDB's fixed flat storage: plain typed arrays (`fixed_flat`).
    Plain,
}

/// Which other engine gives targets and saved answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum CompareWith {
    Duckdb,
    None,
}

/// A decimal number written as a TOML string or integer (dollars, a tolerance).
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(untagged)]
pub enum DecimalText {
    Text(String),
    Integer(i64),
}

impl DecimalText {
    pub fn text(&self) -> String {
        match self {
            DecimalText::Text(text) => text.clone(),
            DecimalText::Integer(n) => n.to_string(),
        }
    }
}

/// One `[[members]]` entry of an engine run: another workload folder served by the same engine.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MemberSetting {
    pub folder: PathBuf,
    pub role: MemberRole,
    #[serde(default)]
    pub start_from: Option<String>,
}

/// The settings of a run; `None` is the default (the accessors give it).
#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Settings {
    pub name: Option<String>,
    pub mode: Option<Mode>,
    pub queries: Option<Vec<String>>,
    pub scale: Option<String>,
    pub scales: Option<Vec<String>>,
    pub threads: Option<Vec<usize>>,
    pub goal: Option<Goal>,
    pub storage: Option<Storage>,
    pub storage_budget_bytes: Option<u64>,
    pub max_submissions: Option<u32>,
    pub session_budget_usd: Option<DecimalText>,
    pub budget_usd: Option<DecimalText>,
    pub speedup: Option<u32>,
    pub compare_with: Option<CompareWith>,
    pub baselines: Option<PathBuf>,
    pub numeric_tolerance: Option<DecimalText>,
    pub parallel_queries: Option<usize>,
    pub parallel_preparations: Option<usize>,
    pub model: Option<String>,
    pub start_from: Option<String>,
    pub capture: Option<PathBuf>,
    pub timing_binding: Option<String>,
    pub branches: Option<u32>,
    pub call_limit_seconds: Option<u64>,
    pub timed_calls: Option<u32>,
    pub memory_limit_bytes: Option<u64>,
    pub emphasis: Option<EngineEmphasis>,
    pub one_engine: Option<bool>,
    pub reuse: Option<Vec<PathBuf>>,
    pub members: Option<Vec<MemberSetting>>,
}

/// Where a run starts from (`start_from`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StartFrom {
    /// `RUN:VERSION`: an accepted version of another engine run.
    Version { run: PathBuf, version: String },
    /// A folder: an exported engine (engine mode) or the work folder of an earlier run (templates mode).
    Folder(PathBuf),
}

impl StartFrom {
    /// `RUN:VERSION` when the text after the last `:` is a version id (letters and digits), else a folder.
    pub fn parse(text: &str) -> StartFrom {
        match text.rsplit_once(':') {
            Some((run, version)) if !run.is_empty() && !version.is_empty() && version.chars().all(|c| c.is_ascii_alphanumeric()) => {
                StartFrom::Version { run: PathBuf::from(run), version: version.to_string() }
            }
            _ => StartFrom::Folder(PathBuf::from(text)),
        }
    }
}

impl Settings {
    /// The settings of `folder`: its `gendb.toml` (if any), then `config` (if given) on top.
    pub fn read(folder: &Path, config: Option<&Path>) -> Result<Settings, FolderError> {
        let own = folder.join(SETTINGS_FILE);
        let mut settings = if own.is_file() { Settings::parse_file(&own)? } else { Settings::default() };
        if let Some(config) = config {
            settings = settings.overlay(Settings::parse_file(config)?);
        }
        Ok(settings)
    }

    /// One settings file, its relative paths resolved against its directory.
    pub fn parse_file(file: &Path) -> Result<Settings, FolderError> {
        let text = std::fs::read_to_string(file).map_err(|e| FolderError::new("settings_invalid", format!("{}: {e}", file.display())))?;
        let settings: Settings = toml::from_str(&text).map_err(|e| FolderError::new("settings_invalid", format!("{}: {e}", file.display())))?;
        Ok(settings.resolved(file.parent().unwrap_or(Path::new("."))))
    }

    /// Every setting `top` gives replaces this one's.
    pub fn overlay(self, top: Settings) -> Settings {
        macro_rules! pick {
            ($($field:ident),* $(,)?) => { Settings { $($field: top.$field.or(self.$field)),* } };
        }
        pick!(
            name, mode, queries, scale, scales, threads, goal, storage, storage_budget_bytes, max_submissions, session_budget_usd, budget_usd, speedup,
            compare_with, baselines, numeric_tolerance, parallel_queries, parallel_preparations, model, start_from, capture, timing_binding, branches,
            call_limit_seconds, timed_calls, memory_limit_bytes, emphasis, one_engine, reuse, members,
        )
    }

    /// The fields every workload of one engine shares (`hardware.threads`, `engine.{branches, call_limit_seconds,
    /// timed_calls, anon_memory_limit_bytes}`) and the budget (a member's request states it; the run's budget is the
    /// primary's) taken from `primary`: the settings a member's request is written with.
    pub fn with_shared_from(mut self, primary: &Settings) -> Settings {
        self.threads = primary.threads.clone();
        self.budget_usd = primary.budget_usd.clone();
        self.branches = primary.branches;
        self.call_limit_seconds = primary.call_limit_seconds;
        self.timed_calls = primary.timed_calls;
        self.memory_limit_bytes = primary.memory_limit_bytes;
        self
    }

    /// Relative paths made absolute against `base`.
    fn resolved(mut self, base: &Path) -> Settings {
        let absolute = |p: &mut PathBuf| {
            if p.is_relative() {
                *p = base.join(&*p);
            }
        };
        self.baselines.iter_mut().for_each(absolute);
        self.capture.iter_mut().for_each(absolute);
        self.reuse.iter_mut().flatten().for_each(absolute);
        let resolve_start = |text: &mut String| {
            *text = match StartFrom::parse(text) {
                StartFrom::Version { mut run, version } => {
                    absolute(&mut run);
                    format!("{}:{version}", run.display())
                }
                StartFrom::Folder(mut folder) => {
                    absolute(&mut folder);
                    folder.display().to_string()
                }
            }
        };
        self.start_from.iter_mut().for_each(resolve_start);
        for member in self.members.iter_mut().flatten() {
            absolute(&mut member.folder);
            member.start_from.iter_mut().for_each(resolve_start);
        }
        self
    }

    /// `name`, else the folder's name in lower case with every character other than a letter, digit or `_` as `_`.
    pub fn name_or(&self, folder: &Path) -> String {
        self.name.clone().unwrap_or_else(|| {
            let base = folder.file_name().map(|n| n.to_string_lossy().to_string()).unwrap_or_default();
            base.to_ascii_lowercase().chars().map(|c| if c.is_ascii_lowercase() || c.is_ascii_digit() { c } else { '_' }).collect()
        })
    }

    pub fn mode(&self) -> Mode {
        self.mode.unwrap_or(Mode::Templates)
    }

    pub fn goal(&self) -> Goal {
        self.goal.unwrap_or(Goal::Fast)
    }

    pub fn storage(&self) -> Storage {
        self.storage.unwrap_or(Storage::Designed)
    }

    pub fn compare_with(&self) -> CompareWith {
        self.compare_with.unwrap_or(CompareWith::Duckdb)
    }

    pub fn threads(&self) -> Vec<usize> {
        self.threads.clone().unwrap_or_else(|| vec![1])
    }

    pub fn max_submissions(&self) -> u32 {
        self.max_submissions.unwrap_or(3)
    }

    pub fn speedup(&self) -> u32 {
        self.speedup.unwrap_or(5)
    }

    pub fn numeric_tolerance(&self) -> String {
        self.numeric_tolerance.as_ref().map_or_else(|| "1e-9".to_string(), DecimalText::text)
    }

    pub fn parallel_queries(&self) -> usize {
        self.parallel_queries.unwrap_or(5)
    }

    pub fn parallel_preparations(&self) -> usize {
        self.parallel_preparations.unwrap_or(1)
    }

    pub fn timing_binding(&self) -> String {
        self.timing_binding.clone().unwrap_or_else(|| "v0".into())
    }

    pub fn branches(&self) -> u32 {
        self.branches.unwrap_or(1)
    }

    pub fn call_limit_seconds(&self) -> u64 {
        self.call_limit_seconds.unwrap_or(60)
    }

    /// `memory_limit_bytes`, else the host's memory (`MemTotal` of `/proc/meminfo`).
    pub fn memory_limit_bytes(&self) -> Result<u64, FolderError> {
        if let Some(bytes) = self.memory_limit_bytes {
            return Ok(bytes);
        }
        let meminfo = std::fs::read_to_string("/proc/meminfo").unwrap_or_default();
        let kib = meminfo.lines().find_map(|l| l.strip_prefix("MemTotal:")).and_then(|v| v.trim().trim_end_matches("kB").trim().parse::<u64>().ok());
        kib.map(|k| k * 1024).ok_or_else(|| FolderError::new("settings_invalid", "memory_limit_bytes: the host's memory cannot be read from /proc/meminfo; set memory_limit_bytes"))
    }

    pub fn one_engine(&self) -> bool {
        self.one_engine.unwrap_or(false)
    }

    pub fn start(&self) -> Option<StartFrom> {
        self.start_from.as_deref().map(StartFrom::parse)
    }
}
