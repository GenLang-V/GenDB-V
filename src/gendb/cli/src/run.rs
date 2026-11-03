//! `gendb run FOLDER`: a workload folder (`gendb_synthesis::workload_folder`) driven to its results in steps. Each step
//! is a GenDB command run as a child of this executable, or the DuckDB helper (`baselines/duckdb_baselines.py`); each
//! finished step is recorded in `WORK/run.json` (its exit status and the file of its record), so a rerun skips it.
//! The controller's own records make every command itself resumable.
//!
//! Before any step, every query is translated once by the frontend against the schema GenDB writes, so an unsupported
//! statement, constraint or parameter is refused before any data work or author call.
//!
//! Templates mode (`mode = "templates"`), one scale:
//! 1. `data`: `setup_data.sh SCALE` when `data/SCALE/` is missing; every Parquet footer checked against `schema.sql`;
//! 2. `requests`: the input files (`WORK/inputs/`) and the preparation request `WORK/requests/prepare.json`;
//! 3. `baselines`: the DuckDB helper over the source data (`compare_with = "duckdb"`; timed for `goal = "fast"`,
//!    answers only for `"correct"`) or a saved baselines folder, then the final request `WORK/requests/run.json` (with
//!    `serve.json`), which names the capture the next steps write;
//! 4. `seed` (only with `start_from`, an earlier work folder): that run's storages seeded into this run's library;
//! 5. `prepare`: `gendb preflight` writes the capture (designed storage; not needed when a capture is given), or
//!    `gendb prepare-flat-storage` writes the capture and the flat storages (plain);
//! 6. `preflight` (only with `--until preflight`): `gendb preflight` and `gendb render-query-inputs` of the first query
//!    on the final request, which cost nothing;
//! 7. `synthesize`: `gendb synthesize WORK/requests/run.json` (the workload storage session first when designed).
//!
//! Engine mode (`mode = "engine"`), the scale ladder, and each `[[members]]` folder the same way in its own library:
//! `data`; `requests` (per scale `requests/flat-SCALE.json`); `baselines` (the helper at the timing binding per
//! scale, answers only for a check member); `prepare` (`gendb prepare-flat-storage` per scale), then
//! `requests/engine.json` and `requests/members/NAME.json`; `seed` (`start_from = "RUN:VERSION"`: the seed run's
//! storages); `check` (`gendb engine check-request`, exit 1 stops the run); `preflight` (only with `--until
//! preflight`: `gendb engine render-inputs`); `synthesize` (`gendb engine prepare`, then `gendb engine synthesize`).
//!
//! A request file of an earlier invocation that the folder now writes differently is refused ("use a new --out"): a
//! work folder belongs to one workload and one set of settings.

mod folder_commands;

pub use folder_commands::{FolderCommand, folder_command};

use gendb_frontend::parser::SqlParser;
use gendb_synthesis::controller::request::{MemberRole, WorkloadRequest};
use gendb_synthesis::published::PublishedRun;
use gendb_synthesis::workload_folder::requests::{self, Baselines, FlatStorages, RunContext, ScaleInputs};
use gendb_synthesis::workload_folder::settings::{CompareWith, Goal, Mode, Settings, StartFrom, Storage};
use gendb_synthesis::workload_folder::{WorkloadFolder, write_request};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};

/// The record of a work folder's finished steps.
pub const RUN_RECORD: &str = "run.json";
/// The DuckDB helper, in this source tree.
const DUCKDB_HELPER: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../baselines/duckdb_baselines.py");

pub const USAGE: &str = "usage: gendb run FOLDER [--config FILE] [--mode templates|engine] [--storage designed|plain] [--scale S] \
[--threads 1,8] [--queries Q01,Q06] [--out WORK] [--until data|requests|baselines|prepare|preflight]";

/// Where `--until` stops: after this step (`preflight` adds the free preflight step).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Until {
    Data,
    Requests,
    Baselines,
    Prepare,
    Preflight,
}

impl Until {
    fn parse(word: &str) -> Option<Until> {
        Some(match word {
            "data" => Until::Data,
            "requests" => Until::Requests,
            "prepare" => Until::Prepare,
            "baselines" => Until::Baselines,
            "preflight" => Until::Preflight,
            _ => return None,
        })
    }
}

/// The arguments of `gendb run`.
#[derive(Debug, Default, PartialEq)]
pub struct RunOptions {
    pub folder: PathBuf,
    pub config: Option<PathBuf>,
    /// The command-line settings (`--mode --storage --scale --threads --queries`), on top of the files'.
    pub flags: Settings,
    pub out: Option<PathBuf>,
    pub until: Option<Until>,
}

impl RunOptions {
    /// Parse the words after `gendb run`.
    pub fn parse(words: &[&str]) -> Result<RunOptions, String> {
        let mut options = RunOptions::default();
        let mut folder = None;
        let mut words = words.iter();
        while let Some(&word) = words.next() {
            let mut value = || words.next().copied().ok_or_else(|| format!("{word} needs a value"));
            match word {
                "--config" => options.config = Some(PathBuf::from(value()?)),
                "--out" => options.out = Some(PathBuf::from(value()?)),
                "--mode" => options.flags.mode = Some(setting_word(word, value()?)?),
                "--storage" => options.flags.storage = Some(setting_word(word, value()?)?),
                "--scale" => options.flags.scale = Some(value()?.to_string()),
                "--threads" => {
                    let text = value()?;
                    let threads: Result<Vec<usize>, _> = text.split(',').map(str::parse).collect();
                    options.flags.threads = Some(threads.map_err(|_| format!("--threads {text}: worker counts, comma separated"))?);
                }
                "--queries" => options.flags.queries = Some(value()?.split(',').filter(|q| !q.is_empty()).map(str::to_string).collect()),
                "--until" => {
                    let text = value()?;
                    options.until = Some(Until::parse(text).ok_or_else(|| format!("--until {text}: one of data, requests, baselines, prepare, preflight"))?);
                }
                flag if flag.starts_with("--") => return Err(format!("unknown option {flag}")),
                path if folder.is_none() => folder = Some(PathBuf::from(path)),
                extra => return Err(format!("unexpected argument {extra}")),
            }
        }
        options.folder = folder.ok_or("FOLDER is required")?;
        Ok(options)
    }
}

/// A setting given on the command line as its `gendb.toml` word (`--mode engine`).
fn setting_word<T: serde::de::DeserializeOwned>(flag: &str, word: &str) -> Result<T, String> {
    serde_json::from_value(json!(word)).map_err(|_| format!("{flag} {word}: not a value of this setting"))
}

/// Entry of `gendb run` (the words after it). Prints the run's summary (JSON); exit 0 when every step asked for ran, 1
/// when a step stopped the run (its reason on stderr), 2 for a usage error.
pub fn main(arguments: &[OsString]) -> ExitCode {
    let words: Option<Vec<&str>> = arguments.iter().map(|w| w.to_str()).collect();
    let Some(words) = words else {
        eprintln!("gendb run: arguments must be UTF-8\n{USAGE}");
        return ExitCode::from(2);
    };
    if words.iter().any(|w| matches!(*w, "--help" | "-h")) {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let options = match RunOptions::parse(&words) {
        Ok(options) => options,
        Err(error) => {
            eprintln!("gendb run: {error}\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match Run::open(&options).and_then(|mut run| run.drive(options.until)) {
        Ok(summary) => {
            println!("{}", serde_json::to_string_pretty(&summary).expect("JSON values serialize"));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb run: {error}");
            ExitCode::from(1)
        }
    }
}

/// The folder's settings with `config` and `flags` on top (`gendb.toml`, then `--config`, then the flags).
pub fn effective_settings(folder: &Path, config: Option<&Path>, flags: Settings) -> Result<Settings, String> {
    Ok(Settings::read(folder, config).map_err(|e| e.to_string())?.overlay(flags))
}

/// The default work folder: `FOLDER/runs/<mode>[-<storage>]-<scales>` (for example `templates-designed-sf100`).
pub fn default_work(folder: &WorkloadFolder) -> Result<PathBuf, String> {
    let scales = folder.run_scales().map_err(|e| e.to_string())?.join("-");
    let name = match folder.settings.mode() {
        Mode::Templates => format!("templates-{}-{scales}", storage_word(folder.settings.storage())),
        Mode::Engine => format!("engine-{scales}"),
    };
    Ok(folder.root.join("runs").join(name))
}

fn storage_word(storage: Storage) -> &'static str {
    match storage {
        Storage::Designed => "designed",
        Storage::Plain => "plain",
    }
}

/// The record `WORK/run.json`: the folder, the settings that shape the requests, and the finished steps by key.
pub struct RunRecord {
    path: PathBuf,
    doc: Value,
}

impl RunRecord {
    /// The record of `work`, created for `folder` and `settings`; an existing one must name the same folder and settings.
    pub fn open(work: &Path, folder: &Path, settings: Value) -> Result<RunRecord, String> {
        let path = work.join(RUN_RECORD);
        if path.is_file() {
            let doc: Value = serde_json::from_str(&std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?).map_err(|e| format!("{}: {e}", path.display()))?;
            if doc["folder"] != json!(folder) || doc["settings"] != settings {
                return Err(format!("{} is the work folder of another workload or other settings (it records {} with {}): use a new --out", work.display(), doc["folder"], doc["settings"]));
            }
            return Ok(RunRecord { path, doc });
        }
        std::fs::create_dir_all(work).map_err(|e| format!("{}: {e}", work.display()))?;
        let record = RunRecord { path, doc: json!({"format": "gendb.run.v1", "folder": folder, "settings": settings, "steps": {}}) };
        record.save()?;
        Ok(record)
    }

    /// Whether step `key` finished.
    pub fn done(&self, key: &str) -> bool {
        self.doc["steps"][key]["exit"] == 0
    }

    /// Record step `key` as finished with `exit` and the file of its record.
    pub fn finish(&mut self, key: &str, exit: i32, record: Option<&Path>) -> Result<(), String> {
        let at = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_millis() as u64).unwrap_or(0);
        self.doc["steps"][key] = json!({"exit": exit, "record": record, "finished_unix_ms": at});
        self.save()
    }

    fn save(&self) -> Result<(), String> {
        let text = serde_json::to_string_pretty(&self.doc).map_err(|e| e.to_string())? + "\n";
        let partial = self.path.with_extension("json.partial");
        std::fs::write(&partial, text).map_err(|e| format!("{}: {e}", partial.display()))?;
        std::fs::rename(&partial, &self.path).map_err(|e| format!("{}: {e}", self.path.display()))
    }
}

/// One `[[members]]` folder of an engine run.
struct Member {
    name: String,
    role: MemberRole,
    start_from: Option<String>,
    folder: WorkloadFolder,
    scales: Vec<String>,
}

/// A run being driven: the folder, the machine, the work folder's record and this executable.
struct Run {
    folder: WorkloadFolder,
    scales: Vec<String>,
    members: Vec<Member>,
    ctx: RunContext,
    exe: PathBuf,
    record: RunRecord,
    /// Templates `start_from`: the earlier work folder whose sessions the queries continue.
    continuation: Option<Continuation>,
}

impl Run {
    /// Read the folder (and its members), translate every query, open the work folder.
    fn open(options: &RunOptions) -> Result<Run, String> {
        Run::open_with(options, effective_settings(&options.folder, options.config.as_deref(), options.flags.clone())?)
    }

    /// [`Run::open`] with the effective `settings` given.
    fn open_with(options: &RunOptions, mut settings: Settings) -> Result<Run, String> {
        let continuation = match (settings.mode(), settings.start()) {
            (Mode::Templates, Some(StartFrom::Folder(work))) => Some(Continuation::read(&work)?),
            (Mode::Templates, Some(StartFrom::Version { .. })) => return Err("start_from RUN:VERSION is for mode = \"engine\"; in templates mode it names an earlier work folder".into()),
            (Mode::Engine, Some(StartFrom::Version { run, version })) => {
                settings.start_from = Some(format!("{}:{version}", engine_run_dir(&run)?.display()));
                None
            }
            _ => None,
        };
        if let Some(continuation) = &continuation {
            if settings.goal() != Goal::Fast {
                return Err("start_from (templates) continues the earlier sessions as incumbents, which needs goal = \"fast\"".into());
            }
            settings.capture.get_or_insert_with(|| continuation.capture.clone());
        }
        let folder = WorkloadFolder::read(&options.folder, settings).map_err(|e| e.to_string())?;
        let scales = folder.run_scales().map_err(|e| e.to_string())?;
        let work = match &options.out {
            Some(out) => std::path::absolute(out).map_err(|e| format!("{}: {e}", out.display()))?,
            None => default_work(&folder)?,
        };
        let ctx = RunContext::from_environment(&work).map_err(|e| e.to_string())?;
        let members = read_members(&folder)?;
        let parser = SqlParser::from_environment().map_err(|e| format!("SQL frontend: {e}"))?;
        for (name, workload) in std::iter::once(("primary", &folder)).chain(members.iter().map(|m| (m.name.as_str(), &m.folder))) {
            workload.check_queries(&parser, &work.join("checks").join(name)).map_err(|e| e.to_string())?;
        }
        let settings_summary = json!({"mode": format!("{:?}", folder.settings.mode()).to_lowercase(), "storage": storage_word(folder.settings.storage()),
            "goal": format!("{:?}", folder.settings.goal()).to_lowercase(), "compare_with": format!("{:?}", folder.settings.compare_with()).to_lowercase(),
            "scales": scales, "threads": folder.settings.threads(), "queries": folder.queries.iter().map(|q| &q.name).collect::<Vec<_>>()});
        let record = RunRecord::open(&ctx.work, &folder.root, settings_summary)?;
        let exe = std::env::current_exe().map_err(|e| format!("this executable: {e}"))?;
        Ok(Run { folder, scales, members, ctx, exe, record, continuation })
    }

    /// Every step up to `until` (all of them without it); returns the summary.
    fn drive(&mut self, until: Option<Until>) -> Result<Value, String> {
        let next = match self.folder.settings.mode() {
            Mode::Templates => self.templates(until)?,
            Mode::Engine => self.engine(until)?,
        };
        Ok(json!({"work": self.ctx.work, "until": until.map(|u| format!("{u:?}").to_lowercase()), "steps": self.record.doc["steps"], "next": next}))
    }

    /// The steps of templates mode (module documentation); returns what to run next.
    fn templates(&mut self, until: Option<Until>) -> Result<Value, String> {
        let scale = self.scales[0].clone();
        self.step("data", |run| ensure_data(&run.folder, &scale).map(|()| None))?;
        if until == Some(Until::Data) {
            return Ok(json!("gendb run without --until data"));
        }
        let base = scale_inputs(&self.folder, &scale, None, None)?;
        requests::write_inputs(&self.folder, &self.ctx.paths(None), std::slice::from_ref(&base)).map_err(|e| e.to_string())?;
        let prepare = self.settle("prepare", &requests::templates_request(&self.folder, &self.ctx, &base).map_err(|e| e.to_string())?)?;
        self.finish_once("requests", &prepare)?;
        if until == Some(Until::Requests) {
            return Ok(json!(prepare));
        }
        let timed = if self.folder.settings.goal() == Goal::Fast { "all" } else { "none" };
        let (bindings, out) = (self.ctx.paths(None).bindings(&scale), self.ctx.work.join("baselines").join(&scale));
        let baselines = self.baselines(&self.folder.clone(), "baselines", &prepare, &bindings, &out, timed)?;
        // The capture is the given one, else the one the preparation step writes (its path is known before it runs).
        let plain = self.folder.settings.storage() == Storage::Plain;
        let given = self.folder.settings.capture.clone();
        let prepare_dir = self.ctx.work.join("steps/prepare");
        let capture = given.clone().unwrap_or_else(|| prepare_dir.join("data"));
        let full = ScaleInputs { capture: Some(capture.clone()), baselines, ..base };
        let mut final_request = requests::templates_request(&self.folder, &self.ctx, &full).map_err(|e| e.to_string())?;
        if let Some(continuation) = &self.continuation {
            continuation.apply(&mut final_request)?;
        }
        let run_request = self.settle("run", &final_request)?;
        let visible = self.folder.visible_bindings(&scale).map_err(|e| e.to_string())?;
        self.settle("serve", &requests::serve_request(final_request.clone(), &visible))?;
        if until == Some(Until::Baselines) {
            return Ok(json!(run_request));
        }
        if let Some(continuation) = &self.continuation {
            let (source, target) = (continuation.library.clone(), self.ctx.paths(None).library);
            self.step("seed", |run| run.gendb("seed", &[os("seed-engine-library"), source.into(), target.into(), os("--apply")]).map(Some))?;
        }
        if plain || given.is_none() {
            let route = if plain { "prepare-flat-storage" } else { "preflight" };
            self.step("prepare", |run| run.gendb("prepare", &[os(route), prepare.clone().into(), prepare_dir.clone().into()]).map(Some))?;
        }
        if !capture.is_dir() {
            return Err(format!("the preparation wrote no capture {} (its record: {})", capture.display(), self.log("prepare").display()));
        }
        if until == Some(Until::Prepare) {
            return Ok(json!(capture));
        }
        if until == Some(Until::Preflight) {
            let first = final_request.queries.first().and_then(|q| q.name.clone()).ok_or("the folder has no query")?;
            let (preflight_dir, render_dir) = (self.ctx.work.join("steps/preflight"), self.ctx.work.join("steps/render"));
            self.step("preflight", |run| run.gendb("preflight", &[os("preflight"), run_request.clone().into(), preflight_dir.into()]).map(Some))?;
            self.step("render", |run| run.gendb("render", &[os("render-query-inputs"), run_request.clone().into(), first.into(), render_dir.into()]).map(Some))?;
            return Ok(json!(format!("gendb run {} --out {} (synthesis: calls the author)", self.folder.root.display(), self.ctx.work.display())));
        }
        let synthesize_dir = self.ctx.work.join("steps/synthesize");
        self.step("synthesize", |run| run.gendb("synthesize", &[os("synthesize"), run_request.clone().into(), synthesize_dir.into()]).map(Some))?;
        Ok(json!(format!("gendb serve {} --out {}", self.folder.root.display(), self.ctx.work.display())))
    }

    /// The steps of engine mode (module documentation); returns what to run next.
    fn engine(&mut self, until: Option<Until>) -> Result<Value, String> {
        let scales = self.scales.clone();
        let workloads: Vec<(Option<String>, WorkloadFolder, Vec<String>)> = std::iter::once((None, self.folder.clone(), scales.clone()))
            .chain(self.members.iter().map(|m| (Some(m.name.clone()), m.folder.clone(), m.scales.clone())))
            .collect();
        self.step("data", |_| {
            for (_, folder, scales) in &workloads {
                for scale in scales {
                    ensure_data(folder, scale)?;
                }
            }
            Ok(None)
        })?;
        if until == Some(Until::Data) {
            return Ok(json!("gendb run without --until data"));
        }
        // Per workload: its flat preparation requests, one per scale.
        let mut flat_requests: BTreeMap<(Option<String>, String), PathBuf> = BTreeMap::new();
        for (member, folder, scales) in &workloads {
            let paths = self.ctx.paths(member.as_deref());
            let bases = scales.iter().map(|s| scale_inputs(folder, s, None, None)).collect::<Result<Vec<_>, _>>()?;
            requests::write_inputs(folder, &paths, &bases).map_err(|e| e.to_string())?;
            for base in &bases {
                let name = match member {
                    None => format!("flat-{}", base.name),
                    Some(m) => format!("members/{m}-flat-{}", base.name),
                };
                let request = requests::flat_preparation_request(folder, &self.ctx, base, &paths.library).map_err(|e| e.to_string())?;
                flat_requests.insert((member.clone(), base.name.clone()), self.settle(&name, &request)?);
            }
        }
        let first_flat = flat_requests[&(None, scales[0].clone())].clone();
        self.finish_once("requests", &first_flat)?;
        if until == Some(Until::Requests) {
            return Ok(json!(first_flat));
        }
        // Baselines per workload and scale (a check member's answers only), over the source data.
        let mut baselines: BTreeMap<(Option<String>, String), Option<Baselines>> = BTreeMap::new();
        for (member, folder, scales) in &workloads {
            let role = member.as_ref().map(|m| self.members.iter().find(|x| x.name == *m).expect("a member").role);
            let timed = match role {
                Some(MemberRole::Check) => "none".to_string(),
                _ => folder.settings.timing_binding(),
            };
            for scale in scales {
                let key = step_key(member.as_deref(), "baselines", scale);
                let out = match member {
                    None => self.ctx.work.join("baselines").join(scale),
                    Some(m) => self.ctx.work.join("members").join(m).join("baselines").join(scale),
                };
                let request = flat_requests[&(member.clone(), scale.clone())].clone();
                let bindings = self.ctx.paths(member.as_deref()).bindings(scale);
                baselines.insert((member.clone(), scale.clone()), self.baselines(folder, &key, &request, &bindings, &out, &timed)?);
            }
        }
        if until == Some(Until::Baselines) {
            return Ok(json!(self.ctx.work.join("baselines")));
        }
        for ((member, scale), request) in &flat_requests {
            let key = step_key(member.as_deref(), "prepare", scale);
            let dir = self.ctx.work.join("steps").join(&key);
            self.step(&key, |run| run.gendb(&key, &[os("prepare-flat-storage"), request.clone().into(), dir.into()]).map(Some))?;
        }
        // The workloads' requests over the captures and flat storages: members first, the primary names them.
        let mut entries = vec![];
        for (member, folder, scales) in workloads.iter().rev() {
            let mut inputs = vec![];
            for scale in scales {
                let capture = self.ctx.work.join("steps").join(step_key(member.as_deref(), "prepare", scale)).join("data");
                let saved = baselines.remove(&(member.clone(), scale.clone())).flatten();
                inputs.push(scale_inputs(folder, scale, Some(capture), saved)?);
            }
            let flat_record = self.ctx.work.join("steps").join(step_key(member.as_deref(), "prepare", &scales[0])).join("flat-storage.json");
            let flat = FlatStorages::read(&flat_record).map_err(|e| e.to_string())?;
            match member {
                Some(name) => {
                    let request = requests::engine_request(folder, &self.ctx, &inputs, &flat, Some(name), vec![]).map_err(|e| e.to_string())?;
                    self.settle(&format!("members/{name}"), &request)?;
                    let m = self.members.iter().find(|x| x.name == *name).expect("a member");
                    entries.insert(0, requests::member_entry(&self.ctx, name, m.role, m.start_from.as_deref()));
                }
                None => {
                    let request = requests::engine_request(folder, &self.ctx, &inputs, &flat, None, std::mem::take(&mut entries)).map_err(|e| e.to_string())?;
                    self.settle("engine", &request)?;
                }
            }
        }
        let engine_request = self.ctx.request_file("engine");
        if until == Some(Until::Prepare) {
            return Ok(json!(engine_request));
        }
        if let Some(StartFrom::Version { run, .. }) = self.folder.settings.start() {
            let source = engine_run_library(&run)?;
            let target = self.ctx.paths(None).library;
            self.step("seed", |r| r.gendb("seed", &[os("seed-engine-library"), source.into(), target.into(), os("--apply")]).map(Some))?;
        }
        self.step("check", |run| run.gendb("check", &[os("engine"), os("check-request"), engine_request.clone().into()]).map(Some))?;
        if until == Some(Until::Preflight) {
            let dir = self.ctx.work.join("steps/engine-inputs");
            self.step("preflight", |run| run.gendb("preflight", &[os("engine"), os("render-inputs"), engine_request.clone().into(), dir.into()]).map(Some))?;
            return Ok(json!(format!("gendb run {} --out {} (synthesis: calls the engine agents)", self.folder.root.display(), self.ctx.work.display())));
        }
        let dir = self.ctx.work.join("steps/engine");
        self.step("engine-prepare", |run| run.gendb("engine-prepare", &[os("engine"), os("prepare"), engine_request.clone().into(), dir.clone().into()]).map(Some))?;
        self.step("synthesize", |run| run.gendb("synthesize", &[os("engine"), os("synthesize"), engine_request.clone().into(), dir.clone().into()]).map(Some))?;
        Ok(json!(format!("gendb serve-engine {} --out {}", self.folder.root.display(), self.ctx.work.display())))
    }

    /// `gendb import FOLDER PUBLISHED_RUN` (module documentation of `folder_commands`): steps `data`, `requests` (the
    /// import request `requests/import.json`: correctness, the first binding of each template as its one test binding, no
    /// saved answers), `prepare` (plain storage only: `gendb prepare-flat-storage`, which the import reads), `import`;
    /// then `requests/run.json` (the import request over the import's capture) and `serve.json` for serve and evaluate.
    fn import(&mut self, published: &Path) -> Result<Value, String> {
        let scale = self.scales[0].clone();
        self.step("data", |run| ensure_data(&run.folder, &scale).map(|()| None))?;
        let base = scale_inputs(&self.folder, &scale, None, None)?;
        requests::write_inputs(&self.folder, &self.ctx.paths(None), std::slice::from_ref(&base)).map_err(|e| e.to_string())?;
        let mut request = requests::templates_request(&self.folder, &self.ctx, &base).map_err(|e| e.to_string())?;
        request.workload_storage = None;
        request.data_allowance = None;
        for query in &mut request.queries {
            query.test_bindings.truncate(1);
        }
        let import_request = self.settle("import", &request)?;
        self.finish_once("requests", &import_request)?;
        if self.folder.settings.storage() == Storage::Plain {
            let dir = self.ctx.work.join("steps/flat");
            self.step("prepare", |run| run.gendb("prepare", &[os("prepare-flat-storage"), import_request.clone().into(), dir.into()]).map(Some))?;
        }
        let import_dir = self.ctx.work.join("steps/import");
        let source = std::path::absolute(published).map_err(|e| format!("{}: {e}", published.display()))?;
        self.step("import", |run| run.gendb("import", &[os("import"), import_request.clone().into(), source.into(), import_dir.clone().into()]).map(Some))?;
        request.prepared_workload = Some(import_dir.join("data"));
        self.settle("run", &request)?;
        let visible = self.folder.visible_bindings(&scale).map_err(|e| e.to_string())?;
        self.settle("serve", &requests::serve_request(request, &visible))?;
        let summary = self.log("import");
        Ok(json!({"work": self.ctx.work, "steps": self.record.doc["steps"], "import": summary,
            "next": format!("gendb serve {} --out {}", self.folder.root.display(), self.ctx.work.display())}))
    }

    /// The baselines of `folder` at one scale: the saved folder of the `baselines` setting (its `<scale>/` when it has
    /// one; the scale is `out`'s name), else the DuckDB helper's over `request`'s data at `bindings` (`compare_with =
    /// "duckdb"`, step `key`, into `out`, `timed` as its `--timed`), else none.
    fn baselines(&mut self, folder: &WorkloadFolder, key: &str, request: &Path, bindings: &Path, out: &Path, timed: &str) -> Result<Option<Baselines>, String> {
        if let Some(saved) = &folder.settings.baselines {
            let per_scale = saved.join(out.file_name().unwrap_or_default());
            return Baselines::read(if per_scale.is_dir() { &per_scale } else { saved }).map(Some).map_err(|e| e.to_string());
        }
        if folder.settings.compare_with() == CompareWith::None {
            return Ok(None);
        }
        self.step(key, |run| {
            let python = SqlParser::from_environment().map_err(|e| format!("SQL frontend: {e}"))?.python().to_path_buf();
            let arguments = [OsString::from(DUCKDB_HELPER), request.into(), bindings.into(), out.into(), os("--timed"), os(timed)];
            run.child(key, &python, &arguments).map(Some)
        })?;
        Baselines::read(out).map(Some).map_err(|e| e.to_string())
    }

    /// Run `step` unless the record lists `key` as finished; record it when it succeeds.
    fn step(&mut self, key: &str, step: impl FnOnce(&mut Run) -> Result<Option<PathBuf>, String>) -> Result<(), String> {
        if self.record.done(key) {
            eprintln!("gendb run: {key}: done earlier");
            return Ok(());
        }
        eprintln!("gendb run: {key}");
        let record = step(self)?;
        self.record.finish(key, 0, record.as_deref())
    }

    /// Record `key` once with `record` (a step that is redone, unchanged, on every invocation).
    fn finish_once(&mut self, key: &str, record: &Path) -> Result<(), String> {
        if self.record.done(key) { Ok(()) } else { self.record.finish(key, 0, Some(record)) }
    }

    /// Write `requests/<name>.json`, or check that the existing one is the same request.
    fn settle(&self, name: &str, request: &WorkloadRequest) -> Result<PathBuf, String> {
        settle_request(&self.ctx.request_file(name), request)
    }

    /// `WORK/logs/<key>.json`: the record a step's command printed.
    fn log(&self, key: &str) -> PathBuf {
        self.ctx.work.join("logs").join(format!("{}.json", key.replace('/', "-")))
    }

    /// `gendb ARGUMENTS` (this executable) as step `key`; returns the file of the record it printed.
    fn gendb(&self, key: &str, arguments: &[OsString]) -> Result<PathBuf, String> {
        self.child(key, &self.exe, arguments)
    }

    /// Run `program ARGUMENTS` with its standard output in `WORK/logs/<key>.json` (its error stream is this one's);
    /// refused unless it exits 0.
    fn child(&self, key: &str, program: &Path, arguments: &[OsString]) -> Result<PathBuf, String> {
        let log = self.log(key);
        std::fs::create_dir_all(log.parent().expect("logs/")).map_err(|e| format!("{}: {e}", log.display()))?;
        let stdout = std::fs::File::create(&log).map_err(|e| format!("{}: {e}", log.display()))?;
        let status = Command::new(program).args(arguments).stdin(Stdio::null()).stdout(stdout).status().map_err(|e| format!("{key}: {}: {e}", program.display()))?;
        match status.code() {
            Some(0) => Ok(log),
            code => Err(format!("{key}: {} {} exited with {} (its record: {})", program.display(), arguments.iter().map(|a| a.to_string_lossy()).collect::<Vec<_>>().join(" "), code.map_or("a signal".to_string(), |c| c.to_string()), log.display())),
        }
    }
}

/// `gendb import FOLDER PUBLISHED_RUN` through the step driver: templates mode, `goal = "correct"`, `compare_with =
/// "none"`, the storage kind of the published run ([`published_storage`]); default work folder
/// `FOLDER/runs/import-<published folder name>`.
pub fn import(options: &RunOptions, published: &Path) -> Result<Value, String> {
    let run = PublishedRun::read(published)?;
    let mut settings = effective_settings(&options.folder, options.config.as_deref(), options.flags.clone())?;
    settings.mode = Some(Mode::Templates);
    settings.goal = Some(Goal::Correct);
    settings.compare_with = Some(CompareWith::None);
    settings.start_from = None;
    let tables: Vec<String> = WorkloadFolder::read(&options.folder, settings.clone()).map_err(|e| e.to_string())?.schema.tables.into_iter().map(|t| t.name).collect();
    settings.storage = Some(published_storage(&run, &tables));
    let name = run.root.file_name().map(|n| n.to_string_lossy().to_string()).unwrap_or_default();
    let out = options.out.clone().unwrap_or_else(|| options.folder.join("runs").join(format!("import-{name}")));
    let options = RunOptions { folder: options.folder.clone(), config: options.config.clone(), flags: options.flags.clone(), out: Some(out), until: None };
    Run::open_with(&options, settings)?.import(&run.root)
}

/// The storage kind of a published run: plain when every storage it publishes is GenDB's flat storage of a table
/// (`flat_<table>`; a one-query folder of a plain run publishes none), else designed. Admission checks the choice again:
/// under `fixed_flat` a query reading any other storage is refused by name.
pub fn published_storage(run: &PublishedRun, tables: &[String]) -> Storage {
    let flat = |name: &str| name.strip_prefix("flat_").is_some_and(|table| tables.iter().any(|t| t == table));
    if run.storages.iter().all(|s| flat(&s.name)) { Storage::Plain } else { Storage::Designed }
}

/// The step key of a workload's step at one scale: `prepare/sf1`, `members/NAME/prepare/sf1`.
fn step_key(member: Option<&str>, step: &str, scale: &str) -> String {
    match member {
        None => format!("{step}/{scale}"),
        Some(name) => format!("members/{name}/{step}/{scale}"),
    }
}

fn os(word: &str) -> OsString {
    OsString::from(word)
}

/// Write `request` to `path`, or check that the file there is this request (else refused: use a new work folder).
pub fn settle_request(path: &Path, request: &WorkloadRequest) -> Result<PathBuf, String> {
    let text = serde_json::to_string_pretty(request).map_err(|e| e.to_string())? + "\n";
    match std::fs::read_to_string(path) {
        Ok(existing) if existing == text => Ok(path.to_path_buf()),
        Ok(_) => Err(format!("{} differs from the request the folder now gives (the folder, its data or the settings changed): use a new --out", path.display())),
        Err(_) => {
            write_request(path, request).map_err(|e| e.to_string())?;
            Ok(path.to_path_buf())
        }
    }
}

/// `data/<scale>/` of `folder`, written by `setup_data.sh SCALE` when missing, with every file's footer checked.
pub fn ensure_data(folder: &WorkloadFolder, scale: &str) -> Result<(), String> {
    let dir = folder.data_dir(scale);
    if !dir.is_dir() {
        let script = folder.setup_script().ok_or_else(|| format!("data_missing: {} does not exist; write the data there (or add setup_data.sh SCALE)", dir.display()))?;
        eprintln!("gendb run: {} is missing: bash {} {scale}", dir.display(), script.display());
        let status = Command::new("bash").arg(&script).arg(scale).current_dir(&folder.root).stdin(Stdio::null()).status().map_err(|e| format!("{}: {e}", script.display()))?;
        if !status.success() || !dir.is_dir() {
            return Err(format!("{} {scale} exited with {status} and did not write {}", script.display(), dir.display()));
        }
    }
    folder.check_data(scale).map_err(|e| e.to_string())
}

/// What the request writer needs of one scale: its files and data size, with the capture and baselines when known.
fn scale_inputs(folder: &WorkloadFolder, scale: &str, capture: Option<PathBuf>, baselines: Option<Baselines>) -> Result<ScaleInputs, String> {
    let locations = folder.locations(scale).map_err(|e| e.to_string())?;
    let data_size = folder.data_size(scale).map_err(|e| e.to_string())?;
    Ok(ScaleInputs { name: scale.to_string(), locations, capture, data_size, baselines })
}

/// The `[[members]]` folders of an engine run, each read with the fields every workload of one engine shares taken
/// from the primary (and its budget, which a member's request needs but does not use).
fn read_members(primary: &WorkloadFolder) -> Result<Vec<Member>, String> {
    let mut members = vec![];
    for entry in primary.settings.members.iter().flatten() {
        let mut settings = Settings::read(&entry.folder, None).map_err(|e| e.to_string())?.with_shared_from(&primary.settings);
        settings.mode = Some(Mode::Engine);
        settings.budget_usd = primary.settings.budget_usd.clone();
        let folder = WorkloadFolder::read(&entry.folder, settings).map_err(|e| e.to_string())?;
        let scales = folder.run_scales().map_err(|e| e.to_string())?;
        let name = folder.settings.name_or(&folder.root);
        members.push(Member { name, role: entry.role, start_from: entry.start_from.clone(), folder, scales });
    }
    Ok(members)
}

/// The engine run directory `RUN` of `start_from = "RUN:VERSION"`: a controller run directory (it holds
/// `request.json`), or a `gendb run` work folder (its `steps/engine`).
fn engine_run_dir(run: &Path) -> Result<PathBuf, String> {
    [run.to_path_buf(), run.join("steps/engine")]
        .into_iter()
        .find(|dir| dir.join("request.json").is_file())
        .ok_or_else(|| format!("start_from {}: not an engine run directory (no request.json there or in steps/engine)", run.display()))
}

/// The library of the engine run `run` (its recorded request's `library`).
fn engine_run_library(run: &Path) -> Result<PathBuf, String> {
    let request = engine_run_dir(run)?.join("request.json");
    let doc: Value = serde_json::from_str(&std::fs::read_to_string(&request).map_err(|e| format!("{}: {e}", request.display()))?).map_err(|e| format!("{}: {e}", request.display()))?;
    doc["library"].as_str().map(PathBuf::from).ok_or_else(|| format!("{}: no library", request.display()))
}

/// Templates `start_from`: an earlier work folder of `gendb run` whose query sessions this run's queries continue
/// (`queries[].continue_from`), over its capture and the storages of its library (seeded into this run's).
struct Continuation {
    library: PathBuf,
    capture: PathBuf,
    /// Query name -> its closed session `steps/synthesize/queries/query-NNNN`.
    sessions: BTreeMap<String, PathBuf>,
}

impl Continuation {
    fn read(work: &Path) -> Result<Continuation, String> {
        let path = work.join("requests/run.json");
        let text = std::fs::read_to_string(&path).map_err(|e| format!("start_from {}: {e} (the work folder of an earlier gendb run)", work.display()))?;
        let request: WorkloadRequest = serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
        let capture = request.prepared_workload.clone().ok_or_else(|| format!("{}: no prepared_workload", path.display()))?;
        let sessions = request
            .queries
            .iter()
            .enumerate()
            .filter_map(|(index, q)| Some((q.name.clone()?, work.join("steps/synthesize/queries").join(format!("query-{index:04}")))))
            .collect();
        Ok(Continuation { library: request.library, capture, sessions })
    }

    /// Each query continues its earlier session; the storages are the earlier run's, so no storage session runs.
    fn apply(&self, request: &mut WorkloadRequest) -> Result<(), String> {
        request.workload_storage = None;
        for query in &mut request.queries {
            let name = query.name.clone().unwrap_or_default();
            let session = self.sessions.get(&name).filter(|s| s.is_dir()).ok_or_else(|| format!("start_from: the earlier run has no session of query {name}"))?;
            query.continue_from = Some(session.clone());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn run_options_parse_flags_and_refuse_unknown_words() {
        let options = RunOptions::parse(&["w/tpc-h", "--scale", "sf1", "--threads", "1,32", "--queries", "Q01,Q06", "--storage", "plain", "--until", "preflight", "--out", "o"]).unwrap();
        assert_eq!(options.folder, Path::new("w/tpc-h"));
        assert_eq!((options.flags.scale.as_deref(), options.flags.threads.as_deref()), (Some("sf1"), Some([1, 32].as_slice())));
        assert_eq!(options.flags.queries, Some(vec!["Q01".to_string(), "Q06".to_string()]));
        assert_eq!((options.flags.storage, options.until, options.out.as_deref()), (Some(Storage::Plain), Some(Until::Preflight), Some(Path::new("o"))));
        assert_eq!(RunOptions::parse(&["f", "--mode", "engine"]).unwrap().flags.mode, Some(Mode::Engine));
        assert!(RunOptions::parse(&["f", "--mode", "fast"]).unwrap_err().contains("--mode fast"));
        assert!(RunOptions::parse(&["f", "--until", "synthesize"]).unwrap_err().contains("--until synthesize"));
        assert!(RunOptions::parse(&["f", "--bogus"]).unwrap_err().contains("unknown option"));
        assert!(RunOptions::parse(&["f", "g"]).unwrap_err().contains("unexpected argument g"));
        assert!(RunOptions::parse(&["--scale"]).unwrap_err().contains("needs a value"));
        assert_eq!(RunOptions::parse(&[]).unwrap_err(), "FOLDER is required");
    }

    /// A finished step is skipped on the next invocation; a work folder of other settings is refused; a request file
    /// that would change is refused.
    #[test]
    fn steps_are_recorded_and_skipped_and_a_changed_work_folder_is_refused() {
        let work = std::env::temp_dir().join(format!("gendb-run-record-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&work);
        let settings = json!({"mode": "templates", "scales": ["tiny"]});
        let mut record = RunRecord::open(&work, Path::new("/f"), settings.clone()).unwrap();
        assert!(!record.done("data"));
        record.finish("data", 0, None).unwrap();
        record.finish("prepare", 0, Some(Path::new("/w/logs/prepare.json"))).unwrap();
        let reopened = RunRecord::open(&work, Path::new("/f"), settings.clone()).unwrap();
        assert!(reopened.done("data") && reopened.done("prepare") && !reopened.done("baselines"));
        assert_eq!(reopened.doc["steps"]["prepare"]["record"], "/w/logs/prepare.json");
        assert!(RunRecord::open(&work, Path::new("/f"), json!({"mode": "engine"})).err().unwrap().contains("use a new --out"));
        assert!(RunRecord::open(&work, Path::new("/other"), settings).err().unwrap().contains("use a new --out"));
        let request: WorkloadRequest = serde_json::from_value(json!({"format_version":2,"dataset":{"tables":[]},"queries":[],"hardware":{"threads":[1]},
            "max_concurrent_queries":1,"author_executable":"claude","library":"/l","barriers":{"activity_lock":"/a","build_lock":"/b","race_lock":"/r"}})).unwrap();
        let path = work.join("requests/run.json");
        settle_request(&path, &request).unwrap();
        settle_request(&path, &request).unwrap();
        let changed = WorkloadRequest { max_concurrent_queries: 2, ..request };
        assert!(settle_request(&path, &changed).unwrap_err().contains("use a new --out"));
        std::fs::remove_dir_all(&work).unwrap();
    }

    #[test]
    fn step_keys_name_the_workload_and_scale() {
        assert_eq!(step_key(None, "prepare", "sf1"), "prepare/sf1");
        assert_eq!(step_key(Some("anyschema"), "baselines", "tiny"), "members/anyschema/baselines/tiny");
        assert!(Until::Requests < Until::Baselines && Until::Baselines < Until::Prepare && Until::Prepare < Until::Preflight);
    }
}
