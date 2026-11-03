//! The folder forms of `gendb serve|evaluate|import|serve-engine`: the first argument is a workload folder (a directory
//! holding `schema.sql`), and the command works on that folder's work folder (`--out WORK`, default the one `gendb run`
//! uses with the same settings, `super::default_work`).
//!
//! - `gendb serve FOLDER [--out WORK] [--config FILE] [--query Q [--args A,B | --binding ID]]`: the admitted packages
//!   of `WORK/requests/run.json` served at the folder's bindings (default: every query at every binding), into a new
//!   `WORK/steps/serve-N` (its request `WORK/requests/serve-N.json`);
//! - `gendb evaluate FOLDER [--out WORK] [--config FILE] [--bindings FILE]`: `gendb evaluate` of `WORK/requests/run.json`
//!   at the folder's bindings (or FILE), results in the output home `WORK/output`;
//! - `gendb import FOLDER PUBLISHED_RUN [--out WORK] [--config FILE]`: the published packages admitted over the folder's
//!   data without an author (`super::Run::import`; default WORK `FOLDER/runs/import-<published folder name>`), after
//!   which `serve` and `evaluate` work on that WORK;
//! - `gendb serve-engine FOLDER [--out WORK] [--config FILE]`: every query at every binding of the engine run's last
//!   scale, from `WORK/requests/engine.json`'s library, into a new `WORK/steps/serve-engine-N`.

use super::{RunOptions, default_work, effective_settings};
use gendb_synthesis::controller::request::WorkloadRequest;
use gendb_synthesis::workload_folder::requests::serve_request;
use gendb_synthesis::workload_folder::settings::Settings;
use gendb_synthesis::workload_folder::{WorkloadFolder, write_request};
use serde_json::{Value, json};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// A command with a folder form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FolderCommand {
    Serve,
    Evaluate,
    Import,
    ServeEngine,
}

impl FolderCommand {
    /// The folder form of `word` when its first argument is a workload folder; `None` keeps the request form.
    pub fn parse(word: &str, arguments: &[OsString]) -> Option<FolderCommand> {
        let command = match word {
            "serve" => FolderCommand::Serve,
            "evaluate" => FolderCommand::Evaluate,
            "import" => FolderCommand::Import,
            "serve-engine" => FolderCommand::ServeEngine,
            _ => return None,
        };
        arguments.first().filter(|first| WorkloadFolder::is_folder(Path::new(first))).map(|_| command)
    }

    fn name(self) -> &'static str {
        match self {
            FolderCommand::Serve => "serve",
            FolderCommand::Evaluate => "evaluate",
            FolderCommand::Import => "import",
            FolderCommand::ServeEngine => "serve-engine",
        }
    }

    fn usage(self) -> &'static str {
        match self {
            FolderCommand::Serve => "usage: gendb serve FOLDER [--out WORK] [--config FILE] [--query Q [--args A,B | --binding ID]]",
            FolderCommand::Evaluate => "usage: gendb evaluate FOLDER [--out WORK] [--config FILE] [--bindings FILE]",
            FolderCommand::Import => "usage: gendb import FOLDER PUBLISHED_RUN [--out WORK] [--config FILE]",
            FolderCommand::ServeEngine => "usage: gendb serve-engine FOLDER [--out WORK] [--config FILE]",
        }
    }
}

/// The parsed words of a folder command.
#[derive(Debug, Default, PartialEq)]
pub struct FolderOptions {
    pub folder: PathBuf,
    /// `import`: the published run folder.
    pub published: Option<PathBuf>,
    pub out: Option<PathBuf>,
    pub config: Option<PathBuf>,
    pub query: Option<String>,
    pub args: Option<Vec<String>>,
    pub binding: Option<String>,
    pub bindings: Option<PathBuf>,
}

impl FolderOptions {
    pub fn parse(command: FolderCommand, words: &[&str]) -> Result<FolderOptions, String> {
        let mut options = FolderOptions::default();
        let mut positional = vec![];
        let mut words = words.iter();
        while let Some(&word) = words.next() {
            let mut value = || words.next().copied().ok_or_else(|| format!("{word} needs a value"));
            match (word, command) {
                ("--out", _) => options.out = Some(PathBuf::from(value()?)),
                ("--config", _) => options.config = Some(PathBuf::from(value()?)),
                ("--query", FolderCommand::Serve) => options.query = Some(value()?.to_string()),
                ("--args", FolderCommand::Serve) => options.args = Some(value()?.split(',').map(str::to_string).collect()),
                ("--binding", FolderCommand::Serve) => options.binding = Some(value()?.to_string()),
                ("--bindings", FolderCommand::Evaluate) => options.bindings = Some(PathBuf::from(value()?)),
                (flag, _) if flag.starts_with("--") => return Err(format!("unknown option {flag}")),
                (path, _) => positional.push(PathBuf::from(path)),
            }
        }
        let expected = if command == FolderCommand::Import { 2 } else { 1 };
        if positional.len() != expected {
            return Err(format!("{} positional arguments, {expected} expected", positional.len()));
        }
        options.published = (command == FolderCommand::Import).then(|| positional[1].clone());
        options.folder = positional.swap_remove(0);
        if (options.args.is_some() || options.binding.is_some()) && options.query.is_none() || options.args.is_some() && options.binding.is_some() {
            return Err("--args or --binding (not both) go with --query".into());
        }
        Ok(options)
    }
}

/// Entry of a folder command (the words after the command). Prints its record; exit 0 when it returned one, 1 when it
/// stopped with an error (on stderr), 2 for a usage error.
pub fn folder_command(command: FolderCommand, arguments: &[OsString]) -> ExitCode {
    let words: Option<Vec<&str>> = arguments.iter().map(|w| w.to_str()).collect();
    let parsed = words.ok_or_else(|| "arguments must be UTF-8".to_string()).and_then(|words| FolderOptions::parse(command, &words));
    let options = match parsed {
        Ok(options) => options,
        Err(error) => {
            eprintln!("gendb {}: {error}\n{}", command.name(), command.usage());
            return ExitCode::from(2);
        }
    };
    let result = match command {
        FolderCommand::Import => import(&options),
        _ => work_of(&options).and_then(|(folder, work)| match command {
            FolderCommand::Serve => serve(&folder, &work, &options),
            FolderCommand::Evaluate => evaluate(&work, options.bindings.as_deref()),
            _ => serve_engine(&folder, &work),
        }),
    };
    match result {
        Ok(record) => {
            println!("{}", serde_json::to_string_pretty(&record).expect("JSON values serialize"));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb {}: {error}", command.name());
            ExitCode::from(1)
        }
    }
}

/// The folder (read with its settings and `--config`) and its work folder.
fn work_of(options: &FolderOptions) -> Result<(WorkloadFolder, PathBuf), String> {
    let settings = effective_settings(&options.folder, options.config.as_deref(), Settings::default())?;
    let folder = WorkloadFolder::read(&options.folder, settings).map_err(|e| e.to_string())?;
    let work = match &options.out {
        Some(out) => std::path::absolute(out).map_err(|e| format!("{}: {e}", out.display()))?,
        None => default_work(&folder)?,
    };
    Ok((folder, work))
}

/// A request file of the work folder, read; missing means the run has not written it yet.
fn work_request(work: &Path, name: &str) -> Result<WorkloadRequest, String> {
    let path = work.join("requests").join(format!("{name}.json"));
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e} (run gendb run FOLDER first, with the same --out)", path.display()))?;
    serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))
}

/// The scale of a templates run (the one in its `run.json`).
fn run_scale(work: &Path) -> Result<String, String> {
    let path = work.join(super::RUN_RECORD);
    let doc: Value = serde_json::from_str(&std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?).map_err(|e| format!("{}: {e}", path.display()))?;
    doc["settings"]["scales"].as_array().and_then(|s| s.last()).and_then(Value::as_str).map(str::to_string).ok_or_else(|| format!("{}: no scales", path.display()))
}

/// `dir/<stem>-N` for the first N from 1 that does not exist.
fn next_free(dir: &Path, stem: &str) -> PathBuf {
    (1..).map(|n| dir.join(format!("{stem}-{n}"))).find(|p| !p.exists()).expect("a free name")
}

fn serve(folder: &WorkloadFolder, work: &Path, options: &FolderOptions) -> Result<Value, String> {
    let request = work_request(work, "run")?;
    let visible = folder.visible_bindings(&run_scale(work)?).map_err(|e| e.to_string())?;
    let mut serving = serve_request(request, &visible);
    if let Some(name) = &options.query {
        serving.queries.retain(|q| q.name.as_deref() == Some(name.as_str()));
        let query = serving.queries.first_mut().ok_or_else(|| format!("the run has no query {name}"))?;
        if let Some(args) = &options.args {
            query.arguments = vec![args.clone()];
        }
        if let Some(id) = &options.binding {
            let listed = visible["queries"][name.as_str()].as_array().into_iter().flatten().find(|b| b["binding_id"] == id.as_str());
            let arguments = listed.ok_or_else(|| format!("{name} has no binding {id} in the folder's bindings"))?["arguments"].clone();
            query.arguments = vec![serde_json::from_value(arguments).map_err(|e| e.to_string())?];
        }
    }
    let run_dir = next_free(&work.join("steps"), "serve");
    let request_file = work.join("requests").join(format!("{}.json", run_dir.file_name().expect("a name").to_string_lossy()));
    write_request(&request_file, &serving).map_err(|e| e.to_string())?;
    let exe = std::env::current_exe().map_err(|e| format!("this executable: {e}"))?;
    gendb_synthesis::controller::workload_run::serve(&request_file, &run_dir, &exe).map_err(|e| e.to_string())
}

fn evaluate(work: &Path, bindings: Option<&Path>) -> Result<Value, String> {
    work_request(work, "run")?;
    let request_file = work.join("requests/run.json");
    let bindings = match bindings {
        Some(file) => file.to_path_buf(),
        None => {
            let file = work.join("inputs").join(format!("bindings-{}.json", run_scale(work)?));
            if !file.is_file() {
                return Err(format!("{}: no bindings file (give --bindings FILE)", file.display()));
            }
            file
        }
    };
    let exe = std::env::current_exe().map_err(|e| format!("this executable: {e}"))?;
    gendb_synthesis::output::evaluation::evaluate(&request_file, &bindings, &work.join("output"), &exe).map_err(|e| e.to_string())
}

/// Every query at every binding of the engine run's last scale, served from its library by its selected version.
fn serve_engine(folder: &WorkloadFolder, work: &Path) -> Result<Value, String> {
    let request = work_request(work, "engine")?;
    let engine = request.engine.as_ref().ok_or("requests/engine.json has no engine section")?;
    let scale = engine.scales.last().ok_or("requests/engine.json has no scale")?;
    let visible = folder.visible_bindings(&scale.name).map_err(|e| e.to_string())?;
    let mut statements = vec![];
    for query in &folder.queries {
        for binding in visible["queries"][query.name.as_str()].as_array().into_iter().flatten() {
            statements.push(json!({"sql": query.sql, "parameters": query.parameters, "arguments": binding["arguments"]}));
        }
    }
    let serving = json!({"library": request.library, "dataset": folder.schema.dataset(&scale.locations), "prepared_workload": scale.prepared_workload,
        "storage_policy": request.storage_policy, "workers": request.hardware.threads, "statements": statements});
    let out = next_free(&work.join("steps"), "serve-engine");
    let request_file = work.join("requests").join(format!("{}.json", out.file_name().expect("a name").to_string_lossy()));
    std::fs::create_dir_all(request_file.parent().expect("requests/")).map_err(|e| e.to_string())?;
    std::fs::write(&request_file, serde_json::to_string_pretty(&serving).map_err(|e| e.to_string())? + "\n").map_err(|e| format!("{}: {e}", request_file.display()))?;
    let exe = std::env::current_exe().map_err(|e| format!("this executable: {e}"))?;
    gendb_synthesis::engine::serving::serve_engine_request(&request_file, &out, &exe)
}

/// `gendb import FOLDER PUBLISHED_RUN`: through `gendb run`'s step driver ([`super::Run::import`]).
fn import(options: &FolderOptions) -> Result<Value, String> {
    let published = options.published.clone().expect("import names a published run");
    let run = RunOptions { folder: options.folder.clone(), config: options.config.clone(), flags: Settings::default(), out: options.out.clone(), until: None };
    super::import(&run, &published)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn folder_options_parse_per_command() {
        let serve = FolderOptions::parse(FolderCommand::Serve, &["w/rc", "--query", "readings-count", "--args", "4", "--out", "o"]).unwrap();
        assert_eq!((serve.folder.as_path(), serve.query.as_deref(), serve.args.as_deref()), (Path::new("w/rc"), Some("readings-count"), Some(["4".to_string()].as_slice())));
        assert!(FolderOptions::parse(FolderCommand::Serve, &["w/rc", "--args", "4"]).unwrap_err().contains("go with --query"));
        assert!(FolderOptions::parse(FolderCommand::Serve, &["w/rc", "--query", "q", "--args", "4", "--binding", "v0"]).unwrap_err().contains("not both"));
        let import = FolderOptions::parse(FolderCommand::Import, &["w/rc", "results/example"]).unwrap();
        assert_eq!(import.published.as_deref(), Some(Path::new("results/example")));
        assert!(FolderOptions::parse(FolderCommand::Import, &["w/rc"]).unwrap_err().contains("2 expected"));
        assert!(FolderOptions::parse(FolderCommand::Evaluate, &["w/rc", "--query", "q"]).unwrap_err().contains("unknown option"));
        assert_eq!(FolderOptions::parse(FolderCommand::Evaluate, &["w/rc", "--bindings", "b.json"]).unwrap().bindings.as_deref(), Some(Path::new("b.json")));
    }

    /// Only a directory holding `schema.sql` takes the folder form; a request file keeps the request form.
    #[test]
    fn the_folder_form_needs_a_workload_folder() {
        let dir = std::env::temp_dir().join(format!("gendb-folder-form-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        assert_eq!(FolderCommand::parse("serve", &[dir.clone().into()]), None);
        std::fs::write(dir.join("schema.sql"), "CREATE TABLE t (a bigint NOT NULL);\n").unwrap();
        assert_eq!(FolderCommand::parse("serve", &[dir.clone().into(), "x".into()]), Some(FolderCommand::Serve));
        assert_eq!(FolderCommand::parse("serve-engine", &[dir.clone().into()]), Some(FolderCommand::ServeEngine));
        assert_eq!(FolderCommand::parse("synthesize", &[dir.clone().into()]), None);
        assert_eq!(FolderCommand::parse("serve", &[dir.join("schema.sql").into(), "run".into()]), None);
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
