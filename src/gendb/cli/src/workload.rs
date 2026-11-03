//! `gendb synthesize|preflight|serve|prepare-flat-storage REQUEST.json RUN_DIR`: one workload run of the public controller
//! (`gendb_synthesis::controller::workload_run`). The controller owns everything: request validation, the run
//! directory's records, data preparation, author sessions, admission and serving; this command passes it the request,
//! the run directory and this executable (which runs candidate libraries as `gendb worker` and the authors' local tools
//! as `gendb author-tools mcp`), then prints the returned record.

use gendb_synthesis::controller::workload_run::{self, WorkloadError};
use serde_json::Value;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// The route of a workload run; a run directory belongs to one route.
#[derive(Clone, Copy)]
pub enum Route {
    /// Author sessions per query, admission, the workload summary.
    Synthesize,
    /// Statements, data preparation and every query's preflight, without any author (a dry run before paying).
    Preflight,
    /// Serve admitted packages at the request's bindings and worker counts; no synthesis.
    Serve,
    /// Prepare the fixed flat storages of a `fixed_flat` request once; no preflight, no author.
    PrepareFlatStorage,
}

impl Route {
    pub fn parse(word: &str) -> Option<Self> {
        Some(match word {
            "synthesize" => Self::Synthesize,
            "preflight" => Self::Preflight,
            "serve" => Self::Serve,
            "prepare-flat-storage" => Self::PrepareFlatStorage,
            _ => return None,
        })
    }

    fn name(self) -> &'static str {
        match self {
            Self::Synthesize => "synthesize",
            Self::Preflight => "preflight",
            Self::Serve => "serve",
            Self::PrepareFlatStorage => "prepare-flat-storage",
        }
    }
}

/// Entry of `gendb <route>` (`arguments`: the words after it). Prints the controller's record (the workload summary,
/// the preflight record or the serving summary) as JSON; its `status` says what happened. Exit 0 when the controller
/// returned a record, 2 for a usage error, 3 when the run stopped with an error (printed on stderr).
pub fn main(route: Route, arguments: &[OsString]) -> ExitCode {
    let usage = format!("usage: gendb {} REQUEST.json RUN_DIR", route.name());
    let [request, run_dir] = arguments else {
        eprintln!("{usage}");
        return ExitCode::from(2);
    };
    if [request, run_dir].iter().any(|word| matches!(word.to_str(), Some("--help" | "-h"))) {
        println!("{usage}");
        return ExitCode::SUCCESS;
    }
    match run(route, Path::new(request), Path::new(run_dir)) {
        Ok(record) => {
            println!("{}", serde_json::to_string_pretty(&record).expect("JSON values serialize"));
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("gendb {}: {message}", route.name());
            ExitCode::from(3)
        }
    }
}

fn run(route: Route, request: &Path, run_dir: &Path) -> Result<Value, String> {
    let executable = framework_executable()?;
    let result: Result<Value, WorkloadError> = match route {
        Route::Serve => workload_run::serve(request, run_dir, &executable),
        Route::Synthesize => async_runtime()?.block_on(workload_run::synthesize(request, run_dir, &executable)),
        Route::Preflight => async_runtime()?.block_on(workload_run::preflight(request, run_dir, &executable)),
        Route::PrepareFlatStorage => workload_run::flat_preparation::prepare_flat_storage(request, run_dir),
    };
    result.map_err(|error| error.to_string())
}

/// This executable, which the controller runs as the worker and as the authors' local-tool server.
fn framework_executable() -> Result<PathBuf, String> {
    std::env::current_exe().map_err(|e| format!("this executable: {e}"))
}

/// The runtime of the asynchronous routes; created only for them, never for `gendb worker`.
fn async_runtime() -> Result<tokio::runtime::Runtime, String> {
    tokio::runtime::Runtime::new().map_err(|e| format!("async runtime: {e}"))
}
