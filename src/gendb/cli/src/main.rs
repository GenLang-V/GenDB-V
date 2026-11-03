//! `gendb`: the one command of GenDB. A subcommand only parses its arguments, calls the library module that owns the
//! work, prints that module's machine-readable record and maps the outcome to an exit code:
//!
//! - `gendb synthesize|preflight|serve|prepare-flat-storage REQUEST RUN_DIR`: one workload run of the public controller,
//!   see [`workload`];
//! - `gendb run FOLDER ...`: a workload folder driven to its results in resumable steps (requests, data, preparation,
//!   baselines, synthesis), see [`run`]; `serve`, `evaluate`, `import` and `serve-engine` also take a workload folder in
//!   place of a request (`run::folder_command`);
//! - `gendb sql ...`: the SQLSpec reference workflow (`gendb_verification::reference`), see [`sql`];
//! - `gendb baseline ...`: exact qualification of baseline-engine answers per binding
//!   (`gendb_verification::baseline`), see [`baseline`];
//! - `gendb worker REQUEST RESULT`: the isolated worker child (`gendb_runtime::worker::worker_main`);
//! - `gendb author-tools mcp CONTEXT EVIDENCE_DIR`: the local-tool MCP server of one author call, workload storage or
//!   query author (`gendb_synthesis::tools::mcp`), on stdin/stdout;
//! - `gendb exclude-storage LIBRARY POLICY PACKAGE REASON`: the user's persistent exclusion of a storage package under
//!   a storage policy (`gendb_synthesis::storage::exclusion`), appended to the library.
//! - `gendb seed-engine-library SOURCE TARGET [--apply] [PACKAGE]...`: seed an engine library (or a new library whose
//!   query sessions continue from another run's admitted packages, `queries[].continue_from`) with admitted storage
//!   packages and their assets by hard links (`gendb_synthesis::storage::engine_library`); a dry run without `--apply`;
//! - `gendb serve-engine REQUEST OUT_DIR`: serve SQL statements (or AST bytes) from an engine library's admitted engine
//!   version (`gendb_synthesis::engine::serving`);
//! - `gendb engine synthesize|prepare|render-inputs|final-evaluation|re-evaluate REQUEST ...`, `gendb engine
//!   operator-note RUN_DIR BRANCH TEXT` and `gendb engine operator-resume RUN_DIR BRANCH [TEXT]`: the engine run (schema
//!   line in rounds, general line in branch sessions), the general line's version 0 alone, one round's first-call inputs
//!   without a provider, the general line's final evaluation of one version, or the operator's records for a branch
//!   (`gendb_synthesis::engine::rounds`, `gendb_synthesis::engine::final_evaluation`,
//!   `gendb_synthesis::engine::operator_resume`); `synthesize` and `prepare` stop on SIGTERM/SIGINT after every process
//!   they started (`gendb_runtime::process_stop`);
//! - `gendb engine export RUN_DIR VERSION OUT` and `gendb engine check-request REQUEST.json`: the source of one admitted
//!   version of a general-line run as an engine folder another run can seed from (`engine.workloads` seed `{source}`;
//!   `gendb_synthesis::engine::export::export_version`), and the inputs, libraries and assets of every workload of a
//!   request at every scale checked without a timing (`gendb_synthesis::engine::rounds::check_request`); both routed by
//!   `gendb_synthesis::engine::rounds::command`, like every engine subcommand;
//! - `gendb processes RUN_DIR`: what is left of a run's ended controller launches (`gendb_runtime::process_stop::
//!   leftovers`); lists only, exit 1 when something is left;
//! - `gendb evaluate REQUEST BINDINGS HOME`: the final evaluation of the admitted packages at named bindings
//!   (`gendb_synthesis::output::evaluation`);
//! - `gendb import REQUEST PUBLISHED_DIR RUN_DIR`: the packages of a published run folder admitted into the request's
//!   library without any author (`gendb_synthesis::controller::workload_run::import`);
//! - `gendb rebuild QUERY [HOME [OUT]]`: a published query's full crate (`gendb_synthesis::output::rebuild`);
//! - `gendb output query HOME REQUEST INDEX SESSION` / `gendb output workload HOME SESSION`: (re)write the output home
//!   of a closed session (`gendb_synthesis::output`), as the controller does after a session;
//! - `reclaim-trial-assets`, `benchmark-inputs`, `render-query-inputs`, `render-saved-prompt`, `operator-stop` and
//!   `build-identity`: see `HELP` (`gendb help`), which lists every command with its arguments.
//!
//! GenDB starts the worker and the author tools with this same executable (`std::env::current_exe()`), so there is no
//! second binary. Exit codes: 0 success, 1 a recorded non-success outcome of `sql` (a refused statement, a failed
//! proof, a mismatch) or `baseline` (an answer not eligible as a target), 2 a usage error, 3 a failure. The workload routes exit 0 whenever the controller returned its
//! record (its `status` says what happened). The worker keeps its own contract: 0 result written, 1 refusal, 2 usage.
//! Saved ABI v1/v2 packages, format 1 requests and the pre-refactor commands belong to the earlier GenDB version
//! (not part of this repository).

mod baseline;
mod run;
mod sql;
mod workload;

use gendb_runtime::worker::{WORKER_SUBCOMMAND, worker_main};
use gendb_synthesis::controller::workload_run::authors::LOCAL_TOOL_SERVER_WORDS;
use gendb_synthesis::tools::mcp;
use std::ffi::OsString;
use std::path::Path;
use std::process::ExitCode;
use workload::Route;

const HELP: &str = "\
usage: gendb <command> [arguments]

commands:
  run           FOLDER [--config FILE] [--mode templates|engine] [--storage designed|plain] [--scale S] [--threads 1,8]
                [--queries Q01,Q06] [--out WORK] [--until data|requests|baselines|prepare|preflight]   a workload folder
                (schema.sql, queries/, data/, bindings.json, gendb.toml) to its results in steps recorded in WORK/run.json
                (default WORK: FOLDER/runs/<mode>[-<storage>]-<scales>); a rerun skips finished steps. --until preflight
                stops after the free steps (data, requests, DuckDB baselines, preparation, preflight, the first query's
                rendered inputs); without --until the authors are called
  serve | evaluate | import | serve-engine   FOLDER [--out WORK] ...   the folder forms: serve [--query Q [--args A,B |
                --binding ID]] (default every query at every binding), evaluate [--bindings FILE], import PUBLISHED_RUN
                (default WORK FOLDER/runs/import-<name>), serve-engine (every query at the last scale's bindings)
  synthesize    REQUEST.json RUN_DIR   author, verify and admit the workload's storages (workload_storage) and every query
  preflight     REQUEST.json RUN_DIR   statements, data preparation and preflight only; no author is called
  serve         REQUEST.json RUN_DIR   serve admitted packages at the request's bindings; no synthesis
  prepare-flat-storage REQUEST.json RUN_DIR   storage_policy fixed_flat: prepare the fixed flat storage of every table
                once (verified, assets from the capture's column files, registered); no preflight, no author
  sql           SQL reference workflow: translate, check-library, build, run, eval, diff (gendb sql --help)
  baseline      session | qualify   a binding's baseline-runner session; exact qualification of a recorded
                baseline answer against the run's reference (gendb baseline help)
  worker        REQUEST.json RESULT.json   one isolated worker request (started by GenDB itself)
  author-tools  mcp CONTEXT.json EVIDENCE_DIR   an author's local-tool server (started by GenDB itself)
  reclaim-trial-assets SESSION_DIR LIBRARY [--apply] [--keep ASSET]...   list (with --apply remove) an ended author
                session's disposable run-local trial assets; never modifies the library
  evaluate      REQUEST.json BINDINGS.json HOME   serve every named query at every named binding and worker count,
                1 warm + 3 hot calls per cell under the timing lock; results in HOME/evaluation/ and HOME/records/evaluation/
  import        REQUEST.json PUBLISHED_DIR RUN_DIR   admit the published packages of PUBLISHED_DIR (for example GenDB-V's
                results/<workload>/<run>/) into the request's library over the request's data, without any author: each
                request query takes the published query with the same template text; only author files are taken (fixed
                files generated again), each crate verified whole by Verus, storages built over the data, queries
                evaluated and qualified; then gendb serve and gendb evaluate run them. A rerun on RUN_DIR resumes
  rebuild       QUERY [HOME [OUT]]   assemble a published query's full crate (default HOME output/tpch-sf100, OUT
                ./rebuild-QUERY) from the library's framework files and HOME's author code
  output        query HOME REQUEST.json INDEX SESSION_DIR | workload HOME SESSION_DIR   write the readable output home of a
                closed query (request query INDEX, named by its `name`) or workload storage session
  exclude-storage LIBRARY POLICY PACKAGE REASON   record the user's review exclusion of a storage package under a
                storage policy (physical_only) in the library: append-only; every later request of that policy honors
                it; nothing is deleted and other policies are unaffected
  benchmark-inputs REQUEST KEYS VISIBLE TARGETS MIN_SPEEDUP OUT   write REQUEST with each query's visible benchmark
                bindings, runtime targets and early stop (KEYS: benchmark keys in request order, comma separated)
  render-query-inputs REQUEST.json QUERY OUT_DIR   the inputs of query QUERY's first author call (prompt, context,
                author contract) through the public controller with a render-only author: no provider, nothing admitted
  render-saved-prompt SESSION_DIR CALL OUT.md   the prompt of a saved author call (SESSION_DIR/calls/CALL) rendered
                again by this executable's prompt code from the session's records as they were before that call (for
                reviewing a prompt change; not what the author received): no provider, nothing admitted
  operator-stop SESSION_DIR REASON   record the operator's stop of one author session (<run>/queries/query-NNNN): before
                its next author call it qualifies its best candidate and closes (reason operator_stop); written once;
                signals nothing (a running call ends on its own, or when its provider group is interrupted)
  build-identity   print this executable's preflight and reference source identities and runtime build identity (JSON)
  seed-engine-library SOURCE TARGET [--apply] [PACKAGE]...   seed the engine library TARGET (or a new library for query
                sessions with continue_from) with admitted storage packages of SOURCE (default: every storage name's
                current version) and their assets, by hard links; no query package, nothing built or hashed; a dry run
                (reads SOURCE only) unless --apply
  engine        synthesize REQUEST.json RUN_DIR | prepare REQUEST.json RUN_DIR | render-inputs REQUEST.json OUT_DIR
                [PREPARED_RUN_DIR]   the engine run (schema line: rounds of one engine author session each; general line:
                branch sessions from version 0), the general line's version 0 alone, or the first call's inputs (no
                provider). SIGTERM or SIGINT to synthesize or prepare stops every process it started, records
                RUN_DIR/processes/stop-<id>.json and ends it with that signal; relaunching the command resumes the run.
                final-evaluation REQUEST.json RUN_DIR VERSION [SCALE [WORKLOAD]]: the general line's full protocol (1 warm
                + 3 hot calls per cell at every worker count, every visible binding, timed variants, a profile) of one
                admitted version at one scale (default, or SCALE `-`: the run's current one; in a stage run the
                workload's last), under RUN_DIR/engine/final/; WORKLOAD names a stage run's workload (default: the goal),
                evaluated in its own library; for reporting only
                re-evaluate REQUEST.json RUN_DIR ATTEMPT: with the run's controller stopped, the development evaluation of
                an attempt judged not better, again: its recorded Verus run and race, the race's suspicious pairs timed
                again after a quiet host; admitted as the next version when now better; the branch is told by a note
                operator-note RUN_DIR BRANCH TEXT: a note shown once at the top of the branch's next author call
                operator-resume RUN_DIR BRANCH [TEXT]: with the run's controller stopped (refused while it runs), record
                that the branch's provider wait (calls/NNNN/provider-wait.json) is over, with the reason TEXT; the
                relaunched controller then calls at once, in the same provider session with the short continuation
                message (provider-wait-cleared.json beside the wait's record; written once)
                export RUN_DIR VERSION OUT: the source of one admitted version as an engine folder OUT (the shared engine,
                the default module, the storage families, the plans, a manifest and a README with every workload's proof
                and admission digests), which a run's engine.workloads names as a seed {source: OUT}; OUT must not exist
                check-request REQUEST.json: every workload of the request (engine.workloads members included) at every
                scale: its inputs, its library and its scale's assets, read and checked; no timing, nothing written; exit 0
                when nothing was found, 1 when it lists problems (run it before engine prepare)
  processes     RUN_DIR   list the live processes left by the run's ended controller launches (RUN_DIR/processes/):
                carrying a launch's tag, in its process group or session after the leader ended, or working under
                RUN_DIR; signals nothing; exit 1 when something is left
  serve-engine  REQUEST.json OUT_DIR   serve SQL statements with one binding each (or AST bytes) from an engine library's
                selected (or named) engine version at the requested worker counts; echo verdict and AST digest per cell

Exit codes: 0 success, 1 recorded non-success outcome (sql, baseline, engine check-request), 2 usage error, 3 failure.
Saved pre-refactor packages, format 1 requests and commands: the earlier GenDB version (not part of this repository).";

fn main() -> ExitCode {
    let arguments: Vec<OsString> = std::env::args_os().skip(1).collect();
    let Some((command, rest)) = arguments.split_first() else {
        eprintln!("{HELP}");
        return ExitCode::from(2);
    };
    let Some(word) = command.to_str() else {
        eprintln!("gendb: unknown command {command:?}\n{HELP}");
        return ExitCode::from(2);
    };
    if let Some(command) = run::FolderCommand::parse(word, rest) {
        return run::folder_command(command, rest);
    }
    if let Some(route) = Route::parse(word) {
        return workload::main(route, rest);
    }
    match word {
        WORKER_SUBCOMMAND => worker_main(rest),
        "sql" => sql::main(rest),
        "baseline" => baseline::main(rest),
        "author-tools" => author_tools(rest),
        "reclaim-trial-assets" => reclaim_trial_assets(rest),
        "exclude-storage" => exclude_storage(rest),
        "evaluate" => evaluate(rest),
        "import" => import(rest),
        "rebuild" => rebuild(rest),
        "output" => output(rest),
        "benchmark-inputs" => benchmark_inputs(rest),
        "render-query-inputs" => render_query_inputs(rest),
        "render-saved-prompt" => render_saved_prompt(rest),
        "operator-stop" => operator_stop(rest),
        "build-identity" => build_identity(),
        "seed-engine-library" => seed_engine_library(rest),
        "serve-engine" => serve_engine(rest),
        "engine" => gendb_synthesis::engine::rounds::command(rest),
        "processes" => processes(rest),
        "run" => run::main(rest),
        "help" | "--help" | "-h" => {
            println!("{HELP}");
            ExitCode::SUCCESS
        }
        _ => {
            eprintln!("gendb: unknown command {word}\n{HELP}");
            ExitCode::from(2)
        }
    }
}

/// `gendb render-query-inputs REQUEST.json QUERY OUT_DIR` (`workload_run::render`): prints the render record.
fn render_query_inputs(arguments: &[OsString]) -> ExitCode {
    let [request, query, out] = arguments else {
        eprintln!("usage: gendb render-query-inputs REQUEST.json QUERY OUT_DIR");
        return ExitCode::from(2);
    };
    let Some(query) = query.to_str() else {
        eprintln!("gendb render-query-inputs: QUERY must be UTF-8");
        return ExitCode::from(2);
    };
    let executable = match std::env::current_exe() {
        Ok(executable) => executable,
        Err(error) => {
            eprintln!("gendb render-query-inputs: this executable: {error}");
            return ExitCode::from(3);
        }
    };
    match gendb_synthesis::controller::workload_run::render::render_query_inputs(Path::new(request), query, Path::new(out), &executable) {
        Ok(record) => {
            println!("{}", serde_json::to_string_pretty(&record).expect("JSON values serialize"));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb render-query-inputs: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb render-saved-prompt SESSION_DIR CALL OUT.md` (`workload_run::render`): prints the render record.
fn render_saved_prompt(arguments: &[OsString]) -> ExitCode {
    let [session, call, out] = arguments else {
        eprintln!("usage: gendb render-saved-prompt SESSION_DIR CALL OUT.md");
        return ExitCode::from(2);
    };
    let Some(call) = call.to_str().and_then(|call| call.parse::<u64>().ok()) else {
        eprintln!("gendb render-saved-prompt: CALL must be a call number");
        return ExitCode::from(2);
    };
    match gendb_synthesis::controller::workload_run::render::render_saved_prompt(Path::new(session), call, Path::new(out)) {
        Ok(record) => {
            println!("{}", serde_json::to_string_pretty(&record).expect("JSON values serialize"));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb render-saved-prompt: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb operator-stop SESSION_DIR REASON` (`gendb_synthesis::controller::run::record_operator_stop`): prints the record.
fn operator_stop(arguments: &[OsString]) -> ExitCode {
    let [session, reason] = arguments else {
        eprintln!("usage: gendb operator-stop SESSION_DIR REASON");
        return ExitCode::from(2);
    };
    let Some(reason) = reason.to_str() else {
        eprintln!("gendb operator-stop: REASON must be UTF-8");
        return ExitCode::from(2);
    };
    finish("operator-stop", gendb_synthesis::controller::run::record_operator_stop(Path::new(session), reason))
}

/// `gendb build-identity`: the content identities this executable compares preflight evidence by
/// (`admission::preflight::reuse`) and its runtime build identity.
fn build_identity() -> ExitCode {
    let identity = serde_json::json!({"preflight_sources":gendb_verification::admission::PREFLIGHT_SOURCES,
        "reference_sources":gendb_verification::admission::REFERENCE_SOURCES,"runtime":gendb_runtime::identity::runtime_build_identity()});
    println!("{identity}");
    ExitCode::SUCCESS
}

/// `gendb benchmark-inputs REQUEST KEYS VISIBLE TARGETS MIN_SPEEDUP OUT`
/// (`gendb_synthesis::controller::benchmark_inputs`): write REQUEST to OUT with each query's visible benchmark bindings,
/// runtime targets and early stop; KEYS names the queries' benchmark keys in request order, comma separated (empty
/// entry: query left as it is).
fn benchmark_inputs(arguments: &[OsString]) -> ExitCode {
    const USAGE: &str = "usage: gendb benchmark-inputs REQUEST.json KEYS(Q01,Q02,..) VISIBLE.json TARGETS.json MIN_SPEEDUP OUT.json";
    let words: Option<Vec<&str>> = arguments.iter().map(|word| word.to_str()).collect();
    let Some([request, keys, visible, targets, min_speedup, out]) = words.as_deref() else {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    };
    let read = |path: &str| -> Result<serde_json::Value, String> {
        serde_json::from_slice(&std::fs::read(path).map_err(|e| format!("{path}: {e}"))?).map_err(|e| format!("{path}: {e}"))
    };
    let result = (|| -> Result<(), String> {
        let mut parsed: gendb_synthesis::controller::request::WorkloadRequest = serde_json::from_value(read(request)?).map_err(|e| format!("{request}: {e}"))?;
        let keys: Vec<String> = keys.split(',').map(str::to_string).collect();
        let factor: u32 = min_speedup.parse().map_err(|e| format!("MIN_SPEEDUP: {e}"))?;
        gendb_synthesis::controller::benchmark_inputs::apply_benchmark_inputs(&mut parsed, &keys, &read(visible)?, &read(targets)?, targets, factor)?;
        let text = serde_json::to_string_pretty(&parsed).map_err(|e| e.to_string())?;
        std::fs::write(out, text + "\n").map_err(|e| format!("{out}: {e}"))
    })();
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("gendb benchmark-inputs: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb reclaim-trial-assets SESSION_DIR LIBRARY [--apply] [--keep ASSET]...`
/// (`gendb_synthesis::query::assets::reclaim_ended_session`): prints its record; dry run unless `--apply`.
fn reclaim_trial_assets(arguments: &[OsString]) -> ExitCode {
    const USAGE: &str = "usage: gendb reclaim-trial-assets SESSION_DIR LIBRARY [--apply] [--keep ASSET]...";
    let words: Option<Vec<&str>> = arguments.iter().map(|word| word.to_str()).collect();
    let Some([session, library, flags @ ..]) = words.as_deref() else {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    };
    let (mut apply, mut keep, mut flags) = (false, std::collections::BTreeSet::new(), flags.iter());
    while let Some(flag) = flags.next() {
        match (*flag, flags.clone().next()) {
            ("--apply", _) => apply = true,
            ("--keep", Some(asset)) => match gendb_artifacts::ContentId::parse_hex(asset) {
                Ok(id) => {
                    keep.insert(id);
                    flags.next();
                }
                Err(_) => {
                    eprintln!("gendb reclaim-trial-assets: --keep needs a 64-hex asset id, got {asset}");
                    return ExitCode::from(2);
                }
            },
            _ => {
                eprintln!("{USAGE}");
                return ExitCode::from(2);
            }
        }
    }
    match gendb_synthesis::query::assets::reclaim_ended_session(Path::new(session), Path::new(library), &keep, apply) {
        Ok(record) => {
            println!("{}", serde_json::to_string_pretty(&record).unwrap_or_default());
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb reclaim-trial-assets: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb exclude-storage LIBRARY POLICY PACKAGE REASON` (`gendb_synthesis::storage::exclusion::record_exclusion`):
/// prints the exclusion record (an existing exclusion of the package under the policy is returned unchanged).
fn exclude_storage(arguments: &[OsString]) -> ExitCode {
    use gendb_synthesis::storage::exclusion::{EXCLUSION_MEANING, exclusion_stream, record_exclusion};
    const USAGE: &str = "usage: gendb exclude-storage LIBRARY POLICY PACKAGE REASON";
    let words: Option<Vec<&str>> = arguments.iter().map(|word| word.to_str()).collect();
    let Some([library, policy, package, reason]) = words.as_deref() else {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    };
    let Ok(package) = gendb_artifacts::ContentId::parse_hex(package) else {
        eprintln!("gendb exclude-storage: PACKAGE needs a 64-hex storage package id, got {package}\n{USAGE}");
        return ExitCode::from(2);
    };
    let recorded = gendb_artifacts::ObjectStore::open_existing(library)
        .map_err(|error| format!("library {library}: {error}"))
        .and_then(|store| record_exclusion(&store, policy, package, reason).map_err(|error| error.to_string()));
    match recorded {
        Ok(recorded) => {
            let mut record = serde_json::to_value(&recorded).unwrap_or_default();
            record["stream"] = serde_json::json!(exclusion_stream(policy));
            record["meaning"] = serde_json::json!(EXCLUSION_MEANING);
            println!("{}", serde_json::to_string_pretty(&record).unwrap_or_default());
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb exclude-storage: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb author-tools mcp CONTEXT.json EVIDENCE_DIR`: stdout carries the MCP protocol only, so every error goes to
/// stderr (2 usage, 3 failure).
fn author_tools(arguments: &[OsString]) -> ExitCode {
    let words: Option<Vec<String>> = arguments.iter().map(|word| word.to_str().map(String::from)).collect();
    let server = LOCAL_TOOL_SERVER_WORDS[1];
    let Some([context, evidence]) = (match words.as_deref() {
        Some([word, context, evidence]) if word == server => Some([context.clone(), evidence.clone()]),
        _ => None,
    }) else {
        eprintln!("usage: gendb author-tools {server} {}", mcp::USAGE);
        return ExitCode::from(2);
    };
    match mcp::main(&[context, evidence]) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("gendb author-tools {server}: {message}");
            ExitCode::from(3)
        }
    }
}

/// Print a JSON record (exit 0) or the error (exit 3).
fn finish(command: &str, result: Result<serde_json::Value, String>) -> ExitCode {
    match result {
        Ok(record) => {
            println!("{}", serde_json::to_string_pretty(&record).unwrap_or_default());
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb {command}: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb evaluate REQUEST.json BINDINGS.json HOME` (`gendb_synthesis::output::evaluation::evaluate`).
fn evaluate(arguments: &[OsString]) -> ExitCode {
    let words: Option<Vec<&str>> = arguments.iter().map(|w| w.to_str()).collect();
    let Some([request, bindings, home]) = words.as_deref() else {
        eprintln!("usage: gendb evaluate REQUEST.json BINDINGS.json HOME");
        return ExitCode::from(2);
    };
    let result = std::env::current_exe()
        .map_err(|e| format!("this executable: {e}"))
        .and_then(|exe| gendb_synthesis::output::evaluation::evaluate(Path::new(request), Path::new(bindings), Path::new(home), &exe).map_err(|e| e.to_string()));
    finish("evaluate", result)
}

/// `gendb import REQUEST.json PUBLISHED_DIR RUN_DIR` (`gendb_synthesis::controller::workload_run::import::import`): prints
/// the import summary (its `status` says whether everything closed; `admitted` and `refused` list the outcomes).
fn import(arguments: &[OsString]) -> ExitCode {
    let [request, published, run_dir] = arguments else {
        eprintln!("usage: gendb import REQUEST.json PUBLISHED_DIR RUN_DIR");
        return ExitCode::from(2);
    };
    let result = std::env::current_exe().map_err(|e| format!("this executable: {e}")).and_then(|exe| {
        let runtime = tokio::runtime::Runtime::new().map_err(|e| format!("async runtime: {e}"))?;
        runtime
            .block_on(gendb_synthesis::controller::workload_run::import::import(Path::new(request), Path::new(published), Path::new(run_dir), &exe))
            .map_err(|e| e.to_string())
    });
    finish("import", result)
}

/// `gendb rebuild QUERY [HOME [OUT]]` (`gendb_synthesis::output::rebuild`).
fn rebuild(arguments: &[OsString]) -> ExitCode {
    let words: Option<Vec<&str>> = arguments.iter().map(|w| w.to_str()).collect();
    let (query, home, out) = match words.as_deref() {
        Some([q]) => (*q, "output/tpch-sf100".to_string(), format!("rebuild-{q}")),
        Some([q, h]) => (*q, h.to_string(), format!("rebuild-{q}")),
        Some([q, h, o]) => (*q, h.to_string(), o.to_string()),
        _ => {
            eprintln!("usage: gendb rebuild QUERY [HOME [OUT]]");
            return ExitCode::from(2);
        }
    };
    let result = gendb_synthesis::output::rebuild(Path::new(&home), query, Path::new(&out))
        .map(|dir| serde_json::json!({"query":query,"crate":dir}))
        .map_err(|e| e.to_string());
    finish("rebuild", result)
}

/// `gendb output query HOME REQUEST.json INDEX SESSION_DIR` or `gendb output workload HOME SESSION_DIR`.
fn output(arguments: &[OsString]) -> ExitCode {
    use gendb_synthesis::controller::request::WorkloadRequest;
    use gendb_synthesis::output::{QueryOutput, WorkloadOutput, write_query, write_workload};
    let words: Option<Vec<&str>> = arguments.iter().map(|w| w.to_str()).collect();
    let result = match words.as_deref() {
        Some(["query", home, request, index, session]) => (|| {
            let text = std::fs::read_to_string(request).map_err(|e| format!("{request}: {e}"))?;
            let parsed: WorkloadRequest = serde_json::from_str(&text).map_err(|e| format!("{request}: {e}"))?;
            let index: usize = index.parse().map_err(|_| format!("INDEX must be a query position, got {index}"))?;
            let query = parsed.queries.get(index).ok_or_else(|| format!("the request has no query {index}"))?;
            let name = query.name.clone().unwrap_or_else(|| format!("query-{index:04}"));
            let out = QueryOutput { name: &name, request: query, session: Path::new(session), library: &parsed.library };
            write_query(Path::new(home), &out).map_err(|e| e.to_string())
        })(),
        Some(["workload", home, session]) => (|| {
            // The library is the run's: `<run>/request.json` of the session `<run>/workload-storage/session`.
            let request = Path::new(session).join("../../request.json");
            let text = std::fs::read_to_string(&request).map_err(|e| format!("{}: {e} (the workload session's run request names the library)", request.display()))?;
            let parsed: WorkloadRequest = serde_json::from_str(&text).map_err(|e| format!("{}: {e}", request.display()))?;
            write_workload(Path::new(home), &WorkloadOutput { session: Path::new(session), library: &parsed.library }).map_err(|e| e.to_string())
        })(),
        _ => {
            eprintln!("usage: gendb output query HOME REQUEST.json INDEX SESSION_DIR | gendb output workload HOME SESSION_DIR");
            return ExitCode::from(2);
        }
    };
    finish("output", result)
}

/// `gendb seed-engine-library SOURCE TARGET [--apply] [PACKAGE]...` (`gendb_synthesis::storage::engine_library`): prints
/// the seed record; a dry run unless `--apply`.
fn seed_engine_library(arguments: &[OsString]) -> ExitCode {
    const USAGE: &str = "usage: gendb seed-engine-library SOURCE_LIBRARY TARGET_LIBRARY [--apply] [PACKAGE]...";
    let words: Option<Vec<&str>> = arguments.iter().map(|w| w.to_str()).collect();
    let Some([source, target, rest @ ..]) = words.as_deref() else {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    };
    let apply = rest.contains(&"--apply");
    let packages: Result<Vec<gendb_artifacts::ContentId>, _> = rest.iter().filter(|w| **w != "--apply").map(|w| gendb_artifacts::ContentId::parse_hex(w)).collect();
    let Ok(packages) = packages else {
        eprintln!("gendb seed-engine-library: every PACKAGE is a 64-hex storage package id\n{USAGE}");
        return ExitCode::from(2);
    };
    let result = gendb_synthesis::storage::engine_library::seed_engine_library(Path::new(source), Path::new(target), &packages, apply).map_err(|e| e.to_string());
    finish("seed-engine-library", result)
}

/// `gendb processes RUN_DIR` (`gendb_runtime::process_stop::leftovers`): prints the leftovers record; exit 0 when no
/// process is left, 1 when some are, 3 when the records or the process table cannot be read.
fn processes(arguments: &[OsString]) -> ExitCode {
    let [run] = arguments else {
        eprintln!("usage: gendb processes RUN_DIR");
        return ExitCode::from(2);
    };
    match gendb_runtime::process_stop::leftovers(Path::new(run)) {
        Ok(leftovers) => {
            println!("{}", serde_json::to_string_pretty(&leftovers).expect("JSON values serialize"));
            if leftovers.processes.is_empty() { ExitCode::SUCCESS } else { ExitCode::from(1) }
        }
        Err(error) => {
            eprintln!("gendb processes: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb serve-engine REQUEST.json OUT_DIR` (`gendb_synthesis::engine::serving::serve_engine_request`).
fn serve_engine(arguments: &[OsString]) -> ExitCode {
    let [request, out] = arguments else {
        eprintln!("usage: gendb serve-engine REQUEST.json OUT_DIR");
        return ExitCode::from(2);
    };
    let result = std::env::current_exe()
        .map_err(|e| format!("this executable: {e}"))
        .and_then(|exe| gendb_synthesis::engine::serving::serve_engine_request(Path::new(request), Path::new(out), &exe));
    finish("serve-engine", result)
}
