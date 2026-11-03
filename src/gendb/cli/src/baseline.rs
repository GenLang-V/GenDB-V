//! `gendb baseline`: exact qualification of baseline-engine answers per binding (`gendb_verification::baseline`).
//! `session` prints a binding's baseline-runner session (JSONL); `qualify` prints (with `--out`, also writes once) the
//! qualification record of one runner block.

use gendb_verification::baseline::{BaselineError, StatementEvidence};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const USAGE: &str = "\
usage: gendb baseline <subcommand> --flag value...
  session  --statement DIR --binding NAME --name STATEMENT_ID
           the binding's runner session: bound SQL (each $n as CAST('<text>' AS <declared type>)), output fields
  qualify  --statement DIR --binding NAME --session FILE --engine-output FILE --workers N [--out FILE]
           exact qualification record; exit 0 target-eligible, 1 recorded not eligible
DIR is a run's statement evidence directory (queries/query-NNNN/verus-preflight). Exit 1 also for a refused
session rendering, 2 usage, 3 failure (unreadable inputs).";

/// Entry of `gendb baseline` (`arguments`: the words after `baseline`).
pub fn main(arguments: &[OsString]) -> ExitCode {
    let words: Option<Vec<&str>> = arguments.iter().map(|word| word.to_str()).collect();
    let Some([subcommand, rest @ ..]) = words.as_deref() else {
        return usage("a subcommand is required");
    };
    if matches!(*subcommand, "help" | "--help" | "-h") {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let mut flags = std::collections::BTreeMap::new();
    for pair in rest.chunks(2) {
        match pair {
            [flag, value] if flag.starts_with("--") && flags.insert(&flag[2..], *value).is_none() => {}
            _ => return usage(&format!("bad flags {pair:?}")),
        }
    }
    let known: &[&str] = match *subcommand {
        "session" => &["statement", "binding", "name"],
        "qualify" => &["statement", "binding", "session", "engine-output", "workers", "out"],
        _ => return usage(&format!("unknown subcommand {subcommand}")),
    };
    if let Some(flag) = flags.keys().find(|f| !known.contains(f)) {
        return usage(&format!("unknown flag --{flag}"));
    }
    // Errors carry their exit code: 1 refused, 2 usage, 3 failure.
    let required = |name: &str| flags.get(name).copied().ok_or((2, format!("--{name} is required")));
    let result = (|| -> Result<ExitCode, (u8, String)> {
        let evidence = StatementEvidence::open(Path::new(required("statement")?)).map_err(message)?;
        let binding = required("binding")?;
        if *subcommand == "session" {
            let lines = evidence.session(binding, required("name")?).map_err(message)?;
            lines.iter().for_each(|line| println!("{line}"));
            return Ok(ExitCode::SUCCESS);
        }
        let workers = required("workers")?.parse().map_err(|_| (2, "--workers must be a count".to_string()))?;
        let record = evidence.qualify(binding, Path::new(required("session")?), Path::new(required("engine-output")?), workers).map_err(message)?;
        let text = serde_json::to_string_pretty(&record).expect("JSON values serialize");
        if let Some(out) = flags.get("out") {
            write_once(&PathBuf::from(out), &text)?;
        }
        println!("{text}");
        Ok(if record["target_eligible"] == true { ExitCode::SUCCESS } else { ExitCode::from(1) })
    })();
    result.unwrap_or_else(|(code, error)| {
        eprintln!("gendb baseline {subcommand}: {error}");
        if code == 2 {
            eprintln!("{USAGE}");
        }
        ExitCode::from(code)
    })
}

fn message(error: BaselineError) -> (u8, String) {
    match error {
        BaselineError::Refused(why) => (1, format!("refused: {why}")),
        BaselineError::Failure(why) => (3, why),
    }
}

/// Write `text` to a new file (an existing record is never overwritten).
fn write_once(path: &Path, text: &str) -> Result<(), (u8, String)> {
    use std::io::Write;
    let failed = |e: std::io::Error| (3, format!("{}: {e}", path.display()));
    std::fs::File::create_new(path).map_err(failed)?.write_all(format!("{text}\n").as_bytes()).map_err(failed)
}

fn usage(problem: &str) -> ExitCode {
    eprintln!("gendb baseline: {problem}\n{USAGE}");
    ExitCode::from(2)
}
