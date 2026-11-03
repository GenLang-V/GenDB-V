//! `gendb sql`: the SQLSpec reference workflow, one subcommand per function of `gendb_verification::reference`
//! (SQL + schema DDL, PostgreSQL dialect -> typed AST -> evaluator crate -> one pinned `rust_verify --no-cheating
//! --compile` run -> verified evaluator -> run on fixture databases). Each subcommand writes its records once (an
//! output path must not exist) and prints its record as JSON on stdout.
//!
//! Path flags are made absolute here: the parser and Verus run in their own working directories. Toolchains come
//! from their pins, overridable by the environment variables named in [`USAGE`].

use gendb_frontend::ast::Translation;
use gendb_frontend::parser::{ParserError, SqlParser};
use gendb_verification::reference::{
    self, BuildOptions, BuildStatus, DEFAULT_EVALUATOR_CRATE_NAME, ReferenceError, RunProcess, StatementSource,
};
use gendb_verification::verus::{FrozenCrate, ToolchainError, VerusToolchain};
use serde_json::Value;
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::PathBuf;
use std::process::ExitCode;

const USAGE: &str = "\
usage: gendb sql <subcommand> [--flag value]...
  translate      --schema DDL (--sql FILE | --query-file FILE --label L) --out DIR
  check-library  --out DIR
  build          --ast AST.json --out DIR [--checked-library DIR] [--crate-name NAME]
  run            --build DIR --fixture FIXTURE.json --out FILE
  eval           --schema DDL (--sql FILE | --query-file FILE --label L) --fixture FIXTURE.json --out DIR
                 [--checked-library DIR] [--crate-name NAME]
  diff           --fixture FIXTURE.json --reference PG_EVIDENCE.json --out DIR [--checked-library DIR]
Prints the subcommand's JSON record. Exit 0 ok, 1 recorded non-ok outcome, 2 usage, 3 framework failure.
Toolchains: GENDB_VERUS_HOME (Verus); GENDB_SQL_FRONTEND_PYTHON, GENDB_SQL_FRONTEND_DIR (SQL parser).";

/// Entry of `gendb sql` (`arguments`: the words after `sql`).
pub fn main(arguments: &[OsString]) -> ExitCode {
    match dispatch(arguments) {
        Ok(outcome) => {
            println!("{}", serde_json::to_string_pretty(&outcome.record).expect("JSON values serialize"));
            if outcome.ok { ExitCode::SUCCESS } else { ExitCode::from(1) }
        }
        Err(Failure::Help) => {
            println!("{USAGE}");
            ExitCode::SUCCESS
        }
        Err(Failure::Usage(message)) => {
            eprintln!("gendb sql: {message}\n{USAGE}");
            ExitCode::from(2)
        }
        Err(Failure::Framework(message)) => {
            eprintln!("gendb sql: {message}");
            ExitCode::from(3)
        }
    }
}

/// A subcommand's record and whether it reports success (exit 0) or a recorded non-success outcome (exit 1).
struct Outcome {
    record: Value,
    ok: bool,
}

enum Failure {
    Help,
    Usage(String),
    /// The workflow could not complete (toolchain, parser, files, records); never a recorded outcome.
    Framework(String),
}

macro_rules! framework_failure {
    ($($error:ty),*) => {
        $(impl From<$error> for Failure {
            fn from(e: $error) -> Self {
                Failure::Framework(e.to_string())
            }
        })*
    };
}

framework_failure!(ReferenceError, ToolchainError, ParserError);

#[derive(Clone, Copy)]
enum Subcommand {
    Translate,
    CheckLibrary,
    Build,
    Run,
    Eval,
    Diff,
}

impl Subcommand {
    fn parse(word: &str) -> Option<Self> {
        Some(match word {
            "translate" => Self::Translate,
            "check-library" => Self::CheckLibrary,
            "build" => Self::Build,
            "run" => Self::Run,
            "eval" => Self::Eval,
            "diff" => Self::Diff,
            _ => return None,
        })
    }

    /// The flags the subcommand accepts; any other flag is a usage error.
    fn flags(self) -> &'static [&'static str] {
        match self {
            Self::Translate => &["schema", "sql", "query-file", "label", "out"],
            Self::CheckLibrary => &["out"],
            Self::Build => &["ast", "out", "checked-library", "crate-name"],
            Self::Run => &["build", "fixture", "out"],
            Self::Eval => &["schema", "sql", "query-file", "label", "fixture", "out", "checked-library", "crate-name"],
            Self::Diff => &["fixture", "reference", "out", "checked-library"],
        }
    }
}

fn dispatch(arguments: &[OsString]) -> Result<Outcome, Failure> {
    let words: Vec<&str> = arguments
        .iter()
        .map(|word| word.to_str().ok_or_else(|| Failure::Usage(format!("argument {word:?} is not UTF-8"))))
        .collect::<Result<_, _>>()?;
    let (word, rest) = words.split_first().ok_or_else(|| Failure::Usage("a subcommand is required".into()))?;
    if matches!(*word, "help" | "--help" | "-h") {
        return Err(Failure::Help);
    }
    let subcommand = Subcommand::parse(word).ok_or_else(|| Failure::Usage(format!("unknown subcommand {word}")))?;
    let flags = Flags::parse(rest, subcommand.flags())?;
    match subcommand {
        Subcommand::Translate => translate(&flags),
        Subcommand::CheckLibrary => check_library(&flags),
        Subcommand::Build => build(&flags),
        Subcommand::Run => run_evaluator(&flags),
        Subcommand::Eval => evaluate(&flags),
        Subcommand::Diff => diff(&flags),
    }
}

fn translate(flags: &Flags) -> Result<Outcome, Failure> {
    let schema = flags.required_path("schema")?;
    let source = statement_source(flags)?;
    let out = flags.required_path("out")?;
    let translated = reference::translate(&SqlParser::from_environment()?, &schema, &source, &out)?;
    let ok = matches!(translated.translation, Translation::Ok(_));
    Ok(Outcome { record: translated.record, ok })
}

fn check_library(flags: &Flags) -> Result<Outcome, Failure> {
    let out = flags.required_path("out")?;
    let check = reference::check_library(&pinned_toolchain()?, &out)?;
    Ok(Outcome { ok: check.verified(), record: check.record })
}

fn build(flags: &Flags) -> Result<Outcome, Failure> {
    let ast = flags.required_path("ast")?;
    let out = flags.required_path("out")?;
    let checked = checked_library(flags)?;
    let options = build_options(flags, checked.as_ref());
    let build = reference::build_ast_file(&pinned_toolchain()?, &ast, &out, &options)?;
    Ok(Outcome { ok: build.status == BuildStatus::Ok, record: build.record })
}

fn run_evaluator(flags: &Flags) -> Result<Outcome, Failure> {
    let build = flags.required_path("build")?;
    let fixture = flags.required_path("fixture")?;
    let out = flags.required_path("out")?;
    let evaluation = reference::run_evaluator(&build, &fixture, &out)?;
    Ok(Outcome { ok: evaluation.is_sql_outcome(), record: evaluation.record })
}

fn evaluate(flags: &Flags) -> Result<Outcome, Failure> {
    let schema = flags.required_path("schema")?;
    let source = statement_source(flags)?;
    let fixture = flags.required_path("fixture")?;
    let out = flags.required_path("out")?;
    let checked = checked_library(flags)?;
    let options = build_options(flags, checked.as_ref());
    let (toolchain, parser) = (pinned_toolchain()?, SqlParser::from_environment()?);
    let evaluation = reference::evaluate(&toolchain, &parser, &schema, &source, &fixture, &out, &options)?;
    Ok(Outcome { ok: evaluation.is_sql_outcome(), record: evaluation.record })
}

/// Every case of a reference fixture against recorded PostgreSQL evidence. Each case's evaluator runs in a child
/// `gendb sql run` of this executable; the printed record has one short line per case (`diff.json` has them all).
fn diff(flags: &Flags) -> Result<Outcome, Failure> {
    let fixture = flags.required_path("fixture")?;
    let evidence = flags.required_path("reference")?;
    let out = flags.required_path("out")?;
    let checked = checked_library(flags)?;
    let program = std::env::current_exe().map_err(|e| Failure::Framework(format!("this executable: {e}")))?;
    let child = RunProcess { program, args: vec!["sql".into(), "run".into()] };
    let (toolchain, parser) = (pinned_toolchain()?, SqlParser::from_environment()?);
    let diff = reference::diff_fixture(&toolchain, &parser, &child, &fixture, &evidence, &out, checked.as_ref())?;
    Ok(Outcome { ok: diff.all_matched(), record: diff.brief() })
}

/// The pinned Verus installation, checked to be the pinned release before any output is written.
fn pinned_toolchain() -> Result<VerusToolchain, Failure> {
    let toolchain = VerusToolchain::from_env()?;
    toolchain.version()?;
    Ok(toolchain)
}

/// `--sql FILE`, or `--query-file FILE --label L` (the query headed `-- L:` in that file).
fn statement_source(flags: &Flags) -> Result<StatementSource, Failure> {
    match (flags.path("sql"), flags.path("query-file"), flags.text("label")) {
        (Some(sql), None, None) => Ok(StatementSource::Sql(sql)),
        (None, Some(file), Some(label)) => Ok(StatementSource::Labelled { file, label: label.to_owned() }),
        _ => Err(Failure::Usage("give --sql FILE or --query-file FILE --label L".into())),
    }
}

/// The verified library snapshot of `--checked-library DIR` (a `check-library` output), if given.
fn checked_library(flags: &Flags) -> Result<Option<FrozenCrate>, Failure> {
    Ok(flags.path("checked-library").map(|dir| reference::load_checked_library(&dir)).transpose()?)
}

fn build_options<'a>(flags: &'a Flags, checked_library: Option<&'a FrozenCrate>) -> BuildOptions<'a> {
    BuildOptions { crate_name: flags.text("crate-name").unwrap_or(DEFAULT_EVALUATOR_CRATE_NAME), checked_library }
}

/// `--name value` pairs, each name at most once and accepted by the subcommand.
struct Flags(BTreeMap<String, String>);

impl Flags {
    fn parse(words: &[&str], accepted: &[&str]) -> Result<Self, Failure> {
        let mut flags = BTreeMap::new();
        let mut words = words.iter();
        while let Some(word) = words.next() {
            let name = word.strip_prefix("--").ok_or_else(|| Failure::Usage(format!("unexpected argument {word}")))?;
            if !accepted.contains(&name) {
                return Err(Failure::Usage(format!("unknown flag --{name}")));
            }
            let value = words.next().ok_or_else(|| Failure::Usage(format!("--{name} needs a value")))?;
            if flags.insert(name.to_owned(), (*value).to_owned()).is_some() {
                return Err(Failure::Usage(format!("--{name} is given twice")));
            }
        }
        Ok(Flags(flags))
    }

    fn text(&self, name: &str) -> Option<&str> {
        self.0.get(name).map(String::as_str)
    }

    /// A path flag, made absolute against the current directory.
    fn path(&self, name: &str) -> Option<PathBuf> {
        self.text(name).map(|p| std::path::absolute(p).unwrap_or_else(|_| PathBuf::from(p)))
    }

    fn required_path(&self, name: &str) -> Result<PathBuf, Failure> {
        self.path(name).ok_or_else(|| Failure::Usage(format!("--{name} is required")))
    }
}
