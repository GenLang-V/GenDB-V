//! The SQLSpec reference evaluator as a toolchain workflow: check the whole SQLSpec library, build (freeze, verify,
//! compile) the evaluator crate of one translated statement, run it on fixture databases, and compare its answers
//! with recorded PostgreSQL evidence. The crate sources, echo grammar, codecs and fixture format come from
//! `gendb_sqlspec`; this module adds the pinned Verus runs and the records.
//!
//! Commands (each writes its records once; an output path must not exist):
//! - [`check_library`]: every library module (`spec`, `exec`, `bridge`, `link`, `pins`) in one `--no-cheating` run;
//! - [`translate`]: SQL + schema DDL -> `ast.json` with the Python parser;
//! - [`build_ast_file`] / [`build_evaluator`]: one `VerifyAndCompile` run over the frozen evaluator crate, then the
//!   echo comparison (translation validation) and, given a checked library snapshot, a byte comparison of the
//!   copied library files;
//! - [`run_evaluator`]: a built evaluator on one fixture database;
//! - [`evaluate`]: translate + build + run;
//! - [`diff_fixture`]: every case of a reference fixture, each run in a child process, compared by the PostgreSQL
//!   harness with evidence recorded earlier (differential testing, not a proof).
//!
//! What a successful evaluation shows: the rows or SQL error equal `denote_top(db, query_spec())` for the fixture
//! database under the statement's schema (checked by Verus). Trusted: the pinned toolchain, the `spec`
//! definitions, the SQL -> AST translation (the echo shows only that the compiled AST is the translated one), the
//! fixture input codec, the wire codec, the evaluator shim and the loader.

mod evaluator_build;
mod postgres;
mod statement;

pub use evaluator_build::{
    build_evaluator, check_library, evaluator_options, load_checked_library, BuildOptions, BuildStatus, EvaluatorBuild, LibraryCheck,
    DEFAULT_EVALUATOR_CRATE_NAME, LIBRARY_CRATE_NAME,
};
pub use postgres::{crate_name_for, diff_fixture, FixtureDiff, RunProcess};
pub use statement::{build_ast_file, evaluate, run_evaluator, translate, Evaluation, StatementSource, Translated};

use crate::verus::{FreezeError, RunError, ToolchainError};
use gendb_frontend::ast::AstError;
use gendb_frontend::parser::ParserError;
use gendb_sqlspec::evaluator::EvaluatorError;
use gendb_sqlspec::fixtures::FixtureError;
use gendb_sqlspec::pg_text::NonUtf8Text;
use std::fmt;
use std::path::{Path, PathBuf};

/// A reference workflow that could not complete. Recorded non-success outcomes (a refused statement, a failed
/// proof, an echo mismatch) are not errors; they are statuses in the records.
#[derive(Debug)]
pub enum ReferenceError {
    Io { path: PathBuf, message: String },
    /// Records are written once: the output path exists already.
    OutputExists(PathBuf),
    /// A record or AST file is malformed or not usable for the requested step.
    Record { path: PathBuf, message: String },
    Toolchain(ToolchainError),
    /// A framework file could not be frozen (a refused framework file is a recorded `Rejected` build instead).
    Freeze(FreezeError),
    Run(RunError),
    Parser(ParserError),
    Ast(AstError),
    Evaluator(EvaluatorError),
    Fixture(FixtureError),
    Output(NonUtf8Text),
    /// The PostgreSQL harness or a child evaluation process could not run.
    Process { program: PathBuf, message: String },
}

impl ReferenceError {
    /// The author-contract failure class: every reference failure is a tool failure, never the author's.
    pub fn failure_class(&self) -> &'static str {
        "tool_failure"
    }
}

impl fmt::Display for ReferenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, message } => write!(f, "{}: {message}", path.display()),
            Self::OutputExists(path) => write!(f, "{} already exists; records are written once", path.display()),
            Self::Record { path, message } => write!(f, "{}: {message}", path.display()),
            Self::Toolchain(e) => e.fmt(f),
            Self::Freeze(e) => e.fmt(f),
            Self::Run(e) => e.fmt(f),
            Self::Parser(e) => e.fmt(f),
            Self::Ast(e) => e.fmt(f),
            Self::Evaluator(e) => e.fmt(f),
            Self::Fixture(e) => e.fmt(f),
            Self::Output(e) => e.fmt(f),
            Self::Process { program, message } => write!(f, "{}: {message}", program.display()),
        }
    }
}

impl std::error::Error for ReferenceError {}

macro_rules! from_error {
    ($($source:ty => $variant:ident),* $(,)?) => {
        $(impl From<$source> for ReferenceError {
            fn from(e: $source) -> Self {
                Self::$variant(e)
            }
        })*
    };
}

from_error!(
    ToolchainError => Toolchain,
    FreezeError => Freeze,
    RunError => Run,
    ParserError => Parser,
    AstError => Ast,
    EvaluatorError => Evaluator,
    FixtureError => Fixture,
    NonUtf8Text => Output,
);

fn io_error(path: &Path) -> impl FnOnce(std::io::Error) -> ReferenceError + '_ {
    move |e| ReferenceError::Io { path: path.to_path_buf(), message: e.to_string() }
}

/// Create the output directory of a command; it must not exist.
fn create_output_dir(dir: &Path) -> Result<(), ReferenceError> {
    if dir.exists() {
        return Err(ReferenceError::OutputExists(dir.to_path_buf()));
    }
    std::fs::create_dir_all(dir).map_err(io_error(dir))
}

fn read_text(path: &Path) -> Result<String, ReferenceError> {
    std::fs::read_to_string(path).map_err(io_error(path))
}

fn read_json(path: &Path) -> Result<serde_json::Value, ReferenceError> {
    serde_json::from_str(&read_text(path)?).map_err(|e| ReferenceError::Record { path: path.to_path_buf(), message: e.to_string() })
}

fn write_text(path: &Path, text: &str) -> Result<(), ReferenceError> {
    std::fs::write(path, text).map_err(io_error(path))
}

/// Pretty JSON with a final newline.
fn write_json(path: &Path, value: &serde_json::Value) -> Result<(), ReferenceError> {
    write_text(path, &(serde_json::to_string_pretty(value).expect("JSON values serialize") + "\n"))
}
