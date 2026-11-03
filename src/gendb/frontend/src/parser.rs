//! Host binding of the Python SQL parser (`frontend/parser`, package `gendb_sql_frontend`): runs it on SQL + schema DDL +
//! explicit dialect and decodes its document.
//!
//! **Deployment policy.** The parser runs from source; no GenDB binary embeds it. A `SqlParser` names the interpreter
//! and the parser directory explicitly:
//! - `SqlParser::pinned()`: the interpreter pinned in `parser/toolchain.json` and the parser directory of the source
//!   tree this crate was compiled from;
//! - `SqlParser::from_environment()`: the same, with `GENDB_SQL_FRONTEND_PYTHON` / `GENDB_SQL_FRONTEND_DIR` overriding
//!   either (the names `toolchain.json` records under `deployment`);
//! - `SqlParser::new(python, parser_dir)`: any explicit choice.
//!
//! After decoding, a statement with a constant subexpression that raises an SQL error is refused
//! (`crate::constants`); the returned document text is then that refusal document.
//!
//! The Rust decoder embeds the AST encoding schema at compile time while the parser reads `<parser_dir>/../ast/
//! ast_schema.json` at run time, so every constructor refuses a parser directory whose schema file differs from the
//! embedded one (no mixing of an old parser with a new decoder). The parser itself refuses an interpreter or sqlglot
//! version other than the pin (`toolchain_mismatch`), so documents only come from the pinned toolchain.

use crate::ast::{self, AstError, Translation, SCHEMA_JSON};
use crate::constants;
use crate::params::Placeholder;
use std::ffi::OsStr;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The parser's pinned toolchain and deployment record, embedded at compile time.
pub const TOOLCHAIN_JSON: &str = include_str!("../parser/toolchain.json");
/// Environment variable overriding the interpreter.
pub const PYTHON_ENV: &str = "GENDB_SQL_FRONTEND_PYTHON";
/// Environment variable overriding the parser directory.
pub const PARSER_DIR_ENV: &str = "GENDB_SQL_FRONTEND_DIR";

#[derive(Debug)]
pub enum ParserError {
    /// The toolchain record or the parser directory is unusable (missing pin, schema file differs, ...).
    Toolchain(String),
    /// The process could not run or exited abnormally (not a refusal).
    Process(String),
    /// The process printed a document that does not decode.
    Document(AstError),
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParserError::Toolchain(m) => write!(f, "frontend toolchain: {m}"),
            ParserError::Process(m) => write!(f, "frontend process: {m}"),
            ParserError::Document(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for ParserError {}

/// Where the parser runs: an interpreter and a parser directory whose AST schema is the compiled one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SqlParser {
    python: PathBuf,
    parser_dir: PathBuf,
}

impl SqlParser {
    /// Run `python -m gendb_sql_frontend` in `parser_dir`.
    pub fn new(python: PathBuf, parser_dir: PathBuf) -> Result<SqlParser, ParserError> {
        let schema_file = parser_dir.join("../ast/ast_schema.json");
        let runtime_schema = std::fs::read_to_string(&schema_file).map_err(|e| ParserError::Toolchain(format!("{}: {e}", schema_file.display())))?;
        if runtime_schema != SCHEMA_JSON {
            return Err(ParserError::Toolchain(format!("{} differs from the AST schema this binary was compiled with", schema_file.display())));
        }
        Ok(SqlParser { python, parser_dir })
    }

    /// The pinned interpreter and the parser directory of the compiled source tree.
    pub fn pinned() -> Result<SqlParser, ParserError> {
        SqlParser::new(pinned_python()?, default_parser_dir())
    }

    /// `pinned()`, with the interpreter and parser directory overridable by `PYTHON_ENV` / `PARSER_DIR_ENV`.
    pub fn from_environment() -> Result<SqlParser, ParserError> {
        let python = match std::env::var_os(PYTHON_ENV) {
            Some(p) => PathBuf::from(p),
            None => pinned_python()?,
        };
        let parser_dir = std::env::var_os(PARSER_DIR_ENV).map(PathBuf::from).unwrap_or_else(default_parser_dir);
        SqlParser::new(python, parser_dir)
    }

    pub fn python(&self) -> &Path {
        &self.python
    }

    pub fn parser_dir(&self) -> &Path {
        &self.parser_dir
    }

    /// Translate the statement in `sql_file` against `schema_file` (CREATE TABLE statements) in `dialect`, with typed
    /// placeholders `$n` declared by `placeholders` (`crate::params`; empty for a statement without placeholders).
    /// Returns the document text (for records) and its decoding (an AST or a named refusal).
    pub fn translate(&self, schema_file: &Path, sql_file: &Path, dialect: &str, placeholders: &[Placeholder]) -> Result<(String, Translation), ParserError> {
        let mut args = vec![flag("--schema"), absolute(schema_file)?.into_os_string(), flag("--sql"), absolute(sql_file)?.into_os_string(), flag("--dialect"), dialect.into()];
        if !placeholders.is_empty() {
            let declaration = serde_json::to_string(placeholders).map_err(|e| ParserError::Process(e.to_string()))?;
            args.extend([flag("--params"), declaration.into()]);
        }
        self.run(&args)
    }

    /// Translate the query labelled `label` (`-- Q6: ...` headers) of `query_file`.
    pub fn translate_labelled(&self, schema_file: &Path, query_file: &Path, label: &str, dialect: &str) -> Result<(String, Translation), ParserError> {
        let args = [
            flag("--schema"),
            absolute(schema_file)?.into_os_string(),
            flag("--query-file"),
            absolute(query_file)?.into_os_string(),
            flag("--label"),
            label.into(),
            flag("--dialect"),
            dialect.into(),
        ];
        self.run(&args)
    }

    fn run(&self, args: &[std::ffi::OsString]) -> Result<(String, Translation), ParserError> {
        let out = Command::new(&self.python)
            .current_dir(&self.parser_dir)
            .env("PYTHONDONTWRITEBYTECODE", "1")
            .args(["-m", "gendb_sql_frontend", "translate"])
            .args(args)
            .output()
            .map_err(|e| ParserError::Process(format!("{}: {e}", self.python.display())))?;
        // Exit 0 = translated, 1 = refused (both print a document); anything else is a process failure.
        if !matches!(out.status.code(), Some(0 | 1)) {
            return Err(ParserError::Process(format!("{}: {}", out.status, String::from_utf8_lossy(&out.stderr))));
        }
        let text = String::from_utf8(out.stdout).map_err(|e| ParserError::Process(e.to_string()))?;
        let doc = ast::decode(&text).map_err(ParserError::Document)?;
        if let Translation::Ok(statement) = &doc
            && let Some(refusal) = constants::refusal(statement)
        {
            return Ok((constants::refusal_document(statement, &refusal), Translation::Refused(refusal)));
        }
        Ok((text, doc))
    }
}

/// The parser directory of the source tree this crate was compiled from.
fn default_parser_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("parser")
}

fn pinned_python() -> Result<PathBuf, ParserError> {
    let record: serde_json::Value = serde_json::from_str(TOOLCHAIN_JSON).map_err(|e| ParserError::Toolchain(e.to_string()))?;
    record.get("python").and_then(serde_json::Value::as_str).map(PathBuf::from).ok_or_else(|| ParserError::Toolchain("python".into()))
}

fn flag(name: &str) -> std::ffi::OsString {
    OsStr::new(name).to_owned()
}

/// The parser runs in its own directory, so relative paths are resolved against the caller's working directory first.
fn absolute(p: &Path) -> Result<PathBuf, ParserError> {
    std::path::absolute(p).map_err(|e| ParserError::Process(format!("{}: {e}", p.display())))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The override variables are the ones the toolchain record names, and the compiled tree's parser directory holds
    /// the compiled schema.
    #[test]
    fn deployment_policy_matches_toolchain_record() {
        let record: serde_json::Value = serde_json::from_str(TOOLCHAIN_JSON).unwrap();
        assert_eq!(record["deployment"]["python_env"], PYTHON_ENV);
        assert_eq!(record["deployment"]["parser_dir_env"], PARSER_DIR_ENV);
        let parser = SqlParser::new(pinned_python().unwrap(), default_parser_dir()).unwrap();
        assert_eq!(parser.parser_dir(), default_parser_dir());
        let other = SqlParser::new(pinned_python().unwrap(), default_parser_dir().join("gendb_sql_frontend"));
        assert!(matches!(other, Err(ParserError::Toolchain(_))));
    }
}
