//! Read-only inspection of the configured Claude Code executable: its `--version` and `--help` output, retained as
//! evidence, and a check that it offers every flag a launch uses. No inference request is dispatched.

use super::launch::LAUNCH_FLAGS;
use crate::controller::records;
use serde_json::{Value, json};
use std::fmt;
use std::fs::{self, OpenOptions};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// Why the executable cannot serve as the author transport. Every refusal names its evidence directory.
#[derive(Debug)]
pub enum InspectionError {
    /// The evidence directory or one of its records could not be written or read.
    Evidence { path: PathBuf, detail: String },
    /// The executable could not be started.
    Unavailable(std::io::Error),
    /// `--version` or `--help` exited unsuccessfully (its output is not trusted even when it looks complete).
    CommandFailed { command: &'static str, status: String, evidence: PathBuf },
    /// The help lacks a flag the launch uses.
    MissingFlag { flag: &'static str, evidence: PathBuf },
}

impl fmt::Display for InspectionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InspectionError::Evidence { path, detail } => write!(f, "Claude inspection evidence {}: {detail}", path.display()),
            InspectionError::Unavailable(error) => write!(f, "Claude executable unavailable: {error}"),
            InspectionError::CommandFailed { command, status, evidence } => {
                write!(f, "Claude {command} inspection failed ({status}); evidence {}", evidence.display())
            }
            InspectionError::MissingFlag { flag, evidence } => {
                write!(f, "Claude transport lacks {flag}; evidence {}", evidence.display())
            }
        }
    }
}

impl std::error::Error for InspectionError {}

fn evidence_error(path: &Path) -> impl Fn(std::io::Error) -> InspectionError + '_ {
    move |error| InspectionError::Evidence { path: path.to_path_buf(), detail: error.to_string() }
}

/// The inspected version text and the evidence record (`capability_inspection` of every `invocation.json`).
pub(super) struct Inspection {
    pub version: String,
    pub record: Value,
}

/// Run `--version` and `--help` into regular files in a fresh `claude-inspection-<pid>-<ns>` directory under
/// `evidence_parent`. Claude Code 2.1.270 can exit before flushing its help to a pipe (a successful exit with only
/// 8192 bytes); regular files keep the complete output.
pub(super) fn inspect(executable: &Path, evidence_parent: &Path) -> Result<Inspection, InspectionError> {
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default().as_nanos();
    let directory = evidence_parent.join(format!("claude-inspection-{}-{nonce}", std::process::id()));
    fs::create_dir_all(&directory).map_err(evidence_error(&directory))?;
    let directory = directory.canonicalize().map_err(evidence_error(&directory))?;
    let (version, version_record) = run_inspection_command(executable, &directory, "version")?;
    let (help, help_record) = run_inspection_command(executable, &directory, "help")?;
    if let Some(flag) = LAUNCH_FLAGS.into_iter().find(|flag| !help.contains(flag)) {
        return Err(InspectionError::MissingFlag { flag, evidence: directory });
    }
    Ok(Inspection { version: version.trim().into(), record: json!({"version":version_record,"help":help_record}) })
}

/// `<executable> --<command>` with stdout/stderr in `<command>.stdout.txt`/`.stderr.txt` and `<command>.json`.
fn run_inspection_command(
    executable: &Path,
    directory: &Path,
    command: &'static str,
) -> Result<(String, Value), InspectionError> {
    let stdout = directory.join(format!("{command}.stdout.txt"));
    let stderr = directory.join(format!("{command}.stderr.txt"));
    let output_file = |path: &Path| OpenOptions::new().write(true).create_new(true).open(path).map_err(evidence_error(path));
    gendb_runtime::process_stop::park_if_stopping();
    let status = Command::new(executable).arg(format!("--{command}")).stdin(Stdio::null()).stdout(output_file(&stdout)?).stderr(output_file(&stderr)?).status();
    // An inspection ended by the user's stop is never read (`gendb_runtime::process_stop`).
    gendb_runtime::process_stop::park_if_stopping();
    let status = status.map_err(InspectionError::Unavailable)?;
    let text = fs::read_to_string(&stdout).map_err(evidence_error(&stdout))?;
    let record = json!({"argv":[executable,format!("--{command}")],"exit_code":status.code(),
        "stdout":stdout,"stderr":stderr,"stdout_bytes":text.len()});
    let record_path = directory.join(format!("{command}.json"));
    records::write_json_atomic(&record_path, &record)
        .map_err(|error| InspectionError::Evidence { path: record_path, detail: error.detail })?;
    if !status.success() {
        return Err(InspectionError::CommandFailed { command, status: status.to_string(), evidence: directory.to_path_buf() });
    }
    Ok((text, record))
}
