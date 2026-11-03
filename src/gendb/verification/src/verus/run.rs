//! One `rust_verify --no-cheating` invocation over a frozen crate, and the classification of its outcome.

use super::freeze::FrozenCrate;
use super::toolchain::VerusToolchain;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::BTreeMap;
use std::fmt;
use std::fs;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

/// rustc code generation settings passed through Verus (the author's compiler choice, validated here).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CodegenOptions {
    /// `-C opt-level`; values above 3 are clamped to 3.
    pub opt_level: u8,
    /// `-C target-cpu` (for example `native`); `None` = rustc default.
    pub target_cpu: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VerusOptions {
    /// Library name: `lib<crate_name>.so`. Lowercase ASCII, digits and `_`; not a standard or Verus crate name.
    pub crate_name: String,
    pub codegen: CodegenOptions,
    /// Verifier threads; `None` = Verus default (all hardware threads). Verification speed only.
    pub num_threads: Option<u32>,
}

impl VerusOptions {
    /// Where a compiling run in `out_dir` writes the library.
    pub fn library_path(&self, out_dir: &Path) -> PathBuf {
        out_dir.join(format!("lib{}.so", self.crate_name))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VerusMode {
    /// Verification (plus Verus's own erasure/lifetime pass); no library.
    Verify,
    /// Verification, then compilation of the same crate to a cdylib.
    VerifyAndCompile,
}

/// Exactly what was started: program, argv, the complete environment and the working directory.
#[derive(Clone, Debug, Serialize)]
pub struct VerusInvocation {
    pub program: PathBuf,
    pub args: Vec<String>,
    pub env: BTreeMap<String, String>,
    pub cwd: PathBuf,
}

/// `verification-results` of `--output-json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct VerificationSummary {
    pub success: bool,
    pub verified: u64,
    pub errors: u64,
    pub encountered_error: bool,
    pub encountered_vir_error: bool,
    pub is_verifying_entire_crate: bool,
}

/// One rustc/Verus diagnostic from `--error-format=json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Diagnostic {
    pub level: String,
    pub message: String,
    pub file: Option<String>,
    pub line: Option<u64>,
    pub column: Option<u64>,
    pub rendered: String,
}

impl Diagnostic {
    /// An error diagnostic other than rustc's closing "aborting due to N previous errors" summary.
    fn is_error(&self) -> bool {
        self.level == "error" && !self.message.starts_with("aborting due to")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum VerusOutcome {
    /// Verify mode: every function verified, zero errors.
    Verified,
    /// VerifyAndCompile mode: verified with zero errors and the library exists.
    Compiled,
    /// [`compile_unverified`] only: the crate compiled with `--no-verify` and the library exists. No proof obligation
    /// was checked; never evidence (admission refuses a build argv naming `--no-verify`).
    CompiledUnverified,
    /// Verus reported failed proof obligations (`errors > 0`).
    ProofFailure,
    /// Verus or rustc refused the source without a failed proof obligation (`--no-cheating`, unsupported feature,
    /// type/lifetime/mode error, zero verified functions).
    Rejected,
    /// The tool itself failed (could not start, signal, internal error, or output inconsistent with a success).
    ToolFailure,
}

impl VerusOutcome {
    /// The author-contract failure class of a non-success outcome; `None` for `Verified` and `Compiled`.
    pub fn failure_class(self) -> Option<&'static str> {
        match self {
            Self::Verified | Self::Compiled | Self::CompiledUnverified => None,
            Self::ProofFailure => Some("proof_failure"),
            Self::Rejected => Some("refusal"),
            Self::ToolFailure => Some("tool_failure"),
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct VerusRun {
    pub mode: VerusMode,
    pub invocation: VerusInvocation,
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub wall_ns: u64,
    /// Raw `--output-json` text; build records store it verbatim.
    pub stdout: String,
    pub stderr: String,
    pub verification: Option<VerificationSummary>,
    pub diagnostics: Vec<Diagnostic>,
    pub outcome: VerusOutcome,
    /// Why the outcome was chosen (one line).
    pub detail: String,
    /// Present only for `Compiled`.
    pub artifact: Option<PathBuf>,
}

impl VerusRun {
    /// Error diagnostics in rendered (human) form, without rustc's summary line.
    pub fn rendered_errors(&self) -> String {
        self.diagnostics.iter().filter(|d| d.is_error()).map(|d| d.rendered.as_str()).collect()
    }

    /// The run record (`run.json`) that build evidence is published from: outcome, argv, complete environment,
    /// program, exit status, wall time, library and the raw output.
    pub fn record(&self) -> serde_json::Value {
        json!({"outcome":self.outcome,"detail":self.detail,"verification":self.verification,
            "errors":self.rendered_errors(),"diagnostics":self.diagnostics,"argv":self.invocation.args,"environment":self.invocation.env,
            "program":self.invocation.program,"exit_code":self.exit_code,"signal":self.signal,"wall_ns":self.wall_ns,
            "artifact":self.artifact,"stdout":self.stdout,"stderr":self.stderr})
    }
}

/// A run that could not be started as requested. Nothing about the candidate's proofs is implied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunError {
    /// The options do not form a valid argv (crate name or target cpu).
    InvalidOptions { message: String },
    /// The module scope of a diagnostic run is empty or not a module path.
    InvalidModuleScope { message: String },
    /// The run's output directory exists already or cannot be created.
    OutputDirectory { path: PathBuf, message: String },
}

impl RunError {
    /// `missing_input` for a bad module scope (the request names it), `tool_failure` otherwise.
    pub fn failure_class(&self) -> &'static str {
        match self {
            Self::InvalidModuleScope { .. } => "missing_input",
            Self::InvalidOptions { .. } | Self::OutputDirectory { .. } => "tool_failure",
        }
    }
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidOptions { message } | Self::InvalidModuleScope { message } => f.write_str(message),
            Self::OutputDirectory { path, message } => write!(f, "{}: {message}", path.display()),
        }
    }
}

impl std::error::Error for RunError {}

/// Crate names that would shadow a standard or Verus crate.
const RESERVED_CRATE_NAMES: [&str; 7] = ["vstd", "verus_builtin", "verus_builtin_macros", "verus_state_machines_macros", "core", "std", "alloc"];

/// Exact argv of one whole-crate run. Both modes use the same arguments; compiling appends `--compile -o <library>`.
/// There is no option that skips or narrows verification here: [`verify_modules`] and [`compile_unverified`] append
/// theirs to this argv, and neither run is ever evidence.
pub fn verus_args(frozen: &FrozenCrate, options: &VerusOptions, mode: VerusMode, out_dir: &Path) -> Result<Vec<String>, RunError> {
    let name = &options.crate_name;
    let valid_name = name.chars().next().is_some_and(|c| c.is_ascii_lowercase())
        && name.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_');
    if !valid_name || RESERVED_CRATE_NAMES.contains(&name.as_str()) {
        return Err(RunError::InvalidOptions { message: format!("invalid crate name {name}") });
    }
    let mut args = vec![
        frozen.crate_root().display().to_string(),
        "--edition=2021".into(),
        "--crate-type=cdylib".into(),
        format!("--crate-name={name}"),
        "--no-cheating".into(),
        "--output-json".into(),
        "--error-format=json".into(),
        "-C".into(),
        format!("opt-level={}", options.codegen.opt_level.min(3)),
    ];
    if let Some(cpu) = &options.codegen.target_cpu {
        if cpu.is_empty() || !cpu.chars().all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_') {
            return Err(RunError::InvalidOptions { message: format!("invalid target cpu {cpu}") });
        }
        args.extend(["-C".into(), format!("target-cpu={cpu}")]);
    }
    if let Some(threads) = options.num_threads {
        args.extend(["--num-threads".into(), threads.max(1).to_string()]);
    }
    if mode == VerusMode::VerifyAndCompile {
        args.extend(["--compile".into(), "-o".into(), options.library_path(out_dir).display().to_string()]);
    }
    Ok(args)
}

/// One whole-crate Verus invocation over `frozen`: the evidence-grade run. `out_dir` must not exist; it becomes
/// the working directory, the temporary directory and the library location.
pub fn run_verus(toolchain: &VerusToolchain, frozen: &FrozenCrate, options: &VerusOptions, mode: VerusMode, out_dir: &Path) -> Result<VerusRun, RunError> {
    invoke(toolchain, frozen, options, mode, &[], out_dir)
}

/// Diagnostic verification of only the given crate modules (and their descendants): the argv of a whole-crate
/// verify plus one `--verify-module <m>` per module. Never evidence: the result does not verify the entire crate,
/// and admission refuses any stored argv carrying a partial-verification option. A successful scoped run is
/// reported as `Verified` with a detail naming the scope; every other outcome is classified as for [`run_verus`].
pub fn verify_modules(toolchain: &VerusToolchain, frozen: &FrozenCrate, options: &VerusOptions, modules: &[String], out_dir: &Path) -> Result<VerusRun, RunError> {
    if modules.is_empty() {
        return Err(RunError::InvalidModuleScope { message: "verify_modules needs at least one module".into() });
    }
    let mut scope_args = vec![];
    for module in modules {
        let valid = !module.is_empty()
            && module.split("::").all(|p| p.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_') && p.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'));
        if !valid {
            return Err(RunError::InvalidModuleScope { message: format!("invalid module path {module}") });
        }
        scope_args.extend(["--verify-module".to_string(), module.clone()]);
    }
    let mut run = invoke(toolchain, frozen, options, VerusMode::Verify, &scope_args, out_dir)?;
    // The whole-crate classification treats a partial report as a tool failure; here it is the expected success.
    if let (Some(0), None, Some(v)) = (run.exit_code, run.signal, run.verification.as_ref())
        && !v.is_verifying_entire_crate
        && v.success
        && v.errors == 0
        && v.verified > 0
        && !v.encountered_error
        && !v.encountered_vir_error
    {
        run.outcome = VerusOutcome::Verified;
        run.detail = format!("module-scoped {modules:?}: {} verified, 0 errors (NOT the entire crate; diagnostic only)", v.verified);
    }
    Ok(run)
}

/// The option of [`compile_unverified`]: rust_verify checks no proof obligation.
pub const NO_VERIFY: &str = "--no-verify";

/// Diagnostic compilation of the whole crate WITHOUT proof checking: the argv of a whole-crate verify-and-compile run
/// plus `--no-verify` (the same `--no-cheating`, crate, codegen and environment). Never evidence: nothing was verified,
/// and admission refuses any stored build argv naming `--no-verify` (`gendb_artifacts::verus::VERUS_PARTIAL_OPTIONS`).
/// Outcome: `CompiledUnverified` when rust_verify exits 0 and wrote the library; `Rejected` when it reports an error
/// (type, mode, lifetime or a `--no-cheating` refusal; the first error names it); `ToolFailure` otherwise (signal,
/// panic, no library). The verification summary, if Verus printed one, stays in the record verbatim.
pub fn compile_unverified(toolchain: &VerusToolchain, frozen: &FrozenCrate, options: &VerusOptions, out_dir: &Path) -> Result<VerusRun, RunError> {
    let mut run = invoke(toolchain, frozen, options, VerusMode::VerifyAndCompile, &[NO_VERIFY.to_string()], out_dir)?;
    let library = options.library_path(&run.invocation.cwd);
    let (outcome, detail) = classify_unverified(run.exit_code, run.signal, &run.diagnostics, &run.stderr, library.is_file());
    run.artifact = (outcome == VerusOutcome::CompiledUnverified).then_some(library);
    (run.outcome, run.detail) = (outcome, detail);
    Ok(run)
}

/// Outcome of a [`compile_unverified`] run (no verification result is required or trusted).
fn classify_unverified(exit_code: Option<i32>, signal: Option<i32>, diagnostics: &[Diagnostic], stderr: &str, library_written: bool) -> (VerusOutcome, String) {
    use VerusOutcome::*;
    if let Some(sig) = signal {
        return (ToolFailure, format!("rust_verify terminated by signal {sig}"));
    }
    if stderr.contains("Internal Verus Error") || stderr.contains("panicked at") {
        return (ToolFailure, "rust_verify internal error (panic); see stderr".into());
    }
    match (exit_code, diagnostics.iter().find(|d| d.is_error())) {
        (_, Some(first_error)) => (Rejected, format!("{} (exit {exit_code:?}, --no-verify)", first_error.message)),
        (Some(0), None) if library_written => (CompiledUnverified, "compiled with --no-verify: NO proof obligation was checked (diagnostic only)".into()),
        (Some(0), None) => (ToolFailure, "exit 0 but no library was written (--no-verify)".into()),
        (code, None) => (ToolFailure, format!("exit {code:?} without diagnostics (--no-verify)")),
    }
}

fn invoke(toolchain: &VerusToolchain, frozen: &FrozenCrate, options: &VerusOptions, mode: VerusMode, scope_args: &[String], out_dir: &Path) -> Result<VerusRun, RunError> {
    let directory_error = |message: String| RunError::OutputDirectory { path: out_dir.to_owned(), message };
    if out_dir.exists() {
        return Err(directory_error("already exists; each run uses a fresh output directory".into()));
    }
    fs::create_dir_all(out_dir).map_err(|e| directory_error(e.to_string()))?;
    let out_dir = out_dir.canonicalize().map_err(|e| directory_error(e.to_string()))?;
    let invocation = VerusInvocation {
        program: toolchain.rust_verify.clone(),
        args: verus_args(frozen, options, mode, &out_dir)?.into_iter().chain(scope_args.iter().cloned()).collect(),
        env: toolchain.environment(&out_dir),
        cwd: out_dir.clone(),
    };
    // The user's stop (`gendb_runtime::process_stop`): no run starts once the controller is stopping, and a run it
    // ends is never classified (the thread parks); `rust_verify` stays in the controller's process group and gets
    // SIGTERM when the controller dies.
    gendb_runtime::process_stop::park_if_stopping();
    let start = Instant::now();
    let mut command = Command::new(&invocation.program);
    command.args(&invocation.args).env_clear().envs(&invocation.env).current_dir(&invocation.cwd);
    gendb_runtime::process_stop::die_with_controller(&mut command, libc::SIGTERM);
    let output = command.output();
    gendb_runtime::process_stop::park_if_stopping();
    let wall_ns = start.elapsed().as_nanos() as u64;
    let output = match output {
        Ok(output) => output,
        Err(e) => {
            return Ok(VerusRun {
                mode, invocation, exit_code: None, signal: None, wall_ns, stdout: String::new(), stderr: String::new(),
                verification: None, diagnostics: vec![], outcome: VerusOutcome::ToolFailure,
                detail: format!("cannot start rust_verify: {e}"), artifact: None,
            })
        }
    };
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let verification = parse_verification(&stdout);
    let diagnostics = parse_diagnostics(&stderr);
    let library = options.library_path(&out_dir);
    let library_written = mode == VerusMode::VerifyAndCompile && library.is_file();
    let (exit_code, signal) = (output.status.code(), output.status.signal());
    let (outcome, detail) = classify(mode, exit_code, signal, verification.as_ref(), &diagnostics, &stderr, library_written);
    Ok(VerusRun {
        mode, invocation, exit_code, signal, wall_ns, stdout, stderr, verification, diagnostics,
        artifact: (outcome == VerusOutcome::Compiled).then_some(library), outcome, detail,
    })
}

/// Parses the `--output-json` object on stdout (absent on some early errors). Module-scoped runs
/// (`--verify-module`, `is-verifying-entire-crate: false`) omit `success`; only for them it is derived as no error
/// encountered and 0 errors. A whole-crate report without `success` stays malformed (no summary).
fn parse_verification(stdout: &str) -> Option<VerificationSummary> {
    let output: serde_json::Value = serde_json::from_str(stdout.trim()).ok()?;
    let mut results = output.get("verification-results")?.clone();
    let object = results.as_object_mut()?;
    if !object.contains_key("success") && object.get("is-verifying-entire-crate").and_then(|x| x.as_bool()) == Some(false) {
        let flag = |k: &str| object.get(k).and_then(|x| x.as_bool());
        let derived = !flag("encountered-error")? && !flag("encountered-vir-error")? && object.get("errors")?.as_u64()? == 0;
        object.insert("success".into(), serde_json::Value::Bool(derived));
    }
    serde_json::from_value(results).ok()
}

/// Parses `--error-format=json` diagnostics; other stderr lines are ignored here (they stay in `VerusRun::stderr`).
fn parse_diagnostics(stderr: &str) -> Vec<Diagnostic> {
    stderr
        .lines()
        .filter(|l| l.starts_with('{'))
        .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .filter(|v| v["$message_type"] == "diagnostic")
        .map(|v| {
            let primary = v["spans"].as_array().and_then(|s| s.iter().find(|s| s["is_primary"] == true).or(s.first())).cloned();
            Diagnostic {
                level: v["level"].as_str().unwrap_or_default().into(),
                message: v["message"].as_str().unwrap_or_default().into(),
                file: primary.as_ref().and_then(|s| s["file_name"].as_str().map(String::from)),
                line: primary.as_ref().and_then(|s| s["line_start"].as_u64()),
                column: primary.as_ref().and_then(|s| s["column_start"].as_u64()),
                rendered: v["rendered"].as_str().unwrap_or_default().into(),
            }
        })
        .collect()
}

/// Outcome of a whole-crate run and a one-line reason. A success needs exit 0, a successful report over the entire
/// crate with at least one verified function and zero errors, and, when compiling, the library on disk.
fn classify(
    mode: VerusMode,
    exit_code: Option<i32>,
    signal: Option<i32>,
    verification: Option<&VerificationSummary>,
    diagnostics: &[Diagnostic],
    stderr: &str,
    library_written: bool,
) -> (VerusOutcome, String) {
    use VerusOutcome::*;
    if let Some(sig) = signal {
        return (ToolFailure, format!("rust_verify terminated by signal {sig}"));
    }
    if stderr.contains("Internal Verus Error") || stderr.contains("panicked at") {
        return (ToolFailure, "rust_verify internal error (panic); see stderr".into());
    }
    match exit_code {
        Some(0) => match verification {
            None => (ToolFailure, "exit 0 without a verification result".into()),
            Some(v) if !v.is_verifying_entire_crate => (ToolFailure, "Verus did not verify the entire crate".into()),
            Some(v) if !v.success || v.errors > 0 => (ToolFailure, "exit 0 with an unsuccessful verification result".into()),
            Some(v) if v.verified == 0 => (Rejected, "zero functions verified".into()),
            Some(v) => match mode {
                VerusMode::Verify => (Verified, format!("{} verified, 0 errors", v.verified)),
                VerusMode::VerifyAndCompile if library_written => (Compiled, format!("{} verified, 0 errors, library written", v.verified)),
                VerusMode::VerifyAndCompile => (ToolFailure, "verified but no library was written".into()),
            },
        },
        Some(code) => match (verification, diagnostics.iter().find(|d| d.is_error())) {
            (Some(v), _) if v.errors > 0 => (ProofFailure, format!("{} verification errors (exit {code})", v.errors)),
            (_, Some(first_error)) => (Rejected, format!("{} (exit {code})", first_error.message)),
            _ => (ToolFailure, format!("exit {code} without diagnostics")),
        },
        None => (ToolFailure, "no exit status".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn diag(level: &str, message: &str) -> Diagnostic {
        Diagnostic { level: level.into(), message: message.into(), file: None, line: None, column: None, rendered: String::new() }
    }
    fn summary(success: bool, verified: u64, errors: u64) -> VerificationSummary {
        VerificationSummary { success, verified, errors, encountered_error: !success, encountered_vir_error: false, is_verifying_entire_crate: true }
    }

    #[test]
    fn classification() {
        use VerusMode::*;
        use VerusOutcome::*;
        let ok = summary(true, 3, 0);
        assert_eq!(classify(VerifyAndCompile, Some(0), None, Some(&ok), &[], "", true).0, Compiled);
        assert_eq!(classify(VerifyAndCompile, Some(0), None, Some(&ok), &[], "", false).0, ToolFailure);
        assert_eq!(classify(Verify, Some(0), None, Some(&ok), &[], "", false).0, Verified);
        assert_eq!(classify(Verify, Some(0), None, Some(&summary(true, 0, 0)), &[], "", false).0, Rejected);
        assert_eq!(classify(Verify, Some(0), None, None, &[], "", false).0, ToolFailure);
        let failed = summary(false, 2, 1);
        assert_eq!(classify(Verify, Some(1), None, Some(&failed), &[diag("error", "postcondition not satisfied")], "", false).0, ProofFailure);
        let refused = [diag("error", "assume/admit not allowed with --no-cheating"), diag("error", "aborting due to 1 previous error")];
        assert_eq!(classify(Verify, Some(1), None, None, &refused, "", false), (Rejected, "assume/admit not allowed with --no-cheating (exit 1)".into()));
        assert_eq!(classify(Verify, Some(1), None, None, &[diag("error", "aborting due to 1 previous error")], "", false).0, ToolFailure);
        assert_eq!(classify(Verify, Some(101), None, None, &refused, "thread 'rustc' panicked at x", false).0, ToolFailure);
        assert_eq!(classify(Verify, None, Some(9), None, &[], "", false).0, ToolFailure);
        assert_eq!([Verified, Compiled, ProofFailure, Rejected, ToolFailure].map(VerusOutcome::failure_class), [None, None, Some("proof_failure"), Some("refusal"), Some("tool_failure")]);
    }

    #[test]
    fn unverified_compilation_is_classified_without_a_verification_result() {
        use VerusOutcome::*;
        assert_eq!(classify_unverified(Some(0), None, &[], "", true).0, CompiledUnverified);
        assert_eq!(CompiledUnverified.failure_class(), None);
        assert_eq!(classify_unverified(Some(0), None, &[], "", false).0, ToolFailure);
        let type_error = [diag("error", "mismatched types"), diag("error", "aborting due to 1 previous error")];
        assert_eq!(classify_unverified(Some(1), None, &type_error, "", false), (Rejected, "mismatched types (exit Some(1), --no-verify)".into()));
        assert_eq!(classify_unverified(Some(1), None, &type_error[1..], "", false).0, ToolFailure);
        assert_eq!(classify_unverified(None, Some(6), &[], "", false).0, ToolFailure);
        assert_eq!(classify_unverified(Some(101), None, &type_error, "thread 'rustc' panicked at x", false).0, ToolFailure);
    }

    #[test]
    fn scoped_output_without_success_parses() {
        let failed = r#"{"func-details":{},"verification-results":{"encountered-error":true,"encountered-vir-error":false,"verified":34,"errors":10,"is-verifying-entire-crate":false},"verus":{}}"#;
        let v = parse_verification(failed).unwrap();
        assert_eq!((v.success, v.verified, v.errors, v.is_verifying_entire_crate), (false, 34, 10, false));
        assert_eq!(classify(VerusMode::Verify, Some(1), None, Some(&v), &[], "", false).0, VerusOutcome::ProofFailure);
        let ok = r#"{"func-details":{},"verification-results":{"encountered-error":false,"encountered-vir-error":false,"verified":53,"errors":0,"is-verifying-entire-crate":false},"verus":{}}"#;
        let v = parse_verification(ok).unwrap();
        assert!(v.success && v.errors == 0 && !v.is_verifying_entire_crate);
        assert_eq!(parse_verification(&ok.replace("\"is-verifying-entire-crate\":false", "\"is-verifying-entire-crate\":true")), None);
    }

    #[test]
    fn parses_output_json_and_diagnostics() {
        let stdout = r#"{"func-details":{},"verification-results":{"encountered-error":false,"encountered-vir-error":false,"success":true,"verified":5,"errors":0,"is-verifying-entire-crate":true},"verus":{}}"#;
        assert_eq!(parse_verification(stdout), Some(summary(true, 5, 0)));
        assert_eq!(parse_verification(""), None);
        let stderr = "note: plain line\n{\"$message_type\":\"diagnostic\",\"message\":\"postcondition not satisfied\",\"level\":\"error\",\"spans\":[{\"file_name\":\"src/agent/mod.rs\",\"line_start\":2,\"column_start\":63,\"is_primary\":true}],\"rendered\":\"error: x\"}\n";
        let d = parse_diagnostics(stderr);
        assert_eq!(d.len(), 1);
        assert_eq!((d[0].file.as_deref(), d[0].line, d[0].column), (Some("src/agent/mod.rs"), Some(2), Some(63)));
    }

    #[test]
    fn pin_parses_and_args_are_fixed() {
        let pin = super::super::verus_pin();
        assert_eq!(pin.verus.commit, "671956ec527d3b7164779f767bdbfe769bedce6c");
        assert_eq!(pin.rust.toolchain, "1.98.1-x86_64-unknown-linux-gnu");
        let frozen = FrozenCrate::from_recorded("/f".into(), vec![], vec![]);
        let mut o = VerusOptions { crate_name: "q".into(), codegen: CodegenOptions { opt_level: 3, target_cpu: Some("native".into()) }, num_threads: None };
        let v = verus_args(&frozen, &o, VerusMode::Verify, Path::new("/o")).unwrap();
        let c = verus_args(&frozen, &o, VerusMode::VerifyAndCompile, Path::new("/o")).unwrap();
        assert_eq!(v[0], "/f/src/lib.rs");
        assert_eq!(&c[..v.len()], &v[..]);
        assert_eq!(&c[v.len()..], &["--compile".to_string(), "-o".into(), "/o/libq.so".into()]);
        o.crate_name = "vstd".into();
        assert!(matches!(verus_args(&frozen, &o, VerusMode::Verify, Path::new("/o")), Err(RunError::InvalidOptions { .. })));
    }

    /// The argv of a saved, admitted Q6 build (its `local-jobs/0001-c1-compile/verus/run.json`):
    /// the same options must still produce exactly that argv, so build evidence stays comparable.
    #[test]
    fn saved_q6_build_argv_is_reproduced() {
        let base = "/path/to/run/queries/query-0000/calls/0001/local-jobs/0001-c1-compile";
        let frozen = FrozenCrate::from_recorded(format!("{base}/frozen/crate").into(), vec!["mod.rs".into()], vec!["lib.rs".into()]);
        let options = VerusOptions { crate_name: "gendb_query".into(), codegen: CodegenOptions { opt_level: 3, target_cpu: None }, num_threads: Some(8) };
        let args = verus_args(&frozen, &options, VerusMode::VerifyAndCompile, Path::new(&format!("{base}/verus"))).unwrap();
        let saved = [
            &format!("{base}/frozen/crate/src/lib.rs"), "--edition=2021", "--crate-type=cdylib", "--crate-name=gendb_query", "--no-cheating",
            "--output-json", "--error-format=json", "-C", "opt-level=3", "--num-threads", "8", "--compile", "-o", &format!("{base}/verus/libgendb_query.so"),
        ];
        assert_eq!(args, saved);
    }
}
