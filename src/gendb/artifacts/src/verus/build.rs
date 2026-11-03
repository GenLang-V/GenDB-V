//! Build records: what one Verus invocation verified and compiled, and whether that evidence is admissible.

use super::{RecordError, read_record, rejected};
use crate::content_id::ContentId;
use crate::object_store::ObjectStore;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

pub const VERUS_TCB_KIND: &str = "gendb.verus.tcb.v1";
pub const VERUS_BUILD_KIND: &str = "gendb.verus.build.v1";
pub const VERUS_IMPLEMENTATION_KIND: &str = "gendb.verus.implementation.v1";

/// Options of the pinned Verus release (`rust_verify/src/config.rs`) that restrict or skip verification or checks,
/// or replace the pinned vstd. The toolchain wrapper never passes them; admission refuses a stored argv naming any.
pub const VERUS_PARTIAL_OPTIONS: &[&str] = &[
    "--no-verify", "--verify-only-module", "--verify-module", "--verify-function", "--verify-root",
    "--no-lifetime", "--no-erasure-check", "--no-trait-conflicts", "--no-external-by-default",
    "--no-vstd", "--is-vstd", "--is-core", "--is-stdlib-outside-of-core", "--import", "--export",
];

/// Flags an admissible build invocation must pass: full checking, compilation, machine-readable results.
const REQUIRED_BUILD_FLAGS: [&str; 3] = ["--no-cheating", "--compile", "--output-json"];

/// One trusted component of the claim (its stated reason for being trusted).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusTrustedItemV1 {
    pub id: String,
    pub item: String,
    pub identity: String,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusTcbV1 {
    pub items: Vec<VerusTrustedItemV1>,
    /// The toolchain refusal list exactly as enforced when the build ran.
    pub refusal_rules: serde_json::Value,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VerusBuildPurposeV1 {
    Candidate,
    /// Framework ABI fixture whose entry is not a checked query theorem. Never admitted.
    AbiFixtureUnproved,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VerusSourceOwnerV1 {
    Framework,
    Agent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusSourceFileV1 {
    /// Relative to the frozen crate's `src/`.
    pub path: String,
    pub owner: VerusSourceOwnerV1,
    pub blob: ContentId,
    pub bytes: u64,
}

/// One Verus invocation that verified and then compiled one frozen crate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusBuildV1 {
    pub purpose: VerusBuildPurposeV1,
    /// `rust_verify --version --output-json` of the pinned installation, as checked.
    pub provider_identity: String,
    pub argv: Vec<String>,
    pub environment: BTreeMap<String, String>,
    pub exit_code: Option<i32>,
    pub frozen_directory: PathBuf,
    /// Every source of the frozen crate, stored as it was verified and compiled.
    pub sources: Vec<VerusSourceFileV1>,
    /// Raw stdout of the invocation (`--output-json`).
    pub verus_output: ContentId,
    /// The compiled `cdylib`.
    pub library: ContentId,
    pub library_bytes: u64,
    pub wall_ns: u64,
    pub tcb: ContentId,
}

impl VerusBuildV1 {
    /// The stored bytes of framework file `path` (relative to `src/`).
    pub fn framework_bytes(&self, store: &ObjectStore, path: &str) -> Result<Vec<u8>, RecordError> {
        let source = self
            .sources
            .iter()
            .find(|s| s.path == path && s.owner == VerusSourceOwnerV1::Framework)
            .ok_or_else(|| rejected(format!("build lacks framework file {path}")))?;
        Ok(store.read_blob(source.blob, Some(source.bytes))?)
    }

    /// The stored text of framework file `path` (relative to `src/`).
    pub fn framework_text(&self, store: &ObjectStore, path: &str) -> Result<String, RecordError> {
        String::from_utf8(self.framework_bytes(store, path)?)
            .map_err(|error| rejected(format!("framework file {path} is not UTF-8: {error}")))
    }

    /// Every stored source of the build, framework and author, as `(path, owner, text)` in record order: the crate
    /// exactly as it was verified and compiled (for composition checks over two builds).
    pub fn source_texts(&self, store: &ObjectStore) -> Result<Vec<(String, VerusSourceOwnerV1, String)>, RecordError> {
        self.sources
            .iter()
            .map(|source| {
                let bytes = store.read_blob(source.blob, Some(source.bytes))?;
                let text = String::from_utf8(bytes).map_err(|error| rejected(format!("source {} is not UTF-8: {error}", source.path)))?;
                Ok((source.path.clone(), source.owner, text))
            })
            .collect()
    }

    /// The check configuration of the build ([`VerusCheckConfigurationV1::of_build`]).
    pub fn check_configuration(&self) -> Result<VerusCheckConfigurationV1, RecordError> {
        VerusCheckConfigurationV1::of_build(self)
    }
}

/// What decides the meaning of a crate's text when Verus checks it, beyond the text: the pinned toolchain (its
/// `rust_verify --version` identity, which names Verus, vstd and rustc), the verification-relevant options and the
/// toolchain environment (vstd kind, Z3, rustc library path, `PATH`). Two builds whose shared files denote the same
/// propositions must have equal configurations.
///
/// Derived from the stored argv, whose only admissible shape is the one `gendb_verification::verus::verus_args`
/// writes: the crate root, `--edition=2021`, `--crate-type=cdylib`, `--crate-name=<name>`, `--no-cheating`,
/// `--output-json`, `--error-format=json`, `-C opt-level=<n>`, optionally `-C target-cpu=<cpu>` and `--num-threads <n>`,
/// and `--compile -o <library>`. Any other argument (for example `--cfg`, `--extern`, `-Z`, `--edition=2018`) refuses the
/// build. Excluded from the comparison, with the reason: the crate root, library and temporary paths and the crate
/// name (locations and the per-kind name; checked text cannot observe them: author code may invoke only the audited
/// macros of the refusal list's allowlist, which excludes `module_path!`, `file!`, `env!` and `cfg!`, and framework text
/// uses none); `--num-threads` (verifier parallelism); and the codegen options `opt-level`/`target-cpu`, which act after
/// verification on the ghost-erased crate and cannot reach checked text because `cfg`/`cfg_attr` attributes and `cfg!`
/// are refused in author code and absent from framework text (target features are visible to source only through
/// `cfg`). The target triple is the host's for both builds (no `--target` is admitted).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusCheckConfigurationV1 {
    pub provider_identity: String,
    /// The verification-relevant options in argv order.
    pub options: Vec<String>,
    /// The build environment without `TMPDIR` (a per-run scratch path).
    pub environment: BTreeMap<String, String>,
}

impl VerusCheckConfigurationV1 {
    /// The configuration of `build`, refusing any argument outside the admissible argv shape.
    pub fn of_build(build: &VerusBuildV1) -> Result<Self, RecordError> {
        let mut options = Vec::new();
        let mut args = build.argv.iter().skip(1);
        while let Some(arg) = args.next() {
            let arg = arg.as_str();
            match arg {
                "--edition=2021" | "--crate-type=cdylib" | "--no-cheating" | "--output-json" | "--error-format=json" | "--compile" => {
                    options.push(arg.to_string())
                }
                "-C" => match args.next().map(String::as_str) {
                    Some(value) if value.starts_with("opt-level=") || value.starts_with("target-cpu=") => {}
                    other => return Err(RecordError::BuildEvidence(format!("verus build uses an unsupported codegen option -C {other:?}"))),
                },
                "--num-threads" | "-o" if args.next().is_some() => {}
                _ if arg.starts_with("--crate-name=") => {}
                _ => return Err(RecordError::BuildEvidence(format!("verus build uses an unsupported option {arg}"))),
            }
        }
        let environment = build.environment.iter().filter(|(key, _)| *key != "TMPDIR").map(|(k, v)| (k.clone(), v.clone())).collect();
        Ok(Self { provider_identity: build.provider_identity.clone(), options, environment })
    }
}

/// A verified module usable by later authors (reused copies are re-verified in their crate).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusImplementationV1 {
    pub build: ContentId,
    /// Module inside the frozen crate: `agent/<file> (<role>)` or a framework module such as `gendb_entry`.
    pub module: String,
    /// Operation names a checked contract bridge established for this module.
    pub operations: Vec<String>,
    /// Exported exec items with the `requires`/`ensures` text Verus checked.
    pub items: Vec<VerusItemV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusItemV1 {
    pub path: String,
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
}

/// What the caller's toolchain run produced, for [`publish_build`].
pub struct VerusBuildInput<'a> {
    pub purpose: VerusBuildPurposeV1,
    pub provider_identity: String,
    pub argv: Vec<String>,
    pub environment: BTreeMap<String, String>,
    pub exit_code: Option<i32>,
    pub stdout: &'a str,
    pub frozen_directory: &'a Path,
    /// Paths relative to `<frozen>/src/`.
    pub sources: Vec<(String, VerusSourceOwnerV1)>,
    pub library_path: &'a Path,
    pub wall_ns: u64,
    pub tcb: ContentId,
}

/// Store the frozen sources, the raw Verus output and the library, then the build record. This records what
/// happened; [`check_build_evidence`] decides whether it counts.
pub fn publish_build(store: &ObjectStore, input: VerusBuildInput<'_>) -> Result<ContentId, RecordError> {
    read_record::<VerusTcbV1>(store, input.tcb, VERUS_TCB_KIND)?;
    let mut sources = Vec::with_capacity(input.sources.len());
    for (path, owner) in input.sources {
        let file = input.frozen_directory.join("src").join(&path);
        let bytes = std::fs::read(&file).map_err(|error| RecordError::io(&file, error))?;
        sources.push(VerusSourceFileV1 { blob: store.put_blob(&bytes)?, bytes: bytes.len() as u64, path, owner });
    }
    let library = std::fs::read(input.library_path).map_err(|error| RecordError::io(input.library_path, error))?;
    let record = VerusBuildV1 {
        purpose: input.purpose,
        provider_identity: input.provider_identity,
        argv: input.argv,
        environment: input.environment,
        exit_code: input.exit_code,
        frozen_directory: input.frozen_directory.to_owned(),
        sources,
        verus_output: store.put_blob(input.stdout.as_bytes())?,
        library_bytes: library.len() as u64,
        library: store.put_blob(&library)?,
        wall_ns: input.wall_ns,
        tcb: input.tcb,
    };
    Ok(store.put(1, VERUS_BUILD_KIND, &record)?)
}

/// Check the stored evidence of one build: a candidate build; one invocation with `--no-cheating`, `--compile` and
/// `--output-json`, no partial-verification option, exit 0; the stored raw output reporting success with zero errors,
/// a non-zero verified count, the entire crate verified and no encountered (VIR) error; the library stored whole.
pub fn check_build_evidence(store: &ObjectStore, id: ContentId) -> Result<VerusBuildV1, RecordError> {
    let build: VerusBuildV1 = read_record(store, id, VERUS_BUILD_KIND)?;
    if build.purpose != VerusBuildPurposeV1::Candidate {
        return Err(RecordError::BuildEvidence("an unproved ABI fixture build is never admitted".into()));
    }
    for flag in REQUIRED_BUILD_FLAGS {
        if !build.argv.iter().any(|a| a == flag) {
            return Err(RecordError::BuildEvidence(format!("verus build lacks {flag}")));
        }
    }
    for arg in &build.argv {
        let name = arg.split('=').next().unwrap_or(arg);
        if VERUS_PARTIAL_OPTIONS.contains(&name) {
            return Err(RecordError::BuildEvidence(format!("verus build used partial-verification option {name}")));
        }
    }
    if build.exit_code != Some(0) {
        return Err(RecordError::BuildEvidence("verus build did not exit 0".into()));
    }
    let output = store.read_blob(build.verus_output, None)?;
    let output: serde_json::Value =
        serde_json::from_slice(&output).map_err(|error| RecordError::BuildEvidence(format!("verus output: {error}")))?;
    let results = &output["verification-results"];
    let complete_success = results["success"] == true
        && results["errors"].as_u64() == Some(0)
        && results["verified"].as_u64().unwrap_or(0) != 0
        && results["is-verifying-entire-crate"] == true
        && results["encountered-error"] == false
        && results["encountered-vir-error"] == false;
    if !complete_success {
        return Err(RecordError::BuildEvidence(format!(
            "verus output does not report a complete successful verification of the entire crate: {results}"
        )));
    }
    library_path(store, &build)?;
    Ok(build)
}

/// Stored library file for the worker to load. Only its length is checked: no copy and no re-hash of the library.
pub fn library_path(store: &ObjectStore, build: &VerusBuildV1) -> Result<PathBuf, RecordError> {
    let path = store.object_path(build.library);
    let length = std::fs::metadata(&path).map_err(|error| RecordError::io(&path, error))?.len();
    if length != build.library_bytes {
        return Err(RecordError::BuildEvidence("stored verus library extent differs".into()));
    }
    Ok(path)
}
