//! The source-controlled toolchain pin and the installed toolchain it names.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Source-controlled pin of the Verus release, Rust toolchain and Z3 (`verification/verus/toolchain.json`).
pub const VERUS_PIN_JSON: &str = include_str!("../../verus/toolchain.json");

/// Placeholder in [`VerusPin::default_home`] for the repository this crate was built in.
const REPOSITORY_PLACEHOLDER: &str = "<repository>";

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VerusPin {
    pub format_version: u32,
    pub verus: VerusRelease,
    pub rust: RustPin,
    pub z3: Z3Pin,
    /// How `rust_verify` is started (recorded reasoning; see [`VerusToolchain::environment`]).
    pub launcher: String,
    /// Environment variable that overrides the installation directory.
    pub home_env: String,
    /// Installation directory used when `home_env` is unset, with `<repository>` for the repository root.
    pub default_home: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VerusRelease {
    pub release_tag: String,
    pub version: String,
    pub commit: String,
    pub asset: String,
    pub url: String,
    /// Directory of `rust_verify`, `libvstd.rlib` and `vstd.vir`, relative to the home.
    pub install_dir: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RustPin {
    pub toolchain: String,
    pub components: Vec<String>,
    /// Relative to the home.
    pub rustup_home: String,
    /// Relative to the home.
    pub cargo_home: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Z3Pin {
    pub version: String,
    pub source: String,
    /// The `z3` executable, relative to the home.
    pub path: String,
}

pub fn verus_pin() -> VerusPin {
    serde_json::from_str(VERUS_PIN_JSON).expect("verification/verus/toolchain.json is valid")
}

/// Why the pinned toolchain cannot be used. Always the `tool_failure` class: the candidate is not implicated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ToolchainError {
    /// The installation directory does not resolve.
    Home { path: PathBuf, message: String },
    /// A file the pinned installation must contain is absent.
    Incomplete { missing: PathBuf },
    /// `rust_verify` could not be started.
    Start { program: PathBuf, message: String },
    /// `rust_verify --version --output-json` printed no JSON.
    UnreadableVersion { message: String, stderr: String },
    /// The installed Verus release is not the pinned one.
    VersionMismatch { installed_version: Option<String>, installed_commit: Option<String>, pinned_version: String, pinned_commit: String },
}

impl ToolchainError {
    pub fn failure_class(&self) -> &'static str {
        "tool_failure"
    }
}

impl fmt::Display for ToolchainError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Home { path, message } => write!(f, "Verus home {}: {message}", path.display()),
            Self::Incomplete { missing } => write!(f, "pinned Verus installation incomplete: missing {}", missing.display()),
            Self::Start { program, message } => write!(f, "cannot start {}: {message}", program.display()),
            Self::UnreadableVersion { message, stderr } => write!(f, "rust_verify --version --output-json: {message}; stderr: {stderr}"),
            Self::VersionMismatch { installed_version, installed_commit, pinned_version, pinned_commit } => {
                write!(f, "installed Verus {installed_version:?} {installed_commit:?} differs from pin {pinned_version} {pinned_commit}")
            }
        }
    }
}

impl std::error::Error for ToolchainError {}

/// The installed pinned toolchain: resolved paths, each checked to exist.
#[derive(Clone, Debug, Serialize)]
pub struct VerusToolchain {
    pub home: PathBuf,
    pub rust_verify: PathBuf,
    /// `lib` of the pinned rustup toolchain (the `LD_LIBRARY_PATH` of `rust_verify`).
    pub rust_lib: PathBuf,
    pub z3: PathBuf,
    pub pin: VerusPin,
}

impl VerusToolchain {
    /// The installation named by the pin's `home_env` variable (`GENDB_VERUS_HOME`), else its `default_home`.
    pub fn from_env() -> Result<Self, ToolchainError> {
        let pin = verus_pin();
        let home = std::env::var_os(&pin.home_env).map(PathBuf::from).unwrap_or_else(|| default_home(&pin));
        Self::at(&home)
    }

    /// The installation at `home`, checked to contain `rust_verify`, the compiled vstd, the Rust libraries and Z3.
    pub fn at(home: &Path) -> Result<Self, ToolchainError> {
        let pin = verus_pin();
        let home = home.canonicalize().map_err(|e| ToolchainError::Home { path: home.to_owned(), message: e.to_string() })?;
        let toolchain = Self {
            rust_verify: home.join(&pin.verus.install_dir).join("rust_verify"),
            rust_lib: home.join(&pin.rust.rustup_home).join("toolchains").join(&pin.rust.toolchain).join("lib"),
            z3: home.join(&pin.z3.path),
            home,
            pin,
        };
        let vstd_library = toolchain.rust_verify.with_file_name("libvstd.rlib");
        let vstd_vir = toolchain.rust_verify.with_file_name("vstd.vir");
        for required in [&toolchain.rust_verify, &toolchain.rust_lib, &toolchain.z3, &vstd_library, &vstd_vir] {
            if !required.exists() {
                return Err(ToolchainError::Incomplete { missing: required.clone() });
            }
        }
        Ok(toolchain)
    }

    /// The complete environment of every invocation; the process environment is cleared, so nothing else leaks in.
    /// `rust_verify` is started directly, as the pin's `launcher` note explains.
    pub fn environment(&self, tmp: &Path) -> BTreeMap<String, String> {
        BTreeMap::from([
            ("PATH".into(), "/usr/local/bin:/usr/bin:/bin".into()),
            ("LD_LIBRARY_PATH".into(), self.rust_lib.display().to_string()),
            ("VSTD_KIND".into(), "Imported".into()),
            ("VERUS_Z3_PATH".into(), self.z3.display().to_string()),
            ("TMPDIR".into(), tmp.display().to_string()),
        ])
    }

    /// The raw `rust_verify --version --output-json` object, checked against the pinned version and commit.
    /// Build records store its text as the provider identity.
    pub fn version(&self) -> Result<serde_json::Value, ToolchainError> {
        gendb_runtime::process_stop::park_if_stopping();
        let output = Command::new(&self.rust_verify).args(["--version", "--output-json"]).env_clear().envs(self.environment(&std::env::temp_dir())).output();
        // A version check ended by the user's stop is never read (`gendb_runtime::process_stop`).
        gendb_runtime::process_stop::park_if_stopping();
        let output = output.map_err(|e| ToolchainError::Start { program: self.rust_verify.clone(), message: e.to_string() })?;
        let version: serde_json::Value = serde_json::from_slice(&output.stdout).map_err(|e| ToolchainError::UnreadableVersion {
            message: e.to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        })?;
        let installed_version = version["verus"]["version"].as_str();
        let installed_commit = version["verus"]["commit"].as_str();
        if installed_version != Some(self.pin.verus.version.as_str()) || installed_commit != Some(self.pin.verus.commit.as_str()) {
            return Err(ToolchainError::VersionMismatch {
                installed_version: installed_version.map(String::from),
                installed_commit: installed_commit.map(String::from),
                pinned_version: self.pin.verus.version.clone(),
                pinned_commit: self.pin.verus.commit.clone(),
            });
        }
        Ok(version)
    }
}

/// The pin's `default_home` with `<repository>` replaced by the repository root of this source tree
/// (`<repository>/src/gendb/verification` is this crate). The installation is outside the source tree, so other
/// checkouts and this one resolve to the same pinned installation.
fn default_home(pin: &VerusPin) -> PathBuf {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    PathBuf::from(pin.default_home.replace(REPOSITORY_PLACEHOLDER, &repository.display().to_string()))
}
