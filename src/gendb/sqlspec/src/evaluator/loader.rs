//! Loading a compiled evaluator library and calling its C ABI v1 (`sqlspec/interpreter/host/shim.rs`):
//! `gendb_sql_abi_version_v1() -> u64`, `gendb_sql_run_v1(data, len, sink) -> i32`, `gendb_sql_echo_v1(sink) -> i32`.
//! The shim delivers each call's complete output through one `SqlSinkV1::put` call.
//!
//! Trust: the loader and `dlopen` are trusted. A library stays mapped until the process exits (no `dlclose`); each
//! call copies its input inside the shim, so no host memory is borrowed across calls. Only a library built by
//! `gendb_verification::reference` (verified and compiled from one frozen snapshot) should be loaded.

use crate::codec::{decode_result, encode_database, HostTables, RunOutcome, WireError};
use std::ffi::{c_void, CStr, CString};
use std::fmt;
use std::path::{Path, PathBuf};

/// Version of the evaluator's wire formats and C symbols (`ABI_VERSION` of the shim).
pub const ABI_VERSION: u64 = 1;

/// A failed load of, or call into, an evaluator library.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvaluatorError {
    Open { path: PathBuf, reason: String },
    MissingSymbol { symbol: &'static str, reason: String },
    AbiVersion { library: u64 },
    /// The shim returned a non-zero status (negative: the sink was unusable).
    Shim(i32),
    NoOutput,
    Wire(WireError),
    EchoNotUtf8,
}

impl fmt::Display for EvaluatorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvaluatorError::Open { path, reason } => write!(f, "dlopen {}: {reason}", path.display()),
            EvaluatorError::MissingSymbol { symbol, reason } => write!(f, "{symbol}: {reason}"),
            EvaluatorError::AbiVersion { library } => write!(f, "library ABI version {library}, host {ABI_VERSION}"),
            EvaluatorError::Shim(rc) => write!(f, "shim returned {rc}"),
            EvaluatorError::NoOutput => f.write_str("shim delivered no output"),
            EvaluatorError::Wire(e) => e.fmt(f),
            EvaluatorError::EchoNotUtf8 => f.write_str("echo text is not UTF-8"),
        }
    }
}

impl std::error::Error for EvaluatorError {}

/// Host-provided output sink of the shim.
#[repr(C)]
struct SqlSinkV1 {
    ctx: *mut c_void,
    put: Option<unsafe extern "C" fn(*mut c_void, *const u8, u64) -> i32>,
}

/// Stores the one output of a call into `ctx: *mut Option<Vec<u8>>`; refuses a second delivery.
unsafe extern "C" fn sink_put(ctx: *mut c_void, data: *const u8, len: u64) -> i32 {
    let out = unsafe { &mut *(ctx as *mut Option<Vec<u8>>) };
    if out.is_some() || (data.is_null() && len > 0) {
        return 1;
    }
    let bytes = if len == 0 { Vec::new() } else { unsafe { std::slice::from_raw_parts(data, len as usize) }.to_vec() };
    *out = Some(bytes);
    0
}

type VersionFn = unsafe extern "C" fn() -> u64;
type RunFn = unsafe extern "C" fn(*const u8, u64, *const SqlSinkV1) -> i32;
type EchoFn = unsafe extern "C" fn(*const SqlSinkV1) -> i32;

/// A compiled evaluator library, loaded once and never unloaded.
pub struct EvaluatorLibrary {
    path: PathBuf,
    run: RunFn,
    echo: EchoFn,
}

fn dlerror() -> String {
    let e = unsafe { libc::dlerror() };
    if e.is_null() { "unknown dlerror".into() } else { unsafe { CStr::from_ptr(e) }.to_string_lossy().into_owned() }
}

impl EvaluatorLibrary {
    /// `dlopen(RTLD_NOW | RTLD_LOCAL)`, check the ABI version and bind the entry symbols.
    pub fn load(path: &Path) -> Result<Self, EvaluatorError> {
        let open_error = |reason: String| EvaluatorError::Open { path: path.to_path_buf(), reason };
        let text = CString::new(path.as_os_str().as_encoded_bytes()).map_err(|e| open_error(e.to_string()))?;
        let handle = unsafe { libc::dlopen(text.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL) };
        if handle.is_null() {
            return Err(open_error(dlerror()));
        }
        let symbol = |name: &'static str| -> Result<*mut c_void, EvaluatorError> {
            let c = CString::new(name).expect("static symbol name");
            let p = unsafe { libc::dlsym(handle, c.as_ptr()) };
            if p.is_null() { Err(EvaluatorError::MissingSymbol { symbol: name, reason: dlerror() }) } else { Ok(p) }
        };
        let version: VersionFn = unsafe { std::mem::transmute(symbol("gendb_sql_abi_version_v1")?) };
        let library = unsafe { version() };
        if library != ABI_VERSION {
            return Err(EvaluatorError::AbiVersion { library });
        }
        Ok(EvaluatorLibrary {
            path: path.to_path_buf(),
            run: unsafe { std::mem::transmute::<*mut c_void, RunFn>(symbol("gendb_sql_run_v1")?) },
            echo: unsafe { std::mem::transmute::<*mut c_void, EchoFn>(symbol("gendb_sql_echo_v1")?) },
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Evaluate the library's statement on `tables` (the verified outcome, or the shim's wire refusal).
    pub fn run(&self, tables: &HostTables) -> Result<RunOutcome, EvaluatorError> {
        let wire = encode_database(tables);
        let bytes = collect_output(|sink| unsafe { (self.run)(wire.as_ptr(), wire.len() as u64, sink) })?;
        decode_result(&bytes).map_err(EvaluatorError::Wire)
    }

    /// Echo text of the library's executable AST.
    pub fn echo(&self) -> Result<String, EvaluatorError> {
        let bytes = collect_output(|sink| unsafe { (self.echo)(sink) })?;
        String::from_utf8(bytes).map_err(|_| EvaluatorError::EchoNotUtf8)
    }
}

/// Call a shim entry with a fresh sink and return the one output it delivered.
fn collect_output(call: impl FnOnce(*const SqlSinkV1) -> i32) -> Result<Vec<u8>, EvaluatorError> {
    let mut out: Option<Vec<u8>> = None;
    let sink = SqlSinkV1 { ctx: &mut out as *mut Option<Vec<u8>> as *mut c_void, put: Some(sink_put) };
    let rc = call(&sink);
    if rc != 0 {
        return Err(EvaluatorError::Shim(rc));
    }
    out.ok_or(EvaluatorError::NoOutput)
}
