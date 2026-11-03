//! `dlopen` of a Verus-compiled library, its layout-record check and its entry symbols (shared by every ABI version).

use super::error::AbiError;
use super::records::LayoutFn;
use std::ffi::{CStr, CString, c_void};
use std::path::{Path, PathBuf};

/// A library loaded with `dlopen(RTLD_NOW | RTLD_LOCAL)`. It is never unloaded: there is deliberately no `dlclose`,
/// because unloading code is unsafe if any thread the library spawned is still alive, and "every spawned worker is
/// joined" is a proof obligation of the candidate, not something this host checks. The caller must be a short-lived
/// child process that keeps the library and every input it was given until the OS ends the process.
pub(super) struct LoadedLibrary {
    pub path: PathBuf,
    handle: *mut c_void,
}

impl LoadedLibrary {
    /// `dlopen`, then refuse a library whose layout record (read through `layout_symbol`) differs from `expected`,
    /// entry count included. A library of another ABI version lacks the symbol and is refused.
    ///
    /// # Safety
    /// Loading runs the library's initializers. Only a library produced by the framework's Verus build of a frozen
    /// crate (framework-owned shim; author code that adds initializers is refused by the scanner) may be loaded, and
    /// only in an offline child process.
    pub unsafe fn open(path: &Path, layout_symbol: &'static str, expected: &[u64]) -> Result<Self, AbiError> {
        let open_error = |reason: String| AbiError::Open { path: path.to_owned(), reason };
        let text = CString::new(path.as_os_str().as_encoded_bytes()).map_err(|e| open_error(e.to_string()))?;
        let handle = unsafe { libc::dlopen(text.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL) };
        if handle.is_null() {
            return Err(open_error(last_loader_error()));
        }
        let library = Self { path: path.to_owned(), handle };
        // SAFETY: the layout symbol of every framework shim has the `LayoutFn` signature.
        let layout: LayoutFn = unsafe { std::mem::transmute(library.symbol(layout_symbol)?) };
        let mut actual = vec![0u64; expected.len()];
        let available = unsafe { layout(actual.as_mut_ptr(), actual.len() as u64) };
        if available != expected.len() as u64 || actual != expected {
            return Err(AbiError::LayoutMismatch { actual, expected: expected.to_vec() });
        }
        Ok(library)
    }

    /// The address of `symbol`; the caller transmutes it to the entry signature the shim declares for it.
    pub fn symbol(&self, symbol: &'static str) -> Result<*mut c_void, AbiError> {
        let missing = |reason: String| AbiError::MissingSymbol { path: self.path.clone(), symbol, reason };
        let text = CString::new(symbol).map_err(|e| missing(e.to_string()))?;
        let address = unsafe { libc::dlsym(self.handle, text.as_ptr()) };
        if address.is_null() {
            return Err(missing(last_loader_error()));
        }
        Ok(address)
    }
}

fn last_loader_error() -> String {
    let text = unsafe { libc::dlerror() };
    if text.is_null() { "unknown".into() } else { unsafe { CStr::from_ptr(text) }.to_string_lossy().into_owned() }
}
