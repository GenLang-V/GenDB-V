//! Evidence files of admission: JSON written once (never overwritten), read back for later steps.

use super::AdmissionError;
use serde::Serialize;
use std::io::Write;
use std::path::Path;

/// Pretty JSON into the new file `path`; an existing file is an error (evidence is written once).
pub(crate) fn write_new_json(path: &Path, value: &impl Serialize) -> Result<(), AdmissionError> {
    let bytes = serde_json::to_vec_pretty(value).map_err(AdmissionError::tool)?;
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .and_then(|mut file| file.write_all(&bytes))
        .map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))
}

pub(crate) fn create_dir(path: &Path) -> Result<(), AdmissionError> {
    std::fs::create_dir_all(path).map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))
}

pub(crate) fn write_text(path: &Path, text: &str) -> Result<(), AdmissionError> {
    std::fs::write(path, text).map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))
}

/// Milliseconds since the Unix epoch (fresh evidence directory names).
pub(crate) fn now_unix_ms() -> u128 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default().as_millis()
}
