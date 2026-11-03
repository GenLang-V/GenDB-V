//! Registration of a storage: admission of a checked, built storage package, the one function the `storage_register`
//! tool, the workload role's qualification and a query's qualification (for its new storages) all call.
//!
//! By the time a storage is registered its checked build is already a library build record and its asset for the
//! current capture is already built from that stored library (`storage::build`); registration builds nothing. It
//! appends the admission with its evidence: the asset build record, the tiny-input build record and the author's
//! description (parts, layout, who registered it). Registering a package that is already admitted returns that
//! admission.

use super::catalog::STORAGE_DESCRIPTION_KIND;
use gendb_artifacts::verus as records;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::storage::admit_storage;
use serde::Serialize;
use serde_json::{Value, json};

/// The admission of one storage package.
#[derive(Clone, Debug, Serialize)]
pub struct Registration {
    pub name: String,
    pub package: ContentId,
    pub admission: ContentId,
    /// The asset for the capture it was built over (built before registration; never rebuilt here).
    pub asset: ContentId,
    /// `true` when this call appended the admission; `false` when the package was already admitted.
    pub admitted_now: bool,
}

/// Admit `package` (a published storage package of `name` whose asset `asset` is built) with its evidence records and
/// the author's `description` (stored as descriptive evidence).
pub fn register_storage(
    store: &ObjectStore,
    name: &str,
    package: ContentId,
    asset: ContentId,
    evidence: &[ContentId],
    description: &Value,
) -> Result<Registration, AdmissionError> {
    let versions = records::storage_versions(store, name).map_err(AdmissionError::tool)?;
    if let Some((admission, _)) = versions.iter().find(|(_, admitted)| admitted.package == package) {
        return Ok(Registration { name: name.into(), package, asset, admission: *admission, admitted_now: false });
    }
    let description = store
        .put(1, STORAGE_DESCRIPTION_KIND, &json!({"package":package,"description":description,"scope":"the author's words; descriptive, never interpreted"}))
        .map_err(AdmissionError::tool)?;
    let evidence: Vec<ContentId> = evidence.iter().copied().chain([description]).collect();
    let admission = admit_storage(store, package, evidence)?;
    Ok(Registration { name: name.into(), package, asset, admission, admitted_now: true })
}
