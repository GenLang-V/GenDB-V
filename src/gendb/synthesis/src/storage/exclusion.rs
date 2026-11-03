//! Persistent user exclusions of storage packages under a restricted stored-data policy (`storage_policy`).
//!
//! The user's review may find that a storage package holds something `physical_only` excludes, although its builder
//! proves its `represents` and it may even have been registered under that policy (the declaration is reviewed, not
//! proved). Recording an exclusion (`gendb exclude-storage`) appends one record to the library stream
//! `storage-policy-exclusions.<policy>`. From then on every request of that policy kind over this library treats the
//! package as ineligible (`policy::StoredDataPolicy::ineligible`), whether or not the request lists anything, and an
//! exclusion wins over an `eligible_storages` entry. So the author catalogs leave it out, together with every earlier
//! query package that reads it (`storages.json`, `verus-library.json`); a workspace storage with the same package id is
//! refused before its asset is built; qualification refuses it; serving refuses a package that reads it.
//!
//! An exclusion is policy ineligibility, not a failed proof or a correctness revocation: the package, its admission,
//! its assets and the query packages over it stay in the library unchanged, and a request under `unrestricted` may
//! still use them. Nothing is deleted or rewritten, and there is no withdrawal record. Recording the same package
//! again under the same policy returns the existing exclusion.

use super::policy::PHYSICAL_ONLY;
use crate::controller::records::now_unix_ms;
use gendb_artifacts::verus::VERUS_STORAGE_PACKAGE_KIND;
use gendb_artifacts::{AppendRecord, ContentId, ObjectStore, append_record, lookup_record_head};
use gendb_verification::admission::AdmissionError;
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// Record kind of one exclusion.
pub const STORAGE_POLICY_EXCLUSION_KIND: &str = "gendb.storage-policy-exclusion.v1";

/// What an exclusion does (printed with every recording).
pub const EXCLUSION_MEANING: &str = "under this policy kind the package is ineligible for every later request over this library, with or without a request-level list (an exclusion wins over eligible_storages): it is not offered to authors, query packages reading it are not offered or served, a workspace storage with this package id is refused before its asset is built, and qualification refuses it. Policy ineligibility only: the package, its admission, assets and proofs stay in the library unchanged and remain usable under unrestricted";

/// One user exclusion of a storage package under a policy kind.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StoragePolicyExclusion {
    /// The policy kind it applies under (`physical_only`).
    pub policy: String,
    /// The excluded storage package (a published storage package record).
    pub package: ContentId,
    /// The package's storage name (descriptive).
    pub storage: String,
    /// Who reviewed what, and why the package is ineligible under `policy`.
    pub reason: String,
    pub recorded_unix_ms: u64,
}

/// The result of recording an exclusion.
#[derive(Clone, Debug, Serialize)]
pub struct RecordedExclusion {
    /// The exclusion record's identity.
    pub exclusion: ContentId,
    pub record: StoragePolicyExclusion,
    /// `false` when the package was already excluded under this policy (the earlier record is returned).
    pub recorded_now: bool,
}

/// The library stream of the exclusions under `policy`.
pub fn exclusion_stream(policy: &str) -> String {
    format!("storage-policy-exclusions.{policy}")
}

/// Every exclusion recorded under `policy`, oldest first: `(record id, exclusion)`.
pub fn recorded_exclusions(store: &ObjectStore, policy: &str) -> Result<Vec<(ContentId, StoragePolicyExclusion)>, AdmissionError> {
    let mut exclusions = vec![];
    let mut next = lookup_record_head(store, &exclusion_stream(policy)).map_err(AdmissionError::tool)?;
    while let Some(link) = next {
        let record: AppendRecord = store.read(link).and_then(|object| object.decode()).map_err(AdmissionError::tool)?;
        let object = store.read(record.subject).map_err(AdmissionError::tool)?;
        let exclusion = (object.format_version == 1 && object.kind == STORAGE_POLICY_EXCLUSION_KIND)
            .then(|| object.decode::<StoragePolicyExclusion>().ok())
            .flatten()
            .filter(|exclusion| exclusion.policy == policy)
            .ok_or_else(|| AdmissionError::tool(format!("record {} on {} is not a {policy} storage policy exclusion", record.subject, exclusion_stream(policy))))?;
        exclusions.push((record.subject, exclusion));
        next = record.previous;
    }
    exclusions.reverse();
    Ok(exclusions)
}

/// The exclusion of `package` under `policy`, if one is recorded.
pub fn exclusion_of(store: &ObjectStore, policy: &str, package: ContentId) -> Result<Option<(ContentId, StoragePolicyExclusion)>, AdmissionError> {
    Ok(recorded_exclusions(store, policy)?.into_iter().find(|(_, exclusion)| exclusion.package == package))
}

/// Exclude the storage package `package` under `policy` for the stated `reason` (the public route). Only the restricted
/// policy has exclusions; `package` must be a published storage package record (admitted or not).
pub fn record_exclusion(store: &ObjectStore, policy: &str, package: ContentId, reason: &str) -> Result<RecordedExclusion, AdmissionError> {
    if policy != PHYSICAL_ONLY {
        return Err(AdmissionError::refusal(format!(
            "storage_policy_exclusion_scope: exclusions apply under {PHYSICAL_ONLY} only, not {policy} (unrestricted admits every storage whose builder proves its represents)"
        )));
    }
    if reason.trim().is_empty() {
        return Err(AdmissionError::refusal("storage_policy_exclusion_reason: an exclusion needs a nonempty reason (who reviewed what, and why)"));
    }
    let object = store.read(package).map_err(|e| AdmissionError::missing_input(format!("storage package {package}: {e}")))?;
    if object.kind != VERUS_STORAGE_PACKAGE_KIND {
        return Err(AdmissionError::refusal(format!("{package} is a {} record, not a storage package", object.kind)));
    }
    if let Some((exclusion, record)) = exclusion_of(store, policy, package)? {
        return Ok(RecordedExclusion { exclusion, record, recorded_now: false });
    }
    let name = object.decode::<Value>().map_err(AdmissionError::tool)?["name"].as_str().unwrap_or_default().to_string();
    let record = StoragePolicyExclusion { policy: policy.into(), package, storage: name, reason: reason.trim().into(), recorded_unix_ms: now_unix_ms() };
    let exclusion = store.put(1, STORAGE_POLICY_EXCLUSION_KIND, &record).map_err(AdmissionError::tool)?;
    append_record(store, &exclusion_stream(policy), exclusion).map_err(AdmissionError::tool)?;
    Ok(RecordedExclusion { exclusion, record, recorded_now: true })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::policy::UNRESTRICTED;
    use serde_json::json;

    /// Recording appends one record per package and policy; a fresh store view reads it back; only a storage package
    /// under the restricted policy with a reason is recorded.
    #[test]
    fn exclusions_are_appended_once_per_package_and_read_from_a_fresh_store() {
        let root = crate::controller::test_support::scratch_root("storage-exclusion-records");
        let store = ObjectStore::open(root.join("library")).unwrap();
        let package = store.put(1, VERUS_STORAGE_PACKAGE_KIND, &json!({"name":"lineitem_by_order"})).unwrap();
        let not_a_storage = store.put(1, "gendb.verus.qualification-evidence.v1", &json!({})).unwrap();
        let refused = |policy: &str, id: ContentId, reason: &str| record_exclusion(&store, policy, id, reason).unwrap_err().message;
        assert!(refused(UNRESTRICTED, package, "reviewed").starts_with("storage_policy_exclusion_scope"));
        assert!(refused(PHYSICAL_ONLY, package, " ").starts_with("storage_policy_exclusion_reason"));
        assert!(refused(PHYSICAL_ONLY, not_a_storage, "reviewed").contains("not a storage package"));
        assert!(recorded_exclusions(&store, PHYSICAL_ONLY).unwrap().is_empty(), "refusals record nothing");

        let first = record_exclusion(&store, PHYSICAL_ONLY, package, " review: stores matching rows of another table ").unwrap();
        assert!(first.recorded_now && first.record.storage == "lineitem_by_order" && first.record.reason == "review: stores matching rows of another table");
        let again = record_exclusion(&store, PHYSICAL_ONLY, package, "a second review").unwrap();
        assert!(!again.recorded_now && again.exclusion == first.exclusion && again.record == first.record, "the earlier exclusion stands");

        let fresh = ObjectStore::open_existing(root.join("library")).unwrap();
        assert_eq!(recorded_exclusions(&fresh, PHYSICAL_ONLY).unwrap(), vec![(first.exclusion, first.record.clone())]);
        assert_eq!(exclusion_of(&fresh, PHYSICAL_ONLY, package).unwrap().map(|(id, _)| id), Some(first.exclusion));
        assert!(exclusion_of(&fresh, PHYSICAL_ONLY, not_a_storage).unwrap().is_none());
        assert!(recorded_exclusions(&fresh, UNRESTRICTED).unwrap().is_empty());
        std::fs::remove_dir_all(root).unwrap();
    }
}
