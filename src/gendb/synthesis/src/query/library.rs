//! The author's view of the admitted library (`verus-library.json`): verified agent modules of earlier admitted
//! query packages (the implementation records their packages list; storage builds, which have their own catalog
//! `storages.json`, and checked but unadmitted builds are not offered), with their stored sources copied into the workspace, every recorded item's effective checked contract,
//! the package admissions, and the measurements recorded when those packages were qualified (descriptive; not targets
//! and not this data; a package over stored data names its statement, storages, implementations and the data its
//! measurements ran on; a package whose statement declares integrity constraints is labelled with their digest,
//! `declared_constraints`: its code was proved under those assumptions). Reused code is copied into a new crate and
//! verified again there.

use super::source_items::{ItemSource, describe_item};
use crate::storage::policy::StoredDataPolicy;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_artifacts::verus::{
    self as records, VerusImplementationV1, VerusPackageAdmissionV1, VerusPackageAdmissionV2, VerusQueryPackageV2, VerusQueryPackageV3,
    VerusSourceOwnerV1, VerusStatementKeyV2,
};
use std::collections::BTreeSet;
use gendb_verification::admission::AdmissionError;
use serde_json::{Value, json};
use std::fs;
use std::path::Path;

/// Record kinds of the evidence written at qualification (`admission::qualification`).
const QUALIFICATION_EVIDENCE_KIND: &str = "gendb.verus.qualification-evidence.v1";
const ASSET_BUILD_EVIDENCE_KIND: &str = "gendb.verus.asset-build-evidence.v1";

const LIBRARY_USE: &str = "verified agent modules of earlier admitted query packages (admitted storages are listed separately in storages.json); copy any into your src/agent and declare them; copies are re-verified with your crate. Operations lists only what a checked contract bridge established (the fixed entry covers the whole plan); record items hold only each function's own clause text; effective_items gives the contract Verus checked, resolved from the build's stored sources: direct, inherited (a trait-impl method: the trait declaration's requires/ensures/no_unwind plus the impl's definitions of the trait's spec functions) or unresolved (unknown, never 'no requirements'); module_role is the whole file's declared role, item_role is inferred only from a fixed interface, otherwise unspecified.";

/// The inventory of `store`; agent sources are copied once under `code_dir/<build>/<path>`. Packages over stored data
/// that read a storage `policy` excludes, their implementations (unless another listed package has them) and their
/// qualification measurements are left out.
pub fn library_inventory(store: &ObjectStore, code_dir: &Path, policy: &StoredDataPolicy) -> Result<Value, AdmissionError> {
    let excluded = policy_excluded(store, policy)?;
    let (admitted_packages, admitted_implementations) = admitted_query_implementations(store, &excluded)?;
    let mut implementations = vec![];
    for object in store.list_kind(records::VERUS_IMPLEMENTATION_KIND).map_err(AdmissionError::tool)? {
        if !admitted_implementations.contains(&object.id) {
            continue;
        }
        let record: VerusImplementationV1 = object.decode().map_err(AdmissionError::tool)?;
        // Only implementations whose build is admissible evidence are offered.
        let Ok(build) = records::check_build_evidence(store, record.build) else { continue };
        let mut agent_sources = vec![];
        let mut sources = vec![];
        for source in &build.sources {
            let bytes = store.read_blob(source.blob, Some(source.bytes)).map_err(AdmissionError::tool)?;
            if source.owner == VerusSourceOwnerV1::Agent {
                let path = code_dir.join(record.build.to_hex()).join(&source.path);
                if !path.exists() {
                    fs::create_dir_all(path.parent().expect("a joined path has a parent")).map_err(AdmissionError::tool)?;
                    fs::write(&path, &bytes).map_err(AdmissionError::tool)?;
                }
                agent_sources.push(path);
            }
            sources.push(ItemSource {
                path: source.path.clone(),
                text: String::from_utf8(bytes).map_err(AdmissionError::tool)?,
                provenance: json!({"build":record.build,"path":source.path,"owner":source.owner,"blob":source.blob,"bytes":source.bytes}),
            });
        }
        // Records name `agent/<file> (<file role>)` or a framework module such as `gendb_entry`.
        let (file, module_role) = match record.module.split_once(" (") {
            Some((file, role)) => (file.to_string(), role.trim_end_matches(')').to_string()),
            None => (format!("{}.rs", record.module.replace("::", "/")), "framework".to_string()),
        };
        let effective: Vec<Value> = record.items.iter().map(|item| describe_item(&sources, &file, &module_role, &item.path)).collect();
        implementations.push(json!({"implementation":object.id,"record":record,"agent_sources":agent_sources,"effective_items":effective}));
    }
    Ok(json!({"format_version":1,"implementations":implementations,"package_admissions":admitted_packages,
        "admitted_package_evidence":{"records":recorded_measurements(store, &excluded)?,"packages_over_stored_data":stored_data_package_evidence(store, &excluded)?,
            "scope":"measurements recorded when earlier packages of this library were qualified, on the data version and row counts they name (column_rows, data); descriptive, not targets and not necessarily this data or this host state"},
        "excluded_by_storage_policy":excluded.admissions.len(),"use":LIBRARY_USE}))
}

/// Query package admissions (over stored data) that read a storage the policy excludes, and their qualification
/// evidence records.
#[derive(Default)]
struct PolicyExcluded {
    admissions: BTreeSet<ContentId>,
    evidence: BTreeSet<ContentId>,
}

fn policy_excluded(store: &ObjectStore, policy: &StoredDataPolicy) -> Result<PolicyExcluded, AdmissionError> {
    let mut excluded = PolicyExcluded::default();
    if policy.is_unrestricted() {
        return Ok(excluded);
    }
    for object in store.list_kind(records::VERUS_PACKAGE_ADMISSION_V2_KIND).map_err(AdmissionError::tool)? {
        let admission: VerusPackageAdmissionV2 = object.decode().map_err(AdmissionError::tool)?;
        let package: VerusQueryPackageV3 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        if policy.ineligible_use(store, package.storage_uses.iter().map(|u| (u.name.as_str(), u.package)))?.is_some() {
            excluded.admissions.insert(object.id);
            excluded.evidence.extend(admission.qualification_evidence);
        }
    }
    Ok(excluded)
}

/// The admissions of query packages (v1 for saved v2 packages, v2 for packages over stored data) and the
/// implementation records their admitted packages list.
fn admitted_query_implementations(store: &ObjectStore, excluded: &PolicyExcluded) -> Result<(Vec<ContentId>, BTreeSet<ContentId>), AdmissionError> {
    let mut admissions = vec![];
    let mut implementations = BTreeSet::new();
    for object in store.list_kind(records::VERUS_PACKAGE_ADMISSION_KIND).map_err(AdmissionError::tool)? {
        let admission: VerusPackageAdmissionV1 = object.decode().map_err(AdmissionError::tool)?;
        let package: VerusQueryPackageV2 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        implementations.extend(package.implementations);
        admissions.push(object.id);
    }
    for object in store.list_kind(records::VERUS_PACKAGE_ADMISSION_V2_KIND).map_err(AdmissionError::tool)? {
        if excluded.admissions.contains(&object.id) {
            continue;
        }
        let admission: VerusPackageAdmissionV2 = object.decode().map_err(AdmissionError::tool)?;
        let package: VerusQueryPackageV3 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        implementations.extend(package.implementations);
        admissions.push(object.id);
    }
    Ok((admissions, implementations))
}

/// Per admitted query package over stored data: its statement, SQL, storage uses and implementations, and what its
/// qualification measured (the exact hot medians per worker count at the first admission binding, the score, the
/// storages' requests and sizes) with the data version and rows of the assets it ran over.
fn stored_data_package_evidence(store: &ObjectStore, excluded: &PolicyExcluded) -> Result<Vec<Value>, AdmissionError> {
    let read = |id: ContentId| store.read(id).and_then(|o| o.decode::<Value>()).map_err(AdmissionError::tool);
    let mut packages = vec![];
    for object in store.list_kind(records::VERUS_PACKAGE_ADMISSION_V2_KIND).map_err(AdmissionError::tool)? {
        if excluded.admissions.contains(&object.id) {
            continue;
        }
        let admission: VerusPackageAdmissionV2 = object.decode().map_err(AdmissionError::tool)?;
        let package: VerusQueryPackageV3 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        let sql = read(package.claim)?["sql"].clone();
        let mut qualifications = vec![];
        for evidence in &admission.qualification_evidence {
            let evaluation = read(*evidence)?["evaluation"].take();
            let measurements: Vec<Value> = evaluation["measurements"].as_array().into_iter().flatten()
                .map(|m| json!({"workers":m["workers"],"binding":m["binding"],"status":m["status"],"median_ns":m["median_ns"],"samples_ns":m["samples_ns"],
                    "warm_ns":m["warm_ns"],"calling_thread_share_permille":m["calling_thread_share_permille"],"storage_requests":m["storage_requests"]}))
                .collect();
            qualifications.push(json!({"record":evidence,"measurements":measurements,"score_ns":evaluation["score_ns"],"storages":evaluation["storage"]}));
        }
        let data = admission.assets.iter().map(|asset| Ok(json!({"asset":asset,"tables":read(*asset)?["key"]["tables"]}))).collect::<Result<Vec<_>, AdmissionError>>()?;
        let mut record = json!({"admission":object.id,"package":admission.package,"statement_key":package.statement,"sql":sql,
            "storage_uses":package.storage_uses,"implementations":package.implementations,"qualifications":qualifications,"data":data});
        let key: VerusStatementKeyV2 = store.read(package.statement).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        if let Some(digest) = key.constraints_digest() {
            // Entry v5: proved under these declared constraints; reused code is verified again in the new crate.
            record["declared_constraints"] = json!(digest);
        }
        packages.push(record);
    }
    Ok(packages)
}

/// Per qualification and asset-build evidence record: its measurements, as recorded.
fn recorded_measurements(store: &ObjectStore, excluded: &PolicyExcluded) -> Result<Vec<Value>, AdmissionError> {
    let mut measured = vec![];
    for object in store.list_kind(QUALIFICATION_EVIDENCE_KIND).map_err(AdmissionError::tool)?.into_iter().filter(|o| !excluded.evidence.contains(&o.id)) {
        let record: Value = object.decode().map_err(AdmissionError::tool)?;
        let cells = record.pointer("/real_data/cells").and_then(Value::as_array).map(|cells| {
            cells
                .iter()
                .map(|c| json!({"workers":c["workers"],"status":c["status"],"reference_rows":c["reference_rows"],"warm_wall_ns":c["warm_wall_ns"],
                    "hot_wall_ns":c["hot_wall_ns"],"median_hot_wall_ns":c["median_hot_wall_ns"],"usage":c["usage"],"dispatch_spawned":c.pointer("/dispatch/spawned")}))
                .collect::<Vec<_>>()
        });
        measured.push(json!({"record":object.id,"kind":"qualification","real_data_cells":cells,"timing":record.pointer("/real_data/timing"),
            "verus_wall_ns":record.pointer("/verus/wall_ns"),"verification":record.pointer("/verus/verification")}));
    }
    for object in store.list_kind(ASSET_BUILD_EVIDENCE_KIND).map_err(AdmissionError::tool)? {
        let record: Value = object.decode().map_err(AdmissionError::tool)?;
        measured.push(json!({"record":object.id,"kind":"asset_build","column_rows":record.pointer("/asset/column_rows"),"build_wall_ns":record.pointer("/asset/build_wall_ns"),
            "bytes":record.pointer("/asset/bytes"),"declared_optimization":record.pointer("/asset/declared_optimization")}));
    }
    Ok(measured)
}

#[cfg(test)]
mod tests {
    use super::*;
    use gendb_artifacts::verus::{VERUS_STORAGE_PACKAGE_KIND, VerusStoragePackageV1};
    use std::path::PathBuf;

    /// Over an existing library (read-only; its agent sources are copied to scratch): the inventory offers only
    /// implementation records of admitted query packages, never a storage build.
    #[test]
    #[ignore = "reads an existing library: set GENDB_LIBRARY; -- --ignored"]
    fn inventory_offers_only_admitted_query_implementations() {
        let store = ObjectStore::open_existing(std::env::var("GENDB_LIBRARY").expect("GENDB_LIBRARY")).unwrap();
        let code = PathBuf::from(std::env::var("TMPDIR").expect("TMPDIR (scratch)")).join(format!("library-inventory-{}", std::process::id()));
        let inventory = library_inventory(&store, &code, &StoredDataPolicy::Unrestricted).unwrap();
        let (admissions, admitted) = admitted_query_implementations(&store, &PolicyExcluded::default()).unwrap();
        let offered: Vec<&Value> = inventory["implementations"].as_array().unwrap().iter().collect();
        for package in inventory["admitted_package_evidence"]["packages_over_stored_data"].as_array().unwrap() {
            assert!(package["sql"].is_string() && package["data"][0]["tables"].is_array(), "{package}");
        }
        assert!(!admissions.is_empty() && !offered.is_empty());
        let storage_builds: BTreeSet<String> = store
            .list_kind(VERUS_STORAGE_PACKAGE_KIND)
            .unwrap()
            .iter()
            .map(|o| o.decode::<VerusStoragePackageV1>().unwrap().build.to_hex())
            .collect();
        assert!(!storage_builds.is_empty());
        for implementation in offered {
            let id: ContentId = serde_json::from_value(implementation["implementation"].clone()).unwrap();
            assert!(admitted.contains(&id), "{id} is not listed by an admitted query package");
            let build = implementation["record"]["build"].as_str().unwrap();
            assert!(!storage_builds.contains(build), "storage build {build} offered as a query implementation");
        }
        println!("offered {} implementation records of {} admissions; {} storage builds excluded", admitted.len(), admissions.len(), storage_builds.len());
        fs::remove_dir_all(&code).ok();
    }
}
