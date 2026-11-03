//! Serving without synthesis (the controller's `synthesis: disabled` route): one requested statement is translated
//! again as its statement instance and served from its admitted package (over stored data, else ABI v3; see
//! `gendb_runtime::serve`) at every requested argument binding and worker count. No synthesis, proof or reference. Saved ABI v1/v2 packages are served only by
//! the earlier GenDB version.

use crate::storage::flat;
use crate::storage::payload::uses_holding_a_column_twice;
use crate::storage::policy::StoredDataPolicy;
use gendb_artifacts::ObjectStore;
use gendb_frontend::params::ParamRequest;
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::ABI_VERSION;
use gendb_runtime::serve::{AdmittedPackage, WorkerExecutor, admitted_package, serve};
use gendb_storage::io::PartAccess;
use gendb_storage::versions::CurrentCapture;
use gendb_storage::import::PreparedSource;
use gendb_verification::admission::execution::{CHILD_TIMEOUT_SECONDS, RANGE_CAPACITY};
use gendb_verification::admission::{AdmissionError, IntegrityConstraints, prepare_statement};
use serde_json::{Value, json};
use std::path::Path;

/// One requested statement: SQL, parameter declaration and argument bindings (none: the one binding of a concrete
/// statement), translated with the request's declared integrity constraints.
pub struct ServeRequest<'a> {
    pub sql: &'a str,
    pub parameters: &'a [ParamRequest],
    pub integrity_constraints: Option<&'a IntegrityConstraints>,
    pub arguments: &'a [Vec<String>],
    /// A package reading a storage this policy excludes is not served.
    pub storage_policy: &'a StoredDataPolicy,
}

/// Serve `request` from its admitted package at every argument binding and every count of `worker_counts` (`worker`:
/// the executable run as `<worker> worker REQUEST RESULT`; evidence under `work`), mapping stored parts with `access`
/// (kernel advice, recorded in every cell as `part_access`). One record per served cell, or one `unsupported` record
/// naming why the statement has no admitted package, which storage of its package the storage policy excludes, or
/// (under `physical_only`) which column its storages together store twice, or (under `fixed_flat`) which storage use
/// lacks its prepared flat asset (`storage::flat::served_package_refusal`).
#[allow(clippy::too_many_arguments)]
pub fn serve_statement(
    parser: &SqlParser,
    store: &ObjectStore,
    source: &PreparedSource,
    request: &ServeRequest<'_>,
    worker: &Path,
    worker_counts: &[usize],
    access: PartAccess,
    work: &Path,
) -> Result<Vec<Value>, AdmissionError> {
    let statement = match prepare_statement(parser, source.dataset(), request.integrity_constraints, request.sql, request.parameters, &[], &[], &work.join("statement")) {
        Ok(statement) => statement,
        Err(refused) => return Ok(vec![json!({"sql":request.sql,"status":"unsupported","reason":refused.error.to_string()})]),
    };
    let admitted = admitted_package(store, &statement.instance).map_err(AdmissionError::tool)?;
    if admitted.is_none() {
        let reason = if request.parameters.is_empty() {
            "no admitted package for this statement (neither over stored data nor ABI v3); saved ABI v1/v2 packages are served only by the earlier GenDB version (not part of this repository)"
        } else {
            "no admitted Verus package for this statement and parameter declaration"
        };
        return Ok(vec![json!({"sql":request.sql,"status":"unsupported","reason":reason})]);
    }
    if let Some(AdmittedPackage::StoredDataV4 { resolved, .. }) = &admitted {
        let uses = resolved.package.storage_uses.iter().map(|u| (u.name.as_str(), u.package));
        if let Some(reason) = request.storage_policy.ineligible_use(store, uses)? {
            return Ok(vec![json!({"sql":request.sql,"status":"unsupported","reason":reason})]);
        }
        // Its storages together hold each column once (a user-listed earlier registration could hold a second copy).
        if request.storage_policy.stores_columns_once() {
            let uses = resolved.package.storage_uses.iter().map(|u| (u.name.clone(), u.package)).collect();
            if let Some(reason) = uses_holding_a_column_twice(store, uses)? {
                return Ok(vec![json!({"sql":request.sql,"status":"unsupported","reason":reason})]);
            }
        }
    }
    let bindings: Vec<Vec<String>> = if request.arguments.is_empty() { vec![vec![]] } else { request.arguments.to_vec() };
    let current = CurrentCapture::of(source).map_err(AdmissionError::tool)?;
    // Under fixed_flat only packages over the prepared flat storages, without static items, are served.
    if request.storage_policy.is_fixed_flat()
        && let Some(admitted) = &admitted
        && let Some(reason) = flat::served_package_refusal(store, &current, admitted)?
    {
        return Ok(vec![json!({"sql":request.sql,"status":"unsupported","reason":reason})]);
    }
    let abi = match admitted {
        Some(AdmittedPackage::StoredDataV4 { .. }) => 4,
        _ => ABI_VERSION,
    };
    let mut out = vec![];
    for texts in &bindings {
        for workers in worker_counts {
            let executor = WorkerExecutor::new(worker, work, CHILD_TIMEOUT_SECONDS, RANGE_CAPACITY, 1);
            let mut cell = match serve(store, &statement.instance, texts, &current, access, &executor, *workers as u32) {
                Ok(served) => {
                    let mut record = served.record().map_err(AdmissionError::tool)?;
                    record["status"] = json!("executed");
                    record["tier"] = json!("verus_package");
                    record["abi"] = json!(abi);
                    record["columns"] = json!(statement.instance.doc.output.names);
                    record
                }
                Err(reason) => json!({"status":"unsupported","reason":reason.to_string()}),
            };
            cell["sql"] = json!(request.sql);
            cell["arguments_requested"] = json!(texts);
            cell["workers"] = json!(workers);
            cell["part_access"] = json!(access);
            cell["statement_key"] = json!(statement.key_id);
            out.push(cell);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::request::WorkloadRequest;
    use gendb_runtime::serve::DeclaredConstraints;

    /// Read-only compatibility of the accepted results with declared-constraint support: for every record of the
    /// reviewer-written list (`GENDB_ACCEPTED_KEYS`: `{records: [{query, request, query_index, recorded_statement_key,
    /// selected_package}]}`) the statement is translated again from its request without declarations (no data read;
    /// statement records under `TMPDIR`), its statement key v2 (`statement_key_v4`, the key of packages over stored data) must equal the recorded one, and the library lookup
    /// of serving must find the selected package with no declaration involved. No serving, preflight, proof or build.
    #[test]
    #[ignore = "reads accepted run requests and libraries; needs the pinned frontend; set GENDB_ACCEPTED_KEYS; -- --ignored"]
    fn accepted_statements_keep_their_keys_and_packages() {
        let list: Value = serde_json::from_str(&std::fs::read_to_string(std::env::var_os("GENDB_ACCEPTED_KEYS").expect("GENDB_ACCEPTED_KEYS")).unwrap()).unwrap();
        let scratch = crate::controller::test_support::scratch_root("t5-accepted-keys");
        let parser = SqlParser::from_environment().unwrap();
        let mut mismatches = vec![];
        for record in list["records"].as_array().unwrap() {
            let query = record["query"].as_u64().unwrap();
            let request: WorkloadRequest = serde_json::from_str(&std::fs::read_to_string(record["request"].as_str().unwrap()).unwrap()).unwrap();
            let statement = &request.queries[record["query_index"].as_u64().unwrap() as usize];
            assert!(request.integrity_constraints.is_none(), "q{query}: accepted requests declare no constraints");
            let prepared = prepare_statement(&parser, &request.dataset, None, &statement.sql, &statement.parameters, &[], &[], &scratch.join(format!("q{query}"))).unwrap();
            let store = ObjectStore::open_existing(&request.library).unwrap();
            let found = match admitted_package(&store, &prepared.instance).unwrap() {
                Some(AdmittedPackage::StoredDataV4 { resolved, constraints, .. }) => Some((resolved.admission.package.to_hex(), "stored_data_v4", constraints)),
                Some(AdmittedPackage::SavedV3 { resolved, constraints, .. }) => Some((resolved.admission.package.to_hex(), "saved_v3", constraints)),
                None => None,
            };
            let result = json!({"query":query,"statement_key":prepared.key_id,"statement_key_v4":prepared.key_v4_id,
                "key_equal":prepared.key_v4_id == record["recorded_statement_key"],"package":found.as_ref().map(|f| &f.0),"route":found.as_ref().map(|f| f.1),
                "package_equal":found.as_ref().is_some_and(|f| f.0 == record["selected_package"] && f.2 == DeclaredConstraints::None)});
            println!("{result}");
            if result["key_equal"] != true || result["package_equal"] != true {
                mismatches.push(result);
            }
        }
        assert!(mismatches.is_empty(), "{mismatches:?}");
    }
}
