//! One stored copy of each column's values under `physical_only` revision 2: each `(table, column)`
//! is `base_payload` of at most one storage of the serving storage.
//!
//! The check reads declarations and library records only (no data, no hashes, no source text):
//! - a new storage's payload is the columns its manifest declares as `base_payload`. Several parts of one storage
//!   naming a column are, by that declaration, one copy (an encoding over codes, dictionary and offsets, or disjoint
//!   partitions). `index_keys`, `permutation`, `own_skip_metadata` and `layout_offsets_counts` parts hold no payload;
//! - the serving storage is the set the storage budget counts (`storage::budget::serving_storages`: usable admitted
//!   versions that are current after the submission's replacements or are read by an admitted query package, here only
//!   those applicable to the run; in an engine library exactly the storages the selected engine version reads, and for
//!   an engine version under admission the storages it reads, [`engine_serving_payload`]), user-listed packages
//!   included, plus the storages they extend (`built_from.extends`: the source's parts are inside the extension by hard
//!   link, and are declared once, by the source);
//! - an admitted storage's payload is its recorded `base_payload` columns when it was registered under exactly
//!   revision 2, else (an earlier registration, usable only when the user lists it) every column it declares,
//!   conservatively, except those of the storage it extends;
//! - a storage and its re-verifications (same author sources, made by the framework) are one holder.
//!
//! One predicate ([`check_single_copy`]): the serving storage as it would stand after the state change holds each
//! column once. Refused (`storage_payload_duplicate`): a column two new storages of one submission both hold, a column
//! a new storage holds that a serving storage (another package; for a candidate without a package, another name)
//! already stores, and a column the serving storage itself already stores twice (user listings of earlier
//! registrations). Applied before every verified or diagnostic storage build (package unknown, so versions of the
//! candidate's own name are left to the later checks), at every evaluation and registration of storages, and at a
//! query's evaluation and admission with its storage uses as the new holders (a pinned older version of a name beside
//! its current version would be a second copy; checked under the library budget lock, so no storage replacement races
//! it), and when a package is served (its uses together). The re-verification of an admitted storage is not a new copy
//! and is not checked.
//!
//! What this establishes: the declarations of the serving storage and the new storages never name one column's values
//! twice across storages. It does not prove that builder code follows the policy: whether a part is what it declares
//! (an `index_keys` part carrying no other column, one copy spread over several parts of one storage) is decided by
//! review of the published sources; Verus does not check it.

use super::budget::{engine_serving_storages, serving_storages};
use super::catalog::{AdmittedStorage, admitted_storage, description_of};
use super::manifest::{DataPolicy, PartKind, StorageManifest};
use super::policy::{StoredDataPolicy, registered_current_revision};
use super::reverify::reverified_package;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::TableDef;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::AdmissionError;
use gendb_verification::obligations::DeclaredSource;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// One column of one table.
pub type Column = (String, String);

/// The payload columns one storage holds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PayloadHolder {
    pub name: String,
    /// `None`: a candidate before its package is known.
    pub package: Option<ContentId>,
    /// The package and the packages it re-verifies: one holder.
    pub lineage: BTreeSet<ContentId>,
    pub columns: BTreeSet<Column>,
    /// `false`: an earlier registration without a revision-2 declaration, counted as storing every declared column.
    pub declared: bool,
}

impl PayloadHolder {
    /// The `base_payload` columns `manifest` declares (none for the free-text form, which `physical_only` refuses).
    pub fn of_manifest(manifest: &StorageManifest, package: Option<ContentId>) -> Result<Self, AdmissionError> {
        let columns = payload_parts(manifest)?.into_keys().collect();
        Ok(Self { name: manifest.name.clone(), package, lineage: package.into_iter().collect(), columns, declared: true })
    }

    fn describe(&self) -> String {
        let package = self.package.map(|p| format!(" ({p})")).unwrap_or_default();
        let how = if self.declared { "declared base_payload" } else { "registered before revision 2, so every column it declares counts as stored payload" };
        format!("{}{package}, {how}", self.name)
    }

    /// Whether `other` is the same storage: the same package or a re-verification of it, or for a candidate without
    /// a package, the same name (decided once the package is known).
    fn same_storage(&self, other: &PayloadHolder) -> bool {
        match self.package {
            Some(_) => !self.lineage.is_disjoint(&other.lineage),
            None => self.name == other.name,
        }
    }

    fn shared_column(&self, other: &PayloadHolder) -> Option<Column> {
        self.columns.intersection(&other.columns).next().cloned()
    }
}

/// One admitted storage of the serving storage as the library records it: what its payload is computed from.
#[derive(Clone, Debug)]
pub struct RecordedStorage {
    pub name: String,
    pub package: ContentId,
    pub declaration: DeclaredSource,
    /// Its registration description (recorded policy standing and `data_policy`).
    pub description: Value,
    /// The package of the source it `extends`.
    pub extends: Option<ContentId>,
    /// The packages it re-verifies, nearest first.
    pub reverifies: Vec<ContentId>,
}

/// `(table, column) -> parts` of the `base_payload` declarations of `manifest`.
pub fn payload_parts(manifest: &StorageManifest) -> Result<BTreeMap<Column, Vec<usize>>, AdmissionError> {
    let mut columns: BTreeMap<Column, Vec<usize>> = BTreeMap::new();
    for entry in manifest.part_policies()?.unwrap_or_default() {
        if entry.kind == PartKind::BasePayload {
            for column in &entry.columns {
                columns.entry((entry.table.clone(), column.clone())).or_default().push(entry.part);
            }
        }
    }
    Ok(columns)
}

/// `storage_check`'s per-column summary for review: for every column a part names, the parts holding its one copy
/// (`base_payload`), indexing it as a key (`index_keys`) and describing it otherwise.
pub fn column_report(manifest: &StorageManifest) -> Result<Value, AdmissionError> {
    let mut report: BTreeMap<String, Value> = BTreeMap::new();
    for entry in manifest.part_policies()?.unwrap_or_default() {
        let role = match entry.kind {
            PartKind::BasePayload => "payload_parts",
            PartKind::IndexKeys => "index_key_parts",
            _ => "metadata_parts",
        };
        for column in &entry.columns {
            let slot = report.entry(format!("{}.{column}", entry.table)).or_insert_with(|| json!({"payload_parts":[],"index_key_parts":[],"metadata_parts":[]}));
            slot[role].as_array_mut().expect("initialized").push(json!(entry.part));
        }
    }
    Ok(json!(report))
}

/// The payload of the serving storage as it will stand once new versions of the names `replacing` are registered,
/// with the storages they extend.
pub fn serving_payload(
    store: &ObjectStore,
    capture: &CurrentCapture,
    schema: &[TableDef],
    policy: &StoredDataPolicy,
    replacing: &BTreeSet<String>,
) -> Result<Vec<PayloadHolder>, AdmissionError> {
    let (serving, _) = serving_storages(store, capture, schema, policy, replacing)?;
    payload_of_serving(store, &serving)
}

/// The payload of an engine library's serving storage as it will stand once an engine version reading the storage
/// packages `uses` is selected (`storage::budget::engine_serving_storages`), with the storages they extend. A
/// re-layout of a stored table is accepted against it exactly when that version no longer reads the old storage.
pub fn engine_serving_payload(
    store: &ObjectStore,
    capture: &CurrentCapture,
    schema: &[TableDef],
    policy: &StoredDataPolicy,
    uses: &BTreeSet<ContentId>,
) -> Result<Vec<PayloadHolder>, AdmissionError> {
    let (serving, _) = engine_serving_storages(store, capture, schema, policy, uses)?;
    payload_of_serving(store, &serving)
}

/// The payload holders of `serving` (from `serving_storages`; those applicable to the run) and what they extend.
pub fn payload_of_serving(store: &ObjectStore, serving: &[AdmittedStorage]) -> Result<Vec<PayloadHolder>, AdmissionError> {
    let roots = serving.iter().filter(|s| s.applicability.is_ok()).map(|s| (s.package.name.clone(), s.package_id)).collect();
    Ok(payload_holders(&recorded_storages(store, roots)?))
}

/// Serving applicability of one package under `physical_only`: the storages it reads (and what they extend) together
/// hold each column once, else the named `storage_payload_duplicate` reason.
pub fn uses_holding_a_column_twice(store: &ObjectStore, uses: Vec<(String, ContentId)>) -> Result<Option<String>, AdmissionError> {
    Ok(check_single_copy(&[], &payload_holders(&recorded_storages(store, uses)?)).err().map(|refusal| refusal.message))
}

/// The admitted storages `roots` (`(name, package)`) and, transitively, the storages they extend, as the library
/// records them (each package once).
pub fn recorded_storages(store: &ObjectStore, roots: Vec<(String, ContentId)>) -> Result<Vec<RecordedStorage>, AdmissionError> {
    let mut pending = roots;
    let mut seen = BTreeSet::new();
    let mut recorded = vec![];
    while let Some((name, package)) = pending.pop() {
        if !seen.insert(package) {
            continue;
        }
        let (record, declaration) = admitted_storage(store, package)?;
        let extends = record.derived_from.as_ref().and_then(|d| d.extends.and_then(|k| d.sources.get(k)));
        if let Some(source) = extends {
            pending.push((source.name.clone(), source.package));
        }
        let mut reverifies = vec![];
        while let Some(original) = reverified_package(store, *reverifies.last().unwrap_or(&package), &name)? {
            if original == package || reverifies.contains(&original) {
                break;
            }
            reverifies.push(original);
        }
        let description = description_of(store, package, &name)?;
        recorded.push(RecordedStorage { name, package, declaration, description, extends: extends.map(|s| s.package), reverifies });
    }
    Ok(recorded)
}

/// The holders among `holders` that are not one of `serving` (no shared lineage): what a query's storage uses add to
/// the serving storage when it is admitted (for example an older version of a name it pins).
pub fn added_to(holders: Vec<PayloadHolder>, serving: &[PayloadHolder]) -> Vec<PayloadHolder> {
    holders.into_iter().filter(|h| serving.iter().all(|s| h.lineage.is_disjoint(&s.lineage))).collect()
}

/// The payload holders of recorded storages (pure): a revision-2 registration's declared `base_payload` columns; an
/// earlier one's declared columns except those of the storage it extends (when that storage is among `recorded`).
pub fn payload_holders(recorded: &[RecordedStorage]) -> Vec<PayloadHolder> {
    let declared_columns = |declaration: &DeclaredSource| -> BTreeSet<Column> {
        declaration.tables.iter().flat_map(|t| t.columns.iter().filter(|c| !c.row_count_only).map(|c| (t.name.clone(), c.name.clone()))).collect()
    };
    recorded
        .iter()
        .map(|storage| {
            let declared = registered_current_revision(&storage.description)
                .then(|| serde_json::from_value::<DataPolicy>(storage.description["data_policy"].clone()).ok())
                .flatten()
                .and_then(|policy| match policy {
                    DataPolicy::Parts(parts) => Some(parts),
                    DataPolicy::Text(_) => None,
                });
            let columns = match &declared {
                Some(parts) => parts.iter().filter(|p| p.kind == PartKind::BasePayload).flat_map(|p| p.columns.iter().map(|c| (p.table.clone(), c.clone()))).collect(),
                None => {
                    let inherited = storage.extends.and_then(|source| recorded.iter().find(|r| r.package == source)).map(|r| declared_columns(&r.declaration)).unwrap_or_default();
                    declared_columns(&storage.declaration).difference(&inherited).cloned().collect()
                }
            };
            PayloadHolder {
                name: storage.name.clone(),
                package: Some(storage.package),
                lineage: std::iter::once(storage.package).chain(storage.reverifies.iter().copied()).collect(),
                columns,
                declared: declared.is_some(),
            }
        })
        .collect()
}

/// The shared predicate: the serving storage as it would stand (`serving` plus `new`) holds each column once. Refuse
/// (`storage_payload_duplicate`) a column that two of the new holders `new` both hold, that a new holder holds and a
/// serving storage (another package and lineage; for a candidate without a package, another name) already stores, or
/// that two serving storages already both store (`new` may be empty: a query admission adding no storage).
pub fn check_single_copy(new: &[PayloadHolder], serving: &[PayloadHolder]) -> Result<(), AdmissionError> {
    let refusal = |column: Column, holder: &PayloadHolder, other: &PayloadHolder| {
        AdmissionError::refusal(format!(
            "storage_payload_duplicate: column {}.{} is base_payload of storage {} and is also stored by storage {}: under storage_policy physical_only each column's values are stored once across the serving storage. Keep the one copy: read that storage (built_from, or extends to add parts beside it) and add index_keys, a permutation or skip metadata for another access path",
            column.0,
            column.1,
            holder.describe(),
            other.describe()
        ))
    };
    for (index, holder) in new.iter().enumerate() {
        for other in new[index + 1..].iter().filter(|other| other.name != holder.name) {
            if let Some(column) = holder.shared_column(other) {
                return Err(refusal(column, holder, other));
            }
        }
        for other in serving.iter().filter(|s| !holder.same_storage(s)) {
            if let Some(column) = holder.shared_column(other) {
                return Err(refusal(column, holder, other));
            }
        }
    }
    for (index, holder) in serving.iter().enumerate() {
        for other in serving[index + 1..].iter().filter(|other| holder.lineage.is_disjoint(&other.lineage)) {
            if let Some(column) = holder.shared_column(other) {
                return Err(AdmissionError::refusal(format!(
                    "storage_payload_duplicate: the serving storage already stores column {}.{} twice, in {} and in {} (user-listed earlier registrations, or an older version of a name that an admitted query package still reads beside its current version); no new storage is admitted under storage_policy physical_only until one copy remains (the user's eligible_storages or exclusions)",
                    column.0,
                    column.1,
                    holder.describe(),
                    other.describe()
                )));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::manifest::StoredTable;

    fn manifest(name: &str, columns: &[&str], data_policy: Value) -> StorageManifest {
        let mut m = StorageManifest::example();
        m.name = name.into();
        m.tables = vec![StoredTable { table: "lineitem".into(), columns: columns.iter().map(|c| c.to_string()).collect() }];
        m.parts = (0..data_policy.as_array().unwrap().len()).map(|i| format!("part {i}")).collect();
        m.data_policy = serde_json::from_value(data_policy).unwrap();
        m
    }

    fn part(index: usize, kind: &str, columns: &[&str]) -> Value {
        json!({"part":index,"table":"lineitem","kind":kind,"columns":columns,"why":"own rows"})
    }

    fn holder(m: &StorageManifest, package: Option<u8>) -> PayloadHolder {
        PayloadHolder::of_manifest(m, package.map(|b| ContentId::from_bytes([b; 32]))).unwrap()
    }

    /// One copy of each column with key indexes, a permutation and skip metadata beside it is accepted, including a
    /// text column whose one copy spans codes, dictionary and offsets parts and an extension that only adds metadata.
    #[test]
    fn one_copy_with_index_keys_permutation_and_multi_part_encoding_is_accepted() {
        let physical = StoredDataPolicy::PhysicalOnly { eligible_storages: vec![] };
        let base = manifest("lineitem_base", &["l_orderkey", "l_shipdate", "l_comment"], json!([
            part(0, "base_payload", &["l_orderkey", "l_shipdate"]),
            part(1, "base_payload", &["l_comment"]), part(2, "base_payload", &["l_comment"]), part(3, "base_payload", &["l_comment"]),
            part(4, "index_keys", &["l_orderkey"]),
            part(5, "permutation", &["l_shipdate"]),
            part(6, "own_skip_metadata", &["l_shipdate"]),
            part(7, "layout_offsets_counts", &[]),
        ]));
        physical.check_declaration(&base).unwrap();
        assert_eq!(payload_parts(&base).unwrap()[&("lineitem".into(), "l_comment".into())], [1, 2, 3]);
        let report = column_report(&base).unwrap();
        assert_eq!(report["lineitem.l_orderkey"], json!({"payload_parts":[0],"index_key_parts":[4],"metadata_parts":[]}));
        // An extension over the admitted base adds a key index on a base column: its new parts hold no payload.
        let index = manifest("lineitem_by_partkey", &["l_orderkey"], json!([part(0, "index_keys", &["l_orderkey"])]));
        physical.check_declaration(&index).unwrap();
        let serving = [holder(&base, Some(1))];
        check_single_copy(&[holder(&index, None)], &serving).unwrap();
        check_single_copy(&[holder(&index, Some(2))], &serving).unwrap();
        // The already admitted base itself (same package), or a candidate version of its own name before the package is
        // known, is not a second copy.
        check_single_copy(&[holder(&base, Some(1))], &serving).unwrap();
        check_single_copy(&[holder(&base, None)], &serving).unwrap();
    }

    /// A second payload representation of a stored column is refused: in another storage of the serving storage, as
    /// a sibling of the same submission, and as a new version of a name while an admitted query reads the old one.
    #[test]
    fn a_second_payload_copy_is_refused() {
        let base = manifest("lineitem_base", &["l_orderkey", "l_shipdate"], json!([part(0, "base_payload", &["l_orderkey", "l_shipdate"])]));
        let sorted = manifest("lineitem_by_shipdate", &["l_shipdate"], json!([part(0, "base_payload", &["l_shipdate"])]));
        let serving = [holder(&base, Some(1))];
        let refused = check_single_copy(&[holder(&sorted, None)], &serving).unwrap_err().message;
        assert!(refused.starts_with("storage_payload_duplicate: column lineitem.l_shipdate") && refused.contains("lineitem_base"), "{refused}");
        assert!(check_single_copy(&[holder(&base, None), holder(&sorted, None)], &[]).unwrap_err().message.starts_with("storage_payload_duplicate"));
        assert!(check_single_copy(&[holder(&base, Some(3))], &serving).unwrap_err().message.starts_with("storage_payload_duplicate"));
    }

    /// Revision-1 kinds and payload or key parts without columns are refused under physical_only; registrations are
    /// current only under exactly revision 2.
    #[test]
    fn revision_1_declarations_and_other_revisions_are_not_current() {
        let physical = StoredDataPolicy::PhysicalOnly { eligible_storages: vec![] };
        let covering = manifest("orders_covering", &["l_orderkey"], json!([{"part":0,"table":"lineitem","kind":"own_index","why":"covering index"}]));
        assert!(physical.check_declaration(&covering).unwrap_err().message.starts_with("storage_policy_declaration_revision"));
        assert!(StoredDataPolicy::Unrestricted.check_declaration(&covering).is_ok());
        let unnamed = manifest("keys", &["l_orderkey"], json!([part(0, "index_keys", &[])]));
        assert!(physical.check_declaration(&unnamed).unwrap_err().message.starts_with("storage_policy_declaration_invalid"));
        let unstored = manifest("keys", &["l_orderkey"], json!([part(0, "base_payload", &["l_comment"])]));
        assert!(physical.check_declaration(&unstored).unwrap_err().message.starts_with("storage_policy_declaration_invalid"));

        use crate::storage::policy::{PHYSICAL_ONLY_REVISION, registration_ineligibility};
        let current = json!({"storage_policy":"physical_only","storage_policy_revision":PHYSICAL_ONLY_REVISION});
        assert_eq!(physical.standing(), current);
        assert_eq!(registration_ineligibility(&current), None);
        assert_eq!(registration_ineligibility(&json!({"storage_policy":"physical_only"})), Some("storage_policy_revision_superseded"));
        assert_eq!(registration_ineligibility(&json!({"storage_policy":"physical_only","storage_policy_revision":3})), Some("storage_policy_revision_unsupported"));
        assert_eq!(registration_ineligibility(&json!({"storage_policy":"unrestricted"})), Some("storage_policy_ineligible"));
    }

    fn recorded(name: &str, package: u8, columns: &[&str], description: Value, extends: Option<u8>, reverifies: &[u8]) -> RecordedStorage {
        let schema = vec![TableDef {
            name: "lineitem".into(),
            columns: ["l_orderkey", "l_shipdate", "l_comment"]
                .map(|n| gendb_frontend::ast::ColumnDef { name: n.into(), ty: gendb_frontend::ast::PgType::Int4, nullable: false })
                .to_vec(),
            constraints: vec![],
        }];
        let declaration = manifest(name, columns, json!([part(0, "base_payload", columns)])).declaration(&schema).unwrap();
        let id = |b: u8| ContentId::from_bytes([b; 32]);
        RecordedStorage { name: name.into(), package: id(package), declaration, description, extends: extends.map(id), reverifies: reverifies.iter().map(|b| id(*b)).collect() }
    }

    fn registered(data_policy: Value) -> Value {
        json!({"storage_policy":"physical_only","storage_policy_revision":2,"data_policy":data_policy})
    }

    /// The serving inventory as registration checks it: an index-only extension over an admitted base and the base's
    /// re-verification are one copy; a new version of the base name or another storage re-storing a base column is
    /// refused; a user-listed earlier registration counts every declared column it does not inherit, so listing it
    /// neither hides its payload nor lets two listed copies pass.
    #[test]
    fn serving_inventory_keeps_extensions_and_reverifications_and_counts_listed_payload() {
        let base = recorded("lineitem_base", 1, &["l_orderkey", "l_shipdate", "l_comment"], registered(json!([part(0, "base_payload", &["l_orderkey", "l_shipdate", "l_comment"])])), None, &[]);
        let base_reverified = recorded("lineitem_base", 2, &["l_orderkey", "l_shipdate", "l_comment"], registered(json!([part(0, "base_payload", &["l_orderkey", "l_shipdate", "l_comment"])])), None, &[1]);
        let by_key = recorded("lineitem_keyed", 3, &["l_orderkey", "l_shipdate", "l_comment"], registered(json!([part(0, "index_keys", &["l_orderkey"])])), Some(1), &[]);
        let serving = payload_holders(&[base, base_reverified, by_key]);
        assert!(serving[2].columns.is_empty(), "an index-only extension holds no payload of its own");
        // Registration of a new index-only extension (package known): accepted, the inventory is one copy.
        let index = manifest("lineitem_by_shipdate_keys", &["l_shipdate"], json!([part(0, "index_keys", &["l_shipdate"]), part(1, "permutation", &["l_shipdate"])]));
        check_single_copy(&[holder(&index, Some(9))], &serving).unwrap();
        // Registration of a re-sorted payload copy, or of a new base version while the others are served: refused.
        let sorted = manifest("lineitem_by_shipdate", &["l_shipdate"], json!([part(0, "base_payload", &["l_shipdate"])]));
        assert!(check_single_copy(&[holder(&sorted, Some(9))], &serving).unwrap_err().message.starts_with("storage_payload_duplicate: column lineitem.l_shipdate"));
        let base_v3 = manifest("lineitem_base", &["l_shipdate"], json!([part(0, "base_payload", &["l_shipdate"])]));
        assert!(check_single_copy(&[holder(&base_v3, Some(8))], &serving).is_err());

        // User-listed earlier registrations: a legacy base and a legacy extension adding a covering copy of l_shipdate.
        let legacy = json!({"storage_policy":"physical_only","data_policy":[part(0, "own_source_values", &[])]});
        let old_base = recorded("old_base", 4, &["l_orderkey", "l_comment"], legacy.clone(), None, &[]);
        let old_extension = recorded("old_by_date", 5, &["l_orderkey", "l_shipdate", "l_comment"], legacy.clone(), Some(4), &[]);
        let listed = payload_holders(&[old_base.clone(), old_extension]);
        assert_eq!(listed[1].columns, BTreeSet::from([("lineitem".to_string(), "l_shipdate".to_string())]), "inherited columns are the source's");
        assert!(!listed[0].declared && listed[0].columns.len() == 2);
        assert!(check_single_copy(&[holder(&sorted, Some(9))], &listed).unwrap_err().message.contains("registered before revision 2"));
        check_single_copy(&[holder(&index, Some(9))], &listed).unwrap();
        // Two listed copies of one column: no new storage passes while both are served.
        let old_copy = recorded("old_copy", 6, &["l_comment"], legacy, None, &[]);
        let doubled = payload_holders(&[old_base, old_copy]);
        assert!(check_single_copy(&[holder(&index, Some(9))], &doubled).unwrap_err().message.starts_with("storage_payload_duplicate: the serving storage already stores column lineitem.l_comment twice"));
    }

    /// Query admission (`check_query_storage_uses`'s predicate): the uses already serving add nothing; a pinned older
    /// version of a name beside its current version is a second copy; a query-only admission over two user-listed
    /// copies is refused although it builds no storage; serving applicability judges a package's uses together.
    #[test]
    fn query_uses_join_the_serving_storage_under_one_copy() {
        let all = ["l_orderkey", "l_shipdate", "l_comment"];
        let payload = registered(json!([part(0, "base_payload", &all)]));
        let current = recorded("lineitem_base", 1, &all, payload.clone(), None, &[]);
        let keyed = recorded("lineitem_keyed", 3, &all, registered(json!([part(0, "index_keys", &["l_orderkey"])])), Some(1), &[]);
        let serving = payload_holders(&[current.clone(), keyed.clone()]);
        let reads_serving = added_to(payload_holders(&[current.clone(), keyed]), &serving);
        assert!(reads_serving.is_empty());
        check_single_copy(&reads_serving, &serving).unwrap();
        let older = recorded("lineitem_base", 2, &all, payload, None, &[]);
        let pins_older = added_to(payload_holders(&[older.clone()]), &serving);
        assert!(check_single_copy(&pins_older, &serving).unwrap_err().message.contains("lineitem_base (0202"));
        // A re-verification of the current version pinned instead is the same holder.
        let reverified = recorded("lineitem_base", 4, &all, registered(json!([part(0, "base_payload", &all)])), None, &[1]);
        assert!(added_to(payload_holders(&[reverified]), &serving).is_empty());
        let legacy = json!({"storage_policy":"physical_only"});
        let listed = payload_holders(&[recorded("old_a", 5, &["l_comment"], legacy.clone(), None, &[]), recorded("old_b", 6, &["l_comment"], legacy, None, &[])]);
        assert!(check_single_copy(&[], &listed).unwrap_err().message.contains("already stores column lineitem.l_comment twice"));
        assert!(check_single_copy(&[], &payload_holders(&[current, older])).is_err(), "one package reading both versions is not served");
    }
}
