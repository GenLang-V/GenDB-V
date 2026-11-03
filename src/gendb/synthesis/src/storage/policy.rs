//! The user's stored-data policy of a workload run (request `storage_policy`): which kinds of prepared data an
//! admitted storage may hold before the measured query call. This module is the one source of the policy's wording;
//! prompts, task files, manifests and docs quote or point to it.
//!
//! - `unrestricted` (default, the historical behaviour): any storage whose builder proves its `represents`, including
//!   pre-aggregates and other query-derived parts.
//! - `physical_only` (revision 2): each table's source rows stored once, in one physical
//!   organization chosen freely: layouts, sorting and clustering (every row kept), partitioning, lossless encodings and
//!   compression. Beside that one copy only metadata: each table's own indexes (key values -> own row positions or
//!   ranges, no other column's values), permutations (row positions only, another order), skipping metadata and layout
//!   offsets/counts over its own rows, readers over them. No second copy of any column (full or partial, re-sorted or
//!   re-encoded), no covering index payload, no materialized query computation (query-derived payloads or filtered
//!   result tables, materialized joins, cross-table row locators even when position-only, precomputed subquery
//!   answers, aggregates, prefix sums or cached answers). A table's row order may be chosen with another table in mind,
//!   but nothing stored records a correspondence between two tables' rows; a query relying on aligned rows checks their
//!   keys at runtime. Filtering, joins and aggregation inside each measured call remain allowed and timed. Revision 1
//!   (earlier registrations, with no recorded revision) also allowed own-table copies and covering indexes.
//!
//! - `fixed_flat` (the plain-array storage ablation): no storage is designed. GenDB prepares one fixed flat
//!   storage per table (`storage::flat`): every column as a plain typed array in source row order, written by the
//!   framework, never by an author. Query authors read only those; storage tools, workspace storages and other
//!   admitted storages are refused (`storage::flat` documents every enforcement route).
//!
//! This is a benchmark policy, not a verified property: Verus proves what a storage and a query compute (total
//! correctness relative to their outcome contracts), not which category a stored part belongs to. Enforcement is
//! transparent declaration plus reviewable evidence, failing closed on unknown storage:
//! 1. every storage checked or built under `physical_only` must carry the manifest's `data_policy` declaration (per
//!    part, the one table it is computed from, which allowed kind it is and its columns), recorded with its
//!    registration together with the run's policy kind and revision;
//! 2. each column is `base_payload` of at most one storage of the serving storage (`storage::payload`): checked from
//!    declarations before a build, and authoritatively at every evaluation and registration;
//! 3. an admitted storage is eligible only when its registration recorded `physical_only` revision 2 exactly, or when
//!    the user lists its package in `eligible_storages` with a review note (a listed package still takes part in the
//!    one-copy check of 2), and in either case the user has not excluded it (`storage::exclusion`: a persistent library record that wins over both). A re-verification has the
//!    standing of the package it re-verifies. A library may hold other storages: authors are offered only eligible
//!    ones (`storages.json`) and only earlier query packages whose storages are all eligible (`verus-library.json`);
//!    every evaluation refuses an ineligible admitted use, a workspace storage whose package is excluded is refused
//!    before its asset is built, qualification refuses an ineligible use, and serving refuses a package that reads one.
//!
//! Whether a declaration is true (a part labelled `index_keys`, `permutation` or one multi-part copy really is one) is
//! decided by review of the published builder and reader sources.

use super::catalog::description_of;
use super::flat::{self, FIXED_FLAT};
use gendb_verification::obligations::FLAT_STORAGE_GENERATOR;
use super::exclusion::exclusion_of;
use super::reverify::reverified_package;
use super::manifest::{PartKind, StorageManifest};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_verification::admission::AdmissionError;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

/// `kind` of the physical-only policy, as recorded with every storage registered under it.
pub const PHYSICAL_ONLY: &str = "physical_only";
/// `kind` of the default policy.
pub const UNRESTRICTED: &str = "unrestricted";
/// The current revision of `physical_only`, recorded with every storage registered under it
/// (`storage_policy_revision`). Revision 1 (no recorded field; earlier registrations) allowed
/// own-table copies and covering indexes; revision 2 stores each table's payload once.
pub const PHYSICAL_ONLY_REVISION: u64 = 2;

/// Allowed before the measured call under `physical_only`.
const PHYSICAL_ALLOWED: [&str; 6] = [
    "each table's source rows stored ONCE (base_payload): every stored column in one copy, in any column layout, partitioning, sorting or clustering (every row kept), with lossless encodings and compression; one copy may span several parts (codes, dictionary, offsets, values; disjoint partitions). Co-clustering is allowed: a table's row order may follow another table's order, provided nothing cross-table is stored and a query relying on aligned rows checks their keys at run time",
    "indexes of one table (index_keys): that table's own key values -> that table's own row positions or ranges; the key values may repeat values of the stored copy, but an index carries no other column's values",
    "permutations of one table (permutation): row positions only, into the one stored copy, giving another sort order",
    "skipping metadata computed from one table's own rows or blocks, such as per-block min/max (zone maps), per-row or per-block Bloom filters over its own values (including trigram Bloom filters for LIKE) and statistics",
    "stored run offsets, row counts and block offsets that describe the representation itself, even when the layout's groups match a query's GROUP BY (a sorted, run-length-encoded layout gives group sizes for free, as in column stores); queries still read and combine the actual values, and stored aggregates of values stay excluded",
    "readers over those representations",
];
/// Excluded under `physical_only`.
const PHYSICAL_EXCLUDED: [&str; 8] = [
    "a second copy of any column's values, full or partial, in any order or encoding, in the same or another storage (for example a re-sorted copy of a table or of some of its columns): keep another order as a permutation",
    "covering indexes: an index that carries copies of columns other than its keys",
    "stored query-derived payload values (expression results such as price*(1-discount)) or tables holding only a predicate's matching rows",
    "materialized joins or denormalized results (a row's values from another table copied beside it, join results)",
    "cross-table row locators, even when they store only positions: join indexes or row-match maps from one table's rows or keys to another table's matching rows, positions or ranges, and stored positions of another table's rows",
    "precomputed EXISTS/NOT EXISTS/IN flags or other subquery answers",
    "aggregate summaries: group or block sums/counts, prefix sums or counts, aggregate value bounds (such as revenue bounds), cubes",
    "cached answers, or any state carried across measured calls",
];

/// Where `physical_only` draws the line (the author view's `boundary`).
const PHYSICAL_BOUNDARY: &str = "Each column's values are stored once across the serving storage (base_payload); everything else stored is metadata over that one copy: index keys with own row positions or ranges, permutations (row positions only), skip metadata and layout offsets/counts. Every stored value, index entry and metadata entry holds or describes one table's own source rows. The only allowed influence of another table is the choice of a table's row order (clustering, every row kept; keys used only to choose the order are not stored). Nothing stored records a correspondence between two tables' rows: no other table's values, keys or row positions and no match ranges or join indexes, whether or not values are copied; a query that relies on two tables' rows lining up checks their key values at runtime, and joins are computed inside the measured call. An index or metadata part must locate or bound its own table's rows, not carry a query's answer, computed payload or other columns' values; sorting source rows is allowed, storing only a query's selected rows is not. When a structure is uncertain, choose the conservative form and say why in data_policy";

/// What the choice among stored organizations covers under the policy `kind` (both roles' prompts and task files).
pub fn storage_choices(kind: &str) -> &'static str {
    if kind == FIXED_FLAT {
        "nothing: the stored organization is fixed (storage_policy fixed_flat: one plain typed array per column, in source row order)"
    } else if kind == PHYSICAL_ONLY {
        "formats, encodings, compression, ordering and partitioning of the one stored copy of each table's source rows, blocks, and each table's own key indexes, permutations and skip metadata (storage_policy physical_only: each column's values stored once, no covering index payload, no materialized query computation, no cross-table row locators)"
    } else {
        "formats, encodings, compression, ordering, blocks, indexes, skip metadata and pre-aggregates"
    }
}

/// One admitted storage package the user reviewed and admits into a `physical_only` run.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EligibleStorage {
    pub package: ContentId,
    /// Who reviewed what (the builder and reader sources) and why it holds no materialized query computation and no
    /// second payload copy (the current revision's rule; a listing also admits the package's re-verifications).
    pub review: String,
}

/// The request's stored-data policy. JSON: absent or `{"kind": "unrestricted"}`,
/// `{"kind": "physical_only", "eligible_storages": [{"package", "review"}]}`, or `{"kind": "fixed_flat"}`. The user's exclusions are library
/// records (`storage::exclusion`), not request fields, so every request over the library honors them.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum StoredDataPolicy {
    #[default]
    Unrestricted,
    PhysicalOnly {
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        eligible_storages: Vec<EligibleStorage>,
    },
    /// The fixed flat storages only (`storage::flat`).
    FixedFlat {},
}

impl StoredDataPolicy {
    pub fn is_unrestricted(&self) -> bool {
        *self == StoredDataPolicy::Unrestricted
    }

    pub fn kind(&self) -> &'static str {
        match self {
            StoredDataPolicy::Unrestricted => UNRESTRICTED,
            StoredDataPolicy::PhysicalOnly { .. } => PHYSICAL_ONLY,
            StoredDataPolicy::FixedFlat {} => FIXED_FLAT,
        }
    }

    /// Whether the run reads only the fixed flat storages (no storage is designed, built or registered by an author).
    pub fn is_fixed_flat(&self) -> bool {
        *self == StoredDataPolicy::FixedFlat {}
    }

    /// Whether each column must be stored once across the serving storage (`physical_only`: per-part declarations and
    /// the one-copy check of `storage::payload`).
    pub fn stores_columns_once(&self) -> bool {
        matches!(self, StoredDataPolicy::PhysicalOnly { .. })
    }

    /// Each listed package once, with a review note.
    pub fn validate(&self) -> Result<(), String> {
        let StoredDataPolicy::PhysicalOnly { eligible_storages } = self else { return Ok(()) };
        let mut seen = std::collections::BTreeSet::new();
        for listed in eligible_storages {
            if listed.review.trim().is_empty() || !seen.insert(listed.package) {
                return Err(format!("eligible_storages: package {} needs one entry with a nonempty review", listed.package));
            }
        }
        Ok(())
    }

    /// [`Self::author_view`] for a dataset schema with a nullable column (`nullable`): under `physical_only` it says
    /// that a column's validity part is part of its one copy, under `fixed_flat` that a nullable column has a validity
    /// part ([`flat::author_view_for`]). Without a nullable column it is `author_view`, byte for byte.
    pub fn author_view_for(&self, nullable: bool) -> Value {
        match self {
            StoredDataPolicy::PhysicalOnly { .. } if nullable => {
                let mut view = self.author_view();
                view["nullable"] = json!("a nullable column's validity part (which rows are NULL) is base_payload of that column, part of its one stored copy");
                view
            }
            StoredDataPolicy::FixedFlat {} => flat::author_view_for(nullable),
            _ => self.author_view(),
        }
    }

    /// The policy as both roles read it (prompt facts, `stored-data.json`, the workload summary).
    pub fn author_view(&self) -> Value {
        match self {
            StoredDataPolicy::Unrestricted => json!({"kind":UNRESTRICTED,
                "meaning":"any storage whose builder proves its `represents` may be admitted, including pre-aggregates and other derived parts"}),
            StoredDataPolicy::PhysicalOnly { eligible_storages } => json!({"kind":PHYSICAL_ONLY,"revision":PHYSICAL_ONLY_REVISION,
                "meaning":"store each table's source rows once and optimize the physical organization of that one copy freely; beside it keep only own-table key indexes, permutations and skip metadata; do not store a second copy of any column, covering index payload, query computation or cross-table correspondences before the measured call",
                "allowed":PHYSICAL_ALLOWED,"excluded":PHYSICAL_EXCLUDED,
                "boundary":PHYSICAL_BOUNDARY,
                "runtime":"filtering, joins, aggregation, sorting and temporary structures built inside each measured query call are allowed and timed; nothing computed in one call may be kept for a later call",
                "declaration":"every storage manifest needs data_policy: one entry {part, table, kind, columns, why} per part: the one stored table whose rows it is computed from; its kind: base_payload (part of the one stored copy of `columns`; one copy may span several parts of the storage, each listing the column), index_keys (key `columns` -> own row positions or ranges, no other column's values), permutation (row positions only), own_skip_metadata or layout_offsets_counts (query_derived_values and the revision-1 kinds own_source_values/own_index are refused); `columns`: stored columns of that table, required for base_payload and index_keys; and why it holds no query computation and no second copy. storage_check reports each part and, per column, which parts hold its payload or keys; the declaration is recorded with the storage and its published sources are reviewed; a storage without it is refused (storage_policy_declaration_missing), a malformed one too (storage_policy_declaration_invalid, storage_policy_declaration_revision)",
                "single_copy":"each column is base_payload of at most one storage of the serving storage (the storages storage-budget.json counts, and the storages they extend). A storage declaring base_payload for a column another serving storage already stores is refused (storage_payload_duplicate): before its build (storage_check, storage_build, verified or unverified diagnostic) against storages of other names, and at every evaluation and registration together with the other storages of the submission. A query package is refused at evaluation and admission when its storage uses would add a second copy to the serving storage (for example an older version of a storage pinned beside its current version), and a package whose storages together hold a column twice is not served. Parts inherited through built_from.extends are the source's, so an extension that adds index_keys, permutation or skip metadata parts over an admitted storage reuses its copy. An admitted storage registered before this revision counts as storing every column it declares",
                "admitted_storages":"only storages registered under physical_only revision 2, or reviewed packages the user lists, are offered (storages.json) and usable; storages registered under an earlier revision (which allowed second copies and covering indexes) are not (storage_policy_revision_superseded); earlier query code and measurements are offered only for packages over usable storages (verus-library.json)",
                "user_excluded":"a storage package the user's review excluded under physical_only is neither offered nor usable, even if registered under it or listed: storages.json excluded_by_storage_policy counts it, and a workspace storage with the same package is refused (storage_policy_excluded)",
                "reviewed_packages":eligible_storages,
                "not_a_proof":"Verus proves what your code computes, not this classification; the one-copy check reads your declaration, and whether each part is what it declares is checked by review of the declaration and sources"}),
            StoredDataPolicy::FixedFlat {} => flat::author_view(),
        }
    }

    /// What a registration under this policy records with the storage, beside the author's description:
    /// `storage_policy`, and under `physical_only` its `storage_policy_revision`.
    pub fn standing(&self) -> Value {
        match self {
            StoredDataPolicy::Unrestricted => json!({"storage_policy":UNRESTRICTED}),
            StoredDataPolicy::PhysicalOnly { .. } => json!({"storage_policy":PHYSICAL_ONLY,"storage_policy_revision":PHYSICAL_ONLY_REVISION}),
            StoredDataPolicy::FixedFlat {} => json!({"storage_policy":FIXED_FLAT,"generator":FLAT_STORAGE_GENERATOR}),
        }
    }

    /// A storage checked or built under `physical_only` must declare, per part, the stored table it is computed from,
    /// a current allowed kind and, for `base_payload` and `index_keys`, its columns (`manifest.data_policy`, checked
    /// by `StorageManifest::part_policies`); `query_derived_values`, the revision-1 kinds and the free-text form are
    /// refused there. Under `unrestricted` a given per-part list must still be well formed. Whether each column is
    /// stored once is `storage::payload`'s check.
    pub fn check_declaration(&self, manifest: &StorageManifest) -> Result<(), AdmissionError> {
        let name = &manifest.name;
        if self.is_fixed_flat() {
            return Err(AdmissionError::refusal(format!(
                "fixed_flat_storage_tools_unavailable: storage {name}: under storage_policy fixed_flat no storage is designed or built by an author; queries read the prepared flat storages"
            )));
        }
        let parts = manifest.part_policies()?;
        if self.is_unrestricted() {
            return Ok(());
        }
        let Some(parts) = parts.filter(|p| !p.is_empty()) else {
            return Err(AdmissionError::refusal(format!(
                "storage_policy_declaration_missing: storage {name} has no per-part data_policy; under storage_policy physical_only each storage manifest declares, for every part, {{part, table, kind, columns, why}}: the one stored table it is computed from, which allowed kind it is and its columns (stored-data.json storage_policy)"
            )));
        };
        for entry in parts {
            if entry.kind == PartKind::QueryDerivedValues {
                return Err(AdmissionError::refusal(format!(
                    "storage_policy_declaration_invalid: storage {name} declares part {} as query_derived_values, which storage_policy physical_only excludes",
                    entry.part
                )));
            }
            if entry.kind.is_revision_1() {
                return Err(AdmissionError::refusal(format!(
                    "storage_policy_declaration_revision: storage {name} declares part {} as {}, a kind of physical_only revision 1; revision {PHYSICAL_ONLY_REVISION} stores each column once: declare base_payload (part of the one copy of its columns), index_keys (key columns -> own row positions, no other values), permutation (row positions only), own_skip_metadata or layout_offsets_counts",
                    entry.part,
                    entry.kind.name()
                )));
            }
            if entry.kind.names_columns() && entry.columns.is_empty() {
                return Err(AdmissionError::refusal(format!(
                    "storage_policy_declaration_invalid: storage {name} declares part {} as {} without columns: name the stored columns of {} whose {} it holds",
                    entry.part,
                    entry.kind.name(),
                    entry.table,
                    if entry.kind == PartKind::BasePayload { "values" } else { "key values" }
                )));
            }
        }
        Ok(())
    }

    /// Why the user excluded storage `package` under this policy (`None`: not excluded; never under `unrestricted`).
    /// Reads the library's persistent exclusions (`storage::exclusion`), so it holds for every request over `store`.
    pub fn excluded(&self, store: &ObjectStore, package: ContentId) -> Result<Option<String>, AdmissionError> {
        if !self.stores_columns_once() {
            return Ok(None);
        }
        Ok(exclusion_of(store, PHYSICAL_ONLY, package)?.map(|(record, exclusion)| {
            format!(
                "storage_policy_excluded: storage package {package} ({}) is excluded under physical_only by the user's review (exclusion record {record}): {}",
                exclusion.storage, exclusion.reason
            )
        }))
    }

    /// Refuse a storage `package` the user excluded under this policy (a workspace storage checked before its asset is
    /// built, or any storage use at qualification).
    pub fn refuse_excluded(&self, store: &ObjectStore, package: ContentId) -> Result<(), AdmissionError> {
        match self.excluded(store, package)? {
            Some(reason) => Err(AdmissionError::refusal(reason)),
            None => Ok(()),
        }
    }

    /// Why the admitted storage `package` (named `name`) may not be used under this policy (`None`: it may). Decided
    /// for the package and the packages it re-verifies (same author sources): a user exclusion of any of them wins
    /// over an `eligible_storages` entry and over the recorded registration; a listing of any of them admits it; else
    /// its recorded registration decides ([`registration_ineligibility`]).
    pub fn ineligible(&self, store: &ObjectStore, package: ContentId, name: &str) -> Result<Option<String>, AdmissionError> {
        if self.is_fixed_flat() {
            return flat::flat_ineligibility(store, package, name);
        }
        let StoredDataPolicy::PhysicalOnly { eligible_storages } = self else { return Ok(None) };
        let mut lineage = vec![package];
        while let Some(origin) = reverified_package(store, *lineage.last().expect("nonempty"), name)? {
            if lineage.contains(&origin) {
                break;
            }
            lineage.push(origin);
        }
        for member in &lineage {
            if let Some(reason) = self.excluded(store, *member)? {
                return Ok(Some(reason));
            }
        }
        if eligible_storages.iter().any(|listed| lineage.contains(&listed.package)) {
            return Ok(None);
        }
        let recorded = description_of(store, package, name)?;
        Ok(registration_ineligibility(&recorded).map(|reason| format!("{reason}: admitted storage {name} ({package}) {}", registration_detail(&recorded))))
    }

    /// The first storage use (`(name, package)`) this policy excludes, as its named reason (`None`: every use may be
    /// read). Used for query packages: their dependency closure is their storage uses.
    pub fn ineligible_use<'a>(&self, store: &ObjectStore, uses: impl IntoIterator<Item = (&'a str, ContentId)>) -> Result<Option<String>, AdmissionError> {
        for (name, package) in uses {
            if let Some(reason) = self.ineligible(store, package, name)? {
                return Ok(Some(reason));
            }
        }
        Ok(None)
    }
}

/// The policy standing recorded with an admitted storage (its registration `description`): `storage_policy` and, when
/// recorded, `storage_policy_revision`. A re-verification records the standing of the package it re-verifies.
pub fn recorded_standing(description: &Value) -> Value {
    let mut standing = json!({"storage_policy":description["storage_policy"]});
    if !description["storage_policy_revision"].is_null() {
        standing["storage_policy_revision"] = description["storage_policy_revision"].clone();
    }
    standing
}

/// The recorded revision of a `physical_only` registration (1 when none is recorded: registrations before revisions).
pub fn recorded_revision(description: &Value) -> u64 {
    description["storage_policy_revision"].as_u64().unwrap_or(1)
}

/// Whether registration `description` recorded exactly the current `physical_only` revision (an unknown later revision
/// is not assumed to mean the same).
pub fn registered_current_revision(description: &Value) -> bool {
    description["storage_policy"] == PHYSICAL_ONLY && recorded_revision(description) == PHYSICAL_ONLY_REVISION
}

/// The named reason an unlisted admitted storage with registration `description` is not usable under the current
/// `physical_only` (`None`: registered under exactly revision [`PHYSICAL_ONLY_REVISION`]).
pub fn registration_ineligibility(description: &Value) -> Option<&'static str> {
    if description["storage_policy"] != PHYSICAL_ONLY {
        Some("storage_policy_ineligible")
    } else if recorded_revision(description) < PHYSICAL_ONLY_REVISION {
        Some("storage_policy_revision_superseded")
    } else if recorded_revision(description) > PHYSICAL_ONLY_REVISION {
        Some("storage_policy_revision_unsupported")
    } else {
        None
    }
}

fn registration_detail(description: &Value) -> String {
    if description["storage_policy"] != PHYSICAL_ONLY {
        format!("was registered under storage policy {}, not physical_only, and is not in eligible_storages", description["storage_policy"])
    } else if recorded_revision(description) > PHYSICAL_ONLY_REVISION {
        format!("was registered under physical_only revision {}, which this GenDB does not know (it applies revision {PHYSICAL_ONLY_REVISION}), and is not in eligible_storages", recorded_revision(description))
    } else {
        format!(
            "was registered under physical_only revision {}, which allowed second payload copies and covering indexes; revision {PHYSICAL_ONLY_REVISION} stores each column once, and the package is not in eligible_storages (the user may list it after reviewing that it holds no second copy)",
            recorded_revision(description)
        )
    }
}

/// Each stored part of a storage manifest with its declared source table, kind and columns (`storage_check`'s report):
/// `table` and `kind` are null when the manifest uses the free-text form.
pub fn part_sources(manifest: &StorageManifest) -> Result<Vec<Value>, AdmissionError> {
    let declared = manifest.part_policies()?;
    Ok(manifest
        .parts
        .iter()
        .enumerate()
        .map(|(index, label)| {
            let entry = declared.as_ref().and_then(|d| d.iter().find(|p| p.part == index));
            json!({"part":index,"label":label,"table":entry.map(|e| &e.table),"kind":entry.map(|e| e.kind.name()),"columns":entry.map(|e| &e.columns)})
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn policy_defaults_to_unrestricted_and_physical_only_needs_declarations() {
        let omitted: StoredDataPolicy = serde_json::from_value(json!({"kind":"unrestricted"})).unwrap();
        assert!(omitted.is_unrestricted() && StoredDataPolicy::default().is_unrestricted());
        let physical: StoredDataPolicy = serde_json::from_value(json!({"kind":"physical_only"})).unwrap();
        assert_eq!(physical.kind(), PHYSICAL_ONLY);
        assert!(physical.validate().is_ok());
        let mut manifest = super::super::manifest::StorageManifest::example();
        manifest.tables[0].table = "t".into();
        manifest.data_policy = serde_json::from_value(json!([{"part":0,"table":"t","kind":"base_payload","columns":["<column>"],"why":"the one sorted copy"}])).unwrap();
        assert!(physical.check_declaration(&manifest).is_ok());
        let mut revision_1 = manifest.clone();
        revision_1.data_policy = serde_json::from_value(json!([{"part":0,"table":"t","kind":"own_source_values","why":"sorted copy"}])).unwrap();
        assert!(physical.check_declaration(&revision_1).unwrap_err().message.starts_with("storage_policy_declaration_revision"));
        let mut text = manifest.clone();
        text.data_policy = serde_json::from_value(json!("part 0: day column sorted")).unwrap();
        assert!(physical.check_declaration(&text).unwrap_err().message.starts_with("storage_policy_declaration_missing"));
        assert!(StoredDataPolicy::Unrestricted.check_declaration(&text).is_ok());
        let mut other_table = manifest.clone();
        other_table.data_policy = serde_json::from_value(json!([{"part":0,"table":"u","kind":"index_keys","columns":["<column>"],"why":"x"}])).unwrap();
        assert!(physical.check_declaration(&other_table).unwrap_err().message.starts_with("storage_policy_declaration_invalid"));
        let mut derived = manifest.clone();
        derived.data_policy = serde_json::from_value(json!([{"part":0,"table":"t","kind":"query_derived_values","why":"sums"}])).unwrap();
        assert!(physical.check_declaration(&derived).is_err() && StoredDataPolicy::Unrestricted.check_declaration(&derived).is_ok());
        assert!(!storage_choices(physical.kind()).contains("pre-aggregates") && storage_choices(UNRESTRICTED).contains("pre-aggregates"));
        assert!(serde_json::from_value::<StoredDataPolicy>(json!({"kind":"physical_only","extra":1})).is_err());
        let package = ContentId::from_bytes([7; 32]);
        let twice = StoredDataPolicy::PhysicalOnly { eligible_storages: vec![EligibleStorage { package, review: "r".into() }; 2] };
        assert!(twice.validate().is_err());
        let unreviewed = StoredDataPolicy::PhysicalOnly { eligible_storages: vec![EligibleStorage { package, review: " ".into() }] };
        assert!(unreviewed.validate().is_err());
    }

    /// `fixed_flat` takes no fields, records its generator, refuses every author storage declaration, has no user
    /// exclusions and admits no package that is not a generated flat storage (here: one the library does not hold).
    #[test]
    fn fixed_flat_refuses_author_storages_and_unknown_packages() {
        let flat: StoredDataPolicy = serde_json::from_value(json!({"kind":"fixed_flat"})).unwrap();
        assert!(flat.is_fixed_flat() && !flat.stores_columns_once() && flat.kind() == FIXED_FLAT && flat.validate().is_ok());
        assert!(serde_json::from_value::<StoredDataPolicy>(json!({"kind":"fixed_flat","eligible_storages":[]})).is_err());
        assert_eq!(flat.standing(), json!({"storage_policy":"fixed_flat","generator":FLAT_STORAGE_GENERATOR}));
        let refused = flat.check_declaration(&super::super::manifest::StorageManifest::example()).unwrap_err();
        assert!(refused.message.starts_with("fixed_flat_storage_tools_unavailable"), "{refused}");
        assert!(storage_choices(FIXED_FLAT).starts_with("nothing"));
        let root = crate::controller::test_support::scratch_root("storage-policy-flat");
        let store = ObjectStore::open(root.join("library")).unwrap();
        let package = ContentId::from_bytes([3; 32]);
        assert_eq!(flat.excluded(&store, package).unwrap(), None);
        assert!(flat.ineligible(&store, package, "flat_t").unwrap().unwrap().starts_with("storage_policy_ineligible"));
        std::fs::remove_dir_all(root).unwrap();
    }

    /// Fail closed: under physical_only a package without a recorded physical_only registration is ineligible unless
    /// the user lists it, alone or as a query package's storage use.
    #[test]
    fn unknown_admitted_storage_is_ineligible_unless_listed() {
        let root = crate::controller::test_support::scratch_root("storage-policy");
        let store = ObjectStore::open(root.join("library")).unwrap();
        let package = ContentId::from_bytes([9; 32]);
        let physical = StoredDataPolicy::PhysicalOnly { eligible_storages: vec![] };
        assert!(physical.ineligible(&store, package, "old").unwrap().unwrap().starts_with("storage_policy_ineligible"));
        assert_eq!(StoredDataPolicy::Unrestricted.ineligible(&store, package, "old").unwrap(), None);
        let listed = StoredDataPolicy::PhysicalOnly { eligible_storages: vec![EligibleStorage { package, review: "sources reviewed: sorted copy".into() }] };
        assert_eq!(listed.ineligible(&store, package, "old").unwrap(), None);
        let uses = [("old", package)];
        assert!(physical.ineligible_use(&store, uses).unwrap().is_some() && listed.ineligible_use(&store, uses).unwrap().is_none());
        std::fs::remove_dir_all(root).unwrap();
    }

    /// An exclusion recorded once in the library holds for a fresh request and store view without any request-level
    /// list, wins over an `eligible_storages` entry, reaches a query package through its storage uses, and leaves
    /// unrestricted use, other packages and the package record itself untouched.
    #[test]
    fn recorded_exclusion_holds_for_a_fresh_request_and_wins_over_a_listing() {
        use super::super::exclusion::record_exclusion;
        use gendb_artifacts::verus::VERUS_STORAGE_PACKAGE_KIND;
        let root = crate::controller::test_support::scratch_root("storage-policy-exclusion");
        let library = root.join("library");
        let listed = |package| StoredDataPolicy::PhysicalOnly { eligible_storages: vec![EligibleStorage { package, review: "sources reviewed".into() }] };
        let (excluded, kept) = {
            let store = ObjectStore::open(&library).unwrap();
            let excluded = store.put(1, VERUS_STORAGE_PACKAGE_KIND, &json!({"name":"orders_by_customer"})).unwrap();
            let kept = store.put(1, VERUS_STORAGE_PACKAGE_KIND, &json!({"name":"customer_sorted"})).unwrap();
            assert_eq!(listed(excluded).ineligible(&store, excluded, "orders_by_customer").unwrap(), None, "listed and not yet excluded");
            record_exclusion(&store, PHYSICAL_ONLY, excluded, "review: stores another table's row ranges").unwrap();
            (excluded, kept)
        };
        let store = ObjectStore::open_existing(&library).unwrap();
        let request: StoredDataPolicy = serde_json::from_value(json!({"kind":"physical_only"})).unwrap();
        let reason = request.ineligible(&store, excluded, "orders_by_customer").unwrap().unwrap();
        assert!(reason.starts_with("storage_policy_excluded") && reason.contains("another table's row ranges"), "{reason}");
        assert!(listed(excluded).ineligible(&store, excluded, "orders_by_customer").unwrap().unwrap().starts_with("storage_policy_excluded"), "exclusion wins over a listing");
        assert_eq!(listed(kept).ineligible(&store, kept, "customer_sorted").unwrap(), None, "other packages are unaffected");
        let query_uses = [("customer_sorted", kept), ("orders_by_customer", excluded)];
        assert!(listed(kept).ineligible_use(&store, query_uses).unwrap().unwrap().starts_with("storage_policy_excluded"), "a query package reading it is ineligible");
        assert!(request.refuse_excluded(&store, excluded).unwrap_err().message.starts_with("storage_policy_excluded"));
        assert!(request.refuse_excluded(&store, kept).is_ok());
        assert_eq!(StoredDataPolicy::Unrestricted.ineligible_use(&store, query_uses).unwrap(), None, "unrestricted use stays available");
        assert_eq!(StoredDataPolicy::Unrestricted.excluded(&store, excluded).unwrap(), None);
        assert_eq!(store.read(excluded).unwrap().kind, VERUS_STORAGE_PACKAGE_KIND, "the package record is unchanged");
        std::fs::remove_dir_all(root).unwrap();
    }
}
