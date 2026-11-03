//! Applicability by content, and re-verification of an admitted storage against the current framework.
//!
//! An admitted storage applies to a run when it represents the same content: its declaration (tables, table ids,
//! column ordinals, names and SQL types) equals the declaration of the same columns over the run's schema
//! ([`content_matches`]). Its generated framework text need not be byte-equal: when the framework files of its
//! dependency closure differ from a fresh generation (another emitter or SQLSpec version, comment changes, ...), the
//! storage is *stale* ([`ClosureState`]) and is re-verified once when first used: its unchanged author files
//! (interface and builder, from its checked build) are frozen with a fresh generation of the framework files, verified
//! and compiled whole, published and admitted as a new version of the same name ([`materialize`], then the ordinary
//! check-and-register path of `tools::bench`). Its asset is reused by hard links when the builder identity is unchanged
//! (`storage::identity`), else rebuilt by the new library. Nothing about the old package is assumed: the new package
//! carries its own proof.

use super::freeze::{FrozenStorage, derived_modules, manifest_derivation_of, storage_framework};
use super::manifest::{DataPolicy, StorageLayout, StorageManifest, StoredTable};
use crate::query::candidate::CompilerChoice;
use gendb_artifacts::verus::{self as records, VerusDerivationV1, VerusSourceOwnerV1, VerusStoragePackageV1};
use gendb_artifacts::{ContentId, ObjectStore, blob_id};
use gendb_frontend::ast::TableDef;
use gendb_verification::admission::AdmissionError;
use gendb_verification::obligations::{DeclaredSource, StorageName, storage_crate_files};
use gendb_verification::verus::{AuthorRoot, freeze_author_crate};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

/// Record kind of the evidence that a package re-verifies an earlier one.
pub const REVERIFICATION_KIND: &str = "gendb.verus.storage-reverification.v1";

/// Whether an applicable storage's closure is the current framework's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosureState {
    Current,
    /// The named closure files differ from a fresh generation: re-verified on first use.
    Stale(String),
}

/// The declaration `package` stores, recomputed over `schema` for the same tables and ordinals, must equal its
/// recorded declaration (`storage_content_differs` otherwise, naming the first difference).
pub fn content_matches(schema: &[TableDef], package: &VerusStoragePackageV1) -> Result<DeclaredSource, String> {
    let recorded: DeclaredSource = serde_json::from_value(package.declaration.clone()).map_err(|e| format!("storage_content_differs: unreadable declaration: {e}"))?;
    let mut selection: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for table in &recorded.tables {
        let id = schema.iter().position(|t| t.name == table.name).ok_or_else(|| format!("storage_content_differs: table {} is not in this schema", table.name))?;
        selection.insert(id, table.columns.iter().filter(|c| !c.row_count_only).map(|c| c.ordinal).collect());
    }
    let fresh = DeclaredSource::for_storage(schema, &selection).map_err(|e| format!("storage_content_differs: {e}"))?;
    if fresh != recorded {
        return Err(format!(
            "storage_content_differs: storage {} stores columns whose table, position, name or type differs in this schema",
            package.name
        ));
    }
    Ok(fresh)
}

/// The closure state of `package` (content already matched, `declaration` its fresh declaration): every
/// framework-generated closure file (all but its interface files) equals the fresh generation byte for byte.
pub fn closure_state(schema: &[TableDef], package: &VerusStoragePackageV1, declaration: &DeclaredSource) -> Result<ClosureState, AdmissionError> {
    let name = StorageName::new(&package.name).map_err(AdmissionError::tool)?;
    let fresh = storage_crate_files(schema, &name, declaration, false).map_err(AdmissionError::tool)?;
    let interface = name.interface_prefix();
    let mut differing = vec![];
    for file in package.closure.iter().filter(|f| !f.path.starts_with(&interface)) {
        match fresh.iter().find(|f| f.path == file.path) {
            Some(current) if blob_id(current.text.as_bytes()) == file.blob => {}
            Some(_) => differing.push(file.path.clone()),
            None => differing.push(format!("{} (no longer generated)", file.path)),
        }
    }
    let closure_paths: BTreeSet<&str> = package.closure.iter().map(|f| f.path.as_str()).collect();
    let shared_now = fresh.iter().filter(|f| gendb_registry::closure_definition(&f.path, name.as_str()).is_some() && !closure_paths.contains(f.path.as_str()));
    differing.extend(shared_now.map(|f| format!("{} (new in the framework)", f.path)));
    if differing.is_empty() {
        return Ok(ClosureState::Current);
    }
    let shown: Vec<&String> = differing.iter().take(5).collect();
    Ok(ClosureState::Stale(format!(
        "closure_stale: {} framework file(s) of its dependency closure differ from the current framework ({shown:?}{}); it is re-verified once when first used",
        differing.len(),
        if differing.len() > 5 { ", ..." } else { "" }
    )))
}

/// The admitted package that re-verifies `package` under the current framework, if one exists: a version of the same
/// name whose admission evidence names `package` as re-verified and whose closure is current.
pub fn recorded_reverification(store: &ObjectStore, schema: &[TableDef], package: ContentId, name: &str) -> Result<Option<ContentId>, AdmissionError> {
    for (_, admission) in records::storage_versions(store, name).map_err(AdmissionError::tool)? {
        for evidence in &admission.evidence {
            let object = store.read(*evidence).map_err(AdmissionError::tool)?;
            if object.kind != REVERIFICATION_KIND {
                continue;
            }
            let record: Value = object.decode().map_err(AdmissionError::tool)?;
            if record["reverifies"] != json!(package) {
                continue;
            }
            let newer: VerusStoragePackageV1 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
            if let Ok(declaration) = content_matches(schema, &newer)
                && closure_state(schema, &newer, &declaration)? == ClosureState::Current
            {
                return Ok(Some(admission.package));
            }
        }
    }
    Ok(None)
}

/// The package that admitted `package` (of storage `name`) re-verifies, from its admission's re-verification evidence
/// (`None`: an author's registration). A re-verification has the same author sources, so it has the re-verified
/// package's standing under the storage policy (`storage::policy`).
pub fn reverified_package(store: &ObjectStore, package: ContentId, name: &str) -> Result<Option<ContentId>, AdmissionError> {
    for (_, admission) in records::storage_versions(store, name).map_err(AdmissionError::tool)? {
        if admission.package != package {
            continue;
        }
        for evidence in &admission.evidence {
            let object = store.read(*evidence).map_err(AdmissionError::tool)?;
            if object.kind == REVERIFICATION_KIND {
                let record: Value = object.decode().map_err(AdmissionError::tool)?;
                return serde_json::from_value(record["reverifies"].clone()).map(Some).map_err(AdmissionError::tool);
            }
        }
    }
    Ok(None)
}

/// Freeze the re-verification of admitted `package` into the fresh directory `dir` (`source/` its author files as
/// checked, `frozen/` the frozen storage): its unchanged author files with a fresh generation of the framework files;
/// for a storage built from admitted storages, `sources` are their current versions (in use order). The manifest is
/// reconstructed from the package and its registration description.
pub fn materialize(
    store: &ObjectStore,
    schema: &[TableDef],
    package: &VerusStoragePackageV1,
    description: &Value,
    sources: Option<Vec<ContentId>>,
    dir: &Path,
) -> Result<(FrozenStorage, std::path::PathBuf), AdmissionError> {
    let declaration = content_matches(schema, package).map_err(AdmissionError::refusal)?;
    let name = StorageName::new(&package.name).map_err(AdmissionError::tool)?;
    let build = records::storage_build(store, package).map_err(AdmissionError::tool)?;
    let source_root = dir.join("source/src");
    for (path, owner, text) in build.source_texts(store).map_err(AdmissionError::tool)? {
        if owner == VerusSourceOwnerV1::Agent {
            let file = source_root.join(&path);
            std::fs::create_dir_all(file.parent().expect("a file path")).map_err(AdmissionError::tool)?;
            std::fs::write(&file, text).map_err(AdmissionError::tool)?;
        }
    }
    let derivation = match (&package.derived_from, sources) {
        (Some(d), Some(current)) => Some(VerusDerivationV1 {
            sources: d.sources.iter().zip(current).map(|(s, package)| records::VerusDerivationSourceV1 { name: s.name.clone(), package }).collect(),
            extends: d.extends,
        }),
        (Some(d), None) => Some(d.clone()),
        (None, _) => None,
    };
    let manifest = reconstructed_manifest(package, description, &declaration, schema, &build.argv, derivation.as_ref());
    let candidate_derivation = manifest_derivation_of(store, derivation.as_ref())?;
    let framework = storage_framework(schema, &name, &declaration, manifest.uses_declared_constraints, candidate_derivation.as_ref())?;
    let (interface_root, builder_root) = manifest.author_roots();
    for root in [&interface_root, &builder_root] {
        std::fs::create_dir_all(source_root.join(root)).map_err(AdmissionError::tool)?;
    }
    let frozen_dir = dir.join("frozen");
    std::fs::create_dir_all(&frozen_dir).map_err(AdmissionError::tool)?;
    let roots = [
        AuthorRoot { crate_directory: &interface_root, source: &source_root.join(&interface_root) },
        AuthorRoot { crate_directory: &builder_root, source: &source_root.join(&builder_root) },
    ];
    let krate = freeze_author_crate(&framework, &roots, &frozen_dir.join("crate")).map_err(super::freeze::freeze_error)?;
    let frozen = FrozenStorage {
        compiler: manifest.compiler.clone().unwrap_or_default(),
        modules: derived_modules(&manifest, &krate),
        declaration,
        author_files: krate.author_files.clone(),
        framework_files: krate.framework_files.clone(),
        derivation,
        manifest,
    };
    crate::controller::records::write_new_json(&frozen_dir.join("storage.json"), &frozen).map_err(AdmissionError::tool)?;
    Ok((frozen, frozen_dir))
}

/// The manifest of a re-verification: the package's tables and opt-in, its registered parts, layout and data_policy
/// (or neutral placeholders when the registration recorded none), derived modules and the build's code generation.
fn reconstructed_manifest(
    package: &VerusStoragePackageV1,
    description: &Value,
    declaration: &DeclaredSource,
    schema: &[TableDef],
    argv: &[String],
    derivation: Option<&VerusDerivationV1>,
) -> StorageManifest {
    let tables = declaration
        .tables
        .iter()
        .map(|t| StoredTable { table: t.name.clone(), columns: t.columns.iter().filter(|c| !c.row_count_only).map(|c| schema[t.table_id].columns[c.ordinal].name.clone()).collect() })
        .collect();
    let text = |field: &str, fallback: &str| description["layout"][field].as_str().filter(|t| !t.trim().is_empty()).unwrap_or(fallback).to_string();
    let parts: Vec<String> = match description["parts"].as_array() {
        Some(labels) if !labels.is_empty() => labels.iter().map(|l| l.as_str().unwrap_or("part").to_string()).collect(),
        _ => vec!["parts as recorded by the re-verified package".into()],
    };
    let compiler = CompilerChoice {
        opt_level: argv.iter().find_map(|a| a.strip_prefix("opt-level=")).and_then(|v| v.parse().ok()).unwrap_or(3),
        target_cpu: argv.iter().find_map(|a| a.strip_prefix("target-cpu=")).map(str::to_string),
    };
    StorageManifest {
        format_version: 1,
        name: package.name.clone(),
        crate_dir: "crate".into(),
        tables,
        parts,
        layout: StorageLayout {
            summary: text("summary", "as the re-verified package"),
            units: text("units", "as the re-verified package"),
            choice: text("choice", "re-verification of an admitted storage under the current framework"),
        },
        data_policy: serde_json::from_value::<DataPolicy>(description["data_policy"].clone()).unwrap_or_default(),
        modules: vec![],
        compiler: Some(compiler),
        notes: "re-verification of an admitted storage: its unchanged interface and builder with the current framework files".into(),
        uses_declared_constraints: package.assumed_constraints.is_some(),
        built_from: derivation.map(|d| super::manifest::BuiltFrom {
            sources: d.sources.iter().map(|s| super::manifest::SourceStorage { name: s.name.clone(), admitted: s.package }).collect(),
            extends: d.extends.map(|k| d.sources[k].name.clone()),
        }),
    }
}
