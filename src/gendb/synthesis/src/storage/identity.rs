//! The builder identity of a storage build: exactly what the toolchain compiles into the builder library, and the
//! inputs it runs over (asset identity from builder-relevant content only). Two checked builds of
//! equal builder identity compile the same source files, byte for byte, with the same toolchain, options and
//! environment, and their builders read the same inputs; an asset one of them built is therefore an output of the
//! other's library too (the compiler is already in the trusted base; nothing here parses or interprets source text),
//! and the other's proof covers it. Such an asset is reused by hard links instead of being rebuilt (`storage::build`).
//!
//! The identity covers: the declaration and stored tables, the check configuration (toolchain identity, options,
//! environment) and code generation options, the admitted source packages and the extended source of a storage built
//! from admitted storages, and every source file of the build by its exact content id. Any byte change in any file
//! (a comment included) gives a new identity and a rebuild.

use gendb_artifacts::verus::{self as records, VerusBuildV1, VerusStoragePackageV1};
use gendb_artifacts::{ContentId, ObjectStore, content_id};
use gendb_verification::admission::AdmissionError;
use serde_json::json;

/// The builder identity of admitted or published storage package `package`.
pub fn builder_identity(store: &ObjectStore, package: &VerusStoragePackageV1) -> Result<ContentId, AdmissionError> {
    let build: VerusBuildV1 = records::storage_build(store, package).map_err(AdmissionError::tool)?;
    let files: Vec<(&String, ContentId)> = build.sources.iter().map(|source| (&source.path, source.blob)).collect();
    let sources: Vec<(&String, ContentId)> =
        package.derived_from.iter().flat_map(|d| d.sources.iter()).map(|source| (&source.name, source.package)).collect();
    let codegen: Vec<&String> = build.argv.iter().filter(|a| a.starts_with("opt-level=") || a.starts_with("target-cpu=")).collect();
    let configuration = build.check_configuration().map_err(AdmissionError::tool)?;
    let identity = json!({"declaration":package.declaration,"tables":package.tables,"configuration":configuration,"codegen":codegen,
        "sources":sources,"extends":package.derived_from.as_ref().and_then(|d| d.extends),"files":files});
    content_id(1, "gendb.storage-builder-identity.v2", &identity).map_err(AdmissionError::tool)
}
