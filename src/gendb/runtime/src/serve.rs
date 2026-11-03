//! Serving of admitted packages, including new bindings of admitted templates.
//!
//! Compose and execute only. A request is looked up first by its statement key v2 ([`statement_key_v4`]: the
//! generated schema and statement texts, free-parameter declaration, output columns). An admitted query package over
//! stored data (entry v4, ABI 4) is served over the stored asset of each of its storage uses for the current capture
//! (`gendb_storage::versions::resolve_storage_assets`: per stored table the source version, row-order identity and row
//! count); a use without an asset for the current capture is refused by name ([`ServeError::NoStorageAsset`]), with no
//! fallback to another route. Otherwise the saved route serves an admitted ABI v3 package by its statement key v1
//! ([`statement_key`]) over its representation's asset for the current source versions. Both run the stored library in
//! a worker child ([`WorkerExecutor`]) with the request's arguments.
//!
//! Every allowed binding reuses the same package, library and assets; nothing here proves, regenerates, hashes or
//! validates (admission already happened offline), and nothing is written to the library. Argument texts are
//! converted exactly (`gendb_frontend::params::parse_arguments`: an ill-formed or inexact text is refused here, before
//! execution); the parameter domain is decided by the verified entry (`ParamRefused`). The answer keeps the exact
//! status: rows, the exact SQL error, capacity or parameter refusal, with the arguments echoed. Saved ABI v1/v2
//! packages are served only by the earlier GenDB version.
//!
//! Declared integrity constraints. A request whose statement was translated with declared constraints (a schema table
//! declares one) is looked up first by its own statement key v2, which carries the generated `gendb_constraints.rs`:
//! its package was proved under exactly these declarations (entry v5). Without one, the same statement without the
//! declarations is looked up as any request is (key v2, then key v1): an unconstrained package's claim holds for every
//! database, so it serves unchanged and the declarations are unused. A constrained package is never reached by a
//! request without declarations or with another list (no subset matching). See [`admitted_package`].
//!
//! Engines. [`engine`] serves a statement from an admitted engine version (one verified engine for the whole schema):
//! the statement arrives as AST bytes, the engine's verified echo is compared with the host's rendering, and the answer
//! keeps the engine's named refusals. It never falls back to a per-template package.

mod asset;
pub mod engine;
mod error;
mod executor;
mod statement;

pub use asset::current_asset;
pub use error::ServeError;
pub use executor::{StorageQueryCall, WorkerExecutor};
pub use statement::{
    StatementError, free_parameters, parameter_declaration, statement_arguments, statement_key, statement_key_v4,
};

use crate::abi::{ABI_VERSION, CallOutcome, StatementArgument};
use crate::answer::{AnswerError, QueryAnswer};
use crate::worker::{MappedStorageUse, ProcessIoDelta, StorageUseInput};
use gendb_artifacts::verus::{
    ADMITTED_ABI_V4_VERSION, ResolvedVerusPackageV3, ResolvedVerusPackageV4, VerusStatementKeyV1, VerusStatementKeyV2, library_path,
    query_entry_identity, resolve_package_v3, resolve_package_v4,
};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::params::{Instance, ParamValue, parse_arguments};
use gendb_storage::io::PartAccess;
use gendb_storage::versions::{CurrentCapture, resolve_storage_assets};
use serde_json::{Value, json};
use std::borrow::Cow;

/// Trusted items of serving, `(id, statement)`, for the TCB list of admitted v3 packages (ids unchanged from the earlier GenDB version).
pub const TRUSTED_ITEMS: [(&str, &str); 2] = [
    (
        "host_arguments",
        "gendb_frontend::params::parse_arguments + gendb_runtime::serve::statement_arguments: request texts converted \
         exactly (no rounding) into typed arguments in slot order; echoed in run results and serving results; domain \
         decided by the verified entry",
    ),
    (
        "package_lookup_v3",
        "serving resolves the package by the statement key (emitted meaning of the instance, free-parameter \
         declaration, output columns) through the frontend and emitter (gendb_frontend::translator), both already \
         trusted",
    ),
];

/// Trusted items of serving packages over stored data, `(id, statement)`, for their TCB list.
pub const TRUSTED_ITEMS_V4: [(&str, &str); 2] = [
    TRUSTED_ITEMS[0],
    (
        "package_lookup_v4",
        "serving resolves the package by the statement key v2 (the generated schema.rs and the generated query.rs \
         without its SQL header as separate fields, free-parameter declaration, output columns; the same construction \
         as admission, gendb_runtime::serve::statement_key_v4) through the frontend and translator, both already \
         trusted, then the asset of every storage use for one current capture (gendb_storage::versions); a use without \
         an asset is refused, never served from another route",
    ),
];

/// Trusted serving item of packages proved under declared integrity constraints (entry v5), for their TCB list.
pub const DECLARED_CONSTRAINTS_LOOKUP: (&str, &str) = (
    "package_lookup_declared_constraints",
    "a request that declares integrity constraints is looked up first by its statement key v2 including the generated \
     gendb_constraints.rs (the same construction as admission, gendb_runtime::serve::statement_key_v4), so a package \
     proved under declared constraints is reached only by a request with the identical declaration list, never by a \
     request without declarations or with another list; serving rechecks that the package's entry is the key's",
);

/// How a served package relates to the request's declared integrity constraints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclaredConstraints {
    /// The request declares none.
    None,
    /// The package was proved under exactly the request's declarations (entry v5); `digest` is their
    /// `constraints_digest`.
    Assumed { digest: ContentId },
    /// The request declares constraints and the package is an unconstrained one, served by its own claim, which holds
    /// for every database; the declarations are unused.
    Unused,
}

/// Which admitted route served a request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ServingRoute {
    /// A saved-route package (entry v3, ABI 3) over its representation's asset.
    SavedV3,
    /// A query package over stored data (entry v4, ABI 4) over its storage uses' assets.
    StoredDataV4,
}

/// The stored asset of one storage use of a served v4 package.
#[derive(Clone, Debug)]
pub struct ServedStorage {
    pub name: String,
    pub package: ContentId,
    pub asset: ContentId,
}

/// A served statement: the answer, the records it came from, and the arguments as requested, parsed and passed.
pub struct Served {
    pub route: ServingRoute,
    pub answer: QueryAnswer,
    pub statement: ContentId,
    pub admission: ContentId,
    pub package: ContentId,
    pub claim: ContentId,
    pub build: ContentId,
    /// The v3 representation's asset (saved route).
    pub asset: Option<ContentId>,
    /// The asset of every storage use, in use order (v4 route).
    pub storages: Vec<ServedStorage>,
    /// The request's argument texts, their exact typed values and the ABI arguments passed (slot order).
    pub argument_texts: Vec<String>,
    pub argument_values: Vec<ParamValue>,
    pub arguments: Vec<StatementArgument>,
    /// The served call (the last one the executor ran); on the v4 route with its per-use request counters.
    pub outcome: CallOutcome,
    /// v4 route: what every storage use mapped (parts, stored bytes) and the call's process I/O (descriptive).
    pub storage_uses: Vec<MappedStorageUse>,
    pub process_io: Option<ProcessIoDelta>,
    /// The package and the request's declared integrity constraints.
    pub constraints: DeclaredConstraints,
}

impl Served {
    /// Record form: the answer (rows as PostgreSQL output text), the arguments, every record id, and the served
    /// call's dispatch and wall time. The saved route's form is unchanged; the v4 route adds `route`, the storage
    /// assets, the verified request counters (extent requests, not device I/O), the stored bytes and the process I/O.
    pub fn record(&self) -> Result<Value, AnswerError> {
        let mut record = json!({
            "answer": self.answer.record()?,
            "argument_texts": self.argument_texts,
            "arguments": self.arguments,
            "statement": self.statement,
            "admission": self.admission,
            "package": self.package,
            "claim": self.claim,
            "build": self.build,
            "dispatch": {"spawned": self.outcome.dispatch.spawned, "joined": self.outcome.dispatch.joined},
            "wall_ns": self.outcome.usage.wall_ns,
        });
        match self.route {
            ServingRoute::SavedV3 => record["asset"] = json!(self.asset),
            ServingRoute::StoredDataV4 => {
                record["route"] = json!("stored_data_v4");
                record["storage_assets"] = json!(self
                    .storages
                    .iter()
                    .map(|s| json!({"storage": s.name, "package": s.package, "asset": s.asset}))
                    .collect::<Vec<_>>());
                record["storage_requests"] = json!(self.outcome.storage_requests);
                record["storage_uses"] = json!(self.storage_uses);
                record["process_io"] = json!(self.process_io);
            }
        }
        match self.constraints {
            DeclaredConstraints::None => {}
            DeclaredConstraints::Assumed { digest } => {
                record["integrity_constraints"] = json!({"package":"assumed","constraints_digest":digest.to_hex(),
                    "basis":"the package's claim assumes exactly the request's declared constraints (user declared, never checked against the data)"});
            }
            DeclaredConstraints::Unused => {
                record["integrity_constraints"] = json!({"package":"none",
                    "basis":"no package proved under these declarations; an unconstrained package's claim holds for every database and the declarations are unused"});
            }
        }
        Ok(record)
    }

    /// The assets the answer was computed over: the v3 asset, or the v4 storage assets in use order.
    pub fn asset_ids(&self) -> Vec<ContentId> {
        self.asset.into_iter().chain(self.storages.iter().map(|s| s.asset)).collect()
    }
}

/// The admitted package a statement instance resolves to, by the route order of [`serve`], with the key it was found
/// by and its relation to the request's declared constraints.
pub enum AdmittedPackage {
    StoredDataV4 { statement: ContentId, key: VerusStatementKeyV2, resolved: Box<ResolvedVerusPackageV4>, constraints: DeclaredConstraints },
    SavedV3 { statement: ContentId, key: VerusStatementKeyV1, resolved: Box<ResolvedVerusPackageV3>, constraints: DeclaredConstraints },
}

/// The admitted package of `instance`, in route order:
/// 1. only when its schema declares integrity constraints: the package of its statement key v2, which carries the
///    declarations (proved under exactly them, entry v5);
/// 2. the package over stored data of the statement key v2 of the instance without declared constraints;
/// 3. the saved ABI v3 package of that instance's statement key v1;
/// else `None`. Without declared constraints only 2 and 3 apply, to the instance itself: the lookup before constraints
/// could be declared. A constrained request served by 2 or 3 uses an unconstrained package unchanged
/// ([`DeclaredConstraints::Unused`]).
pub fn admitted_package(store: &ObjectStore, instance: &Instance) -> Result<Option<AdmittedPackage>, ServeError> {
    let declared = declares_constraints(instance);
    if declared {
        let key = statement_key_v4(instance)?;
        let statement = key.identity()?;
        if let Some(resolved) = resolve_package_v4(store, statement)? {
            let digest = key.constraints_digest().ok_or(ServeError::PackageMismatch)?;
            let constraints = DeclaredConstraints::Assumed { digest };
            return Ok(Some(AdmittedPackage::StoredDataV4 { statement, key, resolved: Box::new(resolved), constraints }));
        }
    }
    let constraints = if declared { DeclaredConstraints::Unused } else { DeclaredConstraints::None };
    let unconstrained = without_declared_constraints(instance);
    let key = statement_key_v4(&unconstrained)?;
    let statement = key.identity()?;
    if let Some(resolved) = resolve_package_v4(store, statement)? {
        return Ok(Some(AdmittedPackage::StoredDataV4 { statement, key, resolved: Box::new(resolved), constraints }));
    }
    let key = statement_key(&unconstrained)?;
    let statement = key.identity()?;
    Ok(resolve_package_v3(store, statement)?.map(|resolved| AdmittedPackage::SavedV3 { statement, key, resolved: Box::new(resolved), constraints }))
}

/// Some table of the instance's schema declares an integrity constraint (the request declared some).
fn declares_constraints(instance: &Instance) -> bool {
    instance.doc.tables.iter().any(|t| !t.constraints.is_empty())
}

/// The instance with every declared constraint removed (borrowed unchanged when it declares none).
fn without_declared_constraints(instance: &Instance) -> Cow<'_, Instance> {
    if !declares_constraints(instance) {
        return Cow::Borrowed(instance);
    }
    let mut unconstrained = instance.clone();
    for table in &mut unconstrained.doc.tables {
        table.constraints.clear();
    }
    Cow::Owned(unconstrained)
}

/// Serve the statement `instance` at `arguments` (one text per free parameter, slot order) with `workers` workers from
/// its admitted package ([`admitted_package`]): check the worker count against the proved domain; convert the
/// arguments exactly (refused here, before execution); resolve the assets for `capture` (the current prepared data,
/// `CurrentCapture::of`); run the stored library through `executor` (v4: each storage use mapped with `access`); return
/// its exact answer. A worker failure or a status that answers nothing is an error.
pub fn serve(
    store: &ObjectStore,
    instance: &Instance,
    arguments: &[String],
    capture: &CurrentCapture,
    access: PartAccess,
    executor: &WorkerExecutor,
    workers: u32,
) -> Result<Served, ServeError> {
    match admitted_package(store, instance)?.ok_or(ServeError::NoPackage)? {
        AdmittedPackage::StoredDataV4 { statement, key, resolved, constraints } => {
            let same_entry = resolved.package.entry_identity == query_entry_identity(&key);
            // Defensive: admission already required every storage's assumed declarations to be exactly the key's.
            let assumptions_agree = resolved.storages.iter().all(|s| s.check_declared_constraints(key.constraints_digest()).is_ok());
            if resolved.package.abi_version != ADMITTED_ABI_V4_VERSION || resolved.key != key || !same_entry || !assumptions_agree {
                return Err(ServeError::PackageMismatch);
            }
            check_workers(resolved.package.workers, workers)?;
            let (argument_values, abi_arguments) = exact_arguments(instance, arguments)?;
            let uses = resolved.package.storage_uses.iter().zip(&resolved.storages).map(|(u, p)| (u.name.as_str(), u.package, p));
            let assets = resolve_storage_assets(store, uses, capture)?;
            let inputs: Vec<StorageUseInput> =
                assets.iter().map(|a| StorageUseInput { name: a.name.clone(), parts_directory: a.directory.clone() }).collect();
            let library = library_path(store, &resolved.build)?;
            let call = executor.query_storages(&library, &inputs, access, &abi_arguments, workers)?;
            Ok(Served {
                route: ServingRoute::StoredDataV4,
                answer: QueryAnswer::of(&call.served.outcome)?,
                statement,
                admission: resolved.admission_id,
                package: resolved.admission.package,
                claim: resolved.package.claim,
                build: resolved.package.build,
                asset: None,
                storages: assets.iter().map(|a| ServedStorage { name: a.name.clone(), package: a.package, asset: a.asset_id }).collect(),
                argument_texts: arguments.to_vec(),
                argument_values,
                arguments: abi_arguments,
                outcome: call.served.outcome,
                storage_uses: call.storage_uses,
                process_io: call.served.process_io,
                constraints,
            })
        }
        AdmittedPackage::SavedV3 { statement, key, resolved, constraints } => {
            if resolved.package.abi_version != ABI_VERSION || resolved.key != key {
                return Err(ServeError::PackageMismatch);
            }
            check_workers(resolved.package.workers, workers)?;
            let (argument_values, abi_arguments) = exact_arguments(instance, arguments)?;
            let (asset, parts) = current_asset(store, resolved.package.representation, &capture.source_versions())?;
            let library = library_path(store, &resolved.build)?;
            let outcome = executor.query(&library, &parts, &abi_arguments, workers)?;
            Ok(Served {
                route: ServingRoute::SavedV3,
                answer: QueryAnswer::of(&outcome)?,
                statement,
                admission: resolved.admission_id,
                package: resolved.admission.package,
                claim: resolved.package.claim,
                build: resolved.package.build,
                asset: Some(asset),
                storages: vec![],
                argument_texts: arguments.to_vec(),
                argument_values,
                arguments: abi_arguments,
                outcome,
                storage_uses: vec![],
                process_io: None,
                constraints,
            })
        }
    }
}

fn check_workers(domain: (u32, u32), workers: u32) -> Result<(), ServeError> {
    if (domain.0..=domain.1).contains(&workers) { Ok(()) } else { Err(ServeError::WorkersOutsideDomain { workers, domain }) }
}

/// The request's argument texts converted exactly, and their ABI arguments (slot order).
fn exact_arguments(instance: &Instance, arguments: &[String]) -> Result<(Vec<ParamValue>, Vec<StatementArgument>), ServeError> {
    let values = parse_arguments(&instance.free, arguments).map_err(ServeError::Arguments)?;
    let abi = statement_arguments(&values)?;
    Ok((values, abi))
}

#[cfg(test)]
mod tests {
    //! The route order of [`admitted_package`] over a temporary library holding fixture records (no Verus run: build
    //! outputs are fixture JSON reporting a complete verification; the framework texts are the keys' texts).
    use super::*;
    use gendb_artifacts::verus::*;
    use gendb_frontend::ast::{Translation, decode};
    use std::collections::BTreeMap;
    use std::path::{Path, PathBuf};

    const COMPLETE: &str = "{\"verification-results\":{\"success\":true,\"verified\":1,\"errors\":0,\"is-verifying-entire-crate\":true,\"encountered-error\":false,\"encountered-vir-error\":false}}";

    /// `SELECT c FROM t` over `t(c integer)` whose `constraints` field is `constraints` (AST JSON).
    fn instance(constraints: &str) -> Instance {
        let doc = format!(
            r#"{{"format": "gendb-sql-ast-v1", "status": "ok", "frontend": {{"identity": "unit"}}, "sql": "SELECT c FROM t",
            "schema": {{"tables": [{{"name": "t", "columns": [{{"name": "c", "type": {{"kind": "int4"}}, "nullable": false}}], "constraints": {constraints}}}]}},
            "output": {{"names": ["c"], "columns": [{{"type": {{"kind": "int4"}}, "nullable": false, "dscale": null}}], "pg_types": ["int4"]}},
            "root": 1, "nodes": [
              {{"id": 0, "tag": "Table", "table": 0, "columns": [{{"type": {{"kind": "int4"}}, "nullable": false, "dscale": null}}]}},
              {{"id": 1, "tag": "OrderedQuery", "body": 0, "keys": [], "limit": null, "offset": 0}}]}}"#
        );
        let Translation::Ok(doc) = decode(&doc).unwrap() else { panic!("refused") };
        Instance::concrete(&doc).unwrap()
    }

    fn key_constraint(primary: bool) -> String {
        format!(r#"[{{"kind": "key", "name": null, "primary": {primary}, "columns": [0], "nulls_distinct": true, "deferrable": false, "initially_deferred": false}}]"#)
    }

    /// Write `files` (path relative to `src/`, text, owner) under `dir` and publish them as one complete build.
    fn build(store: &ObjectStore, dir: &Path, files: &[(&str, &str, VerusSourceOwnerV1)], tcb: ContentId) -> ContentId {
        for (path, text, _) in files {
            let file = dir.join("src").join(path);
            std::fs::create_dir_all(file.parent().unwrap()).unwrap();
            std::fs::write(file, text).unwrap();
        }
        std::fs::write(dir.join("lib.so"), b"\x7fELF-fixture").unwrap();
        let argv = ["lib.rs", "--edition=2021", "--no-cheating", "--output-json", "--compile", "-o", "/x/lib.so"].map(String::from).to_vec();
        publish_build(store, VerusBuildInput {
            purpose: VerusBuildPurposeV1::Candidate,
            provider_identity: "pinned".into(),
            argv,
            environment: BTreeMap::from([("VSTD_KIND".into(), "Imported".into())]),
            exit_code: Some(0),
            stdout: COMPLETE,
            frozen_directory: dir,
            sources: files.iter().map(|(p, _, o)| (p.to_string(), *o)).collect(),
            library_path: &dir.join("lib.so"),
            wall_ns: 1,
            tcb,
        })
        .unwrap()
    }

    /// A library with one admitted storage `s` whose closure is `schema` (the column schema both keys share).
    struct Library {
        store: ObjectStore,
        dir: PathBuf,
        tcb: ContentId,
        storage: ContentId,
        evidence: ContentId,
        schema: String,
    }

    impl Library {
        fn new(name: &str) -> Library {
            let lane = PathBuf::from(std::env::var_os("TMPDIR").expect("a scratch TMPDIR is required"));
            let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
            let dir = lane.join("gendb-runtime-tests").join(format!("{name}-{}-{nanos}", std::process::id()));
            let store = ObjectStore::open(dir.join("library")).unwrap();
            let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: json!([]) }).unwrap();
            let schema = statement_key_v4(&instance("[]")).unwrap().schema;
            let shared = [("schema.rs", schema.as_str()), ("stores/s/declaration.rs", "DECLARATION"), ("stores/s/interface/mod.rs", "INTERFACE")];
            let framework = VerusSourceOwnerV1::Framework;
            let mut files: Vec<(&str, &str, VerusSourceOwnerV1)> = shared.iter().map(|(p, t)| (*p, *t, framework)).collect();
            files[2].2 = VerusSourceOwnerV1::Agent;
            let entry = "// fixture entry `gendb-verus-storage-entry-v1`\npub proof fn theorem_storage_built() {}\n";
            files.extend([("gendb_entry.rs", entry, framework), ("builder/mod.rs", "BUILDER", VerusSourceOwnerV1::Agent)]);
            let storage_build = build(&store, &dir.join("storage"), &files, tcb);
            let record: VerusBuildV1 = store.read(storage_build).unwrap().decode().unwrap();
            let closure = record
                .sources
                .iter()
                .filter(|s| s.path == "schema.rs" || s.path.starts_with("stores/"))
                .map(|s| VerusClosureFileV1 { path: s.path.clone(), blob: s.blob, bytes: s.bytes })
                .collect();
            let package = VerusStoragePackageV1 {
                name: "s".into(), build: storage_build, entry_identity: VERUS_STORAGE_ENTRY_V1_IDENTITY.into(), assumed_constraints: None,
                tables: vec![VerusStoredTableV1 { table: "t".into(), table_id: 0, ordinals: vec![0] }], declaration: json!({"tables": []}),
                schema_ddl: store.put_blob(b"CREATE TABLE t (c integer NOT NULL);").unwrap(), frontend: json!({"identity": "unit"}), closure,
                configuration: record.check_configuration().unwrap(), readers: vec![],
                theorems: vec!["gendb_entry::theorem_storage_built".into()], workers: (1, 64), tcb, derived_from: None,
            };
            let storage_framework: Vec<(&str, &str)> = files.iter().filter(|f| f.2 == framework).map(|f| (f.0, f.1)).collect();
            let storage = publish_storage_package(&store, &package, &storage_framework).unwrap();
            let evidence = store.put(1, "fixture-evidence", &true).unwrap();
            let admission = VerusStorageAdmissionV1 { package: storage, gate_identity: "g".into(), evidence: vec![evidence] };
            admit_storage_package(&store, &admission).unwrap();
            Library { store, dir, tcb, storage, evidence, schema }
        }

        /// Admit a query package for `instance`'s statement key v2, with the entry its key selects.
        fn admit(&self, name: &str, instance: &Instance) -> ContentId {
            let key = statement_key_v4(instance).unwrap();
            let entry = query_entry_identity(&key);
            let entry_text = format!("// fixture entry `{entry}`\npub proof fn theorem_end_to_end() {{}}\n");
            let framework = VerusSourceOwnerV1::Framework;
            let mut files = vec![
                ("schema.rs", self.schema.as_str(), framework),
                ("stores/s/declaration.rs", "DECLARATION", framework),
                ("stores/s/interface/mod.rs", "INTERFACE", framework),
                ("gendb_entry.rs", entry_text.as_str(), framework),
                ("query.rs", key.statement.as_str(), framework),
                ("agent/mod.rs", "AGENT", VerusSourceOwnerV1::Agent),
            ];
            if let Some(module) = &key.constraints {
                files.push(("gendb_constraints.rs", module.as_str(), framework));
            }
            let build = build(&self.store, &self.dir.join(name), &files, self.tcb);
            let statement = publish_statement_key_v2(&self.store, &key).unwrap();
            let uses = vec![VerusStorageUseV1 { name: "s".into(), package: self.storage }];
            let claim = publish_claim_v2(&self.store, VerusSqlClaimV2Input {
                statement, build, theorems: vec!["gendb_entry::theorem_end_to_end".into()], sql: "SELECT c FROM t".into(),
                frontend: json!({"identity": "unit"}), schema_ddl: "DDL", parameters: vec![], demand: json!({}), storage_uses: uses.clone(),
            })
            .unwrap();
            let package = self
                .store
                .put(1, VERUS_QUERY_PACKAGE_V3_KIND, &VerusQueryPackageV3 {
                    statement, claim, entry_identity: entry.into(), build, storage_uses: uses, implementations: vec![], abi_version: 4,
                    workers: (1, 64), tcb: self.tcb,
                })
                .unwrap();
            let expected: Vec<(&str, &str)> = files.iter().filter(|f| f.2 == framework).map(|f| (f.0, f.1)).collect();
            let evidence = vec![self.evidence];
            let admission = VerusPackageAdmissionV2 { package, gate_identity: "g".into(), qualification_evidence: evidence, assets: vec![] };
            admit_package_v4(&self.store, &admission, &expected, &|_| Ok(())).unwrap();
            package
        }

        /// The package `instance` resolves to and how it relates to its declarations.
        fn lookup(&self, instance: &Instance) -> Option<(ContentId, DeclaredConstraints)> {
            match admitted_package(&self.store, instance).unwrap()? {
                AdmittedPackage::StoredDataV4 { resolved, constraints, .. } => Some((resolved.admission.package, constraints)),
                AdmittedPackage::SavedV3 { .. } => panic!("no v3 package in this library"),
            }
        }
    }

    /// Route order: a constrained request takes the package proved under exactly its declarations, else the
    /// unconstrained package of the same statement (declarations unused); a request without declarations, or with
    /// another list, never takes the constrained package.
    #[test]
    fn declared_constraints_route_order() {
        let (plain, primary, unique) = (instance("[]"), instance(&key_constraint(true)), instance(&key_constraint(false)));
        let only_constrained = Library::new("only-constrained");
        let assumed = only_constrained.admit("v5", &primary);
        let digest = statement_key_v4(&primary).unwrap().constraints_digest().unwrap();
        assert_eq!(only_constrained.lookup(&primary), Some((assumed, DeclaredConstraints::Assumed { digest })));
        assert_eq!(only_constrained.lookup(&plain), None, "a request without declarations never takes a constrained package");
        assert_eq!(only_constrained.lookup(&unique), None, "nor does a request with another declaration list");

        let both = Library::new("both");
        let unconstrained = both.admit("v4", &plain);
        assert_eq!(both.lookup(&plain), Some((unconstrained, DeclaredConstraints::None)));
        assert_eq!(both.lookup(&primary), Some((unconstrained, DeclaredConstraints::Unused)), "the unconstrained claim serves unchanged");
        let assumed = both.admit("v5", &primary);
        assert_eq!(both.lookup(&primary), Some((assumed, DeclaredConstraints::Assumed { digest })), "the exact declarations come first");
        assert_eq!(both.lookup(&plain), Some((unconstrained, DeclaredConstraints::None)));
        assert_eq!(both.lookup(&unique), Some((unconstrained, DeclaredConstraints::Unused)));
        // The saved route's key of a constrained request is the unconstrained instance's key v1.
        assert_ne!(statement_key(&primary).unwrap(), statement_key(&plain).unwrap());
        assert_eq!(statement_key(&without_declared_constraints(&primary)).unwrap(), statement_key(&plain).unwrap());
        std::fs::remove_dir_all(&only_constrained.dir).unwrap();
        std::fs::remove_dir_all(&both.dir).unwrap();
    }
}
