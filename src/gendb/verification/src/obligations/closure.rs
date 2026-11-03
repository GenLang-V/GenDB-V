//! The dependency closure of a storage's interface and the composition rule of a storage build with a query build.
//!
//! The closure is every file of the storage build that the registry marks `Presence::Shared` for that storage
//! (`gendb_registry::closure_definition`): the SQLSpec library (with the fixed `link` definitions), `schema.rs`,
//! `gendb_abi.rs`, the fixed entry submodules and `gendb_entry/stored.rs`, and `stores/<name>/{mod.rs,
//! declaration.rs, interface/**}`. A query build must carry it byte for byte at the same paths
//! (`storage_spec_identity`). Everything else differs by kind and is compared with a fresh generation of its own kind
//! at admission (crate roots, `stores.rs`, the two entry roots, the kind-only generated modules) or is author code.
//!
//! Equal text alone does not give equal meaning: Rust resolves methods and trait items through every `impl` block of
//! the crate, and some built-in macros expand to the crate name or the source path. Identical interface text proved
//! `represents()` in a storage crate and its negation in a query crate when the builder and the query module supplied
//! different methods, when a query module's inherent `view` took precedence over an interface type's `View`, or
//! through `module_path!()`, also renamed as `seq!` (S1c probes P1-P4, P7-P9). The rule [`check_storage_composition`]
//! therefore has two parts, closure identity and the central author-source rules over every author file of both builds
//! ([`author_source_findings`], the same `verus::scan_source` that freezing runs). The basis for "equal closure text,
//! equal meaning" is:
//! - Paths. Closure files can name `crate::{spec, exec, bridge, link, schema, gendb_abi}`, `crate::stores::<name>` and
//!   the shared `crate::gendb_entry::<submodule>`s, which both crate roots declare identically. Anything else exists
//!   in one kind only (`builder`, `gendb_source`, `query`, `gendb_params`, `agent`, other storages, the kind-only entry
//!   submodules), so naming it fails to compile in the other build. The two entry roots define disjoint public names,
//!   no traits and no prelude names, so neither a path nor a glob import of an entry root resolves differently
//!   (unit tests `entry_roots_are_disjoint_and_complete`, `per_kind_framework_files_follow_the_source_rules`).
//! - Implementations (rule `impl_ownership`). Every `impl` of an author file, in `builder/**`, `agent/**` or any
//!   storage's `interface/**`, is at the top level of the file's `verus!` block and implements a struct, enum or union
//!   defined there, or a trait defined there. Closure code cannot name such a type and cannot have such a trait in
//!   scope. Rust does not choose an implementation for an unknown self type merely because it is the only one (the call
//!   is ambiguous and fails to compile, probes P10), so these implementations cannot enter method or trait resolution
//!   in closure code. Kind-specific framework files follow the same rule (test). Closure files may implement
//!   anything: they are the same in both builds.
//! - Macros (rules `macro`, `macro_import`, derives in `attribute`). Author code invokes only `seq!`, `set!`, `map!`
//!   and `vec!` (and `verus!` at the top level), derives only `Clone`, `Copy`, `PartialEq` and `Eq`, cannot
//!   define macros and cannot rebind those names, so they denote the toolchain's macros, whose audited expansions
//!   depend on neither the crate, the path, the environment nor the configuration. `cfg` is refused.
//! - Configuration. Both builds use the same pinned Verus/vstd/Z3 toolchain (a record check at admission) and the same
//!   crate attributes (lint levels only). Crate names and codegen options reach no source that can be checked
//!   (`module_path!`, `file!` and `cfg` are refused).
//!
//! Trust. The source rules are a lexical scan, not a Rust parser, and are not themselves verified. That rustc and
//! Verus resolve names, methods and implementations as described (coherence, resolution, ambiguity) is trusted like
//! the rest of the toolchain; no general theorem about Rust is claimed.

use super::storage_crate::StorageName;
use crate::verus::{scan_source, FrameworkSource, RefusalFinding};
use gendb_registry::{author_definition, closure_definition};
use std::collections::BTreeMap;
use std::fmt;

/// How a query build fails to carry a storage build's closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosureMismatch {
    /// A closure file of the storage build is absent from the query build.
    Missing { path: String },
    /// A closure file has other bytes in the query build.
    Different { path: String },
    /// The query build has a closure file (of this storage or the shared library) the storage build lacks.
    Extra { path: String },
}

impl fmt::Display for ClosureMismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing { path } => write!(f, "storage_spec_identity: {path} of the storage build is missing from the query build"),
            Self::Different { path } => write!(f, "storage_spec_identity: {path} differs between the storage build and the query build"),
            Self::Extra { path } => write!(f, "storage_spec_identity: {path} of the query build is not in the storage build"),
        }
    }
}

impl std::error::Error for ClosureMismatch {}

/// The closure files of storage `name` among `files` (all files of one build, framework and author, relative to
/// `src/`), by path.
pub fn storage_closure<'a>(files: &'a [FrameworkSource], name: &StorageName) -> BTreeMap<&'a str, &'a str> {
    files.iter().filter(|f| closure_definition(&f.path, name.as_str()).is_some()).map(|f| (f.path.as_str(), f.text.as_str())).collect()
}

/// `Ok` exactly when the query build carries the storage build's closure of `name`: the same paths and bytes.
pub fn compare_storage_closure(storage_build: &[FrameworkSource], query_build: &[FrameworkSource], name: &StorageName) -> Result<(), ClosureMismatch> {
    let (stored, queried) = (storage_closure(storage_build, name), storage_closure(query_build, name));
    for (path, text) in &stored {
        match queried.get(path) {
            None => return Err(ClosureMismatch::Missing { path: path.to_string() }),
            Some(other) if other != text => return Err(ClosureMismatch::Different { path: path.to_string() }),
            Some(_) => {}
        }
    }
    match queried.keys().find(|path| !stored.contains_key(*path)) {
        Some(path) => Err(ClosureMismatch::Extra { path: path.to_string() }),
        None => Ok(()),
    }
}

/// Why a query build cannot be composed with a storage build.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompositionError {
    Closure(ClosureMismatch),
    /// Author files of either build break the author-source rules (every finding, with its rule id).
    SourceRules(Vec<RefusalFinding>),
}

impl CompositionError {
    /// Refused: the builds do not state the same storage propositions.
    pub fn failure_class(&self) -> &'static str {
        "refusal"
    }
}

impl fmt::Display for CompositionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Closure(mismatch) => mismatch.fmt(f),
            Self::SourceRules(findings) => {
                f.write_str("author-source rules:")?;
                findings.iter().try_for_each(|x| write!(f, " {}:{}: {}: {};", x.file, x.line, x.rule, x.detail))
            }
        }
    }
}

impl std::error::Error for CompositionError {}

/// `Ok` exactly when the query build may use the storage build of `name`: it carries the storage's closure byte for
/// byte ([`compare_storage_closure`]) and every author file of both builds passes the author-source rules
/// ([`author_source_findings`]). With the same toolchain (a record check), `represents` and `stored_relations` then
/// denote the same propositions in both builds, on the basis stated in this module's documentation.
pub fn check_storage_composition(storage_build: &[FrameworkSource], query_build: &[FrameworkSource], name: &StorageName) -> Result<(), CompositionError> {
    compare_storage_closure(storage_build, query_build, name).map_err(CompositionError::Closure)?;
    let findings: Vec<RefusalFinding> = author_source_findings(storage_build).into_iter().chain(author_source_findings(query_build)).collect();
    if findings.is_empty() { Ok(()) } else { Err(CompositionError::SourceRules(findings)) }
}

/// The findings of the central author-source scan (`verus::scan_source`, exactly what freezing runs) over the author
/// files of `files` (`gendb_registry::author_definition`: `builder/**`, `agent/**` and every storage's `interface/**`),
/// with paths relative to `src/`. Empty for a build whose author code may be admitted or composed; usable for any crate
/// kind (a v3 candidate's author files are its `agent/**`).
pub fn author_source_findings(files: &[FrameworkSource]) -> Vec<RefusalFinding> {
    files.iter().filter(|f| author_definition(&f.path).is_some()).flat_map(|f| scan_source(&f.path, &f.text)).collect()
}
