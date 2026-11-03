//! A published run folder, read for the author files of its admitted packages (`gendb import`,
//! `controller::workload_run::import`): GenDB-V's `results/<workload>/<run>/`, or a one-query folder such as
//! `results/example-readings-count/`.
//!
//! Layouts:
//! - a run: `crates/queries/<query>/` (each query package's complete crate) with its template
//!   `queries/<query>/query.sql`, and `crates/storages/<storage>-v<N>/` (each storage package's complete crate) with
//!   its published manifest `storage/<storage>/v<N>/manifest.json`;
//! - one query: `query.sql` and that query's complete crate `crates/<name>/` (a run over GenDB's fixed flat storage,
//!   which publishes no storage crate).
//!
//! Trust: nothing published is trusted. Only author-owned files are taken: a query crate's `src/agent/**`, a storage
//! crate's `src/stores/<name>/interface/**` and `src/builder/**`, and a storage's published manifest (stored columns,
//! part labels, layout, stored-data declaration, derivation). Every framework file of a published crate is ignored:
//! the import freezes the author files with a fresh generation of the framework files, and admission checks the result
//! as it checks any submission. Two published framework files are read for a choice only, which that admission checks
//! again: a query crate's `src/stores.rs` (the storages it reads, in use order) and whether a storage crate carries
//! `src/gendb_constraints.rs` (its builder assumes the run's declared integrity constraints, storage entry v2).
//!
//! Each crate may carry `compile.json` beside `src/` (a [`CompilerChoice`]: `opt_level`, optional `target_cpu`): the
//! compiler options of its admitted build, which the import's manifest names so the crate compiles as it was admitted
//! (absent: the default, opt-level 3 and rustc's default CPU). It changes code generation only, never what is checked.
//!
//! A query is matched to a request query by its template text (`query.sql`, ignoring leading and trailing white
//! space). The storage version a query (or a derived storage) reads is the published version of that name whose
//! interface files equal the crate's copy byte for byte (the composition rule admission checks again).

use crate::controller::author::CandidateSubmission;
use crate::query::candidate::{CompilerChoice, MANIFEST_FILE, ModuleDeclaration, ModuleRole, QueryManifest, REQUIRED_ITEMS, StorageUseDeclaration};
use crate::storage::manifest::{BuiltFrom, DataPolicy, STORAGE_MANIFEST_FILE, SourceStorage, StorageLayout, StorageManifest, StoredTable};
use gendb_artifacts::ContentId;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};

/// The workspace directory of a seeded query candidate (its manifest and crate).
const QUERY_SEED_DIRECTORY: &str = "import";
/// The crate directory of a seeded candidate, relative to its manifest.
const SEED_CRATE_DIRECTORY: &str = "crate";
/// The compiler options of a published crate's admitted build, beside its `src/` (optional).
pub const COMPILE_FILE: &str = "compile.json";
/// The layout `choice` of an imported storage whose published manifest names none (descriptive only).
const IMPORTED_LAYOUT_CHOICE: &str = "imported from a published run: the published manifest names no layout choice";
/// The `why` of a published part declaration that names none (descriptive only; the declaration itself is checked).
const IMPORTED_PART_WHY: &str = "as published (the published manifest names no reason)";

/// A published run folder ([module documentation](self)).
#[derive(Clone, Debug)]
pub struct PublishedRun {
    pub root: PathBuf,
    pub queries: Vec<PublishedQuery>,
    pub storages: Vec<PublishedStorage>,
}

/// One published query package.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PublishedQuery {
    pub name: String,
    /// `src/` of its complete crate (only `agent/**` and `stores.rs` are read).
    pub crate_src: PathBuf,
    /// Its template text (`query.sql`).
    pub sql: String,
    /// The storages it reads, in use order (`src/stores.rs`).
    pub uses: Vec<String>,
    /// The compiler options of its admitted build (`compile.json`); `None`: the default.
    pub compiler: Option<CompilerChoice>,
}

/// One published storage package.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PublishedStorage {
    pub name: String,
    /// The `N` of `<name>-v<N>`.
    pub version: u32,
    /// `src/` of its complete crate (only `stores/<name>/interface/**`, `builder/**` and whether it carries
    /// `gendb_constraints.rs` are read).
    pub crate_src: PathBuf,
    pub manifest: PublishedManifest,
    /// The compiler options of its admitted build (`compile.json`); `None`: the default.
    pub compiler: Option<CompilerChoice>,
}

/// `storage/<name>/v<N>/manifest.json` as published: the author's manifest without its crate directory, modules,
/// compiler choice and notes, and with its derivation's sources by name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PublishedManifest {
    pub name: String,
    pub tables: Vec<StoredTable>,
    pub parts: Vec<String>,
    /// The per-part stored-data declaration (each entry's `why` may be absent), or the free text of earlier manifests.
    #[serde(default)]
    pub data_policy: Value,
    pub layout: PublishedLayout,
    #[serde(default)]
    pub built_from: Option<PublishedDerivation>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PublishedLayout {
    pub summary: String,
    pub units: String,
    #[serde(default)]
    pub choice: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PublishedDerivation {
    /// The source storages' names, in the builder's use order.
    pub sources: Vec<String>,
    #[serde(default)]
    pub extends: Option<String>,
}

impl PublishedStorage {
    /// `<name>-v<N>`: the folder name of its crate and the key of its import records.
    pub fn label(&self) -> String {
        format!("{}-v{}", self.name, self.version)
    }

    /// Its builder assumes the declared integrity constraints (the crate carries `gendb_constraints.rs`).
    pub fn uses_declared_constraints(&self) -> bool {
        self.crate_src.join("gendb_constraints.rs").is_file()
    }
}

impl PublishedRun {
    /// Read the published folder `root` (either layout). Refused by name when it has neither layout, a crate lacks its
    /// template or manifest, or a crate or manifest cannot be read.
    pub fn read(root: &Path) -> Result<Self, String> {
        let root = root.canonicalize().map_err(|e| format!("published folder {}: {e}", root.display()))?;
        let crates = root.join("crates");
        let (queries, storages) = if crates.join("queries").is_dir() {
            let queries = subdirectories(&crates.join("queries"))?
                .into_iter()
                .map(|(name, dir)| PublishedQuery::read(&name, &dir.join("src"), &root.join("queries").join(&name).join("query.sql")))
                .collect::<Result<Vec<_>, _>>()?;
            let storages = match crates.join("storages").is_dir() {
                true => subdirectories(&crates.join("storages"))?.into_iter().map(|(label, dir)| PublishedStorage::read(&root, &label, &dir)).collect::<Result<Vec<_>, _>>()?,
                false => vec![],
            };
            (queries, storages)
        } else if root.join("query.sql").is_file() && crates.is_dir() {
            let query_crates: Vec<(String, PathBuf)> = subdirectories(&crates)?.into_iter().filter(|(_, dir)| dir.join("src/agent").is_dir()).collect();
            let [(name, dir)] = query_crates.as_slice() else {
                return Err(format!("published folder {}: a one-query folder holds exactly one query crate under crates/ (found {})", root.display(), query_crates.len()));
            };
            (vec![PublishedQuery::read(name, &dir.join("src"), &root.join("query.sql"))?], vec![])
        } else {
            return Err(format!(
                "published folder {}: neither a run (crates/queries/<query>/ with queries/<query>/query.sql) nor one query (query.sql with crates/<name>/)",
                root.display()
            ));
        };
        Ok(Self { root, queries, storages })
    }

    /// The published queries whose template text is `sql` (leading and trailing white space ignored).
    pub fn queries_for_sql(&self, sql: &str) -> Vec<&PublishedQuery> {
        self.queries.iter().filter(|query| query.sql.trim() == sql.trim()).collect()
    }

    /// The published version of storage `name` that the crate at `crate_src` reads: the one whose interface files equal
    /// the crate's `stores/<name>/interface/**` byte for byte. Refused by name when none or several do.
    pub fn storage_read_by(&self, crate_src: &Path, name: &str) -> Result<&PublishedStorage, String> {
        let copy = interface_files(crate_src, name)?;
        let versions: Vec<&PublishedStorage> = self.storages.iter().filter(|storage| storage.name == name).collect();
        let mut equal = vec![];
        for storage in &versions {
            if interface_files(&storage.crate_src, name)? == copy {
                equal.push(*storage);
            }
        }
        match equal.as_slice() {
            [storage] => Ok(storage),
            [] if versions.is_empty() => Err(format!("published_storage_missing: {} reads storage {name}, whose crate is not published", crate_src.display())),
            [] => Err(format!(
                "published_storage_missing: {} reads storage {name}, but no published version of it ({}) has the interface it carries",
                crate_src.display(),
                versions.iter().map(|s| s.label()).collect::<Vec<_>>().join(", ")
            )),
            _ => Err(format!("published_storage_ambiguous: several published versions of storage {name} have the interface {} carries", crate_src.display())),
        }
    }

    /// The storages of `storage`'s derivation (its published `built_from` sources, each the version its crate carries),
    /// in the builder's use order.
    pub fn sources_of(&self, storage: &PublishedStorage) -> Result<Vec<&PublishedStorage>, String> {
        let names = storage.manifest.built_from.iter().flat_map(|d| &d.sources);
        names.map(|source| self.storage_read_by(&storage.crate_src, source)).collect()
    }

    /// Every storage `queries` read, with every storage those are built from, in an order where each storage follows
    /// its sources (its import needs their admitted packages).
    pub fn storage_plan(&self, queries: &[&PublishedQuery]) -> Result<Vec<&PublishedStorage>, String> {
        let mut pending: Vec<&PublishedStorage> = vec![];
        for query in queries {
            for name in &query.uses {
                pending.push(self.storage_read_by(&query.crate_src, name)?);
            }
        }
        let mut needed: BTreeMap<String, &PublishedStorage> = BTreeMap::new();
        while let Some(storage) = pending.pop() {
            if needed.insert(storage.label(), storage).is_none() {
                pending.extend(self.sources_of(storage)?);
            }
        }
        let mut ordered: Vec<&PublishedStorage> = vec![];
        let mut placed: BTreeSet<String> = BTreeSet::new();
        while ordered.len() < needed.len() {
            let ready: Vec<&PublishedStorage> = needed
                .values()
                .filter(|s| !placed.contains(&s.label()))
                .filter(|s| self.sources_of(s).is_ok_and(|sources| sources.iter().all(|source| placed.contains(&source.label()))))
                .copied()
                .collect();
            if ready.is_empty() {
                return Err("published_storage_cycle: the published storages' built_from sources form a cycle".into());
            }
            for storage in ready {
                placed.insert(storage.label());
                ordered.push(storage);
            }
        }
        Ok(ordered)
    }
}

impl PublishedQuery {
    fn read(name: &str, crate_src: &Path, sql: &Path) -> Result<Self, String> {
        if !crate_src.join("agent").is_dir() {
            return Err(format!("published query {name}: {} has no agent/ (not a query crate)", crate_src.display()));
        }
        let sql = fs::read_to_string(sql).map_err(|e| format!("published query {name}: its template {}: {e}", sql.display()))?;
        let stores = crate_src.join("stores.rs");
        let listing = fs::read_to_string(&stores).map_err(|e| format!("published query {name}: {}: {e}", stores.display()))?;
        let uses = listing.lines().filter_map(|line| line.trim().strip_prefix("pub mod ")?.strip_suffix(';').map(str::to_string)).collect();
        Ok(Self { name: name.to_string(), crate_src: crate_src.to_path_buf(), sql, uses, compiler: compiler_choice(crate_src)? })
    }
}

impl PublishedStorage {
    fn read(root: &Path, label: &str, dir: &Path) -> Result<Self, String> {
        let malformed = || format!("published storage crate {}: its folder is named <storage>-v<N>", dir.display());
        let (name, version) = label.rsplit_once("-v").ok_or_else(malformed)?;
        let version: u32 = version.parse().map_err(|_| malformed())?;
        let crate_src = dir.join("src");
        for root_dir in [crate_src.join("stores").join(name).join("interface"), crate_src.join("builder")] {
            if !root_dir.is_dir() {
                return Err(format!("published storage {label}: {} is missing (not a storage crate)", root_dir.display()));
            }
        }
        let path = root.join("storage").join(name).join(format!("v{version}")).join("manifest.json");
        let text = fs::read(&path).map_err(|e| format!("published storage {label}: its manifest {}: {e}", path.display()))?;
        let manifest: PublishedManifest = serde_json::from_slice(&text).map_err(|e| format!("published storage {label}: {}: {e}", path.display()))?;
        if manifest.name != name {
            return Err(format!("published storage {label}: its manifest names storage {}", manifest.name));
        }
        let compiler = compiler_choice(&crate_src)?;
        Ok(Self { name: name.to_string(), version, crate_src, manifest, compiler })
    }

    /// The storage manifest of the import: the published manifest with the crate directory `crate`, modules derived
    /// from the files, the published compiler choice (`compile.json`, else the default), `sources` (the admitted
    /// packages of its derivation's sources, in use order) as its `built_from`, and placeholder texts for the
    /// descriptive fields the published manifest omits.
    pub fn import_manifest(&self, sources: &[(String, ContentId)], provenance: &str) -> Result<StorageManifest, String> {
        let published = &self.manifest;
        let published_sources: Vec<&String> = published.built_from.iter().flat_map(|d| &d.sources).collect();
        if sources.iter().map(|(name, _)| name).ne(published_sources.iter().copied()) {
            return Err(format!("published storage {}: its derivation names the sources {published_sources:?}, the import gives {}", self.label(), sources.len()));
        }
        let built_from = published.built_from.as_ref().map(|derivation| BuiltFrom {
            sources: sources.iter().map(|(name, package)| SourceStorage { name: name.clone(), admitted: *package }).collect(),
            extends: derivation.extends.clone(),
        });
        let mut data_policy = published.data_policy.clone();
        for entry in data_policy.as_array_mut().into_iter().flatten() {
            if let Some(fields) = entry.as_object_mut() {
                fields.entry("why").or_insert_with(|| json!(IMPORTED_PART_WHY));
            }
        }
        let data_policy: DataPolicy = match data_policy {
            Value::Null => DataPolicy::default(),
            other => serde_json::from_value(other).map_err(|e| format!("published storage {}: data_policy: {e}", self.label()))?,
        };
        Ok(StorageManifest {
            format_version: 1,
            name: self.name.clone(),
            crate_dir: SEED_CRATE_DIRECTORY.into(),
            tables: published.tables.clone(),
            parts: published.parts.clone(),
            layout: StorageLayout {
                summary: published.layout.summary.clone(),
                units: published.layout.units.clone(),
                choice: published.layout.choice.clone().unwrap_or_else(|| IMPORTED_LAYOUT_CHOICE.into()),
            },
            data_policy,
            modules: vec![],
            compiler: self.compiler.clone(),
            notes: format!("imported from the published storage {provenance}"),
            uses_declared_constraints: self.uses_declared_constraints(),
            built_from,
        })
    }
}

/// Write the published storage's author files and its import manifest into `workspace/<name>-v<N>/` (replacing an
/// earlier seed there): `verus-storage.json`, and `crate/src/stores/<name>/interface/**` and `crate/src/builder/**`
/// copied from the published crate. `sources`: the admitted packages of its derivation's sources, in use order.
/// Returns the manifest's workspace-relative path.
pub fn seed_storage_workspace(storage: &PublishedStorage, sources: &[(String, ContentId)], workspace: &Path) -> Result<PathBuf, String> {
    let manifest = storage.import_manifest(sources, &storage.crate_src.display().to_string())?;
    let seed = workspace.join(storage.label());
    replace_directory(&seed)?;
    let (interface, builder) = manifest.author_roots();
    let crate_src = seed.join(SEED_CRATE_DIRECTORY).join("src");
    for root in [interface, builder] {
        copy_author_tree(&storage.crate_src.join(&root), &crate_src.join(&root))?;
    }
    write_json(&seed.join(STORAGE_MANIFEST_FILE), &manifest)?;
    Ok(PathBuf::from(storage.label()).join(STORAGE_MANIFEST_FILE))
}

/// Write the published query's author files and its import manifest into `workspace/import/` (replacing an earlier
/// seed there): `verus-query.json` (each of `uses` an admitted package, in use order; every agent file declared, `mod.rs`
/// as the entry with `query`, the others as helpers whose items Verus reports; the published compiler choice) and
/// `crate/src/agent/**` copied from the published crate. Returns the submission that freezes it.
pub fn seed_query_workspace(query: &PublishedQuery, uses: &[(String, ContentId)], workspace: &Path) -> Result<CandidateSubmission, String> {
    if uses.iter().map(|(name, _)| name).ne(query.uses.iter()) {
        return Err(format!("published query {}: it reads {:?}, the import names {:?}", query.name, query.uses, uses.iter().map(|(n, _)| n).collect::<Vec<_>>()));
    }
    let seed = workspace.join(QUERY_SEED_DIRECTORY);
    replace_directory(&seed)?;
    let agent = seed.join(SEED_CRATE_DIRECTORY).join("src/agent");
    let files = copy_author_tree(&query.crate_src.join("agent"), &agent)?;
    let modules = files
        .iter()
        .map(|file| {
            let file = file.to_string_lossy().into_owned();
            match file == "mod.rs" {
                true => ModuleDeclaration { file, role: ModuleRole::Entry, items: REQUIRED_ITEMS.map(String::from).to_vec() },
                false => ModuleDeclaration { file, role: ModuleRole::Helper, items: vec![] },
            }
        })
        .collect();
    let manifest = QueryManifest {
        format_version: 2,
        crate_dir: SEED_CRATE_DIRECTORY.into(),
        storage_uses: uses.iter().map(|(name, package)| StorageUseDeclaration::admitted(name, *package)).collect(),
        modules,
        compiler: query.compiler.clone(),
        notes: format!("imported from the published query crate {}", query.crate_src.display()),
    };
    write_json(&seed.join(MANIFEST_FILE), &manifest)?;
    Ok(CandidateSubmission {
        candidate_manifest: PathBuf::from(QUERY_SEED_DIRECTORY).join(MANIFEST_FILE),
        rationale: format!("the published package {} (gendb import)", query.name),
        data_access_analysis: "as published; no author was called".into(),
    })
}

/// The compiler choice in `compile.json` beside the crate source `crate_src` (`<crate>/compile.json`); `None` without the
/// file. Refused by name when the file is not a valid choice.
fn compiler_choice(crate_src: &Path) -> Result<Option<CompilerChoice>, String> {
    let path = crate_src.parent().unwrap_or(crate_src).join(COMPILE_FILE);
    if !path.is_file() {
        return Ok(None);
    }
    let text = fs::read(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let choice: CompilerChoice = serde_json::from_slice(&text).map_err(|e| format!("published_compile_invalid: {}: {e}", path.display()))?;
    if choice.opt_level > 3 {
        return Err(format!("published_compile_invalid: {}: opt_level must be 0..=3", path.display()));
    }
    Ok(Some(choice))
}

/// The interface files of storage `name` in the crate at `crate_src` (`stores/<name>/interface/**`), by relative path.
fn interface_files(crate_src: &Path, name: &str) -> Result<BTreeMap<PathBuf, Vec<u8>>, String> {
    author_tree(&crate_src.join("stores").join(name).join("interface")).map(|files| files.into_iter().collect())
}

/// Every file under the author directory `dir` with its bytes, by path relative to `dir`, sorted. Only regular files
/// and directories are allowed (a symbolic link or another kind of entry is refused by name, so nothing outside the
/// published crate is read).
fn author_tree(dir: &Path) -> Result<Vec<(PathBuf, Vec<u8>)>, String> {
    if !dir.is_dir() {
        return Err(format!("{} is not a directory", dir.display()));
    }
    let mut files = vec![];
    let mut pending = vec![dir.to_path_buf()];
    while let Some(current) = pending.pop() {
        for entry in fs::read_dir(&current).map_err(|e| format!("{}: {e}", current.display()))? {
            let path = entry.map_err(|e| format!("{}: {e}", current.display()))?.path();
            let kind = fs::symlink_metadata(&path).map_err(|e| format!("{}: {e}", path.display()))?.file_type();
            if kind.is_dir() {
                pending.push(path);
            } else if kind.is_file() {
                let relative = path.strip_prefix(dir).map_err(|e| e.to_string())?.to_path_buf();
                files.push((relative, fs::read(&path).map_err(|e| format!("{}: {e}", path.display()))?));
            } else {
                return Err(format!("published_author_file_refused: {} is not a regular file or directory", path.display()));
            }
        }
    }
    files.sort();
    Ok(files)
}

/// Copy the author tree `from` to the fresh directory `to`; the copied files' relative paths.
fn copy_author_tree(from: &Path, to: &Path) -> Result<Vec<PathBuf>, String> {
    let files = author_tree(from)?;
    for (relative, bytes) in &files {
        if relative.components().any(|c| !matches!(c, Component::Normal(_))) {
            return Err(format!("published_author_file_refused: {} is not a plain relative path", relative.display()));
        }
        let target = to.join(relative);
        fs::create_dir_all(target.parent().expect("a file path")).map_err(|e| format!("{}: {e}", target.display()))?;
        fs::write(&target, bytes).map_err(|e| format!("{}: {e}", target.display()))?;
    }
    fs::create_dir_all(to).map_err(|e| format!("{}: {e}", to.display()))?;
    Ok(files.into_iter().map(|(relative, _)| relative).collect())
}

/// The subdirectories of `dir` by name, sorted.
fn subdirectories(dir: &Path) -> Result<Vec<(String, PathBuf)>, String> {
    let mut found = vec![];
    for entry in fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))? {
        let path = entry.map_err(|e| format!("{}: {e}", dir.display()))?.path();
        if path.is_dir()
            && let Some(name) = path.file_name().and_then(|n| n.to_str())
        {
            found.push((name.to_string(), path.clone()));
        }
    }
    found.sort();
    Ok(found)
}

/// Remove `dir` (an earlier seed written by this module) and create it empty.
fn replace_directory(dir: &Path) -> Result<(), String> {
    if dir.exists() {
        fs::remove_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    }
    fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let text = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    fs::write(path, text).map_err(|e| format!("{}: {e}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::test_support::scratch_root;

    const PACKAGE: [u8; 32] = [7; 32];

    fn write(path: &Path, text: &str) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    /// A run folder: storage `base` (from source columns), `extra` built from `base` (extending it), and query `q1`
    /// reading `extra` and `base`, each crate with a framework file that does not matter (tampered on purpose).
    fn run_folder(root: &Path) -> PathBuf {
        let run = root.join("published");
        let manifest = |name: &str, built_from: Value| {
            json!({"name":name,"tables":[{"table":"t","columns":["a"]}],"parts":["t.a: I64 values"],
                "data_policy":[{"part":0,"table":"t","kind":"base_payload","columns":["a"]}],
                "layout":{"summary":"one part","units":"rows"},"built_from":built_from})
        };
        for (name, built_from) in [("base", Value::Null), ("extra", json!({"sources":["base"],"extends":"base"}))] {
            let src = run.join(format!("crates/storages/{name}-v1/src"));
            write(&src.join(format!("stores/{name}/interface/mod.rs")), &format!("// interface of {name}\n"));
            write(&src.join("builder/mod.rs"), &format!("// builder of {name}\n"));
            write(&src.join("gendb_entry.rs"), "// TAMPERED fixed entry: proves nothing\n");
            write(&run.join(format!("storage/{name}/v1/manifest.json")), &manifest(name, built_from).to_string());
        }
        let extra = run.join("crates/storages/extra-v1/src");
        write(&extra.join("stores/base/interface/mod.rs"), "// interface of base\n");
        let query = run.join("crates/queries/q1/src");
        write(&run.join("crates/queries/q1/compile.json"), r#"{"opt_level": 3, "target_cpu": "native"}"#);
        write(&query.join("agent/mod.rs"), "pub fn query() {}\n");
        write(&query.join("agent/scan/kernel.rs"), "// a helper\n");
        write(&query.join("stores.rs"), "// FRAMEWORK FILE: the storages this crate carries.\npub mod extra;\npub mod base;\n");
        write(&query.join("stores/extra/interface/mod.rs"), "// interface of extra\n");
        write(&query.join("stores/base/interface/mod.rs"), "// interface of base\n");
        write(&query.join("gendb_entry.rs"), "// TAMPERED fixed entry: ensures true\n");
        write(&query.join("query.rs"), "// TAMPERED statement\n");
        write(&run.join("queries/q1/query.sql"), "SELECT a FROM t WHERE a > $1;\n");
        run
    }

    /// Queries match by template text; storages resolve by interface text and are planned sources first; a query
    /// reading a storage version that is not published is refused by name.
    #[test]
    fn queries_match_by_template_and_storages_resolve_by_interface() {
        let root = scratch_root("published-run");
        let run = PublishedRun::read(&run_folder(&root)).unwrap();
        assert_eq!(run.queries.len(), 1);
        assert_eq!(run.queries[0].uses, ["extra", "base"]);
        assert_eq!(run.queries_for_sql("  SELECT a FROM t WHERE a > $1;").len(), 1, "white space around the template is ignored");
        assert!(run.queries_for_sql("SELECT a FROM t WHERE a > $2;").is_empty());
        let plan: Vec<String> = run.storage_plan(&[&run.queries[0]]).unwrap().iter().map(|s| s.label()).collect();
        assert_eq!(plan, ["base-v1", "extra-v1"], "a storage follows its sources");
        write(&run.queries[0].crate_src.join("stores/base/interface/mod.rs"), "// another interface\n");
        let missing = run.storage_plan(&[&run.queries[0]]).unwrap_err();
        assert!(missing.starts_with("published_storage_missing") && missing.contains("base-v1"), "{missing}");
        fs::remove_dir_all(root).unwrap();
    }

    /// Only the author files reach the workspace: the query's agent tree with a manifest that pins the admitted uses and
    /// declares every agent file; no published framework file (tampered here) is copied. A symbolic link in an author
    /// tree is refused by name.
    #[test]
    fn a_query_seed_takes_the_agent_files_only() {
        let root = scratch_root("published-query-seed");
        let run = PublishedRun::read(&run_folder(&root)).unwrap();
        let workspace = root.join("author");
        let package = ContentId::from_bytes(PACKAGE);
        let uses = [("extra".to_string(), package), ("base".to_string(), package)];
        let submission = seed_query_workspace(&run.queries[0], &uses, &workspace).unwrap();
        assert_eq!(submission.candidate_manifest, Path::new("import/verus-query.json"));
        let seeded: Vec<PathBuf> = author_tree(&workspace).unwrap().into_iter().map(|(path, _)| path).collect();
        assert_eq!(seeded, [Path::new("import/crate/src/agent/mod.rs"), Path::new("import/crate/src/agent/scan/kernel.rs"), Path::new("import/verus-query.json")]);
        let manifest: QueryManifest = serde_json::from_slice(&fs::read(workspace.join("import/verus-query.json")).unwrap()).unwrap();
        assert_eq!(manifest.storage_uses, [StorageUseDeclaration::admitted("extra", package), StorageUseDeclaration::admitted("base", package)]);
        assert_eq!(manifest.modules[0], ModuleDeclaration { file: "mod.rs".into(), role: ModuleRole::Entry, items: vec!["query".into()] });
        assert_eq!((manifest.modules[1].file.as_str(), manifest.modules[1].role), ("scan/kernel.rs", ModuleRole::Helper));
        assert_eq!(manifest.compiler, Some(CompilerChoice { opt_level: 3, target_cpu: Some("native".into()) }), "the published compile.json");
        assert_eq!(seed_query_workspace(&run.queries[0], &uses, &workspace).unwrap(), submission, "seeding again gives the same seed");
        assert!(seed_query_workspace(&run.queries[0], &uses[..1], &workspace).unwrap_err().contains("reads"), "the uses must be the published ones");
        std::os::unix::fs::symlink("/etc/hostname", run.queries[0].crate_src.join("agent/link.rs")).unwrap();
        assert!(seed_query_workspace(&run.queries[0], &uses, &workspace).unwrap_err().starts_with("published_author_file_refused"));
        fs::remove_dir_all(root).unwrap();
    }

    /// A storage seed holds its two author roots and the import manifest: the published columns, parts and declaration
    /// (a missing `why` filled), the derivation pinned to the sources' admitted packages, entry v2 exactly when the crate
    /// carries `gendb_constraints.rs`; the tampered framework file is not copied.
    #[test]
    fn a_storage_seed_takes_its_author_roots_and_the_published_manifest() {
        let root = scratch_root("published-storage-seed");
        let run = PublishedRun::read(&run_folder(&root)).unwrap();
        let workspace = root.join("author");
        let package = ContentId::from_bytes(PACKAGE);
        let extra = run.storages.iter().find(|s| s.name == "extra").unwrap();
        let relative = seed_storage_workspace(extra, &[("base".into(), package)], &workspace).unwrap();
        assert_eq!(relative, Path::new("extra-v1/verus-storage.json"));
        let seeded: Vec<PathBuf> = author_tree(&workspace.join("extra-v1")).unwrap().into_iter().map(|(path, _)| path).collect();
        assert_eq!(seeded, [Path::new("crate/src/builder/mod.rs"), Path::new("crate/src/stores/extra/interface/mod.rs"), Path::new("verus-storage.json")]);
        let manifest: StorageManifest = serde_json::from_slice(&fs::read(workspace.join(&relative)).unwrap()).unwrap();
        manifest.check().unwrap();
        assert_eq!(manifest.built_from, Some(BuiltFrom { sources: vec![SourceStorage { name: "base".into(), admitted: package }], extends: Some("base".into()) }));
        let DataPolicy::Parts(parts) = &manifest.data_policy else { panic!("a per-part declaration") };
        assert_eq!((parts[0].why.as_str(), manifest.uses_declared_constraints), (IMPORTED_PART_WHY, false));
        assert_eq!(manifest.compiler, None, "no compile.json: the default compiler choice");
        write(&run.root.join("crates/storages/base-v1/compile.json"), r#"{"opt_level": 9}"#);
        assert!(PublishedRun::read(&run.root).unwrap_err().starts_with("published_compile_invalid"), "an invalid choice is refused by name");
        assert!(seed_storage_workspace(extra, &[], &workspace).unwrap_err().contains("sources"), "every source needs its package");
        write(&extra.crate_src.join("gendb_constraints.rs"), "// declared constraints\n");
        assert!(extra.import_manifest(&[("base".into(), package)], "p").unwrap().uses_declared_constraints);
        fs::remove_dir_all(root).unwrap();
    }

    /// The one-query layout: `query.sql` beside `crates/<name>/`.
    #[test]
    fn a_one_query_folder_names_its_crate() {
        let root = scratch_root("published-one-query");
        let folder = root.join("example");
        write(&folder.join("query.sql"), "SELECT COUNT(*) AS n FROM readings WHERE value > $1;");
        write(&folder.join("crates/example/src/agent/mod.rs"), "pub fn query() {}\n");
        write(&folder.join("crates/example/src/stores.rs"), "pub mod flat_readings;\n");
        let run = PublishedRun::read(&folder).unwrap();
        assert_eq!((run.queries[0].name.as_str(), run.queries[0].uses.as_slice(), run.storages.len()), ("example", ["flat_readings".to_string()].as_slice(), 0));
        assert_eq!(run.queries_for_sql("SELECT COUNT(*) AS n FROM readings WHERE value > $1;\n").len(), 1);
        assert!(PublishedRun::read(&root).unwrap_err().contains("neither a run"));
        fs::remove_dir_all(root).unwrap();
    }
}
