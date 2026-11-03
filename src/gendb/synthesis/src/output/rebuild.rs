//! Framework versions in the library and `gendb rebuild qNN`: the full crate of a published query, assembled from the
//! library (framework files, kept once as the blobs of the admitted build record) and the output home (author code).

use super::{OutputError, io_error, read_json, write_json, write_text};
use gendb_artifacts::verus::{VerusBuildV1, VerusSourceOwnerV1};
use gendb_artifacts::{ContentId, ObjectStore};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

fn open_build(library: &Path, build: &str) -> Result<(ObjectStore, VerusBuildV1), OutputError> {
    let store = ObjectStore::open_existing(library).map_err(|e| io_error(library, e))?;
    let id = ContentId::parse_hex(build).map_err(|e| OutputError(format!("build id {build}: {e}")))?;
    let record: VerusBuildV1 = store.read(id).and_then(|o| o.decode()).map_err(|e| OutputError(format!("build record {build}: {e}")))?;
    Ok((store, record))
}

/// Record the framework version of an admitted build: `<library>/framework/<kind>-<version>.json` lists every
/// framework-owned file of the build (path, blob, bytes); the blobs themselves are the library's single copy. The
/// version is the first 12 hex digits of the SHA-256 of that list, so equal framework files share one manifest. Returns
/// the manifest's path relative to the library.
pub(crate) fn record_framework_version(library: &Path, build: &str, kind: &str) -> Result<String, OutputError> {
    let (_, record) = open_build(library, build)?;
    let files: Vec<_> = record
        .sources
        .iter()
        .filter(|s| s.owner == VerusSourceOwnerV1::Framework)
        .map(|s| json!({"path":s.path,"blob":s.blob.to_hex(),"bytes":s.bytes}))
        .collect();
    let listing = serde_json::to_string(&files).unwrap_or_default();
    let version: String = Sha256::digest(listing.as_bytes()).iter().take(6).map(|b| format!("{b:02x}")).collect();
    let relative = format!("framework/{kind}-{version}.json");
    let path = library.join(&relative);
    if !path.exists() {
        write_json(&path, &json!({"kind":kind,"version":version,"files":files,
            "meaning":"the framework files of a GenDB crate (fixed entry, SQLSpec library, ABI, generated statement files), stored once as library blobs; author files are not listed"}))?;
    }
    Ok(relative)
}

/// Assemble the full crate of query `query` of the output `home` under `out` (`out/src/...`): framework files from the
/// library blobs of its admitted build, the author's `agent/` from `queries/<query>/code/`, every storage interface
/// copy from the published folder of the exact storage version the query reads (`storage_versions` of its rebuild
/// record). A record written before storage versions, or a missing version folder, is refused by name (republish the
/// query with `gendb output query`); no other version of the name is ever used. Writes `out/README.md` with the Verus
/// invocation of the build. Returns `out`.
pub fn rebuild(home: &Path, query: &str, out: &Path) -> Result<PathBuf, OutputError> {
    let plan_path = home.join("records/queries").join(query).join("rebuild.json");
    let plan = read_json(&plan_path).ok_or_else(|| OutputError(format!("{}: no rebuild record (was the query published?)", plan_path.display())))?;
    let library = PathBuf::from(plan["library"].as_str().ok_or_else(|| OutputError("rebuild record without library".into()))?);
    let build = plan["build"].as_str().ok_or_else(|| OutputError(format!("{query} has no selected build")))?;
    let (store, record) = open_build(&library, build)?;
    let versions = plan["storage_versions"].as_array().ok_or_else(|| {
        OutputError(format!("{query}: its rebuild record predates storage versions (no storage_versions); republish it with `gendb output query`"))
    })?;
    let folders: Vec<(String, PathBuf)> = versions
        .iter()
        .map(|v| match (v["name"].as_str(), v["folder"].as_str()) {
            (Some(name), Some(folder)) if home.join(folder).is_dir() => Ok((name.to_string(), home.join(folder))),
            _ => Err(OutputError(format!("{query}: storage version {v} is not published in {} (republish with `gendb output query`)", home.display()))),
        })
        .collect::<Result<_, _>>()?;
    for source in &record.sources {
        let target = out.join("src").join(&source.path);
        let text = match source.owner {
            VerusSourceOwnerV1::Framework => {
                let bytes = store.read_blob(source.blob, Some(source.bytes)).map_err(|e| OutputError(format!("{}: {e}", source.path)))?;
                String::from_utf8(bytes).map_err(|e| OutputError(format!("{}: {e}", source.path)))?
            }
            VerusSourceOwnerV1::Agent => {
                let from = author_file(home, query, &folders, &source.path)?;
                std::fs::read_to_string(&from).map_err(|e| io_error(&from, e))?
            }
        };
        write_text(&target, &text)?;
    }
    write_text(
        &out.join("README.md"),
        &format!(
            "# {query} crate (rebuilt)\n\nAssembled by `gendb rebuild {query}` from the library `{}` (framework files) and the output home (author code). The admitted build ran:\n\n```\nrust_verify {}\n```\n\nwith environment {:?}.\n",
            library.display(),
            record.argv.join(" "),
            record.environment
        ),
    )?;
    Ok(out.to_path_buf())
}

/// Where the output home keeps an author file of a query crate: `agent/**` in the query's `code/`, a storage interface
/// copy `stores/<name>/interface/**` in the `interface/` of the version folder `folders` names for it.
fn author_file(home: &Path, query: &str, folders: &[(String, PathBuf)], path: &str) -> Result<PathBuf, OutputError> {
    if let Some(rest) = path.strip_prefix("agent/") {
        return Ok(home.join("queries").join(query).join("code").join(rest));
    }
    if let Some(rest) = path.strip_prefix("stores/")
        && let Some((name, file)) = rest.split_once("/interface/")
    {
        let (_, folder) = folders.iter().find(|(n, _)| n == name).ok_or_else(|| OutputError(format!("{query}: the build reads storage {name}, which its rebuild record does not list")))?;
        return Ok(folder.join("interface").join(file));
    }
    Err(OutputError(format!("author file {path} has no place in the output home")))
}
