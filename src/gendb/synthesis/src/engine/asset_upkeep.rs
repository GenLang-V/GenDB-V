//! When the general line releases the run library's superseded storage assets, and which heads keep theirs (the
//! rule and the release itself: `storage::asset_release`).
//!
//! The heads ([`kept_heads`]) are the main-line head and every branch's head: the versions the next evaluations are
//! judged against (a branch session's parent, a merge's or a rebase's main-line head) and the main line serves. Their
//! assets stay at every capture; every other derived storage asset that admitted versions read is released.
//!
//! A release pass ([`release_pass`]) runs only when no other evaluation can be reading an asset it releases:
//! - after an admission (`engine::acceptance`, once the version's records and its main-line decision are written),
//!   when the run has one branch: that evaluation is then the only one, and its timings are over;
//! - after a scale move (`engine::branches`), when no session runs;
//! - at a controller start with no open session (`engine::branches::run_general_engine`): an open session may resume
//!   an admission whose storages the pass would otherwise release.
//!
//! A pass never fails its caller: its record, or its error, is one line of `<run>/engine/asset-releases.jsonl`, and an
//! error is also flagged for the operator (`flags.jsonl`).
//!
//! A run of several workloads (`engine::stage`: a stage run or `engine.workloads`) has one library per workload, all
//! admitting every version in lockstep (`vNNN` is version NNN + 1 of each), so the same heads are kept in each:
//! [`release_workload_pass`] runs a pass over one workload's library and names the workload in its log line.

use super::tree::{self, MAIN, VersionTree, append_flag, version_number};
use crate::controller::records::now_unix_ms;
use crate::storage::asset_release::{KeptHead, release_superseded_assets};
use gendb_artifacts::ObjectStore;
use gendb_artifacts::verus::engine_versions;
use gendb_verification::admission::AdmissionError;
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::path::Path;

/// The log of release passes under the run's engine directory, one line per pass.
pub const RELEASES_FILE: &str = "asset-releases.jsonl";

/// The heads whose storage assets stay (module documentation), with the storages each reads, from the version tree
/// and the library's admitted versions.
pub fn kept_heads(tree: &VersionTree, store: &ObjectStore) -> Result<Vec<KeptHead>, AdmissionError> {
    let branches: BTreeSet<&str> = tree.versions().map(|n| n.branch.as_str()).filter(|b| *b != MAIN).collect();
    let heads: BTreeSet<&str> = tree.main_line_head().into_iter().chain(branches.iter().filter_map(|b| tree.branch_head(b))).collect();
    let versions = engine_versions(store).map_err(AdmissionError::tool)?;
    heads
        .into_iter()
        .map(|head| {
            let number = version_number(head).ok_or_else(|| AdmissionError::tool(format!("head {head} is not a version id")))?;
            let version = versions.iter().find(|v| v.version == number + 1).ok_or_else(|| AdmissionError::tool(format!("head {head} is not an admitted engine version of the library")))?;
            Ok(KeptHead { version: head.to_string(), uses: version.package.storage_uses.clone() })
        })
        .collect()
}

/// One release pass over the run library `library` (`why`: what triggered it), logged under `engine_dir`. Returns the
/// pass's record, or `{"error": ...}` when it failed (logged and flagged; module documentation).
pub fn release_pass(library: &Path, engine_dir: &Path, why: &str) -> Value {
    release(library, engine_dir, why, None)
}

/// [`release_pass`] over the library of the workload `workload` of a run of several workloads (module documentation): its log line and any flag
/// name the workload.
pub fn release_workload_pass(library: &Path, engine_dir: &Path, why: &str, workload: &str) -> Value {
    release(library, engine_dir, why, Some(workload))
}

/// One release pass ([`release_pass`]), its record naming `workload` when given.
fn release(library: &Path, engine_dir: &Path, why: &str, workload: Option<&str>) -> Value {
    let outcome = (|| -> Result<Value, AdmissionError> {
        let store = ObjectStore::open_existing(library).map_err(AdmissionError::tool)?;
        let tree = VersionTree::read(engine_dir).map_err(AdmissionError::tool)?;
        release_superseded_assets(&store, &kept_heads(&tree, &store)?, why)
    })();
    let mut record = outcome.unwrap_or_else(|error| {
        let failed = json!({"at_unix_ms":now_unix_ms(),"why":why,"error":error.to_string()});
        let of = workload.map_or_else(String::new, |w| format!(" (workload {w})"));
        let _ = append_flag(engine_dir, &json!({"at_unix_ms":now_unix_ms(),"kind":"asset_release","reason":format!("a release of superseded storage assets failed{of}: {error}")}));
        failed
    });
    if let Some(workload) = workload {
        record["workload"] = json!(workload);
        record["library"] = json!(library);
    }
    if let Err(error) = tree::append_line(&engine_dir.join(RELEASES_FILE), &record) {
        let _ = append_flag(engine_dir, &json!({"at_unix_ms":now_unix_ms(),"kind":"asset_release","reason":format!("the release log could not be written: {error}")}));
    }
    record
}

/// A pass that did not run (`why` and the reason), logged like a pass.
pub fn record_skipped(engine_dir: &Path, why: &str, reason: &str) {
    let record = json!({"at_unix_ms":now_unix_ms(),"why":why,"skipped":reason});
    let _ = tree::append_line(&engine_dir.join(RELEASES_FILE), &record);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::tree::{MainLineChange, NodeKind, TreeNode, append_main_line, read_lines, write_node};
    use crate::storage::asset_release::tests::line;
    use crate::storage::engine_library::tests::{capture, remove_scratch};
    use gendb_artifacts::ContentId;
    use gendb_artifacts::verus::{resolve_storage_asset, VerusStoragePackageV1};

    /// The records of a run whose versions are `nodes` (`(id, branch)`, v000 on `main`) and whose main-line head is
    /// `head`, under `<root>/<name>/engine`.
    fn run_records(root: &Path, name: &str, nodes: &[(&str, &str)], head: &str) -> std::path::PathBuf {
        let engine_dir = root.join(name).join("engine");
        std::fs::create_dir_all(&engine_dir).unwrap();
        for (index, (id, branch)) in nodes.iter().enumerate() {
            let kind = if *branch == MAIN { NodeKind::FrameworkGenerated } else { NodeKind::Branch };
            let parents = if index == 0 { vec![] } else { vec![nodes[index - 1].0.to_string()] };
            let node = TreeNode { format_version: 1, id: (*id).into(), accepted: true, kind, branch: (*branch).into(), parents, scale: "sf1".into(), score: None, reason: None,
                session: None, iteration: None, direction: None, rationale: None, created_unix_ms: index as u64 };
            write_node(&engine_dir, &node).unwrap();
        }
        let changes = if head == "v000" { vec![("v000", None)] } else { vec![("v000", None), (head, Some("v000"))] };
        for (version, previous) in changes {
            let change = MainLineChange { version: version.into(), previous: previous.map(String::from), reason: "race".into(), scale: "sf1".into(), race: None, adopted: None,
                selection: ContentId::from_bytes([1; 32]), at_unix_ms: 1 };
            append_main_line(&engine_dir, &change).unwrap();
        }
        engine_dir
    }

    /// Done-check 1 through the run's records: with a second branch whose head is v001, nothing is released (every
    /// head keeps its storages); on one line (v001 and v002 on b1, v002 the head), the pass after v002's admission keeps
    /// v002's assets and releases v001's narrow, one line in `asset-releases.jsonl`. A pass that cannot read the
    /// library is logged and flagged for the operator, never raised.
    #[test]
    fn a_pass_keeps_every_heads_assets_and_logs_what_it_released() {
        let root = crate::controller::test_support::scratch_root("asset-upkeep");
        let line = line(&root);
        let library = root.join("engine");
        let branches = run_records(&root, "branches", &[("v000", MAIN), ("v001", "b2"), ("v002", "b1")], "v002");
        let heads = kept_heads(&VersionTree::read(&branches).unwrap(), &line.library.store).unwrap();
        assert_eq!(heads.iter().map(|h| h.version.as_str()).collect::<Vec<_>>(), ["v001", "v002"]);
        assert_eq!(release_pass(&library, &branches, "admission of v002")["released_assets"].as_u64(), Some(0));
        let one_line = run_records(&root, "one-line", &[("v000", MAIN), ("v001", "b1"), ("v002", "b1")], "v002");
        let record = release_pass(&library, &one_line, "admission of v002");
        assert_eq!(record["released_assets"].as_u64(), Some(2), "{record:#}");
        let logged = read_lines(&one_line.join(RELEASES_FILE)).unwrap();
        assert_eq!((logged.len(), &logged[0]["heads"][0]["version"]), (1, &serde_json::json!("v002")));
        let package: VerusStoragePackageV1 = line.library.store.read(line.old).unwrap().decode().unwrap();
        assert!(resolve_storage_asset(&line.library.store, &capture().asset_key(line.old, &package).unwrap()).unwrap().is_none());
        let failed = release_pass(&root.join("no-library"), &one_line, "controller start");
        assert!(failed["error"].is_string(), "{failed:#}");
        let flags = read_lines(&one_line.join(tree::FLAGS_FILE)).unwrap();
        assert!(flags.len() == 1 && flags[0]["kind"] == "asset_release", "{flags:?}");
        remove_scratch(&root);
    }
}
