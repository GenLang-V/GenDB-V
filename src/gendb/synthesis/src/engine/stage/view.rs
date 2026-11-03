//! The stage view of a session's context (whose exact keys are the fixture
//! `prompts/engine_facts/general/stage-fixture.json`, `context.stage`; rendered by `prompts::engine_facts::general::
//! stage`). A session's preparation puts it in `general.stage`; the role's refreshed facts put a fresh copy in the
//! top-level `stage` before every call, which the prompt reads first.
//!
//! - `goal`; `seed` `{run, version, out_of_the_box}` (the out-of-the-box record's view, `root::OutOfTheBox::view`);
//! - `workloads[]`, the goal first, each with its name, role, scale, first scale, library and training facts (from its
//!   prepared inputs), then from the run's records: `head` (the main-line head), the head's `cells`, `score`, `storage`
//!   (budget, plain bytes, the head's serving bytes, whether it reads only the plain storage, the original data record)
//!   and `module_lines` on this workload (`records::WorkloadRecord`), and for a kept workload `last_race` (the head's
//!   race against its parent on this workload; null at the root) and `reference` (the root's timing of the seed here).
//!
//! A run of several workloads (`engine.workloads`; whose exact keys are the fixture
//! `prompts/engine_facts/general/workloads-fixture.json`, `context.workloads` and `context.combined_score`; rendered by
//! `prompts::engine_facts::general::workloads`) has the **workloads view** instead ([`workloads_view`]): a
//! session's preparation puts it in `general.workloads` and `general.combined_score`, the refreshed facts a fresh copy
//! in the top-level `workloads` and `combined_score`. Each workload, the primary first: its name, role, whether it is the
//! primary, scale, first scale, library and training facts; then from the run's records: `head`, `side_origin` (the
//! root's record of its side, `version.json` `workloads.<name>.origin` of `v000`), the head's `cells` and `score` (null
//! for a check workload), `totals_ms` and `targets_ms` (the head's totals and the faster baseline's per worker count,
//! scored as `engine::score` scores them), `budget` (`exempt` for a check workload), `serving_bytes`, `general` (its
//! own module, inherited and family storages, plans), and `last_race` (counted and kept) or `last_check` (check). The
//! combined score is the head's (`version.json` `combined_score`) with `head`.

use super::records::{WorkloadRecord, read_workload_record};
use super::root::OutOfTheBox;
use crate::controller::records::read_json;
use crate::controller::request::{MemberRole, Seed, SeedVersion};
use crate::engine::role::{EngineBench, EngineInputs, FirstScale};
use crate::engine::score::{CellResult, score};
use crate::engine::totals::Baselines;
use crate::engine::tree::{ROOT_VERSION, VersionTree, node_directory};
use crate::prompts::engine_contract::WorkloadRole;
use gendb_artifacts::ContentId;
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// One workload as the stage view shows it, from its prepared inputs (plain data, so the view is tested from records).
#[derive(Clone, Debug)]
pub struct ViewWorkload {
    pub name: String,
    pub role: WorkloadRole,
    pub scale: String,
    pub first_scale: String,
    pub library: PathBuf,
    /// Its training facts at `scale` (`engine::facts::training_facts`).
    pub training: Value,
    /// The original data size at `scale` (its budget for a storage change), the plain storage's bytes and packages, and
    /// the record of the original data size.
    pub budget_bytes: u64,
    pub plain_storage_bytes: u64,
    pub plain_storages: BTreeSet<ContentId>,
    pub original_data_record: PathBuf,
}

impl ViewWorkload {
    /// The workload `name` from its prepared inputs (`inputs.general` set), its first scale and its library.
    pub fn of(name: &str, role: WorkloadRole, inputs: &EngineInputs, first_scale: Option<&FirstScale>, library: &Path) -> Self {
        let general = inputs.general.as_ref();
        let scale = general.map_or_else(String::new, |g| g.scale.name.clone());
        Self {
            name: name.to_string(),
            role,
            first_scale: first_scale.and_then(|f| f.inputs.general.as_ref().map(|g| g.scale.name.clone())).unwrap_or_else(|| scale.clone()),
            scale,
            library: library.to_path_buf(),
            training: inputs.training_facts.clone(),
            budget_bytes: general.map_or(0, |g| g.scale.original_data_bytes),
            plain_storage_bytes: general.map_or(0, |g| g.plain_storage_bytes),
            plain_storages: general.map(|g| g.plain_storages.clone()).unwrap_or_default(),
            original_data_record: general.map(|g| g.scale.original_data_record.clone()).unwrap_or_default(),
        }
    }
}

/// The stage view (module documentation) over the run's records under `engine_dir`.
pub fn stage_view(engine_dir: &Path, goal: &str, seed: &SeedVersion, workloads: &[ViewWorkload]) -> Value {
    let tree = VersionTree::read(engine_dir).unwrap_or_default();
    let head = tree.main_line_head().map(String::from);
    let out_of_the_box = OutOfTheBox::read(engine_dir).map_or_else(|| json!({"status":null,"step":null,"first_errors":[],"score":null,"record":null}), |o| o.view());
    let entries: Vec<Value> = workloads.iter().map(|w| workload_entry(engine_dir, head.as_deref(), w)).collect();
    json!({"goal":goal,"seed":{"run":seed.run,"version":seed.version,"out_of_the_box":out_of_the_box},"workloads":entries})
}

/// One workload's entry of the stage view.
fn workload_entry(engine_dir: &Path, head: Option<&str>, w: &ViewWorkload) -> Value {
    let record = head.and_then(|h| read_workload_record(engine_dir, h, &w.name));
    let kept = w.role == WorkloadRole::Kept;
    let reads_only_plain = record.as_ref().map(|r| !r.uses.is_empty() && r.uses.iter().all(|u| w.plain_storages.contains(&u.package)));
    let last_race = match (&record, head) {
        (Some(r), Some(head)) if kept && r.race.is_some() => json!({"version":head,"parent":r.parent,"record":r.race}),
        _ => Value::Null,
    };
    let reference = if kept {
        read_workload_record(engine_dir, ROOT_VERSION, &w.name).map_or(Value::Null, |r| json!({"version":ROOT_VERSION,"score":r.score,"cells":cells_of(&r)}))
    } else {
        Value::Null
    };
    json!({"name":w.name,"role":w.role.name(),"scale":w.scale,"first_scale":w.first_scale,"library":w.library,"training":w.training,
        "head":head,"cells":record.as_ref().map_or(Value::Null, cells_of),"score":record.as_ref().and_then(|r| r.score.as_ref()),
        "storage":{"budget_bytes":w.budget_bytes,"plain_storage_bytes":w.plain_storage_bytes,"serving_bytes":record.as_ref().and_then(|r| r.serving_bytes),
            "reads_only_plain":reads_only_plain,"original_data_record":w.original_data_record},
        "module_lines":record.as_ref().map_or(0, |r| r.module_lines),"last_race":last_race,"reference":reference})
}

/// A workload record's cells (`null` when it has none or its file cannot be read).
fn cells_of(record: &WorkloadRecord) -> Value {
    record.cells.as_ref().and_then(|file| read_json::<Vec<CellResult>>(file).ok()).map_or(Value::Null, |cells| json!(cells))
}

/// One workload as the workloads view shows it (a run of several workloads): its stage-view facts, its role, whether it
/// is the primary, and what its head's totals are scored with (its baselines, timing binding, worker counts and call
/// limit). Plain data, so the view is tested from records.
#[derive(Clone, Debug)]
pub struct ViewMember {
    pub base: ViewWorkload,
    pub role: MemberRole,
    pub primary: bool,
    pub baselines: Baselines,
    pub timing_binding: String,
    pub workers: Vec<usize>,
    pub call_limit_ns: u64,
}

impl ViewMember {
    /// The workload `name` from its prepared inputs (`inputs.general` set), its role, its first scale and its library.
    pub fn of(name: &str, role: MemberRole, primary: bool, inputs: &EngineInputs, first_scale: Option<&FirstScale>, library: &Path) -> Self {
        let side = if primary { WorkloadRole::Goal } else { WorkloadRole::Kept };
        Self {
            base: ViewWorkload::of(name, side, inputs, first_scale, library),
            role,
            primary,
            baselines: inputs.baselines.clone(),
            timing_binding: inputs.training.timing_binding.clone(),
            workers: inputs.workers.clone(),
            call_limit_ns: inputs.general.as_ref().map_or(0, |g| g.call_limits.call_limit_ns),
        }
    }
}

/// The workloads view and the combined score (module documentation) over the run's records under `engine_dir`.
pub fn workloads_view(engine_dir: &Path, members: &[ViewMember]) -> (Value, Value) {
    let tree = VersionTree::read(engine_dir).unwrap_or_default();
    let head = tree.main_line_head().map(String::from);
    let root: Value = read_json(&node_directory(engine_dir, ROOT_VERSION, true).join("version.json")).unwrap_or(Value::Null);
    let entries: Vec<Value> = members.iter().map(|m| member_entry(engine_dir, head.as_deref(), &root, m)).collect();
    let recorded: Option<Value> = head.as_deref().and_then(|h| read_json::<Value>(&node_directory(engine_dir, h, true).join("version.json")).ok()).map(|v| v["combined_score"].clone()).filter(Value::is_object);
    let combined = match recorded.or_else(|| head.as_deref().and_then(|h| tree.combined_score(h)).map(|c| json!(c))) {
        Some(mut combined) => {
            combined["head"] = json!(head);
            combined
        }
        None => Value::Null,
    };
    (json!(entries), combined)
}

/// One workload's entry of the workloads view.
fn member_entry(engine_dir: &Path, head: Option<&str>, root: &Value, m: &ViewMember) -> Value {
    let w = &m.base;
    let record = head.and_then(|h| read_workload_record(engine_dir, h, &w.name));
    let check = m.role == MemberRole::Check;
    let cells: Option<Vec<CellResult>> = record.as_ref().and_then(|r| r.cells.as_ref()).and_then(|f| read_json(f).ok()).filter(|_| !check);
    // The head's totals and the faster baseline's per worker count, as the score counts them.
    let scored = cells.as_ref().and_then(|c| score(&m.baselines, &m.timing_binding, &m.workers, m.call_limit_ns.max(1), c).ok());
    let per_workers = |value: &dyn Fn(&crate::engine::score::WorkerScore) -> u64| -> Value {
        scored.as_ref().map_or(Value::Null, |s| Value::Object(s.workers.iter().map(|ws| (ws.workers.to_string(), json!(value(ws) as f64 / 1e6))).collect()))
    };
    let reads_only_plain = record.as_ref().map(|r| !r.uses.is_empty() && r.uses.iter().all(|u| w.plain_storages.contains(&u.package)));
    let budget = if check {
        json!({"rule":"exempt","budget_bytes":null,"plain_storage_bytes":w.plain_storage_bytes,"reads_only_plain":reads_only_plain,"original_data_record":null})
    } else {
        json!({"rule":"original_data_size","budget_bytes":w.budget_bytes,"plain_storage_bytes":w.plain_storage_bytes,"reads_only_plain":reads_only_plain,"original_data_record":w.original_data_record})
    };
    let last_race = match (&record, head) {
        (Some(r), Some(head)) if !check && r.race.is_some() => json!({"version":head,"parent":r.parent,"record":r.race}),
        _ => Value::Null,
    };
    let last_check = match (&record, head) {
        (Some(r), Some(head)) if check => r.check.as_ref().map_or(Value::Null, |c| json!({"version":head,"calls":c["calls"],"agreed":c["agreed"],"record":c["record"]})),
        _ => Value::Null,
    };
    let general = record.as_ref().and_then(|r| r.general.clone()).unwrap_or_else(|| json!({"own_module_lines":0,"inherited_storages":[],"family_storages":[],"plan_lines":0}));
    json!({"name":w.name,"role":m.role.name(),"primary":m.primary,"scale":w.scale,"first_scale":w.first_scale,"library":w.library,"training":w.training,
        "head":head,"side_origin":root["workloads"][w.name.as_str()]["origin"].clone(),
        "cells":cells.map_or(Value::Null, |c| json!(c)),"score":if check { Value::Null } else { record.as_ref().and_then(|r| r.score.clone()).map_or(Value::Null, |s| json!(s)) },
        "totals_ms":per_workers(&|ws| ws.total_ns),"targets_ms":per_workers(&|ws| ws.target_ns),
        "budget":budget,"serving_bytes":record.as_ref().and_then(|r| r.serving_bytes),"general":general,"last_race":last_race,"last_check":last_check})
}

impl EngineBench<'_> {
    /// The stage view of a session's role (its goal and kept workloads; module documentation), `None` outside a stage
    /// run (a run of several workloads has the workloads view).
    pub(crate) fn stage_view(&self) -> Option<Value> {
        let stage = self.stage.filter(|s| !s.is_members())?;
        let seed = match &stage.seed {
            Some(Seed::Run { version, .. }) => version.clone(),
            _ => return None,
        };
        let mut workloads = vec![ViewWorkload::of(&stage.primary, WorkloadRole::Goal, self.inputs(), stage.first_scale.as_ref(), &self.bench.config.library)];
        for side in &stage.sides {
            workloads.push(ViewWorkload::of(&side.name, WorkloadRole::Kept, &side.config.inputs, side.stage.first_scale.as_ref(), &side.view.library));
        }
        Some(stage_view(&self.config.engine_dir, &stage.primary, &seed, &workloads))
    }

    /// The workloads view and the combined score of a session's role in a run of several workloads (module
    /// documentation), `None` in every other run.
    pub(crate) fn workloads_view(&self) -> Option<(Value, Value)> {
        let stage = self.stage.filter(|s| s.is_members())?;
        let mut members = vec![ViewMember::of(&stage.workload, stage.role, true, self.inputs(), stage.first_scale.as_ref(), &self.bench.config.library)];
        for side in &stage.sides {
            members.push(ViewMember::of(&side.name, side.role, false, &side.config.inputs, side.stage.first_scale.as_ref(), &side.view.library));
        }
        Some(workloads_view(&self.config.engine_dir, &members))
    }
}
