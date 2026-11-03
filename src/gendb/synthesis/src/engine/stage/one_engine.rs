//! The one-engine rule of a run of several workloads (request `engine.workloads.require_one_engine`; the user's
//! requirement: the first version may be slower, "but it must be a general one-engine"). A version is **one engine** when
//! every workload is served by the default module over storage families or plain flat storages: no workload has a module
//! of its own and none reads an inherited workload-specific storage (`version.json` `general.one_engine`,
//! [`super::records::general_record`]). With the rule set, a submission's evaluation (`super::members::evaluate_members`):
//! - refuses a submission that is not one engine right after its freeze, before any build or timing
//!   ([`OneEngineRule::refusal`]: reason [`NOT_ONE_ENGINE`], naming its own modules and inherited storages);
//! - while the parent (the head) is not one engine, accepts the first one-engine submission whose combined score is not
//!   better when it is correct ([`OneEngineRule::transition`], [`ONE_ENGINE_TRANSITION`]): every crate verified whole,
//!   its storages built and checked, every check workload's answers agreed (each step gating before the decision), and
//!   every counted workload's race finished every cell with agreeing answers. The combined decision, the version and the
//!   main line record it with the races, for reporting; the kept workloads' races and every workload's variants still
//!   run after it, as after any accepting decision ([`CombinedVerdict`]);
//! - from then on the parent is one engine, so the combined score decides as before.
//!
//! Unset, nothing here runs and every evaluation is as before.
//!
//! Trust: none in proofs. The rule reads the freeze's records of each crate (`submission::members::MemberRecord`), the
//! parent's version record and the races' scores; it is host code used for decisions and records.

use super::members::RaceScores;
use super::records::general_record;
use crate::controller::records::read_json;
use crate::engine::submission::members::MemberRecord;
use crate::engine::tree::node_directory;
use gendb_verification::admission::AdmissionError;
use serde_json::{Value, json};
use std::path::Path;

/// The refusal of a submission that is not one engine (the reason's id).
pub const NOT_ONE_ENGINE: &str = "not_one_engine";
/// The acceptance of the first one-engine version of a line whose head is not one engine (the combined decision's key,
/// the version record's key and the main line's reason).
pub const ONE_ENGINE_TRANSITION: &str = "one_engine_transition";
/// The step of an evaluation's `members.json` at which a submission that is not one engine is refused.
pub const ONE_ENGINE_STEP: &str = "one_engine";
/// The request field that sets the rule.
pub const ONE_ENGINE_FIELD: &str = crate::controller::workload_run::lifecycle::ONE_ENGINE_FIELD;

/// The one-engine rule as one evaluation applies it: whether the submission is one engine, and whether its parent is.
#[derive(Clone, Debug, PartialEq)]
pub struct OneEngineRule {
    /// The submission's `general` record over its frozen crates ([`general_record`]: `one_engine`, `own_modules`,
    /// `inherited_storages`).
    pub candidate: Value,
    /// Whether the parent version is one engine (its `version.json` `general.one_engine`).
    pub parent_one_engine: bool,
}

/// What the rule makes of a combined score that is not better ([`OneEngineRule::transition`]).
#[derive(Clone, Debug, PartialEq)]
pub enum Transition {
    /// The parent is one engine: the combined score decides (the submission is an attempt).
    NotApplicable,
    /// Accepted as the first one-engine version: the record joins the combined decision under
    /// [`ONE_ENGINE_TRANSITION`].
    Accepted(Value),
    /// Not accepted: a counted workload's race left cells unfinished (named here), so not every counted answer was
    /// checked.
    Unfinished(String),
}

impl OneEngineRule {
    /// The rule for the submission whose frozen crates recorded `members` (`(workload, record)`, the primary first),
    /// against `parent`, whose `general.one_engine` is read from its version folder under `engine_dir`. A crate without
    /// its record, or a parent version without `general.one_engine`, is a framework error.
    pub fn of(members: &[(String, Option<MemberRecord>)], engine_dir: &Path, parent: &str) -> Result<Self, AdmissionError> {
        if let Some((name, _)) = members.iter().find(|(_, record)| record.is_none()) {
            return Err(AdmissionError::tool(format!("the one-engine rule: workload {name}'s frozen crate has no member record")));
        }
        let candidate = general_record(&members.iter().map(|(n, m)| (n.as_str(), m.as_ref())).collect::<Vec<_>>(), true);
        let file = node_directory(engine_dir, parent, true).join("version.json");
        let version: Value = read_json(&file).map_err(|e| AdmissionError::tool(format!("the one-engine rule: the parent's record: {e}")))?;
        let parent_one_engine = version["general"]["one_engine"]
            .as_bool()
            .ok_or_else(|| AdmissionError::tool(format!("the one-engine rule: {} has no general.one_engine", file.display())))?;
        Ok(Self { candidate, parent_one_engine })
    }

    /// Whether the submission is one engine.
    pub fn candidate_is_one_engine(&self) -> bool {
        self.candidate["one_engine"] == true
    }

    /// The workloads that keep the submission from being one engine (an own module or an inherited storage), each once,
    /// in record order.
    pub fn breaking_workloads(&self) -> Vec<String> {
        let mut names: Vec<String> = vec![];
        let own = self.candidate["own_modules"].as_array().into_iter().flatten().filter_map(Value::as_str);
        let inherited = self.candidate["inherited_storages"].as_array().into_iter().flatten().filter_map(|i| i["workload"].as_str());
        for name in own.chain(inherited) {
            if !names.iter().any(|n| n == name) {
                names.push(name.to_string());
            }
        }
        names
    }

    /// The refusal of a submission that is not one engine (the first line names the rule, then what breaks it); `None`
    /// when it is one engine.
    pub fn refusal(&self) -> Option<String> {
        if self.candidate_is_one_engine() {
            return None;
        }
        let list = |items: Vec<String>| if items.is_empty() { "none".to_string() } else { items.join(", ") };
        let own = list(self.candidate["own_modules"].as_array().into_iter().flatten().filter_map(Value::as_str).map(|n| format!("workloads/{n}/")).collect());
        let inherited = list(
            self.candidate["inherited_storages"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|i| format!("{} ({})", i["workload"].as_str().unwrap_or("-"), i["storages"].as_array().into_iter().flatten().filter_map(Value::as_str).collect::<Vec<_>>().join(", ")))
                .collect(),
        );
        Some(format!(
            "refusal: {NOT_ONE_ENGINE}: this run accepts only a version that is one engine ({ONE_ENGINE_FIELD}): every workload served by the default module workloads/default/ over storage families or plain flat storages, with no workload module of its own and no inherited workload-specific storage. This submission has own modules: {own}; inherited storages: {inherited}. Nothing was built or timed"
        ))
    }

    /// The transition for a combined score that is not better, over the counted workloads' `races` (the primary
    /// first): while the parent is not one engine, the (one-engine) submission is accepted when every counted race
    /// finished every cell (each answer then agreed, or the race would have refused it). `parent` names the parent in
    /// the record.
    pub fn transition(&self, parent: &str, races: &[(&str, &RaceScores)]) -> Transition {
        if self.parent_one_engine || !self.candidate_is_one_engine() {
            return Transition::NotApplicable;
        }
        let unfinished: Vec<String> = races
            .iter()
            .filter(|(_, race)| race.candidate.finished < race.cells)
            .map(|(name, race)| format!("{name} finished {} of {} cells", race.candidate.finished, race.cells))
            .collect();
        if !unfinished.is_empty() {
            return Transition::Unfinished(format!(
                "{ONE_ENGINE_TRANSITION} not applied: the first one-engine version is accepted with a worse combined score only when every counted cell finished with agreeing answers ({})",
                unfinished.join("; ")
            ));
        }
        Transition::Accepted(json!({"rule":ONE_ENGINE_FIELD,"parent":parent,"parent_one_engine":false,"candidate_one_engine":true,
            "counted_cells":races.iter().map(|(name, race)| json!({"workload":name,"finished":race.candidate.finished,"cells":race.cells,"race":race.file})).collect::<Vec<_>>(),
            "meaning":"the first one-engine version of a line whose head is not one engine: accepted although its combined score is not better than its parent's, because it is correct (every crate verified whole, its storages built and checked, every check workload's answers and every counted cell finished with agreeing answers); the races are recorded for reporting, and from this version on the combined score decides"}))
    }
}

/// What the combined decision recorded for an accepted submission (`combined.json`, the record's `combined`): better,
/// not better, or the first one-engine version accepted by [`OneEngineRule::transition`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CombinedVerdict {
    Better,
    NotBetter,
    OneEngineTransition,
}

impl CombinedVerdict {
    /// The verdict of the combined decision `combined`; `None` when there is none (a run of one workload, a stage run).
    pub fn of_record(combined: &Value) -> Option<Self> {
        let better = combined["better"].as_bool()?;
        Some(if better {
            CombinedVerdict::Better
        } else if combined[ONE_ENGINE_TRANSITION].is_object() {
            CombinedVerdict::OneEngineTransition
        } else {
            CombinedVerdict::NotBetter
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::score::{NormalizedTime, Score};
    use std::path::PathBuf;

    fn rule(one_engine: bool, parent_one_engine: bool) -> OneEngineRule {
        let candidate = if one_engine {
            json!({"one_engine":true,"own_modules":[],"inherited_storages":[]})
        } else {
            json!({"one_engine":false,"own_modules":["sec","tpch"],"inherited_storages":[{"workload":"tpch","storages":["narrowpack","narrowpack2"]},{"workload":"sec","storages":["dictpack"]}]})
        };
        OneEngineRule { candidate, parent_one_engine }
    }

    fn race(finished: usize, cells: usize) -> RaceScores {
        let score = |finished: usize| Score { finished, normalized_time: NormalizedTime::from_billionths(1_000_000_000) };
        RaceScores { file: PathBuf::from("race.json"), parent: score(cells), candidate: score(finished), cells }
    }

    /// The refusal names the rule, the field, every own module and every inherited storage by workload; a one-engine
    /// submission has none.
    #[test]
    fn the_refusal_names_what_keeps_a_submission_from_being_one_engine() {
        let refusal = rule(false, false).refusal().unwrap();
        assert!(refusal.starts_with("refusal: not_one_engine: ") && refusal.contains(ONE_ENGINE_FIELD), "{refusal}");
        assert!(refusal.contains("own modules: workloads/sec/, workloads/tpch/") && refusal.contains("tpch (narrowpack, narrowpack2), sec (dictpack)"), "{refusal}");
        assert_eq!(rule(false, false).breaking_workloads(), ["sec", "tpch"]);
        assert_eq!(rule(true, false).refusal(), None);
    }

    /// The transition applies only while the parent is not one engine, and only when every counted cell finished.
    #[test]
    fn the_transition_needs_a_parent_that_is_not_one_engine_and_every_counted_cell_finished() {
        let (tpch, sec) = (race(111, 111), race(18, 18));
        match rule(true, false).transition("v003", &[("tpch", &tpch), ("sec", &sec)]) {
            Transition::Accepted(record) => {
                assert_eq!((record["parent"].as_str(), record["counted_cells"][1]["finished"].as_u64()), (Some("v003"), Some(18)));
            }
            other => panic!("{other:?}"),
        }
        assert_eq!(rule(true, true).transition("v009", &[("tpch", &tpch)]), Transition::NotApplicable, "after the transition the combined score decides");
        match rule(true, false).transition("v003", &[("tpch", &race(110, 111)), ("sec", &sec)]) {
            Transition::Unfinished(why) => assert!(why.contains("tpch finished 110 of 111 cells"), "{why}"),
            other => panic!("{other:?}"),
        }
        let accepted = json!({"better":false,"one_engine_transition":{}});
        assert_eq!(
            [CombinedVerdict::of_record(&json!({"better":true})), CombinedVerdict::of_record(&json!({"better":false})), CombinedVerdict::of_record(&accepted), CombinedVerdict::of_record(&Value::Null)],
            [Some(CombinedVerdict::Better), Some(CombinedVerdict::NotBetter), Some(CombinedVerdict::OneEngineTransition), None]
        );
    }
}
