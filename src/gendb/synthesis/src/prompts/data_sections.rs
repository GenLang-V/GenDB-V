//! The call's data sections at the end of every author prompt, as Markdown text and tables: CURRENT FACTS AND PATHS
//! (`facts`), HANDOFF FROM EARLIER ATTEMPTS and LEDGER (`history`), LATEST FEEDBACK (`feedback`).
//!
//! Every line is a deterministic function of the views `policy` prepares from GenDB's records (the prepared context,
//! the ledger, the trials, the local-job records and the author's NOTES.md). No raw JSON is shown: the only verbatim
//! texts are the SQL, the author's NOTES.md and evaluation errors. A value left out of a section is either a pure
//! repeat of a line that stays (or of the fixed sections), or is in a file the section names (`performance.json`,
//! `ledger.json`, the iteration and local-job records). Durations are in ms with 3 decimals, sizes in GB/MB.
//!
//! A query author sees only its own statement; the workload storage author sees every statement of the workload; the
//! engine author's own CURRENT FACTS head and round handoff are rendered by `prompts::engine_facts` and placed here by
//! [`render_engine`], with the shared Storage, Integrity constraints and Host sections, the ledger and the feedback. The
//! general engine line ([`render_general`]) places its own facts and handoff (`prompts::engine_facts::general`) with
//! compact Integrity constraints and Host sections of its own; the other authors' sections are unchanged by it.

mod facts;
mod feedback;
pub(super) mod format;
mod history;

use serde_json::Value;

/// Which author the sections are for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AuthorKind {
    /// One query (both storage policies).
    Query,
    /// The workload storage author (every statement).
    WorkloadStorage,
    /// The schema-engine author (`prompts::engine_policy`).
    Engine,
    /// The general engine line's author (`prompts::engine_policy::general_author_prompt`).
    GeneralEngine,
}

/// The views one prompt's data sections are rendered from (prepared by `policy`).
pub struct DataViews<'a> {
    pub author: AuthorKind,
    /// The prepared context with the facts refreshed before this call (for example `storage_budget`).
    pub context: &'a Value,
    /// `policy::target_cells`: per benchmark cell the target, the early-stop bar and the engine that set the target.
    pub targets: &'a Value,
    /// `policy::submission_results`: every submission's official result (per cell for a query).
    pub submissions: &'a Value,
    /// The objective status over the trials (`objective_status` / `storage_objective_status`).
    pub objective: &'a Value,
    /// The handoff of a fresh session (`trajectory::attempt_handoff`), or null.
    pub handoff: &'a Value,
    /// `LedgerState::author_view` of this call.
    pub ledger: &'a Value,
    /// `policy::latest_delta`: the latest call, its local jobs and (once evaluated) its submission.
    pub latest: &'a Value,
}

/// The four data sections of one prompt.
pub fn render(views: &DataViews) -> String {
    let mut lines = facts::current_facts(views);
    if !views.handoff.is_null() {
        lines.push(String::new());
        lines.extend(history::handoff(views));
    }
    lines.push(String::new());
    lines.extend(history::ledger(views.ledger));
    lines.push(String::new());
    lines.extend(feedback::latest_feedback(views));
    lines.join("\n") + "\n"
}

/// The data sections of one engine author call: CURRENT FACTS AND PATHS (`engine_facts`, the engine's own head, then
/// the shared Storage, Integrity constraints and Host sections), `rounds_handoff` (the handoff of earlier rounds, when
/// any), the handoff of an earlier session of this round (when the call starts a fresh one), the ledger and the latest
/// feedback.
pub fn render_engine(views: &DataViews, engine_facts: &[String], rounds_handoff: &[String]) -> String {
    let mut lines = facts::engine_current_facts(views, engine_facts);
    if !rounds_handoff.is_empty() {
        lines.push(String::new());
        lines.extend(rounds_handoff.iter().cloned());
    }
    if !views.handoff.is_null() {
        lines.push(String::new());
        lines.extend(history::handoff(views));
    }
    lines.push(String::new());
    lines.extend(history::ledger(views.ledger));
    lines.push(String::new());
    lines.extend(feedback::latest_feedback(views));
    lines.join("\n") + "\n"
}

/// The data sections of one general-line call: CURRENT FACTS AND PATHS (`general_facts`, rendered by
/// `prompts::engine_facts::general`, then the line's compact Integrity constraints and Host sections, shown when the
/// context carries them), `handoff` (the session's handoff, when any), the handoff of a fresh provider session (when
/// the call starts one), the ledger and the latest feedback.
pub fn render_general(views: &DataViews, general_facts: &[String], handoff: &[String]) -> String {
    let mut lines = facts::general_current_facts(views, general_facts);
    for block in [handoff.to_vec(), if views.handoff.is_null() { vec![] } else { history::handoff(views) }, history::ledger(views.ledger), feedback::latest_feedback(views)] {
        if !block.is_empty() {
            lines.push(String::new());
            lines.extend(block);
        }
    }
    lines.join("\n") + "\n"
}
