//! Files of one author session's run directory. Names are part of the saved-evidence format; they did not change
//! in the refactor.
//!
//! ```text
//! <root>/ledger.json            LedgerState (replaced atomically)       controller.lock   run ownership
//! <root>/summary.json           latest run summary                      resolution.json   role closure
//! <root>/context.json           prepared role context (first preparation; later ones: context-preparation-<ms>.json)
//! <root>/preparation-<ms>.json  preparation wall time of one controller process
//! <root>/author/                the author workspace (with the author's NOTES.md for the next attempt)
//! <root>/calls/NNNN/            one author call: receipt.json (controller) plus the transport's own records
//!                               (for Claude Code: prompt.txt, invocation.json, stdout.jsonl, process-exit.json,
//!                               tool-capabilities.json, model-usage.json, superseded-results.json) and local-jobs/
//!                               (author tool evidence)
//! <root>/iterations/NNNN/       one submission: frozen/, frozen-candidate.json, NOTES.md (the author's notes as
//!                               they were at the submission), evaluation.json,
//!                               qualification.json, reevaluation-<revision>.json; in a reselection session
//!                               (controller::reselect) the imported candidate, with source.json (provenance)
//! <root>/iterations/0000/       a continuing session's incumbent (RunRequest::continue_from): frozen/,
//!                               frozen-candidate.json, incumbent.json (provenance, written last), NOTES.md (the
//!                               source author's notes), evaluation.json, qualification.json
//! <root>/reselection.json       a reselection session's selection over its closed source session
//! <root>/operator-stop.json     the operator's stop of this session at its next call boundary (`gendb operator-stop`)
//! <root>/local-session/         retained role service records (service.json, service-finished.json, …)
//! ```

use std::path::{Path, PathBuf};

/// The author's own handoff notes in its workspace (`<root>/author/NOTES.md`): written by the author for the next
/// attempt's fresh session (design and why, what was tried and what helped, untried ideas, proof difficulties). Hints
/// only; GenDB's recorded facts are authoritative.
pub const NOTES_FILE: &str = "NOTES.md";

/// The iteration number of a continuing session's incumbent (`RunRequest::continue_from`); submissions count from 1.
pub const INCUMBENT_ITERATION: u32 = 0;

/// The incumbent's provenance record in its iteration directory, written last when its freeze is complete.
pub const INCUMBENT_FILE: &str = "incumbent.json";

/// The operator's stop record of one session (`controller::run::record_operator_stop`, `gendb operator-stop`).
pub const OPERATOR_STOP_FILE: &str = "operator-stop.json";

/// The file of a call directory that holds the call's complete prompt, written by the transport before the call
/// starts. The prompt names it, so the author can reread its own prompt and feedback.
pub const PROMPT_FILE: &str = "prompt.txt";

#[derive(Clone, Debug)]
pub struct RunLayout {
    root: PathBuf,
}

impl RunLayout {
    pub fn new(root: &Path) -> Self {
        Self { root: root.to_path_buf() }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn ledger(&self) -> PathBuf {
        self.root.join("ledger.json")
    }

    pub fn summary(&self) -> PathBuf {
        self.root.join("summary.json")
    }

    pub fn resolution(&self) -> PathBuf {
        self.root.join("resolution.json")
    }

    pub fn context(&self) -> PathBuf {
        self.root.join("context.json")
    }

    /// The author's workspace (the provider process's working directory).
    pub fn workspace(&self) -> PathBuf {
        self.root.join("author")
    }

    pub fn calls(&self) -> PathBuf {
        self.root.join("calls")
    }

    pub fn call(&self, call_id: u64) -> PathBuf {
        self.calls().join(format!("{call_id:04}"))
    }

    /// Where the transport saves a call's complete prompt ([`PROMPT_FILE`]).
    pub fn prompt(&self, call_id: u64) -> PathBuf {
        self.call(call_id).join(PROMPT_FILE)
    }

    /// The controller's copy of a call's settled receipt.
    pub fn receipt(&self, call_id: u64) -> PathBuf {
        self.call(call_id).join("receipt.json")
    }

    pub fn iterations(&self) -> PathBuf {
        self.root.join("iterations")
    }

    pub fn iteration(&self, iteration: u32) -> PathBuf {
        self.iterations().join(format!("{iteration:04}"))
    }

    /// The role's frozen copy of a submission.
    pub fn frozen(&self, iteration: u32) -> PathBuf {
        self.iteration(iteration).join("frozen")
    }

    /// The author's notes as they were when this submission was frozen (a copy of the workspace's [`NOTES_FILE`]).
    pub fn iteration_notes(&self, iteration: u32) -> PathBuf {
        self.iteration(iteration).join(NOTES_FILE)
    }

    /// The frozen candidate value returned by `SynthesisRole::freeze`.
    pub fn frozen_candidate(&self, iteration: u32) -> PathBuf {
        self.iteration(iteration).join("frozen-candidate.json")
    }

    /// The original evaluation of a submission (never replaced; repairs write `reevaluation`).
    pub fn evaluation(&self, iteration: u32) -> PathBuf {
        self.iteration(iteration).join("evaluation.json")
    }

    /// The incumbent's provenance record ([`INCUMBENT_FILE`] in iteration [`INCUMBENT_ITERATION`]).
    pub fn incumbent(&self) -> PathBuf {
        self.iteration(INCUMBENT_ITERATION).join(INCUMBENT_FILE)
    }

    pub fn qualification(&self, iteration: u32) -> PathBuf {
        self.iteration(iteration).join("qualification.json")
    }

    pub fn reevaluation(&self, iteration: u32, revision: &str) -> PathBuf {
        self.iteration(iteration).join(format!("reevaluation-{revision}.json"))
    }

    /// The operator's stop record ([`OPERATOR_STOP_FILE`]).
    pub fn operator_stop(&self) -> PathBuf {
        self.root.join(OPERATOR_STOP_FILE)
    }

    /// Retained role service records of this session.
    pub fn local_session(&self) -> PathBuf {
        self.root.join("local-session")
    }
}
