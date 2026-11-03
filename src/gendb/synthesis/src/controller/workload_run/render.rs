//! Prompts rendered for review without any provider; nothing is admitted.
//!
//! `gendb render-saved-prompt SESSION_DIR CALL OUT.md` ([`render_saved_prompt`]): the prompt of a saved call of a
//! closed or open author session, rendered again from the session's records by the current prompt code.
//!
//! `gendb render-query-inputs REQUEST.json QUERY OUT_DIR`: the inputs of one query author's first call, rendered for
//! review without any provider. The named query of the request runs alone through the public controller (statements,
//! data preparation, its preflight, its role and author workspace) with a render-only author ([`RenderAuthor`]) that
//! saves the call's prompt, prepared context, tool context and author contract under `OUT_DIR/rendered` and submits no
//! manifest, so the session closes with that refusal and nothing is admitted. The run directory is `OUT_DIR/run`; the
//! request's library is read as by any run (no output home is written). It shows exactly what an author would receive,
//! for any storage policy, with one exception: a query that continues from an earlier session's admitted candidate
//! (`continue_from`) has its incumbent written into the workspace and frozen as in a real run, but the render times
//! nothing, so the incumbent's column shows the source session's recorded evaluation, marked `render_only` in its
//! evaluation record and never qualified (`AuthorTransport::render_only`).

use super::authors::WorkloadAuthors;
use super::{WorkloadError, run_workload};
use crate::controller::author::{AuthorCall, AuthorTransport, CandidateSubmission, Capability};
use crate::controller::crash_dumps;
use crate::controller::layout::RunLayout;
use crate::controller::ledger::{LedgerState, Receipt, Tokens};
use crate::controller::limits::Money;
use crate::controller::records;
use crate::controller::request::{QueryRequest, WorkloadRequest};
use crate::controller::role::{PromptInput, RolePolicy, call_event, local_jobs_event};
use crate::controller::trajectory::attempt_handoff;
use crate::prompts::{StoragePolicy, VerifiedQueryPolicy};
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};

/// The manifest name a render-only submission names (it does not exist, so the submission is refused).
const NO_MANIFEST: &str = "render-only-no-manifest.json";

/// An author that renders its call's inputs under `out` instead of calling a provider.
pub struct RenderAuthor {
    pub out: PathBuf,
}

impl RenderAuthor {
    fn render(&self, request: &AuthorCall) -> std::io::Result<()> {
        fs::create_dir_all(&self.out)?;
        fs::write(self.out.join("prompt.md"), request.prompt)?;
        copy_tree(&request.workspace.join("contract"), &self.out.join("contract"))?;
        for file in [crate::tools::CONTEXT_FILE, "verus-query-example.json", "verus-library.json", "search-index.txt", "ENGINE_MAP.md", "verus-engine.json", "verus-engine-example.json", "NOTES.md"] {
            if request.workspace.join(file).is_file() {
                fs::copy(request.workspace.join(file), self.out.join(file))?;
            }
        }
        if let Some(session) = request.workspace.parent()
            && session.join("context.json").is_file()
        {
            fs::copy(session.join("context.json"), self.out.join("context.json"))?;
        }
        Ok(())
    }
}

impl AuthorTransport for RenderAuthor {
    fn render_only(&self) -> bool {
        true
    }

    fn capability(&self) -> Capability {
        Capability {
            transport: "render-only".into(),
            executable: "none".into(),
            version: "1".into(),
            model: "none (renders the call's inputs; no provider)".into(),
            effort: "none".into(),
            persistent_sessions: true,
            hard_usd_cap: false,
            cost_semantics: "no provider: zero cost".into(),
        }
    }

    fn invoke(&mut self, request: &AuthorCall) -> Receipt {
        let rendered = self.render(request);
        Receipt {
            call_id: request.call.id,
            session_id: request.session_id.into(),
            ended_unix_ms: records::now_unix_ms(),
            elapsed_ms: 1,
            reported_cost_usd: Some(Money::default()),
            billed_cost_usd: None,
            tokens: Some(Tokens::default()),
            outcome: match &rendered {
                Ok(()) => "success".into(),
                Err(error) => format!("render_failed: {error}"),
            },
            output: rendered.is_ok().then(|| {
                json!(CandidateSubmission {
                    candidate_manifest: NO_MANIFEST.into(),
                    rationale: "render only: no candidate".into(),
                    data_access_analysis: "render only".into(),
                })
            }),
            raw_result: Some(json!({"session_id":request.session_id,"render_only":true})),
            usage_scope: None,
        }
    }
}

fn copy_tree(from: &Path, to: &Path) -> std::io::Result<()> {
    for entry in fs::read_dir(from)? {
        let path = entry?.path();
        let target = to.join(path.file_name().expect("a directory entry"));
        if path.is_dir() {
            copy_tree(&path, &target)?;
        } else {
            fs::create_dir_all(to)?;
            fs::copy(&path, &target)?;
        }
    }
    Ok(())
}

/// Render the inputs of query `name`'s first author call (module documentation) into the new directory `out`.
pub fn render_query_inputs(request_path: &Path, name: &str, out: &Path, framework_executable: &Path) -> Result<Value, WorkloadError> {
    let _ = crash_dumps::contain();
    if out.exists() {
        return Err(WorkloadError::invalid(format!("{} exists; render-query-inputs writes a new directory", out.display())));
    }
    let mut request = WorkloadRequest::read(request_path)?;
    request.validate()?;
    let query = request.queries.iter().find(|q| q.name.as_deref() == Some(name)).cloned().ok_or_else(|| WorkloadError::invalid(format!("the request has no query named {name}")))?;
    request.queries = vec![QueryRequest { limits: crate::controller::Limits { max_iterations: 1, ..query.limits.clone() }, ..query }];
    request.max_concurrent_queries = 1;
    request.output_home = None;
    request.workload_storage = None;
    if let gendb_verification::admission::ValidationPolicy::FormalProofs { saved_answers, .. } = &mut request.validation {
        saved_answers.retain(|answer| answer.query == name);
    }
    records::create_dir(out)?;
    let rendered = out.join("rendered");
    let authors = WorkloadAuthors { storage: None, queries: vec![RenderAuthor { out: rendered.clone() }] };
    let runtime = tokio::runtime::Runtime::new().map_err(|e| WorkloadError::invalid(format!("async runtime: {e}")))?;
    let summary = runtime.block_on(run_workload(&request, &out.join("run"), authors, framework_executable))?;
    let record = json!({"format_version":1,"query":name,"rendered":rendered,"prompt":rendered.join("prompt.md"),"rendered_call":rendered.join("prompt.md").is_file(),
        "run":out.join("run"),"summary":summary,"scope":"the inputs of one query author's first call through the public controller with a render-only author: no provider, no admission"});
    records::write_new_json(&out.join("render.json"), &record)?;
    Ok(record)
}

/// The `scope` of a workload storage author's prepared context (`prompts::brief::storage`).
const WORKLOAD_STORAGE_SCOPE: &str = "verus_workload_storage";

/// Render the prompt of call `call_id` of the author session in `session` again with the current prompt code, into
/// the new file `out`, from the session's records as they were before that call: the ledger up to that call (its
/// calls, receipts and trials), the prepared context the call used, the local-job records of the earlier calls and
/// the frozen submissions. Two facts are taken from the call's saved prompt because the records keep only their
/// latest value: the storage budget read before the call and the NOTES.md text of the handoff. Whether the workspace
/// held a submission's code then is not known afterwards, so it is not compared. Reads only; no provider, no
/// evaluation, nothing admitted.
pub fn render_saved_prompt(session: &Path, call_id: u64, out: &Path) -> Result<Value, WorkloadError> {
    if out.exists() {
        return Err(WorkloadError::invalid(format!("{} exists; render-saved-prompt writes a new file", out.display())));
    }
    let layout = RunLayout::new(session);
    let state: LedgerState = records::read_json(&layout.ledger())?;
    let call = state.call(call_id).cloned().ok_or_else(|| WorkloadError::invalid(format!("{} has no call {call_id}", layout.ledger().display())))?;
    let before = state_before_call(&state, call_id);
    let saved_prompt = fs::read_to_string(layout.prompt(call_id)).map_err(|e| records::RecordError::new(&layout.prompt(call_id), e))?;
    let saved = SavedFacts::of(&saved_prompt);
    let mut context: Value = records::read_json(&context_of_call(&layout, call.started_unix_ms)?)?;
    if !saved.storage_budget.is_null() {
        context["storage_budget"] = saved.storage_budget.clone();
    }
    let storage_role = context["scope"] == WORKLOAD_STORAGE_SCOPE;
    let mut feedback: Vec<Value> = before.incumbent.iter().map(|incumbent| json!(incumbent)).collect();
    for earlier in before.calls.iter().filter(|c| c.id < call_id) {
        if let Some(receipt) = &earlier.receipt {
            feedback.push(call_event(earlier, receipt));
        }
        feedback.extend(local_jobs_event(&layout, earlier)?);
        feedback.extend(before.trials.iter().filter(|trial| trial.call_id == earlier.id).map(|trial| json!(trial)));
    }
    let ledger = before.author_view(call_id, &layout.ledger()).map_err(|e| WorkloadError::invalid(format!("ledger view: {e}")))?;
    let handoff = match &saved.notes {
        None => Value::Null,
        Some(notes) => {
            let code_of = |trial: &crate::controller::Trial| {
                let frozen = layout.frozen(trial.iteration);
                if storage_role { StoragePolicy.submission_code(&frozen, &trial.candidate, None) } else { VerifiedQueryPolicy.submission_code(&frozen, &trial.candidate, None) }
            };
            let mut handoff = attempt_handoff(&layout, &before, call_id, code_of)?;
            if handoff.is_object() {
                handoff["notes"]["text"] = notes.clone();
            }
            handoff
        }
    };
    let input = PromptInput {
        context: &context,
        feedback: &feedback,
        iteration: call.iteration,
        submission: before.counted_submissions() + 1,
        limits: &state.limits,
        ledger: &ledger,
        prompt_file: &layout.prompt(call_id),
        handoff: &handoff,
    };
    let prompt = if storage_role { StoragePolicy.author_prompt(&input) } else { VerifiedQueryPolicy.author_prompt(&input) };
    if let Some(parent) = out.parent() {
        records::create_dir(parent)?;
    }
    fs::OpenOptions::new().write(true).create_new(true).open(out).and_then(|mut file| std::io::Write::write_all(&mut file, prompt.as_bytes()))
        .map_err(|e| records::RecordError::new(out, e))?;
    Ok(json!({"format_version":1,"session":session,"call":call_id,"out":out,"saved_prompt":layout.prompt(call_id),
        "saved_prompt_bytes":saved_prompt.len(),"rendered_bytes":prompt.len(),
        "scope":"the saved call's state re-rendered by the current prompt code from the session's records: not what the author received; no provider, nothing admitted"}))
}

/// The ledger as it stood when call `call_id` was dispatched: the earlier calls with their receipts, that call
/// without its receipt, and the submissions of earlier calls.
fn state_before_call(state: &LedgerState, call_id: u64) -> LedgerState {
    let mut before = state.clone();
    before.calls.retain(|call| call.id <= call_id);
    if let Some(call) = before.calls.iter_mut().find(|call| call.id == call_id) {
        call.receipt = None;
    }
    before.trials.retain(|trial| trial.call_id < call_id);
    before.iterations = before.trials.len() as u32;
    before.closed = None;
    before
}

/// The prepared context a call started with: the latest preparation (`context.json`, then
/// `context-preparation-<ms>.json`) written at or before `started_unix_ms`.
fn context_of_call(layout: &RunLayout, started_unix_ms: u64) -> Result<PathBuf, WorkloadError> {
    let mut chosen = layout.context();
    let mut chosen_ms = 0;
    for entry in fs::read_dir(layout.root()).map_err(|e| records::RecordError::new(layout.root(), e))?.flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        let Some(ms) = name.strip_prefix("context-preparation-").and_then(|rest| rest.strip_suffix(".json")).and_then(|ms| ms.parse::<u64>().ok()) else { continue };
        if ms <= started_unix_ms && ms > chosen_ms {
            (chosen, chosen_ms) = (entry.path(), ms);
        }
    }
    Ok(chosen)
}

/// The facts of a saved prompt that the records keep only in their latest version: the storage budget read before
/// the call (CURRENT FACTS) and the handoff's NOTES.md text (`Some` exactly when the call had a handoff). Read from the
/// one-line JSON blocks of the prompt format before the data sections were rendered as text.
struct SavedFacts {
    storage_budget: Value,
    notes: Option<Value>,
}

impl SavedFacts {
    fn of(prompt: &str) -> SavedFacts {
        let block = |heading: &str| -> Value {
            let start = format!("# {heading}\n");
            let Some(after) = prompt.find(&start).map(|at| &prompt[at + start.len()..]) else { return Value::Null };
            let Some(json) = after.split_once("```json\n").map(|(_, rest)| rest) else { return Value::Null };
            json.split_once("\n```").and_then(|(text, _)| serde_json::from_str(text).ok()).unwrap_or(Value::Null)
        };
        let handoff = block("HANDOFF FROM EARLIER ATTEMPTS");
        SavedFacts { storage_budget: block("CURRENT FACTS AND PATHS")["storage_budget"].clone(), notes: (!handoff.is_null()).then(|| handoff["notes"]["text"].clone()) }
    }
}
