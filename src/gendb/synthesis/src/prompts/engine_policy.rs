//! The engine author's role decisions (`RolePolicy`): the prompt of every call of a
//! round, the round's objective and its stop; and the prompt of the general engine line ([`general_author_prompt`]),
//! which `engine::sessions::GeneralSessionPolicy` uses.
//!
//! A round is one author session ending with one submission (`engine::rounds`). Its prompt is structured Markdown in the
//! roles' common format: key paths and the scope rules first; then the engine sections (`prompts::engine_sections`:
//! task, goal, what is fixed, generality rules, storage, evaluation, rounds and versions, how to work, inputs, tools),
//! with the shared `physical_only` policy, proof, reuse, parallelism and check-economy advice, the submission rule and
//! the processes appendix (`prompts::sections`, unchanged); then the call's data: CURRENT FACTS (the engine head from
//! `prompts::engine_facts`, leading with the totals gap per worker count, then the shared Storage, Integrity
//! constraints and Host sections), HANDOFF FROM EARLIER ROUNDS with the carried `NOTES.md`, the in-round handoff of a
//! fresh session, LEDGER and LATEST FEEDBACK (`prompts::data_sections::render_engine`). Everything the author needs
//! beyond that is a file `files.author_contract` maps. Nothing here names a query.
//!
//! A general-line session continues one provider session across its submissions. Its first call (and any call that
//! starts a fresh provider session) gets the full prompt: the key paths ([`general_key_paths`]: the workspace, the
//! session and the run's records given once, every file relative to them) and scope, the general sections
//! (`prompts::engine_general_sections`: goal, the request's emphasis when it sets one, how to work, what is fixed,
//! storage with its policy, fallback, design and proofs, the loop, inputs, tools, submission, the processes appendix),
//! then the data (`prompts::data_sections::render_general`): CURRENT FACTS (`prompts::engine_facts::general::
//! general_facts`, then the line's compact Integrity constraints and Host), the handoff (on a session's first call),
//! LEDGER and LATEST FEEDBACK. A run with one branch is one line of versions
//! (`engine_general_sections::Shape`): its texts say nothing of branches, merges or rebases. A call that continues the
//! provider session after an evaluation (`iteration > 1` and no handoff: the session already holds the full prompt)
//! gets only the evaluation and the facts that changed, led by CHANGED INSTRUCTIONS when GenDB's instruction sections
//! differ from those the provider session holds (`engine::sessions::held_instructions`; every call that sends
//! instructions records their digests, `engine::sessions::record_instructions`).
//!
//! A call that resumes its provider session after the session's previous call was stopped from outside (the ledger
//! records that it resumes, and the stopped call's receipt was rebuilt after the controller was lost:
//! `controller-loss-recovery.json`, `providers::claude_code::CONTROLLER_LOSS_RECOVERY_FILE`) gets a short message
//! ([`general_resumed_prompt`]): CHANGED INSTRUCTIONS when the sections changed, that the call was stopped and the
//! context is kept, and the facts now. When the provider session's context was compacted, the call gets the prompt it
//! would get otherwise (the full prompt, or a continued call's).
//!
//! A stage run (the context's `general.stage`) gets the Stage 2 section after the goal and the main
//! direction, the stage forms of the goal, what is fixed and the loop (`engine_general_sections::Workloads`), its
//! workloads' names for `@GOAL_WORKLOAD@` and `@KEPT_WORKLOADS@`, the goal named in the session line, every workload's
//! files in the key paths (`files.workloads.<name>.<file>`, flattened), and the stage facts.
//!
//! A run of `engine.workloads` (the context's `general.workloads`) gets the section One
//! engine for every workload in Stage 2's place, the Set forms of the goal, what is fixed and the loop, its workloads'
//! names for `@PRIMARY_WORKLOAD@`, `@COUNTED_WORKLOADS@`, `@CHECK_WORKLOADS@` and `@KEPT_MEMBERS@`, the primary
//! workload named in the session line, every workload's files in the key paths, and the workloads' facts
//! (`prompts::engine_facts::general::workloads`).
//!
//! Any call of a general-line session starts with the run operator's pending notes to its branch (`engine::operator_note`:
//! `# NOTE FROM THE RUN'S OPERATOR`, each note shown once); the instruction records digest the prompt the call sends,
//! notes included, and the instruction sections never include the notes.

use super::data_sections::{self, AuthorKind, DataViews};
use super::engine_facts::general::{GeneralView, branch_handoff, changed_facts, evaluation_section, general_facts, resumed_facts, timed_calls};
use super::engine_facts::{engine_facts, rounds_handoff};
use super::engine_general_sections::{self as general, Shape, Workloads};
use super::engine_sections as engine;
use super::instructions::{self, Section};
use super::policy::{evaluated_trials, latest_delta, submission_results};
use super::sections;
use crate::controller::layout::RunLayout;
use crate::controller::ledger::LedgerState;
use crate::controller::limits::count_guard_text;
use crate::controller::{PromptInput, RolePolicy, StopReason, Trial, records};
use crate::engine::protocol::hot_calls_text;
use crate::engine::sessions::{self as engine_sessions, HeldInstructions, InstructionsSent, ProviderContext};
use crate::providers::claude_code::CONTROLLER_LOSS_RECOVERY_FILE;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

/// `objective.kind` of an engine round: its one submission is accepted as the next version or recorded as an attempt.
pub const ENGINE_ROUND_OBJECTIVE: &str = "engine_round";
/// The rule of a round's objective.
pub const ENGINE_ROUND_RULE: &str = "a round ends with one submission: when it passes admission (whole-crate Verus with 0 errors, source rules, composition, coverage, storage policy and budget, saved-answer checks of every template and timed variant), it becomes the next version and is then timed officially (timing records, it never gates); otherwise the round is recorded as an attempt and the next round starts from the latest version";

/// The engine role's policy. It holds no state.
#[derive(Clone, Copy, Debug, Default)]
pub struct EnginePolicy;

impl RolePolicy for EnginePolicy {
    fn author_prompt(&self, input: &PromptInput) -> String {
        engine_author_prompt(input)
    }

    fn objective_status(&self, _context: &Value, trials: &[Trial]) -> Value {
        round_objective_status(trials)
    }

    /// The round's one accepted submission ends it before another author call.
    fn search_stop(&self, _context: &Value, trials: &[Trial]) -> Option<StopReason> {
        trials.iter().any(Trial::eligible).then_some(StopReason::FirstEligibleCandidate)
    }

    /// The identity of a retained submission's frozen engine crate (shown when a fresh session of the same round
    /// starts): its crate version and frozen crate. The workspace is not compared.
    fn submission_code(&self, frozen_dir: &Path, _candidate: &Value, _workspace: Option<&Path>) -> Value {
        let candidate = frozen_dir.join("candidate.json");
        let frozen = std::fs::read(&candidate).ok().and_then(|bytes| serde_json::from_slice::<crate::engine::submission::FrozenEngine>(&bytes).ok());
        match frozen {
            Some(engine) => json!({"crate_version":crate::engine::submission::engine_version_id(&engine, frozen_dir).ok(),"frozen_crate":frozen_dir.join("crate"),"workspace":"not_compared"}),
            None => json!({"error":format!("{} cannot be read", candidate.display())}),
        }
    }
}

/// The round's objective over its trials: met by its first eligible (accepted) submission.
pub fn round_objective_status(trials: &[Trial]) -> Value {
    let met = trials.iter().find(|t| t.eligible());
    json!({"status":if met.is_some() {"met"} else {"unmet"},"kind":ENGINE_ROUND_OBJECTIVE,"iteration":met.map(|t| t.iteration),"rule":ENGINE_ROUND_RULE})
}

/// The key paths at the top of the prompt: every `files` entry of the context and this prompt's saved copy, then the
/// scope rules.
fn key_paths(context: &Value, prompt_file: &Path) -> String {
    let mut lines = vec!["# Key paths and scope".to_string(), String::new()];
    for (name, path) in context["files"].as_object().into_iter().flatten().filter(|(_, path)| !path.is_null()) {
        lines.push(format!("- `{name}`: {}", path.as_str().map_or_else(|| path.to_string(), str::to_string)));
    }
    lines.push(format!("- `this_prompt`: {} (this complete prompt, saved before the call; reread it there)", prompt_file.display()));
    lines.push(String::new());
    lines.push(sections::SCOPE_RULES.to_string());
    lines.join("\n")
}

/// The key paths of a general-line prompt: the workspace, the session directory (its parent) and the run's records
/// (`<run>/engine`) given once, then every `files` entry of the context and this prompt's saved copy as a name and a
/// path relative to the directory it lies in (the contract directory inside the workspace too), then the scope rules.
/// An entry outside these directories keeps its absolute path; a context without a workspace gets [`key_paths`].
fn general_key_paths(context: &Value, prompt_file: &Path) -> String {
    let Some(workspace) = context["files"]["workspace"].as_str().map(PathBuf::from) else {
        return key_paths(context, prompt_file);
    };
    let session = workspace.parent().map(Path::to_path_buf);
    let records = crate::prompts::engine_facts::general::engine_dir(context);
    let contract = workspace.join(crate::prompts::engine_contract::CONTRACT_DIRECTORY);
    // The directories, the most specific first: each entry goes with the first one it lies in.
    let mut roots: Vec<(String, PathBuf)> = vec![(format!("in `<workspace>/{}`, the contract directory", crate::prompts::engine_contract::CONTRACT_DIRECTORY), contract), ("in `<workspace>`".into(), workspace.clone())];
    roots.extend(session.iter().map(|s| ("in `<session>`".to_string(), s.clone())));
    roots.extend(records.iter().map(|r| ("in `<records>`".to_string(), r.clone())));
    let mut entries: Vec<(String, String)> = vec![];
    for (name, path) in context["files"].as_object().into_iter().flatten().filter(|(name, path)| *name != "workspace" && !path.is_null()) {
        flattened_files(name, path, &mut entries);
    }
    entries.push(("this_prompt".into(), prompt_file.display().to_string()));
    let mut grouped: Vec<(String, Vec<String>)> = roots.iter().map(|(label, _)| (label.clone(), vec![])).collect();
    let mut elsewhere: Vec<String> = vec![];
    for (name, path) in entries {
        let note = if name == "this_prompt" { " (this complete prompt, saved before the call; reread it there)" } else { "" };
        match roots.iter().position(|(_, root)| Path::new(&path).starts_with(root)) {
            Some(at) => {
                let relative = Path::new(&path).strip_prefix(&roots[at].1).map(|p| p.display().to_string()).unwrap_or_default();
                grouped[at].1.push(format!("`{name}` {relative}{note}"));
            }
            None => elsewhere.push(format!("`{name}` {path}{note}")),
        }
    }
    let mut lines = vec![
        "# Key paths and scope".to_string(),
        String::new(),
        "`files.<name>` in this prompt names one of the paths below; `<workspace>`, `<session>` and `<records>` name these directories.".to_string(),
        String::new(),
        format!("- `<workspace>` (`files.workspace`, your workspace): {}", workspace.display()),
    ];
    if session.is_some() {
        lines.push("- `<session>`: the parent of `<workspace>`, this session's directory".to_string());
    }
    if let Some(records) = &records {
        lines.push(format!("- `<records>`: {} (the run's records)", records.display()));
    }
    for (label, names) in grouped.iter().filter(|(_, names)| !names.is_empty()) {
        lines.push(format!("- {label}: {}", names.join(", ")));
    }
    if !elsewhere.is_empty() {
        lines.push(format!("- elsewhere: {}", elsewhere.join(", ")));
    }
    lines.push(String::new());
    lines.push(sections::SCOPE_RULES.to_string());
    lines.join("\n")
}

/// The `files` entry `name` as `(name, path)` pairs: a path as it is, an object (a stage run's `files.workloads`, by
/// workload and file) as one pair per path inside it, named by its dotted key path (`workloads.sec.templates`).
fn flattened_files(name: &str, value: &Value, entries: &mut Vec<(String, String)>) {
    match value {
        Value::Null => {}
        Value::Object(fields) => {
            for (key, inner) in fields {
                flattened_files(&format!("{name}.{key}"), inner, entries);
            }
        }
        other => entries.push((name.to_string(), other.as_str().map_or_else(|| other.to_string(), str::to_string))),
    }
}

/// `text` with the engine placeholders and the shared advice filled in from the context.
fn filled(text: &str, context: &Value) -> String {
    let kinds: Vec<String> = context["engine"]["training"]["variants"]["kinds"].as_array().into_iter().flatten().filter_map(|k| k.as_str().map(|k| format!("`{k}`"))).collect();
    text.replace("@PROOF_ADVICE@", sections::PROOF_ADVICE)
        .replace("@REUSE_ADVICE@", &sections::REUSE_ADVICE.replace("@COMMON_DIR@", "`src/agent/common/`"))
        .replace("@PARALLEL_ADVICE@", sections::PARALLEL_ADVICE)
        .replace("@CHECK_ECONOMY@", sections::CHECK_ECONOMY)
        .replace("@TIMING_BINDING@", context["engine"]["training"]["timing_binding"].as_str().unwrap_or("-"))
        .replace("@VARIANT_KINDS@", &if kinds.is_empty() { "none".to_string() } else { kinds.join(", ") })
        .replace("@ROUND@", &context["round"]["number"].to_string())
}

/// The complete prompt of one engine author call.
pub fn engine_author_prompt(input: &PromptInput) -> String {
    let context = input.context;
    let trials = evaluated_trials(input.feedback);
    let data = data_sections::render_engine(
        &DataViews {
            author: AuthorKind::Engine,
            context,
            targets: &json!({"cells":[]}),
            submissions: &submission_results(&trials, &[], &[], None),
            objective: &round_objective_status(&trials),
            handoff: input.handoff,
            ledger: input.ledger,
            latest: &latest_delta(input.feedback, &trials),
        },
        &engine_facts(context),
        &rounds_handoff(context),
    );
    let rounds_so_far = context["engine"]["rounds"].as_array().map_or(0, Vec::len);
    let guard = context["engine"]["limits"]["max_iterations"].as_u64().map_or_else(|| "unset".to_string(), |n| count_guard_text(n as u32));
    let parts = [
        key_paths(context, input.prompt_file),
        format!(
            "GenDB owns evaluation and is requesting the one submission of round {} ({rounds_so_far} earlier rounds; the user's round guard: {guard}).",
            context["round"]["number"]
        ),
        engine::ENGINE_TASK.to_string(),
        engine::ENGINE_GOAL.to_string(),
        engine::ENGINE_FIXED.to_string(),
        engine::GENERALITY_RULES.to_string(),
        engine::ENGINE_STORAGE.to_string(),
        sections::PHYSICAL_ONLY_POLICY.to_string(),
        engine::ENGINE_EVALUATION.to_string(),
        engine::ENGINE_ROUNDS.to_string(),
        engine::ENGINE_HOW_TO_WORK.to_string(),
        engine::ENGINE_INPUTS.to_string(),
        engine::ENGINE_TOOLS.to_string(),
        sections::submission(crate::engine::submission::MANIFEST_FILE),
        sections::PROCESSES_APPENDIX.to_string(),
        data,
    ];
    filled(&parts.join("\n\n"), context)
}

/// `objective.kind` of a general-line session as its prompt states it (the session policy's objective stays open).
const GENERAL_OBJECTIVE: &str = "general_engine_session";

/// The prompt of every call of a general-line session (module documentation): the full prompt, or, on a call that
/// continues its provider session after an evaluation, the evaluation and the facts that changed.
pub fn general_author_prompt(input: &PromptInput) -> String {
    let trials = evaluated_trials(input.feedback);
    let (prompt, sent) = if let Some(resumed) = resumed_after_stop(input) {
        general_resumed_prompt(input, &trials, &resumed)
    } else if input.iteration > 1 && input.handoff.is_null() && !trials.is_empty() {
        general_continuation_prompt(input, &trials)
    } else {
        general_full_prompt(input, &trials)
    };
    let prompt = match session_call(input.prompt_file) {
        Some((session, call)) => crate::engine::operator_note::with_pending_notes(prompt, &session, call),
        None => prompt,
    };
    if let Some((how, sections)) = sent {
        record_sent_instructions(input, how, &prompt, &sections);
    }
    prompt
}

/// What a prompt sends of the instructions, recorded once the whole prompt (with any operator note) is known.
type SentInstructions = Option<(InstructionsSent, Vec<Section>)>;

/// The data sections of a general-line call over `context` (`data_sections::render_general`). The LEDGER keeps this
/// call and the earlier calls without a candidate; its submission guard and cost guard lines are left out, because the
/// general line has no submission limit and one run budget, which the facts state (`Budget and session`, from the same
/// ledger view).
fn general_data(input: &PromptInput, trials: &[Trial], context: &Value, facts: &[String], handoff: &[String]) -> String {
    let objective = json!({"status":"unmet","kind":GENERAL_OBJECTIVE});
    let mut ledger = input.ledger.clone();
    if let Some(fields) = ledger.as_object_mut() {
        for guard in ["submissions", "spent_usd", "spent_complete", "max_cost_usd", "remaining_usd"] {
            fields.remove(guard);
        }
    }
    data_sections::render_general(
        &DataViews {
            author: AuthorKind::GeneralEngine,
            context,
            targets: &json!({"cells":[]}),
            submissions: &submission_results(trials, &[], &[], None),
            objective: &objective,
            handoff: input.handoff,
            ledger: &ledger,
            latest: &latest_delta(input.feedback, trials),
        },
        facts,
        handoff,
    )
}

/// The instruction sections of the general prompt for `context`, filled, in prompt order: everything between the key
/// paths and the data (`prompts::instructions`). A full prompt sends them all; a continued call sends those that
/// changed since its provider session's first prompt.
fn general_instructions(context: &Value) -> String {
    let (shape, workloads) = (Shape::of_context(context), Workloads::of_context(context));
    let mut parts = vec![
        general::goal(shape, workloads),
        general::GENERAL_HOW_TO_WORK.to_string(),
        general::fixed(workloads),
        general::storage_section(),
        general::GENERAL_FALLBACK.to_string(),
        general::design_and_proofs(shape),
        general::the_loop(shape, workloads),
        general::inputs(shape),
        general::GENERAL_TOOLS.to_string(),
        general::general_submission(crate::engine::submission::MANIFEST_FILE, shape),
        general::GENERAL_PROCESSES_APPENDIX.to_string(),
    ];
    // The Stage 2 section of a stage run (in a run of several workloads, One engine for every workload) follows the goal,
    // and the request's emphasis (`engine.emphasis`) comes between them; without them their sections are absent.
    if let Some(section) = general::workloads_section(context).or_else(|| general::stage_section(context).map(str::to_string)) {
        parts.insert(1, section);
    }
    if let Some(emphasis) = general::emphasis_section(context) {
        parts.insert(1, emphasis.to_string());
    }
    // A continued run (`engine.seed_version`) says so right after the goal; without a seed the section is absent.
    if let Some(continued) = general::continued_section(context) {
        parts.insert(1, continued.to_string());
    }
    general_filled(&parts.join("\n\n"), context)
}

/// The session directory and the call of a prompt saved at `<session>/calls/NNNN/prompt.txt` (`RunLayout::prompt`);
/// `None` for a prompt saved elsewhere.
fn session_call(prompt_file: &Path) -> Option<(PathBuf, u64)> {
    let call_dir = prompt_file.parent()?;
    let calls = call_dir.parent().filter(|calls| calls.file_name().is_some_and(|name| name == "calls"))?;
    let call = call_dir.file_name()?.to_str()?.parse().ok()?;
    Some((calls.parent()?.to_path_buf(), call))
}

/// Record what `prompt` sends of the instructions (`engine::sessions::record_instructions`). The prompt cannot fail: a
/// record that cannot be written leaves the next continued call to compare with the provider session's first prompt,
/// which at worst sends a change again.
fn record_sent_instructions(input: &PromptInput, sent: InstructionsSent, prompt: &str, current: &[Section]) {
    if let Some((session, call)) = session_call(input.prompt_file) {
        let _ = engine_sessions::record_instructions(&session, call, sent, prompt, current.iter().map(Section::digest).collect());
    }
}

/// The full prompt of a general-line call (module documentation), and its instruction sections (all sent).
fn general_full_prompt(input: &PromptInput, trials: &[Trial]) -> (String, SentInstructions) {
    let context = input.context;
    let shape = Shape::of_context(context);
    // A fresh provider session inside a session (`handoff` set) also sees the session's latest evaluation.
    let latest = trials.last().filter(|_| !input.handoff.is_null());
    let accepted = latest.filter(|t| t.evaluation["accepted"] == true).and_then(|t| t.evaluation["node"].as_str());
    let view = GeneralView::read(context, accepted);
    let handoff = if input.handoff.is_null() { branch_handoff(context, &view) } else { vec![] };
    let data = general_data(input, trials, context, &general_facts(context, &view, latest, input.ledger), &handoff);
    let session = &context["general"]["session"];
    let session_line = match shape {
        Shape::OneLine => format!("This is session {}", session["number"]),
        Shape::Branches => format!("This is session {} of branch {}", session["number"], session["branch"].as_str().unwrap_or("-")),
    };
    // A stage run names the goal workload, whose scale the session works at; a run of several workloads its primary.
    let goal = match (general::workloads_of(context), general::stage_of(context)) {
        (Some(workloads), _) => format!(" of the primary workload `{}`", primary_workload(workloads)),
        (None, Some(stage)) => format!(" of the goal workload `{}`", stage["goal"].as_str().unwrap_or("-")),
        (None, None) => String::new(),
    };
    let parts = [
        general_key_paths(context, input.prompt_file),
        format!("{session_line} at scale {}{goal}, seeded from {}.", context["general"]["scale"]["name"].as_str().unwrap_or("-"), session["seed"].as_str().unwrap_or("-")),
        general_instructions(context),
        data,
    ];
    let prompt = general_filled(&parts.join("\n\n"), context);
    let sections = instructions::instruction_sections(&prompt);
    (prompt, Some((InstructionsSent::Full, sections)))
}

/// The CHANGED INSTRUCTIONS section of a continued call (module documentation), or `None` when the provider session
/// holds the current instruction sections (or nothing is known about what it holds).
fn changed_instructions(input: &PromptInput, current: &[Section], first_prompt: &str) -> Option<String> {
    let (session, call) = session_call(input.prompt_file)?;
    let held = match engine_sessions::held_instructions(&session, call) {
        HeldInstructions::Recorded { sections, .. } | HeldInstructions::FirstPrompt { sections, .. } => sections,
        HeldInstructions::Unknown => return None,
    };
    let changes = instructions::changes(&held, current);
    if changes.is_empty() {
        return None;
    }
    let mut parts = vec![general::changed_instructions_opening(first_prompt, changes.changed.len(), &changes.removed)];
    parts.extend(changes.changed.iter().map(|section| section.text.clone()));
    parts.push(general::CHANGED_INSTRUCTIONS_END.to_string());
    Some(parts.join("\n\n"))
}

/// The prompt of a call that continues its provider session after an evaluation (module documentation), and the
/// instruction sections it sends when they changed.
fn general_continuation_prompt(input: &PromptInput, trials: &[Trial]) -> (String, SentInstructions) {
    let context = input.context;
    let last = trials.last();
    let accepted = last.filter(|t| t.evaluation["accepted"] == true).and_then(|t| t.evaluation["node"].as_str());
    let view = GeneralView::read(context, accepted);
    // The provider session's first call holds its full prompt (`calls/NNNN/prompt.txt` beside this call's).
    let first = last.and_then(|t| t.evaluation["next_call"]["context"]["calls"][0].as_u64());
    let first_prompt = first.zip(input.prompt_file.parent().and_then(Path::parent)).map_or_else(
        || "the first call's `prompt.txt` under this session's `calls/`".to_string(),
        |(call, calls)| format!("`{}`", calls.join(format!("{call:04}")).join(crate::controller::layout::PROMPT_FILE).display()),
    );
    let current = instructions::level_one_sections(&general_instructions(context));
    let changed = changed_instructions(input, &current, &first_prompt);
    let evaluation = last.map(|t| evaluation_section(context, &view, t)).unwrap_or_default();
    // Only the facts that change: the shared sections (storage policy, constraints, host) are in the first prompt.
    let unchanged_omitted = json!({"files":context["files"]});
    let data = general_data(input, trials, &unchanged_omitted, &changed_facts(context, &view, last, input.ledger), &[]);
    let opening = if changed.is_some() { general::GENERAL_CONTINUATION_AFTER_CHANGES } else { general::GENERAL_CONTINUATION };
    let mut parts: Vec<String> = changed.iter().cloned().collect();
    parts.extend([opening.replace("@FIRST_PROMPT@", &first_prompt), evaluation.join("\n"), data]);
    let prompt = general_filled(&parts.join("\n\n"), context);
    (prompt, changed.is_some().then_some((InstructionsSent::Changed, current)))
}

/// A call that resumes its provider session after the session's previous call was stopped (module documentation).
struct ResumedAfterStop {
    /// The stopped call, and the first call of the provider session (its `prompt.txt` holds the full prompt).
    stopped_call: u64,
    first_prompt: PathBuf,
    /// The provider session's context up to the stopped call (`ProviderContext`, serialized).
    provider_context: Value,
}

/// Whether the call of `input` resumes its provider session after a stopped call whose context was never compacted
/// (module documentation). Reads the session's ledger, the stopped call's directory and the provider session's
/// transcripts; `None` when any of them says otherwise or cannot be read, and the call then gets the prompt it would
/// get otherwise.
fn resumed_after_stop(input: &PromptInput) -> Option<ResumedAfterStop> {
    if !input.handoff.is_null() {
        return None;
    }
    let (session, call) = session_call(input.prompt_file)?;
    let layout = RunLayout::new(&session);
    let state: LedgerState = records::read_json(&layout.ledger()).ok()?;
    let this = state.call(call)?;
    if !state.resumes_provider_session(this) {
        return None;
    }
    let provider_session = state.provider_session_of(this);
    let earlier: Vec<u64> = state.calls.iter().filter(|c| c.id < call && state.provider_session_of(c) == provider_session).map(|c| c.id).collect();
    let (first, stopped) = (*earlier.iter().min()?, *earlier.iter().max()?);
    if !layout.call(stopped).join(CONTROLLER_LOSS_RECOVERY_FILE).is_file() {
        return None;
    }
    let context = ProviderContext::of_call(&session, stopped).ok()?;
    if context.compactions > 0 {
        return None;
    }
    Some(ResumedAfterStop { stopped_call: stopped, first_prompt: layout.prompt(first), provider_context: serde_json::to_value(&context).ok()? })
}

/// The prompt of a call that resumes its provider session after a stopped call (module documentation): CHANGED
/// INSTRUCTIONS when the sections changed, the opening, then the facts now, the ledger and the latest call (the stopped
/// one); and the instruction sections it sends when they changed. The provider session already holds the rest.
fn general_resumed_prompt(input: &PromptInput, trials: &[Trial], resumed: &ResumedAfterStop) -> (String, SentInstructions) {
    let context = input.context;
    let view = GeneralView::read(context, None);
    let first_prompt = format!("`{}`", resumed.first_prompt.display());
    let current = instructions::level_one_sections(&general_instructions(context));
    let changed = changed_instructions(input, &current, &first_prompt);
    let opening = general::resumed_after_stop_opening(resumed.stopped_call, &first_prompt, changed.is_some());
    // As in a continued call: the shared sections (storage policy, constraints, host) are in the first prompt.
    let unchanged_omitted = json!({"files":context["files"]});
    let facts = resumed_facts(context, &view, trials.last(), input.ledger, &resumed.provider_context);
    let data = general_data(input, trials, &unchanged_omitted, &facts, &[]);
    let mut parts: Vec<String> = changed.iter().cloned().collect();
    parts.extend([opening, data]);
    let prompt = general_filled(&parts.join("\n\n"), context);
    (prompt, changed.is_some().then_some((InstructionsSent::Changed, current)))
}

/// The primary workload's name in a workloads view (the workloads fixture: the member marked `primary`, else the first).
fn primary_workload(workloads: &Value) -> &str {
    let all = workloads.as_array().map(Vec::as_slice).unwrap_or_default();
    all.iter().find(|w| w["primary"] == true).or(all.first()).and_then(|w| w["name"].as_str()).unwrap_or("-")
}

/// The names of the workloads of `role` in a workloads view, each in backticks and joined by "and"; `none` when there
/// is none.
fn workloads_with_role(workloads: &Value, role: &str) -> String {
    let names: Vec<String> = workloads.as_array().into_iter().flatten().filter(|w| w["role"] == role).map(|w| format!("`{}`", w["name"].as_str().unwrap_or("-"))).collect();
    if names.is_empty() { "none".to_string() } else { names.join(" and ") }
}

/// `text` with the general line's placeholders and the shared advice filled in from the context; a stage run's workload
/// names (`@GOAL_WORKLOAD@`, `@KEPT_WORKLOADS@`) from its stage view; a run of several workloads' names
/// (`@PRIMARY_WORKLOAD@`, `@COUNTED_WORKLOADS@`, `@CHECK_WORKLOADS@`, `@KEPT_MEMBERS@`) from its workloads view.
fn general_filled(text: &str, context: &Value) -> String {
    let general = &context["general"];
    let named = |name: &Value| format!("`{}`", name.as_str().unwrap_or("-"));
    let (goal, kept) = match general::stage_of(context) {
        Some(stage) => {
            let kept: Vec<String> = stage["workloads"].as_array().into_iter().flatten().filter(|w| w["role"] == "kept").map(|w| named(&w["name"])).collect();
            (named(&stage["goal"]), if kept.is_empty() { "-".to_string() } else { kept.join(" and ") })
        }
        None => ("-".to_string(), "-".to_string()),
    };
    let set = general::workloads_of(context);
    let (primary, counted, check, kept_members) = match set {
        Some(workloads) => (format!("`{}`", primary_workload(workloads)), workloads_with_role(workloads, "counted"), workloads_with_role(workloads, "check"), workloads_with_role(workloads, "kept")),
        None => ("-".to_string(), "-".to_string(), "-".to_string(), "-".to_string()),
    };
    // A continued run (`general.seed`): its root is a seed version, not version 0; a run of several workloads: its root
    // has one side per workload.
    let seed = &general["seed"];
    let version_zero_is = if set.is_some() {
        "GenDB's version 0 of a run (the interpreter engine; this run's root has one side per workload instead, CURRENT FACTS, The root's sides) is exactly this"
    } else if seed.is_object() {
        "GenDB's version 0 of a run (the interpreter engine; this run's root is a seed version instead) is exactly this"
    } else {
        "Version 0 is exactly this (`files.versions_records`/v000/code)"
    };
    let templates_of = |names: &Value| -> String {
        let names: Vec<String> = names.as_array().into_iter().flatten().filter_map(|n| n.as_str().map(|n| format!("`{n}`"))).collect();
        match names.len() {
            0 => "no template".to_string(),
            1 => format!("1 template ({})", names[0]),
            n => format!("{n} templates ({})", names.join(", ")),
        }
    };
    let kinds: Vec<String> = context["engine"]["training"]["variants"]["kinds"].as_array().into_iter().flatten().filter_map(|k| k.as_str().map(|k| format!("`{k}`"))).collect();
    let memory = general["limits"]["anon_memory_limit_bytes"].as_u64().map_or("-".to_string(), |b| format!("{} GiB", b as f64 / (1u64 << 30) as f64));
    text.replace("@CALL_LIMIT@", &general["limits"]["call_limit_seconds"].as_u64().map_or("-".to_string(), |s| format!("{s} s")))
        .replace("@TIMED_CALLS@", &hot_calls_text(timed_calls(context)))
        .replace("@MEMORY_LIMIT@", &memory)
        .replace("@BRANCHES@", &general["branches"].as_array().map_or("-".to_string(), |b| b.len().to_string()))
        .replace("@VARIANT_KINDS@", &if kinds.is_empty() { "none".to_string() } else { kinds.join(", ") })
        .replace("@GOAL_WORKLOAD@", &goal)
        .replace("@KEPT_WORKLOADS@", &kept)
        .replace("@PRIMARY_WORKLOAD@", &primary)
        .replace("@COUNTED_WORKLOADS@", &counted)
        .replace("@CHECK_WORKLOADS@", &check)
        .replace("@KEPT_MEMBERS@", &kept_members)
        .replace("@VERSION_ZERO_IS@", version_zero_is)
        .replace("@SEED_VERSION@", &seed["version"].as_str().map_or("-".to_string(), |v| format!("`{v}`")))
        // The seed run by its directory name: other runs are not inputs (the input boundary), so no path is given.
        .replace("@SEED_RUN@", seed["run"].as_str().and_then(|run| std::path::Path::new(run).file_name()).and_then(|name| name.to_str()).unwrap_or("-"))
        .replace("@SEED_TEMPLATES@", &templates_of(&seed["seed_templates"]))
        .replace("@NEW_TEMPLATES@", &templates_of(&seed["new_templates"]))
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::controller::limits::tests::limits;
    use crate::controller::ledger::TrialStatus;

    fn trial(iteration: u32, evaluation: Value) -> Trial {
        serde_json::from_value(json!({"iteration":iteration,"call_id":iteration,"candidate":{},"status":TrialStatus::Evaluated,"evaluation":evaluation})).unwrap()
    }

    /// The round stops at its accepted submission; a refused one leaves it unmet.
    #[test]
    fn a_round_is_met_by_its_accepted_submission() {
        let refused = trial(1, json!({"eligible":false,"status":"refusal"}));
        assert_eq!(round_objective_status(std::slice::from_ref(&refused))["status"], "unmet");
        assert_eq!(EnginePolicy.search_stop(&Value::Null, std::slice::from_ref(&refused)), None);
        let accepted = [refused, trial(2, json!({"eligible":true,"status":"version_accepted"}))];
        assert_eq!(EnginePolicy.search_stop(&Value::Null, &accepted), Some(StopReason::FirstEligibleCandidate));
        assert_eq!(round_objective_status(&accepted)["iteration"], 2);
    }

    /// A schema-engine round prompt with every data section filled: two templates with baselines, a version with totals
    /// and variants, an accepted and a failed round, an evaluated submission with local jobs, a handoff, the ledger,
    /// the storage budget, the declared constraints and the observed host.
    pub(crate) fn schema_line_fixture_prompt() -> String {
        let context = json!({"files":{"workspace":"/w","author_contract":"/w/contract/engine/index.json","engine_map":"/w/ENGINE_MAP.md","notes":"/w/NOTES.md",
                "versions_records":"/run/engine/versions","rounds":"/run/engine/rounds"},
            "round":{"number":3,"seed":{"kind":"version","description":"v1 (round 1)","version":"v1"},"notes":{"file":"/w/NOTES.md","from":"v1 (round 1)","text":"# Notes\nplan"}},
            "engine":{"limits":{"max_iterations":12},
                "training":{"timing_binding":"v0","workers":[1,32],"other_bindings":["v1"],
                    "templates":[{"name":"Q01","tables":["t"],"baselines":[{"binding":"v0","workers":1,"umbra_ns":1_000_000,"duckdb_ns":2_000_000},{"binding":"v0","workers":32,"umbra_ns":500_000,"duckdb_ns":400_000}]},
                        {"name":"Q02","tables":["t","u"],"baselines":[{"binding":"v0","workers":1,"umbra_ns":3_000_000,"duckdb_ns":2_500_000},{"binding":"v0","workers":32,"umbra_ns":700_000,"duckdb_ns":900_000}]}],
                    "baseline_totals":[{"binding":"v0","workers":1,"umbra_ns":4_000_000,"duckdb_ns":4_500_000,"target_ns":4_000_000,"target_engine":"umbra"},
                        {"binding":"v0","workers":32,"umbra_ns":1_200_000,"duckdb_ns":1_300_000,"target_ns":1_200_000,"target_engine":"umbra"}],
                    "variants":{"kinds":["wrapped_tables","from_permutation"],"frozen":4,"timed":2,"not_timed":2}},
                "versions":[{"version":"v1","round":1,"crate_version":"abc","directory":"/run/engine/versions/v001",
                    "totals":{"workers":[{"workers":1,"engine_ns":5_000_000,"umbra_ns":4_000_000,"duckdb_ns":4_500_000,"target_ns":4_000_000,"target_engine":"umbra","gap_ns":1_000_000,"margin":0.8,"below_both":false},
                        {"workers":32,"engine_ns":1_000_000,"umbra_ns":1_200_000,"duckdb_ns":1_300_000,"target_ns":1_200_000,"target_engine":"umbra","gap_ns":-200_000,"margin":1.2,"below_both":true}],
                        "templates":[{"template":"Q01","workers":1,"engine":{"median_ns":2_000_000}},{"template":"Q02","workers":32,"engine":{"median_ns":600_000}}],
                        "stop":{"stop":false,"margin_reached":0.8,"reasons":["1 workers: not below Umbra"]}},
                    "variants":{"summary":[{"workers":64,"compared":2,"geometric_mean":1.1,"largest":{"ratio":1.3,"variant":{"id":"Q01-wrapped_tables"}}}],"report":"/v/variants.md"},
                    "other_bindings":[{"binding":"v1","totals":{"workers":[{"engine_ns":5_100_000}]}}]}],
                "rounds":[{"round":1,"outcome":"version","version":"v1","seed":"an empty engine crate","reported_cost_usd":"12.5","directory":"/run/engine/rounds/round-0001"},
                    {"round":2,"outcome":"attempt","status":"proof_failure","reason":"iteration_limit","error":"Verus: postcondition not satisfied","failure_class":"proof_failure",
                        "workspace":"/run/engine/rounds/round-0002/author","evaluation_record":"/r2/e.json","seed":"v1 (round 1)","reported_cost_usd":"3.25","directory":"/run/engine/rounds/round-0002"}]},
            "storage_policy":{"kind":"physical_only"},
            "storage_budget":{"budget_bytes":1_000_000_000u64,"used_bytes":600_000_000u64,"left_bytes":400_000_000u64,"used_by":[{"name":"flat_t","counted_bytes":600_000_000u64}],
                "file":"/w/contract/engine/storage-budget.json","meaning":"m"},
            "performance":{"free_bytes_at_prepare":50_000_000_000u64,"evaluation_timing":"official cells: 1 warm + 3 hot calls"},
            "integrity_constraints":{"declarations":[{"table":"t","sql":"PRIMARY KEY (a)"},{"table":"u","sql":"FOREIGN KEY (b) REFERENCES t (a)"}],"in_words":"the engine entry states bound_db with these",
                "trust":"user_declared","basis":"b","details":"/w/contract/engine/integrity-constraints.json"},
            "hardware":{"threads":[1,32]},
            "observed_hardware":{"cpu_model":"Test CPU","packages_in_affinity":2,"physical_cores_in_affinity":32,"logical_cpus_in_affinity":64,"affinity_cpu_list":"0-63",
                "numa_nodes":[{"node":0,"cpu_list":"0,2,4,6","distance":[10,21]},{"node":1,"cpu_list":"1,3,5,7","distance":[21,10]}],
                "caches":[{"level":3,"type":"Unified","size_per_instance":"32 MiB","instances_visible_to_affinity":2,"logical_cpus_sharing_each_instance":32,"line_bytes":64}],
                "host_memory_bytes":{"total":400_000_000_000u64,"available":300_000_000_000u64,"swap_free":0},"memory_scope":"host","cpu_features":"sse4_2 avx2 bmi2 avx512f",
                "crash_dumps":{"coredump_filter":"0x0","contained":true},"source":"/proc"}});
        let feedback = vec![
            json!({"call":1,"iteration":1,"attempt":1,"author_outcome":"success","provider_reported_cost_usd":"1.5"}),
            json!({"call":1,"iteration":1,"local_jobs":{"jobs":2,"by_action":{"trial":1,"verify":1},"failed_jobs":1,"latest":{"job_id":2,"action":"trial","status":"refused","failure_class":"execution_failure","error":"Q02 at 32 workers: answer disagrees"}},
                "session_local_jobs":{"jobs":2,"by_action":{"trial":1,"verify":1},"failed_jobs":1}}),
            json!({"iteration":1,"call_id":1,"candidate":{"candidate_manifest":"verus-engine.json","rationale":"r","data_access_analysis":"d"},"status":"evaluated","directory":"/r/iterations/0001",
                "evaluation":{"eligible":false,"status":"proof_failure","failure_class":"proof_failure","error":"Verus: postcondition not satisfied\nat agent/mod.rs:10",
                    "verus":{"detail":"1 error","outcome":"proof_failure","wall_ns":71_000_000_000u64,"record":"/r/run.json"}}}),
        ];
        let ledger = json!({"max_cost_usd":"40","spent_usd":"1.5","spent_complete":true,"remaining_usd":"38.5","file":"/r/ledger.json","earlier_calls":1,
            "submissions":{"used":1,"limit":1,"remaining_including_this_call":0,"not_counted_framework_failures":[]},
            "runs_without_candidate":[],"this_call":{"call":2,"iteration":2,"attempt":1}});
        let handoff = json!({"paths":{"submission_records":"/r/iterations","earlier_prompts":"/r/calls"},"notes":{"text":"# Notes\nearlier session"},
            "local_trials":[{"call":1,"job":1,"action":"trial","verified":false,"status":"completed","crate_version":"abc","cells":[{"binding":"v0","workers":1,"median_hot_ns":2_000_000,"status":"saved_answers_agree"}]}]});
        engine_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &ledger,
            prompt_file: Path::new("/r/calls/0002/prompt.txt"), handoff: &handoff })
    }

    /// The SHA-256 of `text` in hex.
    pub(crate) fn sha256_hex(text: &str) -> String {
        use sha2::{Digest, Sha256};
        Sha256::digest(text.as_bytes()).iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Golden: the schema-engine round prompt renders byte for byte as before the general line's prompt was added
    /// (the digest of this repository's prompt wording, with the schema-neutral co-clustering example of the storage
    /// policy and the appendix's rule to wait for a local job with the `wait` tool).
    #[test]
    fn the_schema_engine_prompt_renders_as_before() {
        let prompt = schema_line_fixture_prompt();
        assert_eq!(sha256_hex(&prompt), SCHEMA_PROMPT_GOLDEN, "the schema-engine prompt changed:\n{prompt}");
    }

    const SCHEMA_PROMPT_GOLDEN: &str = "bc60c3ccf4b11919347deaea160ecb53a2853c9a38a0c0416ee11f700a393e45";

    /// The four general-line renders of the scripted run, built in its order: b1's first call after version 0; after
    /// its first accepted submission, the call that continues the provider session, and the same call when the
    /// provider session could not be resumed (a fresh provider session with the controller's handoff); after the rest
    /// of session 1, the first call of the branch's fresh second session. The ledger views and the run's spend are the
    /// real ones of the scripted ledgers. `(name, prompt)`.
    pub(crate) fn general_fixture_prompts(root: &Path) -> Vec<(&'static str, String)> {
        use crate::prompts::engine_facts::general::tests as fixture;
        let mut prompts = vec![];
        let run = fixture::version_zero_run(&root.join("scripted"));
        let context = fixture::session_context(&run, 1);
        let ledger = fixture::ledger_view(&run.session_one);
        prompts.push(("first-call-b1-session-1", general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(),
            ledger: &ledger, prompt_file: &run.session_one.join("calls/0001/prompt.txt"), handoff: &Value::Null })));
        fixture::first_submission(&run);
        let context = fixture::session_context(&run, 1);
        let feedback = fixture::feedback_after_first_submission(&run);
        let ledger = fixture::ledger_view(&run.session_one);
        prompts.push(("continued-call-b1-session-1-after-submission-1", general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2,
            limits: &limits(), ledger: &ledger, prompt_file: &run.session_one.join("calls/0002/prompt.txt"), handoff: &Value::Null })));
        let handoff = json!({"paths":{"submission_records":run.session_one.join("iterations"),"earlier_prompts":run.session_one.join("calls")},"notes":{"text":"# Notes\n\n## Direction\n\nVectorized operators.\n"},"local_trials":[]});
        prompts.push(("fresh-provider-session-b1-session-1-call-2", general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2,
            limits: &limits(), ledger: &ledger, prompt_file: &run.session_one.join("calls/0002/prompt.txt"), handoff: &handoff })));
        fixture::rest_of_session_one(&run);
        let context = fixture::session_context(&run, 2);
        let ledger = fixture::ledger_view(&run.session_two);
        prompts.push(("first-call-b1-session-2-fresh", general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(),
            ledger: &ledger, prompt_file: &run.session_two.join("calls/0001/prompt.txt"), handoff: &Value::Null })));
        prompts
    }

    /// `text` with the scratch root `root` written as `<root>`: the fixture renders name paths under a fresh scratch
    /// directory, so their digests compare the text without it.
    pub(crate) fn rooted(text: &str, root: &Path) -> String {
        text.replace(&root.display().to_string(), "<root>")
    }

    /// The general line's renders of a run without a stage (no `general.stage`): the four renders of the scripted run with
    /// branches, then the one-line session of both modes (no emphasis, `co_optimization`), each as `(name, SHA-256 of its
    /// text with the scratch root written as <root>)`.
    fn general_render_digests(root: &Path) -> Vec<(String, String)> {
        let mut digests: Vec<(String, String)> = vec![];
        let branches = root.join("branches");
        for (name, prompt) in general_fixture_prompts(&branches) {
            digests.push((name.to_string(), sha256_hex(&rooted(&prompt, &branches))));
        }
        for emphasis in [None, Some("co_optimization")] {
            let line = root.join(format!("one-line-{}", emphasis.unwrap_or("plain")));
            for (name, prompt) in one_line_session_prompts(&line, emphasis) {
                digests.push((name, sha256_hex(&rooted(&prompt, &line))));
            }
        }
        digests
    }

    /// Golden: without a stage, every general-line render is byte for byte as before the
    /// stage texts were added (digests recorded with the unchanged prompt, facts and contract code, over this
    /// repository's prompt wording), except that the loop's timing step, the final evaluation's sentence and the
    /// evaluation-time estimate state the development cell: 1 warm call and the run's timed hot calls (3 here).
    #[test]
    fn the_general_renders_without_a_stage_are_unchanged() {
        let root = crate::controller::test_support::scratch_root("general-unchanged");
        let digests = general_render_digests(&root);
        let expected: Vec<(String, String)> = GENERAL_RENDER_GOLDEN.iter().map(|(name, digest)| (name.to_string(), digest.to_string())).collect();
        std::fs::remove_dir_all(&root).ok();
        assert_eq!(digests, expected, "a general-line render without a stage changed");
    }

    /// The loop states the run's timed calls (`general.timed_calls`, the request's `engine.timed_calls`; 3 when absent).
    #[test]
    fn the_loop_states_the_runs_timed_calls() {
        let text = general::the_loop(Shape::OneLine, Workloads::One);
        for (general, expected) in [(json!({}), "1 warm call and 3 hot calls, and the median"), (json!({"timed_calls":5}), "1 warm call and 5 hot calls, and the median"),
            (json!({"timed_calls":1}), "1 warm call and 1 hot call, and the median")] {
            assert!(general_filled(&text, &json!({"general":general})).contains(expected), "{expected}");
        }
    }

    const GENERAL_RENDER_GOLDEN: [(&str, &str); 10] = [
        ("first-call-b1-session-1", "eea806e1a8a48b523f93137f6ed108faa1ff5c622aef671c35c00bfe64184501"),
        ("continued-call-b1-session-1-after-submission-1", "93ae78c7e87fb6aae268a65dcb85c1e341d64f6578f72ea4f4a9b134a9323320"),
        ("fresh-provider-session-b1-session-1-call-2", "3fa6ad1fd61b7cf1f1719beec29f9c3daca7901fb051587568bd37c9a6623863"),
        ("first-call-b1-session-2-fresh", "a52434c227d19e628c7a288fc7d540216a283b8370978042bdcf0377b33e765d"),
        ("one-line-plain-first-call", "419b6c921973f3047a58071175eae6c38d0e69e13d3015b23d5f22beb8b3d57d"),
        ("one-line-plain-continued-call", "54f68b70d45001aa85f692b84d0afd8331e2de580ee6ec5794fe71e8958d4ffc"),
        ("one-line-plain-fresh-session-2", "b52ba5f04ec8b379e4bcf82810b7de33c221eb497d2110127c23eb7407255d62"),
        ("one-line-co_optimization-first-call", "d81887b7fe420819d19f175effd32462818603e6fd75bbea1c06f231e521ad5f"),
        ("one-line-co_optimization-continued-call", "54f68b70d45001aa85f692b84d0afd8331e2de580ee6ec5794fe71e8958d4ffc"),
        ("one-line-co_optimization-fresh-session-2", "a205d47c1602ba3221d695e238210b1032a6f0ae160b3f1d58b78cc4d36f0767"),
    ];

    fn unfilled_placeholder(prompt: &str) -> Option<&str> {
        let placeholder = |line: &str| line.split('@').skip(1).step_by(2).any(|word| !word.is_empty() && word.chars().all(|c| c.is_ascii_uppercase() || c == '_'));
        prompt.lines().find(|l| placeholder(l))
    }

    /// The general prompt: the first call has every section in order, filled, with the facts and the
    /// branch's handoff; a continued call has only the evaluation and the facts that changed; a fresh session has the
    /// full prompt and the branch's previous session.
    #[test]
    fn general_prompts_are_complete_continued_and_fresh() {
        let root = crate::controller::test_support::scratch_root("general-prompts");
        let prompts = general_fixture_prompts(&root);
        let first = &prompts[0].1;
        let order = ["# Key paths and scope", "`<workspace>` (`files.workspace`, your workspace): ", "- in `<workspace>/contract/engine`, the contract directory: `author_contract` index.json",
            "- in `<session>`: `full_context` context.json, `this_prompt` calls/0001/prompt.txt", "- in `<records>`: `findings` FINDINGS.md", "This is session 1 of branch b1 at scale sf1, seeded from v000.",
            "# Goal", "# How to work", "**Freedom.**", "**Sub-agents.**", "# What is fixed", "## The rules of this line", "# Storage", "## Storage policy: physical_only",
            "# Fallback: the verified interpreter", "# Design and proofs", "**Proofs.**", "**Reuse.**", "**Design space map:**", "# The loop", "# Inputs and conduct", "# Tools",
            "**Check economy.**", "# Submission", "# Appendix: processes on a shared host", "# CURRENT FACTS AND PATHS", "## Scale", "## Score at sf1", "## Per template at sf1",
            "## Profile of v000", "## Branches and the version tree", "## Storage at sf1", "## Budget and session", "## Integrity constraints", "## Host",
            "# HANDOFF: YOUR BRANCH SO FAR", "## Notebook carried into this session", "# LEDGER", "# LATEST FEEDBACK"];
        let mut at = 0;
        for heading in order {
            let found = first[at..].find(heading).unwrap_or_else(|| panic!("{heading} missing or out of order"));
            at += found + heading.len();
        }
        assert_eq!(unfilled_placeholder(first), None);
        assert!(first.contains("within the call limit (60 s)") && first.contains("at 60 s of wall time and at 144 GiB of anonymous memory") && first.contains("Up to 3 branches"), "limits and branches filled");
        assert!(first.contains("(kinds: `wrapped_tables`, `commuted_comparisons`)") && first.contains("`direction` (required on your branch's first submission)"));
        assert!(first.contains("- 1 worker: Umbra 340 (the target), DuckDB 452; v000 (main line) 93000, 2/3 finished, ratio 273.529."), "v000 totals at 1 worker");
        assert!(first.contains("Your branch has not stated a direction") && first.contains("This is the branch's first session."));
        assert!(first.contains("Spent so far: $0.00 ($0.00 of it by this session's earlier calls); left: $1000.00.") && first.contains("- Submissions this session: 0 (no limit)."), "{first}");
        // Each path once: the facts name files by their key path or relative to the key paths' directories.
        assert_eq!(first.matches("/engine/TREE.md").count(), 0, "TREE.md is `files.tree`: {first}");
        assert!(first.contains("`NOTES.md` (`files.notes`) as this session started, from `<records>/versions/v000/NOTES.md`:"), "{first}");
        assert!(first.contains("A session ends only at an evaluation, and only when you asked for it") && first.contains("`c2/verus-engine.json` for a manifest in a subfolder") && !first.contains("verus-query.json"));
        for internal in ["root decision", "design 3", "mandate decision"] {
            assert!(!first.contains(internal), "no internal reference: {internal}");
        }
        assert!(!first.contains("Storage budget: none") && !first.contains("- The rule:"), "the library allowance is not shown, and the budget rule is stated once (Storage)");
        assert!(!first.contains("(A fixed entry is") && !first.contains("- Timing:"), "no query-line entries, no timing protocol repeated in the facts");
        assert!(!first.contains("Not the interpreter") && !first.contains("Rounds and versions"), "the schema line's evaluator ban and rounds are not in the general prompt");
        let continued = &prompts[1].1;
        assert!(continued.starts_with("# EVALUATION OF YOUR SUBMISSION"), "{continued}");
        assert!(continued.contains("/branches/b1/sessions/session-0001/calls/0001/prompt.txt"), "names the provider session's full prompt");
        assert!(continued.contains("## Submission 1: accepted as v001 (F 9/9 at sf1, G 41.250)") && continued.contains("- Main line: v001 is now the main-line head"), "{continued}");
        assert!(continued.contains("- Q09: time limit (recorded) / time limit (recorded) / memory limit (recorded) → 9000 / 700 / 650 (- / - / -)"), "{continued}");
        assert!(continued.contains("- Q01: 25000 / 25100 / 25200 → 900 / 60 / 55 (0.036 / 0.002 / 0.002)"), "{continued}");
        assert!(continued.contains("- Records: `files.versions_records`/v001 (version.json, race.json, cells/, variant-answers.json)."), "{continued}");
        assert!(continued.contains("## Profile of v001") && continued.contains("- Towards your last submission: 1 call, 60.0 min of author time, $12.50 provider-reported."), "{continued}");
        assert!(continued.contains("context 180000 tokens at the last turn, 210000 at the peak; 0 automatic compactions"), "{continued}");
        // One budget statement from the real ledger and run spend; no submission limit and no session cost guard.
        assert!(continued.contains("Spent so far: $12.50 ($12.50 of it by this session's earlier calls); left: $987.50.") && continued.contains("- Submissions this session: 1 (no limit)."), "{continued}");
        for misleading in ["Cost guard", " used of ", "left including this call"] {
            assert!(!first.contains(misleading) && !continued.contains(misleading), "{misleading}");
        }
        for absent in ["# Goal", "# How to work", "# Design and proofs", "## Host", "## Integrity constraints", "# HANDOFF"] {
            assert!(!continued.contains(absent), "a continued call does not repeat {absent}");
        }
        assert_eq!(unfilled_placeholder(continued), None);
        let restarted = &prompts[2].1;
        assert!(restarted.contains("# Goal") && restarted.contains("## Submission 1: accepted as v001") && restarted.contains("# HANDOFF FROM EARLIER ATTEMPTS"), "{restarted}");
        assert!(!restarted.contains("# HANDOFF: YOUR BRANCH SO FAR") && restarted.contains("This provider session so far: 1 call;"), "{restarted}");
        let fresh = &prompts[3].1;
        assert!(fresh.contains("# Goal") && fresh.contains("This is session 2 of branch b1 at scale sf1, seeded from v001.") && fresh.contains("Your workspace starts from v001:"), "{fresh}");
        assert!(fresh.contains("- Its last evaluation (submission 3): not accepted, recorded as attempt b1-a002: refusal: schema_name"), "{fresh}");
        assert!(fresh.contains("- The branch's previous session: `<records>/branches/b1/sessions/session-0001`"), "{fresh}");
        assert!(fresh.contains("- Why it ended: provider_compacted"), "{fresh}");
        assert!(fresh.contains("## Tried\n\n- hash join: Q09 finishes."), "the notebook carried verbatim");
        assert_eq!(unfilled_placeholder(fresh), None);
        std::fs::remove_dir_all(&root).ok();
    }

    /// Writes the four general-line renders, the schema line's golden render and the scripted run's output home
    /// (`TREE.md`, `FINDINGS.md`, `PROFILE.md`, per-scale tables, version and attempt folders) under
    /// `GENDB_GENERAL_RENDER_DIR` for review (render-only, no provider).
    #[test]
    #[ignore = "writes the renders under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_general_fixture_renders() {
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        let root = out.join("fixture-run");
        std::fs::create_dir_all(&out).unwrap();
        for (name, prompt) in general_fixture_prompts(&root) {
            std::fs::write(out.join(format!("{name}.md")), &prompt).unwrap();
            println!("{name}: {} lines, {} bytes", prompt.lines().count(), prompt.len());
        }
        std::fs::write(out.join("schema-line-golden-prompt.md"), schema_line_fixture_prompt()).unwrap();
        // The scripted run's output home (TREE.md, FINDINGS.md, PROFILE.md, per-scale tables, version folders).
        let written = crate::output::engine::general::write_general_engine(&out.join("output-home"), &root.join("scripted/run/engine")).unwrap();
        println!("output home: {written}");
    }

    /// The scripted session's context as a one-line run (one branch slot), with the variant kinds the TPC-H training
    /// set has (so the instruction sections are the ones a real one-line run renders).
    fn one_line(mut context: Value) -> Value {
        context["general"]["branches"] = json!([context["general"]["branches"][0].clone()]);
        context["engine"]["training"]["variants"]["kinds"] =
            json!(["always_true_conjunct", "between_expansion", "commuted_comparisons", "conjunct_permutation", "from_permutation", "wrapped_tables"]);
        context
    }

    /// The text of `prompt` without its paths, absolute or under a key-path directory such as `<records>/` (session
    /// directories live under `branches/b1/`).
    fn without_paths(prompt: &str) -> String {
        prompt.split(|c: char| c.is_whitespace() || c == '`').filter(|word| !word.starts_with('/') && !word.starts_with('<')).collect::<Vec<_>>().join(" ")
    }

    /// One line: the first call, a continued call and a fresh session say that each version
    /// builds on the best version, name the head, and say nothing of branches, islands, merges, rebases or the main
    /// line; the goal leads with the fastest verified engine as soon as possible, then work fast and the global view.
    #[test]
    fn one_line_prompts_say_nothing_of_branches() {
        use crate::prompts::engine_facts::general::tests as fixture;
        let root = crate::controller::test_support::scratch_root("general-one-line");
        let run = fixture::version_zero_run(&root.join("scripted"));
        let context = one_line(fixture::session_context(&run, 1));
        let ledger = fixture::ledger_view(&run.session_one);
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &run.session_one.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        let order = ["# Key paths and scope", "This is session 1 at scale sf1, seeded from v000.", "# Goal", "**Build the fastest verified engine, as soon as possible:**", "# How to work",
            "**Global view.**", "**Freedom.**", "**Sub-agents.**", "# What is fixed", "# Storage", "# Fallback: the verified interpreter", "# Design and proofs", "# The loop",
            "**One line of versions.** Each version builds on the best version", "# Inputs and conduct", "# Tools", "# Submission", "# CURRENT FACTS AND PATHS", "## Scale",
            "Head v000 (the best version so far)", "## Score at sf1", "v000 (head) 93000", "## Versions", "1 version and 0 attempts so far", "## Storage at sf1", "- Head v000 serves",
            "## Budget and session", "for every call of the run", "# HANDOFF: YOUR WORK SO FAR", "- This is the first session.", "## Notebook carried into this session", "# LEDGER"];
        let mut at = 0;
        for heading in order {
            let found = first[at..].find(heading).unwrap_or_else(|| panic!("{heading} missing or out of order:\n{first}"));
            at += found + heading.len();
        }
        assert_eq!(unfilled_placeholder(&first), None);
        fixture::first_submission(&run);
        let context = one_line(fixture::session_context(&run, 1));
        let feedback = fixture::feedback_after_first_submission(&run);
        let ledger = fixture::ledger_view(&run.session_one);
        let continued = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &ledger,
            prompt_file: &run.session_one.join("calls/0002/prompt.txt"), handoff: &Value::Null });
        assert!(continued.starts_with("# EVALUATION OF YOUR SUBMISSION"), "{continued}");
        assert!(continued.contains("- Parent v000; interleaved timing at sf1:") && continued.contains("- v001 is now the head, the best version so far; your next submission builds on it."), "{continued}");
        assert!(continued.contains("## Versions") && continued.contains("Last stated direction: vectorized operators"), "{continued}");
        fixture::rest_of_session_one(&run);
        let context = one_line(fixture::session_context(&run, 2));
        let ledger = fixture::ledger_view(&run.session_two);
        let fresh = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &run.session_two.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        assert!(fresh.contains("This is session 2 at scale sf1, seeded from v001.") && fresh.contains("Your workspace starts from v001, the head when this session started") && fresh.contains("- Why it ended: provider_compacted"), "{fresh}");
        for (name, prompt) in [("first", &first), ("continued", &continued), ("fresh", &fresh)] {
            let text = without_paths(prompt);
            let lower = text.to_lowercase();
            for absent in ["branch", "island", "main-line", "main line", "main_line_head", "merge session", "accepted merge", "rebase", "base:"] {
                assert!(!lower.contains(absent), "{name}: {absent}\n{prompt}");
            }
        }
        std::fs::remove_dir_all(&root).ok();
    }

    /// The prompt's first call saved as the transport saves it (`prompt.txt`), with a provider that started (a
    /// non-empty transcript).
    fn sent(session: &Path, call: u64, prompt: &str) {
        let dir = session.join(format!("calls/{call:04}"));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join(crate::controller::layout::PROMPT_FILE), prompt).unwrap();
        std::fs::write(dir.join("stdout.jsonl"), "{\"type\":\"system\",\"subtype\":\"init\"}\n").unwrap();
    }

    /// An older first prompt of the same session: the goal without its first sentence, no How to work section, and a
    /// section the current instructions no longer have.
    fn older_prompt(prompt: &str) -> String {
        let how_to_work = instructions::level_one_sections(prompt).into_iter().find(|s| s.heading == "How to work").unwrap();
        prompt
            .replace("**Build the fastest verified engine, as soon as possible:** ", "")
            .replace(&format!("{}\n\n", how_to_work.text), "")
            .replace("# CURRENT FACTS AND PATHS", "# Retired rule\n\nA rule of an older build.\n\n# CURRENT FACTS AND PATHS")
    }

    /// CHANGED INSTRUCTIONS (task 4): a continued call whose provider session holds the current instructions gets none;
    /// one whose first prompt (sent before instruction records existed) holds older instructions gets the changed and new
    /// sections in full and the removed ones by name, records the new digests, and the call after it gets none.
    #[test]
    fn a_continued_call_gives_the_instructions_changed_since_its_first_prompt() {
        use crate::engine::sessions::{INSTRUCTIONS_FILE, InstructionRecord};
        use crate::prompts::engine_facts::general::tests as fixture;
        let root = crate::controller::test_support::scratch_root("general-changed-instructions");
        let run = fixture::version_zero_run(&root.join("scripted"));
        let session = &run.session_one;
        let context = one_line(fixture::session_context(&run, 1));
        let ledger = fixture::ledger_view(session);
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        sent(session, 1, &first);
        fixture::first_submission(&run);
        let context = one_line(fixture::session_context(&run, 1));
        let feedback = fixture::feedback_after_first_submission(&run);
        let ledger = fixture::ledger_view(session);
        let continued = |call: u64| general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join(format!("calls/{call:04}/prompt.txt")), handoff: &Value::Null });
        let unchanged = continued(2);
        assert!(unchanged.starts_with("# EVALUATION OF YOUR SUBMISSION") && !unchanged.contains("CHANGED INSTRUCTIONS"), "the provider session holds the current instructions");
        // The session's first prompt came from an older build, before the records: GenDB reads it.
        let old = older_prompt(&first);
        sent(session, 1, &old);
        std::fs::remove_file(session.join(INSTRUCTIONS_FILE)).unwrap();
        let changed = continued(2);
        assert!(changed.starts_with("# CHANGED INSTRUCTIONS\n\nGenDB changed the instructions of this run after this provider session's first prompt (`"), "{changed}");
        assert!(changed.contains("The 2 sections below are new or replace the sections of the same name there, in full.") && changed.contains("These sections of the first prompt are removed, and whatever of them still holds is in the sections below: `# Retired rule`."), "{changed}");
        let sections: Vec<String> = instructions::level_one_sections(&changed).into_iter().map(|s| s.heading).collect();
        assert_eq!(sections[..4], ["CHANGED INSTRUCTIONS", "Goal", "How to work", "EVALUATION OF YOUR SUBMISSION"], "the changed sections in prompt order, then the evaluation");
        let current = instructions::instruction_sections(&first);
        for heading in ["Goal", "How to work"] {
            let section = current.iter().find(|s| s.heading == heading).unwrap();
            assert!(changed.contains(&format!("{}\n\n", section.text)), "{heading} in full");
        }
        assert!(changed.contains("(End of the changed instructions.)\n\n# EVALUATION OF YOUR SUBMISSION\n\nThis session continues. The paths of this provider session's first prompt hold"), "{changed}");
        // The record of what the provider session now holds: the current digests.
        let records: Vec<InstructionRecord> = crate::engine::tree::read_lines(&session.join(INSTRUCTIONS_FILE)).unwrap().into_iter().map(|l| serde_json::from_value(l).unwrap()).collect();
        assert_eq!(records.len(), 1);
        assert_eq!((records[0].call, records[0].sent), (2, crate::engine::sessions::InstructionsSent::Changed));
        assert_eq!(records[0].sections, current.iter().map(Section::digest).collect::<Vec<_>>());
        // Sent, the change is held: the next continued call of the provider session gets no section again.
        sent(session, 2, &changed);
        fixture::rest_of_session_one(&run);
        let ledger = fixture::ledger_view(session);
        let next = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 4, submission: 4, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0004/prompt.txt"), handoff: &Value::Null });
        assert!(next.starts_with("# EVALUATION OF YOUR SUBMISSION"), "{next}");
        // A changed prompt that was rendered but never sent holds nothing: the change is given again.
        std::fs::remove_file(session.join("calls/0002/stdout.jsonl")).unwrap();
        let again = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 4, submission: 4, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0004/prompt.txt"), handoff: &Value::Null });
        assert!(again.starts_with("# CHANGED INSTRUCTIONS"), "{again}");
        std::fs::remove_dir_all(&root).ok();
    }

    /// The run operator's note heads the branch's next call, once; the instruction record of that call
    /// digests the prompt it sent (the note included) and never counts the note as an instruction section, so the
    /// continued call after it gets neither the note again nor CHANGED INSTRUCTIONS.
    #[test]
    fn an_operator_note_heads_the_next_call_once() {
        use crate::prompts::engine_facts::general::tests as fixture;
        let root = crate::controller::test_support::scratch_root("general-operator-note");
        let run = fixture::version_zero_run(&root.join("scripted"));
        let session = &run.session_one;
        let engine = session.ancestors().nth(4).unwrap().to_path_buf();
        assert_eq!(engine, run.engine_dir);
        std::fs::create_dir_all(session).unwrap();
        crate::engine::operator_note::write_note(&engine, "b1", "The host was busy during your last timing.", "operator").unwrap();
        let context = one_line(fixture::session_context(&run, 1));
        let ledger = fixture::ledger_view(session);
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        assert!(first.starts_with("# NOTE FROM THE RUN'S OPERATOR\n\n> The host was busy during your last timing.\n\n# Key paths and scope\n"), "{first}");
        assert_eq!(instructions::instruction_sections(&first), instructions::instruction_sections(&first.replacen("# NOTE FROM THE RUN'S OPERATOR\n\n> The host was busy during your last timing.\n\n", "", 1)));
        sent(session, 1, &first);
        fixture::first_submission(&run);
        let context = one_line(fixture::session_context(&run, 1));
        let feedback = fixture::feedback_after_first_submission(&run);
        let ledger = fixture::ledger_view(session);
        let continued = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0002/prompt.txt"), handoff: &Value::Null });
        assert!(continued.starts_with("# EVALUATION OF YOUR SUBMISSION"), "shown once, and no CHANGED INSTRUCTIONS:\n{continued}");
        std::fs::remove_dir_all(&root).ok();
    }

    /// A scripted one-line session whose first call (sent, as the transport saves it) was stopped from outside and whose
    /// retry, call 2, resumes the same provider session (`fixture::stopped_call_and_retry`), with `note` from the run's
    /// operator pending when given: the run and the first call's prompt. [`resumed_prompt`] renders call 2's prompt.
    fn stopped_session(root: &Path, note: Option<&str>) -> (crate::prompts::engine_facts::general::tests::ScriptedRun, String) {
        use crate::prompts::engine_facts::general::tests as fixture;
        let run = fixture::version_zero_run(&root.join("scripted"));
        let session = run.session_one.clone();
        let context = one_line(fixture::session_context(&run, 1));
        let ledger = fixture::ledger_view(&session);
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        sent(&session, 1, &first);
        assert_eq!(fixture::stopped_call_and_retry(&session), (1, 2));
        if let Some(note) = note {
            crate::engine::operator_note::write_note(&run.engine_dir, "b1", note, "operator").unwrap();
        }
        (run, first)
    }

    /// Call 2's prompt in a [`stopped_session`]: the stopped call's event is the latest feedback.
    fn resumed_prompt(run: &crate::prompts::engine_facts::general::tests::ScriptedRun) -> String {
        use crate::prompts::engine_facts::general::tests as fixture;
        let session = &run.session_one;
        let context = one_line(fixture::session_context(run, 1));
        let feedback = vec![json!({"call":1,"iteration":1,"attempt":1,"author_outcome":fixture::STOPPED_OUTCOME,"provider_reported_cost_usd":"255.63"})];
        let ledger = fixture::ledger_view_of(session, 2);
        general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0002/prompt.txt"), handoff: &Value::Null })
    }

    /// A call that resumes its provider session after a stopped call gets a short message (that the call was
    /// stopped and submitted nothing, that the context is kept, then the facts now with the evaluation time and the
    /// provider session's context, the ledger and the stopped call), led by the operator's note when there is one and by
    /// CHANGED INSTRUCTIONS when the sections changed. Without the recovery record, or after a compaction of the provider
    /// session's context, it gets the full prompt as before.
    #[test]
    fn a_call_resumed_after_a_stop_gets_a_short_message() {
        use crate::engine::sessions::{INSTRUCTIONS_FILE, InstructionRecord};
        let root = crate::controller::test_support::scratch_root("general-resumed-after-stop");
        let (run, first) = stopped_session(&root.join("plain"), None);
        let session = &run.session_one;
        let resumed = resumed_prompt(&run);
        let first_prompt = session.join("calls/0001/prompt.txt");
        assert!(resumed.starts_with(&format!("{}\n\nYour previous call (call 1) was stopped before it ended, by the run's operator or a stop of GenDB's controller; it submitted nothing. This call resumes the same provider session: your context is kept, and the goal, the rules and the paths of this provider session's first prompt hold unchanged (`{}`).",
            general::RESUMED_AFTER_STOP_HEADING, first_prompt.display())), "{resumed}");
        let order = ["# YOUR PREVIOUS CALL WAS STOPPED", "# CURRENT FACTS AND PATHS", "## Scale", "Evaluation time at sf1: no evaluation has been timed here yet.", "## Score at sf1", "## Versions",
            "## Storage at sf1", "## Budget and session", "- This provider session so far: 1 call; context 0 tokens at the last turn, 0 at the peak; 0 automatic compactions.", "# LEDGER",
            "# LATEST FEEDBACK", "## Latest call: call 1, ended without a submission: controller_loss_recovery: provider_error"];
        let mut at = 0;
        for heading in order {
            let found = resumed[at..].find(heading).unwrap_or_else(|| panic!("{heading} missing or out of order:\n{resumed}"));
            at += found + heading.len();
        }
        for absent in ["# Key paths and scope", "# Goal", "# How to work", "# HANDOFF", "## Per template", "## Profile of", "## Integrity constraints", "## Host", "CHANGED INSTRUCTIONS", "# EVALUATION OF YOUR SUBMISSION"] {
            assert!(!resumed.contains(absent), "the provider session holds {absent}:\n{resumed}");
        }
        assert_eq!(unfilled_placeholder(&resumed), None);
        assert!(resumed.split_whitespace().count() * 5 < first.split_whitespace().count(), "short: {} words against the first prompt's {}", resumed.split_whitespace().count(), first.split_whitespace().count());
        let records: Vec<InstructionRecord> = crate::engine::tree::read_lines(&session.join(INSTRUCTIONS_FILE)).unwrap().into_iter().map(|l| serde_json::from_value(l).unwrap()).collect();
        assert!(records.iter().all(|r| r.call == 1), "nothing new is sent, nothing recorded for call 2");
        // After a compaction of the provider session's context, the full prompt as before.
        let transcript = session.join("calls/0001/stdout.jsonl");
        let mut text = std::fs::read_to_string(&transcript).unwrap();
        text.push_str("{\"type\":\"system\",\"subtype\":\"compact_boundary\",\"compact_metadata\":{\"trigger\":\"auto\",\"pre_tokens\":970453,\"post_tokens\":12517}}\n");
        std::fs::write(&transcript, text).unwrap();
        assert!(resumed_prompt(&run).starts_with("# Key paths and scope"), "compacted: the full prompt");
        // A retry without the recovery record (not a stop): the full prompt as before.
        let (run, _) = stopped_session(&root.join("not-stopped"), None);
        std::fs::remove_file(run.session_one.join("calls/0001").join(CONTROLLER_LOSS_RECOVERY_FILE)).unwrap();
        assert!(resumed_prompt(&run).starts_with("# Key paths and scope"), "no stop: the full prompt");
        // The operator's note leads the message.
        let (run, _) = stopped_session(&root.join("note"), Some("The run's operator stopped your last call to give you facts you did not have."));
        let with_note = resumed_prompt(&run);
        assert!(with_note.starts_with("# NOTE FROM THE RUN'S OPERATOR\n\n> The run's operator stopped your last call to give you facts you did not have.\n\n# YOUR PREVIOUS CALL WAS STOPPED\n\n"), "{with_note}");
        // The provider session's first prompt came from an older build: the changed sections lead, and are recorded.
        let (run, first) = stopped_session(&root.join("changed"), None);
        let session = &run.session_one;
        sent(session, 1, &older_prompt(&first));
        std::fs::remove_file(session.join(INSTRUCTIONS_FILE)).unwrap();
        let changed = resumed_prompt(&run);
        assert!(changed.starts_with("# CHANGED INSTRUCTIONS\n\n") && changed.contains("(End of the changed instructions.)\n\n# YOUR PREVIOUS CALL WAS STOPPED\n\n"), "{changed}");
        assert!(changed.contains("its instructions hold with the changes above (CHANGED INSTRUCTIONS)"), "{changed}");
        let records: Vec<InstructionRecord> = crate::engine::tree::read_lines(&session.join(INSTRUCTIONS_FILE)).unwrap().into_iter().map(|l| serde_json::from_value(l).unwrap()).collect();
        assert_eq!(records.iter().map(|r| (r.call, r.sent)).collect::<Vec<_>>(), [(2, InstructionsSent::Changed)]);
        std::fs::remove_dir_all(&root).ok();
    }

    /// Writes the call that resumes its provider session after a stopped call (the render: the scripted
    /// one-line fixture, no provider), plain and with an operator's note, under `GENDB_GENERAL_RENDER_DIR` for review.
    #[test]
    #[ignore = "writes the renders under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_resumed_after_stop_renders() {
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        std::fs::create_dir_all(&out).unwrap();
        for (name, note) in [("one-line-resumed-after-stop", None), ("one-line-resumed-after-stop-with-note", Some("The run's operator stopped your last call to give you facts you did not have."))] {
            let root = out.join(format!("fixture-run-{name}"));
            std::fs::remove_dir_all(&root).ok();
            let (run, _) = stopped_session(&root, note);
            let prompt = resumed_prompt(&run);
            std::fs::write(out.join(format!("{name}.md")), &prompt).unwrap();
            println!("{name}: {} lines, {} words, {} bytes", prompt.lines().count(), prompt.split_whitespace().count(), prompt.len());
        }
    }

    /// Writes the continued call of a scripted one-line session whose provider session's first prompt is the prompt at
    /// `GENDB_OLD_FIRST_PROMPT` (the live run's first prompt, from an older build), and the one-line first call, under
    /// `GENDB_GENERAL_RENDER_DIR` (render-only, no provider).
    #[test]
    #[ignore = "writes the renders under GENDB_GENERAL_RENDER_DIR for review; reads GENDB_OLD_FIRST_PROMPT"]
    fn write_changed_instructions_render() {
        use crate::prompts::engine_facts::general::tests as fixture;
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        let old = std::fs::read_to_string(std::env::var("GENDB_OLD_FIRST_PROMPT").expect("GENDB_OLD_FIRST_PROMPT")).unwrap();
        std::fs::create_dir_all(&out).unwrap();
        let run = fixture::version_zero_run(&out.join("fixture-run"));
        let session = &run.session_one;
        let context = one_line(fixture::session_context(&run, 1));
        let ledger = fixture::ledger_view(session);
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        std::fs::write(out.join("one-line-first-call.md"), &first).unwrap();
        // The provider session's first prompt was sent by the older build (no instruction record).
        sent(session, 1, &old);
        std::fs::remove_file(session.join(crate::engine::sessions::INSTRUCTIONS_FILE)).ok();
        fixture::first_submission(&run);
        let context = one_line(fixture::session_context(&run, 1));
        let feedback = fixture::feedback_after_first_submission(&run);
        let ledger = fixture::ledger_view(session);
        let continued = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0002/prompt.txt"), handoff: &Value::Null });
        std::fs::write(out.join("continued-call-with-changed-instructions.md"), &continued).unwrap();
        let held = instructions::instruction_sections(&old);
        let current = instructions::level_one_sections(&general_instructions(&context));
        let changes = instructions::changes(&held.iter().map(Section::digest).collect::<Vec<_>>(), &current);
        println!("old first prompt: {} instruction sections; current: {}; changed or new: {:?}; removed: {:?}", held.len(), current.len(),
            changes.changed.iter().map(|s| s.heading.as_str()).collect::<Vec<_>>(), changes.removed);
        println!("one-line-first-call.md: {} lines; continued-call-with-changed-instructions.md: {} lines", first.lines().count(), continued.lines().count());
        assert!(continued.starts_with("# CHANGED INSTRUCTIONS"));
    }

    /// A general-line context with only what the instruction sections read: `branches` branch slots, the run's limits,
    /// the TPC-H training set's variant kinds, and the request's `engine.emphasis` when set (`None`: absent).
    fn instructions_context(branches: usize, emphasis: Option<&str>) -> Value {
        let slots: Vec<Value> = (1..=branches).map(|b| json!({"branch":format!("b{b}")})).collect();
        let mut context = json!({"general":{"branches":slots,"limits":{"call_limit_seconds":60,"anon_memory_limit_bytes":154_618_822_656u64}},
            "engine":{"training":{"variants":{"kinds":["always_true_conjunct", "between_expansion", "commuted_comparisons", "conjunct_permutation", "from_permutation", "wrapped_tables"]}}}});
        if let Some(emphasis) = emphasis {
            context["general"]["emphasis"] = json!(emphasis);
        }
        context
    }

    /// The "Main direction" section is present only
    /// when the request sets `engine.emphasis: "co_optimization"`, right after the goal, in both shapes; it says what
    /// the emphasis asks, and nothing of how to split the work across sub-agents; an absent or
    /// unknown value adds nothing; and the emphasis changes no other section, so a continued call of either kind of run
    /// compares the same sections.
    #[test]
    fn the_main_direction_appears_only_with_the_emphasis() {
        const HEADING: &str = "Main direction: data and query co-optimization";
        for branches in [1, 3] {
            let plain = instructions::level_one_sections(&general_instructions(&instructions_context(branches, None)));
            let with = instructions::level_one_sections(&general_instructions(&instructions_context(branches, Some("co_optimization"))));
            let unknown = instructions::level_one_sections(&general_instructions(&instructions_context(branches, Some("something_else"))));
            assert!(plain.iter().chain(&unknown).all(|s| s.heading != HEADING), "no main direction without the emphasis ({branches} branch slots)");
            assert_eq!(unknown, plain, "an unknown emphasis adds nothing");
            let headings: Vec<&str> = with.iter().map(|s| s.heading.as_str()).collect();
            assert_eq!(headings[..3], ["Goal", HEADING, "How to work"], "{branches} branch slots");
            assert_eq!(with.iter().filter(|s| s.heading == HEADING).count(), 1);
            let others: Vec<&Section> = with.iter().filter(|s| s.heading != HEADING).collect();
            assert_eq!(others, plain.iter().collect::<Vec<_>>(), "every other section is the same ({branches} branch slots)");
            let section = &with[1].text;
            for said in ["This run makes data and query co-optimization (Storage) the main direction, from the first version.",
                "the goal, the rules, the storage policy and the loop are unchanged",
                "the storage layout, the column access layer and the operators as one design.",
                "(narrow integers, dictionary codes for text, compact offsets), the sort order, the clustering and the skipping metadata together with the algorithms that read them",
                "**Build the access layer for encoded columns from the start.** Your operators then work on the encoded data, not on a plain copy of it",
                "**The first storage change must compress** (the budget, Storage). Re-encoding the largest table alone can be enough."] {
                assert!(section.contains(said), "{said}\n{section}");
            }
            // The section prescribes no split across sub-agents (the lead sizes each task, How to work).
            assert!(section.trim_end().ends_with("Re-encoding the largest table alone can be enough.") && !section.contains("sub-agent"), "{section}");
            assert_eq!(unfilled_placeholder(section), None);
            // What the section relies on is stated in Storage, in both modes.
            let storage = &with.iter().find(|s| s.heading == "Storage").unwrap().text;
            for relied in ["The plain storage is about 1.4 times the original size", "only the space saved can hold indexes, skipping metadata and other structures",
                "At each new scale GenDB builds your storages again with the same verified builders"] {
                assert!(storage.contains(relied), "{relied}");
            }
        }
    }

    /// A continued run (the context's `general.seed`): the section "A continued engine" comes right
    /// after the goal (before the main direction), names the seed version, its run by the directory's name only (other
    /// runs are not inputs), the templates the seed was built for and the new ones, and the user's keep rule; every other
    /// section is unchanged, and without a seed the section is absent.
    #[test]
    fn a_continued_run_names_its_seed_and_its_new_templates() {
        const HEADING: &str = "A continued engine";
        let plain = instructions::level_one_sections(&general_instructions(&instructions_context(1, Some("co_optimization"))));
        assert!(plain.iter().all(|s| s.heading != HEADING), "no continued-engine section without a seed");
        let mut context = instructions_context(1, Some("co_optimization"));
        context["general"]["seed"] = json!({"run":"/runs/seed-runs/general/general-engine","version":"v016","seed_templates":["Q01","Q02"],"new_templates":["U07"]});
        let with = instructions::level_one_sections(&general_instructions(&context));
        let headings: Vec<&str> = with.iter().map(|s| s.heading.as_str()).collect();
        assert_eq!(headings[..3], ["Goal", HEADING, "Main direction: data and query co-optimization"]);
        // Every other section is the same, but the fallback's sentence about version 0 (this run's root is the seed).
        const FALLBACK: &str = "Fallback: the verified interpreter";
        let others = |sections: &[Section]| -> Vec<Section> { sections.iter().filter(|s| s.heading != HEADING && s.heading != FALLBACK).cloned().collect() };
        assert_eq!(others(&with), others(&plain), "every other section is the same");
        let fallback = |sections: &[Section]| sections.iter().find(|s| s.heading == FALLBACK).unwrap().text.clone();
        assert!(fallback(&plain).contains("Version 0 is exactly this (`files.versions_records`/v000/code); its proof"));
        assert!(fallback(&with).contains("GenDB's version 0 of a run (the interpreter engine; this run's root is a seed version instead) is exactly this; its proof"));
        let section = &with[1].text;
        for said in ["Its root `v000` is version `v016` of the run `general-engine`", "(the earlier run's records are not inputs)",
            "**Built for:** 2 templates (`Q01`, `Q02`). **New to it:** 1 template (`U07`).", "this run starts and stays at the last scale of its ladder",
            "the user asks that the engine not lose its performance on the templates it was built for", "DuckDB's total is the target at every worker count"] {
            assert!(section.contains(said), "{said}\n{section}");
        }
        assert!(!section.contains("/runs/seed-runs"), "no path of the seed run: {section}");
        assert_eq!(unfilled_placeholder(section), None);
    }

    /// The scripted one-line session of a run with `engine.emphasis: "co_optimization"`: its first call (sent, as the
    /// transport saves it) and, after its first accepted submission, the call that continues the provider session.
    fn co_optimization_prompts(root: &Path) -> (String, String) {
        use crate::prompts::engine_facts::general::tests as fixture;
        let run = fixture::version_zero_run(&root.join("scripted"));
        let session = &run.session_one;
        let emphasized = |mut context: Value| {
            context["general"]["emphasis"] = json!("co_optimization");
            context
        };
        let context = emphasized(one_line(fixture::session_context(&run, 1)));
        let ledger = fixture::ledger_view(session);
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        sent(session, 1, &first);
        fixture::first_submission(&run);
        let context = emphasized(one_line(fixture::session_context(&run, 1)));
        let feedback = fixture::feedback_after_first_submission(&run);
        let ledger = fixture::ledger_view(session);
        let continued = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0002/prompt.txt"), handoff: &Value::Null });
        (first, continued)
    }

    /// A co-optimization run: the first call has the section after the goal and nothing of branches; the
    /// continued call gets no CHANGED INSTRUCTIONS, because its provider session holds the same sections.
    #[test]
    fn a_co_optimization_run_continues_without_changed_instructions() {
        let root = crate::controller::test_support::scratch_root("general-co-optimization");
        let (first, continued) = co_optimization_prompts(&root);
        let order = ["# Key paths and scope", "This is session 1 at scale sf1, seeded from v000.", "# Goal", "# Main direction: data and query co-optimization", "# How to work",
            "# What is fixed", "# Storage", "# Fallback: the verified interpreter", "# Design and proofs", "# The loop", "# CURRENT FACTS AND PATHS"];
        let mut at = 0;
        for heading in order {
            let found = first[at..].find(heading).unwrap_or_else(|| panic!("{heading} missing or out of order:\n{first}"));
            at += found + heading.len();
        }
        assert_eq!(unfilled_placeholder(&first), None);
        assert!(!without_paths(&first).to_lowercase().contains("branch"), "one line: nothing of branches");
        assert!(continued.starts_with("# EVALUATION OF YOUR SUBMISSION") && !continued.contains("CHANGED INSTRUCTIONS") && !continued.contains("# Main direction"), "{continued}");
        std::fs::remove_dir_all(&root).ok();
    }

    /// Writes the co-optimization run's first call and continued call (the render: the scripted fixture, no
    /// provider) under `GENDB_GENERAL_RENDER_DIR` for review.
    #[test]
    #[ignore = "writes the renders under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_co_optimization_render() {
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        std::fs::create_dir_all(&out).unwrap();
        let (first, continued) = co_optimization_prompts(&out.join("fixture-run"));
        for (name, prompt) in [("co-optimization-first-call", &first), ("co-optimization-continued-call", &continued)] {
            std::fs::write(out.join(format!("{name}.md")), prompt).unwrap();
            println!("{name}: {} lines, {} bytes, sha256 {}", prompt.lines().count(), prompt.len(), sha256_hex(prompt));
        }
    }

    /// The scripted one-line session of a run with `emphasis` (`engine.emphasis`, or none): its first call (sent, as the
    /// transport saves it), the call that continues the provider session after its first accepted submission, and the
    /// first call of the fresh second session. `(name, prompt)`.
    fn one_line_session_prompts(root: &Path, emphasis: Option<&str>) -> Vec<(String, String)> {
        use crate::prompts::engine_facts::general::tests as fixture;
        let run = fixture::version_zero_run(&root.join("scripted"));
        let session = &run.session_one;
        let mode = emphasis.unwrap_or("plain");
        let context_of = |session_number: u32| {
            let mut context = one_line(fixture::session_context(&run, session_number));
            if let Some(emphasis) = emphasis {
                context["general"]["emphasis"] = json!(emphasis);
            }
            context
        };
        let context = context_of(1);
        let ledger = fixture::ledger_view(session);
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        sent(session, 1, &first);
        fixture::first_submission(&run);
        let context = context_of(1);
        let feedback = fixture::feedback_after_first_submission(&run);
        let ledger = fixture::ledger_view(session);
        let continued = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0002/prompt.txt"), handoff: &Value::Null });
        fixture::rest_of_session_one(&run);
        let context = context_of(2);
        let ledger = fixture::ledger_view(&run.session_two);
        let fresh = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &run.session_two.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        vec![(format!("one-line-{mode}-first-call"), first), (format!("one-line-{mode}-continued-call"), continued), (format!("one-line-{mode}-fresh-session-2"), fresh)]
    }

    /// Writes the first call and the continued call of a real session's prepared context (`GENDB_REAL_SESSION`: a
    /// session directory with `context.json` and `ledger.json`, read only) under `GENDB_GENERAL_RENDER_DIR`, as `real-*`
    /// (word counts at a real scale). The prompts are saved, and their instruction records written, under the
    /// render directory only; the run's records are read, never written. A session whose first call has not submitted
    /// yet gets the first call only (a live session).
    #[test]
    #[ignore = "writes the renders under GENDB_GENERAL_RENDER_DIR; reads GENDB_REAL_SESSION"]
    fn write_real_context_renders() {
        use crate::controller::ledger::LedgerState;
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        let real = std::path::PathBuf::from(std::env::var("GENDB_REAL_SESSION").expect("GENDB_REAL_SESSION"));
        let context: Value = serde_json::from_str(&std::fs::read_to_string(real.join("context.json")).unwrap()).unwrap();
        let state: LedgerState = serde_json::from_str(&std::fs::read_to_string(real.join("ledger.json")).unwrap()).unwrap();
        let session = out.join("real-session");
        std::fs::remove_dir_all(&session).ok();
        std::fs::create_dir_all(&session).unwrap();
        let ledger = json!({"spent_usd":"0","spent_complete":true,"file":real.join("ledger.json"),"submissions":{"used":0,"not_counted_framework_failures":[]},
            "runs_without_candidate":[],"this_call":{"call":1,"iteration":1,"attempt":1}});
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        sent(&session, 1, &first);
        std::fs::write(out.join("real-first-call.md"), &first).unwrap();
        println!("real-first-call: {} lines, {} words, {} bytes", first.lines().count(), first.split_whitespace().count(), first.len());
        // A session without an evaluated submission yet (its first call still running) has no continued call to render.
        let Some(trial) = state.trials.iter().find(|t| !t.evaluation.is_null()) else { return };
        let feedback = vec![json!({"call":trial.call_id,"iteration":trial.iteration,"attempt":1,"author_outcome":"success"}),
            json!({"iteration":trial.iteration,"call_id":trial.call_id,"candidate":trial.candidate,"status":"evaluated","evaluation":trial.evaluation,
                "framework_elapsed_ms":trial.framework_elapsed_ms,"directory":real.join(format!("iterations/{:04}", trial.iteration))})];
        let ledger = json!({"spent_usd":"0","spent_complete":true,"file":real.join("ledger.json"),"submissions":{"used":1,"not_counted_framework_failures":[]},
            "runs_without_candidate":[],"this_call":{"call":2,"iteration":2,"attempt":1}});
        let continued = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &ledger,
            prompt_file: &session.join("calls/0002/prompt.txt"), handoff: &Value::Null });
        std::fs::write(out.join("real-continued-call.md"), &continued).unwrap();
        println!("real-continued-call: {} lines, {} words, {} bytes", continued.lines().count(), continued.split_whitespace().count(), continued.len());
        assert!(continued.starts_with("# EVALUATION OF YOUR SUBMISSION"), "the provider session holds the current instructions");
    }

    /// Writes the call that resumes a real session's provider session after its running call is stopped
    /// (`GENDB_REAL_SESSION`, read only) under `GENDB_GENERAL_RENDER_DIR` as `real-resumed-after-stop.md` (a
    /// live run's next call after a relaunch with a new build). A scratch copy of the session's ledger, context, instruction
    /// record and calls' prompts and transcripts is settled as a relaunch settles a stopped call (its receipt rebuilt
    /// without output; its cost here is the provider session's total of the previous receipt, while a relaunch reads it
    /// from the CLI's terminal result), and the retry is begun; the feedback is the session's trials, as a relaunched
    /// controller starts its search with them. The prepared context is the session's first one (a relaunch prepares it
    /// again with the new build).
    #[test]
    #[ignore = "writes the render under GENDB_GENERAL_RENDER_DIR; reads GENDB_REAL_SESSION"]
    fn write_real_resumed_after_stop_render() {
        use crate::controller::ledger::{Ledger, Receipt, UsageScope};
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        let real = std::path::PathBuf::from(std::env::var("GENDB_REAL_SESSION").expect("GENDB_REAL_SESSION"));
        let session = out.join("real-resumed-session");
        std::fs::remove_dir_all(&session).ok();
        std::fs::create_dir_all(&session).unwrap();
        for file in ["context.json", "ledger.json", "instructions.jsonl"] {
            std::fs::copy(real.join(file), session.join(file)).unwrap();
        }
        let recorded: LedgerState = records::read_json(&session.join("ledger.json")).unwrap();
        let (real_layout, layout) = (RunLayout::new(&real), RunLayout::new(&session));
        for call in &recorded.calls {
            std::fs::create_dir_all(layout.call(call.id)).unwrap();
            for file in [crate::controller::layout::PROMPT_FILE, "stdout.jsonl"] {
                std::fs::copy(real_layout.call(call.id).join(file), layout.call(call.id).join(file)).unwrap();
            }
        }
        let mut ledger = Ledger::open(&session, recorded.request.clone(), recorded.limits.clone()).unwrap();
        let stopped = ledger.state.calls.last().cloned().expect("a call");
        assert!(stopped.receipt.is_none(), "the session's latest call is running (this render stops it)");
        let provider_session = ledger.state.provider_session_of(&stopped).to_string();
        let now = records::now_unix_ms();
        // The provider session's total so far stands in for the stopped call's terminal total (session-scoped receipts).
        let session_total = ledger.state.calls.iter().filter_map(|call| call.receipt.as_ref()?.reported_cost_usd).last();
        ledger
            .settle(Receipt { call_id: stopped.id, session_id: provider_session.clone(), ended_unix_ms: now, elapsed_ms: now.saturating_sub(stopped.started_unix_ms),
                reported_cost_usd: session_total, billed_cost_usd: None, tokens: None, outcome: crate::prompts::engine_facts::general::tests::STOPPED_OUTCOME.into(),
                raw_result: None, output: None, usage_scope: Some(UsageScope::Session) })
            .unwrap();
        std::fs::write(layout.call(stopped.id).join(CONTROLLER_LOSS_RECOVERY_FILE),
            json!({"format_version":1,"kind":"controller_loss_receipt_recovery","call_id":stopped.id,"session_id":provider_session,"output_accepted":false}).to_string()).unwrap();
        let retry = ledger.begin_call().unwrap();
        let retry = ledger.assign_provider_session(retry.id, |_| true).unwrap();
        assert!(retry.resumes_provider_session, "the retry resumes the stopped call's provider session");
        let feedback: Vec<Value> = ledger.state.competing_trials().iter().map(|trial| json!(trial)).collect();
        let context: Value = records::read_json(&session.join("context.json")).unwrap();
        let view = ledger.author_view(retry.id).unwrap();
        let prompt = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: retry.iteration, submission: ledger.state.counted_submissions() + 1,
            limits: &recorded.limits, ledger: &view, prompt_file: &layout.prompt(retry.id), handoff: &Value::Null });
        std::fs::write(out.join("real-resumed-after-stop.md"), &prompt).unwrap();
        let headings: Vec<&str> = prompt.lines().filter(|line| line.starts_with("# ")).collect();
        println!("real-resumed-after-stop (call {} stopped, call {} resumes): {} lines, {} words, {} bytes; level-one headings {headings:?}",
            stopped.id, retry.id, prompt.lines().count(), prompt.split_whitespace().count(), prompt.len());
    }

    /// Writes the one-line renders of both modes (no emphasis, and `co_optimization`) under `GENDB_GENERAL_RENDER_DIR`
    /// (word counts: the scripted fixture, no provider).
    #[test]
    #[ignore = "writes the renders under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_one_line_renders() {
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        std::fs::create_dir_all(&out).unwrap();
        for emphasis in [None, Some("co_optimization")] {
            let root = out.join(format!("fixture-run-{}", emphasis.unwrap_or("plain")));
            std::fs::remove_dir_all(&root).ok();
            for (name, prompt) in one_line_session_prompts(&root, emphasis) {
                std::fs::write(out.join(format!("{name}.md")), &prompt).unwrap();
                println!("{name}: {} lines, {} words, {} bytes", prompt.lines().count(), prompt.split_whitespace().count(), prompt.len());
            }
        }
    }

    /// The scripted stage run's renders: session 1's first call (both
    /// workloads' head `v000`) and, after its first submission was accepted as `v001`, the call that continues the
    /// provider session. `(name, prompt)`.
    pub(crate) fn stage_prompts(root: &Path) -> Vec<(&'static str, String)> {
        use crate::prompts::engine_facts::general::tests::stage_run::*;
        let run = stage_run(root);
        let session = run.session_one.clone();
        let context = stage_context(&run, false);
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &stage_ledger_view(&run),
            prompt_file: &session.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        sent(&session, 1, &first);
        stage_first_submission(&run);
        let context = stage_context(&run, true);
        let feedback = stage_feedback_after_first_submission(&run);
        let continued = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &stage_ledger_view(&run),
            prompt_file: &session.join("calls/0002/prompt.txt"), handoff: &Value::Null });
        vec![("stage-first-call-session-1", first), ("stage-continued-call-after-submission-1", continued)]
    }

    /// A stage run's prompt: the first call has the Stage 2 section after the goal and the
    /// main direction, the stage forms of the goal, what is fixed and the loop, the workloads named (no placeholder left),
    /// the key paths of every workload's files and the stage facts; the continued call after an accepted submission has
    /// the kept workload's evaluation and race, and the workloads' lines, and gets no CHANGED INSTRUCTIONS.
    #[test]
    fn a_stage_run_prompt_names_its_workloads_and_shows_their_facts() {
        let root = crate::controller::test_support::scratch_root("general-stage-prompt");
        let prompts = stage_prompts(&root);
        let first = &prompts[0].1;
        let order = ["# Key paths and scope", "`workloads.sec.templates` workloads/sec/templates.md", "`workloads.tpch.baselines` workloads/tpch/baselines.json",
            "This is session 1 at scale sf3 of the goal workload `sec`, seeded from v000.", "# Goal", "on the training templates of the goal workload `sec` at every worker count",
            "# Main direction: data and query co-optimization", "# Stage 2: a second workload", "The version it starts from was built for `tpch`; the same engine now also serves `sec`.",
            "**The goal: make the same engine fast on `sec`.**", "**Keep `tpch`.**", "# How to work", "# What is fixed", "`workloads/<name>/**` (each workload's module, Stage 2)",
            "8. **Workload modules process no queries**", "# Storage", "# The loop", "1. freeze of every workload's crate", "# Submission", "# CURRENT FACTS AND PATHS", "## Scale", "## Score at sf3",
            "## Per template at sf3", "## Workloads", "## Out of the box: the seed on `sec`", "## Kept workload `tpch` at sf100", "## Versions", "## Storage at sf3", "## Budget and session",
            "## Integrity constraints", "- sub: PRIMARY KEY (adsh)", "# HANDOFF: YOUR WORK SO FAR", "# LEDGER"];
        let mut at = 0;
        for heading in order {
            let found = first[at..].find(heading).unwrap_or_else(|| panic!("{heading} missing or out of order:\n{first}"));
            at += found + heading.len();
        }
        assert_eq!(unfilled_placeholder(first), None);
        assert!(!without_paths(first).to_lowercase().contains("branch"), "one line: nothing of branches");
        let continued = &prompts[1].1;
        assert!(continued.starts_with("# EVALUATION OF YOUR SUBMISSION") && !continued.contains("CHANGED INSTRUCTIONS"), "{continued}");
        for said in ["## Submission 1: accepted as v001", "- Kept workload `tpch`: verified, its storages checked, and timed against the parent's `tpch` side at sf100 (recorded, not deciding)",
            "## Interleaved timing per template on `tpch` at sf100 (recorded, not deciding)", "## Workloads", "- `tpch` (kept) at sf100: head v001, F 12/12 finished, G 2.314."] {
            assert!(continued.contains(said), "{said}\n{continued}");
        }
        assert_eq!(unfilled_placeholder(continued), None);
        std::fs::remove_dir_all(&root).ok();
    }

    /// Writes the stage run's renders (the scripted stage run, no provider) under `GENDB_GENERAL_RENDER_DIR` for
    /// review.
    #[test]
    #[ignore = "writes the renders under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_stage_renders() {
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        let root = out.join("fixture-run-stage");
        std::fs::remove_dir_all(&root).ok();
        std::fs::create_dir_all(&out).unwrap();
        for (name, prompt) in stage_prompts(&root) {
            std::fs::write(out.join(format!("{name}.md")), &prompt).unwrap();
            println!("{name}: {} lines, {} words, {} bytes", prompt.lines().count(), prompt.split_whitespace().count(), prompt.len());
        }
    }

    /// The scripted run of several workloads' renders: session 1's
    /// first call (every workload's head `v000`, the root's sides) and, after its first submission was accepted as
    /// `v001`, the call that continues the provider session. `(name, prompt)`.
    pub(crate) fn workloads_prompts(root: &Path) -> Vec<(&'static str, String)> {
        use crate::prompts::engine_facts::general::tests::workloads_run::*;
        let run = workloads_run(root);
        let session = run.session_one.clone();
        let context = workloads_context(&run, false);
        let first = general_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &workloads_ledger_view(&run),
            prompt_file: &session.join("calls/0001/prompt.txt"), handoff: &Value::Null });
        sent(&session, 1, &first);
        workloads_first_submission(&run);
        let context = workloads_context(&run, true);
        let feedback = workloads_feedback_after_first_submission(&run);
        let continued = general_author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits(), ledger: &workloads_ledger_view(&run),
            prompt_file: &session.join("calls/0002/prompt.txt"), handoff: &Value::Null });
        vec![("workloads-first-call-session-1", first), ("workloads-continued-call-after-submission-1", continued)]
    }

    /// A run of several workloads' prompt: the first call has the section One engine
    /// for every workload after the goal and the main direction (no Stage 2 section), the Set forms of the goal, what is
    /// fixed and the loop, the workloads named (no placeholder left), the primary in the session line, every workload's
    /// files in the key paths and the workloads' facts; the continued call after an accepted submission has the combined
    /// decision and every workload's outcome, and gets no CHANGED INSTRUCTIONS.
    #[test]
    fn a_run_of_several_workloads_prompt_names_its_workloads_and_shows_their_facts() {
        let root = crate::controller::test_support::scratch_root("general-workloads-prompt");
        let prompts = workloads_prompts(&root);
        let first = &prompts[0].1;
        let order = ["# Key paths and scope", "`workloads.anyschema.storages` workloads/anyschema/storages.json", "`workloads.sec.templates` workloads/sec/templates.md",
            "This is session 1 at scale sf100 of the primary workload `tpch`, seeded from v000.", "# Goal", "one engine for every workload of this run",
            "on the training templates of every counted workload (`tpch` and `sec`) at every worker count", "# Main direction: data and query co-optimization", "# One engine for every workload",
            "counted (`tpch` and `sec`), check (`anyschema`) and kept (none)", "Your workspace starts from the side of `tpch`, the primary workload", "# How to work", "# What is fixed",
            "12. **Check workloads verify and answer** (gating)", "# Storage", "# Fallback: the verified interpreter", "this run's root has one side per workload instead", "# The loop",
            "4. every check workload: every template at every visible binding", "# Submission", "# CURRENT FACTS AND PATHS", "## Scale", "Scale **sf100** of the primary workload `tpch`",
            "## Workloads", "## Score at sf100 on `tpch`", "## Per template at sf100 on `tpch`", "## The root's sides", "## Counted workload `sec` at sf3", "## Check workload `anyschema` at tiny",
            "## Versions", "## Storage at sf100 on `tpch`", "## Budget and session", "## Integrity constraints", "# HANDOFF: YOUR WORK SO FAR", "# LEDGER"];
        let mut at = 0;
        for heading in order {
            let found = first[at..].find(heading).unwrap_or_else(|| panic!("{heading} missing or out of order:\n{first}"));
            at += found + heading.len();
        }
        assert_eq!(unfilled_placeholder(first), None);
        assert!(!first.contains("# Stage 2") && !first.contains("# A continued engine") && !without_paths(first).to_lowercase().contains("branch"), "{first}");
        assert!(first.contains("In this run the evaluation also runs Verus on every other workload's crate and builds its storages, then `sec`: 18 cells timed the same way at sf3; `anyschema`: 3 templates at 2 bindings at 1 and 64 workers, one call each."), "{first}");
        let continued = &prompts[1].1;
        assert!(continued.starts_with("# EVALUATION OF YOUR SUBMISSION") && !continued.contains("CHANGED INSTRUCTIONS"), "{continued}");
        for said in ["## Submission 1: accepted as v001", "- Combined score over `tpch` and `sec` (the decision): parent F 30/30, G 17.890; yours F 30/30, G 16.263: better.",
            "- `anyschema` (check) at tiny: verified and answered: 12 of 12 calls agreed.", "## Interleaved timing per template on `sec` at sf3", "## Workloads",
            "- `sec` (counted) at sf3: head v001, F 18/18 finished, G 13.949."] {
            assert!(continued.contains(said), "{said}\n{continued}");
        }
        assert_eq!(unfilled_placeholder(continued), None);
        std::fs::remove_dir_all(&root).ok();
    }

    /// Writes the run of several workloads' renders (the scripted run, no provider) under `GENDB_GENERAL_RENDER_DIR` for
    /// the operator's review.
    #[test]
    #[ignore = "writes the renders under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_workloads_renders() {
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        let root = out.join("fixture-run-workloads");
        std::fs::remove_dir_all(&root).ok();
        std::fs::create_dir_all(&out).unwrap();
        for (name, prompt) in workloads_prompts(&root) {
            std::fs::write(out.join(format!("{name}.md")), &prompt).unwrap();
            println!("{name}: {} lines, {} words, {} bytes", prompt.lines().count(), prompt.split_whitespace().count(), prompt.len());
        }
    }

    /// Generality rule 3 names every function the whole-statement evaluator rule refuses.
    #[test]
    fn the_prompt_names_every_refused_evaluator_route() {
        for route in gendb_verification::verus::engine_rules::EVALUATOR_ROUTES {
            assert!(engine::GENERALITY_RULES.contains(&format!("`{}`", route.function)), "{} is not named in GENERALITY_RULES", route.function);
        }
    }

    /// The prompt has the engine sections in order, the shared advice and policy, no unfilled placeholder, and the
    /// facts lead with the totals; it names no template.
    #[test]
    fn the_engine_prompt_is_complete_and_filled() {
        let context = json!({"files":{"workspace":"/w","author_contract":"/w/contract/engine/index.json"},"round":{"number":1,"seed":{"description":"an empty engine crate"},"notes":{}},
            "engine":{"limits":{"max_iterations":12},"rounds":[],"versions":[],"training":{"timing_binding":"v0","workers":[1],"templates":[],"baseline_totals":[],
                "variants":{"kinds":["wrapped_tables","from_permutation"],"frozen":2,"timed":1,"not_timed":1}}},
            "storage_policy":{"kind":"physical_only"}});
        let ledger = json!({});
        let prompt = engine_author_prompt(&PromptInput { context: &context, feedback: &[], iteration: 1, submission: 1, limits: &limits(), ledger: &ledger,
            prompt_file: Path::new("/r/calls/0001/prompt.txt"), handoff: &Value::Null });
        let order = ["# Key paths and scope", "round 1 (0 earlier rounds; the user's round guard: 12)", "# Task", "# Goal", "# What is fixed and what you own", "# Generality rules",
            "# Storage: seeded, with a budget", "# Storage policy: physical_only", "# Evaluation", "# Rounds and versions", "# How to work", "**Proofs.**", "**Reuse.**",
            "# Inputs and conduct", "# Tools", "# Submission", "# Appendix: processes on a shared host", "# CURRENT FACTS AND PATHS", "## Totals against the targets", "# LEDGER", "# LATEST FEEDBACK"];
        let mut at = 0;
        for heading in order {
            let found = prompt[at..].find(heading).unwrap_or_else(|| panic!("{heading} missing or out of order"));
            at += found + heading.len();
        }
        let placeholder = |line: &str| line.split('@').skip(1).step_by(2).any(|word| !word.is_empty() && word.chars().all(|c| c.is_ascii_uppercase() || c == '_'));
        assert!(!prompt.lines().any(placeholder), "an unfilled placeholder: {}", prompt.lines().find(|l| placeholder(l)).unwrap_or_default());
        assert!(prompt.contains("`wrapped_tables`, `from_permutation`") && prompt.contains("verus-engine.json"));
        let sections = [engine::ENGINE_TASK, engine::ENGINE_GOAL, engine::ENGINE_FIXED, engine::GENERALITY_RULES, engine::ENGINE_STORAGE, engine::ENGINE_ROUNDS,
            engine::ENGINE_HOW_TO_WORK, engine::ENGINE_EVALUATION, engine::ENGINE_INPUTS, engine::ENGINE_TOOLS].join("\n");
        let words: Vec<&str> = sections.split(|c: char| !c.is_ascii_alphanumeric()).collect();
        for name in ["Q01", "Q09", "Q21", "lineitem", "orders", "customer", "partsupp", "supplier", "nation", "region"] {
            assert!(!words.contains(&name), "the engine sections name no query or table: {name}");
        }
    }
}
