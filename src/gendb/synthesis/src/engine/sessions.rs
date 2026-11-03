//! One session of a general-line branch: its records, the
//! provider context it has used, when it ends, its role policy, and the run's spend that every call is checked against.
//!
//! A **session** is one author session of the generic controller (`controller::run`) in its own directory
//! `engine/branches/<branch>/sessions/session-NNNN/` (`session.json`, written before it starts: [`SessionRecord`]). Its
//! calls continue one provider session across submissions: every evaluation of the general role names the next call's
//! provider session (`next_call.provider_session`, read by `controller::ledger::Ledger::assign_provider_session`), so
//! submitting costs no context. A session ends after a submission's evaluation ([`session_end`]) when
//! - the author asked for a fresh session (the manifest's `next_session: "fresh"`), or
//! - the provider compacted the session's context at least once since it started (the provider's own signal that the
//!   context is full; read from the call transcripts, [`ProviderContext`]), or
//! - a merge session's merge was accepted, or
//! - the scale ladder's move is due: the main-line head finishes every cell at the current scale
//!   (`engine::branches::ladder_check`). The run moves once no session runs or is open, and the branch's next session
//!   starts at the new scale ([`DueScaleMove`]),
//!
//! and otherwise by the controller's existing stops (the unchanged-resubmission rule, a provider refusal) or by the
//! run's budget, which the session policy checks before every call over the spend of every session of the run
//! ([`RunSpend`]). No turn cap and no time cap are added. Then the branch's next session starts fresh from the
//! branch's files (`engine::branches`).
//!
//! A provider session keeps the instructions of its first prompt. `instructions.jsonl` ([`InstructionRecord`]) records,
//! per call that sent instructions, the digest of every instruction section the provider session holds afterwards, so
//! a later continued call can tell whether GenDB's instruction text changed since (a relaunch with a newer build) and
//! give the changed sections in full ([`held_instructions`]; `prompts::engine_policy`, CHANGED INSTRUCTIONS). A session
//! whose first prompt was sent before these records existed is read from that prompt (`calls/NNNN/prompt.txt`).
//!
//! Units: tokens as the provider counts them; money as provider-reported dollars (`Money`).

use super::role::{copy_tree, make_writable};
use super::submission::{CRATE_DIRECTORY, MANIFEST_FILE};
use super::tree::{NODE_FILE, VersionTree, node_directory};
use crate::controller::layout::{NOTES_FILE, RunLayout};
use crate::prompts::engine_contract::VERSIONS_DIRECTORY;
use gendb_verification::admission::AdmissionError;
use crate::controller::ledger::{CONTINUE_PROVIDER_SESSION, LedgerState};
use crate::controller::limits::Money;
use crate::controller::records::{self, RecordError};
use crate::controller::run::RunRequest;
use crate::controller::{PromptInput, RolePolicy, StopReason, Trial};
use crate::prompts::engine_policy::EnginePolicy;
use crate::prompts::instructions::{SectionDigest, instruction_sections, instructions_digest, sha256_hex};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// The record of one session in its directory.
pub const SESSION_FILE: &str = "session.json";

/// What a session is for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SessionKind {
    /// The branch's own work: submissions are raced against the branch head.
    Branch,
    /// A merge into the main line: seeded from the main-line head, submissions are raced against it.
    Merge,
}

/// The author's choice for the next session (the manifest's `next_session`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NextSession {
    /// Go on in this session (the default).
    Continue,
    /// End this session after this submission's evaluation; a fresh session continues the branch from its files.
    Fresh,
}

/// `session.json`: one session's identity, written before it starts and read back by a restart.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SessionRecord {
    pub format_version: u32,
    /// The branch slot (`b1`, ...); a merge session runs in the slot of the branch it merges.
    pub branch: String,
    /// 1-based within the branch.
    pub number: u32,
    pub kind: SessionKind,
    /// The version the workspace is seeded from: the branch head, or the main-line head for a merge.
    pub seed: String,
    /// A merge session: the branch head whose gains it takes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub merge_from: Option<String>,
    /// The scale its submissions are timed at.
    pub scale: String,
    /// The branch's previous session (its notebook and workspace are carried).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub previous: Option<PathBuf>,
    /// The generic session's request (its ledger identity).
    pub request: RunRequest,
    pub started_unix_ms: u64,
}

/// The directory of session `number` of `branch`.
pub fn session_directory(engine_dir: &Path, branch: &str, number: u32) -> PathBuf {
    engine_dir.join("branches").join(branch).join("sessions").join(format!("session-{number:04}"))
}

/// One session as the driver and the summary see it.
#[derive(Clone, Debug)]
pub struct SessionView {
    pub record: SessionRecord,
    pub directory: PathBuf,
    /// The session has not closed (no summary, or one with unresolved accounting): a relaunch resumes it.
    pub open: bool,
    /// Its summary (`Null` while none).
    pub summary: Value,
    /// Its submissions evaluated so far (from its ledger).
    pub evaluated: u32,
}

impl SessionView {
    /// Read the session in `directory`.
    pub fn read(directory: &Path) -> Result<Self, RecordError> {
        let record: SessionRecord = records::read_json(&directory.join(SESSION_FILE))?;
        let layout = RunLayout::new(directory);
        let summary: Value = if layout.summary().is_file() { records::read_json(&layout.summary())? } else { Value::Null };
        let open = !summary.is_object() || summary["status"] == "accounting_unresolved";
        let evaluated = if layout.ledger().is_file() {
            let ledger: LedgerState = records::read_json(&layout.ledger())?;
            ledger.trials.iter().filter(|t| t.status == crate::controller::ledger::TrialStatus::Evaluated).count() as u32
        } else {
            0
        };
        Ok(Self { record, directory: directory.to_path_buf(), open, summary, evaluated })
    }

    /// The summary's stop reason (`None` while open).
    pub fn reason(&self) -> Option<&str> {
        (!self.open).then(|| self.summary["reason"].as_str()).flatten()
    }
}

/// Every session of `branch`, in number order.
pub fn branch_sessions(engine_dir: &Path, branch: &str) -> Result<Vec<SessionView>, RecordError> {
    let dir = engine_dir.join("branches").join(branch).join("sessions");
    let mut found: Vec<PathBuf> = fs::read_dir(&dir).into_iter().flatten().flatten().map(|e| e.path()).filter(|p| p.join(SESSION_FILE).is_file()).collect();
    found.sort();
    found.iter().map(|d| SessionView::read(d)).collect()
}

// ------------------------------------------------------------------------------------------------ the workspace

/// Seed a session's workspace once and return the seed record: the seed version's sources and
/// manifest (`code/agent`, its workspace storages under `new-storages/`, `seed-manifest.json` as `verus-engine.json`);
/// the branch's notebook `NOTES.md` from the branch's previous session (else the seed version's); read-only copies of
/// the versions the session works from under `versions/` (the seed, the branch head, the main-line head, and for a
/// merge the branch head it takes gains from and their common ancestor), with a merge's own notes beside them under
/// `merge/`. Every other version is readable in the run's records (`tree.json` names their folders). A seeding that a
/// stop interrupted is redone over what it left ([`reopen_interrupted_seeding`]).
pub fn seed_session_workspace(workspace: &Path, engine_dir: &Path, record: &SessionRecord, tree: &VersionTree) -> Result<Value, AdmissionError> {
    let seed = node_directory(engine_dir, &record.seed, true);
    if !seed.join(NODE_FILE).is_file() {
        return Err(AdmissionError::tool(format!("seed version {} has no complete folder ({})", record.seed, seed.display())));
    }
    reopen_interrupted_seeding(workspace)?;
    let crate_src = workspace.join(CRATE_DIRECTORY).join("src");
    // The author's own copy: writable (the version folder's code keeps the frozen crate's read-only modes).
    copy_tree(&seed.join("code/agent"), &crate_src.join("agent"), false)?;
    make_writable(&crate_src.join("agent"))?;
    if seed.join("code/storages").is_dir() {
        copy_tree(&seed.join("code/storages"), &workspace.join("new-storages"), false)?;
        make_writable(&workspace.join("new-storages"))?;
    }
    fs::copy(seed.join("seed-manifest.json"), workspace.join(MANIFEST_FILE)).map_err(|e| AdmissionError::tool(format!("{}: {e}", seed.display())))?;
    let previous_notes = record.previous.as_ref().map(|p| RunLayout::new(p).workspace().join(NOTES_FILE)).filter(|p| p.is_file());
    let notes_from = match (&previous_notes, record.kind) {
        (Some(notes), SessionKind::Branch) => Some(notes.clone()),
        _ => Some(seed.join(NOTES_FILE)).filter(|p| p.is_file()),
    };
    let notes_text = match &notes_from {
        Some(from) => {
            fs::copy(from, workspace.join(NOTES_FILE)).map_err(AdmissionError::tool)?;
            Some(fs::read_to_string(from).map_err(AdmissionError::tool)?)
        }
        None => None,
    };
    let mut read_only: Vec<String> = vec![record.seed.clone()];
    read_only.extend(tree.branch_head(&record.branch).map(String::from));
    read_only.extend(tree.main_line_head().map(String::from));
    let mut merge = Value::Null;
    if let (SessionKind::Merge, Some(branch_head)) = (record.kind, &record.merge_from) {
        let base = tree.merge_base(&record.seed, branch_head);
        read_only.push(branch_head.clone());
        read_only.extend(base.clone());
        let dir = workspace.join("merge");
        records::create_dir(&dir).map_err(AdmissionError::tool)?;
        if let Some(notes) = &previous_notes {
            fs::copy(notes, dir.join("branch-NOTES.md")).map_err(AdmissionError::tool)?;
        }
        let readme = format!("# Merge\n\nThis session merges the gains of branch {} (its head {branch_head}) into the main line. Your workspace starts from the main-line head {}; the branch head's code is under `versions/{branch_head}/code`, their newest common ancestor's under `versions/{}/code`. The branch's notebook is `merge/branch-NOTES.md`; the main line's is `NOTES.md`. A submission is accepted when it beats the main-line head in one interleaved timing; the accepted merge becomes the main-line head and ends this session.\n",
            record.branch, record.seed, base.as_deref().unwrap_or("none"));
        fs::write(dir.join("README.md"), readme).map_err(AdmissionError::tool)?;
        merge = json!({"branch_head":branch_head,"main_line_head":record.seed,"merge_base":base,"readme":dir.join("README.md"),"branch_notes":previous_notes});
    }
    let mut seen = std::collections::BTreeSet::new();
    read_only.retain(|v| seen.insert(v.clone()));
    let versions_dir = workspace.join(VERSIONS_DIRECTORY);
    for id in &read_only {
        let from = node_directory(engine_dir, id, true);
        for part in ["code", "manifest.json", NOTES_FILE, "README.md", "version.json"] {
            let source = from.join(part);
            let target = versions_dir.join(id).join(part);
            if source.is_dir() {
                copy_tree(&source, &target, true)?;
            } else if source.is_file() {
                records::create_dir(target.parent().unwrap_or(&versions_dir)).map_err(AdmissionError::tool)?;
                fs::copy(&source, &target).map_err(AdmissionError::tool)?;
                read_only_file(&target)?;
            }
        }
    }
    Ok(json!({"format_version":1,"session":record,"seed":seed,"copied":["engine/src/agent",MANIFEST_FILE],"notes_from":notes_from,"notes_text":notes_text,
        "read_only_versions":read_only.iter().map(|v| versions_dir.join(v)).collect::<Vec<_>>(),"merge":merge,"seeded_unix_ms":records::now_unix_ms()}))
}

fn read_only_file(path: &Path) -> Result<(), AdmissionError> {
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(path, fs::Permissions::from_mode(0o444)).map_err(AdmissionError::tool)
}

/// Make a seeding that a stop interrupted safe to redo. The session's preparation seeds the workspace again whenever
/// `seed.json` is absent, which means no author call has run in it yet. An interrupted seeding can leave read-only
/// files: the version folders' code keeps the frozen crate's modes until `make_writable`, and the copies under
/// `versions/` are read-only on purpose. Copying over a read-only file fails, so every file the seeding writes that
/// already exists gets write permission first; the seeding then replaces each one and sets its mode again.
fn reopen_interrupted_seeding(workspace: &Path) -> Result<(), AdmissionError> {
    use std::os::unix::fs::PermissionsExt;
    for dir in [workspace.join(CRATE_DIRECTORY).join("src/agent"), workspace.join("new-storages"), workspace.join(VERSIONS_DIRECTORY), workspace.join("merge")] {
        if dir.is_dir() {
            make_writable(&dir)?;
        }
    }
    for file in [workspace.join(MANIFEST_FILE), workspace.join(NOTES_FILE)] {
        if let Some(metadata) = fs::metadata(&file).ok().filter(|m| m.is_file()) {
            fs::set_permissions(&file, fs::Permissions::from_mode(metadata.permissions().mode() | 0o200)).map_err(AdmissionError::tool)?;
        }
    }
    Ok(())
}

// ------------------------------------------------------------------------------------------------ provider context

/// What one transcript says about the context: the last and the largest context of a main-thread assistant turn
/// (`input_tokens + cache_read_input_tokens + cache_creation_input_tokens`) and the completed automatic
/// compactions (`system` events of subtype `compact_boundary`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct TranscriptContext {
    pub turns: u64,
    pub last_context_tokens: u64,
    pub peak_context_tokens: u64,
    pub compactions: u32,
}

/// Read one call's `stream-json` transcript (lines that are not JSON are skipped). Sub-agent turns
/// (`parent_tool_use_id` set) are not the session's context and are not counted.
pub fn transcript_context(transcript: &str) -> TranscriptContext {
    let mut context = TranscriptContext::default();
    for line in transcript.lines().filter(|l| l.contains("\"type\"")) {
        let Ok(event) = serde_json::from_str::<Value>(line) else { continue };
        match event["type"].as_str() {
            Some("system") if event["subtype"] == "compact_boundary" => context.compactions += 1,
            Some("assistant") if event["parent_tool_use_id"].is_null() => {
                let usage = &event["message"]["usage"];
                if !usage.is_object() {
                    continue;
                }
                let tokens = ["input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens"].iter().map(|k| usage[*k].as_u64().unwrap_or(0)).sum();
                context.turns += 1;
                context.last_context_tokens = tokens;
                context.peak_context_tokens = context.peak_context_tokens.max(tokens);
            }
            _ => {}
        }
    }
    context
}

/// The provider session's context up to one call: the calls of the session's ledger that ran in the same
/// provider session as `call_id`, up to it, with their transcripts read together.
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct ProviderContext {
    pub provider_session: Option<String>,
    pub calls: Vec<u64>,
    /// The last turn's context of the last call that had one.
    pub context_tokens: u64,
    pub peak_context_tokens: u64,
    pub compactions: u32,
}

impl ProviderContext {
    /// Read the context of `call_id`'s provider session from the session in `session_root` (its `ledger.json` and each
    /// call's `calls/NNNN/stdout.jsonl`). A missing transcript adds nothing.
    pub fn of_call(session_root: &Path, call_id: u64) -> Result<Self, RecordError> {
        let layout = RunLayout::new(session_root);
        let ledger: LedgerState = records::read_json(&layout.ledger())?;
        let Some(call) = ledger.call(call_id) else {
            return Ok(Self::default());
        };
        let session = ledger.provider_session_of(call).to_string();
        let mut context = Self { provider_session: Some(session.clone()), ..Self::default() };
        for earlier in ledger.calls.iter().filter(|c| c.id <= call_id && ledger.provider_session_of(c) == session) {
            context.calls.push(earlier.id);
            let transcript = fs::read_to_string(layout.call(earlier.id).join("stdout.jsonl")).unwrap_or_default();
            let read = transcript_context(&transcript);
            context.compactions += read.compactions;
            context.peak_context_tokens = context.peak_context_tokens.max(read.peak_context_tokens);
            if read.turns > 0 {
                context.context_tokens = read.last_context_tokens;
            }
        }
        Ok(context)
    }
}

/// A move up the scale ladder that is due after an evaluation (`engine::branches::ladder_check`): the session ends for
/// it, so that the run can move.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DueScaleMove<'a> {
    /// How the texts name the version whose cells decide the move (`head` of one line, `main-line head`).
    pub head: &'a str,
    /// The current scale and the next one.
    pub from: &'a str,
    pub to: &'a str,
}

/// Why the session ends after this evaluation (`None`: it goes on): a move up the scale ladder is due, a merge
/// session's merge was accepted, the author asked for a fresh session, or the provider compacted the session's context
/// (module documentation). A due move is named first: the next session starts at the new scale.
pub fn session_end(asked: Option<NextSession>, context: &ProviderContext, merge_accepted: bool, scale_move: Option<DueScaleMove<'_>>) -> Option<String> {
    if let Some(DueScaleMove { head, from, to }) = scale_move {
        return Some(format!("scale_move: the {head} finishes every cell at {from}; this session ends here and the run moves to {to}; a fresh session continues from your notebook"));
    }
    if merge_accepted {
        return Some("merge_accepted: the merge became the main-line head; the branch continues in a fresh session".into());
    }
    if asked == Some(NextSession::Fresh) {
        return Some("author_asked_fresh: the submission's next_session is fresh".into());
    }
    if context.compactions > 0 {
        return Some(format!("provider_compacted: the provider compacted this session's context {} time(s); a fresh session continues from the branch's files", context.compactions));
    }
    None
}

/// The evaluation's `next_call`: continue the provider session unless the session ends.
pub fn next_call(end: Option<&str>, context: &ProviderContext) -> Value {
    let context = json!({"provider_session_id":context.provider_session,"calls":context.calls,"context_tokens":context.context_tokens,
        "peak_context_tokens":context.peak_context_tokens,"compactions":context.compactions});
    match end {
        None => json!({"provider_session":CONTINUE_PROVIDER_SESSION,"context":context}),
        Some(reason) => json!({"provider_session":"fresh","session_end":reason,"context":context}),
    }
}

// ------------------------------------------------------------------------------------------------ the instructions held

/// The record of the instructions each provider session of a session holds, one [`InstructionRecord`] per line.
pub const INSTRUCTIONS_FILE: &str = "instructions.jsonl";

/// How a call sent instructions to its provider session.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InstructionsSent {
    /// The full prompt (the provider session's first call, or a fresh provider session).
    Full,
    /// A continued call's CHANGED INSTRUCTIONS: the changed sections in full.
    Changed,
}

/// One line of [`INSTRUCTIONS_FILE`]: what the provider session of `call` holds of the instructions once that call's
/// prompt is sent.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InstructionRecord {
    pub format_version: u32,
    pub call: u64,
    /// The call's provider session (from the session's ledger; `None` when the ledger does not name it).
    pub provider_session: Option<String>,
    pub sent: InstructionsSent,
    /// SHA-256 of the call's whole prompt. The record counts only when the call's saved `prompt.txt` is exactly this
    /// prompt and its provider started (its transcript is not empty): a prompt rendered but never sent holds nothing.
    pub prompt_sha256: String,
    /// Every instruction section the provider session holds after this call, in prompt order.
    pub sections: Vec<SectionDigest>,
    /// `prompts::instructions::instructions_digest` of `sections`.
    pub digest: String,
    pub recorded_unix_ms: u64,
}

/// What a provider session holds of the instructions before a call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HeldInstructions {
    /// The newest sent record of the provider session (`call` is the call that sent it).
    Recorded { call: u64, sections: Vec<SectionDigest> },
    /// No record: the instruction sections of the provider session's first prompt, read from its saved `prompt.txt`
    /// (a session that started before these records existed).
    FirstPrompt { call: u64, sections: Vec<SectionDigest> },
    /// Neither a record nor a saved first prompt: nothing is known, so nothing is compared.
    Unknown,
}

/// The provider session of `call` in the session's ledger, and the first call of that provider session. A call the
/// ledger does not hold yet (a render before the call begins) continues the provider session of the newest earlier
/// call.
fn provider_session_of(state: &LedgerState, call: u64) -> Option<(String, u64)> {
    let this = state.call(call).or_else(|| state.calls.iter().filter(|c| c.id < call).max_by_key(|c| c.id))?;
    let session = state.provider_session_of(this).to_string();
    let first = state.calls.iter().filter(|c| c.id <= this.id && state.provider_session_of(c) == session).map(|c| c.id).min()?;
    Some((session, first))
}

/// Whether call `call`'s saved prompt is `prompt_sha256` and its provider started (a non-empty transcript).
pub(crate) fn prompt_was_sent(layout: &RunLayout, call: u64, prompt_sha256: &str) -> bool {
    let sent = fs::read_to_string(layout.prompt(call)).is_ok_and(|prompt| sha256_hex(&prompt) == prompt_sha256);
    sent && fs::metadata(layout.call(call).join("stdout.jsonl")).is_ok_and(|m| m.len() > 0)
}

/// What the provider session of `call` holds before it (module documentation): the newest record of that provider
/// session from an earlier call whose prompt was sent, else its first prompt's instruction sections, else nothing
/// known. Reading only; a record that cannot be read counts as absent.
pub fn held_instructions(session_root: &Path, call: u64) -> HeldInstructions {
    let layout = RunLayout::new(session_root);
    let Ok(state) = records::read_json::<LedgerState>(&layout.ledger()) else {
        return HeldInstructions::Unknown;
    };
    let Some((provider_session, first)) = provider_session_of(&state, call) else {
        return HeldInstructions::Unknown;
    };
    let recorded: Vec<InstructionRecord> = super::tree::read_lines(&session_root.join(INSTRUCTIONS_FILE))
        .unwrap_or_default()
        .into_iter()
        .filter_map(|line| serde_json::from_value(line).ok())
        .collect();
    let newest_sent = recorded
        .into_iter()
        .filter(|r| r.call < call && r.provider_session.as_deref() == Some(provider_session.as_str()))
        .filter(|r| prompt_was_sent(&layout, r.call, &r.prompt_sha256))
        .max_by_key(|r| r.call);
    if let Some(record) = newest_sent {
        return HeldInstructions::Recorded { call: record.call, sections: record.sections };
    }
    match fs::read_to_string(layout.prompt(first)) {
        Ok(prompt) if first < call => HeldInstructions::FirstPrompt { call: first, sections: instruction_sections(&prompt).iter().map(|s| s.digest()).collect() },
        _ => HeldInstructions::Unknown,
    }
}

/// Record that `call`'s prompt sends `sections` (all of them, or the changes that make the provider session hold them)
/// to its provider session. Appends one line to [`INSTRUCTIONS_FILE`]; the record counts once the prompt is sent.
pub fn record_instructions(session_root: &Path, call: u64, sent: InstructionsSent, prompt: &str, sections: Vec<SectionDigest>) -> Result<(), RecordError> {
    let layout = RunLayout::new(session_root);
    let provider_session = records::read_json::<LedgerState>(&layout.ledger()).ok().and_then(|state| provider_session_of(&state, call)).map(|(session, _)| session);
    let record = InstructionRecord {
        format_version: 1,
        call,
        provider_session,
        sent,
        prompt_sha256: sha256_hex(prompt),
        digest: instructions_digest(&sections),
        sections,
        recorded_unix_ms: records::now_unix_ms(),
    };
    let path = session_root.join(INSTRUCTIONS_FILE);
    let mut line = serde_json::to_vec(&record).map_err(|e| RecordError::new(&path, e))?;
    line.push(b'\n');
    use std::io::Write;
    fs::OpenOptions::new().create(true).append(true).open(&path).and_then(|mut file| file.write_all(&line)).map_err(|e| RecordError::new(&path, e))
}

// ------------------------------------------------------------------------------------------------ the run's spend

/// The provider-reported spend of every session of the run, read from their ledgers (counted as each ledger counts its
/// receipts: a resumed session total once, by increment), and the run's budget (the request's `max_cost_usd`). Shared
/// by every session policy of the run; reading is cheap (one small JSON record per session).
#[derive(Clone, Debug)]
pub struct RunSpend {
    engine_dir: Arc<PathBuf>,
    pub budget: Money,
}

/// The run's spend at one moment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct SpendNow {
    /// Counted provider-reported dollars of every call with a settled receipt.
    pub spent: Money,
    /// Reservations of calls whose usage is not known yet (in flight or unresolved).
    pub reserved: Money,
    /// Every call's cost is known.
    pub complete: bool,
}

impl RunSpend {
    pub fn new(engine_dir: &Path, budget: Money) -> Self {
        Self { engine_dir: Arc::new(engine_dir.to_path_buf()), budget }
    }

    /// Sum every session ledger under `engine/branches/*/sessions/*`.
    pub fn now(&self) -> Result<SpendNow, RecordError> {
        let mut now = SpendNow { spent: Money::default(), reserved: Money::default(), complete: true };
        let branches = self.engine_dir.join("branches");
        for branch in fs::read_dir(&branches).into_iter().flatten().flatten() {
            for session in fs::read_dir(branch.path().join("sessions")).into_iter().flatten().flatten() {
                let ledger = session.path().join("ledger.json");
                if !ledger.is_file() {
                    continue;
                }
                let state: LedgerState = records::read_json(&ledger)?;
                for (call, counted) in state.calls.iter().zip(state.counted_usage()) {
                    match counted.cost {
                        Some(cost) => now.spent = now.spent.checked_sum(cost).map_err(|e| RecordError::new(&ledger, e))?,
                        None => {
                            now.complete &= call.usage_in_resumed_session;
                            if !call.reservation_usd.is_unset() {
                                now.reserved = now.reserved.checked_sum(call.reservation_usd).map_err(|e| RecordError::new(&ledger, e))?;
                            }
                        }
                    }
                }
            }
        }
        Ok(now)
    }

    /// The budget is used up by known spend (calls in flight are not counted until their receipts settle; each
    /// session's own ledger guard reserves them).
    pub fn exhausted(&self) -> bool {
        self.now().is_ok_and(|now| now.spent >= self.budget)
    }

    /// The budget left after the known spend (at least one millionth of a dollar, so a session's guard stays valid; the
    /// run stops before a session starts once nothing is left).
    pub fn left(&self) -> Result<Money, RecordError> {
        let now = self.now()?;
        let left = self.budget.remaining_after(now.spent);
        Ok(if left.0 == 0 { Money(1) } else { left })
    }
}

// ------------------------------------------------------------------------------------------------ the policy

/// `objective.kind` of a general-line session.
pub const GENERAL_SESSION_OBJECTIVE: &str = "general_engine_session";
/// The rule of a session's objective.
pub const GENERAL_SESSION_RULE: &str = "open-ended: every submission is evaluated and accepted as the branch's next version when it passes admission and beats the branch head (a merge: the main-line head) in one interleaved timing, otherwise recorded as an attempt; the session goes on after each evaluation until the author asks for a fresh session, the provider compacts the context, a merge is accepted, the run moves up the scale ladder, or the run's budget is used up";

/// The role policy of a general-line session: the engine prompt (`prompt`, the general-line prompt of
/// `prompts`), an objective that stays open, and the stops of the module documentation before every call.
#[derive(Clone)]
pub struct GeneralSessionPolicy {
    pub prompt: fn(&PromptInput) -> String,
    pub spend: RunSpend,
}

impl RolePolicy for GeneralSessionPolicy {
    fn author_prompt(&self, input: &PromptInput) -> String {
        (self.prompt)(input)
    }

    /// Always `unmet` (the goal has no end inside a session), with the session's accepted versions so far.
    fn objective_status(&self, _context: &Value, trials: &[Trial]) -> Value {
        let accepted: Vec<&Value> = trials.iter().filter(|t| t.evaluation["accepted"] == true).map(|t| &t.evaluation["node"]).collect();
        json!({"status":"unmet","kind":GENERAL_SESSION_OBJECTIVE,"accepted":accepted,"rule":GENERAL_SESSION_RULE})
    }

    /// Before every call: the run's budget over every session's spend, then the session end its last evaluation set.
    fn search_stop(&self, _context: &Value, trials: &[Trial]) -> Option<StopReason> {
        if self.spend.exhausted() {
            return Some(StopReason::BudgetLimit);
        }
        let last = trials.last()?;
        if last.evaluation["merge_accepted"] == true {
            return Some(StopReason::FirstEligibleCandidate);
        }
        last.evaluation["next_call"]["session_end"].is_string().then_some(StopReason::FreshSession)
    }

    fn submission_code(&self, frozen_dir: &Path, candidate: &Value, workspace: Option<&Path>) -> Value {
        EnginePolicy.submission_code(frozen_dir, candidate, workspace)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::ledger::{Call, Ledger, Receipt, UsageScope};
    use crate::controller::limits::tests::limits;
    use crate::controller::limits::UNSET_COUNT;

    fn assistant(tokens: u64, subagent: bool) -> String {
        json!({"type":"assistant","parent_tool_use_id":if subagent { json!("toolu_1") } else { Value::Null },
            "message":{"usage":{"input_tokens":2,"cache_read_input_tokens":tokens,"cache_creation_input_tokens":10,"output_tokens":5}}}).to_string()
    }

    const COMPACTION: &str = r#"{"type":"system","subtype":"compact_boundary","compact_metadata":{"trigger":"auto","pre_tokens":970453,"post_tokens":12517}}"#;
    const COMPACTING_STATUS: &str = r#"{"type":"system","subtype":"status","status":"compacting"}"#;

    /// Context size is the main thread's last turn (sub-agent turns are not the session's context); a completed
    /// compaction is a `compact_boundary` event, not the `compacting` status.
    #[test]
    fn transcripts_give_context_size_and_compactions() {
        let transcript = [assistant(100, false), assistant(5000, true), assistant(300, false), COMPACTING_STATUS.into(), "not json".into(), assistant(50, false)].join("\n");
        assert_eq!(transcript_context(&transcript), TranscriptContext { turns: 3, last_context_tokens: 62, peak_context_tokens: 312, compactions: 0 });
        assert_eq!(transcript_context(&format!("{transcript}\n{COMPACTION}")).compactions, 1);
    }

    fn receipt(call: u64, session: &str, total: &str) -> Receipt {
        Receipt { call_id: call, session_id: session.into(), ended_unix_ms: u64::MAX, elapsed_ms: 1, reported_cost_usd: Some(Money::parse(total).unwrap()),
            billed_cost_usd: None, tokens: None, outcome: "success".into(), raw_result: Some(json!({"total_cost_usd": total})),
            output: Some(json!({"candidate_manifest":"verus-engine.json","rationale":"r","data_access_analysis":"d"})), usage_scope: Some(UsageScope::Session) }
    }

    /// One call of a new iteration: begin, assign its provider session, settle and submit it with `evaluation` (as the
    /// controller does), and write its transcript. Returns the assigned call.
    fn submit(ledger: &mut Ledger, root: &Path, total: &str, transcript: &str, evaluation: Value) -> Call {
        let call = ledger.begin_call().unwrap();
        let call = ledger.assign_provider_session(call.id, |earlier| root.join(format!("calls/{:04}/stdout.jsonl", earlier.id)).is_file()).unwrap();
        let dir = RunLayout::new(root).call(call.id);
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("stdout.jsonl"), transcript).unwrap();
        let session = call.provider_session.clone().unwrap();
        let settled = receipt(call.id, &session, total);
        let output = settled.output.clone().unwrap();
        ledger.settle(settled).unwrap();
        ledger.submit(call.id, output).unwrap();
        let trial = ledger.state.trials.last_mut().unwrap();
        trial.status = crate::controller::ledger::TrialStatus::Evaluated;
        trial.evaluation = evaluation;
        ledger.save().unwrap();
        call
    }

    /// Done-check 2: a new iteration resumes the previous provider session when the evaluation asks for it; after a
    /// transcript with a compaction event, or on the author's `fresh`, the session ends and the next call starts a fresh
    /// provider session. Spend is read over every session ledger of the run.
    #[test]
    fn iterations_continue_the_provider_session_until_compaction_or_fresh() {
        let root = crate::controller::test_support::scratch_root("engine-sessions");
        let engine = root.join("engine");
        let session = session_directory(&engine, "b1", 1);
        let guard = crate::controller::limits::Limits { max_iterations: UNSET_COUNT, max_cost_usd: Money::parse("100").unwrap(), ..limits() };
        let mut ledger = Ledger::open(&session, json!({"request":{"task":"general"}}), guard.clone()).unwrap();
        let decide = |call: &Call, asked: Option<NextSession>| {
            let context = ProviderContext::of_call(&session, call.id).unwrap();
            let end = session_end(asked, &context, false, None);
            (next_call(end.as_deref(), &context), end)
        };
        // Iteration 1: a fresh provider session; the evaluation continues it.
        let first = submit(&mut ledger, &session, "1", &assistant(1000, false), Value::Null);
        assert!(!first.resumes_provider_session);
        let (choice, end) = decide(&first, None);
        assert_eq!((choice["provider_session"].as_str(), end), (Some("continue"), None));
        ledger.state.trials.last_mut().unwrap().evaluation = json!({"next_call":choice});
        ledger.save().unwrap();
        // Iteration 2 resumes it; its transcript has a compaction, so the session ends and the next call is fresh.
        let second = submit(&mut ledger, &session, "3", &format!("{}\n{COMPACTION}\n{}", assistant(900_000, false), assistant(20_000, false)), Value::Null);
        assert!(second.resumes_provider_session && second.provider_session == first.provider_session);
        let (choice, end) = decide(&second, None);
        assert!(end.as_deref().unwrap().starts_with("provider_compacted"), "{end:?}");
        assert_eq!((choice["provider_session"].as_str(), choice["context"]["compactions"].as_u64(), choice["context"]["peak_context_tokens"].as_u64()), (Some("fresh"), Some(1), Some(900_012)));
        ledger.state.trials.last_mut().unwrap().evaluation = json!({"next_call":choice});
        ledger.save().unwrap();
        let policy = GeneralSessionPolicy { prompt: |_| String::new(), spend: RunSpend::new(&engine, Money::parse("10").unwrap()) };
        assert_eq!(policy.search_stop(&Value::Null, &ledger.state.trials), Some(StopReason::FreshSession));
        let third = submit(&mut ledger, &session, "4", &assistant(10, false), Value::Null);
        assert!(!third.resumes_provider_session && third.provider_session != first.provider_session, "a fresh provider session after the compaction");
        // The author's `fresh` ends the session too, without a compaction; `continue` alone does not.
        let (_, end) = decide(&third, Some(NextSession::Continue));
        assert_eq!(end, None);
        let (choice, end) = decide(&third, Some(NextSession::Fresh));
        assert!(end.unwrap().starts_with("author_asked_fresh") && choice["provider_session"] == "fresh");
        ledger.state.trials.last_mut().unwrap().evaluation = json!({"next_call":choice});
        ledger.save().unwrap();
        let fourth = submit(&mut ledger, &session, "5", &assistant(10, false), Value::Null);
        assert!(!fourth.resumes_provider_session && fourth.provider_session != third.provider_session);
        // An unchanged resubmission carries its reused evaluation's choice.
        ledger.state.trials.last_mut().unwrap().evaluation = json!({"duplicate_effective_candidate":true,"reused_evaluation":{"next_call":{"provider_session":"continue"}}});
        ledger.save().unwrap();
        let fifth = submit(&mut ledger, &session, "6", &assistant(10, false), Value::Null);
        assert!(fifth.resumes_provider_session && fifth.provider_session == fourth.provider_session);
        // Spend over every session of the run, each provider session counted by increment: session 1 of b1 holds
        // 1 + 2 (one provider session), 4, then 5 + 1; b2's session 2.5.
        drop(ledger);
        let other = session_directory(&engine, "b2", 1);
        let mut second_ledger = Ledger::open(&other, json!({"request":{"task":"general"}}), guard).unwrap();
        submit(&mut second_ledger, &other, "2.5", &assistant(1, false), Value::Null);
        let spend = |budget: &str| RunSpend::new(&engine, Money::parse(budget).unwrap());
        let now = spend("100").now().unwrap();
        assert_eq!((now.spent, now.complete), (Money::parse("15.5").unwrap(), true));
        assert_eq!(spend("100").left().unwrap(), Money::parse("84.5").unwrap());
        let policy = |budget: &str| GeneralSessionPolicy { prompt: |_| String::new(), spend: spend(budget) };
        assert_eq!(policy("100").search_stop(&Value::Null, &[]), None);
        assert_eq!(policy("15.5").search_stop(&Value::Null, &[]), Some(StopReason::BudgetLimit), "every branch's spend counts against the one budget");
        fs::remove_dir_all(&root).unwrap();
    }

    /// Rule 1 of the scale move: an evaluation after which the ladder's move is due ends the session, like a
    /// fresh session, without a compaction or the author's `fresh`, and says why in one fact line; the move is named
    /// before an accepted merge. Without a due move the session goes on.
    #[test]
    fn a_due_scale_move_ends_the_session_at_its_evaluation() {
        let context = ProviderContext { provider_session: Some("s".into()), calls: vec![1, 2], context_tokens: 10, peak_context_tokens: 20, compactions: 0 };
        let due = DueScaleMove { head: "head", from: "sf1", to: "sf10" };
        assert_eq!(session_end(Some(NextSession::Continue), &context, false, None), None, "no move due: the session goes on");
        let end = session_end(Some(NextSession::Continue), &context, false, Some(due)).expect("a due move ends the session");
        assert_eq!(end, "scale_move: the head finishes every cell at sf1; this session ends here and the run moves to sf10; a fresh session continues from your notebook");
        let merged = session_end(None, &context, true, Some(DueScaleMove { head: "main-line head", ..due })).unwrap();
        assert!(merged.starts_with("scale_move: the main-line head finishes every cell at sf1"), "{merged}");
        let choice = next_call(Some(end.as_str()), &context);
        assert_eq!((choice["provider_session"].as_str(), choice["session_end"].as_str()), (Some("fresh"), Some(end.as_str())));
        // The session's policy closes it before the next call, as a fresh session.
        let trial = Trial { iteration: 1, call_id: 2, candidate: Value::Null, status: crate::controller::ledger::TrialStatus::Evaluated,
            evaluation: json!({"accepted":false,"next_call":choice}), framework_elapsed_ms: None, directory: None, recovery_records: vec![], evaluation_record: None };
        let root = crate::controller::test_support::scratch_root("engine-scale-move-end");
        let policy = GeneralSessionPolicy { prompt: |_| String::new(), spend: RunSpend::new(&root.join("engine"), Money::parse("10").unwrap()) };
        assert_eq!(policy.search_stop(&Value::Null, &[trial]), Some(StopReason::FreshSession));
        fs::remove_dir_all(&root).ok();
    }

    /// Done-check 3 (merge-session seeding): a merge session's workspace starts from the main-line head's code,
    /// manifest and notebook, with the branch head's and their common ancestor's code read-only and the branch's
    /// notebook under `merge/`; a branch session carries its previous session's notebook.
    #[test]
    fn merge_sessions_are_seeded_from_the_main_line_head_with_the_branch_head_beside_it() {
        use super::super::tree::{MainLineChange, NodeKind, TreeNode, append_main_line, write_node};
        let root = crate::controller::test_support::scratch_root("engine-session-seed");
        let engine = root.join("engine");
        for (id, branch, parents) in [("v000", "main", vec![]), ("v001", "b1", vec!["v000"]), ("v002", "b2", vec!["v000"])] {
            let dir = node_directory(&engine, id, true);
            fs::create_dir_all(dir.join("code/agent")).unwrap();
            fs::write(dir.join("code/agent/mod.rs"), format!("// {id}\n")).unwrap();
            read_only_file(&dir.join("code/agent/mod.rs")).unwrap();
            fs::write(dir.join("seed-manifest.json"), format!("{{\"version\":\"{id}\"}}")).unwrap();
            fs::write(dir.join(NOTES_FILE), format!("notes of {id}")).unwrap();
            let kind = if id == "v000" { NodeKind::FrameworkGenerated } else { NodeKind::Branch };
            write_node(&engine, &TreeNode { format_version: 1, id: id.into(), accepted: true, kind, branch: branch.into(), parents: parents.iter().map(|p| p.to_string()).collect(),
                scale: "sf1".into(), score: None, reason: None, session: None, iteration: None, direction: None, rationale: None, created_unix_ms: 1 }).unwrap();
        }
        for (version, previous) in [("v000", None), ("v002", Some("v000"))] {
            append_main_line(&engine, &MainLineChange { version: version.into(), previous: previous.map(String::from), reason: "r".into(), scale: "sf1".into(), race: None, adopted: None,
                selection: gendb_artifacts::ContentId::from_bytes([3; 32]), at_unix_ms: 1 }).unwrap();
        }
        let tree = VersionTree::read(&engine).unwrap();
        let previous = session_directory(&engine, "b1", 1);
        fs::create_dir_all(RunLayout::new(&previous).workspace()).unwrap();
        fs::write(RunLayout::new(&previous).workspace().join(NOTES_FILE), "b1 notebook, session 1").unwrap();
        let request = RunRequest { format_version: 1, task: json!({}), limits: limits(), continue_from: None };
        let record = |kind: SessionKind, seed: &str, merge_from: Option<&str>| SessionRecord { format_version: 1, branch: "b1".into(), number: 2, kind, seed: seed.into(),
            merge_from: merge_from.map(String::from), scale: "sf1".into(), previous: Some(previous.clone()), request: request.clone(), started_unix_ms: 1 };
        let merge = root.join("merge-workspace");
        let seeded = seed_session_workspace(&merge, &engine, &record(SessionKind::Merge, "v002", Some("v001")), &tree).unwrap();
        let read = |p: &Path| fs::read_to_string(p).unwrap();
        assert_eq!(read(&merge.join("engine/src/agent/mod.rs")), "// v002\n", "a merge starts from the main-line head");
        assert!(!fs::metadata(merge.join("engine/src/agent/mod.rs")).unwrap().permissions().readonly(), "the author's copy is writable");
        assert!(fs::metadata(merge.join(VERSIONS_DIRECTORY).join("v002/code/agent/mod.rs")).unwrap().permissions().readonly(), "the read-only copies stay read-only");
        assert_eq!(read(&merge.join(MANIFEST_FILE)), "{\"version\":\"v002\"}");
        assert_eq!(read(&merge.join(NOTES_FILE)), "notes of v002", "the main line's notebook");
        assert_eq!(read(&merge.join("merge/branch-NOTES.md")), "b1 notebook, session 1", "the branch's notebook beside it");
        for id in ["v002", "v001", "v000"] {
            assert_eq!(read(&merge.join(VERSIONS_DIRECTORY).join(id).join("code/agent/mod.rs")), format!("// {id}\n"), "{id} read-only");
        }
        assert!(read(&merge.join("merge/README.md")).contains("branch b1 (its head v001)"));
        assert_eq!((seeded["merge"]["branch_head"].as_str(), seeded["merge"]["merge_base"].as_str()), (Some("v001"), Some("v000")));
        let branch = root.join("branch-workspace");
        seed_session_workspace(&branch, &engine, &record(SessionKind::Branch, "v001", None), &tree).unwrap();
        assert_eq!((read(&branch.join("engine/src/agent/mod.rs")), read(&branch.join(NOTES_FILE))), ("// v001\n".to_string(), "b1 notebook, session 1".to_string()));
        assert!(!branch.join("merge").exists());
        // A stop during the seeding, after the copy and before the author's files were made writable, leaves them
        // read-only (as copied from the frozen crate), beside the read-only copies under `versions/` and a manifest.
        // The preparation seeds again (no `seed.json` yet): it replaces every file and sets the modes again.
        read_only_file(&branch.join("engine/src/agent/mod.rs")).unwrap();
        read_only_file(&branch.join(MANIFEST_FILE)).unwrap();
        seed_session_workspace(&branch, &engine, &record(SessionKind::Branch, "v001", None), &tree).unwrap();
        assert_eq!(read(&branch.join("engine/src/agent/mod.rs")), "// v001\n", "the seed's text again");
        assert!(!fs::metadata(branch.join("engine/src/agent/mod.rs")).unwrap().permissions().readonly(), "the author's copy is writable again");
        assert!(!fs::metadata(branch.join(MANIFEST_FILE)).unwrap().permissions().readonly());
        assert!(fs::metadata(branch.join(VERSIONS_DIRECTORY).join("v001/code/agent/mod.rs")).unwrap().permissions().readonly(), "the read-only copies are read-only again");
        assert_eq!(read(&branch.join(VERSIONS_DIRECTORY).join("v001/code/agent/mod.rs")), "// v001\n");
        assert!(seed_session_workspace(&root.join("w3"), &engine, &record(SessionKind::Branch, "v009", None), &tree).is_err(), "an unknown seed version");
        fs::remove_dir_all(&root).unwrap();
    }

    /// Session records round-trip; a session without a summary is open; branch sessions list in number order.
    #[test]
    fn session_records_and_views() {
        let root = crate::controller::test_support::scratch_root("engine-session-records");
        let engine = root.join("engine");
        let request = RunRequest { format_version: 1, task: json!({"role":"general_engine"}), limits: limits(), continue_from: None };
        for number in [2, 1] {
            let dir = session_directory(&engine, "b1", number);
            records::create_dir(&dir).unwrap();
            let record = SessionRecord { format_version: 1, branch: "b1".into(), number, kind: SessionKind::Branch, seed: "v000".into(), merge_from: None,
                scale: "sf1".into(), previous: None, request: request.clone(), started_unix_ms: 1 };
            records::write_new_json(&dir.join(SESSION_FILE), &record).unwrap();
        }
        records::write_new_json(&RunLayout::new(&session_directory(&engine, "b1", 1)).summary(), &json!({"status":"closed","reason":"fresh_session"})).unwrap();
        let sessions = branch_sessions(&engine, "b1").unwrap();
        assert_eq!(sessions.iter().map(|s| (s.record.number, s.open, s.reason())).collect::<Vec<_>>(), [(1, false, Some("fresh_session")), (2, true, None)]);
        assert!(branch_sessions(&engine, "b2").unwrap().is_empty());
        fs::remove_dir_all(&root).unwrap();
    }
}
