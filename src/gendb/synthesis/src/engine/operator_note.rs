//! A note from the run's operator to a branch's next author call: `gendb engine operator-note RUN_DIR BRANCH
//! TEXT`. The operator uses it to tell a live session something the framework's feedback cannot (for example, that an
//! evaluation was decided by load from other services on the shared host, and what was done about it).
//!
//! - [`write_note`] appends the note to the branch's record `engine/branches/<branch>/operator-notes.jsonl`
//!   ([`OperatorNote`], numbered from 1 under the record's lock). It works whether or not a controller runs.
//! - The branch's next author call shows every pending note at the very top of its prompt, under the heading
//!   [`OPERATOR_NOTE_HEADING`] (`prompts::engine_policy::general_author_prompt`, [`with_pending_notes`]), each note's
//!   text as a quoted block, and records the showing in its session's own `operator-notes.jsonl` ([`NoteShown`]: the
//!   note, its text, the call and the digest of the prompt that showed it). So every note a session was shown is kept in
//!   that session's records, and its saved prompt holds the text.
//! - **Once.** A note is pending until a call whose prompt showed it was sent: that call's saved `prompt.txt` is exactly
//!   the prompt recorded with the showing, and its provider started (`engine::sessions::prompt_was_sent`, the rule the
//!   instruction records use). A prompt rendered but never sent shows the note again in the next call. A note written
//!   while no session of the branch is open reaches the first call of the branch's next session.
//!
//! The note is the operator's text, shown as written; GenDB adds nothing to it and decides nothing from it.

use super::sessions::prompt_was_sent;
use crate::controller::layout::RunLayout;
use crate::controller::records::{self, RecordError, now_unix_ms};
use crate::file_lock::FileLock;
use crate::prompts::instructions::{OPERATOR_NOTE_HEADING, sha256_hex};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

/// The record of the notes (in the branch's directory) and of their showings (in each session's directory).
pub const OPERATOR_NOTES_FILE: &str = "operator-notes.jsonl";
/// The lock that numbers a branch's notes.
const OPERATOR_NOTES_LOCK: &str = "operator-notes.lock";

/// One note of the operator to a branch (a line of the branch's [`OPERATOR_NOTES_FILE`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperatorNote {
    pub format_version: u32,
    /// 1-based within the branch.
    pub note: u32,
    pub branch: String,
    pub text: String,
    /// Who wrote it (`operator` for the command; `re_evaluation` for the result of `gendb engine re-evaluate`).
    pub by: String,
    pub written_unix_ms: u64,
}

/// One showing of a note in an author call's prompt (a line of the session's [`OPERATOR_NOTES_FILE`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NoteShown {
    pub format_version: u32,
    pub note: u32,
    pub text: String,
    pub call: u64,
    /// SHA-256 of the whole prompt that showed it: the showing counts once the call's saved `prompt.txt` is this prompt
    /// and its provider started.
    pub prompt_sha256: String,
    pub shown_unix_ms: u64,
}

/// The directory of `branch`: `<engine>/branches/<branch>`.
pub fn branch_directory(engine_dir: &Path, branch: &str) -> PathBuf {
    engine_dir.join("branches").join(branch)
}

/// Append a note with `text` to `branch` (module documentation). The branch must have a session (its directory holds
/// `sessions/`); the text must not be empty.
pub fn write_note(engine_dir: &Path, branch: &str, text: &str, by: &str) -> Result<OperatorNote, RecordError> {
    let dir = branch_directory(engine_dir, branch);
    if branch.is_empty() || branch.contains('/') || !dir.join("sessions").is_dir() {
        return Err(RecordError::new(&dir, format!("{branch} is not a branch of this run with a session (no {})", dir.join("sessions").display())));
    }
    let text = text.trim();
    if text.is_empty() {
        return Err(RecordError::new(&dir, "an operator note needs a text"));
    }
    let lock_path = dir.join(OPERATOR_NOTES_LOCK);
    let lock = fs::OpenOptions::new().create(true).truncate(false).write(true).open(&lock_path).map_err(|e| RecordError::new(&lock_path, e))?;
    let _lock = FileLock::acquire(lock, libc::LOCK_EX).map_err(|e| RecordError::new(&lock_path, e))?;
    let path = dir.join(OPERATOR_NOTES_FILE);
    let note = OperatorNote { format_version: 1, note: notes_in(&path)?.len() as u32 + 1, branch: branch.into(), text: text.into(), by: by.into(), written_unix_ms: now_unix_ms() };
    append(&path, &note)?;
    Ok(note)
}

/// The notes of the branch whose session lives in `session_dir` that no sent prompt has shown yet, in order.
pub fn pending_notes(session_dir: &Path) -> Result<Vec<OperatorNote>, RecordError> {
    let Some(branch_dir) = session_dir.parent().and_then(Path::parent) else { return Ok(vec![]) };
    let notes = notes_in(&branch_dir.join(OPERATOR_NOTES_FILE))?;
    if notes.is_empty() {
        return Ok(notes);
    }
    let mut shown: BTreeSet<u32> = BTreeSet::new();
    for session in fs::read_dir(branch_dir.join("sessions")).into_iter().flatten().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
        let layout = RunLayout::new(&session);
        for showing in shown_in(&session)? {
            if prompt_was_sent(&layout, showing.call, &showing.prompt_sha256) {
                shown.insert(showing.note);
            }
        }
    }
    Ok(notes.into_iter().filter(|n| !shown.contains(&n.note)).collect())
}

/// The section that shows `notes` at the top of a prompt (empty for none): the heading, then each note's text as a
/// quoted block, so no line of a note can start a section of its own.
pub fn notes_section(notes: &[OperatorNote]) -> String {
    if notes.is_empty() {
        return String::new();
    }
    let quoted: Vec<String> = notes.iter().map(|n| n.text.lines().map(|line| if line.is_empty() { ">".to_string() } else { format!("> {line}") }).collect::<Vec<_>>().join("\n")).collect();
    format!("# {OPERATOR_NOTE_HEADING}\n\n{}", quoted.join("\n\n"))
}

/// `prompt` of call `call` in the session `session_dir`, with the branch's pending notes at its top (module
/// documentation), each showing recorded in the session. The prompt cannot fail: unreadable note records leave it as
/// it is, and a showing that cannot be recorded is shown again by the next call.
pub fn with_pending_notes(prompt: String, session_dir: &Path, call: u64) -> String {
    let notes = pending_notes(session_dir).unwrap_or_default();
    if notes.is_empty() {
        return prompt;
    }
    let shown = format!("{}\n\n{prompt}", notes_section(&notes));
    let digest = sha256_hex(&shown);
    let path = session_dir.join(OPERATOR_NOTES_FILE);
    for note in &notes {
        let _ = append(&path, &NoteShown { format_version: 1, note: note.note, text: note.text.clone(), call, prompt_sha256: digest.clone(), shown_unix_ms: now_unix_ms() });
    }
    shown
}

/// The notes recorded in `path` (none when it is absent).
fn notes_in(path: &Path) -> Result<Vec<OperatorNote>, RecordError> {
    super::tree::read_lines(path)?.into_iter().map(|line| serde_json::from_value(line).map_err(|e| RecordError::new(path, e))).collect()
}

/// The showings recorded in a session's directory.
fn shown_in(session_dir: &Path) -> Result<Vec<NoteShown>, RecordError> {
    let path = session_dir.join(OPERATOR_NOTES_FILE);
    super::tree::read_lines(&path)?.into_iter().map(|line| serde_json::from_value(line).map_err(|e| RecordError::new(&path, e))).collect()
}

/// Append one JSON line in one write (`O_APPEND`).
fn append(path: &Path, value: &impl Serialize) -> Result<(), RecordError> {
    if let Some(parent) = path.parent() {
        records::create_dir(parent)?;
    }
    let mut line = serde_json::to_vec(value).map_err(|e| RecordError::new(path, e))?;
    line.push(b'\n');
    fs::OpenOptions::new().create(true).append(true).open(path).and_then(|mut file| file.write_all(&line)).map_err(|e| RecordError::new(path, e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::layout::PROMPT_FILE;

    /// A session directory of `branch`.
    fn session(engine: &Path, branch: &str, number: u32) -> PathBuf {
        let dir = super::super::sessions::session_directory(engine, branch, number);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// The transport's part: the call's prompt saved, its provider started (a non-empty transcript), and the ledger
    /// that names the call (`prompt_was_sent` reads only the saved prompt and the transcript).
    fn send(session: &Path, call: u64, prompt: &str) {
        let dir = RunLayout::new(session).call(call);
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join(PROMPT_FILE), prompt).unwrap();
        fs::write(dir.join("stdout.jsonl"), "{\"type\":\"system\",\"subtype\":\"init\"}\n").unwrap();
    }

    /// Done-check: a note is shown once, at the top of the branch's next call, under its heading; a prompt
    /// rendered but never sent shows it again; every showing is recorded in the session; a note written between
    /// sessions reaches the next session's first call.
    #[test]
    fn an_operator_note_is_shown_once() {
        let root = crate::controller::test_support::scratch_root("engine-operator-note");
        let engine = root.join("engine");
        let one = session(&engine, "b1", 4);
        assert!(write_note(&engine, "b2", "x", "operator").is_err(), "a branch without a session");
        assert!(write_note(&engine, "b1", "  \n", "operator").is_err(), "an empty note");
        let note = write_note(&engine, "b1", "Your last evaluation was decided by load from other services.\n# Not a heading\n\nResubmit it.", "operator").unwrap();
        assert_eq!((note.note, note.branch.as_str(), note.by.as_str()), (1, "b1", "operator"));
        // Call 21 is rendered but its provider never starts: the note stays pending.
        let rendered = with_pending_notes("# EVALUATION OF YOUR SUBMISSION\n\nbody".into(), &one, 21);
        assert_eq!(rendered, "# NOTE FROM THE RUN'S OPERATOR\n\n> Your last evaluation was decided by load from other services.\n> # Not a heading\n>\n> Resubmit it.\n\n# EVALUATION OF YOUR SUBMISSION\n\nbody");
        assert_eq!(crate::prompts::instructions::level_one_sections(&rendered).len(), 2, "a quoted line starts no section");
        assert_eq!(pending_notes(&one).unwrap().len(), 1, "rendered, not sent");
        // Call 22 shows it again and is sent: it is never shown again.
        let shown = with_pending_notes("# EVALUATION OF YOUR SUBMISSION\n\nbody".into(), &one, 22);
        send(&one, 22, &shown);
        assert!(pending_notes(&one).unwrap().is_empty());
        assert_eq!(with_pending_notes("next".into(), &one, 23), "next", "shown once");
        let showings = shown_in(&one).unwrap();
        assert_eq!(showings.iter().map(|s| (s.note, s.call)).collect::<Vec<_>>(), [(1, 21), (1, 22)], "every showing is recorded in the session");
        assert_eq!(showings[1].prompt_sha256, sha256_hex(&shown));
        // A second note, written while session 4 has closed, reaches session 5's first call; the first stays shown.
        write_note(&engine, "b1", "second", "re_evaluation").unwrap();
        let five = session(&engine, "b1", 5);
        let first_call = with_pending_notes("# Key paths and scope".into(), &five, 1);
        assert!(first_call.starts_with("# NOTE FROM THE RUN'S OPERATOR\n\n> second\n\n# Key paths and scope"), "{first_call}");
        send(&five, 1, &first_call);
        assert!(pending_notes(&five).unwrap().is_empty() && pending_notes(&one).unwrap().is_empty());
        let notes = notes_in(&branch_directory(&engine, "b1").join(OPERATOR_NOTES_FILE)).unwrap();
        assert_eq!(notes.iter().map(|n| n.note).collect::<Vec<_>>(), [1, 2]);
        fs::remove_dir_all(&root).ok();
    }
}
