//! The instruction sections of a prompt and their digests.
//!
//! A full prompt of the general engine line is Markdown: the key paths and scope (with the opening line), then the
//! instruction sections (`# Goal` ... `# Appendix: processes on a shared host`), then the data (`# CURRENT FACTS AND
//! PATHS`, the handoff, the ledger, the latest feedback). An instruction section is one level-1 section: its `# `
//! heading line and every line up to the next level-1 heading outside a code fence, without trailing blank lines. Its
//! digest is the SHA-256 of that text.
//!
//! A provider session keeps the instructions of its first prompt for its whole life. When GenDB's instruction text
//! changes during a session (a relaunch with a newer build), the next continued call compares the digests the provider
//! session holds (`engine::sessions::held_instructions`) with the current sections ([`changes`]) and gives the changed
//! sections in full (CHANGED INSTRUCTIONS, `prompts::engine_policy`).

use serde::{Deserialize, Serialize};

/// The level-1 heading that starts the data of a full prompt; instruction sections end before it.
pub const DATA_HEADING: &str = "CURRENT FACTS AND PATHS";
/// The level-1 heading of the operator's notes at the very top of a prompt (`engine::operator_note`); not an
/// instruction section.
pub const OPERATOR_NOTE_HEADING: &str = "NOTE FROM THE RUN'S OPERATOR";

/// One level-1 section: its heading (the text after `# `) and its whole text (heading line included).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Section {
    pub heading: String,
    pub text: String,
}

/// The digest of one instruction section, as records keep it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SectionDigest {
    pub heading: String,
    pub sha256: String,
}

impl Section {
    pub fn digest(&self) -> SectionDigest {
        SectionDigest { heading: self.heading.clone(), sha256: sha256_hex(&self.text) }
    }
}

/// The SHA-256 of `text` in hex.
pub fn sha256_hex(text: &str) -> String {
    use sha2::{Digest, Sha256};
    Sha256::digest(text.as_bytes()).iter().map(|b| format!("{b:02x}")).collect()
}

/// The level-1 sections of `text`, in order. A line `# <heading>` outside a fenced code block starts a section; lines
/// before the first heading belong to none; a section's trailing blank lines are not part of it.
pub fn level_one_sections(text: &str) -> Vec<Section> {
    let mut sections: Vec<Section> = vec![];
    let mut in_fence = false;
    for line in text.lines() {
        if line.trim_start().starts_with("```") {
            in_fence = !in_fence;
        }
        match line.strip_prefix("# ").filter(|_| !in_fence) {
            Some(heading) => sections.push(Section { heading: heading.trim().to_string(), text: line.to_string() }),
            None => {
                if let Some(section) = sections.last_mut() {
                    section.text.push('\n');
                    section.text.push_str(line);
                }
            }
        }
    }
    for section in &mut sections {
        section.text.truncate(section.text.trim_end().len());
    }
    sections
}

/// The instruction sections of a full prompt: every level-1 section after the first one (the key paths and scope),
/// up to the data ([`DATA_HEADING`]). Operator notes before the key paths ([`OPERATOR_NOTE_HEADING`]) are not counted.
pub fn instruction_sections(prompt: &str) -> Vec<Section> {
    level_one_sections(prompt).into_iter().skip_while(|s| s.heading == OPERATOR_NOTE_HEADING).skip(1).take_while(|s| s.heading != DATA_HEADING).collect()
}

/// The digest of a whole set of instruction sections (their digests in order).
pub fn instructions_digest(sections: &[SectionDigest]) -> String {
    sha256_hex(&sections.iter().map(|s| format!("{}\n{}\n", s.heading, s.sha256)).collect::<String>())
}

/// What changed between the instruction sections a provider session holds and the current ones.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Changes {
    /// Current sections that are new or whose text differs, in the current order.
    pub changed: Vec<Section>,
    /// Headings of held sections that the current instructions no longer have.
    pub removed: Vec<String>,
}

impl Changes {
    pub fn is_empty(&self) -> bool {
        self.changed.is_empty() && self.removed.is_empty()
    }
}

/// The changes from `held` to `current` (sections matched by heading).
pub fn changes(held: &[SectionDigest], current: &[Section]) -> Changes {
    let changed = current.iter().filter(|section| !held.iter().any(|h| h.heading == section.heading && h.sha256 == sha256_hex(&section.text))).cloned().collect();
    let removed = held.iter().filter(|h| !current.iter().any(|s| s.heading == h.heading)).map(|h| h.heading.clone()).collect();
    Changes { changed, removed }
}

#[cfg(test)]
mod tests {
    use super::*;

    const PROMPT: &str = "# Key paths and scope\n\n- `a`: /a\n\nGenDB owns evaluation.\n\n# Goal\n\nBe fast.\n\n## Detail\n\nMore.\n\n\n# Tools\n\n- trial\n\n# CURRENT FACTS AND PATHS\n\n## Scale\n\nsf1\n\n# HANDOFF\n\n```markdown\n# Notes\n```\n";

    /// Sections run from a level-1 heading to the next one outside a code fence; the instruction sections are those
    /// between the key paths and the data.
    #[test]
    fn instruction_sections_are_the_level_one_sections_before_the_data() {
        let all = level_one_sections(PROMPT);
        assert_eq!(all.iter().map(|s| s.heading.as_str()).collect::<Vec<_>>(), ["Key paths and scope", "Goal", "Tools", DATA_HEADING, "HANDOFF"], "a fenced `# Notes` is no heading");
        let sections = instruction_sections(PROMPT);
        assert_eq!(sections.iter().map(|s| s.heading.as_str()).collect::<Vec<_>>(), ["Goal", "Tools"]);
        let noted = format!("# {OPERATOR_NOTE_HEADING}\n\n> a note\n\n{PROMPT}");
        assert_eq!(instruction_sections(&noted), sections, "an operator note at the top is not an instruction section");
        assert_eq!(sections[0].text, "# Goal\n\nBe fast.\n\n## Detail\n\nMore.", "level-2 headings stay inside; trailing blank lines are dropped");
    }

    /// Changed, new and removed sections are found by heading and digest; equal texts are no change.
    #[test]
    fn changes_name_new_changed_and_removed_sections() {
        let held: Vec<SectionDigest> = instruction_sections(PROMPT).iter().map(Section::digest).collect();
        assert!(changes(&held, &instruction_sections(PROMPT)).is_empty());
        let now = "# Key paths and scope\n\n# Goal\n\nBe fast, now.\n\n# Work fast\n\nMeasure.\n\n# CURRENT FACTS AND PATHS\n";
        let found = changes(&held, &instruction_sections(now));
        assert_eq!(found.changed.iter().map(|s| s.heading.as_str()).collect::<Vec<_>>(), ["Goal", "Work fast"]);
        assert_eq!(found.removed, ["Tools"]);
        assert_ne!(instructions_digest(&held), instructions_digest(&instruction_sections(now).iter().map(Section::digest).collect::<Vec<_>>()));
    }
}
