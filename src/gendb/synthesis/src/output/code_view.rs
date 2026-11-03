//! The reading view of verified Rust/Verus code (`code-view/`): the same file with the proof text
//! removed, for reading only. It is never compiled; `code/` is authoritative.
//!
//! Removed (each removed line becomes an empty line, so every kept line keeps its line number):
//! - `spec fn` and `proof fn` items (with their `#[verifier::..]` attributes and `broadcast` groups/uses); the first
//!   line of a removed item becomes a one-line comment naming it;
//! - `proof { .. }` blocks, `assert ..` statements (with `by` blocks), `let ghost` / `let tracked` statements and
//!   `hide(..)` / `reveal(..)` / `reveal_with_fuel(..)` statements;
//! - loop `invariant`, `invariant_except_break`, `ensures` and `decreases` clauses, and a function's `decreases`,
//!   `recommends` and `opens_invariants` clauses.
//!
//! Kept as comments: each executable function's `requires` / `ensures` / `returns` / `no_unwind` clauses (the line
//! prefixed by `// `; when the body's `{` is on the clause's last line, `{` comes first and the clause follows as a
//! comment). Everything else is unchanged.
//!
//! The scan is lexical: string and character literals and comments are masked before structure is read, and extents
//! are found by bracket depth. It is a reading aid, not a parser; an unusual layout can leave proof text in place.

/// The reading view of one source file (`text`), with the same number of lines.
pub fn code_view(text: &str) -> String {
    let lines: Vec<Vec<char>> = text.split('\n').map(|l| l.chars().collect()).collect();
    let mask = mask_literals_and_comments(&lines);
    let mut view = View { out: lines.iter().map(|l| l.iter().collect::<String>()).collect(), lines, mask };
    view.remove_items();
    view.remove_statements();
    view.rewrite_headers();
    view.out.join("\n")
}

/// A position: (line, column in chars).
type Pos = (usize, usize);

struct View {
    /// The original lines.
    lines: Vec<Vec<char>>,
    /// The lines with literal and comment characters replaced by spaces (structure only).
    mask: Vec<Vec<char>>,
    /// The output lines.
    out: Vec<String>,
}

/// How a removed extent ends.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Extent {
    /// An item: its body's brace group, or a `;` before any brace (no body).
    Item,
    /// A statement: a `;` at depth 0, or a brace group closing at depth 0 (then an immediately following `;`).
    Statement,
}

impl View {
    /// The masked line `i` from its first non-blank character, and that character's column.
    fn trimmed(&self, i: usize) -> (String, usize) {
        let line = &self.mask[i];
        let start = line.iter().position(|c| !c.is_whitespace()).unwrap_or(line.len());
        (line[start..].iter().collect(), start)
    }

    /// Whether the line was already changed (part of an earlier removal or rewrite).
    fn touched(&self, i: usize) -> bool {
        self.out[i] != self.lines[i].iter().collect::<String>()
    }

    /// The position just after the end of the extent of `kind` starting at `from`.
    fn extent_end(&self, from: Pos, kind: Extent) -> Pos {
        let mut depth: i64 = 0;
        let mut opened_brace = false;
        let (mut i, mut j) = from;
        while i < self.mask.len() {
            while j < self.mask[i].len() {
                let c = self.mask[i][j];
                match c {
                    '(' | '[' => depth += 1,
                    '{' => {
                        depth += 1;
                        opened_brace = true;
                    }
                    ')' | ']' => depth -= 1,
                    '}' => {
                        depth -= 1;
                        if depth == 0 && (kind == Extent::Item || opened_brace) {
                            return self.after_optional_semicolon((i, j + 1));
                        }
                    }
                    ';' if depth == 0 => return (i, j + 1),
                    _ => {}
                }
                j += 1;
            }
            i += 1;
            j = 0;
        }
        (self.mask.len() - 1, self.mask.last().map_or(0, Vec::len))
    }

    /// `p`, or just after a `;` that follows it on the same line (only blanks between).
    fn after_optional_semicolon(&self, p: Pos) -> Pos {
        let line = &self.mask[p.0];
        let mut j = p.1;
        while j < line.len() && line[j].is_whitespace() {
            j += 1;
        }
        if j < line.len() && line[j] == ';' { (p.0, j + 1) } else { p }
    }

    /// Remove `[from, to)`: whole lines become empty; a partial line keeps its text outside the range (a first line
    /// keeps `note` instead of the removed part when given).
    fn blank(&mut self, from: Pos, to: Pos, note: Option<String>) {
        for i in from.0..=to.0.min(self.lines.len() - 1) {
            let line = &self.lines[i];
            let start = if i == from.0 { from.1 } else { 0 };
            let end = if i == to.0 { to.1.min(line.len()) } else { line.len() };
            let before: String = line[..start].iter().collect();
            let after: String = line[end..].iter().collect();
            let mut kept = String::new();
            if !before.trim().is_empty() || (i == from.0 && note.is_some()) {
                kept.push_str(&before);
            }
            if i == from.0
                && let Some(n) = &note
            {
                kept.push_str(n);
            }
            if !after.trim().is_empty() {
                kept.push_str(&after);
            }
            self.out[i] = kept;
        }
    }

    /// `spec fn` / `proof fn` items, `broadcast` groups and uses, and `#[verifier::..]` attribute lines.
    fn remove_items(&mut self) {
        let mut i = 0;
        while i < self.lines.len() {
            let (text, col) = self.trimmed(i);
            if text.starts_with("#[verifier") || text.starts_with("#![verifier") {
                let end = self.attribute_end((i, col));
                self.blank((i, col), end, None);
                i = end.0 + 1;
                continue;
            }
            if let Some((kind, name)) = proof_item(&text) {
                let end = self.extent_end((i, col), Extent::Item);
                self.blank((i, col), end, Some(format!("// {kind} {name}: removed in the reading view (see code/)")));
                i = end.0 + 1;
                continue;
            }
            i += 1;
        }
    }

    /// The end of the attribute `#[..]` starting at `from`.
    fn attribute_end(&self, from: Pos) -> Pos {
        let mut depth = 0i64;
        let (mut i, mut j) = from;
        while i < self.mask.len() {
            while j < self.mask[i].len() {
                match self.mask[i][j] {
                    '[' => depth += 1,
                    ']' => {
                        depth -= 1;
                        if depth == 0 {
                            return (i, j + 1);
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            i += 1;
            j = 0;
        }
        from
    }

    /// Proof statements inside executable code.
    fn remove_statements(&mut self) {
        for i in 0..self.lines.len() {
            if self.touched(i) {
                continue;
            }
            let mut j = 0;
            while j < self.mask[i].len() {
                let rest: String = self.mask[i][j..].iter().collect();
                let boundary = j == 0 || !is_ident(self.mask[i][j - 1]);
                if boundary && let Some(kind) = proof_statement(&rest) {
                    let end = self.extent_end((i, j), kind);
                    self.blank((i, j), end, None);
                    break;
                }
                j += 1;
            }
        }
    }

    /// Clauses of executable function headers and loop headers.
    fn rewrite_headers(&mut self) {
        let mut i = 0;
        while i < self.lines.len() {
            if self.touched(i) {
                i += 1;
                continue;
            }
            let (text, col) = self.trimmed(i);
            let header = if exec_fn_start(&text) {
                Some(Header::Function)
            } else if ["while ", "loop", "for "].iter().any(|k| text.starts_with(k)) {
                Some(Header::Loop)
            } else {
                None
            };
            let Some(header) = header else {
                i += 1;
                continue;
            };
            let Some(body) = self.header_end((i, col)) else {
                i += 1;
                continue;
            };
            self.rewrite_clauses(i, body, header);
            i = body.0 + 1;
        }
    }

    /// The position of the body's `{` (or the `;` of a declaration without body) at depth 0 after `from`.
    fn header_end(&self, from: Pos) -> Option<Pos> {
        let mut depth = 0i64;
        let (mut i, mut j) = from;
        while i < self.mask.len() {
            while j < self.mask[i].len() {
                match self.mask[i][j] {
                    '(' | '[' => depth += 1,
                    ')' | ']' => depth -= 1,
                    '{' | ';' if depth == 0 => return Some((i, j)),
                    '{' => depth += 1,
                    '}' => depth -= 1,
                    _ => {}
                }
                j += 1;
            }
            i += 1;
            j = 0;
        }
        None
    }

    /// Rewrite the clause lines between the header start line `start` and its body position `body`.
    fn rewrite_clauses(&mut self, start: usize, body: Pos, header: Header) {
        let mut clause: Option<Clause> = None;
        for i in start..=body.0 {
            let (text, _) = self.trimmed(i);
            if let Some(word) = CLAUSES.iter().find(|w| starts_with_word(&text, w)) {
                clause = Some(header.treatment(word));
            }
            let Some(treatment) = clause else { continue };
            let line: String = self.lines[i].iter().collect();
            let indent: String = line.chars().take_while(|c| c.is_whitespace()).collect();
            // The part of the line that belongs to the clause (before the body's `{` on the last line).
            let (clause_part, tail) = if i == body.0 {
                let chars: Vec<char> = line.chars().collect();
                (chars[..body.1].iter().collect::<String>(), chars[body.1..].iter().collect::<String>())
            } else {
                (line.clone(), String::new())
            };
            let clause_text = clause_part.trim();
            if clause_text.is_empty() {
                continue;
            }
            self.out[i] = match (treatment, tail.is_empty()) {
                (Clause::Comment, true) => format!("{indent}// {clause_text}"),
                (Clause::Comment, false) => format!("{indent}{} // {clause_text}", tail.trim_end()),
                (Clause::Remove, true) => String::new(),
                (Clause::Remove, false) => format!("{indent}{}", tail.trim_end()),
            };
        }
    }
}

#[derive(Clone, Copy)]
enum Header {
    Function,
    Loop,
}

#[derive(Clone, Copy)]
enum Clause {
    Comment,
    Remove,
}

/// Header clause keywords.
const CLAUSES: &[&str] = &["requires", "ensures", "returns", "no_unwind", "recommends", "decreases", "opens_invariants", "invariant_except_break", "invariant"];

impl Header {
    fn treatment(self, word: &str) -> Clause {
        match (self, word) {
            (Header::Function, "requires" | "ensures" | "returns" | "no_unwind") => Clause::Comment,
            _ => Clause::Remove,
        }
    }
}

fn is_ident(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// `text` starts with the word `word` (followed by a non-identifier character or the end).
fn starts_with_word(text: &str, word: &str) -> bool {
    text.strip_prefix(word).is_some_and(|rest| !rest.starts_with(|c: char| is_ident(c)))
}

/// The words of a masked line, with a parenthesized visibility kept as one word (`pub(crate)`).
fn words(text: &str) -> Vec<&str> {
    text.split(|c: char| c.is_whitespace() || c == '<').filter(|w| !w.is_empty()).collect()
}

/// `Some((kind, name))` when the line starts a `spec fn` / `proof fn` item or a `broadcast group` / `broadcast use`.
fn proof_item(text: &str) -> Option<(&'static str, String)> {
    let w = words(text);
    let mut k = 0;
    while k < w.len() && (w[k] == "pub" || w[k].starts_with("pub(") || ["open", "closed", "uninterp", "axiom"].contains(&w[k])) {
        k += 1;
    }
    if w.get(k) == Some(&"broadcast") {
        return match w.get(k + 1) {
            Some(&"group") => Some(("broadcast group", w.get(k + 2).unwrap_or(&"").to_string())),
            Some(&"use") => Some(("broadcast use", String::new())),
            Some(&"proof") if w.get(k + 2) == Some(&"fn") => Some(("proof fn", name_of(w.get(k + 3)))),
            _ => None,
        };
    }
    match (w.get(k), w.get(k + 1)) {
        (Some(&"spec"), Some(&"fn")) => Some(("spec fn", name_of(w.get(k + 2)))),
        (Some(&"proof"), Some(&"fn")) => Some(("proof fn", name_of(w.get(k + 2)))),
        _ => None,
    }
}

fn name_of(word: Option<&&str>) -> String {
    word.map(|w| w.split('(').next().unwrap_or("").to_string()).unwrap_or_default()
}

/// The extent kind when `rest` (masked, from a word boundary) starts a proof statement.
fn proof_statement(rest: &str) -> Option<Extent> {
    let after = |word: &str| rest.strip_prefix(word).map(str::trim_start);
    if after("proof").is_some_and(|r| r.starts_with('{')) {
        return Some(Extent::Statement);
    }
    if let Some(r) = after("assert")
        && (r.starts_with('(') || starts_with_word(r, "forall"))
        && !rest.starts_with("assert_")
    {
        return Some(Extent::Statement);
    }
    if let Some(r) = after("let")
        && (starts_with_word(r, "ghost") || starts_with_word(r, "tracked"))
    {
        return Some(Extent::Statement);
    }
    for call in ["hide", "reveal", "reveal_with_fuel"] {
        if after(call).is_some_and(|r| r.starts_with('(')) && rest.starts_with(call) && !rest[call.len()..].starts_with(|c: char| is_ident(c)) {
            return Some(Extent::Statement);
        }
    }
    None
}

/// Whether a masked line starts an executable function (`fn`, after visibility and qualifiers).
fn exec_fn_start(text: &str) -> bool {
    let w = words(text);
    let mut k = 0;
    while k < w.len() && (w[k] == "pub" || w[k].starts_with("pub(") || ["const", "unsafe", "exec", "async", "extern", "default"].contains(&w[k])) {
        k += 1;
    }
    w.get(k).is_some_and(|f| *f == "fn")
}

/// The lines with every character inside a comment, string literal or character literal replaced by a space.
fn mask_literals_and_comments(lines: &[Vec<char>]) -> Vec<Vec<char>> {
    let mut out = Vec::with_capacity(lines.len());
    let mut in_block_comment = 0usize;
    for line in lines {
        let mut m = line.clone();
        let mut j = 0;
        let mut in_string = false;
        while j < line.len() {
            let c = line[j];
            let next = line.get(j + 1).copied();
            if in_block_comment > 0 {
                if c == '*' && next == Some('/') {
                    in_block_comment -= 1;
                    m[j] = ' ';
                    m[j + 1] = ' ';
                    j += 2;
                    continue;
                }
                if c == '/' && next == Some('*') {
                    in_block_comment += 1;
                }
                m[j] = ' ';
                j += 1;
                continue;
            }
            if in_string {
                m[j] = ' ';
                if c == '\\' {
                    if j + 1 < line.len() {
                        m[j + 1] = ' ';
                    }
                    j += 2;
                    continue;
                }
                if c == '"' {
                    in_string = false;
                }
                j += 1;
                continue;
            }
            match (c, next) {
                ('/', Some('/')) => {
                    for x in m.iter_mut().skip(j) {
                        *x = ' ';
                    }
                    break;
                }
                ('/', Some('*')) => {
                    in_block_comment += 1;
                    m[j] = ' ';
                    m[j + 1] = ' ';
                    j += 2;
                    continue;
                }
                ('"', _) => {
                    in_string = true;
                    m[j] = ' ';
                }
                ('\'', Some('\\')) => {
                    // An escaped character literal: up to the closing quote.
                    let close = (j + 2..line.len()).find(|k| line[*k] == '\'').unwrap_or(line.len() - 1);
                    for x in m.iter_mut().take(close + 1).skip(j) {
                        *x = ' ';
                    }
                    j = close + 1;
                    continue;
                }
                ('\'', Some(_)) if line.get(j + 2) == Some(&'\'') => {
                    m[j] = ' ';
                    m[j + 1] = ' ';
                    m[j + 2] = ' ';
                    j += 3;
                    continue;
                }
                _ => {}
            }
            j += 1;
        }
        // A string literal does not continue past a line end in the masked view (multi-line strings are rare in
        // verified code); the next line starts outside it.
        out.push(m);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::code_view;

    #[test]
    fn proofs_are_removed_and_line_numbers_kept() {
        let code = r#"verus! {
pub open spec fn twice(x: int) -> int {
    x * 2
}

/// Sum of the first `n` values.
pub fn sum(v: &Vec<u64>, n: usize) -> (r: u64)
    requires
        n <= v.len(),
    ensures
        r == total(v@, n),
    decreases n,
{
    let ghost start = v@;
    let mut s: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
        decreases n - i,
    {
        proof {
            lemma_step(v@, i);
        }
        assert(i < v.len()) by {
            lemma_len(v);
        }
        s = s + v[i]; // "{ not a brace"
        i = i + 1;
    }
    hide(twice);
    s
}

proof fn lemma_step(s: Seq<u64>, i: usize)
    ensures true,
{
}
} // verus!"#;
        let view = code_view(code);
        assert_eq!(view.lines().count(), code.lines().count(), "{view}");
        let lines: Vec<&str> = view.lines().collect();
        assert_eq!(lines[1], "// spec fn twice: removed in the reading view (see code/)");
        assert!(lines[2].is_empty() && lines[3].is_empty());
        assert_eq!(lines[6], "pub fn sum(v: &Vec<u64>, n: usize) -> (r: u64)");
        assert_eq!(lines[7], "    // requires");
        assert_eq!(lines[8], "        // n <= v.len(),");
        assert_eq!(lines[10], "        // r == total(v@, n),");
        assert!(lines[11].is_empty(), "function decreases removed");
        assert_eq!(lines[12], "{");
        assert!(lines[13].is_empty(), "ghost let removed");
        assert_eq!(lines[16], "    while i < n");
        assert!(lines[17].is_empty() && lines[18].is_empty() && lines[19].is_empty(), "loop clauses removed");
        assert_eq!(lines[20], "    {");
        assert!(lines[21..27].iter().all(|l| l.is_empty()), "proof block and assert-by removed: {:?}", &lines[21..27]);
        assert_eq!(lines[27], "        s = s + v[i]; // \"{ not a brace\"");
        assert!(lines[30].is_empty(), "hide removed");
        assert_eq!(lines[34], "// proof fn lemma_step: removed in the reading view (see code/)");
        assert_eq!(lines[38], "} // verus!");
    }

    #[test]
    fn a_body_brace_on_a_clause_line_stays_first() {
        let view = code_view("fn f(x: u8) -> (r: u8)\n    ensures r == x, {\n    x\n}");
        assert_eq!(view, "fn f(x: u8) -> (r: u8)\n    { // ensures r == x,\n    x\n}");
    }
}
