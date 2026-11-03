//! Lexical reading of Verus sources: the signature, clauses and body of one `fn` item, the public items of a file,
//! and the contract Verus checked for a recorded item (its own clauses, or those inherited from a trait declaration).
//!
//! Descriptive only. These readers extract text for the author's catalog, the library inventory and records; they
//! never decide admission. Verus's own output (`func-details`) is what establishes that an item was checked, and the
//! stored sources stay the authority for its text. Comments and string/char literals are blanked before any search.

use gendb_verification::obligations::CANDIDATE_CRATE_NAME;
use serde_json::{Value, json};
use std::collections::BTreeSet;

/// `text` with every comment and string/char-literal character replaced by a space (newlines kept), so that searches
/// see only code while character positions stay aligned with `text`.
fn blank_comments_and_literals(text: &str) -> Vec<char> {
    let c: Vec<char> = text.chars().collect();
    let mut out = c.clone();
    let mut i = 0;
    while i < c.len() {
        if c[i] == '/' && c.get(i + 1) == Some(&'/') {
            while i < c.len() && c[i] != '\n' {
                out[i] = ' ';
                i += 1;
            }
        } else if c[i] == '/' && c.get(i + 1) == Some(&'*') {
            // Block comments nest in Rust.
            let mut depth = 0;
            while i < c.len() {
                if c[i] == '/' && c.get(i + 1) == Some(&'*') {
                    depth += 1;
                    out[i] = ' ';
                    out[i + 1] = ' ';
                    i += 2;
                } else if c[i] == '*' && c.get(i + 1) == Some(&'/') {
                    depth -= 1;
                    out[i] = ' ';
                    out[i + 1] = ' ';
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    if c[i] != '\n' {
                        out[i] = ' ';
                    }
                    i += 1;
                }
            }
        } else if c[i] == '\'' && (c.get(i + 2) == Some(&'\'') || (c.get(i + 1) == Some(&'\\') && c.get(i + 3) == Some(&'\''))) {
            // A char literal `'x'` or `'\n'` (a lifetime `'a` has no closing quote here).
            let end = if c[i + 1] == '\\' { i + 3 } else { i + 2 };
            for ch in &mut out[i..=end] {
                *ch = ' ';
            }
            i = end + 1;
        } else if c[i] == '"' {
            out[i] = ' ';
            i += 1;
            while i < c.len() && c[i] != '"' {
                if c[i] == '\\' {
                    out[i] = ' ';
                    i += 1;
                }
                if i < c.len() && c[i] != '\n' {
                    out[i] = ' ';
                }
                i += 1;
            }
            if i < c.len() {
                out[i] = ' ';
            }
            i += 1;
        } else {
            i += 1;
        }
    }
    out
}

/// Code text (comments and literals removed, whitespace kept) of a source.
pub fn code_text(text: &str) -> String {
    blank_comments_and_literals(text).into_iter().collect()
}

fn is_ident_char(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_'
}

/// Whole-word match of `word` at char position `i` of `c`.
fn word_at(c: &[char], i: usize, word: &str) -> bool {
    let w: Vec<char> = word.chars().collect();
    i + w.len() <= c.len()
        && c[i..i + w.len()] == w[..]
        && (i == 0 || !is_ident_char(c[i - 1]))
        && c.get(i + w.len()).is_none_or(|ch| !is_ident_char(*ch))
}

/// Index of the `}` closing the `{` at `open` in blanked `c` (`c.len()` when unbalanced).
fn closing_brace(c: &[char], open: usize) -> usize {
    let (mut depth, mut j) = (0i64, open);
    while j < c.len() {
        match c[j] {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            _ => {}
        }
        j += 1;
    }
    j
}

/// The lexical specification of one `fn` item.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecItem {
    /// From the start of the item's line to its body (signature and clauses).
    pub signature: String,
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
    pub decreases: Vec<String>,
    pub no_unwind: bool,
    /// Body text including braces; `None` for a bodiless declaration (`...;`).
    pub body: Option<String>,
}

/// Keywords that may start the item after a function body; a top-level brace block followed by one of them (or by
/// the end of the text) is the body.
const ITEM_STARTS: [&str; 20] = [
    "pub", "fn", "proof", "spec", "open", "closed", "exec", "struct", "enum", "impl", "trait", "use", "mod", "const", "static", "type", "broadcast",
    "uninterp", "#", "}",
];
/// Clause keywords of a Verus function signature.
const CLAUSE_KEYWORDS: [&str; 8] = ["requires", "ensures", "recommends", "decreases", "returns", "opens_invariants", "no_unwind", "default_ensures"];

/// The unique `fn NAME` of `text` (`None` when absent or not unique). The body is the first top-level brace block that
/// is followed by the end of the item; a top-level `;` first means a declaration.
pub fn spec_item(text: &str, name: &str) -> Option<SpecItem> {
    let c = blank_comments_and_literals(text);
    let starts: Vec<usize> = (0..c.len())
        .filter(|&i| {
            if !word_at(&c, i, "fn") {
                return false;
            }
            let mut j = i + 2;
            while j < c.len() && c[j].is_whitespace() {
                j += 1;
            }
            word_at(&c, j, name)
        })
        .collect();
    let [fn_at] = starts[..] else { return None };
    let line_start = c[..fn_at].iter().rposition(|ch| *ch == '\n').map_or(0, |p| p + 1);
    let (mut depth, mut i, mut body) = (0i64, fn_at, None);
    while i < c.len() {
        match c[i] {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ';' if depth == 0 => {
                body = Some((i, None));
                break;
            }
            '{' if depth == 0 => {
                let end = closing_brace(&c, i);
                let mut next = end + 1;
                while next < c.len() && c[next].is_whitespace() {
                    next += 1;
                }
                let item_follows = next >= c.len()
                    || ITEM_STARTS.iter().any(|w| if *w == "#" || *w == "}" { c[next] == w.chars().next().unwrap() } else { word_at(&c, next, w) });
                if item_follows {
                    body = Some((i, Some(end)));
                    break;
                }
                // A brace block inside the signature (for example a `match` in `ensures`).
                i = end;
            }
            '{' => depth += 1,
            '}' => depth -= 1,
            _ => {}
        }
        i += 1;
    }
    let (body_at, close) = body?;
    let slice = |from: usize, to: usize| text.chars().skip(from).take(to - from).collect::<String>();
    let mut marks = vec![];
    let mut depth = 0i64;
    for i in fn_at..body_at {
        match c[i] {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ if depth == 0 => {
                if let Some(keyword) = CLAUSE_KEYWORDS.iter().find(|k| word_at(&c, i, k)) {
                    marks.push((i, *keyword));
                }
            }
            _ => {}
        }
    }
    let clause = |key: &str| -> Vec<String> {
        marks
            .iter()
            .enumerate()
            .filter(|(_, (_, k))| *k == key)
            .map(|(n, (at, k))| {
                let end = marks.get(n + 1).map_or(body_at, |m| m.0);
                slice(at + k.len(), end).trim().to_string()
            })
            .collect()
    };
    Some(SpecItem {
        signature: slice(line_start, body_at).trim_end().to_string(),
        requires: clause("requires"),
        ensures: clause("ensures"),
        decreases: clause("decreases"),
        no_unwind: marks.iter().any(|(_, k)| *k == "no_unwind"),
        body: close.map(|end| slice(body_at, end + 1)),
    })
}

/// Signature+clauses text, `requires` and `ensures` clause text of the unique `fn NAME` in `text`.
pub fn spec_clauses(text: &str, name: &str) -> Option<(String, Vec<String>, Vec<String>)> {
    spec_item(text, name).map(|s| (s.signature, s.requires, s.ensures))
}

/// `requires` and `ensures` of the unique `fn NAME` in `text` (the clause extractor of admission records).
pub fn requires_ensures(text: &str, name: &str) -> Option<(Vec<String>, Vec<String>)> {
    spec_item(text, name).map(|s| (s.requires, s.ensures))
}

/// The `pub` items of one source with their doc comments and, for functions when `with_clauses`, their signature and
/// clauses: `{"file", "items": [{kind, name, line, signature|text, requires, ensures, decreases?, no_unwind?, doc?}]}`.
/// Re-exports are listed as `{"kind":"re-export","text","line"}`.
pub fn public_items(path: &str, text: &str, with_clauses: bool) -> Value {
    const VISIBILITY_QUALIFIERS: [&str; 4] = ["open ", "closed ", "uninterp ", "broadcast "];
    const KINDS: [&str; 10] = ["spec fn ", "proof fn ", "fn ", "struct ", "enum ", "trait ", "const ", "use ", "type ", "group "];
    let mut items = vec![];
    let mut seen = BTreeSet::new();
    let mut doc: Vec<String> = vec![];
    for (line_index, line) in text.lines().enumerate() {
        let t = line.trim_start();
        if let Some(d) = t.strip_prefix("///") {
            doc.push(d.trim().to_string());
            continue;
        }
        let purpose = std::mem::take(&mut doc).join(" ");
        if t.starts_with("#[") {
            // Attributes sit between an item's doc comment and the item.
            if !purpose.is_empty() {
                doc.push(purpose);
            }
            continue;
        }
        let Some(rest) = t.strip_prefix("pub ") else { continue };
        let rest = rest.trim_start_matches("(crate) ").trim_start_matches("(super) ");
        let rest = VISIBILITY_QUALIFIERS.iter().fold(rest, |r, p| r.strip_prefix(p).unwrap_or(r));
        let Some(kind) = KINDS.iter().find(|p| rest.starts_with(**p)) else { continue };
        let rest = &rest[kind.len()..];
        let kind = kind.trim();
        let name: String = rest.chars().take_while(|c| is_ident_char(*c)).collect();
        let line = line_index + 1;
        if kind == "use" {
            items.push(json!({"kind":"re-export","text":t,"line":line}));
            continue;
        }
        if name.is_empty() || !seen.insert(format!("{kind} {name}")) {
            continue;
        }
        let spec = if with_clauses && kind.ends_with("fn") { spec_item(text, &name) } else { None };
        let mut item = match spec {
            Some(s) => {
                let mut item = json!({"kind":kind,"name":name,"line":line,"signature":s.signature,"requires":s.requires,"ensures":s.ensures});
                if !s.decreases.is_empty() {
                    item["decreases"] = json!(s.decreases);
                }
                if s.no_unwind {
                    item["no_unwind"] = json!(true);
                }
                item
            }
            None => json!({"kind":kind,"name":name,"line":line,"text":t.trim_end_matches('{').trim()}),
        };
        if !purpose.is_empty() {
            item["doc"] = json!(purpose);
        }
        items.push(item);
    }
    json!({"file":path,"items":items})
}

/// Names of the public items of a source (see [`public_items`]).
pub fn public_item_names(text: &str) -> Vec<String> {
    public_items("", text, false)["items"].as_array().into_iter().flatten().filter_map(|i| i["name"].as_str().map(String::from)).collect()
}

/// Public item names of the framework toolkit files (`link/**`, `gendb_entry/**`, `gendb_source.rs`) that `agent_text`
/// mentions (names longer than three characters, lexical and descriptive; qualification records them).
pub fn referenced_framework_helpers(framework: &[gendb_verification::verus::FrameworkSource], agent_text: &str) -> Vec<String> {
    let mut used: Vec<String> = framework
        .iter()
        .filter(|f| f.path.starts_with("link/") || f.path.starts_with("gendb_entry/") || f.path == "gendb_source.rs")
        .flat_map(|f| public_item_names(&f.text))
        .filter(|name| name.len() > 3 && agent_text.contains(name.as_str()))
        .collect();
    used.sort();
    used.dedup();
    used
}

/// The leading `//!` lines of a file, joined.
pub fn module_doc(text: &str) -> String {
    text.lines()
        .take_while(|l| l.starts_with("//!") || l.trim().is_empty())
        .filter_map(|l| l.strip_prefix("//!"))
        .map(str::trim)
        .collect::<Vec<_>>()
        .join(" ")
}

/// Full text of the first item introduced by `head` (for example `pub enum Answer`) up to its closing brace, with the
/// doc comment lines directly above it.
pub fn item_text(text: &str, head: &str) -> Option<String> {
    let start = text.find(head)?;
    let open = start + text[start..].find('{')?;
    let mut depth = 0i32;
    for (i, ch) in text[open..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    let doc_bytes = text[..start].lines().rev().take_while(|l| l.trim_start().starts_with("///")).map(|l| l.len() + 1).sum::<usize>();
                    return Some(text[start - doc_bytes.min(start)..open + i + 1].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

/// Last path identifier of a type or trait text (`gendb_entry::parallel::WorkerTask<X>` -> `WorkerTask`).
fn last_ident(text: &str) -> String {
    let head = text.split('<').next().unwrap_or_default().trim().trim_start_matches('&').trim();
    head.rsplit("::").next().unwrap_or_default().trim().to_string()
}

/// One item-level `impl` or `trait` block.
struct Block {
    /// The implemented trait of `impl Trait for Type`; `None` for an inherent impl or a trait declaration.
    trait_name: Option<String>,
    /// The implementing type, or the declared trait's name.
    subject: String,
    text: String,
}

/// Item-level blocks introduced by `keyword` (`impl` or `trait`). An `impl` names a trait when its header has a
/// top-level `for`.
fn item_blocks(text: &str, keyword: &str) -> Vec<Block> {
    let c = blank_comments_and_literals(text);
    let mut out = vec![];
    for i in 0..c.len() {
        if !word_at(&c, i, keyword) {
            continue;
        }
        let line_start = c[..i].iter().rposition(|ch| *ch == '\n').map_or(0, |p| p + 1);
        let lead: String = c[line_start..i].iter().collect();
        if !["", "pub", "pub(crate)", "unsafe", "pub unsafe"].contains(&lead.trim()) {
            continue;
        }
        let Some(open) = (i..c.len()).find(|j| matches!(c[*j], '{' | ';')).filter(|j| c[*j] == '{') else { continue };
        let mut header: String = c[i + keyword.len()..open].iter().collect();
        if let Some(at) = header.find(" where") {
            header.truncate(at);
        }
        let mut header = header.trim();
        if header.starts_with('<') {
            // Skip the generic parameter list of `impl<...>`.
            let mut depth = 0;
            let cut = header.char_indices().find(|(_, ch)| {
                depth += match ch {
                    '<' => 1,
                    '>' => -1,
                    _ => 0,
                };
                depth == 0
            });
            header = cut.map_or("", |(at, _)| header[at + 1..].trim());
        }
        if keyword == "trait" {
            header = header.split([':', '<']).next().unwrap_or_default().trim();
        }
        let hc: Vec<char> = header.chars().collect();
        let split = (0..hc.len()).find(|j| word_at(&hc, *j, "for"));
        let (trait_name, subject) = match split {
            Some(at) if keyword == "impl" => (Some(last_ident(&hc[..at].iter().collect::<String>())), last_ident(&hc[at + 3..].iter().collect::<String>())),
            _ => (None, last_ident(header)),
        };
        out.push(Block { trait_name, subject, text: text.chars().skip(open).take(closing_brace(&c, open) + 1 - open).collect() });
    }
    out
}

/// One checked source file of a build, for contract resolution.
pub struct ItemSource {
    /// Path under the crate's `src/`.
    pub path: String,
    pub text: String,
    /// Where the text is stored (library blob or frozen file).
    pub provenance: Value,
}

/// Module path of a file under the crate's `src/` (`agent/mod.rs` -> `agent`).
fn file_module_path(file: &str) -> String {
    let mut parts: Vec<&str> = file.trim_end_matches(".rs").split('/').collect();
    if parts.len() > 1 && parts.last() == Some(&"mod") {
        parts.pop();
    }
    parts.join("::")
}

/// The item role the fixed entry gives an agent item it calls (`crate::agent::{decode, build, query}`).
fn entry_item_role(name: &str) -> Option<&'static str> {
    match name {
        "decode" => Some("representation_abstraction"),
        "build" => Some("representation_builder"),
        "query" => Some("query"),
        _ => None,
    }
}

/// What one recorded item is and what contract Verus checked for it, resolved from the build's own sources:
/// - `module_role` is the declared role of the whole file (author-declared for agent files);
/// - `item_role` is inferred only from a fixed interface (the entry's `agent::decode/build/query`, or a method of an
///   `impl Trait for Type` whose trait is declared in the build); otherwise `unspecified`;
/// - `contract.status` is `direct` (the item's own clauses), `inherited` (a trait-impl method: its own clauses plus the
///   trait declaration's `requires`/`ensures`/`no_unwind` and the impl's definitions of the trait's spec functions)
///   or `unresolved` (not placed lexically; unknown, never "no requirements").
pub fn describe_item(sources: &[ItemSource], file: &str, module_role: &str, path: &str) -> Value {
    let module = file_module_path(file);
    let relative = path.strip_prefix(&format!("{CANDIDATE_CRATE_NAME}::{module}::")).unwrap_or(path);
    let (ty, method) = match relative.rsplit_once("::") {
        Some((ty, method)) => (Some(last_ident(ty)), method),
        None => (None, relative),
    };
    let mut item_role = match (module.as_str(), ty.as_ref(), entry_item_role(method)) {
        ("agent", None, Some(role)) => json!({"role":role,"justification":format!("called by the fixed entry as crate::agent::{method}")}),
        _ => json!({"role":"unspecified"}),
    };
    let describe = |item_role: Value, contract: Value| {
        json!({"path":path,"module":file,"module_role":module_role,"item_role":item_role,"contract":contract,
            "resolution":"lexical over the build's stored checked sources; Verus checked the item itself"})
    };
    let unresolved = |reason: String| json!({"status":"unresolved","reason":reason});
    let Some(source) = sources.iter().find(|s| s.path == file) else {
        return describe(item_role, unresolved(format!("{file} is not among the build's sources")));
    };
    // A method: the unique impl block of its type that defines it.
    let owner = match &ty {
        None => None,
        Some(ty) => {
            let blocks: Vec<Block> = item_blocks(&source.text, "impl").into_iter().filter(|b| &b.subject == ty && spec_item(&b.text, method).is_some()).collect();
            match <[Block; 1]>::try_from(blocks) {
                Ok([block]) => Some(block),
                Err(_) => return describe(item_role, unresolved(format!("no unique impl block of {ty} with `fn {method}` in {file}"))),
            }
        }
    };
    let scope = owner.as_ref().map_or(source.text.as_str(), |b| b.text.as_str());
    let Some(own) = spec_item(scope, method) else {
        return describe(item_role, unresolved(format!("`fn {method}` is not unique in {file}")));
    };
    let direct = json!({"signature":own.signature,"requires":own.requires,"ensures":own.ensures,"no_unwind":own.no_unwind,"source":source.provenance});
    let Some(Block { trait_name: Some(trait_name), subject: ty, text: impl_block }) = owner else {
        return describe(item_role, json!({"status":"direct","direct":direct}));
    };
    let declarations: Vec<(&ItemSource, String)> = sources
        .iter()
        .flat_map(|s| item_blocks(&s.text, "trait").into_iter().filter(|b| b.subject == trait_name).map(move |b| (s, b.text)))
        .collect();
    let [(declared_in, trait_block)] = &declarations[..] else {
        return describe(item_role, json!({"status":"unresolved","direct":direct,
            "reason":format!("trait {trait_name} is not declared exactly once in the build's sources; its inherited clauses are unknown here, not absent")}));
    };
    let Some(declared) = spec_item(trait_block, method) else {
        return describe(item_role, json!({"status":"unresolved","direct":direct,"reason":format!("`fn {method}` is not unique in trait {trait_name}")}));
    };
    item_role = json!({"role":"trait_method","trait":trait_name,"trait_source":declared_in.path,
        "justification":format!("method of `impl {trait_name} for {ty}`; the trait declaration fixes its contract")});
    // The trait's spec functions, as the impl block defines them.
    let tc = blank_comments_and_literals(trait_block);
    let spec_names: Vec<String> = (0..tc.len())
        .filter(|i| word_at(&tc, *i, "spec"))
        .filter_map(|i| {
            let rest: String = tc[i + 4..].iter().collect();
            let rest = rest.trim_start().strip_prefix("fn")?;
            let name: String = rest.trim_start().chars().take_while(|ch| is_ident_char(*ch)).collect();
            (!name.is_empty()).then_some(name)
        })
        .collect();
    let mut complete = true;
    let binding: Vec<Value> = spec_names
        .iter()
        .map(|name| match spec_item(&impl_block, name) {
            Some(definition) => json!({"name":name,"signature":definition.signature,"definition":definition.body}),
            None => {
                complete = false;
                json!({"name":name,"definition":null,"reason":"not defined in the impl block (trait default or not placed lexically)"})
            }
        })
        .collect();
    describe(item_role, json!({"status":if complete {"inherited"} else {"unresolved"},"direct":direct,
        "inherited":{"trait":trait_name,"source":declared_in.provenance,"signature":declared.signature,
            "requires":declared.requires,"ensures":declared.ensures,"no_unwind":declared.no_unwind},
        "binding":{"impl":format!("impl {trait_name} for {ty}"),"source":source.provenance,"spec_functions":binding}}))
}

#[cfg(test)]
mod tests {

    /// Every storage entry's recorded items are found by the extractor publication uses (a missing name would refuse
    /// every package of that entry at publication).
    #[test]
    fn every_storage_entry_records_its_items_with_the_real_extractor() {
        use gendb_verification::obligations::{STORAGE_ENTRY_DERIVED, STORAGE_ENTRY_DERIVED_V2, STORAGE_ENTRY_V1, STORAGE_ENTRY_V2};
        for entry in [STORAGE_ENTRY_V1, STORAGE_ENTRY_V2, STORAGE_ENTRY_DERIVED, STORAGE_ENTRY_DERIVED_V2] {
            for item in entry.recorded_items {
                let (requires, ensures) = super::requires_ensures(entry.source, item).unwrap_or_else(|| panic!("{}: {item}", entry.name));
                assert!(!requires.is_empty() || !ensures.is_empty(), "{}: {item} has clauses", entry.name);
            }
        }
    }
    use super::*;

    #[test]
    fn spec_clause_text_is_extracted_around_match_blocks() {
        let text = "verus! {\n// fn query in a comment\npub fn query(parts: &[Part], w: usize) -> (r: Result<u8, E>)\n    requires\n        w >= 1, // note {\n    ensures\n        match r { Ok(v) => v > 0, Err(_) => true },\n{\n    let x = \"{\";\n    Ok(1)\n}\n\npub open spec fn decode(p: Seq<u8>) -> Option<u8> { None }\n}\n";
        let (signature, requires, ensures) = spec_clauses(text, "query").unwrap();
        assert!(signature.starts_with("pub fn query") && signature.ends_with("Err(_) => true },"));
        assert_eq!(requires, ["w >= 1, // note {"]);
        assert_eq!(ensures, ["match r { Ok(v) => v > 0, Err(_) => true },"]);
        let (decode, r, e) = spec_clauses(text, "decode").unwrap();
        assert_eq!((decode.as_str(), r.len(), e.len()), ("pub open spec fn decode(p: Seq<u8>) -> Option<u8>", 0, 0));
        assert!(spec_clauses(text, "absent").is_none());
        let entry = spec_clauses(gendb_verification::obligations::ENTRY_SOURCE, "abi_query").unwrap();
        assert!(!entry.1.is_empty() && !entry.2.is_empty(), "{entry:?}");
    }

    #[test]
    fn item_text_and_public_items_extract_items() {
        let text = "/// doc\npub enum Answer {\n    Rows(u8),\n    Capacity,\n}\n/// f doc\npub open spec fn f(x: int) -> bool\n    recommends x > 0,\n{ x > 1 }\n";
        assert_eq!(item_text(text, "pub enum Answer").unwrap(), "/// doc\npub enum Answer {\n    Rows(u8),\n    Capacity,\n}");
        let items = public_items("x.rs", text, true);
        assert_eq!(items["items"][1]["name"], "f");
        assert_eq!(items["items"][1]["doc"], "f doc");
        assert_eq!(public_item_names(text), ["Answer", "f"]);
    }

    #[test]
    fn trait_method_contract_is_inherited_from_the_declaration() {
        let framework = "pub trait WorkerTask {\n    spec fn pre(&self) -> bool;\n    fn run(self) -> (out: u8)\n        requires self.pre(),\n        no_unwind;\n}\n";
        let agent = "struct SumTask { lo: usize }\nimpl WorkerTask for SumTask {\n    open spec fn pre(&self) -> bool { self.lo == 0 }\n    fn run(self) -> (out: u8) { 0 }\n}\n";
        let sources = [
            ItemSource { path: "gendb_entry/parallel.rs".into(), text: framework.into(), provenance: json!("framework") },
            ItemSource { path: "agent/mod.rs".into(), text: agent.into(), provenance: json!("agent") },
        ];
        let item = describe_item(&sources, "agent/mod.rs", "entry", "gendb_query::agent::SumTask::run");
        assert_eq!(item["contract"]["status"], "inherited", "{item:#}");
        assert_eq!(item["contract"]["inherited"]["requires"], json!(["self.pre(),"]));
        assert_eq!(item["contract"]["inherited"]["no_unwind"], true);
        assert!(item["contract"]["binding"]["spec_functions"][0]["definition"].as_str().unwrap().contains("self.lo == 0"));
        assert_eq!(item["item_role"]["role"], "trait_method");
        let missing = describe_item(&sources, "agent/other.rs", "helper", "gendb_query::agent::other::f");
        assert_eq!(missing["contract"]["status"], "unresolved");
    }
}
