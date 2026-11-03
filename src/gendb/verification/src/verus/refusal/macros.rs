//! The macro policy of author code: which macros may be invoked, which derives may be used, and which names a `use`
//! may not bind.
//!
//! Author code cannot define macros (`macro_rules!` is refused, `macro` needs a refused `#![feature]`), so every macro
//! it can reach comes from the pinned toolchain (std, core, alloc, vstd), under its own name or under a `use` rename.
//! Framework Verus sources define and re-export no macros. Three checks close the set:
//! - an invocation `NAME!(..)`/`NAME![..]`/`NAME!{..}` (plain or path-qualified) must name a [`SUPPORTED_MACROS`] entry;
//!   `verus!` is allowed only at the top level (checked by the top-level rule);
//! - a derive must be a plain [`SUPPORTED_DERIVES`] name;
//! - a `use` may not bind (as its last segment or its `as` alias) a supported macro, derive or attribute name, or a
//!   word that the scan treats as a keyword before `!` ([`NOT_MACRO_WORDS`]). Without this, `use std::module_path as
//!   seq;` would make `seq!()` expand to the crate's module path, and `use std::module_path as r#if;` (the lexer reads
//!   `r#if` as `if`) would hide an invocation behind a keyword.
//!
//! So a supported name always denotes the toolchain's own macro. The supported expansions were audited on the pinned
//! toolchain (`rust_verify -Zunpretty=expanded`): `seq!` is `View::view` of an array
//! literal, `set!`/`map!` are `empty().insert(..)` chains on vstd types, `vec!` is alloc's boxed-array conversion, and
//! the derives implement their std trait for the annotated type only. None of them depends on the source location,
//! the environment or the configuration, and none adds an implementation to another type.

use super::super::lexer::{group_end, Tok, Token};
use super::{rule, Findings, ALLOWED_ATTRIBUTES};

/// Macros author code may invoke inside `verus!`.
pub const SUPPORTED_MACROS: &[&str] = &["seq", "set", "map", "vec"];

/// Derives author code may use: the ones admitted code uses whose expansions call only what Verus tracks. A derived
/// `Clone` calls its fields' `clone` (a cycle through a manual `Clone` is refused by Verus); a derived `PartialEq`
/// compares fields structurally and can call back into author code only through a manual `PartialEq` impl, which the
/// trait allowlist refuses ([`super::traits`]). `Debug` (a fmt trait std calls without its preconditions) and every
/// other derive are refused.
pub const SUPPORTED_DERIVES: &[&str] = &["Clone", "Copy", "PartialEq", "Eq"];

/// Words that may stand before `!(`, `![` or `!{` without invoking a macro: Rust keywords (`if !(a)`, `return
/// !b`) and Verus clause words (`requires !(x)`, `.. implies !(p) by ..`). None of them is a toolchain macro (checked
/// on the pinned toolchain); a `use` may not bind them.
pub(super) const NOT_MACRO_WORDS: &[&str] = &[
    // Rust strict and reserved keywords.
    "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn", "for", "if", "impl", "in", "let",
    "loop", "match", "mod", "move", "mut", "pub", "ref", "return", "self", "Self", "static", "struct", "super", "trait",
    "true", "type", "unsafe", "use", "where", "while", "async", "await", "dyn", "abstract", "become", "box", "do", "final",
    "macro", "override", "priv", "typeof", "unsized", "virtual", "yield", "try",
    // Verus clause and operator words.
    "implies", "requires", "ensures", "recommends", "invariant", "invariant_except_break", "decreases", "returns",
    "when", "via", "opens_invariants", "no_unwind", "default_ensures", "by",
];

/// The macro name invoked at `i`, if `tokens[i]` starts an invocation: `NAME !` followed by a delimiter group, or
/// `macro_rules !` in any form.
fn invocation_at(tokens: &[Token], i: usize) -> Option<&str> {
    let name = tokens[i].ident()?;
    if !tokens.get(i + 1).is_some_and(|t| t.is_punct('!')) {
        return None;
    }
    if name == "macro_rules" {
        return Some(name);
    }
    let group = tokens.get(i + 2).is_some_and(|t| matches!(t.tok, Tok::Punct('(' | '[' | '{')));
    (group && !NOT_MACRO_WORDS.contains(&name)).then_some(name)
}

/// Every invocation of a macro outside [`SUPPORTED_MACROS`], anywhere (attributes included). A top-level `verus!`
/// (brace depth 0) is the file's verified code and is checked by the top-level rule.
pub(super) fn check_invocations(tokens: &[Token], findings: &mut Findings) {
    let mut depth = 0usize;
    for (i, token) in tokens.iter().enumerate() {
        match token.tok {
            Tok::Punct('{') => depth += 1,
            Tok::Punct('}') => depth = depth.saturating_sub(1),
            _ => {}
        }
        let Some(name) = invocation_at(tokens, i) else { continue };
        let top_level_verus = name == "verus" && depth == 0;
        if !top_level_verus && !SUPPORTED_MACROS.contains(&name) {
            findings.refuse(token.line, rule::MACRO, format!("`{name}!` is not a supported macro (supported: {})", SUPPORTED_MACROS.join(", ")));
        }
    }
}

/// The derives of a `derive(...)` attribute body (`body[0]` is `derive`): `None` names the finding.
pub(super) fn check_derive(body: &[Token], line: usize, findings: &mut Findings) {
    let list = match body.get(1) {
        Some(t) if t.is_punct('(') => &body[2..group_end(body, 1).saturating_sub(1).max(2)],
        _ => {
            findings.refuse(line, rule::ATTRIBUTE, "`derive` without a parenthesized list".into());
            return;
        }
    };
    for item in list.split(|t| t.is_punct(',')).filter(|item| !item.is_empty()) {
        match item {
            [t] if t.ident().is_some_and(|name| SUPPORTED_DERIVES.contains(&name)) => {}
            _ => findings.refuse(
                line,
                rule::ATTRIBUTE,
                format!("only the derives {} are supported, written by their plain names", SUPPORTED_DERIVES.join(", ")),
            ),
        }
    }
}

/// Whether a `use` may not bind `name`.
fn reserved(name: &str) -> bool {
    SUPPORTED_MACROS.contains(&name)
        || SUPPORTED_DERIVES.contains(&name)
        || ALLOWED_ATTRIBUTES.contains(&name)
        || NOT_MACRO_WORDS.contains(&name)
        || matches!(name, "verus" | "macro_rules")
}

/// One name a `use` declaration binds: `name`, the last segment of the imported path or its `as` alias, and
/// `imported`, that last segment (`a::{self}` and `a::{self as b}` import `a`).
pub(super) struct UseBinding {
    pub name: String,
    pub imported: String,
}

/// Every `use` declaration (at any depth), by line: the names it binds, `None` if the scan cannot read its tree.
pub(super) fn use_declarations(tokens: &[Token]) -> Vec<(usize, Option<Vec<UseBinding>>)> {
    let mut declarations = Vec::new();
    for (i, token) in tokens.iter().enumerate() {
        // `use<..>` is a precise-capturing bound in an `impl Trait` type, not an import.
        if token.ident() != Some("use") || tokens.get(i + 1).is_some_and(|t| t.is_punct('<')) {
            continue;
        }
        let end = (i + 1..tokens.len()).find(|&j| tokens[j].is_punct(';')).unwrap_or(tokens.len());
        // Verus `broadcast use a::x, b::y;` lists several paths without braces.
        let trees: Option<Vec<Vec<UseBinding>>> = split_top_level(&tokens[i + 1..end]).into_iter().map(use_tree_bindings).collect();
        declarations.push((token.line, trees.map(|trees| trees.into_iter().flatten().collect())));
    }
    declarations
}

/// Every `use` declaration that binds a reserved name, or whose tree the scan cannot read.
pub(super) fn check_imports(tokens: &[Token], findings: &mut Findings) {
    for (line, bindings) in use_declarations(tokens) {
        match bindings {
            Some(bindings) => {
                for binding in bindings.into_iter().filter(|binding| reserved(&binding.name)) {
                    findings.refuse(
                        line,
                        rule::MACRO_IMPORT,
                        format!("`use` binds `{}`, a supported macro, derive or attribute name or a keyword of the scan", binding.name),
                    );
                }
            }
            None => findings.refuse(line, rule::MACRO_IMPORT, "`use` declaration the scan cannot read".into()),
        }
    }
}

/// The names a use tree binds (`None` if the tokens are not a use tree): the last segment of each imported path, or
/// its `as` alias (none for `as _` and globs); `a::{self}` binds `a`.
fn use_tree_bindings(tree: &[Token]) -> Option<Vec<UseBinding>> {
    let mut bindings = Vec::new();
    let mut last_segment: Option<&str> = None;
    let mut i = 0;
    if tree.first().is_some_and(|t| t.tok == Tok::Op("::")) {
        i = 1;
    }
    loop {
        let token = tree.get(i)?;
        if token.is_punct('*') {
            return (i + 1 == tree.len()).then_some(bindings);
        }
        if token.is_punct('{') {
            let close = group_end(tree, i);
            if close != tree.len() || !tree[close - 1].is_punct('}') {
                return None;
            }
            for item in split_top_level(&tree[i + 1..close - 1]) {
                let mut inner = use_tree_bindings(item)?;
                // `self` inside a group imports, and without an alias binds, the enclosing module's name.
                for binding in inner.iter_mut().filter(|binding| binding.imported == "self") {
                    if binding.name == "self" {
                        binding.name = last_segment?.to_string();
                    }
                    binding.imported = last_segment?.to_string();
                }
                bindings.append(&mut inner);
            }
            return Some(bindings);
        }
        let name = token.ident()?;
        match tree.get(i + 1) {
            None => {
                bindings.push(UseBinding { name: name.to_string(), imported: name.to_string() });
                return Some(bindings);
            }
            Some(t) if t.tok == Tok::Op("::") => {
                last_segment = Some(name);
                i += 2;
            }
            Some(t) if t.ident() == Some("as") && tree.len() == i + 3 => {
                let alias = tree[i + 2].ident()?;
                if alias != "_" {
                    bindings.push(UseBinding { name: alias.to_string(), imported: name.to_string() });
                }
                return Some(bindings);
            }
            Some(_) => return None,
        }
    }
}

/// The comma-separated items of a group's contents, split at nesting depth 0 (empty items dropped).
fn split_top_level(tokens: &[Token]) -> Vec<&[Token]> {
    let mut items = Vec::new();
    let (mut start, mut i) = (0, 0);
    while i < tokens.len() {
        if matches!(tokens[i].tok, Tok::Punct('(' | '[' | '{')) {
            i = group_end(tokens, i);
            continue;
        }
        if tokens[i].is_punct(',') {
            items.push(&tokens[start..i]);
            start = i + 1;
        }
        i += 1;
    }
    items.push(&tokens[start..]);
    items.into_iter().filter(|item| !item.is_empty()).collect()
}

#[cfg(test)]
mod tests {
    use super::super::{rule, scan_source};

    fn findings(src: &str, rule: &str) -> usize {
        scan_source("m.rs", src).iter().filter(|f| f.rule == rule).count()
    }

    #[test]
    fn supported_macros_derives_and_keyword_negations_pass() {
        let src = r#"use vstd::prelude::*;
use crate::link::grouped as grp;
use crate::a::{b, c::{self as cc, d}, e as _};
verus! {
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct P { x: u8 }
spec fn s() -> Seq<int> { seq![1int, 2] }
spec fn t() -> Set<int> { set![1int] }
spec fn m() -> Map<int, int> { map![1int => 2int] }
fn v(b: bool) -> (r: Vec<u8>) requires !(b && !b), ensures !(r@.len() == 0) {
    if !(b) { return vec![0u8; 2]; }
    vec![1u8]
}
proof fn q(a: bool) { assert forall|i: int| 0 <= i implies !(i < 0) by {} }
proof fn r() { broadcast use vstd::layout::layout_of_slices, vstd::layout::layout_of_primitives; }
fn w(x: impl Fn(u8) -> u8 + use<>) {}
}
"#;
        // The `impl Fn` type is refused by the impl-Trait rule; its `use<>` is not read as an import.
        let all: Vec<_> = scan_source("m.rs", src).into_iter().filter(|f| f.rule != rule::IMPL_TRAIT_TYPE).collect();
        assert!(all.is_empty(), "{all:?}");
    }

    #[test]
    fn unsupported_invocations_are_refused_plain_qualified_or_renamed() {
        for src in [
            "verus! { spec fn f() -> bool { module_path!()@.len() == 0 } }",
            "verus! { spec fn f() -> bool { std::module_path!()@.len() == 0 } }",
            "verus! { spec fn f() -> bool { file!()@.len() == 0 } }",
            "verus! { spec fn f() -> nat { line!() as nat } }",
            "verus! { spec fn f() -> bool { stringify!(x)@.len() == 1 } }",
            "use std::module_path as mp;\nverus! { spec fn f() -> bool { mp!()@.len() == 0 } }",
            "verus! { fn f() { let s = include_str!(\"/etc/x\"); } }",
            "verus! { #[doc = include_str!(\"x\")] fn f() {} }",
            "verus! { verus! { fn f() {} } }",
            "macro_rules! m { () => {} }",
            "verus! { proof fn f() { calc! { (==) 1int; {} 1int; } } }",
        ] {
            assert_eq!(findings(src, rule::MACRO), 1, "{src}");
        }
    }

    /// `use std::module_path as seq;` would make `seq!()` name the crate (S1c probe P9): every binding of a supported or
    /// scan-keyword name is refused, whatever it imports.
    #[test]
    fn imports_binding_reserved_names_are_refused() {
        for (src, count) in [
            ("use std::module_path as seq;", 1),
            ("use std::file as vec;", 1),
            ("use vstd::prelude::seq;", 1),
            ("use std::module_path as r#if;", 1),
            ("use a::{b as implies, c::{self as requires}};", 2),
            ("use some::Derive as Clone;", 1),
            ("use other::attr as inline;", 1),
            ("verus! { fn f() { use std::module_path as map; } }", 1),
            ("pub(crate) use std::module_path as set;", 1),
            ("use a::b::{self, c} as d;", 1),
            ("verus! { proof fn f() { broadcast use vstd::layout::group_a, vstd::seq::seq; } }", 1),
        ] {
            assert_eq!(findings(src, rule::MACRO_IMPORT), count, "{src}");
        }
    }

    #[test]
    fn only_supported_plain_derives() {
        assert_eq!(findings("verus! { #[derive(Clone, Hash)] struct S; }", rule::ATTRIBUTE), 1);
        assert_eq!(findings("verus! { #[derive(Debug)] struct S; }", rule::ATTRIBUTE), 1);
        assert_eq!(findings("verus! { #[derive(Clone, Copy, PartialEq, Eq)] struct S; }", rule::ATTRIBUTE), 0);
        assert_eq!(findings("verus! { #[derive(std::clone::Clone)] struct S; }", rule::ATTRIBUTE), 1);
        assert_eq!(findings("verus! { #[derive] struct S; }", rule::ATTRIBUTE), 1);
        assert_eq!(findings("verus! { #[derive(Clone, Copy,)] struct S; }", rule::ATTRIBUTE), 0);
    }
}
