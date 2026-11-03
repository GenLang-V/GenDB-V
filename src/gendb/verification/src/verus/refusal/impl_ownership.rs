//! Implementation ownership: every `impl` block of an author file implements something the file owns.
//!
//! Rust resolves methods and trait items through every `impl` block of the crate. An author `impl` for a type or trait
//! that other code can name can therefore change what that code means, without changing its text: an inherent `view`
//! for a framework type takes precedence over its `View` implementation at every `x@` in the SQLSpec library, and a
//! method a storage interface calls can be supplied differently by a storage crate's builder and a query crate's query
//! module (both verified in S1c probes P1-P4, P7, P8). Author roots are `builder/**`, `stores/<name>/interface/**` and
//! `agent/**`; a storage interface lies outside the closure of every other storage, so the rule applies to all of them.
//!
//! An `impl` block is accepted exactly when:
//! 1. it is an item at the top level of the file's `verus!` block (brace depth 1): not nested in an inline module
//!    (Verus itself refuses items inside function bodies);
//! 2. its header is `impl<..>? Name<..>?` or `impl<..>? Trait<..>? for SelfType` (a single `for`, no `!`);
//! 3. either the self type is a plain `Name<..>?` of a struct, enum or union defined at the top level of the same file
//!    (with any trait the trait allowlist accepts: `View`, `WorkerTask`, `Clone`, `Copy` or an own trait), or the trait
//!    is a plain `Trait<..>?` defined at the top level of the same file (any self type: such a trait is never in scope
//!    in code outside the author's root);
//! 4. that name is not one of the impl's own generic parameters (`impl<T> View for T` next to a `struct T`).
//!
//! A plain name at file scope denotes the local definition: a same-name `use` in that module is a compile error
//! (E0255) and glob imports are shadowed by it. Type aliases do not count (`type L = Other; impl L` implements
//! `Other`). Headers the scan cannot read (references, tuples, qualified paths, const-block arguments, higher-ranked
//! `for<..>`) are refused. This is a lexical check, not a Rust proof. Which traits may be implemented at all is the
//! trait allowlist's rule ([`super::traits`]), which reads the same headers ([`impl_items`]).

use super::super::lexer::{Tok, Token};
use super::{rule, Findings};
use std::collections::BTreeSet;

/// Names of structs, enums, unions and traits defined at the top level (brace depth 1) of a file.
pub(super) struct FileOwned {
    pub types: BTreeSet<String>,
    pub traits: BTreeSet<String>,
}

/// One `impl` block (an `impl` keyword that is not in a type): its line, whether it is at the top level of the file's
/// `verus!` block (brace depth 1), and its header after `impl` up to the body.
pub(super) struct ImplItem<'a> {
    pub line: usize,
    pub top_level: bool,
    pub header: &'a [Token],
}

/// A readable `impl` header: the impl's own generic parameter names, the trait path (`None` for an inherent impl) and
/// the self type, both without the where clause.
pub(super) struct ImplHeader<'a> {
    pub parameters: BTreeSet<&'a str>,
    pub trait_path: Option<&'a [Token]>,
    pub self_type: &'a [Token],
}

/// Every `impl` block of the file, in order.
pub(super) fn impl_items(tokens: &[Token]) -> Vec<ImplItem<'_>> {
    let mut items = Vec::new();
    let mut depth = 0usize;
    for (i, token) in tokens.iter().enumerate() {
        match token.tok {
            Tok::Punct('{') => depth += 1,
            Tok::Punct('}') => depth = depth.saturating_sub(1),
            _ => {}
        }
        if token.ident() == Some("impl") && !in_type_position(tokens, i) {
            items.push(ImplItem { line: token.line, top_level: depth == 1, header: impl_header(&tokens[i + 1..]) });
        }
    }
    items
}

pub(super) fn check_impls(tokens: &[Token], findings: &mut Findings) {
    let owned = file_owned(tokens);
    for item in impl_items(tokens) {
        if !item.top_level {
            findings.refuse(item.line, rule::IMPL_OWNERSHIP, "an `impl` block must be at the top level of the file's `verus!` block".into());
            continue;
        }
        if let Err(reason) = parse_header(item.header).and_then(|header| check_ownership(&header, &owned)) {
            findings.refuse(item.line, rule::IMPL_OWNERSHIP, reason);
        }
    }
}

/// `impl` in a type (`x: impl Fn()`, `-> impl View`, `Vec<impl T>`, `&impl T`, `&mut impl T`, `&'a impl T`,
/// `*const impl T`) rather than an item.
pub(super) fn in_type_position(tokens: &[Token], i: usize) -> bool {
    let Some(previous) = i.checked_sub(1).map(|p| &tokens[p]) else { return false };
    let lifetime = i >= 2 && tokens[i - 2].is_punct('\'');
    match &previous.tok {
        Tok::Op(op) => matches!(*op, "->" | "&&"),
        Tok::Punct(c) => matches!(c, ':' | '(' | ',' | '<' | '&' | '=' | '+' | '[' | '|'),
        Tok::Ident(word) => lifetime || matches!(word.as_str(), "mut" | "dyn" | "const"),
        Tok::Literal => false,
    }
}

/// A definition keyword at `i` starts an item: first token, after an item boundary or a visibility.
fn starts_item(tokens: &[Token], i: usize) -> bool {
    match i.checked_sub(1).map(|p| &tokens[p].tok) {
        None => true,
        Some(Tok::Punct('{' | '}' | ';' | ']' | ')')) => true,
        Some(Tok::Ident(word)) => word == "pub",
        _ => false,
    }
}

pub(super) fn file_owned(tokens: &[Token]) -> FileOwned {
    let mut owned = FileOwned { types: BTreeSet::new(), traits: BTreeSet::new() };
    let mut depth = 0usize;
    for (i, token) in tokens.iter().enumerate() {
        match &token.tok {
            Tok::Punct('{') => depth += 1,
            Tok::Punct('}') => depth = depth.saturating_sub(1),
            Tok::Ident(keyword) if depth == 1 && starts_item(tokens, i) => {
                let Some(name) = tokens.get(i + 1).and_then(Token::ident) else { continue };
                match keyword.as_str() {
                    "struct" | "enum" | "union" => owned.types.insert(name.to_string()),
                    "trait" => owned.traits.insert(name.to_string()),
                    _ => false,
                };
            }
            _ => {}
        }
    }
    owned
}

/// The header tokens after `impl`, up to the body's `{`.
fn impl_header(after_impl: &[Token]) -> &[Token] {
    let end = after_impl.iter().position(|t| t.is_punct('{')).unwrap_or(after_impl.len());
    &after_impl[..end]
}

/// The parts of an `impl` header, or why the scan cannot read it.
pub(super) fn parse_header(header: &[Token]) -> Result<ImplHeader<'_>, String> {
    let unreadable = || "an `impl` header the scan cannot read (write `impl Name` or `impl Trait for Name` with plain names)".to_string();
    let (generics, rest) = split_angle_group(header).ok_or_else(unreadable)?;
    let parameters: BTreeSet<&str> = generics.iter().filter_map(Token::ident).collect();
    // Cut the where clause; split at `for` (angle depth 0).
    let mut depth = 0i64;
    let mut fors = Vec::new();
    let mut end = rest.len();
    for (k, t) in rest.iter().enumerate() {
        depth += angle_delta(t);
        if depth == 0 {
            match t.ident() {
                Some("for") => fors.push(k),
                Some("where") => {
                    end = k;
                    break;
                }
                _ => {}
            }
        }
    }
    let rest = &rest[..end];
    let (trait_path, self_type) = match fors.as_slice() {
        [] => (None, rest),
        [k] => (Some(&rest[..*k]), &rest[*k + 1..]),
        _ => return Err(unreadable()),
    };
    if trait_path.is_some_and(|t| t.first().is_some_and(|t| t.is_punct('!'))) {
        return Err("negative `impl` blocks are not supported".into());
    }
    if trait_path.is_some_and(<[Token]>::is_empty) || self_type.is_empty() {
        return Err(unreadable());
    }
    Ok(ImplHeader { parameters, trait_path, self_type })
}

/// Whether `name` is defined at the top level of the file (in `names`) and is not one of the impl's own parameters.
pub(super) fn owned_name(name: Option<&str>, names: &BTreeSet<String>, header: &ImplHeader) -> bool {
    name.is_some_and(|n| names.contains(n) && !header.parameters.contains(n))
}

fn check_ownership(header: &ImplHeader, owned: &FileOwned) -> Result<(), String> {
    let (trait_path, self_type) = (header.trait_path, header.self_type);
    let (trait_name, self_name) = (trait_path.and_then(plain_name), plain_name(self_type));
    if owned_name(self_name, &owned.types, header) || owned_name(trait_name, &owned.traits, header) {
        return Ok(());
    }
    let shown = |name: Option<&str>| name.map_or("..".to_string(), str::to_string);
    Err(match trait_path {
        None => format!("`impl {}` implements a type that is not a struct/enum/union defined at the top level of this file", shown(self_name)),
        Some(_) => format!(
            "`impl {} for {}` implements neither a struct/enum/union nor a trait defined at the top level of this file (plain names)",
            shown(trait_name),
            shown(self_name)
        ),
    })
}

/// `Name` or `Name<..>` (the whole slice): the name.
pub(super) fn plain_name(tokens: &[Token]) -> Option<&str> {
    let (first, arguments) = tokens.split_first()?;
    let plain = arguments.is_empty() || (arguments[0].is_punct('<') && split_angle_group(arguments).is_some_and(|(_, rest)| rest.is_empty()));
    first.ident().filter(|name| plain && *name != "Self")
}

/// A leading `<..>` group (empty if there is none) and the tokens after it; `None` if it does not close.
pub(super) fn split_angle_group(tokens: &[Token]) -> Option<(&[Token], &[Token])> {
    if !tokens.first().is_some_and(|t| t.is_punct('<')) {
        return Some((&[], tokens));
    }
    let mut depth = 0i64;
    for (k, t) in tokens.iter().enumerate() {
        if t.is_punct('{') {
            return None;
        }
        depth += angle_delta(t);
        if depth == 0 {
            return Some((&tokens[1..k], &tokens[k + 1..]));
        }
        if depth < 0 {
            return None;
        }
    }
    None
}

pub(super) fn angle_delta(t: &Token) -> i64 {
    match &t.tok {
        Tok::Punct('<') => 1,
        Tok::Punct('>') => -1,
        Tok::Op("<<") => 2,
        Tok::Op(">>") => -2,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::super::{rule, scan_source};

    fn refused(src: &str) -> usize {
        scan_source("agent/mod.rs", src).iter().filter(|f| f.rule == rule::IMPL_OWNERSHIP).count()
    }

    /// The author's own types keep inherent methods and the allowlisted traits (`View` and `WorkerTask`, qualified or
    /// not); the author's own traits may be implemented for any type; `impl Trait` in types is not an impl block (the
    /// impl-Trait rule refuses it, not this one).
    #[test]
    fn own_types_and_own_traits_are_accepted() {
        let src = r#"use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
verus! {
pub struct Scan<T> { lo: u64, x: T }
#[verifier::reject_recursive_types(T)]
impl<T> WorkerTask for Scan<T> where T: Send + 'static { }
impl<T> Scan<T> { pub fn f<F: Fn(u8) -> u8>(x: impl Fn(), g: F) -> impl View { 0u8 } }
pub enum E { A }
impl View for E { type V = int; open spec fn view(&self) -> int { 0 } }
impl vstd::view::View for Scan<u8> { type V = int; open spec fn view(&self) -> int { 0 } }
pub union U { a: u8 }
impl U { }
pub trait Key { spec fn key(&self) -> int; }
impl Key for u64 { open spec fn key(&self) -> int { *self as int } }
impl<T> Key for Vec<T> { open spec fn key(&self) -> int { 0 } }
impl Key for crate::exec::value::EVal { open spec fn key(&self) -> int { 0 } }
fn g<'a>(x: &impl Key, y: &mut impl Key, z: &'a impl Key) {}
}
"#;
        let found: Vec<(usize, &str)> = scan_source("agent/mod.rs", src).iter().map(|f| (f.line, f.rule)).collect();
        // One finding per line and trait name (`impl Fn`, `impl View`; `impl Key` three times on line 17).
        assert_eq!(found, [(7, rule::IMPL_TRAIT_TYPE), (7, rule::IMPL_TRAIT_TYPE), (17, rule::IMPL_TRAIT_TYPE)]);
    }

    #[test]
    fn implementations_of_other_types_are_refused() {
        for src in [
            // Framework and interface types, imported or qualified (S1c probes P1, P2, P4).
            "use crate::exec::value::EVal;\nverus! {\nimpl EVal { pub open spec fn view(&self) -> int { 0 } }\n}",
            "verus! {\nimpl crate::gendb_entry::stored::StoredParts { }\n}",
            "use crate::stores::s::interface::*;\nverus! {\nimpl View for Z { type V = int; open spec fn view(&self) -> int { 0 } }\n}",
            "use crate::stores::s::interface::Reader;\nverus! {\nimpl Reader for u64 { }\n}",
            // A type alias names another type (probe P8); an inline module is not the file's top level (probe P7).
            "verus! {\npub type L = crate::stores::s::interface::Z;\nimpl L { }\n}",
            "verus! {\npub mod inner {\n    pub struct M;\n    impl M { }\n}\n}",
            // Blanket implementations, also behind a same-name local struct.
            "verus! {\nimpl<T> View for T { }\n}",
            "verus! {\npub struct T;\nimpl<T> View for T { }\n}",
            // Headers the scan does not read.
            "verus! {\npub struct M;\nimpl View for &M { }\n}",
            "verus! {\npub struct M;\nimpl View for (M, M) { }\n}",
            "verus! {\npub struct M<const N: usize>;\nimpl M<{ 1 }> { }\n}",
            "verus! {\npub struct M;\nimpl !Send for M { }\n}",
            "verus! {\npub struct M;\nfn f() { impl M { } }\n}",
            // Outside verus! (also refused by the top-level rule).
            "pub struct M;\nimpl M { }",
        ] {
            assert_eq!(refused(src), 1, "{src}");
        }
    }
}
