//! Trait rules: which traits author code may implement, which bounds its trait definitions may declare, and no
//! `impl Trait` types.
//!
//! Each rule removes a form that the pinned Verus accepts under `--no-cheating` although a call the form makes is not
//! an edge of the call graph Verus checks for cycles and termination (soundness probes run with the
//! admission flags). The rules are an allowlist where one is possible:
//!
//! - [`rule::EXTERNAL_TRAIT_IMPL`]: an `impl Trait for Type` names either a trait defined at the top level of the same
//!   file (a plain name there denotes the local definition) or, by the last segment of its path, one of
//!   [`ALLOWED_EXTERNAL_TRAITS`]. Every other trait is refused: std's and vstd's (Drop, PartialEq, Hash, the fmt
//!   traits, Iterator, the operator traits, From, Default, vstd's spec traits, ...) and an author trait of another file,
//!   which a lexical scan cannot tell apart from an external trait of the same name. A `use` may not rename an item to
//!   one of the allowed names, so such a name always denotes the trait itself (std, vstd and the framework re-export
//!   none of them under another name).
//! - [`rule::ASSOCIATED_TYPE_BOUND`]: a trait definition declares no bound on an associated type: no `type A: T;`
//!   (or a where clause or bounded parameter on it), no where clause on the trait, and no associated type bound
//!   `Trait<A: T>` in its header. Unbounded associated types (`type A;`) stay allowed, and so do bounds on functions,
//!   methods and impls, whose impls Verus does follow.
//! - [`rule::IMPL_TRAIT_TYPE`]: no `impl Trait` type in any position. A return-position `impl Trait` hides the
//!   concrete type; an argument-position one is shorthand for a generic parameter, which stays available, so one
//!   lexical rule covers every position.
//!
//! Like the rest of the scan, these are lexical checks over the token stream, not a Rust proof.

use super::super::lexer::{group_end, Tok, Token};
use super::impl_ownership::{angle_delta, file_owned, impl_items, in_type_position, owned_name, parse_header, plain_name, split_angle_group};
use super::macros::use_declarations;
use super::{rule, Findings};

/// The external traits author code may implement (for its own types; [`super::impl_ownership`]): exactly the ones the
/// admitted builds implement (framework files: `View`; author files: `WorkerTask`, `Clone`, `Copy`). vstd's `View` (an
/// unbounded associated type and a spec method), the framework's `WorkerTask` (run only through `fork_join`, a generic
/// call Verus follows), `Clone` (a manual `clone` that recurses through vstd's `Vec`/`Option` clone or through a
/// generic helper is refused by Verus) and `Copy` (a marker, no methods).
pub const ALLOWED_EXTERNAL_TRAITS: &[&str] = &["View", "WorkerTask", "Clone", "Copy"];

/// Every trait implementation outside the allowlist, and every `use` that renames an item to an allowed trait name.
pub(super) fn check_trait_impls(tokens: &[Token], findings: &mut Findings) {
    let owned = file_owned(tokens);
    for item in impl_items(tokens) {
        // An unreadable header is the ownership rule's finding.
        let Ok(header) = parse_header(item.header) else { continue };
        let Some(trait_path) = header.trait_path else { continue };
        if owned_name(plain_name(trait_path), &owned.traits, &header) {
            continue;
        }
        match last_segment(trait_path) {
            Some(name) if ALLOWED_EXTERNAL_TRAITS.contains(&name) => {}
            name => findings.refuse(
                item.line,
                rule::EXTERNAL_TRAIT_IMPL,
                format!(
                    "`impl {}` implements a trait that is neither defined at the top level of this file nor one of {}",
                    name.unwrap_or(".."),
                    ALLOWED_EXTERNAL_TRAITS.join(", ")
                ),
            ),
        }
    }
    for (line, bindings) in use_declarations(tokens) {
        // An unreadable `use` is the macro-import rule's finding.
        for binding in bindings.unwrap_or_default() {
            if ALLOWED_EXTERNAL_TRAITS.contains(&binding.name.as_str()) && binding.name != binding.imported {
                findings.refuse(
                    line,
                    rule::EXTERNAL_TRAIT_IMPL,
                    format!("`use` binds the allowed trait name `{}` to `{}`", binding.name, binding.imported),
                );
            }
        }
    }
}

/// The last segment of a trait path `Name`, `a::b::Name` or `::a::Name`, each optionally followed by one `<..>`
/// argument group; `None` for any other form.
fn last_segment(path: &[Token]) -> Option<&str> {
    let mut rest = match path.first() {
        Some(t) if t.tok == Tok::Op("::") => &path[1..],
        _ => path,
    };
    loop {
        let (segment, after) = rest.split_first()?;
        let name = segment.ident()?;
        match after.first() {
            None => return Some(name),
            Some(t) if t.tok == Tok::Op("::") => rest = &after[1..],
            Some(t) if t.is_punct('<') => return split_angle_group(after).is_some_and(|(_, tail)| tail.is_empty()).then_some(name),
            Some(_) => return None,
        }
    }
}

/// Every trait definition (the keyword `trait`): a where clause or an associated type bound in its header, a bound
/// on one of its associated types.
pub(super) fn check_trait_definitions(tokens: &[Token], findings: &mut Findings) {
    for (i, token) in tokens.iter().enumerate() {
        if token.ident() == Some("trait") {
            check_trait_definition(tokens, i, findings);
        }
    }
}

/// The trait whose keyword is at `i`. Its header runs from the name to the body's `{` (or a `;`) at angle depth 0;
/// delimiter groups in it are skipped (const arguments, `Fn(..)` sugar). In the trait's own parameter list a `:` at
/// angle depth 1 bounds a parameter; every other `:` inside angle brackets is an associated type bound.
fn check_trait_definition(tokens: &[Token], i: usize, findings: &mut Findings) {
    let unreadable = "a trait header the scan cannot read";
    let after_name = tokens.get(i + 2..).unwrap_or_default();
    let Some((_, after_parameters)) = split_angle_group(after_name) else {
        return findings.refuse(tokens[i].line, rule::ASSOCIATED_TYPE_BOUND, unreadable.into());
    };
    let parameters_end = tokens.len() - after_parameters.len();
    let mut depth = 0i64;
    let mut k = i + 2;
    while k < tokens.len() {
        let token = &tokens[k];
        match &token.tok {
            Tok::Punct('{') if depth == 0 => return check_associated_types(tokens, k, findings),
            Tok::Punct(';') if depth == 0 => return,
            Tok::Punct('(' | '[' | '{') => {
                k = group_end(tokens, k);
                continue;
            }
            Tok::Ident(word) if word == "where" => findings.refuse(token.line, rule::ASSOCIATED_TYPE_BOUND, "a where clause on a trait".into()),
            Tok::Punct(':') if depth >= 2 || (depth == 1 && k >= parameters_end) => findings.refuse(
                token.line,
                rule::ASSOCIATED_TYPE_BOUND,
                "an associated type bound `Trait<A: Bound>` in a trait header".into(),
            ),
            _ => {}
        }
        depth += angle_delta(token);
        if depth < 0 {
            return findings.refuse(token.line, rule::ASSOCIATED_TYPE_BOUND, unreadable.into());
        }
        k += 1;
    }
}

/// The associated type declarations of the trait body that opens at `open` (items `type ...;` at the body's top
/// level): refused when they declare a bound, a bounded parameter or a where clause.
fn check_associated_types(tokens: &[Token], open: usize, findings: &mut Findings) {
    let close = group_end(tokens, open).saturating_sub(1);
    let mut k = open + 1;
    while k < close {
        if matches!(tokens[k].tok, Tok::Punct('(' | '[' | '{')) {
            k = group_end(tokens, k);
            continue;
        }
        if tokens[k].ident() != Some("type") {
            k += 1;
            continue;
        }
        let mut end = k + 1;
        let mut bounded = false;
        while end < close && !tokens[end].is_punct(';') && !tokens[end].is_punct('=') {
            if matches!(tokens[end].tok, Tok::Punct('(' | '[' | '{')) {
                end = group_end(tokens, end);
                continue;
            }
            bounded |= tokens[end].is_punct(':') || tokens[end].ident() == Some("where");
            end += 1;
        }
        if bounded {
            let name = tokens.get(k + 1).and_then(Token::ident).unwrap_or("..");
            findings.refuse(tokens[k].line, rule::ASSOCIATED_TYPE_BOUND, format!("associated type `{name}` declares a bound"));
        }
        k = end;
    }
}

/// Every `impl` keyword in a type (an `impl Trait` type), in any position.
pub(super) fn check_impl_trait_types(tokens: &[Token], findings: &mut Findings) {
    for (i, token) in tokens.iter().enumerate() {
        if token.ident() == Some("impl") && in_type_position(tokens, i) {
            let name = tokens.get(i + 1).and_then(Token::ident).unwrap_or("..");
            findings.refuse(token.line, rule::IMPL_TRAIT_TYPE, format!("an `impl {name}` type (write a generic parameter)"));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{rule, scan_source, SUPPORTED_DERIVES, VERUS_REFUSAL_RULES};
    use super::ALLOWED_EXTERNAL_TRAITS;

    /// The rule texts that the author contract shows name exactly the allowlists the scan enforces.
    #[test]
    fn rule_texts_name_the_allowlists() {
        let refuses = |id: &str| VERUS_REFUSAL_RULES.iter().find(|r| r.id == id).unwrap().refuses;
        assert!(refuses(rule::EXTERNAL_TRAIT_IMPL).contains("View, WorkerTask, Clone and Copy"));
        assert_eq!(ALLOWED_EXTERNAL_TRAITS, ["View", "WorkerTask", "Clone", "Copy"]);
        assert!(refuses(rule::ATTRIBUTE).contains("derives other than Clone, Copy, PartialEq and Eq"));
        assert_eq!(SUPPORTED_DERIVES, ["Clone", "Copy", "PartialEq", "Eq"]);
    }

    /// Findings of `rule` in `src` (scanned as a query author file), as lines.
    fn lines(src: &str, rule: &str) -> Vec<usize> {
        scan_source("agent/mod.rs", src).iter().filter(|f| f.rule == rule).map(|f| f.line).collect()
    }

    /// The allowed external traits (plain or by path), own traits for any type, and plain imports of the allowed names
    /// pass the whole scan.
    #[test]
    fn allowed_trait_implementations_pass() {
        let src = r#"use vstd::prelude::*;
use vstd::view::View;
use crate::gendb_entry::parallel::{fork_join, WorkerTask};
verus! {
pub struct Cols { a: u64 }
impl Clone for Cols { fn clone(&self) -> (r: Cols) ensures r == *self { Cols { a: self.a } } }
impl Copy for Cols {}
impl View for Cols { type V = int; open spec fn view(&self) -> int { self.a as int } }
pub struct Win<T> { lo: u64, x: T }
impl<T: Copy> core::clone::Clone for Win<T> { fn clone(&self) -> Win<T> { Win { lo: self.lo, x: self.x } } }
impl<T: Copy> ::core::marker::Copy for Win<T> {}
impl<T> vstd::view::View for Win<T> { type V = int; open spec fn view(&self) -> int { 0 } }
pub struct Task { lo: u64 }
impl crate::gendb_entry::parallel::WorkerTask for Task { type Output = u64; }
pub trait Key: Copy + Send + Sync + 'static { spec fn key(&self) -> int; }
impl Key for u32 { open spec fn key(&self) -> int { *self as int } }
pub trait Drop { fn drop(&mut self); }
impl Drop for Task { fn drop(&mut self) {} }
}
"#;
        assert_eq!(scan_source("agent/mod.rs", src), vec![]);
    }

    /// Every external trait outside the allowlist is refused, whatever path names it, and so is an author trait of
    /// another file (the scan cannot tell it from an external trait of the same name).
    #[test]
    fn other_trait_implementations_are_refused() {
        for header in [
            "Drop for S",
            "PartialEq for S",
            "Eq for S",
            "PartialOrd for S",
            "Ord for S",
            "core::cmp::PartialEq<S> for S",
            "std::hash::Hash for S",
            "core::borrow::Borrow<u64> for S",
            "core::ops::Deref for S",
            "Iterator for S",
            "IntoIterator for S",
            "core::fmt::Display for S",
            "std::fmt::Debug for S",
            "core::ops::Add for S",
            "From<u64> for S",
            "Into<u64> for S",
            "Default for S",
            "vstd::std_specs::cmp::PartialEqSpecImpl for S",
            "vstd::std_specs::iter::IteratorSpecImpl for S",
            "vstd::view::DeepView for S",
            "crate::agent::common::scatter::KeyIdx for S",
            "KeyIdx for S",
            "<S as Tr>::Assoc for S",
        ] {
            let src = format!("verus! {{\npub struct S;\nimpl {header} {{ }}\n}}\n");
            assert_eq!(lines(&src, rule::EXTERNAL_TRAIT_IMPL), [3], "{header}");
        }
    }

    /// A `use` may not rename an item to an allowed trait name; imports of the allowed traits under their own names
    /// and renames to other names are not this rule's finding.
    #[test]
    fn renames_to_allowed_trait_names_are_refused() {
        for (src, expected) in [
            ("use std::ops::Drop as View;\nverus! {\npub struct S;\nimpl View for S { fn drop(&mut self) {} }\n}\n", vec![1]),
            ("use core::ops::{Deref as WorkerTask};", vec![1]),
            ("use core::fmt::{self as View};", vec![1]),
            ("verus! { fn f() { use std::hash::Hash as Clone; } }", vec![1]),
            ("use vstd::view::View;\nuse vstd::view::View as View;\nuse crate::gendb_entry::parallel::WorkerTask;", vec![]),
            ("use vstd::view::View as V;", vec![]),
        ] {
            assert_eq!(lines(src, rule::EXTERNAL_TRAIT_IMPL), expected, "{src}");
        }
        // Renamed away from an allowed name, the trait is refused where it is implemented.
        let renamed = "use vstd::view::View as V;\nverus! {\npub struct S;\nimpl V for S { }\n}\n";
        assert_eq!(lines(renamed, rule::EXTERNAL_TRAIT_IMPL), [4]);
    }

    /// Bounds on associated types are refused in every form a trait definition can state them; unbounded associated
    /// types, supertraits, bounds on the trait's own parameters and bounds on methods and impls are not.
    #[test]
    fn associated_type_bounds_are_refused() {
        for (src, expected) in [
            ("verus! {\npub trait Fam {\n    type A: T;\n}\n}", vec![3]),
            ("verus! {\npub trait Fam {\n    type A: ?Sized;\n    type B<X: Copy>;\n    type C where Self: Sized;\n}\n}", vec![3, 4, 5]),
            ("verus! {\npub trait Fam where Self::A: T {\n    type A;\n}\n}", vec![2]),
            ("verus! {\npub trait Fam<X>: Sized\n    where X: Copy\n{ }\n}", vec![3]),
            ("verus! {\npub trait G: Fam<A: T> { }\n}", vec![2]),
            ("verus! {\npub trait G: Iterator<Item: Copy> + Sized { }\n}", vec![2]),
            ("verus! {\npub trait G<X: Fam<A: T>> { }\n}", vec![2]),
            ("verus! {\npub trait G<X: Fam<B<C: T>>> { }\n}", vec![2]),
        ] {
            assert_eq!(lines(src, rule::ASSOCIATED_TYPE_BOUND), expected, "{src}");
        }
        let allowed = r#"verus! {
pub trait Fam: Copy + Send + Sync + Sized + 'static {
    type A;
    type B<X>;
    const N: usize;
    spec fn get(&self) -> Self::A;
    fn m(&self) where Self::A: Copy;
    fn d<F: Fn(u8) -> u8>(&self, f: F) -> u8 { let x: Vec<u8> = Vec::new(); f(0) }
}
pub trait Indexed<'a: 'b, 'b, X: Copy + Fam, const N: usize>: Fam + for<'c> Fn(&'c u8) {}
pub trait Other<X = u8> {}
pub struct S;
impl Fam for S { type A = u8; type B<X> = Vec<X>; }
impl<X: Fam> Other<X> for S where X::A: Copy {}
pub type Alias<T> = Vec<T>;
}
"#;
        assert_eq!(lines(allowed, rule::ASSOCIATED_TYPE_BOUND), Vec::<usize>::new());
    }

    /// `impl Trait` types are refused in every position; `impl` blocks are not types.
    #[test]
    fn impl_trait_types_are_refused() {
        for src in [
            "verus! { fn mk() -> impl T { S } }",
            "verus! { fn mk() -> (r: impl T) { S } }",
            "verus! { fn mk() -> Option<impl T> { None } }",
            "verus! { fn mk<'a>(x: &'a S) -> &'a impl T { x } }",
            "verus! { fn f(x: impl T) {} }",
            "verus! { fn f(x: &impl T) {} }",
            "verus! { fn f(x: &mut impl T) {} }",
            "verus! { fn f(x: Vec<impl T>) {} }",
            "verus! { fn f(x: *const impl T) {} }",
            "verus! { pub trait T { fn m(&self) -> impl Copy; } }",
            "verus! { fn f(g: impl Fn(u8) -> u8 + use<>) {} }",
        ] {
            assert_eq!(lines(src, rule::IMPL_TRAIT_TYPE), [1], "{src}");
        }
        let blocks = "verus! {\npub struct S;\nimpl S { fn f<T: Copy>(x: T) -> T { x } }\n#[verifier::reject_recursive_types(T)]\nimpl Clone for S { fn clone(&self) -> S { S } }\n}\n";
        assert_eq!(lines(blocks, rule::IMPL_TRAIT_TYPE), Vec::<usize>::new());
    }
}
