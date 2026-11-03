//! Framework refusal list for author Rust submitted to Verus.
//!
//! Verus `--no-cheating` refuses `assume`, `admit`, `external_body` and `assume_specification`. On the pinned
//! release it does NOT refuse the forms listed in [`VERUS_REFUSAL_RULES`]: each was accepted, verified and
//! compiled by `rust_verify --no-cheating --compile` in the T2a probes, or (macro policy, implementation ownership)
//! gave identical text two meanings in two separately checked crates in the S1c probes, or (trait objects, vstd's
//! rwlock, external trait impls, bounded associated types, `impl Trait` types) verified and then ran until killed or
//! proved `false` in the termination and soundness probes, because a call they make is not an edge of the call graph
//! Verus checks. The macro policy ([`macros`]) and implementation ownership ([`impl_ownership`]) keep what a file
//! means independent of the other author code of its crate; the trait rules ([`traits`]) allow only trait
//! implementations and bounds whose calls Verus follows.
//!
//! The scan is a lexical token check over author files with comments and string/char literals removed
//! ([`super::lexer`]). It is not a Rust parser, is not itself verified, and claims nothing beyond the listed rules.
//! Every author root is scanned (`agent/**` of candidate and query crates, `builder/**` and
//! `stores/<name>/interface/**` of storage builds); framework files are scanned only when a caller asks for it. One
//! rule depends on the file's path (relative to the crate's `src/`): storage interface files may not name the
//! declared-constraints module ([`rule::INTERFACE_NAMES_DECLARED_CONSTRAINTS`]).
//!
//! Engine crates (schema-engine target) add the rules of [`engine_rules`] (template constants, AST fragment tables, and
//! the whole-statement evaluator: its modules, globs and aliases of `exec::relational`, and every function that can
//! reach it); query freezes apply only the evaluator's paths ([`scan_whole_statement_evaluator`]). Like
//! [`STATIC_ITEM_RULE`] they are not part of [`VERUS_REFUSAL_RULES`], so every other crate kind is unchanged.

pub mod engine_rules;
mod impl_ownership;
mod macros;
mod traits;

pub use macros::{SUPPORTED_DERIVES, SUPPORTED_MACROS};
pub use traits::ALLOWED_EXTERNAL_TRAITS;

use super::lexer::{group_end, lex, Tok, Token};
use serde::Serialize;

/// Rule identifiers, shared by the rules table, the findings and the records.
pub mod rule {
    pub const FILE_SET: &str = "file_set";
    pub const OUTSIDE_VERUS: &str = "outside_verus";
    pub const ATTRIBUTE: &str = "attribute";
    pub const VERIFIER_ATTRIBUTE: &str = "verifier_attribute";
    pub const UNSAFE: &str = "unsafe";
    pub const EXTERN: &str = "extern";
    pub const MACRO: &str = "macro";
    pub const DIRECT_THREAD: &str = "direct_thread";
    pub const DYN_TRAIT_OBJECT: &str = "dyn_trait_object";
    pub const VSTD_RWLOCK: &str = "vstd_rwlock";
    pub const EXTERNAL_TRAIT_IMPL: &str = "external_trait_impl";
    pub const ASSOCIATED_TYPE_BOUND: &str = "associated_type_bound";
    pub const IMPL_TRAIT_TYPE: &str = "impl_trait_type";
    pub const IMPL_OWNERSHIP: &str = "impl_ownership";
    pub const MACRO_IMPORT: &str = "macro_import";
    pub const INTERFACE_NAMES_DECLARED_CONSTRAINTS: &str = "interface_names_declared_constraints";
    /// The whole-statement evaluator check (query freezes) and the engine rule of the same id.
    pub const WHOLE_STATEMENT_EVALUATOR: &str = "whole_statement_evaluator";
}

/// One refusal rule. The table is the single source for the author contract and the trusted-computing-base record.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct RefusalRule {
    pub id: &'static str,
    pub refuses: &'static str,
    pub reason: &'static str,
}

pub const VERUS_REFUSAL_RULES: &[RefusalRule] = &[
    RefusalRule {
        id: rule::FILE_SET,
        refuses: "author directory entries other than directories and UTF-8 `.rs` files with plain names (no symlinks); a missing agent/mod.rs",
        reason: "the frozen crate contains only author Rust modules; nothing else can be read at compile time",
    },
    RefusalRule {
        id: rule::OUTSIDE_VERUS,
        refuses: "any top-level item other than `use`, `mod NAME;`, inner attributes and `verus! { ... }` blocks",
        reason: "Verus skips items outside verus! but rustc compiles them; a Drop impl or an .init_array static outside verus! ran unverified code in the probes",
    },
    RefusalRule {
        id: rule::ATTRIBUTE,
        refuses: "attributes other than the allowed list (`verifier::` hints, triggers, derive, allow/warn/deny/expect, inline, must_use, doc, rustfmt/verusfmt skip); derives other than Clone, Copy, PartialEq and Eq written by their plain names",
        reason: "cfg/cfg_attr (the verify pass sets cfg verus_keep_ghost_body, the compile pass does not: a probe verified `r == x + 1` and the compiled library returned 999), link_section/used/no_mangle/export_name/path/verus::internal and other attributes change what is compiled or linked without verification. A derive implements a trait: the supported ones are those admitted code uses whose expansions call only what Verus follows (a derived PartialEq reaches author code only through a manual PartialEq impl, which external_trait_impl refuses); Debug implements a fmt trait that std calls without its preconditions (Verus issue #3138)",
    },
    RefusalRule {
        id: rule::VERIFIER_ATTRIBUTE,
        refuses: "verifier:: attributes outside the allowed hint list, including external*, assume_termination, exec_allows_no_decreases_clause, when_used_as_spec",
        reason: "loop-level assume_termination and exec_allows_no_decreases_clause pass --no-cheating and admit a non-terminating function that meets any ensures; external* items are compiled without verification",
    },
    RefusalRule {
        id: rule::UNSAFE,
        refuses: "`unsafe` (blocks, functions, impls such as `unsafe impl Send`, attributes)",
        reason: "unchecked code; `unsafe impl Send/Sync` would let data cross threads outside the checked ownership rules",
    },
    RefusalRule {
        id: rule::EXTERN,
        refuses: "`extern` (extern blocks, extern \"C\" functions, extern crate)",
        reason: "foreign code and crates outside the frozen crate",
    },
    RefusalRule {
        id: rule::MACRO,
        refuses: "every macro invocation other than seq!, set!, map!, vec! (and verus! at the top level), plain or path-qualified; macro_rules!",
        reason: "other macros bring source or behaviour from outside the checked text (include!, env!, asm!), diverge between the verify and compile passes (cfg!) or between separately checked crates (module_path! names the crate, file! the frozen directory: identical interface text proved `represents()` in a storage crate and its negation in a query crate, S1c probe P3). The supported expansions (audited on the pinned toolchain) depend on neither location, environment nor configuration and implement nothing for other types",
    },
    RefusalRule {
        id: rule::MACRO_IMPORT,
        refuses: "a `use` that binds a supported macro, derive or attribute name, or a keyword the scan reads before `!` (Rust keywords, even as raw identifiers, and Verus clause words such as implies/requires); a `use` the scan cannot read",
        reason: "a rename such as `use std::module_path as seq;` makes a supported name expand to an unsupported macro (S1c probe P9: `seq!()` then named the crate and the same interface text meant different things in two crates)",
    },
    RefusalRule {
        id: rule::IMPL_OWNERSHIP,
        refuses: "an `impl` block that is not at the top level of the file's `verus!` block, or that implements neither a struct/enum/union nor a trait defined at the top level of the same file (plain names, not the impl's own generic parameters; type aliases, references and unreadable headers refused)",
        reason: "Rust resolves methods through every `impl` of the crate: an author's inherent `view` for a framework or interface type takes precedence over its `View` implementation at every `x@`, and a method supplied by a builder and by a query module gives the same interface text two meanings (S1c probes P1-P4, P7, P8). Methods, trait implementations and traits for the author's own types, and the author's own traits for any type, stay available",
    },
    RefusalRule {
        id: rule::INTERFACE_NAMES_DECLARED_CONSTRAINTS,
        refuses: "the identifier `gendb_constraints` (also raw, in a path, a `use`, an alias or a glob) in a storage interface file (`stores/<name>/interface/**`)",
        reason: "the declared-constraints module is in no storage closure, so a storage's `represents` must not depend on it: then the closure is the same in every constraint mode and unconstrained storages compose with constrained queries by the unchanged rule. Its items can be reached only through that module name (the entry roots import them privately), so refusing the name is the whole rule; builders and query modules may name it. A lexical rule: it sees identifiers after comments and string literals are removed and raw identifiers are normalized; the macro rules refuse every macro that could assemble an identifier",
    },
    RefusalRule {
        id: rule::DIRECT_THREAD,
        refuses: "the identifier `thread` (std::thread, vstd::thread)",
        reason: "policy, not a Verus soundness gap: vstd::thread::spawn has no join obligation (a probe spawned a thread, never joined it, and verified), so a worker could outlive the call and its input buffers; workers go only through the framework's verified pass-throughs. std::thread itself is already rejected by Verus (no specification)",
    },
    RefusalRule {
        id: rule::DYN_TRAIT_OBJECT,
        refuses: "the keyword `dyn`: every trait object type (`&dyn T`, `Box<dyn T>`, `dyn Fn(..)`)",
        reason: "soundness: on the pinned release a call through a trait object is not an edge of Verus's call graph, so recursion through `&dyn Trait` escapes the termination and cycle checks. In the termination probes an exec function recursing through `&dyn T` verified (h5), also with an `ensures` that no returning call can meet, and ran until killed (h5b); proof and spec functions recursing through it proved `false` (i5, i6); and a verified `add_one(5)` with `ensures r == n + 1` returned 0 (k1). Edition 2021 writes every trait object with `dyn`, and neither vstd nor the framework files take or return one, so refusing the keyword in author files removes them",
    },
    RefusalRule {
        id: rule::VSTD_RWLOCK,
        refuses: "the identifiers `rwlock` and `RwLock`: the module vstd::rwlock, every path or `use` through it, and the type name",
        reason: "termination: vstd marks RwLock::acquire_read, acquire_write and into_inner `exec_allows_no_decreases_clause`, so calls to them are exempt from the termination check; in the termination probes a second acquire_write on the same lock verified and spun until killed (h7). They are the only such functions of the pinned vstd, and its lock types are reachable only through the module name `rwlock`",
    },
    RefusalRule {
        id: rule::EXTERNAL_TRAIT_IMPL,
        refuses: "an `impl Trait for Type` whose trait is neither defined at the top level of the same file nor one of the allowed external traits View, WorkerTask, Clone and Copy (by the last segment of its path): Drop, PartialEq/Eq/PartialOrd/Ord, Hash, Borrow, Deref, Iterator/IntoIterator, the fmt traits, the operator traits, From/Into, Default, vstd's spec traits and every other std/vstd trait, and author traits of other files; a `use` that renames an item to one of the allowed names",
        reason: "soundness and termination: std and vstd call trait methods implicitly or without their preconditions, outside the call graph Verus checks. In the soundness probes a Drop impl whose body drops a value of its own type verified and ran until killed (v11); a derived PartialEq calling a manual PartialEq impl ran until killed (v18b); an author IteratorSpecImpl reached through std's bound IntoIterator::IntoIter: Iterator proved `false` and a verified add_one(5) returned 0 (v22, r5; Verus PR #3063, open); std calls author fmt and Hash impls (also Borrow, Hasher, BuildHasher, Iterator::nth, Step) without their requires (Verus issues #3138, #3139). The allowed external traits are exactly the ones the admitted builds implement (framework files: View; author files: WorkerTask, Clone, Copy): View (an unbounded associated type and a spec method), WorkerTask (run only through the framework's fork_join, a generic call Verus follows), Clone (a manual clone recursing through vstd's Vec or Option clone or through a generic helper is refused by Verus) and Copy (no methods). A trait of another file cannot be told apart lexically from an external trait of the same name, so an author implements its own trait in the file that defines it; no `use` may rename anything to an allowed name, so that name always denotes the trait itself",
    },
    RefusalRule {
        id: rule::ASSOCIATED_TYPE_BOUND,
        refuses: "in a trait definition: a bound, bounded parameter or where clause on an associated type (`type A: T;`), a where clause on the trait, an associated type bound `Trait<A: T>` in its header; unbounded associated types (`type A;`) are allowed",
        reason: "soundness: on the pinned release the impls that satisfy a bound declared on an associated type are not edges of Verus's call graph, so recursion through them escapes the cycle check. In the soundness probes an author trait `Fam { type A: T; }` whose impl of T calls back through `Fam` proved `false` in proof code (v05) and spec code (v05b), the same bound as a trait-level where clause proved `false` (v05e), the exec form verified and never returned (v05d) and a verified add_one(5) returned 0 (r1); Verus PR #3063 (open). The same bound on a function, a trait method or an impl is followed (v05c and further probes) and stays allowed",
    },
    RefusalRule {
        id: rule::IMPL_TRAIT_TYPE,
        refuses: "the keyword `impl` in a type: every `impl Trait` type, in return position (`-> impl T`, `-> (r: impl T)`, `-> Option<impl T>`) and in argument position (`x: impl T`, `&impl T`)",
        reason: "termination: on the pinned release a call through an opaque return type `impl Trait` does not lead the call graph to the concrete type's impl, so recursion through it escapes the termination check: in the soundness probes an exec method recursing through `fn mk() -> impl T` verified and ran until killed (v01, r2). An argument-position `impl Trait` is shorthand for a generic parameter, which stays available, so one lexical rule covers every position; admitted author code uses neither",
    },
];

/// The rule GenDB adds for query author files under `storage_policy` `fixed_flat` ([`scan_static_items`]); not part of
/// [`VERUS_REFUSAL_RULES`], so every other mode is unchanged.
pub const STATIC_ITEM_RULE: RefusalRule = RefusalRule {
    id: "static_item",
    refuses: "a `static` item (the keyword `static`, not the `'static` lifetime) in a query author file under storage_policy fixed_flat",
    reason: "Verus admits an `exec static` atomic with load and store under --no-cheating (shown by a probe), so a static could carry a value from one measured call to the next; under fixed_flat nothing computed in one call may be kept for a later call. Constants (`const`) stay allowed",
};

/// Findings of [`STATIC_ITEM_RULE`] in one author file: every `static` keyword that does not follow a lifetime quote.
/// Comments and string literals are not tokens, so they never match.
pub fn scan_static_items(file: &str, text: &str) -> Vec<RefusalFinding> {
    let mut findings = Findings { file, list: Vec::new() };
    match lex(text) {
        Ok(tokens) => {
            for (i, token) in tokens.iter().enumerate() {
                let lifetime = i > 0 && tokens[i - 1].is_punct('\'');
                if token.ident() == Some("static") && !lifetime {
                    findings.refuse(token.line, STATIC_ITEM_RULE.id, "a `static` item".into());
                }
            }
        }
        Err(error) => findings.refuse(error.line, rule::OUTSIDE_VERUS, format!("cannot lex author source: {}", error.message)),
    }
    findings.list
}

/// Findings of the query crates' whole-statement evaluator check (`gendb_synthesis::query::candidate::EVALUATOR_RULE`):
/// every path `relational :: eval` / `relational :: entry`, and every group `relational :: { .. }` with an item starting
/// with `eval` or `entry`. Comments and literals are not tokens, so they never match. Engine crates apply the wider
/// [`engine_rules::WHOLE_STATEMENT_EVALUATOR_RULE`] (these paths, globs, aliases and every function that can reach the
/// evaluator, by name).
pub fn scan_whole_statement_evaluator(file: &str, text: &str) -> Vec<RefusalFinding> {
    let mut findings = Findings { file, list: Vec::new() };
    match lex(text) {
        Ok(tokens) => refuse_evaluator_paths(&tokens, &mut findings),
        Err(error) => findings.refuse(error.line, rule::OUTSIDE_VERUS, format!("cannot lex author source: {}", error.message)),
    }
    findings.list
}

/// Every path `relational :: eval` / `relational :: entry`, and every group `relational :: { .. }` with an item (at the
/// group's top level) starting with `eval` or `entry` (`eval as e`, `entry::exec_ordered`).
fn refuse_evaluator_paths(tokens: &[Token], findings: &mut Findings) {
    let evaluator_module = |token: &Token| matches!(token.ident(), Some("eval" | "entry"));
    let refuse = |findings: &mut Findings, token: &Token| {
        findings.refuse(token.line, rule::WHOLE_STATEMENT_EVALUATOR, format!("`relational::{}`", token.ident().unwrap_or_default()));
    };
    for (i, token) in tokens.iter().enumerate() {
        if token.ident() != Some("relational") || tokens.get(i + 1).map(|t| &t.tok) != Some(&Tok::Op("::")) {
            continue;
        }
        let Some(next) = tokens.get(i + 2) else { continue };
        if evaluator_module(next) {
            refuse(findings, next);
        } else if next.is_punct('{') {
            let (mut depth, mut at_item_start) = (0usize, true);
            for inner in &tokens[i + 3..] {
                let closes = inner.is_punct('}') || inner.is_punct(')') || inner.is_punct(']');
                if closes && depth == 0 {
                    break;
                }
                if depth == 0 && at_item_start && evaluator_module(inner) {
                    refuse(findings, inner);
                }
                at_item_start = depth == 0 && inner.is_punct(',');
                if inner.is_punct('{') || inner.is_punct('(') || inner.is_punct('[') {
                    depth += 1;
                } else if closes {
                    depth -= 1;
                }
            }
        }
    }
}

/// Top-level attribute paths allowed in author code.
pub const ALLOWED_ATTRIBUTES: &[&str] = &[
    "verifier", "trigger", "auto", "all_triggers", "derive", "allow", "warn", "deny", "expect",
    "inline", "must_use", "doc", "rustfmt", "verusfmt",
];

/// `verifier::NAME` / `verifier(NAME)` attributes that only guide the prover or the datatype checks and are still
/// checked by Verus.
pub const ALLOWED_VERIFIER_ATTRIBUTES: &[&str] = &[
    "opaque", "opaque_outside_module", "ext_equal", "reject_recursive_types",
    "reject_recursive_types_in_ground_variants", "accept_recursive_types", "rlimit",
    "spinoff_prover", "loop_isolation", "nonlinear", "bit_vector", "memoize", "type_invariant",
    "truncate", "inline", "decreases_by", "recommends_by", "auto_ext_equal",
    "allow_complex_invariants", "trigger", "auto_trigger", "all_triggers", "no_auto_trigger",
    "proof_note", "custom_err", "allow_in_spec", "prover", "verify",
];

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RefusalFinding {
    /// Path relative to the author directory.
    pub file: String,
    /// 1-based; 0 for a finding about a whole file or a missing file.
    pub line: usize,
    pub rule: &'static str,
    pub detail: String,
}

impl RefusalFinding {
    /// A [`rule::FILE_SET`] finding about a whole directory entry.
    pub(super) fn file_set(file: impl Into<String>, detail: &str) -> Self {
        Self { file: file.into(), line: 0, rule: rule::FILE_SET, detail: detail.into() }
    }
}

/// Findings of one author file, sorted by line and rule, without duplicates. `file` is only used in the findings. The
/// one scan behind [`super::freeze_crate`] and [`super::freeze_framework_crate`]; admission and composition checks
/// that re-read author files use it rather than a second parser.
pub fn scan_source(file: &str, text: &str) -> Vec<RefusalFinding> {
    let mut findings = Findings { file, list: Vec::new() };
    match lex(text) {
        Ok(tokens) => {
            refuse_forbidden_tokens(&tokens, &mut findings);
            if is_storage_interface(file) {
                refuse_declared_constraints_module(&tokens, &mut findings);
            }
            macros::check_invocations(&tokens, &mut findings);
            macros::check_imports(&tokens, &mut findings);
            check_attributes(&tokens, &mut findings);
            check_top_level_items(&tokens, &mut findings);
            impl_ownership::check_impls(&tokens, &mut findings);
            traits::check_trait_impls(&tokens, &mut findings);
            traits::check_trait_definitions(&tokens, &mut findings);
            traits::check_impl_trait_types(&tokens, &mut findings);
        }
        Err(error) => findings.refuse(error.line, rule::OUTSIDE_VERUS, format!("cannot lex author source: {}", error.message)),
    }
    let mut list = findings.list;
    list.sort_by(|a, b| (a.line, a.rule).cmp(&(b.line, b.rule)));
    list.dedup();
    list
}

struct Findings<'a> {
    file: &'a str,
    list: Vec<RefusalFinding>,
}

impl Findings<'_> {
    fn refuse(&mut self, line: usize, rule: &'static str, detail: String) {
        self.list.push(RefusalFinding { file: self.file.to_string(), line, rule, detail });
    }
}

/// `unsafe`, `extern`, `thread`, `dyn`, `rwlock` and `RwLock`, anywhere (inside and outside `verus!`). Whole
/// identifier tokens only: `dynamic` or `RwLockPredicate` are other identifiers (the latter is reachable only through
/// the refused module name).
fn refuse_forbidden_tokens(tokens: &[Token], findings: &mut Findings) {
    for token in tokens {
        match token.ident() {
            Some("unsafe") => findings.refuse(token.line, rule::UNSAFE, "`unsafe`".into()),
            Some("extern") => findings.refuse(token.line, rule::EXTERN, "`extern`".into()),
            Some("thread") => findings.refuse(token.line, rule::DIRECT_THREAD, "`thread`".into()),
            Some("dyn") => findings.refuse(token.line, rule::DYN_TRAIT_OBJECT, "`dyn` (a trait object)".into()),
            Some(name @ ("rwlock" | "RwLock")) => findings.refuse(token.line, rule::VSTD_RWLOCK, format!("`{name}` (vstd::rwlock)")),
            _ => {}
        }
    }
}

/// The name of the generated declared-constraints module (`crate::gendb_constraints`).
const DECLARED_CONSTRAINTS_MODULE: &str = "gendb_constraints";

/// Whether `file` (relative to the crate's `src/`) is a storage interface file, `stores/<name>/interface/**`.
fn is_storage_interface(file: &str) -> bool {
    gendb_registry::author_definition(file).is_some_and(|d| d.name == "storage_interface")
}

/// Every identifier `gendb_constraints` of a storage interface file.
fn refuse_declared_constraints_module(tokens: &[Token], findings: &mut Findings) {
    for token in tokens.iter().filter(|t| t.ident() == Some(DECLARED_CONSTRAINTS_MODULE)) {
        findings.refuse(
            token.line,
            rule::INTERFACE_NAMES_DECLARED_CONSTRAINTS,
            "a storage interface names `gendb_constraints`, which is in no storage closure".into(),
        );
    }
}

/// Index of the `[` of an attribute `#[...]` or `#![...]` whose `#` is at `hash`.
fn attribute_bracket(tokens: &[Token], hash: usize) -> Option<usize> {
    if !tokens[hash].is_punct('#') {
        return None;
    }
    let mut open = hash + 1;
    if tokens.get(open).is_some_and(|t| t.is_punct('!')) {
        open += 1;
    }
    tokens.get(open).is_some_and(|t| t.is_punct('[')).then_some(open)
}

/// Every attribute, anywhere, against the allowed attribute and verifier-attribute lists.
fn check_attributes(tokens: &[Token], findings: &mut Findings) {
    let mut i = 0;
    while i < tokens.len() {
        match attribute_bracket(tokens, i) {
            Some(open) => {
                let end = group_end(tokens, open);
                // Body without the closing `]`. An unclosed `[` as the last token has an empty body (refused as an
                // attribute without a plain path); the earlier version panicked on it.
                let body_end = end.saturating_sub(1).max(open + 1);
                check_attribute(&tokens[open + 1..body_end], tokens[i].line, findings);
                i = end;
            }
            None => i += 1,
        }
    }
}

/// One attribute body (inside the brackets): `head...`, `verifier::NAME...` or `verifier(NAME, NAME(..), ...)`.
fn check_attribute(body: &[Token], line: usize, findings: &mut Findings) {
    let Some(head) = body.first().and_then(Token::ident) else {
        findings.refuse(line, rule::ATTRIBUTE, "attribute without a plain path".into());
        return;
    };
    if !ALLOWED_ATTRIBUTES.contains(&head) {
        findings.refuse(line, rule::ATTRIBUTE, format!("`#[{head}...]` is not in the allowed attribute list"));
        return;
    }
    if head == "derive" {
        macros::check_derive(body, line, findings);
        return;
    }
    if head != "verifier" {
        return;
    }
    for name in verifier_attribute_names(body) {
        if !ALLOWED_VERIFIER_ATTRIBUTES.contains(&name.as_str()) {
            findings.refuse(line, rule::VERIFIER_ATTRIBUTE, format!("`verifier::{name}` is not in the allowed verifier attribute list"));
        }
    }
}

/// Names of a `verifier` attribute body; an empty name when the form is neither `::NAME` nor `(...)`.
fn verifier_attribute_names(body: &[Token]) -> Vec<String> {
    match body.get(1).map(|t| &t.tok) {
        Some(Tok::Op("::")) => vec![body.get(2).and_then(Token::ident).unwrap_or_default().to_string()],
        Some(Tok::Punct('(')) => {
            // Top-level names of the list; arguments in nested groups are skipped.
            let end = group_end(body, 1);
            let mut names = Vec::new();
            let mut expect_name = true;
            let mut k = 2;
            while k + 1 < end {
                match &body[k].tok {
                    Tok::Punct('(' | '[' | '{') => {
                        k = group_end(body, k);
                        continue;
                    }
                    Tok::Punct(',') => expect_name = true,
                    Tok::Ident(name) if expect_name => {
                        names.push(name.clone());
                        expect_name = false;
                    }
                    _ => {}
                }
                k += 1;
            }
            names
        }
        _ => vec![String::new()],
    }
}

/// Top level: only `use`, `mod NAME;` (optionally `pub`/`pub(..)`), attributes and `verus! { ... }` blocks.
fn check_top_level_items(tokens: &[Token], findings: &mut Findings) {
    let mut i = 0;
    while i < tokens.len() {
        if tokens[i].is_punct('#') {
            i = attribute_bracket(tokens, i).map_or(i + 1, |open| group_end(tokens, open));
            continue;
        }
        if tokens[i].ident() == Some("verus") && tokens.get(i + 1).is_some_and(|t| t.is_punct('!')) && tokens.get(i + 2).is_some_and(|t| t.is_punct('{')) {
            i = group_end(tokens, i + 2);
            if tokens.get(i).is_some_and(|t| t.is_punct(';')) {
                i += 1;
            }
            continue;
        }
        match allowed_declaration_end(tokens, i) {
            Some(end) => i = end,
            None => {
                findings.refuse(tokens[i].line, rule::OUTSIDE_VERUS, "item outside `verus! { ... }`".into());
                i = skip_item(tokens, i);
            }
        }
    }
}

/// Index just past a `use ...;` or `mod NAME;` declaration (with optional visibility) starting at `start`.
fn allowed_declaration_end(tokens: &[Token], start: usize) -> Option<usize> {
    let mut j = start;
    if tokens[j].ident() == Some("pub") {
        j += 1;
        if tokens.get(j).is_some_and(|t| t.is_punct('(')) {
            j = group_end(tokens, j);
        }
    }
    match tokens.get(j).and_then(Token::ident) {
        Some("use") => {
            while j < tokens.len() && !tokens[j].is_punct(';') {
                j = if tokens[j].is_punct('{') { group_end(tokens, j) } else { j + 1 };
            }
            Some(j + 1)
        }
        Some("mod") if tokens.get(j + 1).and_then(Token::ident).is_some() && tokens.get(j + 2).is_some_and(|t| t.is_punct(';')) => Some(j + 3),
        _ => None,
    }
}

/// Skip one top-level item: up to and including a `;` or a closing top-level brace group (and a `;` after it).
fn skip_item(tokens: &[Token], mut i: usize) -> usize {
    while i < tokens.len() {
        match tokens[i].tok {
            Tok::Punct(';') => return i + 1,
            Tok::Punct('{') => {
                let end = group_end(tokens, i);
                return if tokens.get(end).is_some_and(|t| t.is_punct(';')) { end + 1 } else { end };
            }
            Tok::Punct('(' | '[') => i = group_end(tokens, i),
            _ => i += 1,
        }
    }
    i
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_items_are_found_but_not_the_static_lifetime() {
        let src = "use vstd::prelude::*;\nverus! {\nexec static CALLS: u64 ensures true { 0 }\nfn f(x: &'static [u8]) -> &'static [u8] { x }\n// static in a comment\nconst N: usize = 3;\n}\n";
        let found = scan_static_items("agent/mod.rs", src);
        assert_eq!(found.iter().map(|f| (f.line, f.rule)).collect::<Vec<_>>(), vec![(3, STATIC_ITEM_RULE.id)]);
    }

    /// The query freeze's path check: its original cases (moved here with the check) and a nested group.
    #[test]
    fn whole_statement_evaluator_references_are_found_lexically() {
        let found = |text: &str| !scan_whole_statement_evaluator("agent/mod.rs", text).is_empty();
        for text in [
            "use crate::exec::relational::eval::run;",
            "fn f() { crate::exec::relational::entry::go(); }",
            "use crate::exec::relational::{order, eval};",
            "use crate::exec::relational::{\n    entry as e,\n};",
            "use crate::exec::relational :: eval;",
            "use crate::exec::relational::{order::{sort_rows_exec, slice_exec}, entry::exec_ordered};",
        ] {
            assert!(found(text), "{text}");
        }
        for text in [
            "use crate::exec::relational::order::sort_rows_exec;",
            "// crate::exec::relational::eval in a comment\nfn f() {}",
            "let s = \"relational::eval\";",
            "use crate::exec::relational::{order, evaluation_helper};",
            "use crate::exec::relational::{ops::{eval_like, entry_point}, group};",
        ] {
            assert!(!found(text), "{text}");
        }
        let lines: Vec<(usize, &str)> =
            scan_whole_statement_evaluator("agent/a.rs", "use x;\nuse crate::exec::relational::{\n    rows,\n    eval,\n};\n").iter().map(|f| (f.line, f.rule)).collect();
        assert_eq!(lines, vec![(4, rule::WHOLE_STATEMENT_EVALUATOR)]);
        assert!(scan_static_items("agent/mod.rs", "verus! { fn g(s: &'static str) {} }").is_empty());
    }

    fn rules(src: &str) -> Vec<&'static str> {
        scan_source("m.rs", src).into_iter().map(|f| f.rule).collect()
    }

    #[test]
    fn accepts_ordinary_verus_module() {
        let src = r##"
            //! doc
            #![allow(unused)]
            use vstd::prelude::*;
            pub mod helper;
            verus! {
            // unsafe extern thread in a comment is ignored
            pub open spec fn f(s: Seq<int>) -> int decreases s.len() { if s.len() == 0 { 0 } else { f(s.drop_last()) } }
            #[verifier::opaque]
            pub closed spec fn g() -> bool { true }
            pub fn h<'a>(x: &'a [u8], c: char) -> (r: u64)
                requires x.len() < 10,
                ensures r != 5 || r == 5,
            {
                let s = "unsafe { extern } #[cfg(x)] include_str!(\"x\")";
                let q = 'u'; let e = '\''; let raw = r#"thread "# ;
                assert(forall|i: int| #![trigger x@[i]] 0 <= i < x.len() ==> x@[i] == x@[i]);
                if 1u64 != 2 { 1 } else { 2 }
            }
            } // verus!
        "##;
        assert_eq!(rules(src), Vec::<&str>::new());
    }

    #[test]
    fn refuses_each_rule() {
        let cases: &[(&str, &str)] = &[
            ("verus! { #[verifier::external_body] fn f() {} }", rule::VERIFIER_ATTRIBUTE),
            ("verus! { #[verifier(external)] fn f() {} }", rule::VERIFIER_ATTRIBUTE),
            ("verus! { #[verifier::r#external] fn f() {} }", rule::VERIFIER_ATTRIBUTE),
            ("verus! { fn f() { #[verifier::assume_termination] loop {} } }", rule::VERIFIER_ATTRIBUTE),
            ("verus! { #[verifier::exec_allows_no_decreases_clause] fn f() {} }", rule::VERIFIER_ATTRIBUTE),
            ("verus! { #[cfg(verus_keep_ghost_body)] fn f() {} }", rule::ATTRIBUTE),
            ("verus! { #[cfg_attr(x, verifier::external)] fn f() {} }", rule::ATTRIBUTE),
            ("verus! { #[verus::internal(external_body)] fn f() {} }", rule::ATTRIBUTE),
            ("verus! { fn f() -> bool { cfg!(verus_keep_ghost_body) } }", rule::MACRO),
            ("verus! { spec fn f() -> bool { module_path!()@.len() == 0 } }", rule::MACRO),
            ("use std::module_path as seq;\nverus! { spec fn f() -> bool { seq!()@.len() == 0 } }", rule::MACRO_IMPORT),
            ("verus! { #[derive(Hash)] struct S; }", rule::ATTRIBUTE),
            ("use crate::exec::value::EVal;\nverus! { impl EVal { spec fn view(&self) -> int { 0 } } }", rule::IMPL_OWNERSHIP),
            ("verus! { fn f() { let s = include_str!(\"/etc/x\"); } }", rule::MACRO),
            ("macro_rules! m { () => {} }", rule::MACRO),
            ("verus! { fn f() { unsafe { } } }", rule::UNSAFE),
            ("verus! { unsafe impl Send for S {} }", rule::UNSAFE),
            ("extern crate foo;", rule::EXTERN),
            ("verus! { fn f() { let h = vstd::thread::spawn(|| 1); } }", rule::DIRECT_THREAD),
            ("verus! { pub trait T { fn m(&self); } fn f(a: &dyn T) { a.m() } }", rule::DYN_TRAIT_OBJECT),
            ("verus! { fn f(g: Box<dyn Fn(u64) -> u64>) -> u64 { g(1) } }", rule::DYN_TRAIT_OBJECT),
            ("use vstd::rwlock::RwLock;", rule::VSTD_RWLOCK),
            ("use vstd::rwlock::*;", rule::VSTD_RWLOCK),
            ("use vstd::{rwlock as locks};", rule::VSTD_RWLOCK),
            ("verus! { fn f() { let l = vstd::r#rwlock::ReadHandle::<u64, P>::x(); } }", rule::VSTD_RWLOCK),
            ("verus! { fn f(l: &RwLock<u64, P>) { let h = l.acquire_read(); } }", rule::VSTD_RWLOCK),
            ("impl Drop for S { fn drop(&mut self) {} }", rule::OUTSIDE_VERUS),
            ("verus! { pub struct S; impl Drop for S { fn drop(&mut self) {} } }", rule::EXTERNAL_TRAIT_IMPL),
            ("verus! { pub trait Fam { type A: Copy; } }", rule::ASSOCIATED_TYPE_BOUND),
            ("verus! { pub trait T {} pub struct S; impl T for S {} pub fn mk() -> impl T { S } }", rule::IMPL_TRAIT_TYPE),
            ("#[used] static EVIL: u8 = 0;", rule::ATTRIBUTE),
            ("fn g() -> u64 { 0 }", rule::OUTSIDE_VERUS),
            ("pub mod inline { }", rule::OUTSIDE_VERUS),
        ];
        for (src, rule) in cases {
            assert!(rules(src).contains(rule), "{src} -> {:?}", rules(src));
        }
    }

    #[test]
    fn reports_file_and_line() {
        let f = scan_source("a/b.rs", "use vstd::prelude::*;\n\nverus! {\nfn f() { unsafe {} }\n}\n");
        assert_eq!(f, vec![RefusalFinding { file: "a/b.rs".into(), line: 4, rule: rule::UNSAFE, detail: "`unsafe`".into() }]);
    }

    #[test]
    fn unclosed_trailing_attribute_is_refused_not_a_panic() {
        for src in ["verus! {} #[", "verus! {} #![", "#["] {
            assert!(rules(src).contains(&rule::ATTRIBUTE), "{src} -> {:?}", rules(src));
        }
    }

    #[test]
    fn every_rule_id_is_in_the_table() {
        let ids: Vec<&str> = VERUS_REFUSAL_RULES.iter().map(|r| r.id).collect();
        for id in [
            rule::FILE_SET, rule::OUTSIDE_VERUS, rule::ATTRIBUTE, rule::VERIFIER_ATTRIBUTE, rule::UNSAFE, rule::EXTERN, rule::MACRO,
            rule::MACRO_IMPORT, rule::IMPL_OWNERSHIP, rule::DIRECT_THREAD, rule::DYN_TRAIT_OBJECT, rule::VSTD_RWLOCK,
            rule::INTERFACE_NAMES_DECLARED_CONSTRAINTS, rule::EXTERNAL_TRAIT_IMPL, rule::ASSOCIATED_TYPE_BOUND, rule::IMPL_TRAIT_TYPE,
        ] {
            assert!(ids.contains(&id), "{id}");
        }
        assert_eq!(ids.len(), 16);
    }

    /// The trait-object and rwlock rules match whole identifier tokens: comments, strings and longer identifiers do
    /// not count, and the lock types are refused through the module name that every path to them contains.
    #[test]
    fn trait_object_and_rwlock_rules_match_whole_tokens() {
        let src = "verus! {\n// dyn rwlock RwLock\nfn f() { let dynamic = 1u8; let rwlocks = \"dyn RwLock\"; let my_rwlock = 'd'; }\n}\n";
        assert_eq!(rules(src), Vec::<&str>::new());
        let found = scan_source("agent/mod.rs", "use vstd::rwlock::{RwLock, RwLockPredicate};\nverus! {\nfn f(a: &dyn T) {}\n}\n");
        let found: Vec<(usize, &str, &str)> = found.iter().map(|f| (f.line, f.rule, f.detail.as_str())).collect();
        assert_eq!(found, vec![
            (1, rule::VSTD_RWLOCK, "`rwlock` (vstd::rwlock)"),
            (1, rule::VSTD_RWLOCK, "`RwLock` (vstd::rwlock)"),
            (3, rule::DYN_TRAIT_OBJECT, "`dyn` (a trait object)"),
        ]);
    }

    /// Regression inputs: the termination probes that the pinned Verus accepted under `--no-cheating` and the scan
    /// before these rules passed (h5b and k1: recursion through `&dyn T`, an exec function that never returns and one
    /// that returns a wrong answer; i5: `false` proved in proof code; h7: a second `acquire_write` that spins). Each is
    /// now refused exactly where it names a trait object or vstd's rwlock; h7 also implements vstd's `RwLockPredicate`,
    /// an external trait outside the allowlist. The soundness probes are checked through freezing
    /// (`tests/verus_author_freeze.rs`).
    #[test]
    fn termination_probes_are_refused() {
        const H5B: &str = include_str!("../../tests/fixtures/verus_termination/h5b-dyn-recursion-false-ensures.rs");
        const I5: &str = include_str!("../../tests/fixtures/verus_termination/i5-proof-recursion-through-dyn.rs");
        const K1: &str = include_str!("../../tests/fixtures/verus_termination/k1-dyn-false-wrong-answer.rs");
        const H7: &str = include_str!("../../tests/fixtures/verus_termination/h7-rwlock-double-acquire.rs");
        let cases: [(&str, &str, Vec<(usize, &str)>); 4] = [
            ("h5b", H5B, vec![(11, rule::DYN_TRAIT_OBJECT)]),
            ("i5", I5, vec![(11, rule::DYN_TRAIT_OBJECT)]),
            ("k1", K1, vec![(11, rule::DYN_TRAIT_OBJECT)]),
            ("h7", H7, vec![(4, rule::VSTD_RWLOCK), (4, rule::VSTD_RWLOCK), (7, rule::EXTERNAL_TRAIT_IMPL), (13, rule::VSTD_RWLOCK)]),
        ];
        for (name, src, expected) in cases {
            let found: Vec<(usize, &str)> = scan_source("agent/mod.rs", src).iter().map(|f| (f.line, f.rule)).collect();
            assert_eq!(found, expected, "{name}");
        }
    }

    /// Storage interface files may not name the declared-constraints module in any form the scanner reads (path, use,
    /// alias, group, glob, raw identifier, `super` path, inside a supported macro); comments and strings do not count;
    /// builders and query modules may name it.
    #[test]
    fn interfaces_may_not_name_the_declared_constraints_module() {
        let interface = |src: &str| {
            scan_source("stores/s/interface/readers/a.rs", src).iter().filter(|f| f.rule == rule::INTERFACE_NAMES_DECLARED_CONSTRAINTS).count()
        };
        for src in [
            "use crate::gendb_constraints::declared_db;",
            "use crate::gendb_constraints as c;",
            "use crate::{schema, gendb_constraints::{self as k}};",
            "use crate::gendb_constraints::*;",
            "use crate::r#gendb_constraints::declared_schema;",
            "verus! { spec fn f(db: Database) -> bool { crate::gendb_constraints::declared_db(db) == db } }",
            "verus! { spec fn f() -> Seq<int> { seq![super::super::super::gendb_constraints::N] } }",
        ] {
            assert_eq!(interface(src), 1, "{src}");
        }
        assert_eq!(interface("// gendb_constraints\nverus! { spec fn f() -> bool { \"gendb_constraints\"@.len() > 0 } }"), 0);
        assert_eq!(interface("use crate::gendb_constraints_extra::x;"), 0, "another identifier");
        let src = "use crate::gendb_constraints::declared_db;";
        for other in ["builder/mod.rs", "agent/mod.rs", "stores/s/declaration.rs", "stores/s/interfaces.rs"] {
            assert!(scan_source(other, src).is_empty(), "{other}");
        }
        assert_eq!(interface("verus! {\n\nuse crate::gendb_constraints::declared_db;\n}"), 1);
        assert_eq!(scan_source("stores/s/interface/mod.rs", src)[0].line, 1);
    }
}
