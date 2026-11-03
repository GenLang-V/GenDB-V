//! Multi-root author freeze (`verus::freeze_author_crate`) on real directories, no Verus: a storage crate's two author
//! roots are copied, scanned with `src/`-relative paths and sealed read-only; a query crate's framework copy of a
//! storage interface is scanned like author text; a missing root `mod.rs`, nested roots and a framework file inside an
//! author root are refused. Every termination and soundness probe that the pinned Verus accepted under `--no-cheating`
//! is refused when it is frozen as a query module (`verus::freeze_crate`), and the trait patterns admitted code uses
//! are accepted.
use gendb_verification::verus::{freeze_author_crate, freeze_crate, rule, AuthorRoot, FrameworkSource, FreezeError};
use std::path::{Path, PathBuf};

const LIB_RS: &str = "pub mod stores;\npub mod builder;\n";
const CLEAN: &str = "use vstd::prelude::*;\nverus! {\npub open spec fn represents(n: nat) -> bool { n >= 0 }\n}\n";
const UNSAFE: &str = "use vstd::prelude::*;\nverus! {\npub fn build() { unsafe { } }\n}\n";

fn scratch(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("verus-author-freeze-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// A workspace author directory with `files` (`(relative path, text)`).
fn tree(dir: &Path, files: &[(&str, &str)]) -> PathBuf {
    for (path, text) in files {
        let file = dir.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, text).unwrap();
    }
    dir.to_path_buf()
}

fn framework(files: &[(&str, &str)]) -> Vec<FrameworkSource> {
    files.iter().map(|(path, text)| FrameworkSource { path: path.to_string(), text: text.to_string() }).collect()
}

fn refused(result: Result<gendb_verification::verus::FrozenCrate, FreezeError>) -> Vec<(String, &'static str)> {
    match result {
        Err(FreezeError::Refused { findings }) => findings.into_iter().map(|f| (f.file, f.rule)).collect(),
        other => panic!("expected a refusal, got {other:?}"),
    }
}

#[test]
fn storage_roots_are_copied_scanned_and_sealed() {
    let work = scratch("storage");
    let interface = tree(&work.join("ws/interface"), &[("mod.rs", CLEAN), ("zones.rs", CLEAN)]);
    let builder = tree(&work.join("ws/builder"), &[("mod.rs", CLEAN), ("blocks/mod.rs", CLEAN)]);
    let roots = [AuthorRoot { crate_directory: "stores/s/interface", source: &interface }, AuthorRoot { crate_directory: "builder", source: &builder }];
    let frozen = freeze_author_crate(&framework(&[("lib.rs", LIB_RS), ("stores/s/mod.rs", "pub mod interface;\n")]), &roots, &work.join("frozen")).unwrap();
    assert_eq!(frozen.author_files, ["builder/blocks/mod.rs", "builder/mod.rs", "stores/s/interface/mod.rs", "stores/s/interface/zones.rs"]);
    assert!(frozen.agent_files.is_empty());
    assert_eq!(std::fs::read_to_string(frozen.root.join("src/builder/blocks/mod.rs")).unwrap(), CLEAN);
    let readonly = |p: &Path| std::fs::metadata(p).unwrap().permissions().readonly();
    assert!(readonly(&frozen.root.join("src/stores/s/interface/zones.rs")) && readonly(&frozen.root.join("src/lib.rs")));

    // A finding names the file relative to `src/`; the refused snapshot is kept.
    let builder = tree(&work.join("ws2/builder"), &[("mod.rs", UNSAFE)]);
    let roots = [AuthorRoot { crate_directory: "stores/s/interface", source: &interface }, AuthorRoot { crate_directory: "builder", source: &builder }];
    let findings = refused(freeze_author_crate(&framework(&[("lib.rs", LIB_RS)]), &roots, &work.join("frozen-unsafe")));
    assert_eq!(findings, [("builder/mod.rs".to_string(), rule::UNSAFE)]);
    assert!(work.join("frozen-unsafe/src/builder/mod.rs").exists());

    // Each root needs its own `mod.rs`.
    let no_root = tree(&work.join("ws3/interface"), &[("zones.rs", CLEAN)]);
    let builder = tree(&work.join("ws3/builder"), &[("mod.rs", CLEAN)]);
    let roots = [AuthorRoot { crate_directory: "stores/s/interface", source: &no_root }, AuthorRoot { crate_directory: "builder", source: &builder }];
    let findings = refused(freeze_author_crate(&framework(&[("lib.rs", LIB_RS)]), &roots, &work.join("frozen-no-root")));
    assert_eq!(findings, [("stores/s/interface/mod.rs".to_string(), rule::FILE_SET)]);
}

#[test]
fn query_interface_copies_are_scanned_and_bad_roots_write_nothing() {
    let work = scratch("query");
    let agent = tree(&work.join("ws/agent"), &[("mod.rs", CLEAN)]);
    let roots = [AuthorRoot { crate_directory: "agent", source: &agent }];
    let copy = "use vstd::prelude::*;\nverus! {\npub open spec fn crate_named() -> bool { module_path!()@.len() == 0 }\n}\n";
    let files = framework(&[("lib.rs", "pub mod stores;\npub mod agent;\n"), ("stores/s/interface/mod.rs", copy)]);
    let findings = refused(freeze_author_crate(&files, &roots, &work.join("frozen-copy")));
    assert_eq!(findings, [("stores/s/interface/mod.rs".to_string(), rule::MACRO)]);
    let frozen = freeze_author_crate(&framework(&[("lib.rs", "pub mod agent;\n"), ("stores/s/interface/mod.rs", CLEAN)]), &roots, &work.join("frozen")).unwrap();
    assert_eq!((frozen.agent_files, frozen.author_files), (vec!["mod.rs".to_string()], vec!["agent/mod.rs".to_string()]));

    let framework_error = |roots: &[AuthorRoot<'_>], files: &[FrameworkSource], name: &str| {
        let destination = work.join(name);
        match freeze_author_crate(files, roots, &destination) {
            Err(FreezeError::Framework { message }) => {
                assert!(!destination.exists(), "{name}: nothing is written");
                message
            }
            other => panic!("{name}: expected a framework error, got {other:?}"),
        }
    };
    let lib = framework(&[("lib.rs", LIB_RS)]);
    let nested = [AuthorRoot { crate_directory: "stores/s/interface", source: &agent }, AuthorRoot { crate_directory: "stores/s/interface/inner", source: &agent }];
    assert!(framework_error(&nested, &lib, "nested").contains("equal or nested"));
    let inside = framework(&[("lib.rs", LIB_RS), ("builder/helper.rs", "")]);
    assert!(framework_error(&[AuthorRoot { crate_directory: "builder", source: &agent }], &inside, "inside").contains("belongs to the author"));
    assert!(framework_error(&[AuthorRoot { crate_directory: "gendb_entry", source: &agent }], &lib, "not-author").contains("invalid author root"));
}

/// The probes in `fixtures/verus_termination/` that the pinned Verus verified with the admission flags although they
/// prove `false`, return a wrong answer or never return, frozen as `agent/mod.rs` of a query crate: each is refused by
/// the scan, before Verus, with exactly these findings (line, rule).
#[test]
fn accepted_verus_probes_are_refused_at_freeze() {
    macro_rules! probe {
        ($file:literal) => {
            ($file, include_str!(concat!("fixtures/verus_termination/", $file)))
        };
    }
    let cases: [((&str, &str), Vec<(usize, &str)>); 12] = [
        // Recursion through a trait object (proof of false, never returns, wrong answer) and vstd's rwlock (spins).
        (probe!("h5b-dyn-recursion-false-ensures.rs"), vec![(11, rule::DYN_TRAIT_OBJECT)]),
        (probe!("i5-proof-recursion-through-dyn.rs"), vec![(11, rule::DYN_TRAIT_OBJECT)]),
        (probe!("k1-dyn-false-wrong-answer.rs"), vec![(11, rule::DYN_TRAIT_OBJECT)]),
        (probe!("h7-rwlock-double-acquire.rs"), vec![(4, rule::VSTD_RWLOCK), (4, rule::VSTD_RWLOCK), (7, rule::EXTERNAL_TRAIT_IMPL), (13, rule::VSTD_RWLOCK)]),
        // A bound on an associated type: proof, spec and exec forms, the trait-level where form, and std's IntoIterator.
        (probe!("v05-assoc-type-proof-false.rs"), vec![(11, rule::ASSOCIATED_TYPE_BOUND)]),
        (probe!("v05b-assoc-type-spec-false.rs"), vec![(10, rule::ASSOCIATED_TYPE_BOUND)]),
        (probe!("v05d-assoc-type-exec-never-returns.rs"), vec![(11, rule::ASSOCIATED_TYPE_BOUND)]),
        (probe!("v05e-trait-where-assoc-bound-false.rs"), vec![(10, rule::ASSOCIATED_TYPE_BOUND)]),
        (probe!("v22-std-intoiterator-assoc-bound-false.rs"), vec![(13, rule::EXTERNAL_TRAIT_IMPL), (25, rule::EXTERNAL_TRAIT_IMPL), (34, rule::EXTERNAL_TRAIT_IMPL)]),
        // Exec recursion that never returns: an `impl Trait` return type, a Drop impl, a derived PartialEq over a manual one.
        (probe!("v01-impl-trait-return-recursion.rs"), vec![(11, rule::IMPL_TRAIT_TYPE)]),
        (probe!("v11-drop-recursion.rs"), vec![(9, rule::EXTERNAL_TRAIT_IMPL)]),
        (probe!("v18b-derived-partialeq-manual-impl-cycle.rs"), vec![(13, rule::EXTERNAL_TRAIT_IMPL), (17, rule::EXTERNAL_TRAIT_IMPL), (24, rule::EXTERNAL_TRAIT_IMPL)]),
    ];
    let work = scratch("probes");
    let lib = framework(&[("lib.rs", "pub mod agent;\n")]);
    for ((name, text), expected) in cases {
        let agent = tree(&work.join(name).join("agent"), &[("mod.rs", text)]);
        match freeze_crate(&agent, &lib, &work.join(name).join("frozen")) {
            Err(FreezeError::Refused { findings }) => {
                assert!(findings.iter().all(|f| f.file == "mod.rs"), "{name}: {findings:?}");
                assert_eq!(findings.iter().map(|f| (f.line, f.rule)).collect::<Vec<_>>(), expected, "{name}");
            }
            other => panic!("{name}: expected a refusal, got {other:?}"),
        }
    }
}

/// The trait patterns admitted code uses pass the freeze scan: manual Clone/Copy and View for own types, a WorkerTask
/// with its Output type, the supported derives, own traits (with supertraits and an unbounded associated type)
/// implemented for own and built-in types.
#[test]
fn admitted_trait_patterns_are_accepted_at_freeze() {
    const ALLOWED: &str = r#"use vstd::prelude::*;
use crate::gendb_entry::parallel::{fork_join, WorkerTask};
verus! {
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Key { pub k: u64 }
pub struct Cols { pub a: u64 }
impl Clone for Cols { fn clone(&self) -> (r: Cols) ensures r == *self { Cols { a: self.a } } }
impl Copy for Cols {}
impl View for Cols { type V = int; open spec fn view(&self) -> int { self.a as int } }
pub struct Task<S: Idx> { pub lo: S }
impl<S: Idx> WorkerTask for Task<S> {
    type Output = u64;
    open spec fn pre(&self) -> bool { true }
    open spec fn post(&self, out: u64) -> bool { true }
    fn declared_rows(&self) -> (u64, u64) { (0, 0) }
    fn run(self) -> (out: u64) { 0 }
}
pub trait Family { type Item; spec fn item(&self) -> Self::Item; }
impl Family for Cols { type Item = u64; open spec fn item(&self) -> u64 { self.a } }
pub trait Idx: Copy + Send + Sync + 'static { spec fn idx(&self) -> int; }
impl Idx for u32 { open spec fn idx(&self) -> int { *self as int } }
}
"#;
    let work = scratch("allowed");
    let agent = tree(&work.join("agent"), &[("mod.rs", ALLOWED)]);
    let frozen = freeze_crate(&agent, &framework(&[("lib.rs", "pub mod agent;\n")]), &work.join("frozen")).unwrap();
    assert_eq!(frozen.agent_files, ["mod.rs"]);
}
