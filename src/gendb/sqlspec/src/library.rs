//! The SQLSpec Verus library, embedded at compile time (`build.rs`): every file at its logical path in an assembled
//! crate. The framework copies these texts into the crates it checks; nothing reads the source tree at run time,
//! so a binary always assembles the library it was built with.
//!
//! Top-level modules and which crates copy them:
//! - the checked library crate (`lib.rs` = physical `sqlspec/library.rs`): every module;
//! - candidate crates of the fixed entry: [`CANDIDATE_MODULES`] (the semantics and the proof toolkit);
//! - reference evaluator crates: [`EVALUATOR_MODULES`] (the semantics and the interpreter with its bridges).
//!
//! Trust: `spec` definitions are trusted (they are the fixed meaning); everything else is checked by Verus. The
//! embedding itself is a byte copy.

/// One Verus source file of the library.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LibraryFile {
    /// Logical path relative to the crate's `src/` (for example `exec/relational/eval.rs`).
    pub path: &'static str,
    /// Physical path relative to `src/gendb/sqlspec/` (for example `interpreter/relational/eval.rs`).
    pub source: &'static str,
    pub text: &'static str,
}

/// Every file of the checked library, the root `lib.rs` included, sorted by logical path.
pub static FILES: &[LibraryFile] = include!(concat!(env!("OUT_DIR"), "/library_files.rs"));

/// Logical path of the library root.
pub const ROOT_PATH: &str = "lib.rs";

/// A top-level module of the library.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Module {
    /// The fixed SQL meaning (trusted definitions).
    Spec,
    /// The verified reference interpreter.
    Exec,
    /// Theorems about the meaning.
    Bridge,
    /// The generic proof toolkit of candidate crates.
    Link,
    /// Checked examples (library crate only).
    Pins,
}

/// Declaration order of the library root.
pub const ALL_MODULES: &[Module] = &[Module::Spec, Module::Exec, Module::Bridge, Module::Link, Module::Pins];
/// Modules a candidate crate of the fixed entry copies.
pub const CANDIDATE_MODULES: &[Module] = &[Module::Spec, Module::Exec, Module::Bridge, Module::Link];
/// Modules a reference evaluator crate copies.
pub const EVALUATOR_MODULES: &[Module] = &[Module::Spec, Module::Exec, Module::Bridge];

impl Module {
    pub const fn name(self) -> &'static str {
        match self {
            Module::Spec => "spec",
            Module::Exec => "exec",
            Module::Bridge => "bridge",
            Module::Link => "link",
            Module::Pins => "pins",
        }
    }

    /// The module a logical path belongs to (`exec/ast.rs` and `exec.rs` -> `Exec`); `None` for the root and for
    /// paths outside the library.
    pub fn of_path(path: &str) -> Option<Module> {
        let first = path.split('/').next().unwrap_or("");
        let name = first.strip_suffix(".rs").unwrap_or(first);
        ALL_MODULES.iter().copied().find(|m| m.name() == name)
    }
}

/// The library root file.
pub fn root() -> &'static LibraryFile {
    FILES.iter().find(|f| f.path == ROOT_PATH).expect("build.rs embeds library.rs as lib.rs")
}

/// Files of the given modules, sorted by logical path (the root is not a module file).
pub fn module_files(modules: &[Module]) -> Vec<&'static LibraryFile> {
    FILES.iter().filter(|f| Module::of_path(f.path).is_some_and(|m| modules.contains(&m))).collect()
}

/// Crate-root declarations of the given modules (`pub mod spec;\n...`), in the given order.
pub fn module_declarations(modules: &[Module]) -> String {
    modules.iter().map(|m| format!("pub mod {};\n", m.name())).collect()
}

/// The inner attributes of the library root (`#![...]` lines). Every crate that copies library modules needs them.
pub fn crate_attributes() -> impl Iterator<Item = &'static str> {
    root().text.lines().filter(|l| l.starts_with("#!["))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The root declares exactly the modules that have files, in `ALL_MODULES` order, and every file has a module.
    #[test]
    fn root_declares_every_module_with_files() {
        let declared: Vec<&str> =
            root().text.lines().filter_map(|l| l.strip_prefix("pub mod ").and_then(|r| r.strip_suffix(';'))).collect();
        assert_eq!(declared, ALL_MODULES.iter().map(|m| m.name()).collect::<Vec<_>>());
        for f in FILES.iter().filter(|f| f.path != ROOT_PATH) {
            assert!(Module::of_path(f.path).is_some(), "{} ({}) belongs to no module", f.path, f.source);
        }
        for m in ALL_MODULES {
            assert!(!module_files(&[*m]).is_empty(), "{} has no files", m.name());
        }
    }

    /// Module files exist for every `pub mod` a module file declares (`link.rs` declares `link/<m>.rs`), so an
    /// assembled crate never misses a declared file.
    #[test]
    fn declared_submodules_are_embedded() {
        for f in FILES.iter().filter(|f| f.path != ROOT_PATH) {
            let dir = f.path.strip_suffix("/mod.rs").or_else(|| f.path.strip_suffix(".rs")).unwrap();
            for line in f.text.lines() {
                if let Some(name) = line.strip_prefix("pub mod ").and_then(|r| r.strip_suffix(';')) {
                    let (flat, nested) = (format!("{dir}/{name}.rs"), format!("{dir}/{name}/mod.rs"));
                    assert!(FILES.iter().any(|g| g.path == flat || g.path == nested), "{} declares missing {name}", f.path);
                }
            }
        }
    }

    #[test]
    fn candidate_closure_matches_the_entry_layout() {
        let files = module_files(CANDIDATE_MODULES);
        assert!(files.iter().any(|f| f.path == "link.rs") && !files.iter().any(|f| f.path == "link/mod.rs"));
        assert!(files.iter().any(|f| f.path == "bridge/params.rs") && !files.iter().any(|f| f.path.starts_with("pins/")));
        assert!(files.iter().any(|f| f.path == "exec/relational/entry.rs" && f.source == "interpreter/relational/entry.rs"));
        assert!(!FILES.iter().any(|f| f.source.starts_with("interpreter/host/")));
        assert_eq!(module_declarations(CANDIDATE_MODULES), "pub mod spec;\npub mod exec;\npub mod bridge;\npub mod link;\n");
        assert_eq!(crate_attributes().collect::<Vec<_>>(), ["#![allow(unused_imports)]", "#![allow(non_snake_case)]"]);
    }
}
