//! SQLSpec: GenDB's one SQL semantics library and the host side of its verified reference evaluator.
//!
//! The Verus library lives beside this crate in `sqlspec/{syntax,semantics,interpreter,proofs}` (root
//! `sqlspec/library.rs`); it is checked by the pinned Verus, never compiled by Cargo. This crate provides:
//! - [`library`]: the library sources, embedded at compile time, at their logical paths (`spec`, `exec`, `bridge`,
//!   `link`, `pins`) with the module sets candidate and evaluator crates copy;
//! - [`evaluator`]: the reference evaluator crate's sources, its echo text, and loading/calling a compiled one;
//! - [`codec`]: the value wire formats shared with the trusted shims (`GSQLDB1` database, `GSQLRS1` result);
//! - [`pg_text`]: PostgreSQL text forms of values (date/timestamp input, output rendering, result records);
//! - [`fixtures`]: the PostgreSQL reference fixture format and its input codec.
//!
//! Trust boundary: the `spec` definitions, the SQL -> AST translation (`gendb_frontend`), the codecs here, the
//! evaluator shim and the loader are trusted; the interpreter, bridges, link toolkit, examples and the evaluator
//! entry are checked by Verus with `--no-cheating`.
//!
//! Dependencies: `gendb_frontend` only (AST types and the translator). Freezing, verifying and compiling crates is
//! `gendb_verification` (`verus`, `reference`), which depends on this crate, never the reverse.

pub mod codec;
pub mod evaluator;
pub mod fixtures;
pub mod library;
pub mod pg_text;
