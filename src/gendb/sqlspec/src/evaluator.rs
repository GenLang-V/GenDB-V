//! The reference evaluator: one small Verus crate per translated statement that runs SQLSpec's verified
//! interpreter on a database, used to check expected results (PostgreSQL differential tests, admission
//! references). This module holds the parts that need no toolchain:
//! - [`crate_files`]: the evaluator crate's source files (library modules, the translated statement, the generated
//!   executable schema, the verified entry `abi.rs` and the trusted shim `shim.rs`);
//! - [`echo_text`]: the host's rendering of a translated AST in the shim's echo grammar (translation validation);
//! - [`EvaluatorLibrary`]: loading a compiled evaluator and calling it through the C ABI.
//!
//! Freezing, verifying and compiling a crate is `gendb_verification::reference`.
//!
//! Trust. Checked by Verus in every evaluator crate: the interpreter (`exec`), the bridges and the entry `abi.rs`
//! (`abi_run` returns exactly `denote_top` of the statement on the supplied rows, or the documented input-domain
//! outcome). Trusted: the `spec` definitions; the SQL -> AST translation and emission (`gendb_frontend`, validated
//! per build by the echo comparison, which checks the emitted AST, not its relation to the SQL text); the generated
//! schema module's input (the translated schema); the shim and the wire codec (`crate::codec`); the fixture input
//! codec (`crate::fixtures`); the loader, `dlopen` and the pinned toolchain.

mod crate_files;
mod echo;
mod loader;

pub use crate_files::{
    crate_files, crate_root, schema_module, SourceFile, CRATE_IDENTITY, ENTRY_FILE, ENTRY_SOURCE, SHIM_FILE, SHIM_SOURCE,
    UNSCANNED_TRUSTED_FILES,
};
pub use echo::echo_text;
pub use loader::{EvaluatorError, EvaluatorLibrary, ABI_VERSION};
