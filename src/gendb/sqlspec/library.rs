//! SQLSpec: the Verus SQL semantics library, checked as one crate by the pinned Verus with `--no-cheating`.
//!
//! Every crate the framework assembles copies modules of this library at the logical paths below. The physical
//! sources live in `sqlspec/{syntax,semantics,interpreter,proofs}`; the host crate `gendb_sqlspec::library` embeds
//! them at compile time and maps each file to its logical path.
//! - `spec`   (`spec.rs`, `syntax/`, `semantics/`): the fixed meaning of the supported PostgreSQL fragment. TRUSTED
//!            definitions: every verified statement is proved against them.
//! - `exec`   (`interpreter/`): the verified reference interpreter over machine values, the executable domain and
//!            the `Capacity` refusal. Checked against `spec`.
//! - `bridge` (`proofs/bridge/`): theorems about `spec` that `exec`, `link` and agent proofs use. Checked.
//! - `link`   (`proofs/link/`): the generic proof toolkit of candidate crates; its source-relation definitions
//!            are part of the fixed meaning (see `link.rs`). Checked.
//! - `pins`   (`proofs/examples/`): checked examples of the meaning on concrete values, schemas and ASTs. Only this
//!            library crate contains them.
//!
//! Nothing in this crate uses `assume`, `admit`, `external_body` or `assume_specification`. The declaration order
//! below is the checked one; keep it.
#![allow(unused_imports)]
#![allow(non_snake_case)]

pub mod spec;
pub mod exec;
pub mod bridge;
pub mod link;
pub mod pins;
