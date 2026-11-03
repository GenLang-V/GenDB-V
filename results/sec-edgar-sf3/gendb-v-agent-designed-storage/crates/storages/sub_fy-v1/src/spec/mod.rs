//! `spec`: the fixed mathematical meaning of the supported PostgreSQL fragment. Every item is plain data or a
//! Verus `spec` function or lemma over mathematical integers and sequences; nothing here depends on `exec`,
//! `bridge` or `link`.
//!
//! Trust: the definitions are trusted. They are the meaning every verified statement is proved against, so a
//! change here changes what every claim says. The lemmas are checked by the pinned Verus with `--no-cheating`;
//! nothing uses `assume`, `admit` or `external_body`.
//!
//! Source layout. The module paths stay `spec::<name>`, the paths the emitter, the framework and authors import.
//! The framework assembles `sqlspec/syntax/<name>.rs` and `sqlspec/semantics/<name>.rs` as `spec/<name>.rs`
//! (and this file as `spec/mod.rs`) in the checked library and in every candidate crate:
//! - `syntax/`: the language as data: declared SQL types, schemas with constraint declarations and static
//!   types (`types`), and the typed AST (`ast`). The operator tags the AST names (`IntKind`, `NumKind`,
//!   `ArithOp`, `CmpOp`, `CastOp`) stay next to their meaning in `int` and `scalar`.
//! - `semantics/`: what the language means: PostgreSQL value-domain constants (`limits`); values, NULL,
//!   three-valued logic and SQL errors (`value`); exact operators (`int`, `numeric`, `datetime`, `text`,
//!   `chars`, `scalar`); SQL value equality (`equality`); scalar functions (`fns`) and aggregates (`aggs`);
//!   relational operators on evaluated inputs (`relation`); the denotation (`eval`); top-level ORDER BY /
//!   LIMIT / OFFSET (`order`); static typing and database input domains (`typing`); integrity constraints
//!   (`constraints`).
//!
//! The declaration order below is the checked one; keep it.
pub mod limits;
pub mod types;
pub mod value;
pub mod int;
pub mod numeric;
pub mod datetime;
pub mod text;
pub mod chars;
pub mod scalar;
pub mod equality;
pub mod fns;
pub mod aggs;
pub mod ast;
pub mod relation;
pub mod eval;
pub mod order;
pub mod typing;
pub mod constraints;
