//! `exec`: the verified reference interpreter. It evaluates the executable AST over machine values, and the
//! postcondition of every operator is its bridge to the fixed meaning in `spec`: a result equals the denotation,
//! a SQL error is the denoted error, and `value::Capacity` is returned exactly when the `domain` predicate says an
//! exact intermediate does not fit the machine representation (never a SQL outcome).
//!
//! Trust: nothing here is trusted. Every function is checked against `spec` by the pinned Verus with
//! `--no-cheating`; nothing uses `assume`, `admit` or `external_body`. The only trusted inputs are the `spec`
//! definitions the postconditions name.
//!
//! Source layout. The module paths stay `exec::<name>`, the paths the emitter, the framework and authors import.
//! The framework assembles `sqlspec/interpreter/<name>.rs` as `exec/<name>.rs` (this file is `exec/mod.rs`).
//! - representation: machine values, rows and the `Capacity` refusal (`value`); the executable AST and its
//!   structural view onto `spec::ast` (`ast`); the executable domain and the timestamp representation
//!   invariant (`domain`);
//! - scalar operators, one module per `spec` module: `numeric`, `datetime`, `text`, `chars`, `scalar`
//!   (arithmetic, casts, comparison, three-valued logic), `equality` (IS NOT DISTINCT FROM, DISTINCT);
//! - scalar functions `fns` and aggregates beyond COUNT/SUM `aggs`, one module per feature;
//! - the expression evaluator `expr` and the relational evaluator `relational` (one mutual recursion through
//!   subqueries and CASE conditions).
//!
//! Naming: `<spec function>_exec` is the executable counterpart of one `spec` function (`cast_exec` of
//! `spec::scalar::cast`); `exec_<sort>` evaluates an AST sort, function family or aggregate (`exec_expr`,
//! `exec_fn`, `exec_avg`).
//!
//! The declaration order below is the checked one; keep it.
pub mod value;
pub mod ast;
pub mod domain;
pub mod numeric;
pub mod datetime;
pub mod text;
pub mod chars;
pub mod scalar;
pub mod equality;
pub mod fns;
pub mod aggs;
pub mod expr;
pub mod relational;
