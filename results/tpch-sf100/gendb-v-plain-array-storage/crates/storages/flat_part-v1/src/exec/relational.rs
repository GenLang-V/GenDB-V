//! `exec::relational`: the verified relational evaluator over the executable AST — a materialized reference
//! implementation whose every postcondition is the compositional bridge to `spec::eval` / `spec::order`.
//! Nothing here is trusted (checked with `--no-cheating`, no `assume`/`admit`/`external_body`).
//!
//! The framework assembles `sqlspec/interpreter/relational/<name>.rs` as `exec/relational/<name>.rs` (this file is
//! `exec/relational.rs`); module paths are the ones the emitter, the framework and authors import.
//! - representation: `schema` (runtime database `EDatabase` and its view onto `spec::value::Database`), `rows`
//!   (row copies and concatenations);
//! - domain and checks: `domain` (the finite executable domain `fits_pred` / `fits_query` and the SUM/AVG mass
//!   condition; never a SQL outcome), `check` (`check_db` = `db_wf`, `check_ordered` = `wf_ordered`),
//!   `constraints` (declared integrity constraints, `spec::constraints`);
//! - operators over evaluated inputs: `ops` (Table, Filter, Project, Product, LEFT JOIN, static arity),
//!   `aggregate` (aggregate values of one group: COUNT, exact SUM, dispatch to `exec::aggs`), `group`
//!   (aggregation queries: aggregate arguments per row, `Aggregate`, `GroupBy`), `order` (key comparison,
//!   stable sort, OFFSET/LIMIT);
//! - evaluation: `eval` (`exec_pred` / `exec_query`, the dispatch per constructor), `entry` (`exec_ordered` for a
//!   top-level statement and the checked entry point `evaluate`). `eval` and `entry` are the whole-query
//!   evaluator; query authors use the operators and helpers, not these two modules.
//!
//! The declaration order below is the checked one; keep it.
pub mod schema;
pub mod rows;
pub mod domain;
pub mod aggregate;
pub mod ops;
pub mod group;
pub mod eval;
pub mod order;
pub mod check;
pub mod constraints;
pub mod entry;
