//! SQL frontend: from SQL text to the typed AST and its Verus meaning.
//!
//! - `parser` runs the Python SQLGlot parser/binder (`frontend/parser/`, PostgreSQL name/type/cast resolution and
//!   lowering) on SQL + schema DDL + explicit dialect, under an explicit deployment policy (`SqlParser`).
//! - `ast` decodes and validates its output, the resolved typed AST document `gendb-sql-ast-v1`, against the one
//!   encoding schema `frontend/ast/ast_schema.json` (shared with the Python parser).
//! - `params` typed statement parameters `$n`: declared types, exact values, domains, substitution of fixed parameters
//!   (one path for concrete statements, templates and partial specializations).
//! - `columns` the environment layout of every AST node and the source columns a statement demands, with the source
//!   declaration the verified entry binds.
//! - `constants` refuses a statement with a literal-only constant subexpression whose SQLSpec evaluation raises an SQL
//!   error (PostgreSQL raises it while planning, whatever the data); `SqlParser` applies it to every document.
//! - `engine_encode` writes a statement document at one binding as the AST bytes of an engine call (substitution after
//!   the constant check, then a deterministic prefix encoding); trusted host item `host_ast_encoding`.
//! - `translator` renders a statement (or a template instance) as a deterministic Verus module over the SQLSpec
//!   library (`schema_spec`, `query_spec`/`query_spec_at`, parameter typing/domain, typing lemmas).
//!
//! Trust: the parser, decoder, constant check, parameter substitution and translator are the trusted translator from
//! SQL to the fixed SQL meaning; nothing here is proved. Verus later checks only properties of the emitted module (its
//! executable AST equals its spec AST; the spec AST is well-typed for the emitted schema), never that the emitted
//! meaning is a faithful translation of the SQL. The column demand decides provability and what the host binds, not
//! soundness. This crate depends on no other GenDB crate.

pub mod ast;
pub mod columns;
pub mod constants;
pub mod engine_encode;
pub mod params;
pub mod parser;
pub mod translator;
