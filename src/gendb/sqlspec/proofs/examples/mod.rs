//! `pins`: checked examples of the SQL meaning. Each proof pins one documented fact on concrete values, schemas or
//! ASTs (most are PostgreSQL 18 results recorded by the PostgreSQL reference fixtures in `sqlspec/tests/fixtures`),
//! so a change of a `spec` definition that alters a documented fact fails the library check. Only the library crate
//! contains these examples; candidate and evaluator crates do not.
//!
//! - `q6_ast`:                    TPC-H Q6 as spec AST and as exec constructor proved equal to it (the emission
//!                                pattern of the translator).
//! - `tpch_schema`:               the TPC-H schema with its keys, as `spec::types` data.
//! - `case_subqueries_distinct`:  scalar-subquery cardinality, three-valued `ANY` (IN / NOT IN), lazy CASE, DISTINCT.
//! - `division_and_avg`:          integer and numeric division, AVG.
//! - `constraint_declarations`:   which declared integrity constraints are well formed.
//! - `sum_capacity`:              the SUM/AVG capacity condition (`exec::relational::domain::sum_mass_fits`).
pub mod q6_ast;
pub mod tpch_schema;
pub mod case_subqueries_distinct;
pub mod division_and_avg;
pub mod constraint_declarations;
pub mod sum_capacity;
