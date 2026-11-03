//! Bridge proofs: theorems about the SQL meaning (`spec`) that the executable evaluator (`exec`), the link
//! toolkit (`link`) and agent proofs rely on. Proof code only: no executable function, no trusted step (no
//! `assume`, `admit` or `external_body`); every theorem is checked with `--no-cheating`.
//!
//! Dependencies: `bridge` reads `spec` and never `exec`; `spec` never reads `bridge`, so a crate can include the
//! meaning without these proofs. Inside `bridge`, `typing` (type soundness) is the hub: `fns` and `aggs`
//! supply its per-feature cases, `collect`, `relation` and `equality::lemma_distinct_rows_sub` its row facts, and
//! `order` uses its comparison families. `equality` uses the comparison laws of `order`; `constraints` uses the
//! equality laws. `collect`, `relation` and `params` depend on `spec` alone.
//!
//! - `collect`:     canonical error-strict evaluation of sequences (`spec::relation::collect`).
//! - `relation`:    which input rows the relational operators' output rows come from (element lemmas).
//! - `typing`:      type soundness at the level the evaluator needs (comparison families, row arity).
//! - `equality`:    SQL value equality is an equivalence; structural on values of one exact type.
//! - `fns`:         type soundness (comparison family) of the leaf scalar functions (`spec::fns`), and the
//!                  facts that characterize division, LIKE matching and SUBSTRING.
//! - `aggs`:        type soundness of MIN/MAX/AVG/DISTINCT aggregates (`spec::aggs`).
//! - `order`:       value comparison is a total preorder within a family; ORDER BY: the canonical sort is an
//!                  allowed output (`lemma_denote_top_ok`).
//! - `constraints`: declared integrity constraints as proof hypotheses (keys identify rows, FK targets exist, CHECK).
//! - `params`:      typed statement parameters: ASTs that differ only in literals of the same static type have the
//!                  same typing (a template is well typed at every typed binding once it is at one).
pub mod collect;
pub mod relation;
pub mod typing;
pub mod equality;
pub mod fns;
pub mod aggs;
pub mod order;
pub mod constraints;
pub mod params;
