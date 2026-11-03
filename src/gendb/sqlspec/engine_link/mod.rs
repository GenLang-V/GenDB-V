//! Engine toolkit: generic, checked lemmas that relate a planner's physical plan for any supported query to
//! SQLSpec's exact meaning (`spec::eval::eval_query`, `exec::relational::domain::fits_query`,
//! `spec::order::ordered_ok`). Nothing here names a query, a table or a column; engine authors build planner rules
//! on these lemmas and may add their own.
//!
//! Placement and trust. Engine crates only: the framework copies this folder as `engine_link` into the crates of the
//! schema-engine target and into the toolkit check crate, and nowhere else, so it is outside every storage's
//! dependency closure. The checked examples (`sqlspec/engine_link/examples/`) are the separate
//! top-level module `engine_pins` of the toolkit check crate only. Nothing uses `assume`, `admit` or
//! `external_body`; every lemma and executable function is checked by the pinned Verus with `--no-cheating`. Every
//! definition is an author's optional vocabulary: the fixed engine claim does not mention them, so a weak
//! definition can only fail to prove it.
//!
//! Lemma groups and modules, in dependency order:
//! - `bag`:            permutation witnesses (`perm_of`), bag equality of outcomes (`bag_eq`, O1/O5), multiset laws.
//! - `ops`:            the relational operators applied to evaluated children (`filter_op`, ..), one-step unfolding
//!                     (`lemma_eval_op`), uniform error sequences, two-valued filters.
//! - `bound`:          L1, unique bound database from complete storage coverage.
//! - `locality`:       L2, outcomes depend only on the tables and context positions a node reads; uncorrelated nodes
//!                     have one value in every context of one length.
//! - `classes`:        L3 spec checker: one static analysis deciding totality, uniformity and scale-exactness.
//! - `classes_values`: L3 soundness at the level of one operator on values.
//! - `classes_sound`:  L3 soundness of the analysis, and of the three classes.
//! - `classes_exec_ops`, `classes_exec`: L3 executable checker, proved equal to the spec checker.
//! - `order_free`:     L4 (H2): order independence of deduplication and aggregate values on exact inputs.
//! - `congruence`:     L4, bag congruence of every relational operator under the H1/H2 conditions, operator and node
//!                     forms, and the bridges from L3 to its conditions.
//! - `decorrelate`:    L6, EXISTS / NOT EXISTS and IN / NOT IN to semi- and anti-joins, equality-correlated scalar
//!                     aggregates to grouped lookups, uncorrelated subqueries evaluated once.
//! - `colmap`:         L5, one column-map type (`ColMap`) for reordered and pruned rows: identity, composition,
//!                     side by side (products), the swap (join commutation as bags), conditions through a view.
//! - `remap`:          L5, column references rewritten through a column map (`remap_query`, every nesting level);
//!                     the rewritten node on physical rows has the canonical outcome and domain.
//! - `joins`:          L5, join rules over a product under total conditions: conjunct splitting, equality to hash
//!                     join, pushdown of one-input conjuncts, reordered join trees.
//! - `keys`:           L7, key probes give at most one row, foreign keys exactly one parent; join elimination and
//!                     array joins over dense keys.
//! - `topk`:           O5, a top-k selection (or a full sort) of rows bag-equal to the body is an allowed output.
//!
//! The declaration order below is the checked one; keep it.
pub mod bag;
pub mod ops;
pub mod bound;
pub mod locality;
pub mod classes;
pub mod classes_values;
pub mod classes_sound;
pub mod classes_exec_ops;
pub mod classes_exec;
pub mod order_free;
pub mod congruence;
pub mod decorrelate;
pub mod colmap;
pub mod remap;
pub mod joins;
pub mod keys;
pub mod topk;
