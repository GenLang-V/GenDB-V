//! Checked examples of the engine toolkit (`engine_pins`; only the toolkit check crate carries them, engine crates
//! do not). Each proves one planner rule on a concrete AST over a small two-table schema (`schema`; `fk_join` has
//! its own constrained one), for every well-formed database of that schema, with the toolkit lemmas an engine author
//! would use:
//! - `semi_join`:      an EXISTS correlated on a key (TPC-H Q4 style) is a hash semi-join (L6, L3, L2);
//! - `grouped_lookup`: a correlated AVG on a key (Q17 style) is a lookup in one GROUP BY (L6);
//! - `equi_join`:      an equality condition over a product is a hash join probing the left input (L4 helpers);
//! - `zone_skip`:      hoisted closed bounds (`DATE ... + INTERVAL`) make a range filter skippable per zone, and an
//!                     erroring hoisted constant raises only if a row reaches it (L3, L6);
//! - `stored_group`:   GROUP BY over a storage's reordered copy of a table is bag-equal to the SQL result (L4, L3);
//! - `join_reorder`:   a three-input join tree reordered by the planner, its rows viewed through one column map and
//!                     its condition rewritten through it (L5);
//! - `pushdown`:       a condition on one input filters that input before a hash join (L5);
//! - `fk_join`:        over a second, constrained schema (a foreign key onto a primary key): join elimination and a
//!                     primary-key probe as an array lookup over dense keys (L7);
//! - `top_k`:          ORDER BY .. LIMIT answered by a top-k selection over rows in another order (O5).
pub mod schema;
pub mod semi_join;
pub mod grouped_lookup;
pub mod equi_join;
pub mod zone_skip;
pub mod stored_group;
pub mod join_reorder;
pub mod pushdown;
pub mod fk_join;
pub mod top_k;
