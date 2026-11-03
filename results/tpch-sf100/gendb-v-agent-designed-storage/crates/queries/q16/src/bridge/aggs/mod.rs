//! Type soundness of the aggregates beyond COUNT/SUM (`spec::aggs`), one module per feature. The dispatcher is
//! `bridge::typing::lemma_agg_family`, which proves COUNT/SUM itself and calls these lemmas for the other arms.
//! - `avg`:      AVG.
//! - `minmax`:   MIN / MAX (the extremum is NULL or an argument value).
//! - `distinct`: the result type of `DistinctAgg`.
pub mod avg;
pub mod minmax;
pub mod distinct;
