//! Aggregate operators beyond COUNT/SUM, one module per feature; the dispatch arms are in `spec::relation::agg_value`
//! (values), `spec::typing::type_agg` (typing) and `exec::relational::domain::fits_agg_value` (domain).
//! - `avg`:      AVG.
//! - `minmax`:   MIN / MAX.
//! - `distinct`: typing of `DistinctAgg`; its values use `spec::equality::distinct_vals`.
pub mod avg;
pub mod minmax;
pub mod distinct;
