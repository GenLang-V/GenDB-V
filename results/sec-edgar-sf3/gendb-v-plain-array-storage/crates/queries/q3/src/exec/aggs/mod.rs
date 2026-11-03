//! Executable aggregate operators beyond COUNT/SUM (`spec::aggs`), one module per feature: `avg`, `minmax`
//! (MIN/MAX) and `distinct` (the typing of `DISTINCT` aggregates; their values use
//! `exec::equality::distinct_vals_exec`). COUNT/SUM and the dispatch live in `exec::relational::aggregate`
//! (`exec_agg_value`, values) and `exec::relational::check` (`type_agg_exec`, typing).
pub mod avg;
pub mod minmax;
pub mod distinct;
