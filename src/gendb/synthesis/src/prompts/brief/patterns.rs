//! Short generic proof patterns (no query names): how the pieces of the proof library compose into the fixed claim,
//! and how to keep proofs within the solver's resource limit.

use serde_json::{Value, json};

pub fn patterns() -> Value {
    json!({"format_version":1,"note":"generic patterns; the items named are in your crate (proof-library/index.json); none is required",
        "patterns":[
            {"name":"state your own normal form","steps":["define spec functions over the source relations tables(v) (e.g. the qualifying rows, per-group accumulators) that your code computes",
                "prove once, for every bound db (bound_db(v, db): db_wf, schema, source_columns_are_tables), that denote_body(db, query_spec_at(ps)) equals your normal form's value (or its exact error)",
                "prove your code computes the normal form; combine the two with link::outcome lemmas to reach outcome_ok"]},
            {"name":"relate a Table/Filter/Product/Project tree to your rows","steps":["eval_query of Table t is db.tables[t]; source_columns_are_tables gives db.tables[t] projected on the delivered columns = tables(v)[j] (link::source lemma_proj_all_index)",
                "Filter: exec::relational::domain lemma_eval_filter / filter_results; per-row conditions: link::expr lemma_pred_cmp, lemma_pred_and/or/not, lemma_compare_num/int/date, lemma_expr_col",
                "Product and joins: link::join lemma_eval_product, lemma_eval_table, lemma_product_index, lemma_product_keep, lemma_sum_of_product(_swap); bag semantics, no key assumed",
                "Project: exec::relational::domain lemma_eval_project / project_results; bridge::collect lemma_collect_all, lemma_collect_first_err"]},
            {"name":"aggregate and group results","steps":["spec::relation (group_rows, agg_value) define the meaning; link::query has an optional accumulator toolkit at the top-level context (gcount/gsum/gabs, lemma_aggregate_query, lemma_group_query, lemma_filter_rows, exec_sum_out, exec_count_out, exec_avg_finalize)",
                "order independence: link::join lemma_sum_of_perm, lemma_sum_of_append (any partition and merge order gives the same sum)"]},
            {"name":"EXISTS / correlated subquery","steps":["Pred::Exists(Filter { pred, input }) evaluated in env: link::exists lemma_exists_filter (lemma_exists_filter_table for a base table): when every condition evaluation succeeds, the value is whether some input row satisfies pred in env + row",
                "a correlated Col reads an outer position (annotated-ast.txt shows the environment); a condition error propagates (link::exists doc)"]},
            {"name":"ORDER BY / LIMIT output","steps":["sort with exec::relational::order helpers or your own proved sort; link::outcome lemma_outcome_sorted / lemma_outcome_unordered / lemma_outcome_rows / lemma_slice_whole; link::query lemma_ordered_link, lemma_result_ok_from",
                "ties may appear in any order; any choice among rows tied at the LIMIT boundary is allowed"]},
            {"name":"prove Capacity","steps":["show one violated condition of fits_query on the canonical evaluation path: link::capacity lemma_filter_capacity, lemma_aggregate_capacity, lemma_group_by_capacity, lemma_agg_row_capacity, lemma_num_sum_abs, lemma_int_sum_bound, lemma_fits_each_violation",
                "or prove overflow impossible (e.g. from the declared column domains and slice lengths) and never answer Capacity"]},
            {"name":"prove an exact SqlError","steps":["show the canonical first error: link::capacity lemma_first_input, lemma_second_input, lemma_filter_err, lemma_aggregate_err, lemma_group_by_err, lemma_collect_uniform_err; bridge::collect lemma_collect_first_err; link::outcome lemma_outcome_err_exact",
                "a count beyond int8 is SQL error 22003 (link::capacity lemma_count_value)"]},
            {"name":"partition + merge with fork_join","steps":["one WorkerTask per contiguous row range (pre: the range facts; post: the range's accumulator equals your spec over that range); allocate outputs on the calling thread",
                "fork_join returns each task's output with its post; prove the ranges cover every row exactly once and merge with the order-independence lemmas"]},
            {"name":"rlimit failures","steps":["decompose: one small lemma per step (one row-evaluation step, one loop-invariant step, one merge step); a lemma about a large expression tree is proved over abstract subexpressions",
                "profile: run the failing module through toolchain.json direct_verus with --profile (from verus-tmp/, direct_profiling) and read which definitions and quantifiers are instantiated most",
                "hide what is over-expanded: #[verifier::opaque] or hide(...) on the evaluator and big spec functions, reveal only in the lemma that needs one unfolding step; write one-step unfold lemmas",
                "never raise rlimit: a raised limit hides the cause and fails again under small changes"]},
            {"name":"parallel output buffers","steps":["allocate each task's output on the calling thread, move it into the task, fill it in run (no allocation in no_unwind workers) and return it; parallel.json preallocated_outputs names the verified way to fill a given buffer",
                "fewer tasks than workers, or one, is allowed when faster: the worker count is a maximum"]},
            {"name":"parameters","steps":["params@ is the binding ps (Seq<Literal>); param_domain(params@) gives each literal's type and bounds; the Params fields p<slot> are the exec values (parameters.json params_view)",
                "your proof must hold for every ps with param_domain(ps); query_spec_at(ps) places ps[slot] where $index appears (annotated-ast.txt marks free parameters)"]},
            {"name":"source binding and domains","steps":["build receives in_domain(tables(src@)); decode must return exactly Some(tables(src@)) for what build returns",
                "gendb_source::lemma_source_in_domain(db, v) gives in_domain from db_wf for a bound db; values of numeric columns carry the declared scale"]}]})
}
