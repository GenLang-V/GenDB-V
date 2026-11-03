//! The engine author-source rules: the author files of an
//! engine crate may not contain the fixed text and date constants of the training template texts, nor a table of AST
//! fragments, nor reference the whole-statement evaluator. The first two guard against whole-template dispatch: a
//! planner keyed to a template's literal values, or to stored fragments of the templates' ASTs, instead of general
//! rules. All are lexical, like the rest of the refusal scan: a check of what the source text spells, not a proof, and
//! an author who computes a constant at run time is not caught (a review of the planner covers that).
//!
//! **The constants are derived, never listed by hand** ([`TemplateConstants`]): every SQL string literal of every
//! template text named by `templates.json`, except INTERVAL quantities. A literal after the keyword `DATE` is a date
//! constant; a pattern after `LIKE` also contributes each literal segment between its `%`/`_` wildcards; every other
//! literal is a text constant. Numeric constants (`0.01`, `7.0`, `10`, ...) are not template constants: they are
//! ordinary numbers of any arithmetic.
//!
//! **Where a constant is found** ([`TEMPLATE_CONSTANT_RULE`]), in code only (comments cannot change what code computes
//! and are not scanned):
//! - the content of a string, byte string, raw string, char or byte char literal: it contains a text constant of two
//!   or more characters, equals a one-character one, or contains a date as `YYYY-MM-DD`;
//! - a run of integer literals, each at most 255, with at most [`RUN_GAP`] other tokens and no other literal between
//!   neighbours (`seq![49u8, 45u8, ...]`, `vec![..]`, repeated `v.push(49u8);`): it contains a text constant's UTF-8
//!   bytes contiguously; a one-byte constant only as a run of one literal written with the `u8` suffix
//!   (`seq![82u8]`, `push(70u8)`);
//! - a date as three integer literals `Y, M, D` separated only by commas, colons and field names (a
//!   `Literal::Date { y, m, d }`, `date_from_civil(y, m, d)`), as the integer `YYYYMMDD`, or as its day number from
//!   2000-01-01 (SQLSpec's date value) or from 1970-01-01 (the capture's date columns), with its sign.
//!
//! **AST fragments** ([`AST_FRAGMENT_RULE`]): an executable AST node with a fixed table or column index,
//! `EQuery::Table(<integer literal>)` or `EExpr::Col(<integer literal>)`. A planner reads table and column indices from
//! the query it is given; a stored fragment of a template's AST must name them. Fragments built without literal
//! indices are not caught lexically.
//!
//! **The whole-statement evaluator** ([`WHOLE_STATEMENT_EVALUATOR_RULE`]): the engine is the author's own planner,
//! operators and general expression path, not the verified reference interpreter.
//! Refused: the evaluator modules `exec::relational::{eval, entry}` by path (the query freezes' check,
//! `super::scan_whole_statement_evaluator`), a glob import of `exec::relational` itself, aliases of `relational`, and,
//! by name whatever path, alias or glob it arrives through, every public executable function of the framework library
//! whose calls can reach the evaluator ([`EVALUATOR_ROUTES`], from the SQLSpec interpreter's call graph). Allowed: every
//! other executable helper ([`ALLOWED_EXEC_HELPERS`]: the scalar primitives, the per-operator helpers that cannot reach
//! it, and the toolkit's class checkers, which evaluate only closed constant expressions over an empty database).
//!
//! **Rule sets by engine line** ([`EngineLine`], [`EngineRuleSet`]). A request
//! without `engine.line` runs the schema-engine line and applies [`ENGINE_RULES`] exactly as above.
//! A request with `engine.line: "general"` applies [`GENERAL_ENGINE_RULES`]: the template constants
//! and AST fragments as above, no whole-statement evaluator rule (version 0 is the verified interpreter, and a fallback
//! to it inside the proof is allowed), and the schema-name rule ([`SCHEMA_NAME_RULE`]): a column name of the run's
//! schema as an identifier, as a run of `_`-separated identifier segments or as such a word inside a literal, and a
//! table name inside a literal or as a segment of the storage after `stores::` / `stores.` are refused; every other
//! table-name segment is only reported ([`EngineRuleSet::schema_name_reports`]), because short table names collide with
//! framework words (TPC-H `part` against `Part`, `parts`, `part_len`). The general line scans `agent/**` with the whole
//! set ([`EngineRuleSet::scan_agent_source`]) and the own interface and builder files of every storage the engine reads
//! that is not a generated flat storage with the schema-name rule ([`EngineRuleSet::scan_storage_source`]).
//!
//! **Stage runs** ([`EngineRuleSet::for_stage`]): one engine source serves several
//! workloads, one crate per workload, and every crate is scanned with one rule set, [`STAGE_ENGINE_RULES`]:
//! - the template constants are those of every workload's templates (named `<workload>/<template>`), and the schema-name
//!   rule uses the union of every workload's table and column names ([`STAGE_SCHEMA_NAME_RULE`]);
//! - a column name of one `_`-separated segment (`value`, `tag`, `fy`, `adsh`) is refused only as a whole word inside a
//!   string, byte string or char literal; as an identifier or a segment of one it is reported
//!   ([`SCHEMA_COLUMN_MENTION`]), not refused. One-word names are ordinary words and short abbreviations that collide
//!   with code vocabulary (`tcol_value`, `has_tag`); the stronger generality evidence of a stage run is that one source
//!   verifies and runs over every workload's schema. Every TPC-H column name has two segments, so TPC-H's findings are
//!   unchanged; table names are as on the general line;
//! - [`WORKLOAD_MODULE_RULE`]: the files under `agent/workload/` (one workload's module, composed into its crate by the
//!   freeze) name no statement type or AST path. A workload module opens its workload's storages as the engine's tables
//!   and proves what that needs; query processing stays in the shared engine. What such a module holds is reported, not
//!   refused ([`workload_module_report`]: lines, item kinds, loops, the storages it names): storage technique (layouts,
//!   encodings, indexes) belongs in the storages and the shared engine, parameterized by the schema, and a lexical rule
//!   that tells technique from opening code would be fragile, so the record shows the module's size and shape to review.
//!
//! **Runs of several workloads** ([`EngineRuleSet::for_members`]; `engine.workloads`): the
//! stage rules over every member's names and constants (R1, R2), and three more ([`FAMILY_RULES`]), all structural or
//! lexical:
//! - [`STORAGE_FAMILY_RULE`] (R3): every storage a submission adds is a storage family's instance; a workspace storage
//!   is refused (admitted packages stay allowed);
//! - [`PLAN_IS_DATA_RULE`] (R4): a family's `default_plan.rs` and a workload's plan are data ([`scan_plan_source`]);
//! - [`WORKLOAD_MODULE_SCOPE_RULE`] (R5): a workload that reads only family instances and plain flat storages has no
//!   module of its own (it uses the shared default module).
//!
//! R3 and R5 are applied by the engine freeze (`gendb_synthesis::engine::submission`), R4 there and again at the
//! engine's admission on every family instance's `builder/plan.rs`; the rule set records them.
//!
//! [`scan_engine_source`] is the scan of one author file under the schema-engine line; the engine's admission applies
//! the run's rule set to every `agent/` file of the crate, next to [`super::scan_source`] and [`super::scan_static_items`].

use super::super::lexer::{group_end, lex, Tok, Token};
use super::{refuse_evaluator_paths, rule, Findings, RefusalFinding, RefusalRule};
use crate::verus::FrameworkSource;
use gendb_frontend::ast::TableDef;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::fmt;
use std::path::Path;

pub const TEMPLATE_CONSTANT_RULE: RefusalRule = RefusalRule {
    id: "template_constant",
    refuses: "in an engine author file's code (not comments): a text or date constant of a training template text (derived from templates.json: every string literal except INTERVAL quantities; DATE literals as dates; LIKE patterns and their literal segments) as string or char literal content, as a run of byte-valued integer literals, or a date as `Y, M, D` integers, as `YYYYMMDD` or as its day number from 2000-01-01 or 1970-01-01",
    reason: "generality: the engine must answer every well-typed query by general rules; a rule keyed to a template's literal values is template dispatch, which the metamorphic variants do not catch once the AST is normalized",
};

pub const AST_FRAGMENT_RULE: RefusalRule = RefusalRule {
    id: "ast_fragment_table",
    refuses: "in an engine author file: an executable AST node with a fixed table or column index, `EQuery::Table(<integer literal>)` or `EExpr::Col(<integer literal>)`",
    reason: "generality: a table of AST fragments to match queries against must name tables and columns; a planner takes them from the query it is given",
};

pub const WHOLE_STATEMENT_EVALUATOR_RULE: RefusalRule = RefusalRule {
    id: rule::WHOLE_STATEMENT_EVALUATOR,
    refuses: "in an engine agent/ file's code (not comments or literals): a path to the evaluator modules `relational::eval` or `relational::entry`, or a `relational::{..}` group with an item starting with either; a glob import of exec::relational itself (`relational::*`, or `*` in a `relational::{..}` group; globs of its other submodules stay allowed); an alias of the module (`relational as`); and, as an identifier anywhere (call, path segment, `use .. as` source, method or field name), each public executable function whose calls can reach the evaluator: exec_query, exec_pred, exec_ordered, evaluate, exec_expr, exec_expr_node, exec_expr_if, exec_exprs, exec_filter, exec_project, exec_left_join, exec_left_join_row, exec_agg_arg, exec_agg_args, exec_aggregate, exec_group_by, check_constraints_exec. Every other executable helper stays allowed",
    reason: "the engine is the author's own planner, operators and general expression path, not the verified reference interpreter: its whole-statement functions, and every function that can call them with a query, a condition or an expression of the author's choosing, are refused whatever path, alias or glob they arrive through. Lexical: an author function with one of these names must be renamed",
};

/// One public executable function of the framework library whose calls can reach the whole-statement evaluator.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct EvaluatorRoute {
    pub function: &'static str,
    pub module: &'static str,
    /// How its calls reach `exec_query`, `exec_pred`, `exec_ordered` or `evaluate`.
    pub reaches: &'static str,
}

/// Every public executable function of an engine crate's framework library whose call graph reaches the whole-statement
/// evaluator, from the SQLSpec interpreter sources (`sqlspec/interpreter/**`, assembled as `exec/**`;
/// found by a call-graph script, each edge checked by hand). The other functions that reach it are private
/// to `exec::relational::{eval, constraints}` and cannot be called from agent code (`exec_pred_scalar`,
/// `exec_pred_logic`, `exec_pred_sub`, the seven `exec_query_*` steps, `constraint_holds_exec`, `check_holds_exec`).
/// `link/**`, `bridge/**` and `spec/**` hold none.
pub const EVALUATOR_ROUTES: &[EvaluatorRoute] = &[
    EvaluatorRoute { function: "exec_query", module: "exec::relational::eval", reaches: "the whole-statement evaluator: any query" },
    EvaluatorRoute { function: "exec_pred", module: "exec::relational::eval", reaches: "any condition; EXISTS, IN and ANY subqueries through exec_query, scalar operands through exec_expr" },
    EvaluatorRoute { function: "exec_ordered", module: "exec::relational::entry", reaches: "a whole statement: exec_query, then sort and slice" },
    EvaluatorRoute { function: "evaluate", module: "exec::relational::entry", reaches: "the checked entry: check_constraints_exec, then exec_ordered" },
    EvaluatorRoute { function: "exec_expr", module: "exec::expr", reaches: "any expression; a call, CASE or scalar subquery through exec_expr_node" },
    EvaluatorRoute { function: "exec_expr_node", module: "exec::expr", reaches: "a scalar subquery through exec_query, CASE through exec_expr_if, call arguments through exec_exprs" },
    EvaluatorRoute { function: "exec_expr_if", module: "exec::expr", reaches: "CASE conditions through exec_pred, branches through exec_expr" },
    EvaluatorRoute { function: "exec_exprs", module: "exec::expr", reaches: "exec_expr on each expression of a list" },
    EvaluatorRoute { function: "exec_filter", module: "exec::relational::ops", reaches: "a WHERE condition on each row through exec_pred" },
    EvaluatorRoute { function: "exec_project", module: "exec::relational::ops", reaches: "a SELECT list on each row through exec_exprs" },
    EvaluatorRoute { function: "exec_left_join_row", module: "exec::relational::ops", reaches: "a LEFT JOIN ON condition on each pair through exec_pred" },
    EvaluatorRoute { function: "exec_left_join", module: "exec::relational::ops", reaches: "exec_left_join_row on each left row" },
    EvaluatorRoute { function: "exec_agg_arg", module: "exec::relational::group", reaches: "an aggregate's argument expression through exec_expr" },
    EvaluatorRoute { function: "exec_agg_args", module: "exec::relational::group", reaches: "exec_agg_arg on each aggregate" },
    EvaluatorRoute { function: "exec_aggregate", module: "exec::relational::group", reaches: "aggregation over rows: exec_agg_args on each row" },
    EvaluatorRoute { function: "exec_group_by", module: "exec::relational::group", reaches: "group keys through exec_exprs, aggregate arguments through exec_agg_args" },
    EvaluatorRoute { function: "check_constraints_exec", module: "exec::relational::constraints", reaches: "a CHECK constraint's condition on each row through exec_pred" },
];

/// Executable helpers that stay allowed, by module (the complement of [`EVALUATOR_ROUTES`] and the evaluator modules).
#[derive(Clone, Copy, Debug, Serialize)]
pub struct AllowedHelpers {
    pub module: &'static str,
    /// Its public executable functions (empty: every function of the modules named).
    pub functions: &'static [&'static str],
    pub why: &'static str,
}

/// The executable helpers an engine may call ([`WHOLE_STATEMENT_EVALUATOR_RULE`]); every function listed or covered here
/// was checked not to reach the evaluator.
pub const ALLOWED_EXEC_HELPERS: &[AllowedHelpers] = &[
    AllowedHelpers { module: "exec::{value, numeric, datetime, text, chars, scalar, equality, fns, aggs}", functions: &[], why: "scalar primitives over values: arithmetic, numeric division, casts, dates and intervals, text, LIKE, substring, padding, extract, equality and comparison, aggregate accumulators" },
    AllowedHelpers { module: "exec::expr", functions: &["lit_exec", "subquery_value_exec"], why: "a literal's value; a scalar subquery's value from rows already computed" },
    AllowedHelpers { module: "exec::relational::ops", functions: &["exec_table", "product_rows_exec", "query_arity_exec"], why: "a table's rows, the product of two row lists, a query's static arity" },
    AllowedHelpers { module: "exec::relational::aggregate", functions: &["count_non_null_exec", "all_of_kind_exec", "int_sum_exec", "num_sum_exec", "exec_agg_value", "exec_agg_row"], why: "aggregate values over argument values already computed" },
    AllowedHelpers { module: "exec::relational::order", functions: &["keys_cmp_exec", "sort_rows_exec", "slice_rows_exec"], why: "ORDER BY key comparison, stable sort, OFFSET/LIMIT" },
    AllowedHelpers { module: "exec::relational::rows", functions: &["clone_row", "concat_rows", "null_row_exec", "clone_rows", "append_rows"], why: "row copies and concatenations" },
    AllowedHelpers { module: "exec::relational::check", functions: &["check_schema", "check_db", "check_row", "value_in_column_exec", "check_ordered", "type_query_exec", "type_pred_exec", "type_expr_exec", "type_exprs_exec", "table_tys_exec"], why: "well-formedness and typing checks; nothing is evaluated" },
    AllowedHelpers { module: "exec::relational::constraints", functions: &["check_constraints_wf_exec"], why: "the declared constraints' form; no data is read" },
    AllowedHelpers { module: "exec::relational::{schema, domain}", functions: &[], why: "the runtime database type and the executable domain (specifications)" },
    AllowedHelpers { module: "engine_link::{classes_exec, classes_exec_ops}", functions: &[], why: "the toolkit's class checkers: they call exec_expr only through closed_value_exec, on closed constant expressions (literals, negation, arithmetic, casts, interval addition) over an empty database built there, so no query, condition, CASE, call or subquery is evaluated" },
];

/// The engine rules of the schema-engine line (a request without `engine.line`), for the author contract and the
/// admission record.
pub const ENGINE_RULES: &[RefusalRule] = &[TEMPLATE_CONSTANT_RULE, AST_FRAGMENT_RULE, WHOLE_STATEMENT_EVALUATOR_RULE];

pub const SCHEMA_NAME_RULE: RefusalRule = RefusalRule {
    id: "schema_name",
    refuses: "general engine line, in code (not comments) of an engine agent/ file and of the own interface and builder files of every storage the engine reads that is not a generated flat storage: a column name of the run's schema as an identifier, as a run of `_`-separated segments of an identifier (case-insensitive: `l_shipdate`, `read_l_shipdate_range`, `L_SHIPDATE`), or as such a word inside a string, byte string or char literal; a table name of the run's schema as a word or `_`-separated segment inside such a literal, or as a segment of the identifier after `stores::` or `stores.` (`stores::flat_lineitem`, `stores.flat_lineitem`). Other table-name segments are reported, not refused",
    reason: "generality: main-line engine code works for any schema, so it names no table or column of this one; schema knowledge enters only as data (`schema_exec()`, the generated `crate::flat_tables` access by table and column id, storage declarations). Table names outside literals and storage paths are only reported because short table names collide with framework words (TPC-H `part` against `Part`, `parts`, `part_len`). Lexical, like every refusal rule: names computed at run time are not caught",
};

/// The engine rules of the general line (`engine.line: "general"`): no whole-statement evaluator rule, plus the
/// schema-name rule.
pub const GENERAL_ENGINE_RULES: &[RefusalRule] = &[TEMPLATE_CONSTANT_RULE, AST_FRAGMENT_RULE, SCHEMA_NAME_RULE];

/// The id of a reported (not refused) table-name mention of the general line ([`EngineRuleSet::schema_name_reports`]).
pub const SCHEMA_TABLE_MENTION: &str = "schema_table_name_mention";

/// The schema-name rule of a stage run ([`EngineRuleSet::for_stage`]): the general line's, over the union of every
/// workload's names, with one-word column names refused in literals only. Same id as [`SCHEMA_NAME_RULE`]: it is that
/// rule, in its stage form.
pub const STAGE_SCHEMA_NAME_RULE: RefusalRule = RefusalRule {
    id: "schema_name",
    refuses: "stage run, in code (not comments) of an engine agent/ file and of the own interface and builder files of every storage the engine reads that is not a generated flat storage, with the table and column names of every workload of the run: a column name of two or more `_`-separated segments as an identifier, as a run of segments of an identifier (case-insensitive: `l_shipdate`, `read_l_shipdate_range`, `L_SHIPDATE`) or as such a word inside a string, byte string or char literal; a column name of one segment (`value`, `tag`, `fy`) as a whole word inside such a literal; a table name as a word or `_`-separated segment inside such a literal, or as a segment of the identifier after `stores::` or `stores.`. One-word column names in identifiers and other table-name segments are reported, not refused",
    reason: "generality: one engine source serves every workload, so it names no table or column of any of them; schema knowledge enters only as data (`schema_exec()`, `crate::flat_tables`, storage declarations) and through each workload's module. One-word column names are ordinary words and short abbreviations that collide with code vocabulary (`tcol_value`, `has_tag`), so in identifiers they are only reported; the decisive evidence is that the same source verifies and runs over every workload's schema. Lexical, like every refusal rule",
};

/// The workload-module rule of a stage run: what a workload's module (`agent/workload/**`) may not name.
pub const WORKLOAD_MODULE_RULE: RefusalRule = RefusalRule {
    id: "workload_module_statement",
    refuses: "stage run, in code (not comments) of an engine file under agent/workload/ (one workload's module): a statement type of SQLSpec as an identifier (`EOrderedQuery`, `EQuery`, `EPred`, `EExpr`, `EAgg`, `EOrderKey`, `ELiteral`, `OrderedQuery`, `Query`, `Pred`, `Expr`, `Agg`, `OrderKey`), a path to the AST modules (`exec::ast`, `spec::ast`) or the AST codec (`gendb_ast_codec`)",
    reason: "one engine for every workload: a workload's module opens that workload's storages as the engine's tables and proves what that needs; statements are planned and answered by the shared engine, which every workload's crate verifies and runs, so no workload gets query processing of its own. Its size and item kinds are reported with every freeze and admission. Lexical, like every refusal rule",
};

/// The engine rules of a stage run's crates ([`EngineRuleSet::for_stage`]).
pub const STAGE_ENGINE_RULES: &[RefusalRule] = &[TEMPLATE_CONSTANT_RULE, AST_FRAGMENT_RULE, STAGE_SCHEMA_NAME_RULE, WORKLOAD_MODULE_RULE];

/// R3 of a run of several workloads.
pub const STORAGE_FAMILY_RULE: RefusalRule = RefusalRule {
    id: "storage_family_required",
    refuses: "run of several workloads (engine.workloads), in the engine manifest: a storage use naming a workspace storage (`workspace`). Every storage a submission adds is the instance of a storage family (`{\"name\": <family>, \"family\": <family>}`), composed by GenDB over each workload's whole schema; uses of admitted packages (inherited storages, admitted family instances, the plain flat storages) stay allowed",
    reason: "one engine for every schema: new storage code is written once, as a family whose builder and interface are generic over the schema, and GenDB composes it into every workload; a storage of one workload's own would be workload-specific code. Structural (where a storage comes from), not a judgment of its technique",
};

/// R4 of a run of several workloads ([`scan_plan_source`]).
pub const PLAN_IS_DATA_RULE: RefusalRule = RefusalRule {
    id: "plan_is_data",
    refuses: "run of several workloads, in a storage family's default_plan.rs and in a workload's plans/<workload>/<family>.rs (each instance's builder/plan.rs): anything but `use` lines, comments, `verus!` and one `pub fn plan() -> <type>` without parameters, attributes or specification clauses whose body is data: struct literals, paths, constructors written with an uppercase name (`Some(..)`, `Kind::Sorted(..)`), `vec![..]`, integer and float literals, `true`, `false` and a minus sign before a number. Refused there: a call of a lowercase function or a method, any other macro, an operator, field access, range or struct update, a text or char literal, `if`, `match`, a loop, `let`, a closure, a proof block or assertion",
    reason: "plans are data: a workload's tuning (which table is sorted by which column, which columns get zone maps) as table and column ids, flags and numbers, which the family's shared builder checks at run time; code in a plan would be workload-specific code outside the shared builder. Lexical, like every refusal rule",
};

/// R5 of a run of several workloads.
pub const WORKLOAD_MODULE_SCOPE_RULE: RefusalRule = RefusalRule {
    id: "workload_module_scope",
    refuses: "run of several workloads, at each workload's freeze: a module of the workload's own (`workloads/<workload>/`) while it reads only storage family instances and plain flat storages; such a workload uses the shared default module `workloads/default/`. An own module is allowed only beside an inherited storage that is neither (a seed's workload-specific storage, opened by that module)",
    reason: "one engine for every schema: the shared default module opens family and plain storages by table id for any schema, so a module of a workload's own is needed only to open an inherited workload-specific storage until a family replaces it. Structural (which module a workload uses and which storages it reads)",
};

/// The rules a run of several workloads adds to the stage rules: R3, R4 and R5.
pub const FAMILY_RULES: &[RefusalRule] = &[STORAGE_FAMILY_RULE, PLAN_IS_DATA_RULE, WORKLOAD_MODULE_SCOPE_RULE];

/// The engine rules of the crates of a run of several workloads ([`EngineRuleSet::for_members`]): the stage rules, then
/// [`FAMILY_RULES`].
pub const MEMBER_ENGINE_RULES: &[RefusalRule] =
    &[TEMPLATE_CONSTANT_RULE, AST_FRAGMENT_RULE, STAGE_SCHEMA_NAME_RULE, WORKLOAD_MODULE_RULE, STORAGE_FAMILY_RULE, PLAN_IS_DATA_RULE, WORKLOAD_MODULE_SCOPE_RULE];

/// The directory of the shared default workload module in a run of several workloads (`<crate_dir>/workloads/default/`;
/// composed as `agent/workload/` like any workload's module).
pub const DEFAULT_MODULE_DIRECTORY: &str = "workloads/default/";
/// Where a workload's plan of a family lies in a run of several workloads (`<crate_dir>/plans/<workload>/<family>.rs`).
pub const PLAN_FILE_PATTERN: &str = "plans/<workload>/<family>.rs";

/// The id of a reported (not refused) one-word column name in an identifier of a stage run
/// ([`EngineRuleSet::schema_name_reports`]).
pub const SCHEMA_COLUMN_MENTION: &str = "schema_one_word_column_mention";

/// The directory of a workload's module in a stage run's engine crate (`crate::agent::workload`).
pub const WORKLOAD_MODULE_ROOT: &str = "agent/workload/";

/// The statement types a workload module may not name ([`WORKLOAD_MODULE_RULE`]): SQLSpec's executable AST
/// (`exec::ast`) and its specification AST (`spec::ast`).
const STATEMENT_TYPES: [&str; 13] =
    ["EOrderedQuery", "EQuery", "EPred", "EExpr", "EAgg", "EOrderKey", "ELiteral", "OrderedQuery", "Query", "Pred", "Expr", "Agg", "OrderKey"];

/// The engine line a run follows: the request's `engine.line`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EngineLine {
    /// No `engine.line` in the request: the schema-engine rules ([`ENGINE_RULES`]).
    SchemaEngine,
    /// `engine.line: "general"`: [`GENERAL_ENGINE_RULES`].
    General,
}

impl EngineLine {
    /// The line of a request's `engine.line` value: none is the schema-engine line, `"general"` the general line;
    /// any other value is refused (`Err` names it).
    pub fn of_request(line: Option<&str>) -> Result<Self, String> {
        match line {
            None => Ok(Self::SchemaEngine),
            Some("general") => Ok(Self::General),
            Some(other) => Err(format!("engine.line {other:?} is not a known engine line (absent for the schema-engine line, or \"general\")")),
        }
    }

    /// The request value of the line (`None` for the schema-engine line, whose requests have no `engine.line`).
    pub fn request_value(self) -> Option<&'static str> {
        match self {
            Self::SchemaEngine => None,
            Self::General => Some("general"),
        }
    }

    /// The line's name in records.
    pub fn id(self) -> &'static str {
        match self {
            Self::SchemaEngine => "schema_engine",
            Self::General => "general",
        }
    }

    /// The engine rules this line applies to `agent/**` files.
    pub fn rules(self) -> &'static [RefusalRule] {
        match self {
            Self::SchemaEngine => ENGINE_RULES,
            Self::General => GENERAL_ENGINE_RULES,
        }
    }
}

/// The table and column names of a run's schema, lowercase, each as its `_`-separated segments: the input of
/// [`SCHEMA_NAME_RULE`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SchemaNames {
    tables: Vec<(String, Vec<String>)>,
    columns: Vec<(String, Vec<String>)>,
}

impl SchemaNames {
    /// The names of the tables and columns of `schema` (a translated document's tables).
    pub fn of(schema: &[TableDef]) -> Self {
        Self::from_names(schema.iter().map(|t| t.name.as_str()), schema.iter().flat_map(|t| t.columns.iter().map(|c| c.name.as_str())))
    }

    /// The names given (duplicates and names of underscores only dropped).
    pub fn from_names<'a>(tables: impl IntoIterator<Item = &'a str>, columns: impl IntoIterator<Item = &'a str>) -> Self {
        Self { tables: segmented(tables), columns: segmented(columns) }
    }

    /// The names of the tables and columns of every schema of `schemas` together (a stage run's workloads).
    pub fn of_schemas(schemas: &[&[TableDef]]) -> Self {
        Self::from_names(
            schemas.iter().flat_map(|s| s.iter().map(|t| t.name.as_str())),
            schemas.iter().flat_map(|s| s.iter().flat_map(|t| t.columns.iter().map(|c| c.name.as_str()))),
        )
    }

    /// The number of column names of one segment.
    pub fn one_word_column_count(&self) -> usize {
        self.columns.iter().filter(|(_, s)| s.len() == 1).count()
    }

    /// The first column name of two or more segments whose segments occur contiguously in `word`'s segments.
    fn multi_word_column_in(&self, word: &[String]) -> Option<&str> {
        self.columns.iter().find(|(_, s)| s.len() > 1 && contains_run(word, s)).map(|(name, _)| name.as_str())
    }

    /// The first column name of one segment that is one of `word`'s segments.
    fn one_word_column_in(&self, word: &[String]) -> Option<&str> {
        self.columns.iter().find(|(_, s)| s.len() == 1 && word.contains(&s[0])).map(|(name, _)| name.as_str())
    }

    /// The column name of one segment that `word` is, as a whole word (case-insensitive).
    fn one_word_column_equal(&self, word: &str) -> Option<&str> {
        let word = word.to_lowercase();
        self.columns.iter().find(|(name, s)| s.len() == 1 && *name == word).map(|(name, _)| name.as_str())
    }

    pub fn table_count(&self) -> usize {
        self.tables.len()
    }

    pub fn column_count(&self) -> usize {
        self.columns.len()
    }

    /// The first column name whose segments occur contiguously in `word`'s segments.
    fn column_in(&self, word: &[String]) -> Option<&str> {
        self.columns.iter().find(|(_, s)| contains_run(word, s)).map(|(name, _)| name.as_str())
    }

    /// The first table name whose segments occur contiguously in `word`'s segments.
    fn table_in(&self, word: &[String]) -> Option<&str> {
        self.tables.iter().find(|(_, s)| contains_run(word, s)).map(|(name, _)| name.as_str())
    }
}

/// Each name lowercase with its segments, sorted, without duplicates or names of underscores only.
fn segmented<'a>(names: impl IntoIterator<Item = &'a str>) -> Vec<(String, Vec<String>)> {
    let mut out: Vec<(String, Vec<String>)> = names.into_iter().map(|n| (n.to_lowercase(), segments(n))).filter(|(_, s)| !s.is_empty()).collect();
    out.sort();
    out.dedup();
    out
}

/// The lowercase `_`-separated segments of a name, empty segments dropped (`__l_SHIPDATE_` is `["l", "shipdate"]`).
fn segments(name: &str) -> Vec<String> {
    name.split('_').filter(|s| !s.is_empty()).map(str::to_lowercase).collect()
}

/// Whether `run` occurs contiguously in `word`.
fn contains_run(word: &[String], run: &[String]) -> bool {
    !run.is_empty() && word.windows(run.len()).any(|w| w == run)
}

/// The engine source rules of one run: its line, the template constants, (general line) the schema's names, and for a
/// stage run its workloads. The one selector of engine source scans; recorded with every frozen engine, admission and
/// TCB.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EngineRuleSet {
    line: EngineLine,
    constants: TemplateConstants,
    names: SchemaNames,
    /// A stage run's workloads, goal first ([`EngineRuleSet::for_stage`]); `None` outside stage runs.
    stage: Option<Vec<String>>,
    /// A run of several workloads ([`EngineRuleSet::for_members`]): the stage form plus [`FAMILY_RULES`].
    members: bool,
}

/// One workload of a stage run as its rules see it: its name, its schema and its templates' constants.
#[derive(Clone, Copy, Debug)]
pub struct StageWorkload<'a> {
    pub name: &'a str,
    pub schema: &'a [TableDef],
    pub constants: &'a TemplateConstants,
}

impl EngineRuleSet {
    /// The rule set of `line` over the template `constants` and the run's `schema` (its names matter only to the
    /// general line).
    pub fn for_line(line: EngineLine, constants: TemplateConstants, schema: &[TableDef]) -> Self {
        let names = if line == EngineLine::General { SchemaNames::of(schema) } else { SchemaNames::default() };
        Self { line, constants, names, stage: None, members: false }
    }

    /// The general line's rule set with the names given (tests and tools without a translated schema).
    pub fn general_with_names(constants: TemplateConstants, names: SchemaNames) -> Self {
        Self { line: EngineLine::General, constants, names, stage: None, members: false }
    }

    /// The rule set of every crate of a stage run over `workloads` (goal first; module documentation, "Stage runs"):
    /// the general line's rules in their stage form ([`STAGE_ENGINE_RULES`]) over the constants of every workload's
    /// templates (each named `<workload>/<template>`) and the names of every workload's schema.
    pub fn for_stage(workloads: &[StageWorkload<'_>]) -> Self {
        let schemas: Vec<&[TableDef]> = workloads.iter().map(|w| w.schema).collect();
        let constants = TemplateConstants::united(&workloads.iter().map(|w| (w.name, w.constants)).collect::<Vec<_>>());
        Self {
            line: EngineLine::General,
            constants,
            names: SchemaNames::of_schemas(&schemas),
            stage: Some(workloads.iter().map(|w| w.name.to_string()).collect()),
            members: false,
        }
    }

    /// The stage form with the names given (tests and tools without a translated schema).
    pub fn stage_with_names(workloads: &[&str], constants: TemplateConstants, names: SchemaNames) -> Self {
        Self { line: EngineLine::General, constants, names, stage: Some(workloads.iter().map(|w| w.to_string()).collect()), members: false }
    }

    /// The rule set of every crate of a run of several workloads over `workloads` (`engine.workloads`, the primary first;
    /// module documentation, "Runs of several workloads"): the stage form over every workload's names and template
    /// constants (R1, R2), plus [`FAMILY_RULES`] (R3-R5), recorded with it ([`MEMBER_ENGINE_RULES`]).
    pub fn for_members(workloads: &[StageWorkload<'_>]) -> Self {
        Self { members: true, ..Self::for_stage(workloads) }
    }

    /// The form of [`EngineRuleSet::for_members`] with the names given (tests and tools without a translated schema).
    pub fn members_with_names(workloads: &[&str], constants: TemplateConstants, names: SchemaNames) -> Self {
        Self { members: true, ..Self::stage_with_names(workloads, constants, names) }
    }

    pub fn line(&self) -> EngineLine {
        self.line
    }

    pub fn constants(&self) -> &TemplateConstants {
        &self.constants
    }

    /// The workloads of a stage run's rule set, goal first (`None` outside stage runs).
    pub fn stage_workloads(&self) -> Option<&[String]> {
        self.stage.as_deref()
    }

    /// Whether this is a stage run's rule set (a run of several workloads' too: its crates are frozen and admitted as a
    /// stage run's).
    pub fn is_stage(&self) -> bool {
        self.stage.is_some()
    }

    /// Whether this is the rule set of a run of several workloads ([`EngineRuleSet::for_members`]).
    pub fn is_members(&self) -> bool {
        self.members
    }

    /// The engine rules of the run, recorded with every frozen engine, admission and TCB: those the scans of `agent/**`
    /// apply and, for a run of several workloads, [`FAMILY_RULES`] (applied by the freeze and the admission).
    pub fn rules(&self) -> &'static [RefusalRule] {
        match (self.members, self.is_stage()) {
            (true, _) => MEMBER_ENGINE_RULES,
            (false, true) => STAGE_ENGINE_RULES,
            (false, false) => self.line.rules(),
        }
    }

    /// The rules one scan of an `agent/` file applies.
    fn agent_scan(&self, file: &str) -> Applied<'_> {
        match (self.line, self.is_stage()) {
            (EngineLine::SchemaEngine, _) => Applied::SCHEMA_ENGINE,
            (EngineLine::General, false) => Applied::general(&self.names),
            (EngineLine::General, true) => Applied { workload_module: file.starts_with(WORKLOAD_MODULE_ROOT), ..Applied::stage(&self.names) },
        }
    }

    /// The gating findings of the line's engine rules in one `agent/` file, sorted by line, without duplicates.
    pub fn scan_agent_source(&self, file: &str, text: &str) -> Vec<RefusalFinding> {
        scan_rules(file, text, &self.constants, self.agent_scan(file))
    }

    /// The gating findings in one own interface or builder file of a storage the engine reads that is not a generated
    /// flat storage: [`SCHEMA_NAME_RULE`] on the general line ([`STAGE_SCHEMA_NAME_RULE`] in a stage run), nothing on
    /// the schema-engine line.
    pub fn scan_storage_source(&self, file: &str, text: &str) -> Vec<RefusalFinding> {
        match self.line {
            EngineLine::SchemaEngine => vec![],
            EngineLine::General => {
                let applied = if self.is_stage() { Applied::stage(&self.names) } else { Applied::general(&self.names) };
                scan_rules(file, text, &self.constants, Applied { constants_and_fragments: false, workload_module: false, ..applied })
            }
        }
    }

    /// The schema-name mentions of one file that the schema-name rule reports but does not refuse: a table name as a
    /// segment of an identifier outside a `stores::` / `stores.` path ([`SCHEMA_TABLE_MENTION`]) and, in a stage run, a
    /// one-word column name as a segment of an identifier ([`SCHEMA_COLUMN_MENTION`]). Empty on the schema-engine line.
    pub fn schema_name_reports(&self, file: &str, text: &str) -> Vec<RefusalFinding> {
        let mut findings = Findings { file, list: Vec::new() };
        for m in self.name_mentions(text) {
            let what = if m.rule == SCHEMA_TABLE_MENTION { "table name" } else { "one-word column name" };
            findings.refuse(m.line, m.rule, format!("{what} `{}` in identifier `{}` (reported, not refused)", m.name, m.identifier));
        }
        findings.list
    }

    /// The reported mentions of `files` (each `(path, text)`) summarized for a record: their total, and per rule and
    /// name its count and its first [`REPORTED_SITES`] sites (`file:line identifier`), the most frequent first. A stage
    /// run reports many (one-word column names and short table names are ordinary words), so records keep this summary.
    pub fn schema_name_report_summary<'f>(&self, files: impl IntoIterator<Item = (&'f str, &'f str)>) -> Value {
        let mut by_name: BTreeMap<(&'static str, String), (usize, Vec<String>)> = BTreeMap::new();
        let mut total = 0usize;
        for (path, text) in files {
            for m in self.name_mentions(text) {
                total += 1;
                let entry = by_name.entry((m.rule, m.name)).or_default();
                entry.0 += 1;
                if entry.1.len() < REPORTED_SITES {
                    entry.1.push(format!("{path}:{} `{}`", m.line, m.identifier));
                }
            }
        }
        let mut names: Vec<_> = by_name.into_iter().collect();
        names.sort_by(|a, b| b.1 .0.cmp(&a.1 .0).then_with(|| a.0.cmp(&b.0)));
        let names: Vec<Value> = names.into_iter().map(|((rule, name), (count, sites))| json!({"rule":rule,"name":name,"count":count,"first_sites":sites})).collect();
        json!({"total":total,"by_name":names,"meaning":"schema names in identifiers that the schema-name rule reports and does not refuse (table names; in a stage run also one-word column names)"})
    }

    /// The reported mentions of one file's identifiers ([`EngineRuleSet::schema_name_reports`]); a file that cannot be
    /// lexed has none (the gating scan refuses it).
    fn name_mentions(&self, text: &str) -> Vec<NameMention> {
        let mut mentions = vec![];
        if self.line != EngineLine::General {
            return mentions;
        }
        let Ok(tokens) = lex(text) else { return mentions };
        for (i, token) in tokens.iter().enumerate() {
            let Some(identifier) = token.ident() else { continue };
            let word = segments(identifier);
            let mut mention = |rule: &'static str, name: &str| mentions.push(NameMention { rule, name: name.to_string(), identifier: identifier.to_string(), line: token.line });
            if let Some(table) = self.names.table_in(&word)
                && !after_stores_path(&tokens, i)
            {
                mention(SCHEMA_TABLE_MENTION, table);
            }
            if self.is_stage()
                && self.names.multi_word_column_in(&word).is_none()
                && let Some(column) = self.names.one_word_column_in(&word)
            {
                mention(SCHEMA_COLUMN_MENTION, column);
            }
        }
        mentions
    }

    /// What admission and the frozen engine record of the rule set. A stage run's record adds `stage` (its
    /// workloads, the one-word column names and the workload module's directory), a run of several workloads also
    /// `families` (R3-R5, the default module's directory and the plans' place); every other record is as before.
    pub fn record(&self) -> Value {
        let mut record = json!({"line":self.line.id(),"request_line":self.line.request_value(),"engine_rules":self.rules().iter().map(|r| r.id).collect::<Vec<_>>(),
            "template_constants":self.constants.constants().len(),
            "schema_names":{"tables":self.names.table_count(),"columns":self.names.column_count()}});
        if let Some(workloads) = &self.stage {
            record["stage"] = json!({"workloads":workloads,"one_word_columns":self.names.one_word_column_count(),"workload_module":WORKLOAD_MODULE_ROOT});
        }
        if self.members {
            record["families"] = json!({"rules":FAMILY_RULES.iter().map(|r| r.id).collect::<Vec<_>>(),"default_module":DEFAULT_MODULE_DIRECTORY,"plans":PLAN_FILE_PATTERN});
        }
        record
    }
}

/// The sites of each reported name a record keeps ([`EngineRuleSet::schema_name_report_summary`]).
pub const REPORTED_SITES: usize = 3;

/// One reported schema name in an identifier.
struct NameMention {
    rule: &'static str,
    name: String,
    identifier: String,
    line: usize,
}

/// How the schema-name rule treats column names of one segment.
#[derive(Clone, Copy, PartialEq, Eq)]
enum OneWordColumns {
    /// Like every column name (the general line).
    Refused,
    /// Refused as a whole word in literals only; reported in identifiers (a stage run).
    InLiteralsOnly,
}

/// Which rules one scan applies.
#[derive(Clone, Copy)]
struct Applied<'a> {
    /// [`TEMPLATE_CONSTANT_RULE`] and [`AST_FRAGMENT_RULE`].
    constants_and_fragments: bool,
    /// [`WHOLE_STATEMENT_EVALUATOR_RULE`] (the schema-engine line).
    evaluator: bool,
    /// The schema-name rule over these names (the general line and stage runs).
    names: Option<(&'a SchemaNames, OneWordColumns)>,
    /// [`WORKLOAD_MODULE_RULE`] (a stage run's file under [`WORKLOAD_MODULE_ROOT`]).
    workload_module: bool,
}

impl<'a> Applied<'a> {
    /// [`ENGINE_RULES`].
    const SCHEMA_ENGINE: Applied<'static> = Applied { constants_and_fragments: true, evaluator: true, names: None, workload_module: false };

    /// [`GENERAL_ENGINE_RULES`].
    fn general(names: &'a SchemaNames) -> Self {
        Applied { constants_and_fragments: true, evaluator: false, names: Some((names, OneWordColumns::Refused)), workload_module: false }
    }

    /// [`STAGE_ENGINE_RULES`] without the workload-module rule (a file outside a workload's module).
    fn stage(names: &'a SchemaNames) -> Self {
        Applied { constants_and_fragments: true, evaluator: false, names: Some((names, OneWordColumns::InLiteralsOnly)), workload_module: false }
    }
}

/// Neighbouring integer literals of one byte run have at most this many other tokens between them: the `) ; v . push (`
/// of repeated `v.push(49u8);` calls.
pub const RUN_GAP: usize = 6;
/// The three integers of a civil date have at most this many tokens between neighbours, each a comma, a colon or an
/// identifier: the `, m :` of `Literal::Date { y: 1995, m: 1, d: 1 }`.
const DATE_GAP: usize = 4;

/// What a template constant is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantKind {
    /// A string literal (a comparison value, an IN-list item, a whole LIKE pattern).
    Text,
    /// One literal segment of a LIKE pattern, between wildcards.
    LikeSegment,
    /// A `DATE '...'` literal.
    Date { y: i32, m: u32, d: u32 },
}

/// One constant and the templates whose texts contain it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TemplateConstant {
    pub kind: ConstantKind,
    /// The text (for a date: `YYYY-MM-DD`).
    pub text: String,
    pub templates: Vec<String>,
}

impl fmt::Display for TemplateConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match self.kind {
            ConstantKind::Text => "text constant",
            ConstantKind::LikeSegment => "LIKE pattern segment",
            ConstantKind::Date { .. } => "date constant",
        };
        write!(f, "{kind} '{}' of {}", self.text, self.templates.join(", "))
    }
}

/// The fixed constants of a set of template texts.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TemplateConstants {
    constants: Vec<TemplateConstant>,
}

impl TemplateConstants {
    /// The constants of every template named by `templates.json` (`{"templates": {name: {"sql": file}}}`, files relative
    /// to the JSON file's directory).
    pub fn from_templates_json(path: &Path) -> Result<Self, String> {
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let json: serde_json::Value = serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
        let templates = json["templates"].as_object().ok_or_else(|| format!("{}: no templates object", path.display()))?;
        let dir = path.parent().unwrap_or(Path::new("."));
        let mut texts = Vec::new();
        for (name, template) in templates {
            let file = dir.join(template["sql"].as_str().ok_or_else(|| format!("{name}: no sql file"))?);
            texts.push((name.clone(), std::fs::read_to_string(&file).map_err(|e| format!("{}: {e}", file.display()))?));
        }
        Self::from_texts(&texts)
    }

    /// The constants of `(template name, SQL text)` pairs.
    pub fn from_texts(texts: &[(String, String)]) -> Result<Self, String> {
        let mut found: BTreeMap<(ConstantKind, String), Vec<String>> = BTreeMap::new();
        for (name, sql) in texts {
            for literal in sql_string_literals(sql).map_err(|e| format!("{name}: {e}"))? {
                for (kind, text) in literal.constants().map_err(|e| format!("{name}: {e}"))? {
                    let templates = found.entry((kind, text)).or_default();
                    if !templates.contains(name) {
                        templates.push(name.clone());
                    }
                }
            }
        }
        Ok(Self { constants: found.into_iter().map(|((kind, text), templates)| TemplateConstant { kind, text, templates }).collect() })
    }

    pub fn constants(&self) -> &[TemplateConstant] {
        &self.constants
    }

    /// The constants of several workloads' templates together (a stage run), each template named
    /// `<workload>/<template>`.
    pub fn united(parts: &[(&str, &TemplateConstants)]) -> Self {
        let mut found: BTreeMap<(ConstantKind, String), Vec<String>> = BTreeMap::new();
        for (workload, constants) in parts {
            for c in &constants.constants {
                let templates = found.entry((c.kind, c.text.clone())).or_default();
                templates.extend(c.templates.iter().map(|t| format!("{workload}/{t}")));
            }
        }
        Self { constants: found.into_iter().map(|((kind, text), templates)| TemplateConstant { kind, text, templates }).collect() }
    }
}

/// One string literal of a SQL text, with the keywords just before it.
struct SqlLiteral {
    value: String,
    /// The word before the literal (`DATE`, `INTERVAL`, `LIKE`, ...), upper-cased; empty after a non-word.
    before: String,
}

impl SqlLiteral {
    /// The constants this literal contributes.
    fn constants(&self) -> Result<Vec<(ConstantKind, String)>, String> {
        match self.before.as_str() {
            "INTERVAL" => Ok(vec![]),
            "DATE" => {
                let parts: Vec<&str> = self.value.split('-').collect();
                let parse = || -> Option<ConstantKind> {
                    match parts.as_slice() {
                        [y, m, d] if y.len() == 4 && m.len() == 2 && d.len() == 2 => Some(ConstantKind::Date { y: y.parse().ok()?, m: m.parse().ok()?, d: d.parse().ok()? }),
                        _ => None,
                    }
                };
                let kind = parse().ok_or_else(|| format!("DATE '{}' is not YYYY-MM-DD", self.value))?;
                Ok(vec![(kind, self.value.clone())])
            }
            "LIKE" | "ILIKE" => {
                let mut out = vec![(ConstantKind::Text, self.value.clone())];
                for segment in like_segments(&self.value) {
                    if segment != self.value {
                        out.push((ConstantKind::LikeSegment, segment));
                    }
                }
                Ok(out)
            }
            _ => Ok(vec![(ConstantKind::Text, self.value.clone())]),
        }
    }
}

/// The literal segments of a LIKE pattern (default escape `\`): the text between `%`/`_` wildcards, non-empty.
fn like_segments(pattern: &str) -> Vec<String> {
    let (mut segments, mut current, mut chars) = (vec![], String::new(), pattern.chars());
    while let Some(c) = chars.next() {
        match c {
            '\\' => current.extend(chars.next()),
            '%' | '_' => segments.push(std::mem::take(&mut current)),
            c => current.push(c),
        }
    }
    segments.push(current);
    segments.into_iter().filter(|s| !s.is_empty()).collect()
}

/// Every `'...'` string literal of a SQL text (`''` is a quote), skipping `--` and `/* */` comments and `"..."`
/// identifiers, each with the word before it (`NOT` skipped, so `NOT LIKE` counts as `LIKE`).
fn sql_string_literals(sql: &str) -> Result<Vec<SqlLiteral>, String> {
    let chars: Vec<char> = sql.chars().collect();
    let (mut out, mut i) = (vec![], 0);
    let mut words: Vec<String> = vec![];
    while i < chars.len() {
        let c = chars[i];
        if c == '-' && chars.get(i + 1) == Some(&'-') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && chars.get(i + 1) == Some(&'*') {
            let end = (i + 2..chars.len().saturating_sub(1)).find(|&j| chars[j] == '*' && chars[j + 1] == '/').ok_or("unterminated comment")?;
            i = end + 2;
        } else if c == '\'' || c == '"' {
            let mut value = String::new();
            i += 1;
            loop {
                match chars.get(i) {
                    None => return Err("unterminated quoted text".into()),
                    Some(&q) if q == c && chars.get(i + 1) == Some(&c) => {
                        value.push(c);
                        i += 2;
                    }
                    Some(&q) if q == c => {
                        i += 1;
                        break;
                    }
                    Some(&other) => {
                        value.push(other);
                        i += 1;
                    }
                }
            }
            if c == '\'' {
                let before = words.iter().rev().find(|w| w.as_str() != "NOT").cloned().unwrap_or_default();
                out.push(SqlLiteral { value, before });
            }
            words.clear();
        } else if c.is_alphanumeric() || c == '_' || c == '$' {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_' || chars[i] == '$') {
                i += 1;
            }
            words.push(chars[start..i].iter().collect::<String>().to_uppercase());
        } else {
            if !c.is_whitespace() {
                words.clear();
            }
            i += 1;
        }
    }
    Ok(out)
}

/// The findings of the schema-engine line's [`ENGINE_RULES`] ([`TEMPLATE_CONSTANT_RULE`], [`AST_FRAGMENT_RULE`] and
/// [`WHOLE_STATEMENT_EVALUATOR_RULE`]) in one engine author file, sorted by line, without duplicates. The general
/// line scans through [`EngineRuleSet::scan_agent_source`].
pub fn scan_engine_source(file: &str, text: &str, constants: &TemplateConstants) -> Vec<RefusalFinding> {
    scan_rules(file, text, constants, Applied::SCHEMA_ENGINE)
}

/// The findings of the `applied` rules in one file, sorted by line, without duplicates.
fn scan_rules(file: &str, text: &str, constants: &TemplateConstants, applied: Applied<'_>) -> Vec<RefusalFinding> {
    let mut findings = Findings { file, list: Vec::new() };
    match lex(text) {
        Ok(tokens) => {
            let chars: Vec<char> = text.chars().collect();
            let literals: Vec<SourceLiteral> = tokens.iter().enumerate().filter_map(|(i, t)| SourceLiteral::of(&tokens, i, t, &chars)).collect();
            if applied.constants_and_fragments {
                constants_in_literal_text(&literals, constants, &mut findings);
                constants_in_integer_runs(&literals, constants, &mut findings);
                dates_as_integers(&tokens, &literals, constants, &mut findings);
                ast_fragments(&tokens, &chars, &mut findings);
            }
            if applied.evaluator {
                whole_statement_evaluator(&tokens, &mut findings);
            }
            if let Some((names, one_word)) = applied.names {
                schema_names(&tokens, &literals, names, one_word, &mut findings);
            }
            if applied.workload_module {
                workload_module_statements(&tokens, &mut findings);
            }
        }
        Err(error) => findings.refuse(error.line, rule::OUTSIDE_VERUS, format!("cannot lex author source: {}", error.message)),
    }
    let mut list = findings.list;
    list.sort_by(|a, b| (a.line, a.rule, &a.detail).cmp(&(b.line, b.rule, &b.detail)));
    list.dedup();
    list
}

/// [`SCHEMA_NAME_RULE`]: column names in identifiers and literal words, table names in literal words and in the
/// storage segment of `stores::` / `stores.` paths. With [`OneWordColumns::InLiteralsOnly`] (its stage form,
/// [`STAGE_SCHEMA_NAME_RULE`]) a one-word column name is refused only as a whole literal word.
fn schema_names(tokens: &[Token], literals: &[SourceLiteral], names: &SchemaNames, one_word: OneWordColumns, findings: &mut Findings) {
    let id = SCHEMA_NAME_RULE.id;
    // The column name an identifier or a literal word names, under the one-word treatment.
    let column_in = |word: &[String]| match one_word {
        OneWordColumns::Refused => names.column_in(word),
        OneWordColumns::InLiteralsOnly => names.multi_word_column_in(word),
    };
    for (i, token) in tokens.iter().enumerate() {
        let Some(name) = token.ident() else { continue };
        let word = segments(name);
        if let Some(column) = column_in(&word) {
            findings.refuse(token.line, id, format!("column name `{column}` in identifier `{name}`"));
        }
        if after_stores_path(tokens, i)
            && let Some(table) = names.table_in(&word)
        {
            findings.refuse(token.line, id, format!("table name `{table}` in the storage `stores::{name}` (a storage path named after a table)"));
        }
    }
    for literal in literals {
        let LiteralValue::Text(content) = &literal.value else { continue };
        for word in content.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).filter(|w| !w.is_empty()) {
            let parts = segments(word);
            let whole_word = || if one_word == OneWordColumns::InLiteralsOnly { names.one_word_column_equal(word) } else { None };
            if let Some(column) = column_in(&parts).or_else(whole_word) {
                findings.refuse(literal.line, id, format!("column name `{column}` in a string or char literal (`{word}`)"));
            }
            if let Some(table) = names.table_in(&parts) {
                findings.refuse(literal.line, id, format!("table name `{table}` in a string or char literal (`{word}`)"));
            }
        }
    }
}

/// Whether identifier token `i` follows `stores ::` or `stores .` (a storage's module or its `Stores` field).
fn after_stores_path(tokens: &[Token], i: usize) -> bool {
    i >= 2 && tokens[i - 2].ident() == Some("stores") && (tokens[i - 1].tok == Tok::Op("::") || tokens[i - 1].is_punct('.'))
}

/// [`WORKLOAD_MODULE_RULE`]: a statement type as an identifier, `spec::ast` / `exec::ast`, `gendb_ast_codec`.
fn workload_module_statements(tokens: &[Token], findings: &mut Findings) {
    let id = WORKLOAD_MODULE_RULE.id;
    for (i, token) in tokens.iter().enumerate() {
        match token.ident() {
            Some(name) if STATEMENT_TYPES.contains(&name) => findings.refuse(token.line, id, format!("`{name}`: a statement type in a workload module")),
            Some("ast") if i >= 2 && matches!(tokens[i - 2].ident(), Some("spec" | "exec")) && tokens[i - 1].tok == Tok::Op("::") => {
                findings.refuse(token.line, id, format!("`{}::ast`: the AST module in a workload module", tokens[i - 2].ident().unwrap_or_default()))
            }
            Some("gendb_ast_codec") => findings.refuse(token.line, id, "`gendb_ast_codec`: the AST codec in a workload module".into()),
            _ => {}
        }
    }
}

/// [`PLAN_IS_DATA_RULE`] over one plan file (`file` names it in the findings): the findings, sorted by line, without
/// duplicates; none for a plan that is data. Lexical (tokens, comments dropped): the file is `use` items, a `verus!`
/// block of the same, and exactly one `pub fn plan() -> <type> { <data> }`.
pub fn scan_plan_source(file: &str, text: &str) -> Vec<RefusalFinding> {
    let mut findings = Findings { file, list: Vec::new() };
    match lex(text) {
        Ok(tokens) => {
            let chars: Vec<char> = text.chars().collect();
            let texts = tokens.iter().map(|t| chars[t.span.clone()].iter().collect()).collect();
            let mut scan = PlanScan { tokens: &tokens, texts, plans: 0, findings: &mut findings };
            scan.items(0, tokens.len(), true);
            let plans = scan.plans;
            if plans != 1 {
                findings.refuse(0, PLAN_IS_DATA_RULE.id, format!("a plan file has exactly one `pub fn plan()`, not {plans}"));
            }
        }
        Err(error) => findings.refuse(error.line, PLAN_IS_DATA_RULE.id, format!("cannot lex the plan: {}", error.message)),
    }
    let mut list = findings.list;
    list.sort_by(|a, b| (a.line, &a.detail).cmp(&(b.line, &b.detail)));
    list.dedup();
    list
}

/// Words a plan's body and return type may not hold: statements, control flow, bindings, specification and proof.
const PLAN_KEYWORDS: [&str; 34] = [
    "if", "else", "match", "loop", "while", "for", "let", "return", "break", "continue", "fn", "move", "as", "in", "mut", "ref", "unsafe", "static",
    "const", "impl", "struct", "enum", "trait", "type", "mod", "use", "where", "proof", "assert", "assume", "requires", "ensures", "decreases", "recommends",
];

/// One scan of a plan file: its tokens and their texts, the `plan` functions seen, the findings.
struct PlanScan<'a, 'f> {
    tokens: &'a [Token],
    texts: Vec<String>,
    plans: usize,
    findings: &'a mut Findings<'f>,
}

impl PlanScan<'_, '_> {
    fn refuse(&mut self, line: usize, detail: String) {
        self.findings.refuse(line, PLAN_IS_DATA_RULE.id, detail);
    }

    /// The items in tokens `start..end`: `use` items, at the top level one `verus!` block of items, and `pub fn plan`.
    fn items(&mut self, start: usize, end: usize, top: bool) {
        let tokens = self.tokens;
        let mut i = start;
        while i < end {
            let at = |k: usize| tokens.get(i + k).filter(|_| i + k < end);
            let word = |k: usize| at(k).and_then(Token::ident);
            match tokens[i].ident() {
                Some("use") => i = self.use_item(i + 1, end),
                Some("pub") if word(1) == Some("use") => i = self.use_item(i + 2, end),
                Some("verus") if top && at(1).is_some_and(|t| t.is_punct('!')) && at(2).is_some_and(|t| t.is_punct('{')) => {
                    let close = group_end(tokens, i + 2).min(end);
                    self.items(i + 3, close.saturating_sub(1), false);
                    i = close;
                }
                Some("pub") if word(1) == Some("fn") && word(2) == Some("plan") => {
                    self.plans += 1;
                    i = self.function(i + 3, end);
                }
                _ => {
                    let detail = format!("`{}`: a plan file holds only `use` items and `pub fn plan() -> <type> {{ <data> }}`", self.texts[i]);
                    self.refuse(tokens[i].line, detail);
                    i += 1;
                }
            }
        }
    }

    /// A `use` item from token `i` (after `use`) to its `;`: identifiers, `::`, `{`, `}`, `,` and `*`. Returns the index
    /// after it.
    fn use_item(&mut self, mut i: usize, end: usize) -> usize {
        while i < end && !self.tokens[i].is_punct(';') {
            let t = &self.tokens[i];
            let path_token = t.ident().is_some() || t.tok == Tok::Op("::") || ['{', '}', ',', '*'].iter().any(|&c| t.is_punct(c));
            if !path_token {
                let detail = format!("`{}` in a `use` item", self.texts[i]);
                self.refuse(t.line, detail);
            }
            i += 1;
        }
        i + 1
    }

    /// `pub fn plan` from token `i` (after `plan`): `()`, `->`, a return type of paths, generics, tuples and arrays, and a
    /// body of data ([`PlanScan::body`]). Returns the index after the body.
    fn function(&mut self, i: usize, end: usize) -> usize {
        let tokens = self.tokens;
        let line = tokens.get(i).map_or(0, |t| t.line);
        let shape = tokens.get(i).is_some_and(|t| t.is_punct('(')) && tokens.get(i + 1).is_some_and(|t| t.is_punct(')')) && tokens.get(i + 2).is_some_and(|t| t.tok == Tok::Op("->"));
        if !shape {
            self.refuse(line, "`pub fn plan` takes no parameter and returns its plan: `pub fn plan() -> <type> { .. }`".into());
            return end;
        }
        let mut k = i + 3;
        while k < end && !tokens[k].is_punct('{') {
            let t = &tokens[k];
            let type_token = match t.ident() {
                Some(word) => !PLAN_KEYWORDS.contains(&word),
                None => t.tok == Tok::Op("::") || ['<', '>', ',', '(', ')', '[', ']', ';'].iter().any(|&c| t.is_punct(c)) || self.numeric(k),
            };
            if !type_token {
                let detail = format!("`{}` in the return type of `plan`", self.texts[k]);
                self.refuse(t.line, detail);
            }
            k += 1;
        }
        if k >= end {
            self.refuse(line, "`pub fn plan` has no body".into());
            return end;
        }
        let close = group_end(tokens, k).min(end);
        self.body(k + 1, close.saturating_sub(1));
        close
    }

    /// The body of `plan` in tokens `start..end`: data only ([`PLAN_IS_DATA_RULE`]).
    fn body(&mut self, start: usize, end: usize) {
        let tokens = self.tokens;
        for k in start..end {
            let t = &tokens[k];
            let next = tokens.get(k + 1).filter(|_| k + 1 < end);
            let after_vec = k > start && tokens[k - 1].ident() == Some("vec");
            let refused = match t.ident() {
                Some(word) if PLAN_KEYWORDS.contains(&word) => Some(format!("`{word}`")),
                Some("vec") if next.is_some_and(|n| n.is_punct('!')) => {
                    (!tokens.get(k + 2).is_some_and(|n| n.is_punct('['))).then(|| "`vec!` other than `vec![..]`".to_string())
                }
                Some(word) if next.is_some_and(|n| n.is_punct('!')) => Some(format!("the macro `{word}!` (only `vec![..]`)")),
                Some(word) if next.is_some_and(|n| n.is_punct('(')) && !word.starts_with(|c: char| c.is_ascii_uppercase()) => {
                    Some(format!("the call `{word}(..)` (only constructors written with an uppercase name)"))
                }
                Some(_) => None,
                None if t.tok == Tok::Literal => (!self.numeric(k)).then(|| format!("the literal `{}` (a plan holds ids, flags and numbers)", self.texts[k])),
                None if t.tok == Tok::Op("::") => None,
                None if ['{', '}', '(', ')', '[', ']', ',', ':'].iter().any(|&c| t.is_punct(c)) => None,
                None if t.is_punct('!') && after_vec => None,
                None if t.is_punct('-') && next.is_some_and(|_| self.numeric(k + 1)) => None,
                None => Some(format!("`{}`", self.texts[k])),
            };
            if let Some(what) = refused {
                self.refuse(t.line, format!("{what} in the body of `plan`"));
            }
        }
    }

    /// Whether token `k` is a numeric literal (its text starts with a digit).
    fn numeric(&self, k: usize) -> bool {
        self.tokens[k].tok == Tok::Literal && self.texts[k].starts_with(|c: char| c.is_ascii_digit())
    }
}

/// What a stage run's workload module holds, for the freeze and admission records (module documentation: reported, not
/// refused): of the files of `files` under [`WORKLOAD_MODULE_ROOT`], their number and lines, their items by kind
/// (executable, proof and spec functions, types, impls, traits, consts), their executable loops (`while`, `loop`,
/// `for .. in`) and the storages they name after `stores::` / `stores.`. Lexical counts, comments excluded; an empty
/// module (no file) is all zeros.
pub fn workload_module_report(files: &[FrameworkSource]) -> Value {
    let mut kinds: BTreeMap<&'static str, usize> = ["exec_fn", "proof_fn", "spec_fn", "struct", "enum", "trait", "impl", "const", "type"].into_iter().map(|k| (k, 0)).collect();
    let (mut count, mut lines, mut loops, mut unreadable) = (0usize, 0usize, 0usize, vec![]);
    let mut storages = std::collections::BTreeSet::new();
    for file in files.iter().filter(|f| f.path.starts_with(WORKLOAD_MODULE_ROOT)) {
        count += 1;
        lines += file.text.lines().count();
        let Ok(tokens) = lex(&file.text) else {
            unreadable.push(file.path.clone());
            continue;
        };
        for (i, token) in tokens.iter().enumerate() {
            let Some(word) = token.ident() else { continue };
            let next_is = |name: &str| tokens.get(i + 1).and_then(Token::ident) == Some(name);
            let kind = match word {
                "fn" => Some(function_kind(&tokens, i)),
                "struct" | "enum" | "trait" | "impl" | "type" => Some(word),
                "const" if !next_is("fn") => Some("const"),
                _ => None,
            };
            if let Some(kind) = kind
                && let Some(n) = kinds.get_mut(kind)
            {
                *n += 1;
            }
            let for_loop = word == "for" && tokens[i + 1..].iter().take_while(|t| !t.is_punct('{') && !t.is_punct(';')).any(|t| t.ident() == Some("in"));
            if word == "while" || word == "loop" || for_loop {
                loops += 1;
            }
            if after_stores_path(&tokens, i) {
                storages.insert(word.to_string());
            }
        }
    }
    json!({"root":WORKLOAD_MODULE_ROOT,"files":count,"lines":lines,"items":kinds,"loops":loops,"storages_named":storages,"unreadable":unreadable,
        "meaning":"what this workload's module holds (lexical counts, comments excluded): it should open the workload's storages as the engine's tables and prove what that needs; storage technique belongs in the storages and the shared engine, parameterized by the schema. Reported, not refused"})
}

/// The kind of the function whose `fn` keyword is token `i`: `proof_fn` or `spec_fn` when its qualifiers say so, else
/// `exec_fn`.
fn function_kind(tokens: &[Token], i: usize) -> &'static str {
    for token in tokens[..i].iter().rev() {
        match token.ident() {
            Some("proof") => return "proof_fn",
            Some("spec") => return "spec_fn",
            Some("pub" | "open" | "closed" | "exec" | "const" | "crate" | "super" | "in" | "uninterp") => {}
            _ if token.is_punct('(') || token.is_punct(')') => {}
            _ => break,
        }
    }
    "exec_fn"
}

/// One literal token of the author file, decoded.
struct SourceLiteral {
    /// Token index and line.
    index: usize,
    line: usize,
    value: LiteralValue,
}

enum LiteralValue {
    /// The decoded content of a string, byte string, raw string, char or byte char literal.
    Text(String),
    /// An integer literal: its value, whether a `-` token precedes it, and whether it carries the `u8` suffix.
    Integer { value: u128, negative: bool, u8_suffix: bool },
    /// Any other literal (a float, a C string, an unreadable form).
    Other,
}

impl SourceLiteral {
    fn of(tokens: &[Token], index: usize, token: &Token, chars: &[char]) -> Option<Self> {
        if token.tok != Tok::Literal {
            return None;
        }
        let source: String = chars[token.span.clone()].iter().collect();
        let value = match source.chars().next() {
            Some('"' | '\'' | 'b' | 'r') => text_literal(&source).map_or(LiteralValue::Other, LiteralValue::Text),
            Some(d) if d.is_ascii_digit() => match integer_literal(&source) {
                Some((value, u8_suffix)) => LiteralValue::Integer { value, negative: index > 0 && tokens[index - 1].is_punct('-'), u8_suffix },
                None => LiteralValue::Other,
            },
            _ => LiteralValue::Other,
        };
        Some(Self { index, line: token.line, value })
    }
}

/// The content of a string-like literal: `"..."`, `b"..."`, `r#"..."#`, `br"..."`, `'.'`, `b'.'` (escapes decoded).
/// `None` for a C string or a form this scan does not read.
fn text_literal(source: &str) -> Option<String> {
    let body = source.strip_prefix('b').unwrap_or(source);
    if let Some(raw) = body.strip_prefix('r') {
        let hashes = raw.chars().take_while(|&c| c == '#').count();
        let inner = raw.get(hashes..)?.strip_prefix('"')?;
        return Some(inner.get(..inner.len().checked_sub(1 + hashes)?)?.to_string());
    }
    let quote = body.chars().next()?;
    if quote != '"' && quote != '\'' {
        return None;
    }
    unescape(body.get(1..body.len().checked_sub(1)?)?)
}

/// Rust's string escapes: `\n \r \t \\ \0 \' \"`, `\x41`, `\u{..}`, and a backslash-newline continuation.
fn unescape(text: &str) -> Option<String> {
    let (mut out, mut chars) = (String::new(), text.chars().peekable());
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            '0' => out.push('\0'),
            '\\' => out.push('\\'),
            '\'' => out.push('\''),
            '"' => out.push('"'),
            'x' => {
                let hex: String = [chars.next()?, chars.next()?].iter().collect();
                out.push(char::from(u8::from_str_radix(&hex, 16).ok()?));
            }
            'u' => {
                chars.next().filter(|&c| c == '{')?;
                let hex: String = chars.by_ref().take_while(|&c| c != '}').filter(|&c| c != '_').collect();
                out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
            }
            '\n' => {
                while chars.peek().is_some_and(|c| c.is_whitespace()) {
                    chars.next();
                }
            }
            _ => return None,
        }
    }
    Some(out)
}

/// The value of an integer literal (`49`, `49u8`, `0x31_u8`, `1_995`, `0b1`, `0o7`) and whether its suffix is `u8`.
/// `None` for a float or an unreadable form.
fn integer_literal(source: &str) -> Option<(u128, bool)> {
    let text: String = source.chars().filter(|&c| c != '_').collect();
    let (radix, digits) = match text.get(..2) {
        Some("0x") => (16, &text[2..]),
        Some("0o") => (8, &text[2..]),
        Some("0b") => (2, &text[2..]),
        _ => (10, text.as_str()),
    };
    let end = digits.find(|c: char| !c.is_digit(radix)).unwrap_or(digits.len());
    let (number, suffix) = digits.split_at(end);
    let valid_suffix = suffix.is_empty() || suffix.starts_with('u') || suffix.starts_with('i') || matches!(suffix, "int" | "nat");
    if number.is_empty() || !valid_suffix {
        return None;
    }
    Some((u128::from_str_radix(number, radix).ok()?, suffix == "u8"))
}

/// Constants spelled inside string and char literal contents.
fn constants_in_literal_text(literals: &[SourceLiteral], constants: &TemplateConstants, findings: &mut Findings) {
    for literal in literals {
        let LiteralValue::Text(content) = &literal.value else { continue };
        for constant in constants.constants() {
            let hit = match constant.kind {
                ConstantKind::Date { .. } => content.contains(&constant.text),
                _ if constant.text.chars().count() == 1 => content == &constant.text,
                _ => content.contains(&constant.text),
            };
            if hit {
                findings.refuse(literal.line, TEMPLATE_CONSTANT_RULE.id, format!("{constant} in a string or char literal"));
            }
        }
    }
}

/// Constants spelled as runs of byte-valued integer literals.
fn constants_in_integer_runs(literals: &[SourceLiteral], constants: &TemplateConstants, findings: &mut Findings) {
    let mut runs: Vec<Vec<&SourceLiteral>> = vec![];
    let mut previous: Option<usize> = None;
    for literal in literals {
        let in_byte_range = matches!(literal.value, LiteralValue::Integer { value, negative: false, .. } if value <= 255);
        let joins = in_byte_range && previous.is_some_and(|p| literal.index - p - 1 <= RUN_GAP) && runs.last().is_some_and(|r| !r.is_empty());
        match (in_byte_range, joins) {
            (true, true) => runs.last_mut().expect("joins an open run").push(literal),
            (true, false) => runs.push(vec![literal]),
            (false, _) => runs.push(vec![]),
        }
        previous = Some(literal.index);
    }
    for run in runs.iter().filter(|r| !r.is_empty()) {
        let bytes: Vec<u128> = run.iter().map(|l| match l.value { LiteralValue::Integer { value, .. } => value, _ => unreachable!("runs hold integers") }).collect();
        for constant in constants.constants().iter().filter(|c| !matches!(c.kind, ConstantKind::Date { .. })) {
            let target: Vec<u128> = constant.text.bytes().map(u128::from).collect();
            let at = if target.len() == 1 {
                let single_u8 = matches!(run[0].value, LiteralValue::Integer { u8_suffix: true, .. });
                (run.len() == 1 && single_u8 && bytes == target).then_some(0)
            } else {
                bytes.windows(target.len()).position(|w| w == target.as_slice())
            };
            if let Some(at) = at {
                let line = run[at].line;
                findings.refuse(line, TEMPLATE_CONSTANT_RULE.id, format!("{constant} as the byte values {target:?}"));
            }
        }
    }
}

/// Days from 1970-01-01 to the civil date (proleptic Gregorian).
fn days_from_unix_epoch(y: i32, m: u32, d: u32) -> i64 {
    let y = i64::from(y) - i64::from(m <= 2);
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let mp = (i64::from(m) + 9) % 12;
    let doy = (153 * mp + 2) / 5 + i64::from(d) - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

/// Day number of 2000-01-01 from 1970-01-01 (SQLSpec's and PostgreSQL's date epoch).
const PG_EPOCH_FROM_UNIX: i64 = 10_957;

/// Dates spelled as integers: `Y, M, D` neighbours, `YYYYMMDD`, or a day number from 2000-01-01 or 1970-01-01.
fn dates_as_integers(tokens: &[Token], literals: &[SourceLiteral], constants: &TemplateConstants, findings: &mut Findings) {
    let civil_separator = |t: &Token| t.is_punct(',') || t.is_punct(':') || t.ident().is_some();
    let neighbours = |a: &SourceLiteral, b: &SourceLiteral| b.index - a.index - 1 <= DATE_GAP && tokens[a.index + 1..b.index].iter().all(civil_separator);
    let integers: Vec<(&SourceLiteral, i128)> = literals
        .iter()
        .filter_map(|l| match l.value {
            LiteralValue::Integer { value, negative, .. } => i128::try_from(value).ok().map(|v| (l, if negative { -v } else { v })),
            _ => None,
        })
        .collect();
    for constant in constants.constants() {
        let ConstantKind::Date { y, m, d } = constant.kind else { continue };
        let unix = i128::from(days_from_unix_epoch(y, m, d));
        let forms = [
            (i128::from(y) * 10_000 + i128::from(m) * 100 + i128::from(d), "the integer YYYYMMDD"),
            (unix - i128::from(PG_EPOCH_FROM_UNIX), "its day number from 2000-01-01"),
            (unix, "its day number from 1970-01-01"),
        ];
        for (literal, value) in &integers {
            if let Some((_, form)) = forms.iter().find(|(v, _)| v == value) {
                findings.refuse(literal.line, TEMPLATE_CONSTANT_RULE.id, format!("{constant} as {form} {value}"));
            }
        }
        for triple in literals.windows(3) {
            let values: Vec<Option<i128>> = triple
                .iter()
                .map(|l| match l.value {
                    LiteralValue::Integer { value, negative: false, .. } => i128::try_from(value).ok(),
                    _ => None,
                })
                .collect();
            let close = neighbours(&triple[0], &triple[1]) && neighbours(&triple[1], &triple[2]);
            if close && values == [Some(i128::from(y)), Some(i128::from(m)), Some(i128::from(d))] {
                findings.refuse(triple[0].line, TEMPLATE_CONSTANT_RULE.id, format!("{constant} as the integers {y}, {m}, {d}"));
            }
        }
    }
}

/// `EQuery::Table(<integer literal>)` and `EExpr::Col(<integer literal>)`.
fn ast_fragments(tokens: &[Token], chars: &[char], findings: &mut Findings) {
    for (i, window) in tokens.windows(6).enumerate() {
        let node = match (window[0].ident(), &window[1].tok, window[2].ident()) {
            (Some("EQuery"), Tok::Op("::"), Some("Table")) => "EQuery::Table",
            (Some("EExpr"), Tok::Op("::"), Some("Col")) => "EExpr::Col",
            _ => continue,
        };
        let literal = &window[4];
        let numeric = literal.tok == Tok::Literal && chars.get(literal.span.start).is_some_and(char::is_ascii_digit);
        if window[3].is_punct('(') && numeric && window[5].is_punct(')') {
            let index: String = chars[literal.span.clone()].iter().collect();
            findings.refuse(tokens[i].line, AST_FRAGMENT_RULE.id, format!("`{node}({index})`: an AST node with a fixed index"));
        }
    }
}

/// [`WHOLE_STATEMENT_EVALUATOR_RULE`]: the evaluator modules' paths (the query freezes' check); a glob import of
/// `exec::relational` itself (`relational::*`, or `*` as an item of a `relational::{..}` group), which would bring the
/// evaluator modules in under their bare names; an alias of `relational`; and the names of [`EVALUATOR_ROUTES`] as
/// identifiers anywhere. A glob of another submodule (`relational::domain::*`) is allowed: the routes it could bring in
/// are refused by name.
fn whole_statement_evaluator(tokens: &[Token], findings: &mut Findings) {
    refuse_evaluator_paths(tokens, findings);
    let id = WHOLE_STATEMENT_EVALUATOR_RULE.id;
    for (i, token) in tokens.iter().enumerate() {
        match token.ident() {
            Some("relational") => {
                let next = tokens.get(i + 1);
                if next.and_then(Token::ident) == Some("as") {
                    findings.refuse(token.line, id, "`relational as ..`: an alias of exec::relational".into());
                }
                if next.map(|t| &t.tok) == Some(&Tok::Op("::")) && glob_of_module(&tokens[i + 2..]) {
                    findings.refuse(token.line, id, "a glob import of exec::relational".into());
                }
            }
            Some(name) => {
                if let Some(route) = EVALUATOR_ROUTES.iter().find(|r| r.function == name) {
                    findings.refuse(token.line, id, format!("`{name}` ({}): {}", route.module, route.reaches));
                }
            }
            None => {}
        }
    }
}

/// Whether the path continuing after `module::` imports every item of the module: `*`, or a `{..}` group with `*` as
/// one of its top-level items.
fn glob_of_module(rest: &[Token]) -> bool {
    match rest.first() {
        Some(first) if first.is_punct('*') => true,
        Some(first) if first.is_punct('{') => {
            let (mut depth, mut at_item_start) = (0usize, true);
            for inner in &rest[1..] {
                let closes = inner.is_punct('}') || inner.is_punct(')') || inner.is_punct(']');
                if closes && depth == 0 {
                    return false;
                }
                if depth == 0 && at_item_start && inner.is_punct('*') {
                    return true;
                }
                at_item_start = depth == 0 && inner.is_punct(',');
                if inner.is_punct('{') || inner.is_punct('(') || inner.is_punct('[') {
                    depth += 1;
                } else if closes {
                    depth -= 1;
                }
            }
            false
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn templates() -> TemplateConstants {
        TemplateConstants::from_templates_json(&Path::new(env!("CARGO_MANIFEST_DIR")).join("../fixtures/tpch/templates/templates.json")).unwrap()
    }

    /// The (line, rule) pairs of the findings, once each (one literal may spell several constants).
    fn rules(src: &str) -> Vec<(usize, &'static str)> {
        let mut found: Vec<(usize, &str)> = scan_engine_source("agent/plan.rs", src, &templates()).into_iter().map(|f| (f.line, f.rule)).collect();
        found.dedup();
        found
    }

    /// The derived list of the 22 template texts: every string literal except INTERVAL quantities, DATE literals as
    /// dates, LIKE patterns with their segments.
    #[test]
    fn constants_are_derived_from_the_template_texts() {
        let found: Vec<String> = templates().constants().iter().map(|c| format!("{c}")).collect();
        for expected in [
            "text constant '1-URGENT' of Q12",
            "text constant '%Customer%Complaints%' of Q16",
            "LIKE pattern segment 'Customer' of Q16",
            "LIKE pattern segment 'PROMO' of Q14",
            "text constant 'AIR REG' of Q19",
            "text constant 'R' of Q10",
            "text constant 'F' of Q21",
            "date constant '1995-01-01' of Q07, Q08",
        ] {
            assert!(found.contains(&expected.to_string()), "{expected} not in {found:?}");
        }
        assert!(!found.iter().any(|c| c.contains("'3'") || c.contains("'1'")), "INTERVAL quantities are not constants: {found:?}");
        assert_eq!(found.len(), 26, "{found:#?}");
    }

    #[test]
    fn sql_literals_and_like_segments() {
        let found = TemplateConstants::from_texts(&[("T".into(), "SELECT 'it''s' -- 'comment'\n FROM t WHERE x NOT LIKE '%a\\%b_c%' AND d < DATE '2001-02-03' + INTERVAL '7' DAY AND \"q'uoted\" = 1 /* 'no' */".into())]).unwrap();
        let texts: Vec<(ConstantKind, &str)> = found.constants().iter().map(|c| (c.kind, c.text.as_str())).collect();
        assert_eq!(texts, [
            (ConstantKind::Text, "%a\\%b_c%"),
            (ConstantKind::Text, "it's"),
            (ConstantKind::LikeSegment, "a%b"),
            (ConstantKind::LikeSegment, "c"),
            (ConstantKind::Date { y: 2001, m: 2, d: 3 }, "2001-02-03"),
        ]);
        assert!(TemplateConstants::from_texts(&[("T".into(), "SELECT DATE '2001-2-3'".into())]).is_err());
    }

    /// Planted positives: each spelling of a template constant the rule names, AST nodes with fixed indices, and a
    /// reference to the whole-statement evaluator.
    #[test]
    fn planted_constants_are_refused() {
        let constant = TEMPLATE_CONSTANT_RULE.id;
        let cases: &[(&str, &[(usize, &str)])] = &[
            ("verus! { fn f() -> &'static str { \"1-URGENT\" } }", &[(1, constant)]),
            ("verus! { fn f() -> u8 { b'R' } }", &[(1, constant)]),
            ("verus! { fn f() -> &'static [u8] { br#\"x %Customer%Complaints% y\"# } }", &[(1, constant)]),
            ("verus! { fn f() -> &'static [u8] { b\"\\x50ROMO\" } }", &[(1, constant)]),
            ("verus! { spec fn p() -> Seq<u8> { seq![80u8, 82u8, 79u8, 77u8, 79u8, 37u8] } }", &[(1, constant)]),
            ("verus! { fn f() -> Vec<u8> { let mut v = Vec::new();\nv.push(49u8); v.push(45u8); v.push(85u8); v.push(82u8);\nv.push(71u8); v.push(69u8); v.push(78u8); v.push(84u8); v } }", &[(2, constant)]),
            ("verus! { fn f() -> Vec<u8> { vec![70u8] } }", &[(1, constant)]),
            ("verus! { spec fn d() -> Literal { Literal::Date { y: 1995, m: 1, d: 1 } } }", &[(1, constant)]),
            ("verus! { proof fn d() { assert(date_from_civil(1996, 12, 31) == -1096) by (compute); } }", &[(1, constant)]),
            ("verus! { const LO: i64 = 9131; }", &[(1, constant)]),
            ("verus! { const PACKED: u32 = 19961231; }", &[(1, constant)]),
            ("verus! { fn f() -> &'static str { \"since 1995-01-01\" } }", &[(1, constant)]),
            ("verus! { fn q(t: &EQuery) -> bool { match t { EQuery::Table(3) => true, _ => false } } }", &[(1, AST_FRAGMENT_RULE.id)]),
            ("verus! { fn e() -> EExpr { EExpr::Col(0x11) } }", &[(1, AST_FRAGMENT_RULE.id)]),
            ("use crate::exec::relational::entry::exec_ordered;\nverus! { fn f() {} }", &[(1, WHOLE_STATEMENT_EVALUATOR_RULE.id)]),
        ];
        for (src, expected) in cases {
            let found = rules(src);
            assert_eq!(found, *expected, "{src}");
        }
    }

    /// The whole-statement evaluator rule: paths, globs, aliases and every route's name, whatever way it arrives; the
    /// allowed helpers, the toolkit's checkers, longer identifiers, comments and literals pass.
    #[test]
    fn evaluator_routes_are_refused_by_path_glob_alias_and_name() {
        let id = WHOLE_STATEMENT_EVALUATOR_RULE.id;
        for src in [
            "use crate::exec::relational::eval::exec_query;",
            "use crate::exec::relational::*;",
            "use crate::exec::{relational::{*, order}};",
            "use crate::exec::relational::ops::*;\nfn f() { exec_filter(); }",
            "use crate::exec::relational as r;",
            "use crate::exec::expr::exec_expr as scalar_eval;",
            "fn f() { let v = crate::exec::expr::exec_expr(db, env, e); }",
            "use crate::exec::relational::ops::{exec_table, exec_filter};",
            "fn f() { let r = exec_group_by(db, ctx, q, rows); }",
            "fn f() { let r = self.evaluate(); }",
            "fn f() { if crate::exec::relational::constraints::check_constraints_exec(db).is_ok() {} }",
            "use crate::exec::relational as r;\nfn f() { r::ops::exec_project(db, ctx, es, rows); }",
        ] {
            assert!(rules(src).iter().any(|(_, rule)| *rule == id), "{src}");
        }
        for src in [
            "use crate::exec::relational::ops::{exec_table, product_rows_exec};\nuse crate::exec::relational::order::sort_rows_exec;",
            "use crate::exec::relational::aggregate::{exec_agg_value, exec_agg_row};\nuse crate::exec::expr::subquery_value_exec;",
            "use crate::exec::*;\nuse crate::exec::numeric::*;\nuse crate::exec::relational::domain::*;",
            "use crate::exec::relational::{ops::*, order::*};",
            "use crate::engine_link::classes_exec::{pred_total_exec, query_info_exec};\nuse crate::engine_link::classes_exec_ops::closed_value_exec;",
            "fn my_exec_expr(x: u64) -> u64 { x }\nfn evaluate_plan() {}",
            "// exec_filter and relational::* in a comment\nfn f() { let s = \"exec_expr\"; }",
            "fn f(a: u64, b: u64) -> u64 { a * b }",
        ] {
            assert_eq!(rules(src), vec![], "{src}");
        }
        let line: Vec<(usize, &str)> = rules("use x;\nuse crate::exec::relational::{\n    rows,\n    eval,\n};\nfn f() {\n    exec_filter(); }");
        assert_eq!(line, vec![(4, id), (7, id)]);
    }

    /// Every route is named in the rule's text, and no allowed helper is a route.
    #[test]
    fn evaluator_routes_and_allowed_helpers_are_consistent() {
        for route in EVALUATOR_ROUTES {
            assert!(WHOLE_STATEMENT_EVALUATOR_RULE.refuses.contains(route.function), "{} not named in the rule", route.function);
        }
        for helpers in ALLOWED_EXEC_HELPERS {
            for f in helpers.functions {
                assert!(!EVALUATOR_ROUTES.iter().any(|r| r.function == *f), "{f} is both allowed and a route");
            }
        }
    }

    /// Clean negatives: comments, unrelated literals, distant or large integers, one-byte values without the `u8`
    /// suffix, positive day numbers without their sign, AST nodes over variables, and per-operator helpers.
    #[test]
    fn clean_sources_pass() {
        for src in [
            "// '1-URGENT', 1995-01-01, Q12 checks '2-HIGH'\nverus! { /* PROMO% */ fn f() -> u64 { 0 } }",
            "verus! { fn f() -> &'static str { \"URGENT work\" } }",
            "verus! { fn f() -> u8 { b'Q' } }",
            "verus! { fn f() -> u64 { let a = 82; let b = 70; a + b } }",
            "verus! { #[verifier::rlimit(82)] fn f() -> u64 { 1826 } }",
            "verus! { fn f() -> Vec<u8> { vec![49u8, 45u8] } }",
            "verus! { fn f(x: u64) -> u64 { x + 1995 + 1 + 1 } }",
            "verus! { fn f(t: usize, c: usize) -> (EQuery, EExpr) { (EQuery::Table(t), EExpr::Col(c + 1)) } }",
            "verus! { fn f(q: &EQuery) -> bool { match q { EQuery::Table(t) => *t < 8, _ => false } } }",
            "use crate::exec::relational::{ops::exec_table, aggregate::exec_agg_row, order::sort_rows_exec};\nverus! { fn f() {} }",
        ] {
            assert_eq!(rules(src), vec![], "{src}");
        }
    }

    /// Some TPC-H names (the integration test of version 0 scans with the whole schema).
    fn tpch_names() -> SchemaNames {
        SchemaNames::from_names(
            ["lineitem", "orders", "part", "partsupp", "nation"],
            ["l_orderkey", "l_shipdate", "l_comment", "o_orderdate", "p_name", "p_type", "ps_partkey", "n_name"],
        )
    }

    fn general() -> EngineRuleSet {
        EngineRuleSet::general_with_names(templates(), tpch_names())
    }

    /// The (line, rule) pairs of the general line's findings in one agent file.
    fn general_rules(src: &str) -> Vec<(usize, &'static str)> {
        let mut found: Vec<(usize, &str)> = general().scan_agent_source("agent/plan.rs", src).into_iter().map(|f| (f.line, f.rule)).collect();
        found.dedup();
        found
    }

    /// The request's `engine.line` selects the line: absent is the schema-engine line, `"general"` the general line,
    /// anything else is refused; each line names its rules.
    #[test]
    fn engine_line_of_the_request() {
        assert_eq!(EngineLine::of_request(None), Ok(EngineLine::SchemaEngine));
        assert_eq!(EngineLine::of_request(Some("general")), Ok(EngineLine::General));
        assert!(EngineLine::of_request(Some("General")).is_err() && EngineLine::of_request(Some("")).is_err());
        assert_eq!(EngineLine::SchemaEngine.request_value(), None);
        assert_eq!(EngineLine::General.request_value(), Some("general"));
        let ids = |line: EngineLine| line.rules().iter().map(|r| r.id).collect::<Vec<_>>();
        assert_eq!(ids(EngineLine::SchemaEngine), ["template_constant", "ast_fragment_table", "whole_statement_evaluator"]);
        assert_eq!(ids(EngineLine::General), ["template_constant", "ast_fragment_table", "schema_name"]);
        let record = EngineRuleSet::for_line(EngineLine::SchemaEngine, templates(), &[]).record();
        assert_eq!(record["line"], "schema_engine");
        assert_eq!(record["request_line"], Value::Null);
        assert_eq!(record["schema_names"]["columns"], 0);
        let record = general().record();
        assert_eq!((record["line"].as_str(), record["request_line"].as_str()), (Some("general"), Some("general")));
        assert_eq!((record["schema_names"]["tables"].as_u64(), record["schema_names"]["columns"].as_u64()), (Some(5), Some(8)));
    }

    /// Without `engine.line` every planted evaluator case of the schema-engine run stays refused (the unchanged scan);
    /// the general line accepts them all, and still refuses template constants and AST fragments.
    #[test]
    fn the_general_line_lifts_only_the_evaluator_rule() {
        let schema_engine = EngineRuleSet::for_line(EngineLine::of_request(None).unwrap(), templates(), &[]);
        let evaluator = WHOLE_STATEMENT_EVALUATOR_RULE.id;
        for src in [
            "use crate::exec::relational::entry::exec_ordered;\nverus! { fn f() {} }",
            "use crate::exec::relational::eval::exec_query;",
            "use crate::exec::relational::*;",
            "use crate::exec::{relational::{*, order}};",
            "use crate::exec::relational::ops::*;\nfn f() { exec_filter(); }",
            "use crate::exec::relational as r;",
            "use crate::exec::expr::exec_expr as scalar_eval;",
            "fn f() { let v = crate::exec::expr::exec_expr(db, env, e); }",
            "use crate::exec::relational::ops::{exec_table, exec_filter};",
            "fn f() { let r = exec_group_by(db, ctx, q, rows); }",
            "fn f() { let r = self.evaluate(); }",
            "fn f() { if crate::exec::relational::constraints::check_constraints_exec(db).is_ok() {} }",
            "use crate::exec::relational as r;\nfn f() { r::ops::exec_project(db, ctx, es, rows); }",
        ] {
            let refused = |set: &EngineRuleSet| set.scan_agent_source("agent/plan.rs", src).iter().any(|f| f.rule == evaluator);
            assert!(refused(&schema_engine), "schema-engine line: {src}");
            assert_eq!(scan_engine_source("agent/plan.rs", src, &templates()), schema_engine.scan_agent_source("agent/plan.rs", src), "{src}");
            assert_eq!(general_rules(src), vec![], "general line: {src}");
        }
        assert_eq!(general_rules("verus! { fn f() -> &'static str { \"1-URGENT\" } }"), [(1, TEMPLATE_CONSTANT_RULE.id)]);
        assert_eq!(general_rules("verus! { const LO: i64 = 9131; }"), [(1, TEMPLATE_CONSTANT_RULE.id)]);
        assert_eq!(general_rules("verus! { fn e() -> EExpr { EExpr::Col(0x11) } }"), [(1, AST_FRAGMENT_RULE.id)]);
    }

    /// Planted schema names: a column name as an identifier, as identifier segments (any case), in a literal; a table
    /// name in a literal or as the storage of a `stores::` / `stores.` path. Each is refused on the general line only.
    #[test]
    fn planted_schema_names_are_refused_on_the_general_line() {
        let id = SCHEMA_NAME_RULE.id;
        for src in [
            "verus! { fn f() { let l_shipdate = 0; } }",
            "verus! { fn f(s: &mut StoredParts) { let r = read_l_shipdate_range(s, 0, 1, Ghost(rels)); } }",
            "verus! { fn f() -> usize { L_SHIPDATE } }",
            "verus! { fn f() -> usize { crate::stores::flat_lineitem::interface::L_COMMENT_OFFSETS } }",
            "verus! { fn f() -> usize { crate::stores::flat_lineitem::interface::PART_COUNT } }",
            "verus! { fn f(stores: &Stores) -> usize { stores.flat_partsupp.part_len(0) } }",
            "verus! { fn f() -> &'static str { \"l_orderkey\" } }",
            "verus! { fn f() -> &'static str { \"from part where\" } }",
            "verus! { fn f() -> &'static [u8] { b\"o_orderdate\" } }",
            "verus! { fn f() -> &'static str { \"LINEITEM\" } }",
            "verus! { fn n_name_of(x: u64) -> u64 { x } }",
        ] {
            assert!(general_rules(src).iter().any(|(_, rule)| *rule == id), "{src}");
            assert_eq!(rules(src).iter().filter(|(_, rule)| *rule == id).count(), 0, "schema-engine line: {src}");
        }
        let line: Vec<(usize, &str)> = general_rules("verus! {\n// l_shipdate in a comment\nfn f() {\n    let x = L_SHIPDATE;\n}\n}");
        assert_eq!(line, vec![(4, id)]);
        // The storage scan applies the schema-name rule alone.
        let storage = general().scan_storage_source("stores/zones/interface/mod.rs", "verus! { fn f() -> &'static str { \"1-URGENT\" } fn g() -> usize { P_NAME } }");
        assert_eq!(storage.iter().map(|f| (f.line, f.rule)).collect::<Vec<_>>(), [(1, id)]);
        assert_eq!(EngineRuleSet::for_line(EngineLine::SchemaEngine, templates(), &[]).scan_storage_source("builder/mod.rs", "fn g() -> usize { P_NAME }"), vec![]);
    }

    /// Clean negatives on the general line: framework words that contain a table name (`Part`, `parts`, `part_len`,
    /// `PartView`, `OwnedPart`), other words with a table name inside (`partition`, `orderly`), comments, segments that
    /// only share a prefix (`l`, `shipdate` alone, `ps`), and the generic access by ids. Table-name segments outside
    /// literals and storage paths are reported, not refused.
    #[test]
    fn clean_sources_pass_the_general_line() {
        let clean = [
            "verus! {",
            "use crate::gendb_abi::{OwnedPart, Part};",
            "use crate::gendb_entry::layout::PartView;",
            "use crate::flat_tables::{column_slice, materialize_table, ColumnSlice};",
            "// l_shipdate, lineitem and stores::flat_lineitem in a comment",
            "fn f(stores: &mut Stores, parts: &[Part], t: usize, c: usize) -> usize {",
            "    let part_len = parts.len();",
            "    let partition = 3;",
            "    let orderly = \"a partition, orderly\";",
            "    let (l, shipdate, ps) = (1, 2, 3);",
            "    let s = column_slice(stores, t, c, 0, 1, Ghost(db));",
            "    part_len + partition",
            "}",
            "}",
        ]
        .join("\n");
        let clean = clean.as_str();
        assert_eq!(general_rules(clean), vec![]);
        let reports = general().schema_name_reports("agent/plan.rs", clean);
        let reported: Vec<(usize, &str)> = reports.iter().map(|f| (f.line, f.rule)).collect();
        assert_eq!(reported, [(2, SCHEMA_TABLE_MENTION), (6, SCHEMA_TABLE_MENTION), (7, SCHEMA_TABLE_MENTION), (12, SCHEMA_TABLE_MENTION)], "{reports:?}");
        assert!(reports[2].detail.contains("`part_len`"), "{reports:?}");
        assert_eq!(EngineRuleSet::for_line(EngineLine::SchemaEngine, templates(), &[]).schema_name_reports("agent/plan.rs", clean), vec![]);
    }

    /// A stage run's names: the TPC-H names above plus SEC-EDGAR's (one-word columns `adsh`, `tag`, `value`, `fy`,
    /// `version`; tables `sub`, `num`, `tag`, `pre`).
    fn stage() -> EngineRuleSet {
        let names = SchemaNames::from_names(
            ["lineitem", "orders", "part", "partsupp", "nation", "sub", "num", "tag", "pre"],
            ["l_orderkey", "l_shipdate", "l_comment", "o_orderdate", "p_name", "p_type", "ps_partkey", "n_name", "adsh", "tag", "value", "fy", "version"],
        );
        EngineRuleSet::stage_with_names(&["sec", "tpch"], TemplateConstants::united(&[("tpch", &templates())]), names)
    }

    fn stage_rules(file: &str, src: &str) -> Vec<(usize, &'static str)> {
        let mut found: Vec<(usize, &str)> = stage().scan_agent_source(file, src).into_iter().map(|f| (f.line, f.rule)).collect();
        found.dedup();
        found
    }

    /// Stage runs: the TPC-H planted cases keep their findings (every TPC-H column name has two
    /// segments); one-word column names in identifiers (`tcol_value`, `has_tag`, a local `fy`) are accepted and
    /// reported, and refused as a whole literal word (`"value"`); table names refuse in literals and storage paths
    /// (`stores::num_pack`); statement types refuse in a workload module only; the constants are every workload's.
    #[test]
    fn stage_rules_refuse_one_word_names_only_in_literals() {
        let id = SCHEMA_NAME_RULE.id;
        for src in [
            "verus! { fn f() { let l_shipdate = 0; } }",
            "verus! { fn f(s: &mut StoredParts) { let r = read_l_shipdate_range(s, 0, 1, Ghost(rels)); } }",
            "verus! { fn f() -> usize { crate::stores::flat_lineitem::interface::PART_COUNT } }",
            "verus! { fn f() -> &'static str { \"from part where\" } }",
            "verus! { fn n_name_of(x: u64) -> u64 { x } }",
            "verus! { fn f() -> &'static str { \"value\" } }",
            "verus! { fn f() -> &'static [u8] { b\"num.VALUE\" } }",
            "verus! { fn f() -> usize { crate::stores::num_pack::interface::rows() } }",
            "verus! { fn f(stores: &Stores) -> usize { stores.pre_sorted.part_len(0) } }",
        ] {
            assert!(stage_rules("agent/plan.rs", src).iter().any(|(_, rule)| *rule == id), "{src}");
        }
        // The TPC-H findings are the general line's.
        for src in ["verus! {\n// l_shipdate in a comment\nfn f() {\n    let x = L_SHIPDATE;\n}\n}", "verus! { fn f() -> &'static str { \"1-URGENT\" } }", "verus! { fn e() -> EExpr { EExpr::Col(0x11) } }"] {
            assert_eq!(stage_rules("agent/plan.rs", src), general_rules(src), "{src}");
        }
        let accepted = "verus! {\nfn tcol_value(c: &TCol) -> u64 { 0 }\nfn has_tag(x: u8) -> bool { x > 0 }\nfn f(fy: u64, value: u64) -> u64 { let version = fy + value; version }\nfn g() -> &'static str { \"tcol_value\" }\n}";
        assert_eq!(stage_rules("agent/plan.rs", accepted), vec![]);
        let reports = stage().schema_name_reports("agent/plan.rs", accepted);
        let columns: Vec<(usize, &str)> = reports.iter().filter(|f| f.rule == SCHEMA_COLUMN_MENTION).map(|f| (f.line, f.detail.as_str())).collect();
        assert_eq!(columns.len(), 8, "{reports:#?}");
        assert!(columns[0].1.contains("`value` in identifier `tcol_value`") && columns[1].1.contains("`tag` in identifier `has_tag`"), "{columns:?}");
        assert!(reports.iter().any(|f| f.rule == SCHEMA_TABLE_MENTION && f.detail.contains("`tag` in identifier `has_tag`")), "a table name too");
        assert!(general().schema_name_reports("agent/plan.rs", accepted).iter().all(|f| f.rule == SCHEMA_TABLE_MENTION), "the general line reports no column mention");
        // The workload-module rule: statement types and AST paths in agent/workload/ only.
        let typed = "use crate::exec::ast::EQuery;\nverus! { fn f(q: &EQuery) -> bool { true } }";
        assert_eq!(stage_rules("agent/workload/open.rs", typed), [(1, WORKLOAD_MODULE_RULE.id), (2, WORKLOAD_MODULE_RULE.id)]);
        assert_eq!(stage_rules("agent/open.rs", typed), vec![], "the shared engine plans statements");
        for src in ["fn f() -> crate::spec::ast::OrderedQuery { x }", "use crate::gendb_ast_codec::decode_query;", "fn f(p: &Pred) {}"] {
            assert!(stage_rules("agent/workload/mod.rs", src).iter().any(|(_, rule)| *rule == WORKLOAD_MODULE_RULE.id), "{src}");
        }
        let opening = "use crate::gendb_entry::stores::Stores;\nuse crate::engine_link::bound::lemma_unique_bound_db;\nverus! {\n/// Opens the tables.\npub fn open_tables(stores: &mut Stores) -> u64 { let mut n = 0; while n < 4 { n += 1; } n }\n}";
        assert_eq!(stage_rules("agent/workload/mod.rs", opening), vec![]);
        assert_eq!(general_rules(typed), vec![], "outside stage runs agent/workload/ is an ordinary agent path");
        // The rule set's record and constants.
        let record = stage().record();
        assert_eq!(record["engine_rules"], json!(["template_constant", "ast_fragment_table", "schema_name", "workload_module_statement"]));
        assert_eq!((record["stage"]["workloads"].clone(), record["stage"]["one_word_columns"].clone()), (json!(["sec", "tpch"]), json!(5)));
        assert!(general().record().get("stage").is_none(), "non-stage records are as before");
        let united = TemplateConstants::united(&[("tpch", &templates()), ("other", &TemplateConstants::from_texts(&[("Q1".into(), "SELECT 'AIR REG'".into())]).unwrap())]);
        assert_eq!(united.constants().len(), templates().constants().len(), "a shared constant is one constant");
        let air = united.constants().iter().find(|c| c.text == "AIR REG").unwrap();
        assert_eq!(air.templates, ["tpch/Q19", "other/Q1"]);
        assert!(scan_rules("agent/x.rs", "fn f() -> &'static str { \"AIR REG\" }", &united, Applied::stage(&SchemaNames::default())).iter().any(|f| f.rule == TEMPLATE_CONSTANT_RULE.id));
        // Storage files: the stage form of the schema-name rule alone.
        let storage = stage().scan_storage_source("stores/zones/interface/mod.rs", "verus! { fn read_value() -> u64 { 0 } fn g() -> usize { P_NAME } fn h() -> &'static str { \"1-URGENT\" } }");
        assert_eq!(storage.iter().map(|f| (f.line, f.rule)).collect::<Vec<_>>(), [(1, id)]);
        assert_eq!(storage.len(), 1, "{storage:?}");
    }

    /// The reported mentions of many files are summarized per name with their first sites, the most frequent first.
    #[test]
    fn reports_are_summarized_per_name() {
        let a = "verus! { fn tcol_value(x: u64) -> u64 { let v = slice_value(x); v } }";
        let b = "verus! { fn num_rows(n: u64) -> u64 { n }\nfn has_tag() -> bool { true } fn value_of() {} fn value_at() {} }";
        let summary = stage().schema_name_report_summary([("agent/a.rs", a), ("agent/b.rs", b)]);
        assert_eq!(summary["total"], 7, "{summary:#}");
        let first = &summary["by_name"][0];
        assert_eq!((first["rule"].as_str(), first["name"].as_str(), first["count"].as_u64()), (Some(SCHEMA_COLUMN_MENTION), Some("value"), Some(4)));
        assert_eq!(first["first_sites"], json!(["agent/a.rs:1 `tcol_value`", "agent/a.rs:1 `slice_value`", "agent/b.rs:2 `value_of`"]));
        let names: Vec<(&str, u64)> = summary["by_name"].as_array().unwrap().iter().map(|n| (n["name"].as_str().unwrap(), n["count"].as_u64().unwrap())).collect();
        assert_eq!(names, [("value", 4), ("tag", 1), ("num", 1), ("tag", 1)]);
        assert_eq!(general().schema_name_report_summary([("agent/b.rs", b)])["total"], 0, "TPC-H names: nothing to report in b");
    }

    /// A workload module's report counts its files, lines, item kinds, loops and the storages it names; other files are
    /// not counted.
    #[test]
    fn workload_module_report_counts_its_shape() {
        let file = |path: &str, text: &str| FrameworkSource { path: path.into(), text: text.into() };
        let files = [
            file("agent/workload/mod.rs", "verus! {\npub struct Opened { n: u64 }\nimpl Opened { pub open spec fn rows(&self) -> u64 { self.n } }\npub proof fn lemma_open() {}\npub fn open(stores: &mut Stores) -> u64 {\n    let mut i = 0;\n    while i < 3 { i += 1; }\n    for k in 0..2 { i += k; }\n    crate::stores::flat_sub::interface::rows(&stores.flat_sub) + i\n}\nconst WIDTH: usize = 4;\n}\n"),
            file("agent/workload/keys.rs", "verus! { pub closed spec fn key(x: u64) -> u64 { x } pub const fn k() -> u64 { 1 } }"),
            file("agent/plan.rs", "verus! { fn other() { loop {} } }"),
        ];
        let report = workload_module_report(&files);
        assert_eq!((report["files"].as_u64(), report["lines"].as_u64(), report["loops"].as_u64()), (Some(2), Some(13), Some(2)));
        assert_eq!(report["items"], json!({"const":1,"enum":0,"exec_fn":2,"impl":1,"proof_fn":1,"spec_fn":2,"struct":1,"trait":0,"type":0}));
        assert_eq!(report["storages_named"], json!(["flat_sub"]));
        assert_eq!(workload_module_report(&files[2..])["files"], 0);
    }

    /// Diagnostic (read only): an engine's `agent/**` (directory `GENDB_STAGE_SCAN_AGENT`, for example a version
    /// folder's `code/agent`) under the stage rule set of the workloads whose request files (`dataset`) and
    /// `templates.json` are listed, colon-separated, in `GENDB_STAGE_SCAN_DATASETS` and `GENDB_STAGE_SCAN_TEMPLATES`
    /// (in the same order): its gating findings by rule and its reported mentions, printed. Asserts nothing.
    #[test]
    #[ignore = "reads the agent directory and the request and template files named by GENDB_STAGE_SCAN_*"]
    fn agent_sources_under_stage_rules() {
        let list = |name: &str| std::env::var(name).unwrap_or_else(|_| panic!("{name}")).split(':').map(std::path::PathBuf::from).collect::<Vec<_>>();
        let (datasets, template_files) = (list("GENDB_STAGE_SCAN_DATASETS"), list("GENDB_STAGE_SCAN_TEMPLATES"));
        let mut tables = vec![];
        let mut columns = vec![];
        let mut parts = vec![];
        for (k, (dataset, templates)) in datasets.iter().zip(&template_files).enumerate() {
            let request: Value = serde_json::from_slice(&std::fs::read(dataset).unwrap()).unwrap();
            for table in request["dataset"]["tables"].as_array().unwrap() {
                tables.push(table["name"].as_str().unwrap().to_string());
                columns.extend(table["fields"].as_array().unwrap().iter().map(|f| f["name"].as_str().unwrap().to_string()));
            }
            parts.push((format!("w{k}"), TemplateConstants::from_templates_json(templates).unwrap()));
        }
        let names = SchemaNames::from_names(tables.iter().map(String::as_str), columns.iter().map(String::as_str));
        let united = TemplateConstants::united(&parts.iter().map(|(w, c)| (w.as_str(), c)).collect::<Vec<_>>());
        let rules = EngineRuleSet::stage_with_names(&["w0", "w1"], united, names);
        let root = std::path::PathBuf::from(std::env::var("GENDB_STAGE_SCAN_AGENT").unwrap());
        let mut files = vec![];
        let mut stack = vec![(root.clone(), "agent".to_string())];
        while let Some((dir, prefix)) = stack.pop() {
            for item in std::fs::read_dir(&dir).unwrap() {
                let item = item.unwrap();
                let path = format!("{prefix}/{}", item.file_name().to_string_lossy());
                if item.file_type().unwrap().is_dir() {
                    stack.push((item.path(), path));
                } else if path.ends_with(".rs") {
                    files.push((path, std::fs::read_to_string(item.path()).unwrap()));
                }
            }
        }
        files.sort();
        let mut by_rule: BTreeMap<&str, usize> = BTreeMap::new();
        let mut examples = vec![];
        for (path, text) in &files {
            for f in rules.scan_agent_source(path, text) {
                *by_rule.entry(f.rule).or_default() += 1;
                if examples.len() < 10 {
                    examples.push(format!("{}:{} {}: {}", f.file, f.line, f.rule, f.detail));
                }
            }
        }
        let summary = rules.schema_name_report_summary(files.iter().map(|(p, t)| (p.as_str(), t.as_str())));
        let top: Vec<String> = summary["by_name"].as_array().unwrap().iter().take(8).map(|n| format!("{} {} x{}", n["rule"], n["name"], n["count"])).collect();
        println!("{} files; gating findings by rule {by_rule:?}\nfirst findings: {examples:#?}\nreported mentions {} (most frequent: {top:?})", files.len(), summary["total"]);
    }

    /// The scan bites: the 22 accepted per-template programs of the single-copy run (`output/.../queries/*/code`),
    /// which may legitimately name their template's constants, have findings. Their files are only read.
    #[test]
    #[ignore = "reads accepted per-template programs under output/ that are not part of this repository"]
    fn accepted_per_template_programs_are_caught() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../output/tpch-sf100-single-copy/queries");
        let constants = templates();
        let mut lines = vec![];
        let mut queries: Vec<_> = std::fs::read_dir(&root).unwrap().map(|e| e.unwrap().path()).filter(|p| p.join("code").is_dir()).collect();
        queries.sort();
        let mut total = 0;
        for query in queries {
            let mut files = vec![];
            let mut stack = vec![query.join("code")];
            while let Some(dir) = stack.pop() {
                for entry in std::fs::read_dir(&dir).unwrap() {
                    let path = entry.unwrap().path();
                    if path.is_dir() {
                        stack.push(path);
                    } else if path.extension().is_some_and(|e| e == "rs") {
                        files.push(path);
                    }
                }
            }
            files.sort();
            let mut by_rule: BTreeMap<&str, usize> = BTreeMap::new();
            let mut examples = vec![];
            for file in &files {
                let name = file.strip_prefix(&query).unwrap().display().to_string();
                for f in scan_engine_source(&name, &std::fs::read_to_string(file).unwrap(), &constants) {
                    *by_rule.entry(f.rule).or_default() += 1;
                    if examples.len() < 2 {
                        examples.push(format!("{}:{} {}", f.file, f.line, f.detail));
                    }
                }
            }
            let hits: usize = by_rule.values().sum();
            total += hits;
            lines.push(format!("{} files={} findings={hits} {by_rule:?} {examples:?}", query.file_name().unwrap().to_string_lossy(), files.len()));
        }
        println!("{}\ntotal findings {total}", lines.join("\n"));
        assert!(total > 0);
    }

    /// R4 (`plan_is_data`): a plan of struct literals, constructors, `vec![..]`, numbers and flags passes;
    /// every form of computation, text, attributes, other items and a second or missing `plan` is refused, each with
    /// its line.
    #[test]
    fn plans_are_data() {
        let accepted = [
            "use super::{Plan, Sort, Zones};\nuse vstd::prelude::*;\n/// The default plan: nothing sorted.\nverus! {\npub fn plan() -> Plan {\n    Plan { sort: vec![], zones: None }\n}\n}\n",
            "verus! {\n// tuned for the workload\npub fn plan() -> super::Plan {\n    super::Plan { sort: vec![Sort { table: 2, column: 0, descending: false }], zones: Some(Zones { columns: vec![3, 4], block_rows: 65_536 }), skew: -1, ratio: 0.5 }\n}\n}\n",
            "pub use super::Plan;\npub fn plan() -> Vec<(usize, u64)> { vec![(0, 1), (2, 3)] }\n",
        ];
        for text in accepted {
            assert_eq!(scan_plan_source("plans/sec/plainfam.rs", text), vec![], "{text}");
        }
        let refused = |text: &str, line: usize, words: &str| {
            let findings = scan_plan_source("default_plan.rs", text);
            assert!(findings.iter().any(|f| f.line == line && f.rule == PLAN_IS_DATA_RULE.id && f.detail.contains(words)), "{words}: {findings:?}");
        };
        refused("verus! {\npub fn plan() -> Plan {\n    if true { Plan::DEFAULT } else { Plan::DEFAULT }\n}\n}\n", 3, "`if`");
        refused("verus! {\npub fn plan() -> Plan {\n    Plan { sort: sorted_by(2) }\n}\n}\n", 3, "the call `sorted_by(..)`");
        refused("verus! {\npub fn plan() -> Plan {\n    Plan { width: 2 + 3 }\n}\n}\n", 3, "`+`");
        refused("verus! {\npub fn plan() -> Plan {\n    Plan { name: \"l_shipdate\" }\n}\n}\n", 3, "the literal");
        refused("verus! {\npub fn plan() -> Plan {\n    Plan { n: OTHER.len() }\n}\n}\n", 3, "`.`");
        refused("verus! {\npub fn plan() -> Plan {\n    Plan { ..Plan::DEFAULT }\n}\n}\n", 3, "`..`");
        refused("verus! {\npub fn plan() -> Plan {\n    Plan { v: format!(\"x\") }\n}\n}\n", 3, "the macro `format!`");
        refused("verus! {\npub fn plan() -> Plan {\n    let p = Plan { n: 1 };\n    p\n}\n}\n", 3, "`let`");
        refused("verus! {\npub fn plan() -> Plan {\n    proof { assert(true); }\n    Plan { n: 1 }\n}\n}\n", 3, "`proof`");
        refused("verus! {\n#[verifier::external_body]\npub fn plan() -> Plan { Plan { n: 1 } }\n}\n", 2, "`#`");
        refused("verus! {\npub fn plan(t: usize) -> Plan { Plan { n: 1 } }\n}\n", 2, "takes no parameter");
        refused("verus! {\npub fn plan() -> (r: Plan)\n    ensures r.n == 1,\n{ Plan { n: 1 } }\n}\n", 2, "in the return type");
        refused("verus! {\npub fn plan() -> Plan { Plan { n: 1 } }\nfn helper() -> u64 { 1 }\n}\n", 3, "a plan file holds only");
        refused("verus! {\npub fn plan() -> Plan { Plan { n: 1 } }\npub fn plan() -> Plan { Plan { n: 2 } }\n}\n", 0, "exactly one `pub fn plan()`, not 2");
        refused("use super::Plan;\n", 0, "not 0");
        refused("const N: usize = 3;\npub fn plan() -> Plan { Plan { n: N } }\n", 1, "`const`");
        // Comments are not code.
        assert_eq!(scan_plan_source("p.rs", "// if loop let \"text\"\npub fn plan() -> Plan { /* sorted_by(2) */ Plan { n: 1 } }\n"), vec![]);
    }

    /// The rule set of a run of several workloads: the stage rules over every member's names and
    /// constants, plus R3-R5, recorded with the default module and the plans' place; every other rule set is unchanged.
    #[test]
    fn member_rule_sets_add_the_family_rules() {
        let names = SchemaNames::from_names(["ax_owner"], ["ow_id", "value"]);
        let members = EngineRuleSet::members_with_names(&["tpch", "anyschema"], templates(), names.clone());
        let stage = EngineRuleSet::stage_with_names(&["tpch", "anyschema"], templates(), names);
        assert!(members.is_members() && members.is_stage() && !stage.is_members());
        assert_eq!(members.rules().iter().map(|r| r.id).collect::<Vec<_>>()[..4], stage.rules().iter().map(|r| r.id).collect::<Vec<_>>()[..]);
        assert_eq!(members.rules().iter().skip(4).map(|r| r.id).collect::<Vec<_>>(), ["storage_family_required", "plan_is_data", "workload_module_scope"]);
        let record = members.record();
        assert_eq!(record["families"]["rules"], json!(["storage_family_required", "plan_is_data", "workload_module_scope"]));
        assert_eq!((record["families"]["default_module"].as_str(), record["stage"]["workloads"][1].as_str()), (Some(DEFAULT_MODULE_DIRECTORY), Some("anyschema")));
        assert!(stage.record().get("families").is_none(), "a stage run's record is as before");
        // The agent scans are the stage run's.
        let text = "verus! { fn f() -> u64 { let ow_id = 1; ow_id } }";
        assert_eq!(members.scan_agent_source("agent/mod.rs", text), stage.scan_agent_source("agent/mod.rs", text));
    }
}
