// SQLSpec page data: the SQLSpec book, generated from the Verus source in src/gendb/sqlspec. The chapters and
// sections are set below (BOOK); every definition, constructor and match arm the page shows is cut from the source
// at build time, verbatim. Checks:
//  - the source is read whole: the modules `spec.rs` declares, every line of each file inside an item, a blank or a
//    comment line, or (outside `verus!`) a module comment, `use` or `pub mod` line;
//  - every definition of `spec` (proof lemmas aside) is shown whole in exactly one section, names are unique, and
//    every constructor and match arm named here is found exactly once;
//  - every shown item equals its pin (PINS: SHA-1 of its source text). A changed item fails the build until its new
//    text is read and its pin updated: `node docs/build/pages/sqlspec.mjs --pins` prints the current pins;
//  - the only text left out is OMIT, internal notes in comments: each entry matches exactly once, in a comment;
//  - the pictures' boxes are the constructors of the source, each linked to an existing section;
//  - the two sentences of the page are claims with their source in the README, GUIDE.md, the paper
//    and claim.rs.
import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import { fileURLToPath, pathToFileURL } from "node:url";

const SRC = "src/gendb/sqlspec";
const README = "README.md", GUIDE = "GUIDE.md", CLAIM = "src/gendb/verification/src/obligations/claim.rs";
const SQLSPEC = "sections/03-sqlspec.tex";
/** Sorts of the AST: a box of a syntax picture lists the sorts its fields hold ("[Expr]" for a sequence). */
const AST_SORTS = ["Query", "Pred", "Expr", "Agg", "Literal", "ScalarFn", "OrderKey"];

// ------------------------------------------------------------------------------------------------ the book
// A section: [id, title, { syntax, meaning, typing, wf, capacity }]. An entry is a definition's name (shown whole;
// this section is its home), `Enum::Variant` (one constructor of an enum), or `fn@Pattern` (one arm of the
// function's top-level match). A picture: `tree` of an enum's constructors (box text: `sorts` = the AST sorts of its
// fields, `fields` = its field types, `code` = the first `code` of its doc comment, `sqlstate`), or `pipeline` of a
// struct's fields. Box links: `links` (constructor -> section), else the section that shows the constructor under
// Syntax; with `raises`, a linked section must show code that gives that constructor.
const BOOK = [
  {
    id: "values", title: "Values",
    picture: { kind: "tree", enum: "Val", root: "values-all", text: "fields",
      links: { Null: "values-all", Bool: "values-all", Int: "integers", Num: "numeric", Date: "dates", Ts: "dates", Text: "text" } },
    sections: [
      ["values-all", "SQL values", { syntax: ["Literal::Null", "Literal::Bool"], meaning: ["Val", "Row", "Relation", "Database"] }],
      ["integers", "Integers", { syntax: ["Literal::Int", "IntKind"], meaning: ["int_in_range", "int_result", "int4_min", "int4_max", "int8_min", "int8_max"] }],
      ["numeric", "Numeric", { syntax: ["Literal::Num"], meaning: ["num_in_range", "num_result", "num_add_coeff", "num_sub_coeff", "num_cmp", "pow10", "align", "max_nat", "abs", "sign", "decimal_digits", "numeric_int_digits_max", "numeric_dscale_max", "numeric_max_precision"] }],
      ["dates", "Dates, timestamps", { syntax: ["Literal::Date"], meaning: ["date_from_civil", "civil_from_date", "date_valid", "ts_valid", "ts_result", "date_to_ts", "date_as_usecs", "valid_ymd", "is_leap", "days_in_month", "unix_days_from_civil", "civil_from_unix_days", "usecs_per_day", "USECS_PER_DAY", "postgres_epoch_jdate", "unix_to_postgres_days", "date_min", "date_end", "timestamp_end_date", "timestamp_min", "timestamp_end"] }],
      ["text", "Text", { syntax: ["Literal::Text"], meaning: ["lex_cmp", "chars", "is_cont", "concat", "char_length_max"] }],
    ],
  },
  {
    id: "types", title: "Types",
    picture: { kind: "tree", enum: "SqlType", root: "declared-types", text: "code",
      links: { Bool: "values-all", Int4: "integers", Int8: "integers", Numeric: "numeric", Date: "dates", Timestamp: "dates", Text: "text", Varchar: "text", Bpchar: "text" } },
    sections: [
      ["declared-types", "Declared types", { syntax: ["SqlType", "Column"], meaning: ["scalar_ty_of", "col_ty_of"], wf: ["sql_type_wf", "columns_wf"] }],
      ["static-types", "Static types", { syntax: ["ScalarTy", "ColTy"], typing: ["nn", "family", "kind_accepts", "scale_of"] }],
      ["schemas", "Schemas", { syntax: ["TableSchema", "Schema"], wf: ["schema_wf", "tables_wf"] }],
      ["checked-statements", "Checked statements", { typing: ["wf_ordered", "keys_in_range"] }],
      ["valid-databases", "Valid databases", { meaning: ["db_wf", "row_in_table", "value_in_column", "text_ok", "utf8_chars"] }],
    ],
  },
  {
    id: "constraints", title: "Constraints",
    picture: { kind: "tree", enum: "Constraint", root: "constraints-all", text: "code",
      links: { Key: "keys", ForeignKey: "foreign-keys", Check: "check" } },
    sections: [
      ["constraints-all", "Declared constraints", { syntax: ["Constraint"], meaning: ["constraints_hold", "constraint_holds"], wf: ["constraints_wf", "tables_constraints_wf", "table_constraints_wf", "constraint_wf", "primary_keys"] }],
      ["keys", "Keys", { syntax: ["Constraint::Key"], meaning: ["key_holds", "key_collides", "key_of", "has_null", "all_null"], wf: ["cols_in_range", "cols_distinct", "cols_not_null", "nat_in"] }],
      ["foreign-keys", "Foreign keys", { syntax: ["Constraint::ForeignKey"], meaning: ["fk_holds", "fk_row_holds", "key_matches"], wf: ["has_key_on", "cols_subset", "fk_types_ok", "fk_col_types_ok"] }],
      ["check", "CHECK", { syntax: ["Constraint::Check"], meaning: ["check_holds", "check_row_holds"] }],
    ],
  },
  {
    id: "expressions", title: "Expressions",
    picture: { kind: "tree", enum: "Expr", root: "expr-syntax", text: "sorts", nest: { Call: "ScalarFn" } },
    sections: [
      ["expr-syntax", "Syntax", { syntax: ["Expr"] }],
      ["expr-eval", "Evaluation, typing", { meaning: ["eval_expr", "eval_exprs", "expr_results"], typing: ["type_expr", "type_exprs"] }],
      ["columns", "Columns", { syntax: ["Expr::Col"], meaning: ["eval_expr@Expr::Col"], typing: ["type_expr@Expr::Col"] }],
      ["constants", "Constants", { syntax: ["Expr::Lit", "Literal"], meaning: ["eval_expr@Expr::Lit", "lit_val"], typing: ["type_expr@Expr::Lit", "type_lit"] }],
      ["arithmetic", "Arithmetic", { syntax: ["Expr::Neg", "Expr::Arith", "ArithOp", "NumKind"], meaning: ["eval_expr@Expr::Neg", "eval_expr@Expr::Arith", "arith", "neg", "int_arith", "num_arith", "int_kind_of"], typing: ["type_expr@Expr::Neg", "type_expr@Expr::Arith", "arith_ty"] }],
      ["division", "Division", { syntax: ["ScalarFn::DivInt4", "ScalarFn::DivInt8", "ScalarFn::DivNumeric"], meaning: ["apply_div", "int_div", "trunc_div", "num_div", "num_div_coeff", "div_scale", "div_round", "nbase_weight", "nbase_first_digit", "numeric_min_sig_digits", "numeric_max_display_scale", "dec_digits"], typing: ["type_div"], capacity: ["fits_div", "num_div_fits", "in_u128", "in_i128"] }],
      ["cast", "CAST", { syntax: ["Expr::Cast", "CastOp"], meaning: ["eval_expr@Expr::Cast", "cast"], typing: ["type_expr@Expr::Cast", "cast_ty"] }],
      ["case", "CASE", { syntax: ["Expr::If"], meaning: ["eval_expr@Expr::If"], typing: ["type_expr@Expr::If", "if_ty", "same_shape"] }],
      ["calls", "Function calls", { syntax: ["Expr::Call", "ScalarFn"], meaning: ["eval_expr@Expr::Call", "apply_fn"], typing: ["type_expr@Expr::Call", "type_fn"], capacity: ["fits_fn"] }],
      ["like", "LIKE", { syntax: ["ScalarFn::Like", "ScalarFn::PadBpchar"], meaning: ["apply_like", "like_value", "LikeTok", "like_tokens", "LikeRes", "like_mt", "like_any", "like_scan", "like_end", "like_std", "escape_of", "pct", "underscore", "apply_pad", "spaces"], typing: ["type_like", "type_pad"], capacity: ["fits_like", "fits_pad"] }],
      ["substring", "SUBSTRING", { syntax: ["ScalarFn::Substring2", "ScalarFn::Substring3"], meaning: ["apply_substring", "substring_value", "char_range", "substring_end", "substring_arity"], typing: ["type_substring"], capacity: ["fits_substring"] }],
      ["datetime", "Dates, EXTRACT", { syntax: ["Expr::AddInterval", "ScalarFn::ExtractYear", "ScalarFn::ExtractMonth", "ScalarFn::ExtractDay"], meaning: ["eval_expr@Expr::AddInterval", "add_interval", "ts_add_interval", "ts_add_months", "apply_extract", "extract_field"], typing: ["type_expr@Expr::AddInterval", "type_extract"], capacity: ["fits_extract"] }],
      ["subqueries", "Scalar subqueries", { syntax: ["Expr::Subquery"], meaning: ["eval_expr@Expr::Subquery", "subquery_value", "first_col"], typing: ["type_expr@Expr::Subquery", "subquery_ty"] }],
    ],
  },
  {
    id: "predicates", title: "Predicates",
    picture: { kind: "tree", enum: "Pred", root: "pred-syntax", text: "sorts", notes: [{ label: "Truth", enum: "Truth", to: "three-valued" }] },
    sections: [
      ["pred-syntax", "Syntax", { syntax: ["Pred"] }],
      ["pred-eval", "Evaluation, typing", { meaning: ["eval_pred"], typing: ["type_pred"] }],
      ["comparisons", "Comparisons", { syntax: ["Pred::Cmp", "CmpOp"], meaning: ["eval_pred@Pred::Cmp", "cmp_truth", "compare", "cmp_holds"], typing: ["type_pred@Pred::Cmp"] }],
      ["three-valued", "Three-valued logic", { syntax: ["Pred::And", "Pred::Or", "Pred::Not", "Pred::OfBool"], meaning: ["Truth", "truth_and", "truth_or", "truth_not", "truth_of", "truth_of_val", "eval_pred@Pred::And", "eval_pred@Pred::Or", "eval_pred@Pred::Not", "eval_pred@Pred::OfBool"], typing: ["type_pred@Pred::And", "type_pred@Pred::Or", "type_pred@Pred::Not", "type_pred@Pred::OfBool"] }],
      ["is-null", "IS NULL", { syntax: ["Pred::IsNull"], meaning: ["eval_pred@Pred::IsNull"], typing: ["type_pred@Pred::IsNull"] }],
      ["exists", "EXISTS", { syntax: ["Pred::Exists"], meaning: ["eval_pred@Pred::Exists"], typing: ["type_pred@Pred::Exists"] }],
      ["in-any", "IN, ANY", { syntax: ["Pred::AnyCmp"], meaning: ["eval_pred@Pred::AnyCmp", "any_cmp_truth"], typing: ["type_pred@Pred::AnyCmp", "any_cmp_ok"] }],
    ],
  },
  {
    id: "operators", title: "Operators",
    picture: { kind: "tree", enum: "Query", root: "query-syntax", text: "sorts" },
    sections: [
      ["query-syntax", "Syntax", { syntax: ["Query"] }],
      ["query-eval", "Evaluation, typing", { meaning: ["eval_query"], typing: ["type_query"] }],
      ["table", "Table scan", { syntax: ["Query::Table"], meaning: ["eval_query@Query::Table"], typing: ["type_query@Query::Table", "table_tys"] }],
      ["filter", "Filter", { syntax: ["Query::Filter"], meaning: ["eval_query@Query::Filter", "keep_true"], typing: ["type_query@Query::Filter"] }],
      ["projection", "Projection", { syntax: ["Query::Project"], meaning: ["eval_query@Query::Project"], typing: ["type_query@Query::Project"] }],
      ["joins", "Joins", { syntax: ["Query::Product"], meaning: ["eval_query@Query::Product", "product_rows"], typing: ["type_query@Query::Product"] }],
      ["left-join", "LEFT JOIN", { syntax: ["Query::LeftJoin"], meaning: ["eval_query@Query::LeftJoin", "left_join_rows", "left_join_one", "null_row", "query_arity"], typing: ["type_query@Query::LeftJoin", "nullable_all"] }],
      ["distinct", "DISTINCT", { syntax: ["Query::Distinct"], meaning: ["eval_query@Query::Distinct", "distinct_query_rows", "distinct_rows", "has_not_distinct", "row_not_distinct", "val_not_distinct"], typing: ["type_query@Query::Distinct", "distinct_ty"] }],
    ],
  },
  {
    id: "aggregates", title: "Aggregates",
    picture: { kind: "tree", enum: "Agg", root: "agg-syntax", text: "sorts", notes: [{ label: "Used in", usedBy: "Agg", to: "aggregation" }] },
    sections: [
      ["agg-syntax", "Syntax", { syntax: ["Agg"] }],
      ["aggregation", "Aggregation", { syntax: ["Query::Aggregate"], meaning: ["eval_query@Query::Aggregate", "agg_row", "agg_value", "column", "agg_args", "agg_arg", "agg_arg_results"], typing: ["type_query@Query::Aggregate", "type_agg", "type_aggs"] }],
      ["group-by", "GROUP BY", { syntax: ["Query::GroupBy"], meaning: ["eval_query@Query::GroupBy", "group_rows", "group_members", "group_input"], typing: ["type_query@Query::GroupBy"] }],
      ["count", "COUNT", { syntax: ["Agg::CountStar", "Agg::Count"], meaning: ["agg_value@Agg::CountStar", "agg_value@Agg::Count", "count_non_null"], typing: ["type_agg@Agg::CountStar", "type_agg@Agg::Count"] }],
      ["sum", "SUM", { syntax: ["Agg::Sum"], meaning: ["agg_value@Agg::Sum", "int_sum", "num_sum", "all_of_kind"], typing: ["type_agg@Agg::Sum"] }],
      ["avg", "AVG", { syntax: ["Agg::Avg"], meaning: ["agg_value@Agg::Avg", "avg_value", "avg_sum"], typing: ["type_agg@Agg::Avg", "avg_ty"], capacity: ["fits_avg"] }],
      ["min-max", "MIN, MAX", { syntax: ["Agg::Min", "Agg::Max"], meaning: ["agg_value@Agg::Min", "agg_value@Agg::Max", "min_value", "max_value", "extremum", "extremum_step", "extremum_better"], typing: ["type_agg@Agg::Min", "type_agg@Agg::Max", "minmax_ty"] }],
      ["distinct-aggs", "DISTINCT aggregates", { syntax: ["Agg::DistinctAgg"], meaning: ["agg_value@Agg::DistinctAgg", "distinct_vals", "has_val_not_distinct"], typing: ["type_agg@Agg::DistinctAgg", "distinct_agg_ty"] }],
    ],
  },
  {
    id: "ordering", title: "Ordering",
    picture: { kind: "pipeline", struct: "OrderedQuery", root: "statement", steps: [["body", "denote_body", "statement"], ["keys", "sorted_by", "order-by"], ["offset", "slice_rows", "limit-offset"], ["limit", "slice_rows", "limit-offset"]] },
    sections: [
      ["statement", "Statement", { syntax: ["OrderedQuery"], meaning: ["denote_body"] }],
      ["order-by", "ORDER BY", { syntax: ["OrderKey"], meaning: ["sorted_by", "keys_cmp", "key_cmp"] }],
      ["limit-offset", "OFFSET, LIMIT", { meaning: ["slice_rows"] }],
    ],
  },
  {
    id: "outcomes", title: "Outcomes",
    picture: { kind: "tree", enum: "SqlError", root: "sql-errors", text: "sqlstate", raises: true,
      links: { NumericValueOutOfRange: "integers", DatetimeFieldOverflow: "dates", DivisionByZero: "division", CardinalityViolation: "subqueries", SubstringError: "substring", InvalidEscapeSequence: "like", InvalidEscapeCharacter: "sql-errors", TypeError: "sql-errors" } },
    sections: [
      ["sql-errors", "SQL errors", { meaning: ["SqlError"] }],
      ["first-error", "First error", { meaning: ["collect"] }],
      ["allowed", "Allowed outcomes", { meaning: ["ordered_ok", "denote_top", "sort_rows", "insert_sorted"] }],
    ],
  },
];
/** Group keys of a section, in the order shown, with their labels. */
const GROUPS = [["syntax", "Syntax"], ["meaning", "Meaning"], ["typing", "Typing"], ["wf", "Well-formed"], ["capacity", "Capacity"]];

// ------------------------------------------------------------------------------------------------ omitted notes
// Internal notes in comments that the page leaves out; code is never left out. `line`: the exact text (indentation
// aside) of one comment line of the spec source; the page drops that line and shows an elision mark in its place, the
// other lines keeping their source numbers. `doc` (with `def`): an exact part of that definition's doc comment (white
// space aside), cut from the doc text shown. Each entry must match exactly once, or the build fails.
export const OMIT = [
  { line: "// Deviation D3 (as for AVG, `spec::aggs::avg`; recorded, not tested): PostgreSQL's transition" },
  { line: "// `int4_sum` adds in int64 without an overflow check (numeric.c:6676-6722 at REL_18_3), so a sum" },
  { line: "// past int64 wraps, which needs at least 2^32 rows; this sum is exact, and only its final value is" },
  { line: "// range-checked as int8 (22003)." },
  { def: "utf8_chars", doc: "The range test is written out rather than calling `is_cont`: the two are equal, but admitted proofs were checked against this form, and with the call one of them exceeds the SMT resource limit." },
  { def: "fk_col_types_ok", doc: "(PostgreSQL 18.3 probe)" },
];
/** A doc part of OMIT as a pattern: the white space before it, then its words with any white space between them. */
export const omitPattern = (doc) => new RegExp(`\\s*${doc.trim().split(/\s+/).map((w) => w.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("\\s+")}`, "g");

// ------------------------------------------------------------------------------------------------ pins
// The first 10 hex digits of the SHA-1 of each definition's source text (its doc comment to its last line), as
// read for this page. `node docs/build/pages/sqlspec.mjs --pins` prints the current values.
const PINS = `
int4_min 2cc4f20627  int4_max 6902395191  int8_min cc37d51dd6  int8_max ce61b91b4c
numeric_int_digits_max be7ef00908  numeric_dscale_max 5282370072  numeric_max_precision 5f402565c2  char_length_max 400462a90e
USECS_PER_DAY 27666ffe6b  postgres_epoch_jdate 2fa8e1fd49  unix_to_postgres_days a2f6132e75  date_min 573f8aa4da
date_end e2bf544b84  timestamp_end_date 61a17b03bd  timestamp_min dcb3ccdb7d  timestamp_end a0150f54b1
SqlType fa2b1e8404  Column e52f1537e6  Constraint abe1c5ee52  TableSchema 96801b8024
Schema 076c7e6694  ScalarTy 21cc29bd7a  ColTy 7c93a84312  scalar_ty_of 6bb9d66233
col_ty_of 69e53b3e6d  sql_type_wf 6918c79f42  columns_wf 854b75b9a8  tables_wf eb4898d85d
schema_wf f827ddf3cf  Val c9405b7e57  Row ad46618504  Relation ef62f07212
SqlError 9b13f04236  Truth 9d0a183c6d  truth_of b2d173daf5  truth_and 39e54f5daa
truth_or f8c92a21bc  truth_not 0673e0929a  Database f3be789488  IntKind 8fef7fd2b2
int_in_range 474b16d390  int_result 55f8e44d41  pow10 6611899dc4  align 06e55544cf
max_nat 195439b16b  abs df0cf5b882  sign 5500301bd3  decimal_digits 54ce66cd1e
num_in_range a2da609f2b  num_result 4f3c40a157  num_add_coeff b61581023f  num_sub_coeff 69730239e8
num_cmp c1cf8c889c  usecs_per_day e52c76043e  is_leap b445758e03  days_in_month 4f9bfa403a
valid_ymd 77d0ae6cce  unix_days_from_civil 17f2ee514b  civil_from_unix_days 4b470bc050  date_from_civil acd8336de5
civil_from_date 2da70a5904  date_valid 83659c2a2f  ts_valid 373ff97007  ts_result 8a77cd62d6
date_to_ts 6e36c1711d  date_as_usecs d63319c719  ts_add_months 413e5bd618  ts_add_interval 471f9ba6ac
lex_cmp 46bf45f5c8  is_cont f1f0d7c359  chars 8d2510b7c3  concat ef60cd4f37
ArithOp ce1ee9b6e1  NumKind bb0c4b961e  CmpOp daaf162974  CastOp 9dbabd8ada
int_kind_of 2276038b21  int_arith 3e483228d7  num_arith 6bdeb237b0  arith f12ad3310e
neg 2283250336  cast 53a85c746e  add_interval c5bf388540  compare 64c7a380ba
cmp_holds 98f74dab3b  cmp_truth 3a76bf8661  truth_of_val 6ab0b69506  val_not_distinct 4a2335db1e
row_not_distinct 45c4d8b16d  has_not_distinct 522dca5bfe  distinct_rows 30e6e3f9bf  has_val_not_distinct 04d4f04854
distinct_vals d2dd556e76  type_fn 1c0a4d2166  apply_fn 65df6aba3d  fits_fn 6dc18252a7
trunc_div fcb1d5c317  int_div 834c934c99  numeric_min_sig_digits b1c4bbae50  numeric_max_display_scale 92d5e11e65
dec_digits e63ecc8c39  nbase_weight f89a9d0fc9  nbase_first_digit 69f28afe63  div_scale 8e81b15846
div_round 56032f1a35  num_div_coeff ad1ac98d84  num_div d2da64bbf5  in_u128 bc087a2e07
in_i128 5134d7a6a4  num_div_fits 104283256a  type_div 1bd1647db5  apply_div 13b04599e8
fits_div 21ff4247a4  LikeTok 048a556210  LikeRes 47077e8b33  pct 997ab636ba
underscore e218b46428  like_tokens b43ba75e8d  like_mt 7bd7a05571  like_any 25458d7ee9
like_scan c8c1f13bd2  like_end e5636209e1  like_std e47773d051  escape_of d9d9adec7d
like_value dc0accfcf2  type_like 67d3ed01c4  apply_like 66fac11d76  fits_like 94c0bd103c
substring_end 1236ecbc74  char_range 9fd86765f6  substring_value 2b14faa7a6  substring_arity ac3efed936
type_substring 9ebf23c993  apply_substring 7053ffe4e0  fits_substring e5599849f5  extract_field 8d5e0e8ce5
type_extract a4ebdd3695  apply_extract 7e9bb238f6  fits_extract ea5af972cb  spaces 5ca7301b22
type_pad 0cd89d9c1d  apply_pad 2c566157fc  fits_pad 13614db6ad  avg_ty 4c11decb2e
avg_sum 1195fbe044  avg_value f6fbcf1545  fits_avg b4d1c873cc  minmax_ty 3f9956e3e5
extremum_better 0c510f5273  extremum_step d6fee63562  extremum 91ec18e404  min_value 1fe2384769
max_value bb7ccfe67c  distinct_agg_ty 5f44af903e  Literal 3a6e5a081e  ScalarFn 2e082637ad
Expr 07874cd6d1  Pred f1a4b782c2  Agg 1d6de97557  Query 62a6bfef1a
OrderKey be5e68bace  OrderedQuery aeff67cd55  collect 6adc7f82a8  keep_true 9640bfc51c
product_rows b45c3429ab  null_row 81a548935a  left_join_one 65edeffdcf  left_join_rows 886805bdb7
column f61c15f7bb  count_non_null 00af1c01a8  int_sum 1575a75976  num_sum eb87558190
all_of_kind 1f21f40443  agg_value 3b1a8b589d  agg_row 7d27f6bf9a  group_members bda7784489
group_rows 4618218047  lit_val 3284adf7c8  eval_expr 1ff0c54ff7  first_col 115038f070
subquery_value 29e063c07b  any_cmp_truth 5dc257c4b5  distinct_query_rows 2b6ffe6231  expr_results 71263b43bf
eval_exprs 0b4a866d03  agg_arg 8396c37c33  agg_arg_results 0cfaa1e7ab  agg_args 47af78dd94
group_input 578bc32a1f  query_arity 081bc13da6  eval_pred 1e7f7b593f  eval_query ca0cd58dc4
key_cmp ce06670f26  keys_cmp 0ce7b9bcfd  sorted_by d4ad542552  slice_rows 1b051696e1
denote_body d30715b94e  ordered_ok 1551bae10d  insert_sorted 08594afefe  sort_rows eeec75c939
denote_top 26e6a16abf  nn 48ccdab1f9  type_lit 15979eab65  kind_accepts 39bb264e73
scale_of 0cd647dce7  arith_ty b944d935e3  cast_ty 1a58a4c31c  family a311abd41f
same_shape 47ac153544  if_ty 34b0425f72  subquery_ty 27532b4872  any_cmp_ok 0608159dcb
distinct_ty 67c8c96512  table_tys e42fb5ac55  nullable_all 90ca744a2f  type_expr 3623ceaaa8
type_exprs dfe73a76ba  type_agg 6641b4eec0  type_aggs fad8386478  type_pred 10edb61d96
type_query db2e89fc7e  keys_in_range c9a2932dc5  wf_ordered a7e3574fd1  value_in_column e4d5b275b1
text_ok 2102e614c9  utf8_chars 6d40c31a81  row_in_table 3d8c09ab51  db_wf 3b23c8a7af
nat_in e3d4d32e52  cols_in_range e9ee8c7f54  cols_distinct 133ec70460  cols_not_null 447636bfb7
cols_subset bb14e953bc  has_key_on 1a013b2200  primary_keys 1c721a7f9b  fk_col_types_ok 7212767760
fk_types_ok 342f18fe99  constraint_wf a20d4b05d3  table_constraints_wf 1488752dd6  tables_constraints_wf 472513187c
constraints_wf 8b66deb1d9  key_of a3f4e4caff  has_null c48da2d524  all_null 4907c72d09
key_collides 599bb75e0b  key_holds f023e00b07  key_matches bc35c7739d  fk_row_holds f245034ed0
fk_holds af1c4ea539  check_row_holds 13506d5637  check_holds 180846c35c  constraint_holds 1d70a333ea
constraints_hold 4dfa71aec9
`;

// ------------------------------------------------------------------------------------------------ the source
const pin = (text) => createHash("sha1").update(text).digest("hex").slice(0, 10);
const indentOf = (l) => l.length - l.trimStart().length;
const HEADER = /^pub (?:(?:open|closed) )?(?:(spec|proof) )?fn ([A-Za-z_]\w*)|^pub (enum|struct|type|const) ([A-Za-z_]\w*)/;
const OUTSIDE = /^(\/\/!.*|use [\w:{}*, ]+;|pub mod \w+;|#!\[.*\]|\s*)$/;

/** Brace depth change of one line, outside `//` comments, strings and character literals. */
function depthOf(line) {
  let d = 0;
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (c === "/" && line[i + 1] === "/") break;
    if (c === '"') { i++; while (i < line.length && line[i] !== '"') i += line[i] === "\\" ? 2 : 1; continue; }
    if (c === "'" && line[i + 2] === "'") { i += 2; continue; }
    if (c === "{") d++;
    else if (c === "}") d--;
  }
  return d;
}

/** The modules of `spec` and their files: `spec.rs` names them; a module with submodules names those. */
function specFiles(read, exists) {
  const mods = (text) => [...text.matchAll(/^pub mod (\w+);$/gm)].map((m) => m[1]);
  const files = [];
  for (const m of mods(read(`${SRC}/spec.rs`))) {
    const where = [`syntax/${m}.rs`, `semantics/${m}.rs`, `semantics/${m}/mod.rs`].filter((f) => exists(`${SRC}/${f}`));
    if (where.length !== 1) throw new Error(`module spec::${m}: ${where.length} files (${where.join(", ") || "none"})`);
    files.push({ rel: where[0], module: `spec::${m}` });
    if (where[0].endsWith("/mod.rs")) {
      for (const s of mods(read(`${SRC}/${where[0]}`))) {
        const rel = `semantics/${m}/${s}.rs`;
        if (!exists(`${SRC}/${rel}`)) throw new Error(`module spec::${m}::${s}: no ${rel}`);
        files.push({ rel, module: `spec::${m}::${s}` });
      }
    }
  }
  return files;
}

/** Items of one file: every line between `verus! {` and `} // verus!` is in an item, blank or a `//` comment. */
function parseFile(text, rel, module) {
  const lines = text.split("\n");
  const open = lines.findIndex((l) => /^verus!\s*\{\s*$/.test(l));
  const close = lines.findLastIndex((l) => /^\}\s*\/\/\s*verus!\s*$/.test(l));
  const outside = lines.filter((l, i) => (open < 0 || i < open || i > close) && !OUTSIDE.test(l));
  if (outside.length) throw new Error(`${rel}: unexpected line outside verus!: ${outside[0]}`);
  const items = [];
  if (open < 0) return items;
  for (let i = open + 1; i < close;) {
    const l = lines[i];
    if (/^\s*$/.test(l) || /^\/\/(?!\/)/.test(l)) { i++; continue; }
    const start = i;
    while (i < close && /^\/\/\//.test(lines[i])) i++;
    const doc = lines.slice(start, i).map((x) => x.replace(/^\/\/\/ ?/, ""));
    const codeStart = i;
    while (i < close && /^#\[/.test(lines[i])) i++;
    const m = HEADER.exec(lines[i] || "");
    if (!m) throw new Error(`${rel}:${i + 1}: not an item: ${lines[i]}`);
    const kind = m[3] || (m[1] === "proof" ? "proof" : m[1] === "spec" ? "spec fn" : "fn");
    const name = m[2] || m[4];
    let end = i, depth = 0, opened = false;
    for (;; end++) {
      if (end >= close) throw new Error(`${rel}:${i + 1}: ${name} has no end`);
      const d = depthOf(lines[end]);
      opened ||= /\{/.test(lines[end].replace(/\/\/.*$/, ""));
      depth += d;
      if (kind === "type" || kind === "const") { if (depth === 0 && /;\s*$/.test(lines[end])) break; continue; }
      if (opened && depth === 0 && (end === i || /^\}/.test(lines[end]))) break;
    }
    const src = lines.slice(start, end + 1).join("\n");
    items.push({
      name, kind, module, file: rel, id: `${module}::${name}`,
      line: start + 1, codeLine: codeStart + 1,
      doc: doc.join("\n"), code: lines.slice(codeStart, end + 1).join("\n"),
      pin: pin(src), lines: lines.slice(codeStart, end + 1), head: i - codeStart,
    });
    i = end + 1;
  }
  return items;
}

/** Variants of an enum (or fields of a struct) at indent 4: name, doc, its verbatim lines and first line number. */
function members(item) {
  const out = [];
  const L = item.lines;
  for (let i = item.head + 1; i < L.length - 1;) {
    if (/^\s*$/.test(L[i])) { i++; continue; }
    const start = i;
    while (/^ {4}\/\/\//.test(L[i])) i++;
    const doc = L.slice(start, i).map((x) => x.replace(/^ {4}\/\/\/ ?/, ""));
    const codeStart = i;
    while (/^ {4}#\[/.test(L[i])) i++;
    const m = /^ {4}(?:pub )?([A-Za-z_]\w*)/.exec(L[i]);
    if (!m) throw new Error(`${item.file}:${item.codeLine + i}: not a member of ${item.name}: ${L[i]}`);
    let end = i, depth = 0;
    for (;; end++) {
      depth += depthOf(L[end]) + (L[end].replace(/\/\/.*$/, "").match(/\(/g) || []).length - (L[end].replace(/\/\/.*$/, "").match(/\)/g) || []).length;
      if (depth === 0 || end >= L.length - 2) break;
    }
    const code = L.slice(codeStart, end + 1).join("\n");
    out.push({ name: m[1], doc: doc.join("\n"), code, line: item.codeLine + codeStart, fields: fieldsOf(code.replace(/^\s*#\[.*$/gm, "").trim(), m[1]) });
    i = end + 1;
  }
  return out;
}

/** Types of a member's fields: `Name { a: T, b: U },` -> [{name a, ty T}, ...]; `Name(T, U),` -> [{ty T}, ...]; a
 *  struct field `pub a: T,` -> [{name a, ty T}]. */
function fieldsOf(code, name) {
  const split = (s) => {
    const parts = [];
    let depth = 0, cur = "";
    for (const c of s) {
      if ("<({[".includes(c)) depth++;
      if (">)}]".includes(c)) depth--;
      if (c === "," && depth === 0) { parts.push(cur.trim()); cur = ""; } else cur += c;
    }
    if (cur.trim()) parts.push(cur.trim());
    return parts;
  };
  const body = code.replace(/^(pub )?\w+\s*/, "").replace(/,\s*$/, "").trim();
  if (body.startsWith(":")) return [{ name, ty: body.slice(1).trim() }];
  if (body.startsWith("{")) return split(body.slice(1, -1)).map((f) => ({ name: f.split(":")[0].trim(), ty: f.split(":").slice(1).join(":").trim() }));
  if (body.startsWith("(")) return split(body.slice(1, -1)).map((ty) => ({ name: null, ty }));
  return [];
}

/** Arms of a function's top-level `match` (the `match ... {` line at indent 4; arms at indent 8). */
function arms(item) {
  const L = item.lines;
  const at = L.findIndex((l, i) => i > item.head && /^ {4}match .+\{$/.test(l));
  if (at < 0) return [];
  const out = [];
  let i = at + 1;
  while (i < L.length && !/^ {4}\}/.test(L[i])) {
    if (indentOf(L[i]) === 8 && !/^\s*[)\]}]|^\s*\/\//.test(L[i]) && L[i].includes("=>")) {
      const start = i;
      i++;
      while (i < L.length && !/^ {4}\}/.test(L[i]) && !(indentOf(L[i]) === 8 && !/^\s*[)\]}]/.test(L[i]))) i++;
      out.push({ pat: L[start].trim().split(" => ")[0], code: L.slice(start, i).join("\n"), line: item.codeLine + start });
    } else i++;
  }
  return out;
}

/** The first sentence of a doc comment, for previews: up to the first `.` or `:` outside brackets and `code`, not
 *  after an initial or "e.g"/"i.e"; else the whole text. */
function firstSentence(doc) {
  const t = doc.replace(/\s+/g, " ").trim();
  let depth = 0, code = false;
  for (let i = 0; i < t.length; i++) {
    const c = t[i];
    if (c === "`") code = !code;
    else if (code) continue;
    else if (c === "(" || c === "[") depth++;
    else if ((c === ")" || c === "]") && depth) depth--;
    else if (!depth && (c === "." || c === ":") && (i + 1 === t.length || t[i + 1] === " ") && !/(^|[\s(])([A-Z]|e\.g|i\.e)$/.test(t.slice(0, i))) return t.slice(0, i + 1);
  }
  return t;
}

/** All items of `spec`, read with `read(rel)` and `exists(rel)` (paths relative to the repository). */
export function readSpec(read, exists) {
  const files = specFiles(read, exists);
  const sources = new Map(files.map((f) => [f.rel, read(`${SRC}/${f.rel}`)]));
  const items = files.flatMap((f) => parseFile(sources.get(f.rel), f.rel, f.module));
  return { files, items, sources };
}

/** The pins of the current source, as the PINS block. */
export function currentPins(items) {
  const defs = items.filter((it) => it.kind !== "proof");
  const lines = [];
  for (let i = 0; i < defs.length; i += 4) lines.push(defs.slice(i, i + 4).map((it) => `${it.name} ${it.pin}`).join("  "));
  return `\n${lines.join("\n")}\n`;
}

// ------------------------------------------------------------------------------------------------ the build
export default function build(ctx) {
  const { check } = ctx;
  const { files, items, sources } = readSpec(ctx.read, (rel) => fs.existsSync(path.join(ctx.repo, rel)));
  check(files.length >= 20, `spec has its modules (${files.length} files)`);
  const defs = items.filter((it) => it.kind !== "proof");
  const byName = new Map();
  for (const it of defs) {
    check(!byName.has(it.name), `${it.name}: one definition of this name in spec (${byName.get(it.name)?.id || ""} ${it.id})`);
    byName.set(it.name, it);
  }
  const pins = new Map([...PINS.matchAll(/(\S+) ([0-9a-f]{10})/g)].map((m) => [m[1], m[2]]));

  // omitted notes: the comment lines to drop (file -> line numbers) and the doc comments to show cut
  const dropped = new Map(), usedDrops = new Set(), cutDocs = new Map();
  for (const o of OMIT) {
    if (o.line) {
      check(o.line.startsWith("//"), `omit "${o.line}": a comment line`);
      const hits = [...sources].flatMap(([rel, text]) => text.split("\n").flatMap((l, i) => (l.trim() === o.line ? [[rel, i + 1]] : [])));
      if (!check(hits.length === 1, `omit "${o.line}": matches exactly one line of the spec source (${hits.length})`)) continue;
      const [rel, n] = hits[0];
      if (!dropped.has(rel)) dropped.set(rel, new Set());
      dropped.get(rel).add(n);
    } else {
      const it = byName.get(o.def);
      if (!check(it, `omit in ${o.def}: a definition of spec`)) continue;
      const doc = cutDocs.get(o.def) ?? it.doc, re = omitPattern(o.doc);
      const n = (doc.match(re) || []).length;
      check(n === 1 && !omitPattern(o.doc).test(it.code), `omit "${o.doc}": matches exactly once in the doc comment of ${o.def}, and not its code (${n})`);
      if (n === 1) cutDocs.set(o.def, doc.replace(re, ""));
    }
  }
  const docOf = (it) => cutDocs.get(it.name) ?? it.doc;
  /** Code as shown: its source lines without the dropped ones; `omit` lists [first line, count] of each run dropped. */
  const shownCode = (file, first, code) => {
    const drop = dropped.get(file) || new Set(), out = [], omit = [];
    code.split("\n").forEach((l, k) => {
      const n = first + k, last = omit[omit.length - 1];
      if (!drop.has(n)) out.push(l);
      else {
        usedDrops.add(`${file}:${n}`);
        if (last && last[0] + last[1] === n) last[1]++; else omit.push([n, 1]);
      }
    });
    return omit.length ? { code: out.join("\n"), omit } : { code };
  };

  const home = new Map();         // definition name -> "chapter/section"
  const variantAt = new Map();    // "Enum::Variant" -> "chapter/section" (where it is shown under Syntax)
  const sectionIds = new Map();   // section id -> "chapter/section"
  for (const ch of BOOK) for (const [id] of ch.sections) {
    check(/^[a-z0-9]+(-[a-z0-9]+)*$/.test(id) && !sectionIds.has(id), `section ${id}: id is unique and usable in an address`);
    sectionIds.set(id, `${ch.id}/${id}`);
  }
  const words = (t) => t.split(/[\s,]+/).filter(Boolean).length;
  const changed = [];             // shown definitions whose source text differs from their pin

  /** One entry of a section -> a block of the page (or null after a failed check). */
  const block = (entry, at, group) => {
    const arm = entry.match(/^(\w+)@(.+)$/);
    const variant = entry.match(/^(\w+)::(\w+)$/);
    if (arm) {
      const it = byName.get(arm[1]);
      if (!check(it && it.kind === "spec fn", `${at}: ${arm[1]} is a spec function`)) return null;
      const hits = arms(it).filter((a) => new RegExp(`(^|[^\\w:])${arm[2]}\\b`).test(a.pat));
      if (!check(hits.length === 1, `${at}: ${arm[1]} has one match arm for ${arm[2]} (${hits.length})`)) return null;
      return { kind: "arm", name: entry, of: it.name, pat: arm[2], file: it.file, line: hits[0].line, ...shownCode(it.file, hits[0].line, hits[0].code) };
    }
    if (variant) {
      const it = byName.get(variant[1]);
      if (!check(it && it.kind === "enum", `${at}: ${variant[1]} is an enum`)) return null;
      const v = members(it).find((x) => x.name === variant[2]);
      if (!check(v, `${at}: ${variant[1]} has the constructor ${variant[2]}`)) return null;
      if (group === "syntax") {
        check(!variantAt.has(entry), `${entry}: shown under Syntax in one section (${variantAt.get(entry)}, ${at})`);
        variantAt.set(entry, at);
      }
      return { kind: "variant", name: entry, of: it.name, file: it.file, line: v.line, doc: v.doc, ...shownCode(it.file, v.line, v.code) };
    }
    const it = byName.get(entry);
    if (!check(it, `${at}: ${entry} is a definition of spec`)) return null;
    check(!home.has(entry), `${entry}: shown whole in one section (${home.get(entry)}, ${at})`);
    home.set(entry, at);
    if (!check(pins.get(entry) === it.pin, `${entry} (${SRC}/${it.file}:${it.line}) no longer matches its pin (pin ${pins.get(entry) || "none"}, now ${it.pin})`)) changed.push(entry);
    return { kind: "def", name: it.name, file: it.file, line: it.codeLine, doc: docOf(it), ...shownCode(it.file, it.codeLine, it.code) };
  };

  const chapters = BOOK.map((ch) => {
    check(words(ch.title) <= 3, `chapter ${ch.id}: short title`);
    return {
      id: ch.id, title: ch.title,
      sections: ch.sections.map(([id, title, groups]) => {
        const at = `${ch.id}/${id}`;
        check(words(title) <= 3, `section ${id}: title "${title}" has at most three words`);
        for (const k of Object.keys(groups)) check(GROUPS.some(([g]) => g === k), `section ${id}: known group ${k}`);
        const gs = GROUPS.filter(([k]) => groups[k]?.length).map(([k, label]) => ({ key: k, label, blocks: groups[k].map((e) => block(e, at, k)).filter(Boolean) }));
        check(gs.length > 0, `section ${id}: shows something`);
        return { id, title, groups: gs };
      }),
    };
  });

  check(!changed.length, `${changed.length} shown definitions changed in the source (${changed.join(", ")}): read them, then update PINS with the output of node docs/build/pages/sqlspec.mjs --pins`);
  // completeness: every definition shown whole once; every pin names a definition
  for (const it of defs) check(home.has(it.name), `${it.name} (${SRC}/${it.file}:${it.line}) is shown in a section`);
  for (const name of pins.keys()) check(byName.has(name), `pin ${name}: a definition of spec`);

  // pictures
  const sectionOfVariant = (en, v) => variantAt.get(`${en}::${v}`) || null;
  const sortsOf = (fields) => fields.flatMap((f) => {
    const s = AST_SORTS.find((x) => new RegExp(`\\b${x}\\b`).test(f.ty));
    return s ? [/\bSeq\b/.test(f.ty) ? `[${s}]` : s] : [];
  });
  const picture = (ch) => {
    const P = ch.picture, where = `picture of ${ch.id}`;
    const link = (sec, what) => {
      if (!check(sectionIds.has(sec), `${where}: ${what} links to section ${sec}`)) return null;
      return sectionIds.get(sec);
    };
    if (P.kind === "pipeline") {
      const it = byName.get(P.struct);
      if (!check(it?.kind === "struct", `${where}: ${P.struct} is a struct`)) return null;
      const fields = members(it);
      check(fields.every((f) => P.steps.some(([n]) => n === f.name)) && P.steps.length === fields.length, `${where}: every field of ${P.struct} is a step`);
      return {
        kind: "pipeline", root: { name: P.struct, to: link(P.root, P.struct) },
        steps: P.steps.map(([field, fn, sec]) => {
          const f = fields.find((x) => x.name === field);
          check(f && byName.get(fn)?.kind === "spec fn", `${where}: ${P.struct}.${field} and ${fn} exist`);
          check(home.get(fn) === sectionIds.get(sec), `${where}: ${fn} is shown in ${sec}`);
          return { name: field, sub: f ? f.fields[0].ty : "", fn, to: link(sec, field) };
        }),
      };
    }
    const it = byName.get(P.enum);
    if (!check(it?.kind === "enum", `${where}: ${P.enum} is an enum`)) return null;
    const textOf = (v) => {
      if (P.text === "sorts") { const s = sortsOf(v.fields); return s.length ? `(${s.join(", ")})` : null; }
      if (P.text === "fields") return v.fields.length ? `(${v.fields.map((f) => f.ty).join(", ")})` : null;
      if (P.text === "code") return /`([^`]+)`/.exec(v.doc)?.[1] || null;
      if (P.text === "sqlstate") return /^\[(\d{5})\]/.exec(v.doc)?.[1] || null;
      return null;
    };
    const boxOf = (en, v) => {
      const to = P.links ? link(P.links[v.name], `${en}::${v.name}`) : sectionOfVariant(en, v.name);
      check(to, `${where}: ${en}::${v.name} has a section`);
      if (P.raises && to && to !== sectionIds.get(P.root)) {
        const sec = chapters.flatMap((c) => c.sections.map((s) => [`${c.id}/${s.id}`, s])).find(([k]) => k === to)[1];
        const code = sec.groups.flatMap((g) => g.blocks.map((b) => b.code)).join("\n");
        check(code.includes(`${en}::${v.name}`), `${where}: section ${to} shows code that gives ${en}::${v.name}`);
      }
      return { name: v.name, sub: textOf(v), to };
    };
    const vs = members(it);
    if (P.links) for (const k of Object.keys(P.links)) check(vs.some((v) => v.name === k), `${where}: ${k} is a constructor of ${P.enum}`);
    if (P.text === "code" || P.text === "sqlstate") check(vs.filter((v) => !textOf(v)).length <= 1, `${where}: the constructors' doc comments give the box text`);
    const boxes = vs.map((v) => {
      const b = boxOf(P.enum, v);
      const nest = P.nest?.[v.name];
      if (nest) {
        const n = byName.get(nest);
        if (check(n?.kind === "enum" && v.fields.some((f) => new RegExp(`\\b${nest}\\b`).test(f.ty)), `${where}: ${v.name} holds a ${nest}`)) b.kids = members(n).map((k) => boxOf(nest, k));
      }
      return b;
    });
    const notes = (P.notes || []).map((n) => {
      let text = null;
      if (n.enum) { const e = byName.get(n.enum); if (check(e?.kind === "enum", `${where}: ${n.enum} is an enum`)) text = members(e).map((v) => v.name).join(" · "); }
      if (n.usedBy) {
        const users = members(byName.get("Query")).filter((v) => v.fields.some((f) => new RegExp(`\\b${n.usedBy}\\b`).test(f.ty)));
        if (check(users.length, `${where}: some query operator holds ${n.usedBy}`)) text = users.map((v) => v.name).join(" · ");
      }
      return { label: n.label, text, to: link(n.to, n.label) };
    });
    return { kind: "tree", root: { name: P.enum, to: link(P.root, P.enum) }, boxes, notes };
  };
  for (const [ch, out] of BOOK.map((c, i) => [c, chapters[i]])) out.picture = picture(ch);

  // where a link in the code goes: a definition's home, a constructor's Syntax section
  const index = Object.fromEntries([...home].sort().map(([name, at]) => [name, { at, sum: firstSentence(docOf(byName.get(name))) }]));
  for (const [rel, ns] of dropped) for (const n of ns) check(usedDrops.has(`${rel}:${n}`), `omit: ${rel}:${n} is in shown code`);

  const c = ctx.claim;
  ctx.quote("Ok(Answer::Rows(out)) => ordered_ok(db, oq, Ok(view_rows(out@)))", CLAIM);
  check(home.get("ordered_ok") === "outcomes/allowed", "ordered_ok is shown in Outcomes, Allowed outcomes");
  return {
    title: "SQLSpec",
    lead: c({ text: "A formal meaning of SQL, modeled on PostgreSQL.", repo: [README, "SQLSpec, a formal meaning of SQL modeled on PostgreSQL."], paper: [SQLSPEC, "SQLSpec, a formal SQL library in Verus based on PostgreSQL documentation"] }),
    meaning: {
      formula: "⟦Q⟧(db)",
      text: c({ text: "every allowed answer of query {Q} on database {db}", repo: [GUIDE, "an allowed answer of the statement's SQLSpec meaning ⟦Q⟧(db)"], paper: [SQLSPEC, "SQLSpec defines the set of permitted outcomes $\\llbracket Q\\rrbracket(D)$"] }),
      def: "ordered_ok",
      ...shownCode(byName.get("ordered_ok").file, byName.get("ordered_ok").codeLine, byName.get("ordered_ok").code),
      line: byName.get("ordered_ok").codeLine,
      file: byName.get("ordered_ok").file,
    },
    source: SRC,
    chapters,
    defs: index,
    variants: Object.fromEntries([...variantAt].sort()),
  };
}

// node docs/build/pages/sqlspec.mjs --pins [--repo PATH]: print the PINS block of the current source.
if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  const here = path.dirname(fileURLToPath(import.meta.url));
  const i = process.argv.indexOf("--repo");
  const repo = path.resolve(i > 0 ? process.argv[i + 1] : path.join(here, "../../.."));
  if (!process.argv.includes("--pins")) { console.error("usage: node docs/build/pages/sqlspec.mjs --pins [--repo PATH]"); process.exit(2); }
  const { items } = readSpec((rel) => fs.readFileSync(path.join(repo, rel), "utf8"), (rel) => fs.existsSync(path.join(repo, rel)));
  process.stdout.write(`const PINS = \`${currentPins(items)}\`;\n`);
}
