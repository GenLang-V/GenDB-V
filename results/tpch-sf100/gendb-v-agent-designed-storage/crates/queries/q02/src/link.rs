//! Link toolkit: optional, generic lemmas that help an author prove that their own code and intermediate
//! specifications compute the SQL meaning (`spec::eval`, `spec::order::ordered_ok`) and stay inside the capacity
//! domain (`exec::relational::domain::fits_query`). Nothing here names a query, a table or a column, and nothing is
//! generated from it: authors state and prove their own normal forms and may call these lemmas or ignore them.
//!
//! Trust. Nothing uses `assume`, `admit` or `external_body`; every lemma and executable function is checked by the
//! pinned Verus with `--no-cheating`. Most definitions are an author's optional vocabulary: the fixed claim does not
//! mention them, so a weak or wrong helper can only fail to prove it. The exceptions are the source-relation and
//! result-row definitions the fixed entry and the generated source files state their claims with: `query::{TextCol,
//! TextView, text_wf, text_at, view_rows, proj, proj_all}` and `source::{proj_columns, rows_in_columns,
//! cols_in_table}`. They fix what "the delivered columns of table t" and "the answer rows" mean, so they are part of
//! the fixed meaning like `spec`, and their bodies must not change.
//!
//! Placement: the semantics library root and every candidate crate declare `link` next to `spec`, `exec` and
//! `bridge`, with this file as `link.rs`, so the toolkit is checked with the library and with every candidate. The
//! reference evaluator crates do not copy it. The fixed entry and the generated source files import `link::query`
//! (source columns, `view_rows`) and `link::source`.
//!
//! Dependencies: `link` reads `spec`, `exec` and `bridge`; nothing in those layers reads `link`. Inside `link`,
//! `expr` and `exists` use no other link module, `query` uses `expr`, and `join`, `capacity`, `source` and
//! `outcome` use `query`.
//!
//! - `expr`:     per-row values, comparisons and connectives of expressions and conditions, all total (`Ok`) on
//!               the rows they cover.
//! - `query`:    the accumulator normal form of aggregation queries (`QuerySpec`) with its laws, allowed outputs
//!               and the link lemmas to `GroupBy`/`Aggregate`; also the entry's source-column views.
//! - `join`:     FROM trees as kept rows of left-deep products, projections of products, and sums over relations
//!               (join-order and partition independence without enumerating the product).
//! - `capacity`: when a capacity condition or SQL error found in any evaluation order is the canonical one.
//! - `exists`:   `EXISTS` over a filtered input (correlated or not).
//! - `source`:   the delivered columns of a source table and their declared domains.
//! - `outcome`:  from facts about the statement body to the fixed claim's `ordered_ok` form, and executable rows.
//!
//! The declaration order below is the checked one (a proof in `query` was once order-sensitive); keep it.
pub mod expr;
pub mod query;
pub mod join;
pub mod capacity;
pub mod exists;
pub mod source;
pub mod outcome;
