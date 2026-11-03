//! Verus translation of a validated AST document: the statement's meaning as one Verus module over the SQLSpec library.
//!
//! The module holds
//! - `schema_spec() -> Schema`: the document's schema as the semantics library's `Schema` (`schema`);
//! - `query_spec() -> OrderedQuery`: the AST as a flat let-chain, one constructor per node, children first;
//! - `query_exec() -> (q: EOrderedQuery) ensures q@ == query_spec()` (evaluator crates only; a candidate crate of the
//!   fixed entry v3 omits it, `EmitOptions::candidate`): the same chain in exec form, each node followed by its ghost
//!   spec node and one `assert(view(e) == g)` step, so the proof is linear in the AST size and needs no fuel or
//!   `compute`;
//! - `lemma_query_wf() ensures wf_ordered(schema_spec(), query_spec())`: the semantics library's typing accepts the
//!   AST, proved by evaluation (`by (compute)`), so a mistyped resolution fails verification;
//! - `query_spec_at(ps)`, `param_typed(ps)`, `param_domain(ps)`, `lemma_query_wf_at(ps)`: the meaning at a binding of
//!   the free statement parameters (`crate::params`), uniform for concrete statements (`ps` empty,
//!   `query_spec_at(ps) == query_spec()`) and templates (`template`).
//!
//! Two layouts. [`emit_instance_module`] writes the schema, with its declared constraints, inside the statement module
//! (`query.rs` of the fixed entry v3 and of reference evaluator crates). [`emit_schema_module`] writes a document's
//! schema alone as its own module. The storage-aware crates of the entry v4 split the statement from the schema:
//! [`emit_column_schema_module`] writes `schema.rs`, the column schema (the dataset DDL's tables and columns,
//! independent of the statement and of any declared constraint), so a storage crate and every query crate over the same
//! dataset carry the same text byte for byte; [`emit_statement_module`] writes a `query.rs` that imports `schema_spec`
//! from it; and, when the DDL declares integrity constraints, [`emit_constraints_module`] writes `gendb_constraints.rs`
//! with `declared_schema()` (the declarations over `schema_spec()`), `declared_db(db)` and `lemma_declared_schema`. The
//! statement items are the same text in both layouts.
//!
//! Emission is generic over `ast_schema.json` (sort type names, view functions, variant forms, field kinds and the
//! sorts' typing-equivalence names); it has no per-construct or per-query cases (`constructors`).
//!
//! Trust: this translation is a TRUSTED boundary. That the emitted `schema_spec` / `query_spec` / `query_spec_at`
//! (and `param_typed` / `param_domain`) represent the original SQL and its typed AST is assumed, not proved; the
//! fixed SQL meaning the final claims are stated against is whatever is emitted here. Verus checks only properties
//! of the emitted text itself: that `query_exec` equals `query_spec` (the evaluator's executable AST corresponds to
//! the emitted spec AST), that the emitted AST is well-typed for the emitted schema under the semantics library's
//! typing (`lemma_query_wf`, `lemma_query_wf_at`), and that the example binding lies in the emitted domain. None of
//! these checks relates the emitted AST back to the SQL text or the decoded document; a mistranslation that yields a
//! well-typed AST would pass them. A literal that the exec AST cannot represent (e.g. a numeric coefficient beyond
//! `i128`) is the refusal `executable_domain`.
//!
//! Emitted names (`spec::`, `exec::`, `bridge::params`, `query_spec_at`, ...) are the public interface of assembled
//! candidate and evaluator crates; they do not follow the physical folders of SQLSpec.
//!
//! `constructors` and `schema` also expose the pieces the evaluator's executable schema module reuses
//! (`spec_chain`, `exec_chain`, `spec_constraint`, `check_prefix`, `nat_seq`, `sql_type`); every generator that
//! writes SQL names into generated comments renders them with `comment_text`.

mod constructors;
mod schema;
mod template;

pub use constructors::{exec_chain, spec_chain};
pub use schema::{check_prefix, nat_seq, spec_constraint, sql_type};

use crate::ast::{schema as ast_schema, AstDocument, TableDef};
use crate::params::Instance;
use std::borrow::Cow;
use std::fmt::{self, Write};

/// Module paths of the semantics library inside the crate that includes the emitted module.
#[derive(Debug, Clone)]
pub struct EmitOptions {
    pub spec_module: String,
    pub exec_module: String,
    /// Only templates use it (`bridge::params`).
    pub bridge_module: String,
    /// Where a split statement module (`emit_statement_module`) and the constraints module (`emit_constraints_module`)
    /// import `schema_spec` from.
    pub schema_module: String,
    /// Emit the executable AST `query_exec` of a statement without free parameters (the verified reference evaluator's
    /// crate needs it: ABI echo). A candidate crate of the fixed entry v3 states and proves the meaning only, so it
    /// omits it (`EmitOptions::candidate`): less solver work, same meaning.
    pub exec_ast: bool,
}

impl Default for EmitOptions {
    fn default() -> Self {
        EmitOptions {
            spec_module: "crate::spec".into(),
            exec_module: "crate::exec".into(),
            bridge_module: "crate::bridge".into(),
            schema_module: "crate::schema".into(),
            exec_ast: true,
        }
    }
}

impl EmitOptions {
    /// The emission of a candidate crate of the fixed entry v3 and of its statement key: the meaning without the
    /// evaluator's executable AST.
    pub fn candidate() -> Self {
        EmitOptions { exec_ast: false, ..EmitOptions::default() }
    }
}

/// Why a statement cannot be translated. Serialized (and displayed) as the recorded reason string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum EmitRefusal {
    /// A parameter has no value where one is needed (a template emitted as a concrete statement, or its exec AST).
    UnboundParameters,
    /// A literal does not fit its exec representation.
    ExecutableDomain,
}

impl EmitRefusal {
    pub fn as_str(self) -> &'static str {
        match self {
            EmitRefusal::UnboundParameters => "unbound_parameters",
            EmitRefusal::ExecutableDomain => "executable_domain",
        }
    }
}

impl fmt::Display for EmitRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmitError {
    pub reason: EmitRefusal,
    pub detail: String,
}

impl fmt::Display for EmitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.reason, self.detail)
    }
}

impl std::error::Error for EmitError {}

/// Render the Verus module for a statement without parameters (`EmitRefusal::UnboundParameters` for a template: bind it
/// with `params::instantiate` and use `emit_instance_module`).
pub fn emit_query_module(doc: &AstDocument, opts: &EmitOptions) -> Result<String, EmitError> {
    let inst = Instance::concrete(doc).map_err(|e| EmitError { reason: EmitRefusal::UnboundParameters, detail: e.detail })?;
    emit_instance_module(&inst, opts)
}

/// Render the Verus module for a statement whose fixed parameters are substituted (`params::instantiate`), with the
/// schema inside it.
pub fn emit_instance_module(inst: &Instance, opts: &EmitOptions) -> Result<String, EmitError> {
    let mut out = String::new();
    emit_header(&mut out, &inst.doc);
    emit_imports(&mut out, opts, !inst.free.is_empty());
    open_verus(&mut out);
    schema::emit_schema_spec(&mut out, &inst.doc.tables)?;
    emit_statement_items(&mut out, inst, opts)?;
    Ok(out)
}

/// Render the statement module of a split crate: the same statement items as [`emit_instance_module`], with
/// `schema_spec` imported from `opts.schema_module` (written by [`emit_schema_module`]).
pub fn emit_statement_module(inst: &Instance, opts: &EmitOptions) -> Result<String, EmitError> {
    let mut out = String::new();
    emit_header(&mut out, &inst.doc);
    emit_imports(&mut out, opts, !inst.free.is_empty());
    writeln!(out, "use {}::schema_spec;", opts.schema_module).unwrap();
    open_verus(&mut out);
    emit_statement_items(&mut out, inst, opts)?;
    Ok(out)
}

/// Render the schema module of a split crate: `schema_spec()` of `tables` (a document's schema, i.e. the dataset DDL)
/// and nothing about any statement.
pub fn emit_schema_module(tables: &[TableDef], opts: &EmitOptions) -> Result<String, EmitError> {
    let sch = ast_schema();
    let mut out = String::new();
    writeln!(out, "// Generated by the gendb-sql emitter from a dataset schema ({}; Verus interface {}).", sch.format, sch.verus_interface).unwrap();
    writeln!(out, "// Do not edit: regenerate from the DDL. Statement independent: every storage and query crate over this schema").unwrap();
    writeln!(out, "// carries this text byte for byte.").unwrap();
    writeln!(out, "use vstd::prelude::*;").unwrap();
    for m in ["types", "int", "scalar", "ast"] {
        writeln!(out, "use {}::{m}::*;", opts.spec_module).unwrap();
    }
    open_verus(&mut out);
    schema::emit_schema_spec(&mut out, tables)?;
    writeln!(out, "}} // verus!").unwrap();
    Ok(out)
}

/// Render the column schema module of a split crate (`schema.rs`): [`emit_schema_module`] of `tables` with every
/// table's declared constraints left out. Declared constraints therefore never change this text; for tables without
/// constraints it is byte-equal to `emit_schema_module`.
pub fn emit_column_schema_module(tables: &[TableDef], opts: &EmitOptions) -> Result<String, EmitError> {
    let columns: Vec<TableDef> =
        tables.iter().map(|t| TableDef { name: t.name.clone(), columns: t.columns.clone(), constraints: vec![] }).collect();
    emit_schema_module(&columns, opts)
}

/// Render the constraints module of a split crate (`gendb_constraints.rs`), or `None` when no table of `tables` declares
/// a constraint: `declared_schema()`, the declared constraints of `tables` over the column schema `schema_spec()`
/// imported from `opts.schema_module` ([`emit_column_schema_module`] of the same tables); `declared_db(db)`, `db`'s
/// tables under that schema; and `lemma_declared_schema`, which proves (by evaluation) that the declarations are
/// well-formed and the tables and columns are `schema_spec()`'s. Statement independent.
pub fn emit_constraints_module(tables: &[TableDef], opts: &EmitOptions) -> Result<Option<String>, EmitError> {
    if tables.iter().all(|t| t.constraints.is_empty()) {
        return Ok(None);
    }
    let (sch, spec) = (ast_schema(), &opts.spec_module);
    let mut out = String::new();
    writeln!(out, "// Generated by the gendb-sql emitter from a dataset schema's declared integrity constraints ({}; Verus interface {}).", sch.format, sch.verus_interface).unwrap();
    writeln!(out, "// Do not edit: regenerate from the DDL. Statement independent; the column schema (`schema.rs`) carries no").unwrap();
    writeln!(out, "// constraint, and this module states the declared ones over its `schema_spec()`.").unwrap();
    writeln!(out, "use vstd::prelude::*;").unwrap();
    for m in ["types", "int", "scalar", "ast"] {
        writeln!(out, "use {spec}::{m}::*;").unwrap();
    }
    writeln!(out, "use {spec}::value::Database;\nuse {spec}::constraints::constraints_wf;\nuse {}::schema_spec;", opts.schema_module).unwrap();
    open_verus(&mut out);
    schema::emit_declared_schema(&mut out, tables)?;
    out.push_str(
        "/// `db`'s tables under the declared schema: the same tables and columns, with the declared constraints.\n\
         pub open spec fn declared_db(db: Database) -> Database {\n    Database { schema: declared_schema(), tables: db.tables }\n}\n\n\
         /// The declared schema has `schema_spec()`'s tables and columns, and its declarations are well-formed (evaluated).\n\
         pub proof fn lemma_declared_schema()\n    ensures\n        declared_schema().len() == schema_spec().len(),\n        \
         forall|t: int| #![trigger declared_schema()[t]] 0 <= t < schema_spec().len() ==> declared_schema()[t].columns == schema_spec()[t].columns,\n        \
         constraints_wf(declared_schema()),\n{\n    assert(constraints_wf(declared_schema())) by (compute);\n}\n\n",
    );
    writeln!(out, "}} // verus!").unwrap();
    Ok(Some(out))
}

/// The statement's items after the schema: its AST (and exec AST), typing and parameter interface, and the closing of
/// the `verus!` block.
fn emit_statement_items(out: &mut String, inst: &Instance, opts: &EmitOptions) -> Result<(), EmitError> {
    let doc = &inst.doc;
    if inst.free.is_empty() {
        emit_query_spec(out, doc)?;
        if opts.exec_ast {
            emit_query_exec(out, doc)?;
        }
        emit_concrete_typing(out);
    } else {
        template::emit_template(out, inst)?;
    }
    writeln!(out, "}} // verus!").unwrap();
    Ok(())
}

/// The generated-file header, quoting the source SQL.
fn emit_header(out: &mut String, doc: &AstDocument) {
    let sch = ast_schema();
    let identity = doc.frontend.get("identity").and_then(|v| v.as_str()).unwrap_or("?");
    writeln!(out, "//! Generated by the gendb-sql emitter from a {} document ({identity}; Verus interface {}).", sch.format, sch.verus_interface).unwrap();
    writeln!(out, "//! Do not edit: regenerate from the SQL. Source query:").unwrap();
    for line in doc.sql.lines() {
        writeln!(out, "//!     {}", comment_text(line)).unwrap();
    }
}

/// `text` as it may appear inside a generated `//` or `///` comment: control characters other than tab (a line break
/// would end the comment and turn the rest of a quoted SQL name into source; a bare CR is not allowed in doc
/// comments) are shown escaped (`\n`, `\r`, `\u{b}`). Other text, including every ordinary name, is unchanged.
pub fn comment_text(text: &str) -> Cow<'_, str> {
    let escaped = |c: char| c.is_control() && c != '\t';
    if !text.chars().any(escaped) {
        return Cow::Borrowed(text);
    }
    Cow::Owned(text.chars().map(|c| if escaped(c) { c.escape_default().to_string() } else { c.to_string() }).collect())
}

/// The library imports of a statement module.
fn emit_imports(out: &mut String, opts: &EmitOptions, has_free_params: bool) {
    let (spec, exec) = (&opts.spec_module, &opts.exec_module);
    writeln!(out, "use vstd::prelude::*;").unwrap();
    for m in ["types", "int", "scalar", "ast", "typing"] {
        writeln!(out, "use {spec}::{m}::*;").unwrap();
    }
    if has_free_params {
        writeln!(out, "use {spec}::datetime::*;\nuse {}::params::*;", opts.bridge_module).unwrap();
    }
    writeln!(out, "use {exec}::ast::*;").unwrap();
}

/// The opening of the `verus!` block after the imports.
fn open_verus(out: &mut String) {
    writeln!(out, "\nverus! {{\n").unwrap();
}

fn emit_query_spec(out: &mut String, doc: &AstDocument) -> Result<(), EmitError> {
    writeln!(out, "/// The query's AST (spec).\npub open spec fn query_spec() -> OrderedQuery {{").unwrap();
    spec_chain(out, &doc.nodes, "n")?;
    writeln!(out, "    n{}\n}}\n", doc.root).unwrap();
    Ok(())
}

fn emit_query_exec(out: &mut String, doc: &AstDocument) -> Result<(), EmitError> {
    writeln!(out, "/// The same AST as an exec value, proved equal to `query_spec()` step by step.").unwrap();
    // The proof is linear in the AST (one view step per node): its own prover context and a resource limit that grows
    // with the node count (resource settings only; nothing is assumed).
    writeln!(out, "#[verifier::spinoff_prover]\n#[verifier::rlimit({})]", 10 + doc.nodes.len()).unwrap();
    writeln!(out, "pub fn query_exec() -> (q: EOrderedQuery)\n    ensures q@ == query_spec(),\n{{").unwrap();
    exec_chain(out, &doc.nodes, "")?;
    writeln!(out, "    e{}\n}}\n", doc.root).unwrap();
    Ok(())
}

/// Typing of a statement without free parameters (evaluated), and its parameter interface: the binding is empty and
/// the meaning is `query_spec()`.
fn emit_concrete_typing(out: &mut String) {
    writeln!(out, "/// The AST is well-typed for the schema (the semantics library's typing, evaluated).").unwrap();
    writeln!(out, "pub proof fn lemma_query_wf()\n    ensures wf_ordered(schema_spec(), query_spec()),\n{{").unwrap();
    writeln!(out, "    assert(wf_ordered(schema_spec(), query_spec())) by (compute);\n}}\n").unwrap();
    out.push_str(
        "/// No free statement parameter: the binding is empty and the meaning is `query_spec()`.\n\
         pub open spec fn param_typed(ps: Seq<Literal>) -> bool {\n    ps.len() == 0\n}\n\n\
         pub open spec fn param_domain(ps: Seq<Literal>) -> bool {\n    ps.len() == 0\n}\n\n\
         pub open spec fn query_spec_at(ps: Seq<Literal>) -> OrderedQuery {\n    query_spec()\n}\n\n\
         pub proof fn lemma_query_wf_at(ps: Seq<Literal>)\n    requires param_typed(ps),\n    \
         ensures wf_ordered(schema_spec(), query_spec_at(ps)),\n{\n    lemma_query_wf();\n}\n\n",
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{decode, Translation};

    /// A document with a literal outside its exec representation is the named refusal `executable_domain`: a
    /// numeric coefficient beyond `i128` (valid in spec, where the coefficient is an `int`).
    #[test]
    fn literal_beyond_exec_representation_is_refused() {
        let doc = r#"{"format": "gendb-sql-ast-v1", "status": "ok", "frontend": {"identity": "unit"}, "sql": "SELECT 1e40",
            "schema": {"tables": []},
            "output": {"names": ["x"], "columns": [{"type": {"kind": "numeric", "typmod": null}, "nullable": false, "dscale": 0}], "pg_types": ["numeric"]},
            "root": 4, "nodes": [
              {"id": 0, "tag": "Num", "coeff": "10000000000000000000000000000000000000000", "scale": 0},
              {"id": 1, "tag": "Lit", "lit": 0, "type": {"type": {"kind": "numeric", "typmod": null}, "nullable": false, "dscale": 0}},
              {"id": 2, "tag": "Table", "table": 0, "columns": []},
              {"id": 3, "tag": "Project", "exprs": [1], "input": 2, "columns": [{"type": {"kind": "numeric", "typmod": null}, "nullable": false, "dscale": 0}]},
              {"id": 4, "tag": "OrderedQuery", "body": 3, "keys": [], "limit": null, "offset": 0}]}"#;
        // `Table 0` in an empty schema is refused by the decoder; give it one table.
        let doc = doc.replace(r#""tables": []"#, r#""tables": [{"name": "t", "columns": []}]"#);
        let Translation::Ok(doc) = decode(&doc).unwrap() else { panic!("refused") };
        let e = emit_query_module(&doc, &EmitOptions::default()).unwrap_err();
        assert_eq!(e.reason, EmitRefusal::ExecutableDomain, "{e}");
        assert_eq!(e.to_string().split(':').next(), Some("executable_domain"));
    }

    /// A quoted SQL name may contain a line break; in a generated comment it is shown escaped, so the rest of the
    /// name cannot become source text. Ordinary names are rendered unchanged.
    #[test]
    fn line_breaks_in_names_stay_inside_generated_comments() {
        let doc = r#"{"format": "gendb-sql-ast-v1", "status": "ok", "frontend": {"identity": "unit"}, "sql": "SELECT 1 FROM \"t\nfn t() {}\"",
            "schema": {"tables": [{"name": "t\nfn t() {}", "columns": [{"name": "c\r\nfn c() {}", "type": {"kind": "int4"}, "nullable": false}, {"name": "d", "type": {"kind": "int4"}, "nullable": false}]}]},
            "output": {"names": ["c", "d"], "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}, {"type": {"kind": "int4"}, "nullable": false, "dscale": null}], "pg_types": ["int4", "int4"]},
            "root": 1, "nodes": [
              {"id": 0, "tag": "Table", "table": 0, "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}, {"type": {"kind": "int4"}, "nullable": false, "dscale": null}]},
              {"id": 1, "tag": "OrderedQuery", "body": 0, "keys": [], "limit": null, "offset": 0}]}"#;
        let Translation::Ok(doc) = decode(doc).unwrap() else { panic!("refused") };
        let module = emit_query_module(&doc, &EmitOptions::default()).unwrap();
        assert!(!module.lines().any(|l| l.trim_start().starts_with("fn ")), "{module}");
        assert!(module.contains("        // t\\nfn t() {}\n"), "{module}");
        assert!(module.contains("}, // c\\r\\nfn c() {}\n"), "{module}");
        assert!(module.contains("}, // d\n"), "{module}");
        assert_eq!(comment_text("l_shipdate"), "l_shipdate");
    }

    /// The split layout carries the same meaning as the inline one: the schema module holds exactly the inline
    /// `schema_spec` block and nothing of the statement, and the statement module is the inline module with that block
    /// replaced by one import.
    #[test]
    fn split_modules_recompose_to_the_inline_module() {
        let doc = r#"{"format": "gendb-sql-ast-v1", "status": "ok", "frontend": {"identity": "unit"}, "sql": "SELECT c FROM t",
            "schema": {"tables": [{"name": "t", "columns": [{"name": "c", "type": {"kind": "int4"}, "nullable": false}]}]},
            "output": {"names": ["c"], "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}], "pg_types": ["int4"]},
            "root": 1, "nodes": [
              {"id": 0, "tag": "Table", "table": 0, "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}]},
              {"id": 1, "tag": "OrderedQuery", "body": 0, "keys": [], "limit": null, "offset": 0}]}"#;
        let Translation::Ok(doc) = decode(doc).unwrap() else { panic!("refused") };
        let inst = Instance::concrete(&doc).unwrap();
        let opts = EmitOptions::candidate();
        let inline = emit_instance_module(&inst, &opts).unwrap();
        let schema = emit_schema_module(&doc.tables, &opts).unwrap();
        let statement = emit_statement_module(&inst, &opts).unwrap();
        let block = schema.split_once("verus! {\n\n").unwrap().1.strip_suffix("} // verus!\n").unwrap();
        assert!(block.starts_with("/// The schema") && !schema.contains("query_spec") && !schema.contains("SELECT"), "{schema}");
        let import = "use crate::schema::schema_spec;\n";
        assert!(statement.contains(import) && !statement.contains("fn schema_spec"), "{statement}");
        let recomposed = statement.replacen(import, "", 1).replacen("verus! {\n\n", &format!("verus! {{\n\n{block}"), 1);
        assert_eq!(recomposed, inline);
    }

    /// `SELECT * FROM t` over a table `t (c int4 NOT NULL, d int4)` with the constraints `constraints` (a JSON list),
    /// beside a table `u` without constraints.
    fn constrained(constraints: &str) -> AstDocument {
        let (int4, nullable) = (r#"{"type": {"kind": "int4"}, "nullable": false, "dscale": null}"#, r#"{"type": {"kind": "int4"}, "nullable": true, "dscale": null}"#);
        let doc = format!(
            r#"{{"format": "gendb-sql-ast-v1", "status": "ok", "frontend": {{"identity": "unit"}}, "sql": "SELECT * FROM t",
            "schema": {{"tables": [{{"name": "t", "columns": [{{"name": "c", "type": {{"kind": "int4"}}, "nullable": false}}, {{"name": "d", "type": {{"kind": "int4"}}, "nullable": true}}], "constraints": {constraints}}},
                                  {{"name": "u", "columns": [{{"name": "e", "type": {{"kind": "int8"}}, "nullable": false}}], "constraints": []}}]}},
            "output": {{"names": ["c", "d"], "columns": [{int4}, {nullable}], "pg_types": ["int4", "int4"]}},
            "root": 1, "nodes": [
              {{"id": 0, "tag": "Table", "table": 0, "columns": [{int4}, {nullable}]}},
              {{"id": 1, "tag": "OrderedQuery", "body": 0, "keys": [], "limit": null, "offset": 0}}]}}"#
        );
        let Translation::Ok(doc) = decode(&doc).unwrap() else { panic!("refused") };
        doc
    }

    const PRIMARY_KEY: &str = r#"{"kind": "key", "name": null, "primary": true, "columns": [0], "nulls_distinct": true, "deferrable": false, "initially_deferred": false}"#;
    const CHECK_D_POSITIVE: &str = r#"{"kind": "check", "name": "d_positive", "root": 3, "nodes": [
        {"id": 0, "tag": "Col", "index": 1, "type": {"type": {"kind": "int4"}, "nullable": true, "dscale": null}},
        {"id": 1, "tag": "Int", "v": "0", "kind": "Int4"},
        {"id": 2, "tag": "Lit", "lit": 1, "type": {"type": {"kind": "int4"}, "nullable": false, "dscale": null}},
        {"id": 3, "tag": "Cmp", "op": "Gt", "a": 0, "b": 2}]}"#;

    /// The column schema module is the schema module without constraints: byte-equal for tables without constraints,
    /// and the same text for the same columns whatever is declared.
    #[test]
    fn column_schema_module_is_the_schema_module_without_constraints() {
        let opts = EmitOptions::candidate();
        let plain = constrained("[]");
        let declared = constrained(&format!("[{PRIMARY_KEY}, {CHECK_D_POSITIVE}]"));
        let column_schema = emit_column_schema_module(&plain.tables, &opts).unwrap();
        assert_eq!(column_schema, emit_schema_module(&plain.tables, &opts).unwrap());
        assert_eq!(emit_column_schema_module(&declared.tables, &opts).unwrap(), column_schema);
        assert!(!column_schema.contains("Constraint::"), "{column_schema}");
        // The generic schema module still carries a document's constraints.
        let full = emit_schema_module(&declared.tables, &opts).unwrap();
        assert!(full.contains("Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }") && full.contains("Constraint::Check(c0_1_n3)"), "{full}");
    }

    /// The constraints module exists exactly when some table declares a constraint; it states the declarations over the
    /// imported column schema, table by table, with the same constraint text as the inline schema.
    #[test]
    fn constraints_module_states_the_declarations_over_the_column_schema() {
        let opts = EmitOptions::candidate();
        assert_eq!(emit_constraints_module(&constrained("[]").tables, &opts).unwrap(), None);
        let declared = constrained(&format!("[{PRIMARY_KEY}, {CHECK_D_POSITIVE}]"));
        let module = emit_constraints_module(&declared.tables, &opts).unwrap().unwrap();
        for expected in [
            "use crate::schema::schema_spec;\n",
            "pub open spec fn declared_schema() -> Schema {\n",
            "        TableSchema { columns: schema_spec()[0].columns, constraints: seq![\n            Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true },\n            Constraint::Check(c0_1_n3),\n        ] },\n",
            "        TableSchema { columns: schema_spec()[1].columns, constraints: seq![\n        ] },\n",
            "pub open spec fn declared_db(db: Database) -> Database {\n    Database { schema: declared_schema(), tables: db.tables }\n}\n",
            "    assert(constraints_wf(declared_schema())) by (compute);\n",
        ] {
            assert!(module.contains(expected), "missing {expected:?} in\n{module}");
        }
        assert!(module.contains("let c0_1_n3 = Pred::Cmp"), "{module}");
        assert!(!module.contains("Column {") && !module.contains("query_spec"), "columns are referenced, never repeated: {module}");
        assert!(module.ends_with("} // verus!\n"));
    }
}
