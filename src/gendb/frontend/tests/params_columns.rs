//! Typed statement parameters (`params`, parser placeholders, translator `query_spec_at`) and the generic environment
//! layout / column demand (`columns`), through the Python parser. No Verus: with `GENDB_SQL_EMIT_DIR` set, the emitted
//! template modules are written there for one pinned-Verus check over the SQLSpec library.
//!
//! - `q6_template_bindings`: the Q6 template bound at the standard values is the concrete Q6 AST and module; the
//!   partially and the fully free forms go through the same `declare` / `instantiate` / translator path.
//! - `nested_templates_emit`: grouped and nested/correlated templates through the same path.
//! - `text_template_q16`: TPC-H Q16 with its three text constants and eight sizes as parameters: fully fixed it is the
//!   concrete Q16 module; free text slots have the text domain (no NUL, no bounds); exact text values.
//! - `parameter_refusals`: named refusals of invalid declarations (parser) and values/domains (host).
//! - `q4_demand_and_correlation`: TPC-H Q4's demanded columns and its correlated EXISTS reference.
//! - `demand_invariants`: all 22 TPC-H queries (layout, reads and observations covered, source declaration), the
//!   source fields of the accepted Q1/Q3/Q6/Q19 packages, and non-TPC-H cases for whole-row, cardinality-only, computed
//!   and row-count-only uses and binding refusals.
use gendb_frontend::ast::{AstDocument, FieldValue, Translation};
use gendb_frontend::columns::{self, BindingRefusalReason, NodeLayout, Slot};
use gendb_frontend::params::{self, BindingRequest, ParamDomain, ParamRefusal, ParamRequest, ParamType, ParamValue};
use gendb_frontend::parser::SqlParser;
use gendb_frontend::translator::{emit_instance_module, emit_query_module, EmitOptions, EmitRefusal};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..").canonicalize().unwrap()
}

fn tpch_schema() -> PathBuf {
    repo().join("src/gendb/fixtures/tpch-spec/schema.sql")
}

fn prepared_schema() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/prepared_tpch_schema.sql")
}

fn parser() -> SqlParser {
    SqlParser::from_environment().unwrap()
}

/// Scratch directory under `TMPDIR` (a scratch directory); callers remove it.
fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("gendb-frontend-params-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn translate(schema: &Path, sql: &str, params: &[ParamRequest], name: &str) -> Translation {
    let dir = scratch(name);
    let f = dir.join("query.sql");
    std::fs::write(&f, sql).unwrap();
    let placeholders: Vec<_> = params.iter().map(ParamRequest::placeholder).collect();
    let (_, t) = parser().translate(schema, &f, "postgres", &placeholders).unwrap();
    std::fs::remove_dir_all(&dir).unwrap();
    t
}

fn ok(t: Translation) -> AstDocument {
    match t {
        Translation::Ok(d) => d,
        Translation::Refused(r) => panic!("refused: {r:?}"),
    }
}

fn refused(t: Translation) -> String {
    match t {
        Translation::Refused(r) => r.reason,
        Translation::Ok(_) => panic!("expected a refusal"),
    }
}

fn labelled(schema: &Path, label: &str) -> AstDocument {
    let (_, t) = parser().translate_labelled(schema, &repo().join("src/gendb/fixtures/tpch-spec/queries.sql"), label, "postgres").unwrap();
    ok(t)
}

fn req(index: u32, ty: &str, binding: BindingRequest) -> ParamRequest {
    ParamRequest { index, name: None, sql_type: ty.into(), binding }
}

fn fixed(v: &str) -> BindingRequest {
    BindingRequest::Fixed(v.into())
}

fn free(min: Option<&str>, max: Option<&str>) -> BindingRequest {
    BindingRequest::Free { min: min.map(Into::into), max: max.map(Into::into) }
}

/// Emitted text without the header comment (which quotes the SQL).
fn body(module: &str) -> String {
    module.lines().filter(|l| !l.starts_with("//!")).collect::<Vec<_>>().join("\n")
}

fn write_emitted(name: &str, module: &str) {
    if let Some(dir) = std::env::var_os("GENDB_SQL_EMIT_DIR") {
        std::fs::write(Path::new(&dir).join(format!("{name}.rs")), module).unwrap();
    }
}

const Q6_TEMPLATE: &str = "SELECT\n    SUM(l_extendedprice * l_discount) AS revenue\nFROM lineitem\nWHERE\n    l_shipdate >= $1\n    \
    AND l_shipdate < $1 + INTERVAL '1' YEAR\n    AND l_discount BETWEEN $2 - 0.01 AND $2 + 0.01\n    AND l_quantity < $3;\n";

#[test]
fn q6_template_bindings() {
    let schema = tpch_schema();
    let concrete = labelled(&schema, "Q6");
    let opts = EmitOptions::default();
    let concrete_module = emit_query_module(&concrete, &opts).unwrap();
    write_emitted("q6", &concrete_module);

    // All fixed at the standard substitution values: the concrete AST (annotations included) and module.
    let all_fixed = [req(1, "date", fixed("1994-01-01")), req(2, "numeric(3,2)", fixed("0.06")), req(3, "integer", fixed("24"))];
    let template = ok(translate(&schema, Q6_TEMPLATE, &all_fixed, "q6_fixed"));
    assert_eq!(template.params.iter().map(|p| p.index).collect::<Vec<_>>(), [1, 2, 3]);
    assert!(template.nodes.iter().filter(|n| n.param_index().is_some()).count() == 5, "$1 and $2 twice, $3 once");
    assert_eq!(emit_query_module(&template, &opts).unwrap_err().reason, EmitRefusal::UnboundParameters);
    let decls = params::declare(&template, &all_fixed).unwrap();
    let inst = params::instantiate(&template, &decls).unwrap();
    assert!(inst.free.is_empty() && inst.doc.params.is_empty());
    assert_eq!((&inst.doc.nodes, inst.doc.root, &inst.doc.output, &inst.doc.tables), (&concrete.nodes, concrete.root, &concrete.output, &concrete.tables));
    assert_eq!(body(&emit_instance_module(&inst, &opts).unwrap()), body(&concrete_module));

    // Some fixed ($3), the others free: one path, `ps[slot]` in ascending index order.
    let some_fixed = [req(1, "date", free(Some("1992-01-01"), Some("1998-12-31"))), req(2, "numeric(3,2)", free(Some("0.00"), Some("1.00"))), req(3, "integer", fixed("24"))];
    let t2 = ok(translate(&schema, Q6_TEMPLATE, &some_fixed, "q6_partial"));
    let inst2 = params::instantiate(&t2, &params::declare(&t2, &some_fixed).unwrap()).unwrap();
    assert_eq!(inst2.free.iter().map(|f| (f.index, f.slot)).collect::<Vec<_>>(), [(1, 0), (2, 1)]);
    assert_eq!(inst2.doc.params.iter().map(|p| p.index).collect::<Vec<_>>(), [1, 2]);
    let m2 = emit_instance_module(&inst2, &opts).unwrap();
    assert!(m2.contains("ps[0]") && m2.contains("ps[1]") && !m2.contains("ps[2]") && !m2.contains("fn query_spec()"));
    assert!(m2.contains("Literal::Int { v: 24, kind: IntKind::Int4 }"), "the fixed $3 is the literal 24");
    assert!(m2.contains("scale == 2 && 0 <= coeff <= 100"));
    write_emitted("q6_partial", &m2);

    // Every parameter free, one bound omitted: the type's range applies ($3 up to int4 max).
    let all_free = [req(1, "date", free(Some("1992-01-01"), Some("1998-12-31"))), req(2, "numeric(3,2)", free(Some("0.00"), Some("1.00"))), req(3, "integer", free(Some("1"), None))];
    let t3 = ok(translate(&schema, Q6_TEMPLATE, &all_free, "q6_free"));
    let inst3 = params::instantiate(&t3, &params::declare(&t3, &all_free).unwrap()).unwrap();
    assert_eq!(inst3.free[2].bounds().unwrap().1, &ParamValue::Int(i32::MAX as i64));
    assert_eq!(inst3.doc.nodes, t3.nodes, "nothing fixed: the template itself");
    let m3 = emit_instance_module(&inst3, &opts).unwrap();
    assert!(m3.contains("1 <= v <= 2147483647") && m3.contains("date_from_civil(1992, 1, 1) <= date_from_civil(y, m, d) <= date_from_civil(1998, 12, 31)"));
    write_emitted("q6_template", &m3);

    // The domain on the host side and exact argument conversion; the standard binding is admitted, 1.01 is not.
    let args = |v: [&str; 3]| params::parse_arguments(&inst3.free, &v.map(String::from)).unwrap();
    let standard = args(["1994-01-01", "0.06", "24"]);
    assert_eq!(standard, [ParamValue::Date { y: 1994, m: 1, d: 1 }, ParamValue::Num(6), ParamValue::Int(24)]);
    assert!(inst3.free.iter().zip(&standard).all(|(f, v)| f.admits(v)));
    let out = args(["1996-02-29", "1.01", "0"]);
    assert_eq!(inst3.free.iter().zip(&out).map(|(f, v)| f.admits(v)).collect::<Vec<_>>(), [true, false, false]);
    assert_eq!(ParamType::Numeric { precision: 3, scale: 2 }.text(&ParamValue::Num(6)), "0.06");
}

const Q16_TEMPLATE: &str = "SELECT p_brand, p_type, p_size, COUNT(DISTINCT ps_suppkey) AS supplier_cnt FROM partsupp, part \
    WHERE p_partkey = ps_partkey AND p_brand <> $1 AND p_type NOT LIKE $2 AND p_size IN ($3, $4, $5, $6, $7, $8, $9, $10) \
    AND ps_suppkey NOT IN (SELECT s_suppkey FROM supplier WHERE s_comment LIKE $11) \
    GROUP BY p_brand, p_type, p_size ORDER BY supplier_cnt DESC, p_brand, p_type, p_size";

/// Q16's parameters: `$1`, `$2`, `$11` text, `$3..$10` integer, bound at `texts` (fixed) or free.
fn q16_requests(texts: [BindingRequest; 3], sizes: impl Fn(usize) -> BindingRequest) -> Vec<ParamRequest> {
    let [brand, parts, comment] = texts;
    let mut out = vec![req(1, "text", brand), req(2, "text", parts)];
    out.extend((3..=10).map(|i| req(i, "integer", sizes(i as usize))));
    out.push(req(11, "text", comment));
    out
}

/// TPC-H Q16 with its text constants as `text` parameters (and its sizes as integers): a placeholder types like a text
/// constant (`<>` on char(10), NOT LIKE on varchar, LIKE inside NOT IN); fully fixed at the qgen values it is the
/// concrete Q16 module; free text slots are typed `Text` with domain `text_ok` (no NUL, no bounds) and the empty text
/// as the example; values are exact strings (empty, multi-byte UTF-8, LIKE wildcards) and a NUL is refused.
#[test]
fn text_template_q16() {
    let schema = tpch_schema();
    let opts = EmitOptions::default();
    let standard = ["49", "14", "23", "45", "19", "3", "36", "9"];
    let all_fixed = q16_requests([fixed("Brand#45"), fixed("MEDIUM POLISHED%"), fixed("%Customer%Complaints%")], |i| fixed(standard[i - 3]));
    let template = ok(translate(&schema, Q16_TEMPLATE, &all_fixed, "q16_fixed"));
    let text_lits = template.nodes.iter().filter(|n| n.tag == "Lit" && n.child("lit").is_some_and(|l| template.nodes[l].param_index().is_some_and(|i| [1, 2, 11].contains(&i))));
    assert_eq!(text_lits.count(), 3);
    assert_eq!(template.params.iter().filter(|p| p.ty == ParamType::Text).count(), 3);
    let fixed_inst = params::instantiate(&template, &params::declare(&template, &all_fixed).unwrap()).unwrap();
    assert!(fixed_inst.free.is_empty());
    let concrete = labelled(&schema, "Q16");
    assert_eq!(body(&emit_instance_module(&fixed_inst, &opts).unwrap()), body(&emit_query_module(&concrete, &opts).unwrap()));

    let all_free = q16_requests([free(None, None), free(None, None), free(None, None)], |_| free(Some("1"), Some("50")));
    let t = ok(translate(&schema, Q16_TEMPLATE, &all_free, "q16_free"));
    let inst = params::instantiate(&t, &params::declare(&t, &all_free).unwrap()).unwrap();
    assert_eq!(inst.free.iter().map(|f| (f.index, f.slot, f.ty)).filter(|f| f.2 == ParamType::Text).collect::<Vec<_>>(), [(1, 0, ParamType::Text), (2, 1, ParamType::Text), (11, 10, ParamType::Text)]);
    assert!(inst.free.iter().filter(|f| f.ty == ParamType::Text).all(|f| f.domain == ParamDomain::AllText && f.bounds().is_none()));
    let m = emit_instance_module(&inst, &opts).unwrap();
    for needle in [
        "/// - slot 0: `$1` text without a NUL byte",
        "/// - slot 2: `$3` integer in [1, 50]",
        "    &&& type_lit(ps[0]) == Some(nn(ScalarTy::Text))",
        "    &&& match ps[10] { Literal::Text(b) => text_ok(b), _ => false }",
        "    &&& match ps[2] { Literal::Int { v, .. } => 1 <= v <= 50, _ => false }",
        "/// One binding in the domain: the declared minima (the empty text in a text slot).",
        "seq![Literal::Text(seq![]), Literal::Text(seq![]), Literal::Int { v: 1, kind: IntKind::Int4 }",
        "    assert(param_typed(param_example())) by (compute);\n    assert(match param_example()[2] { Literal::Int { v, .. } => 1 <= v <= 50, _ => false }) by (compute);",
        "    assert(param_domain(param_example()));\n}",
    ] {
        assert!(m.contains(needle), "the Q16 template module lacks {needle}");
    }
    write_emitted("q16_template", &m);

    // Exact text values: any string without NUL, including the empty one and multi-byte UTF-8.
    let mut texts: Vec<String> = ["Brand#45", "MEDIUM POLISHED%"].map(String::from).to_vec();
    texts.extend(standard.map(String::from));
    texts.push("%\u{e9}t\u{e9} \u{65e5}\u{672c}%".into());
    let values = params::parse_arguments(&inst.free, &texts).unwrap();
    assert_eq!((&values[0], &values[10]), (&ParamValue::Text("Brand#45".into()), &ParamValue::Text("%\u{e9}t\u{e9} \u{65e5}\u{672c}%".into())));
    assert!(inst.free.iter().zip(&values).all(|(f, v)| f.admits(v)));
    assert_eq!(ParamType::Text.text(&values[10]), texts[10]);
    assert_eq!(ParamType::Text.parse(""), Ok(ParamValue::Text(String::new())));
    let nul = ParamType::Text.parse("a\0b").unwrap_err();
    assert!(nul.reason == ParamRefusal::InvalidParameterValue && nul.detail.contains("NUL"), "{nul}");
    assert!(!inst.free[0].admits(&ParamValue::Text("a\0b".into())) && !inst.free[0].admits(&ParamValue::Int(1)));
    let literal = ParamType::Text.literal_node(&ParamValue::Text("\u{e9}".into()));
    assert_eq!((literal.tag.as_str(), &literal.fields), ("Text", &vec![FieldValue::Bytes("\u{e9}".into())]));

    // A text parameter takes no bounds (text order depends on the collation).
    let bounded = q16_requests([free(Some("A"), None), free(None, None), free(None, None)], |_| free(None, None));
    assert_eq!(params::declare(&t, &bounded).unwrap_err().reason, ParamRefusal::InvalidParameterDomain);
}

/// Templates over a grouped (Q1) and a nested, correlated (Q4) statement: the same translator path, multi-element lists
/// and EXISTS in the equivalence proof (their modules join the Verus check), and the demand of a template is that of
/// the concrete statement (parameters are literals, not environment positions).
#[test]
fn nested_templates_emit() {
    let schema = prepared_schema();
    let date = [req(1, "date", free(Some("1992-01-01"), Some("1998-12-31")))];
    let q1 = "SELECT l_returnflag, l_linestatus, SUM(l_quantity) AS sum_qty, SUM(l_extendedprice) AS sum_base_price, \
              SUM(l_extendedprice * (1 - l_discount)) AS sum_disc_price, SUM(l_extendedprice * (1 - l_discount) * (1 + l_tax)) AS sum_charge, \
              AVG(l_quantity) AS avg_qty, AVG(l_extendedprice) AS avg_price, AVG(l_discount) AS avg_disc, COUNT(*) AS count_order \
              FROM lineitem WHERE l_shipdate <= $1 - INTERVAL '90' DAY GROUP BY l_returnflag, l_linestatus ORDER BY l_returnflag, l_linestatus";
    let q4 = "SELECT o_orderpriority, COUNT(*) AS order_count FROM orders WHERE o_orderdate >= $1 AND o_orderdate < $1 + INTERVAL '3' MONTH \
              AND EXISTS (SELECT * FROM lineitem WHERE l_orderkey = o_orderkey AND l_commitdate < l_receiptdate) \
              GROUP BY o_orderpriority ORDER BY o_orderpriority";
    for (name, sql, label) in [("q1_template", q1, "Q1"), ("q4_template", q4, "Q4")] {
        let t = ok(translate(&schema, sql, &date, name));
        let inst = params::instantiate(&t, &params::declare(&t, &date).unwrap()).unwrap();
        let m = emit_instance_module(&inst, &EmitOptions::default()).unwrap();
        assert!(m.contains("ps[0]") && !m.contains("fn query_spec()"), "{name}");
        write_emitted(name, &m);
        assert_eq!(
            columns::analyze(&inst.doc).unwrap().columns.keys().collect::<Vec<_>>(),
            columns::analyze(&labelled(&schema, label)).unwrap().columns.keys().collect::<Vec<_>>(),
            "{name}"
        );
    }
}

#[test]
fn parameter_refusals() {
    let schema = tpch_schema();
    let q = "SELECT COUNT(*) AS n FROM lineitem WHERE l_quantity < $1";
    let int1 = [req(1, "integer", free(None, None))];
    assert_eq!(refused(translate(&schema, q, &[], "undeclared")), "undeclared_parameter");
    assert_eq!(refused(translate(&schema, q, &[req(1, "integer", free(None, None)), req(2, "date", free(None, None))], "unused")), "unused_parameter");
    assert_eq!(refused(translate(&schema, q, &[req(1, "varchar(10)", free(None, None))], "varchar")), "unsupported_parameter_type");
    assert_eq!(refused(translate(&schema, q, &[req(1, "char(10)", free(None, None))], "char")), "unsupported_parameter_type");
    assert_eq!(refused(translate(&schema, q, &[req(1, "text", free(None, None))], "text")), "type_mismatch", "numeric < text has no operator");
    assert_eq!(refused(translate(&schema, q, &[req(1, "numeric(40,2)", free(None, None))], "wide")), "unsupported_parameter_type");
    assert_eq!(refused(translate(&schema, q, &[req(1, "numeric", free(None, None))], "no_scale")), "unsupported_parameter_type");
    assert_eq!(refused(translate(&schema, q, &[req(1, "integer", free(None, None)), req(1, "date", free(None, None))], "twice")), "invalid_parameter_declaration");
    assert_eq!(refused(translate(&schema, q, &[req(0, "integer", free(None, None))], "zero")), "invalid_parameter_declaration");
    assert_eq!(refused(translate(&schema, "SELECT l_orderkey FROM lineitem WHERE l_quantity < $1 LIMIT $1", &int1, "limit")), "parameter_position");

    // Host: exact values (no rounding), type ranges, domains, matching declarations.
    let d = ok(translate(&schema, q, &int1, "host"));
    let reason = |r: &[ParamRequest]| params::declare(&d, r).unwrap_err().reason;
    assert_eq!(reason(&[req(1, "integer", fixed("2.5"))]), ParamRefusal::InvalidParameterValue);
    assert_eq!(reason(&[req(1, "integer", fixed("2147483648"))]), ParamRefusal::InvalidParameterValue);
    assert_eq!(reason(&[req(1, "integer", free(Some("5"), Some("4")))]), ParamRefusal::InvalidParameterDomain);
    assert_eq!(reason(&[req(2, "integer", fixed("1"))]), ParamRefusal::ParameterDeclarationMismatch);
    let num = ParamType::Numeric { precision: 3, scale: 2 };
    assert_eq!(num.parse("0.065").unwrap_err().reason, ParamRefusal::InvalidParameterValue);
    assert_eq!(num.parse("10.00").unwrap_err().reason, ParamRefusal::InvalidParameterValue);
    assert_eq!(num.parse("1e2").unwrap_err().reason, ParamRefusal::InvalidParameterValue);
    assert_eq!(num.parse("-.5"), Ok(ParamValue::Num(-50)));
    assert_eq!(ParamType::Date.parse("1994-02-29").unwrap_err().reason, ParamRefusal::InvalidParameterValue);
    assert_eq!(ParamType::Date.parse("1996-2-29").unwrap_err().reason, ParamRefusal::InvalidParameterValue);
    let inst = params::instantiate(&d, &params::declare(&d, &int1).unwrap()).unwrap();
    let e = params::parse_arguments(&inst.free, &[]).unwrap_err();
    assert_eq!((e.reason, e.to_string()), (ParamRefusal::ArgumentCount, "argument_count: 0 arguments for 1 free parameters".to_string()));
}

/// Env slot of `Col` node `id`.
fn col_slot(d: &columns::ColumnDemand, doc: &AstDocument, id: usize) -> Slot {
    let (NodeLayout::Env { env }, Some(FieldValue::Nat(i))) = (&d.layout[id], doc.nodes[id].field("index")) else { panic!("node {id} is not a laid-out Col") };
    env[*i as usize]
}

#[test]
fn q4_demand_and_correlation() {
    let doc = labelled(&prepared_schema(), "Q4");
    let d = columns::analyze(&doc).unwrap();
    let (lineitem, orders) = (0, 1);
    assert_eq!(d.table_columns(orders), [0, 4, 5]);
    assert_eq!(d.table_columns(lineitem), [0, 11, 12]);
    // EXISTS observes cardinality only: lineitem columns are read, never observed as rows.
    assert!(d.table_columns(lineitem).iter().all(|&c| d.columns[&(lineitem, c)].observed_by.is_empty()));
    // The output key is the orders column itself, observed by the root.
    assert_eq!(d.columns[&(orders, 5)].observed_by, [doc.root]);
    // The correlated `o_orderkey` inside EXISTS reads the outer orders occurrence, below the subquery's context.
    let exists = doc.nodes.iter().position(|n| n.tag == "Exists").unwrap();
    let sub_table = d.occurrences.iter().find(|(_, t)| *t == lineitem).unwrap().0;
    let outer_table = d.occurrences.iter().find(|(_, t)| *t == orders).unwrap().0;
    let NodeLayout::Env { env: exists_env } = &d.layout[exists] else { panic!() };
    let readers = &d.columns[&(orders, 0)].read_by;
    assert_eq!(readers.len(), 1);
    let (NodeLayout::Env { env }, Some(FieldValue::Nat(i))) = (&d.layout[readers[0]], doc.nodes[readers[0]].field("index")) else { panic!() };
    assert!((*i as usize) < exists_env.len() && env.len() == exists_env.len() + doc.tables[lineitem].columns.len());
    assert_eq!(env[*i as usize], Slot::Base { occurrence: outer_table, table: orders, column: 0 });
    assert_eq!(col_slot(&d, &doc, d.columns[&(lineitem, 0)].read_by[0]), Slot::Base { occurrence: sub_table, table: lineitem, column: 0 });
    let src = columns::source_declaration(&doc, &d).unwrap();
    assert_eq!(
        src.tables.iter().map(|t| (t.name.as_str(), t.columns.iter().map(|c| c.ordinal).collect::<Vec<_>>())).collect::<Vec<_>>(),
        [("lineitem", vec![0, 11, 12]), ("orders", vec![0, 4, 5])]
    );
}

/// The generic invariants of one analysis: every `Col` read and every observed output slot is demanded, every demanded
/// column has a use, every FROM occurrence is counted, and the source declaration delivers exactly the demand.
fn check_invariants(name: &str, doc: &AstDocument) -> columns::ColumnDemand {
    let d = columns::analyze(doc).unwrap_or_else(|e| panic!("{name}: {e}"));
    for (id, n) in doc.nodes.iter().enumerate() {
        if n.tag == "Col" && !matches!(d.layout[id], NodeLayout::None) {
            if let Slot::Base { table, column, .. } = col_slot(&d, doc, id) {
                assert!(d.columns[&(table, column)].read_by.contains(&id), "{name}: Col {id} not counted");
            }
        }
        if n.tag == "Table" {
            assert!(d.occurrences.iter().any(|(o, t)| *o == id && d.tables.contains(t)), "{name}: Table {id}");
        }
    }
    let NodeLayout::Query { ctx_len: 0, output } = &d.layout[doc.body()] else { panic!("{name}: body layout") };
    for s in output {
        if let Slot::Base { table, column, .. } = s {
            assert!(d.columns[&(*table, *column)].observed_by.contains(&doc.root), "{name}: output slot {s:?}");
        }
    }
    assert!(d.columns.values().all(|u| !u.read_by.is_empty() || !u.observed_by.is_empty()));
    let src = columns::source_declaration(doc, &d).unwrap_or_else(|e| panic!("{name}: {e}"));
    assert_eq!(src.tables.iter().map(|t| t.table_id).collect::<BTreeSet<_>>(), d.tables, "{name}");
    for t in &src.tables {
        let delivered: Vec<usize> = t.columns.iter().map(|c| c.ordinal).collect();
        let demanded = d.table_columns(t.table_id);
        assert!(delivered == demanded || (demanded.is_empty() && t.columns.len() == 1 && t.columns[0].row_count_only), "{name}: {}", t.name);
    }
    d
}

#[test]
fn demand_invariants() {
    // Every TPC-H query: nested, correlated, derived tables, outer joins, views.
    let schema = tpch_schema();
    for q in 1..=22 {
        check_invariants(&format!("Q{q}"), &labelled(&schema, &format!("Q{q}")));
    }
    // The source fields of the accepted Q1/Q3/Q6/Q19 packages (recorded in their exports) are the demand.
    let expected: [(&str, &[(&str, &[&str])]); 4] = [
        ("Q1", &[("lineitem", &["l_quantity", "l_extendedprice", "l_discount", "l_tax", "l_returnflag", "l_linestatus", "l_shipdate"])]),
        (
            "Q3",
            &[
                ("lineitem", &["l_orderkey", "l_extendedprice", "l_discount", "l_shipdate"]),
                ("orders", &["o_orderkey", "o_custkey", "o_orderdate", "o_shippriority"]),
                ("customer", &["c_custkey", "c_mktsegment"]),
            ],
        ),
        ("Q6", &[("lineitem", &["l_quantity", "l_extendedprice", "l_discount", "l_shipdate"])]),
        (
            "Q19",
            &[("lineitem", &["l_partkey", "l_quantity", "l_extendedprice", "l_discount", "l_shipinstruct", "l_shipmode"]), ("part", &["p_partkey", "p_brand", "p_size", "p_container"])],
        ),
    ];
    for (label, tables) in expected {
        let doc = labelled(&prepared_schema(), label);
        let d = check_invariants(label, &doc);
        let mut got: Vec<(String, Vec<String>)> =
            d.tables.iter().map(|&t| (doc.tables[t].name.clone(), d.table_columns(t).iter().map(|c| doc.tables[t].columns[*c].name.clone()).collect())).collect();
        got.sort();
        let mut want: Vec<(String, Vec<String>)> = tables.iter().map(|(t, cs)| (t.to_string(), cs.iter().map(|c| c.to_string()).collect())).collect();
        want.sort();
        assert_eq!(got, want, "{label}");
    }

    // Non-TPC-H uses.
    let dir = scratch("schema");
    let ddl = dir.join("schema.sql");
    std::fs::write(
        &ddl,
        "CREATE TABLE t (a integer NOT NULL, b integer NOT NULL, n integer, f boolean NOT NULL);\n\
         CREATE TABLE s (c integer NOT NULL, d integer NOT NULL, e numeric(10,2) NOT NULL);",
    )
    .unwrap();
    let case = |name: &str, sql: &str| {
        let doc = ok(translate(&ddl, sql, &[], name));
        let d = columns::analyze(&doc).unwrap();
        (doc, d)
    };
    let (t, s) = (0, 1);
    // Whole rows observed by DISTINCT (and the output), through a projection.
    let (doc, d) = case("distinct", "SELECT DISTINCT a, b FROM t");
    let distinct = doc.nodes.iter().position(|n| n.tag == "Distinct").unwrap();
    assert_eq!(d.columns[&(t, 1)].observed_by, [distinct, doc.root]);
    // An unused computed column of a derived table still reads its inputs (it is evaluated).
    let (doc, d) = case("derived", "SELECT x FROM (SELECT a AS x, b + 1 AS y FROM t) AS q");
    assert_eq!(d.table_columns(t), [0, 1]);
    assert!(d.columns[&(t, 1)].observed_by.is_empty() && d.columns[&(t, 0)].observed_by == [doc.root]);
    // A correlated scalar subquery: its output column is observed (a value), its condition columns are read.
    let (doc, d) = case("scalar", "SELECT a FROM t WHERE b = (SELECT c FROM s WHERE s.d = t.a)");
    let sub = doc.nodes.iter().position(|n| n.tag == "Subquery").unwrap();
    assert_eq!(d.columns[&(s, 0)].observed_by, [sub]);
    assert_eq!(d.table_columns(s), [0, 1]);
    // EXISTS: only cardinality; `SELECT *` of the subquery demands nothing by itself.
    let (_, d) = case("exists", "SELECT a FROM t WHERE EXISTS (SELECT * FROM s WHERE s.d = t.a)");
    assert_eq!((d.table_columns(t), d.table_columns(s)), (vec![0], vec![1]));
    // Rows counted, no column demanded: one NOT NULL column carries the row count.
    let (doc, d) = case("count", "SELECT COUNT(*) AS k FROM s");
    let src = columns::source_declaration(&doc, &d).unwrap();
    assert!(d.columns.is_empty() && src.tables[0].columns.len() == 1 && src.tables[0].columns[0].row_count_only);
    // A nullable column is delivered with its validity (declared nullability carried); a row-count carrier is NOT NULL.
    let (doc, d) = case("nullable", "SELECT COUNT(*) AS k FROM t WHERE n > 0");
    let src = columns::source_declaration(&doc, &d).unwrap();
    let n = &src.tables[0].columns[0];
    assert!(n.name == "n" && n.nullable && !n.row_count_only, "{n:?}");
    assert!(serde_json::to_value(n).unwrap()["nullable"] == true);
    assert!(serde_json::to_value(&src).unwrap().to_string().matches("nullable").count() == 1, "NOT NULL columns serialize without the field");
    // Representation limits are named binding refusals.
    let (doc, d) = case("bool", "SELECT a FROM t WHERE f");
    assert_eq!(columns::source_declaration(&doc, &d).unwrap_err().reason, BindingRefusalReason::UnbindableSourceType);
    std::fs::remove_dir_all(&dir).unwrap();
}
