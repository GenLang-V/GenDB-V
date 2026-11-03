//! Generator and fixed-text consistency checks (no Verus run; the generated files are checked by Verus in every
//! candidate crate and by `tests/verus_params_entry.rs`).

use super::binder_module::binder_module;
use super::candidate::{framework_check_files, ENTRY_SUBMODULES};
use super::params_module::{check_free_params, params_module, ArgumentAbi};
use super::source_module::{source_module, STATEMENT_SOURCE, STORAGE_SOURCE};
use super::*;
use crate::verus::FrameworkSource;
use gendb_frontend::params::{FreeParam, ParamDomain, ParamType, ParamValue};
use gendb_sqlspec::library::{self, CANDIDATE_MODULES};

fn column(ordinal: usize, name: &str, ty: DeclaredType, row_count_only: bool) -> DeclaredColumn {
    DeclaredColumn { ordinal, name: name.into(), ty, row_count_only, nullable: false }
}

/// Table id 1 `s` with non-contiguous columns of every kind but I64, then table id 0 `c` delivered only through a
/// `char(3)` row-count carrier (its relation has no column).
fn two_tables() -> DeclaredSource {
    DeclaredSource {
        tables: vec![
            DeclaredTable {
                table_id: 1,
                name: "s".into(),
                columns: vec![
                    column(0, "id", DeclaredType::Int4, false),
                    column(2, "x", DeclaredType::Numeric { precision: 10, scale: 2 }, false),
                    column(3, "d", DeclaredType::Date, false),
                    column(4, "tag", DeclaredType::Varchar { max_chars: 8 }, false),
                ],
            },
            DeclaredTable { table_id: 0, name: "c".into(), columns: vec![column(1, "k", DeclaredType::Bpchar { len: 3 }, true)] },
        ],
    }
}

/// Relations are projections onto the declared (non-carrier) columns, in ABI order; the carrier column only gives
/// the row count; the domain is decided per column with the declared SQL type.
#[test]
fn source_module_is_data_only() {
    let source = two_tables();
    source.check_deliverable(&[2, 6]).unwrap();
    let text = source_module(&source, &[2, 6], "fixture", &STATEMENT_SOURCE);
    for needle in [
        "pub t0_f1: Seq<i128>,",
        "pub t1_f0: TextView,",
        "pub t0_f3: TextCol,",
        "pub open spec fn source_cols_t0() -> Seq<nat> {\n    seq![0nat, 2, 3, 4]\n}",
        "pub open spec fn source_cols_t1() -> Seq<nat> {\n    Seq::<nat>::empty()\n}",
        "Seq::new(source_rows_t0(v) as nat, |i: int| seq![Val::Int(v.t0_f0[i] as int), Val::Num { coeff: v.t0_f1[i] as int, scale: 2 }, date32_val(v.t0_f2[i]), Val::Text(text_at(v.t0_f3, i))])",
        "Seq::new(source_rows_t1(v) as nat, |i: int| Seq::<Val>::empty())",
        "pub open spec fn source_rows_t1(v: SourceView) -> int {\n    v.t1_f0.offsets.len() - 1\n}",
        "&&& table_t0(v) == proj_all(db.tables[source_table_t0() as int], source_cols_t0())",
        "assert(schema_spec()[1].columns[2] == Column { ty: SqlType::Numeric { precision: 10, scale: 2 }, nullable: false }) by (compute);",
        "let b0_1 = decimal_column_in(s.t0_f1, 2, Column { ty: SqlType::Numeric { precision: 10, scale: 2 }, nullable: false });",
        "let b0_3 = text_column_in(&s.t0_f3, n0, Column { ty: SqlType::Varchar { max_chars: 8 }, nullable: false });",
        "crate::link::source::lemma_source_in_domain(db, source_table_t1(), source_cols_t1());",
    ] {
        assert!(text.contains(needle), "gendb_source lacks {needle}:\n{text}");
    }
    for forbidden in ["query_spec", "eval_", "fits_", "ordered_ok", "Capacity"] {
        assert!(!text.contains(forbidden), "gendb_source mentions {forbidden}");
    }
}

/// A nullable field carries its validity through the source module (view, row count, `or_null` rows, exact domain
/// helpers of the kinds used), the binder (a `Utf8` column with no offsets after the values) and the declaration
/// (`nullable: true`); a declaration of NOT NULL columns generates none of it, and its serialized form has no
/// `nullable` field.
#[test]
fn nullable_columns_carry_their_validity_through_the_generated_modules() {
    let nullable = |ordinal, name: &str, ty| DeclaredColumn { nullable: true, ..column(ordinal, name, ty, false) };
    let source = DeclaredSource {
        tables: vec![DeclaredTable {
            table_id: 0,
            name: "t".into(),
            columns: vec![nullable(0, "fy", DeclaredType::Int4), column(1, "name", DeclaredType::Text, false), nullable(2, "label", DeclaredType::Text)],
        }],
    };
    source.check_deliverable(&[3]).unwrap();
    let text = source_module(&source, &[3], "fixture", &STORAGE_SOURCE);
    for needle in [
        "pub open spec fn or_null(valid: u8, value: Val) -> Val {",
        "pub t0_f0: Seq<i32>,\n    pub t0_v0: Seq<u8>,",
        "pub t0_v2: &'static [u8],",
        "&&& v.t0_v0.len() == source_rows_t0(v)",
        "&&& v.t0_v2.len() == source_rows_t0(v)",
        "seq![or_null(v.t0_v0[i], Val::Int(v.t0_f0[i] as int)), Val::Text(text_at(v.t0_f1, i)), or_null(v.t0_v2[i], Val::Text(text_at(v.t0_f2, i)))]",
        "pub fn nullable_int32_column_in(c: &[i32], valid: &[u8], col: Column) -> (b: bool)",
        "pub fn nullable_text_column_in(c: &TextCol, valid: &[u8], n: usize, col: Column) -> (b: bool)",
        "let b0_0 = nullable_int32_column_in(s.t0_f0, s.t0_v0, Column { ty: SqlType::Int4, nullable: true });",
        "let b0_2 = nullable_text_column_in(&s.t0_f2, s.t0_v2, n0, Column { ty: SqlType::Text, nullable: true });",
        "assert(schema_spec()[0].columns[0] == Column { ty: SqlType::Int4, nullable: true }) by (compute);",
        "//   t0_f0 = fy (ordinal 0): SqlType::Int4, nullable (validity t0_v0).",
    ] {
        assert!(text.contains(needle), "gendb_source lacks {needle}:\n{text}");
    }
    assert!(!text.contains("nullable_decimal") && !text.contains("nullable_date32"), "only the helpers of the kinds used");
    let binder = binder_module(&source, "fixture", ENTRY_IDENTITY);
    for needle in [
        "pub open spec fn is_validity_column(c: Column) -> bool {\n    c is Utf8 && c->Utf8_offsets@.len() == 0\n}",
        "columns.len() == 5 && columns[0] is I32 && is_validity_column(columns[1]) && columns[2] is Utf8 && columns[3] is Utf8 && is_validity_column(columns[4])",
        "t0_v0: columns[1]->Utf8_bytes@",
        "t0_v2: columns[4]->Utf8_bytes@",
        "if s.t0_v0.len() != n0 {",
        "if s.t0_v2.len() != n0 {",
        "let s = SourceRef { t0_f0, t0_v0, t0_f1, t0_f2, t0_v2 };",
    ] {
        assert!(binder.contains(needle), "binder lacks {needle}:\n{binder}");
    }
    let declaration = super::declaration_module::declaration_module(&StorageName::new("t_all").unwrap(), &source, &[3]);
    assert!(declaration.contains("seq![Column { ty: SqlType::Int4, nullable: true }, Column { ty: SqlType::Text, nullable: false }, Column { ty: SqlType::Text, nullable: true }]"), "{declaration}");
    let serialized = serde_json::to_value(&source).unwrap();
    assert_eq!(serialized["tables"][0]["columns"][0]["nullable"], true);
    assert!(serialized["tables"][0]["columns"][1].get("nullable").is_none(), "NOT NULL: no field");
    assert_eq!(serde_json::from_value::<DeclaredSource>(serialized).unwrap(), source);

    // NOT NULL declarations generate none of it.
    let plain = two_tables();
    assert!(!plain.has_nullable());
    let (text, binder) = (source_module(&plain, &[2, 6], "fixture", &STATEMENT_SOURCE), binder_module(&plain, "fixture", ENTRY_IDENTITY));
    for forbidden in ["or_null", "nullable_", "_v0", "validity", "nullable: true"] {
        assert!(!text.contains(forbidden) && !binder.contains(forbidden), "{forbidden}");
    }
    assert!(!serde_json::to_string(&plain).unwrap().contains("nullable"));
}

#[test]
fn undeliverable_sources_are_refused() {
    let refusal = |source: &DeclaredSource| source.check_deliverable(&[2, 6]).unwrap_err().to_string();
    assert!(refusal(&DeclaredSource { tables: vec![] }).contains("no source table"));
    let mut bad = two_tables();
    bad.tables[0].columns[1].ordinal = 9;
    assert!(refusal(&bad).contains("ordinal 9 outside the table"));
    let mut bad = two_tables();
    bad.tables[1].columns.clear();
    assert!(refusal(&bad).contains("row count cannot be passed"));
    let mut bad = two_tables();
    bad.tables[0].table_id = 2;
    assert!(refusal(&bad).contains("outside the schema"));
    let mut bad = two_tables();
    bad.tables[0].columns[1].ty = DeclaredType::Numeric { precision: 39, scale: 0 };
    assert!(refusal(&bad).contains("precision 39 > 38"));
    assert_eq!(AssemblyError::Source("x".into()).failure_class(), "tool_failure");
}

/// Two source tables with their own row counts: every ABI column binds to its table-qualified field, each table's
/// row count comes from its own field 0 and every other field of that table is compared with it (never with
/// another table's count).
#[test]
fn binder_binds_every_table_with_its_own_row_count() {
    let field = |ty| column(0, "c", ty, false);
    let source = DeclaredSource {
        tables: vec![
            DeclaredTable {
                table_id: 0,
                name: "a".into(),
                columns: vec![field(DeclaredType::Text), field(DeclaredType::Numeric { precision: 12, scale: 2 }), field(DeclaredType::Date)],
            },
            DeclaredTable { table_id: 1, name: "b".into(), columns: vec![field(DeclaredType::Int8), field(DeclaredType::Varchar { max_chars: 4 })] },
        ],
    };
    let binder = binder_module(&source, "fixture", ENTRY_IDENTITY);
    for needle in [
        "use crate::gendb_source::{source_wf, SourceRef, SourceView, TextCol, TextView};",
        "columns.len() == 5 && columns[0] is Utf8 && columns[1] is I128 && columns[2] is I32 && columns[3] is I64 && columns[4] is Utf8",
        "t0_f0: TextView { offsets: columns[0]->Utf8_offsets@, bytes: columns[0]->Utf8_bytes@ }",
        "t0_f1: columns[1]->I128_0@",
        "t1_f0: columns[3]->I64_0@",
        "t1_f1: TextView { offsets: columns[4]->Utf8_offsets@, bytes: columns[4]->Utf8_bytes@ }",
        "let t1_f0 = match &columns[3] { Column::I64(s) => *s, _ => return None };",
        "let s = SourceRef { t0_f0, t0_f1, t0_f2, t1_f0, t1_f1 };",
        "let n0: usize = s.t0_f0.offsets.len() - 1;",
        "if !text_offsets_ok(&s.t0_f0, n0)",
        "if s.t0_f1.len() != n0",
        "if s.t0_f2.len() != n0",
        "let n1: usize = s.t1_f0.len();",
        "if !text_offsets_ok(&s.t1_f1, n1)",
    ] {
        assert!(binder.contains(needle), "binder lacks {needle}:\n{binder}");
    }
    // Table 1 is never compared with table 0's row count.
    assert!(!binder.contains("t1_f1, n0") && !binder.contains("s.t1_f0.len() != n0"));
}

fn free(index: u32, slot: usize, ty: ParamType, min: ParamValue, max: ParamValue) -> FreeParam {
    FreeParam { index, slot, ty, domain: ParamDomain::Range { min, max } }
}

/// `$1` numeric and `$3` integer free with `$2` fixed: dense slots 0 and 1 in ascending index order; the argument of
/// slot 1 is `$3`'s, never `$2`'s.
#[test]
fn params_module_maps_dense_slots() {
    let params = [
        free(1, 0, ParamType::Numeric { precision: 10, scale: 2 }, ParamValue::Num(-500), ParamValue::Num(99_999)),
        free(3, 1, ParamType::Int4, ParamValue::Int(-100), ParamValue::Int(100)),
    ];
    check_free_params(&params, ArgumentAbi::SharedParamArg).unwrap();
    let text = params_module(&params, "fixture", ArgumentAbi::SharedParamArg);
    for needle in [
        "// Slot 0 = $1 numeric(10,2) (ABI argument 0 = ParamArg::Num).",
        "// Slot 1 = $3 integer (ABI argument 1 = ParamArg::Int).",
        "pub p0: i128,",
        "pub p1: i64,",
        "seq![Literal::Num { coeff: self.p0 as int, scale: 2 }, Literal::Int { v: self.p1 as int, kind: IntKind::Int4 }]",
        "if args.len() == 2 && arg_literal_0(args[0]) is Some && arg_literal_1(args[1]) is Some {",
        "if !(-500i128 <= p.p0 && p.p0 <= 99999i128) {",
        "if !(-100i64 <= p.p1 && p.p1 <= 100i64) {",
        "let p1 = match args[1] {\n        ParamArg::Int(x) => x,",
    ] {
        assert!(text.contains(needle), "gendb_params lacks {needle}:\n{text}");
    }
    let concrete = params_module(&[], "concrete", ArgumentAbi::SharedParamArg);
    assert!(concrete.contains("if args.len() == 0 {") && concrete.contains("pub struct Params {\n}"));
    let gap = [
        free(1, 0, ParamType::Int4, ParamValue::Int(0), ParamValue::Int(1)),
        free(3, 2, ParamType::Int4, ParamValue::Int(0), ParamValue::Int(1)),
    ];
    assert!(check_free_params(&gap, ArgumentAbi::SharedParamArg).unwrap_err().to_string().contains("dense"));
    let unordered = [
        free(3, 0, ParamType::Int4, ParamValue::Int(0), ParamValue::Int(1)),
        free(1, 1, ParamType::Int4, ParamValue::Int(0), ParamValue::Int(1)),
    ];
    assert!(check_free_params(&unordered, ArgumentAbi::SharedParamArg).unwrap_err().to_string().contains("ascending"));
    let mistyped = [free(1, 0, ParamType::Date, ParamValue::Int(0), ParamValue::Int(1))];
    assert!(check_free_params(&mistyped, ArgumentAbi::SharedParamArg).is_err());
    let empty = [free(1, 0, ParamType::Date, ParamValue::Date { y: 2000, m: 2, d: 1 }, ParamValue::Date { y: 2000, m: 1, d: 31 })];
    assert!(check_free_params(&empty, ArgumentAbi::SharedParamArg).unwrap_err().to_string().contains("empty"));
}

/// A text slot next to an integer slot (query entry v4): `QueryArg`, a borrowed byte field viewed as `Literal::Text`,
/// the verified NUL decision instead of the literal evaluator. v3 candidates (`ParamArg`) refuse text parameters, and
/// a text parameter with bounds is mistyped.
#[test]
fn params_module_binds_text_arguments() {
    let text_slot = FreeParam { index: 1, slot: 0, ty: ParamType::Text, domain: ParamDomain::AllText };
    let params = [text_slot.clone(), free(2, 1, ParamType::Int4, ParamValue::Int(1), ParamValue::Int(50))];
    check_free_params(&params, ArgumentAbi::QueryArg).unwrap();
    let text = params_module(&params, "fixture", ArgumentAbi::QueryArg);
    for needle in [
        "use crate::gendb_arguments::QueryArg;",
        "// Slot 0 = $1 text (ABI argument 0 = QueryArg::Text).",
        "pub p0: &'static [u8],",
        "seq![Literal::Text(self.p0@), Literal::Int { v: self.p1 as int, kind: IntKind::Int4 }]",
        "pub open spec fn arg_literal_0(a: QueryArg) -> Option<Literal> {\n    match a {\n        QueryArg::Text(x) => Some(Literal::Text(x@)),",
        "fn text_arg_ok(b: &[u8]) -> (r: bool)\n    ensures r == text_ok(b@),",
        "    assert(ps[0] == Literal::Text(p.p0@));\n    if !text_arg_ok(p.p0) {\n        return false;\n    }",
        "if !(1i64 <= p.p1 && p.p1 <= 50i64) {",
        "pub fn bind_params(args: &[QueryArg]) -> (r: Option<Params>)",
        "let p0 = match args[0] {\n        QueryArg::Text(x) => x,",
    ] {
        assert!(text.contains(needle), "gendb_params lacks {needle}:\n{text}");
    }
    assert!(!text.contains("ParamArg") && !text.contains("ELiteral::Text"));
    let numeric_only = [free(1, 0, ParamType::Int4, ParamValue::Int(1), ParamValue::Int(50))];
    assert!(!params_module(&numeric_only, "fixture", ArgumentAbi::QueryArg).contains("text_arg_ok"), "no text helper without a text slot");
    assert!(check_free_params(&params, ArgumentAbi::SharedParamArg).unwrap_err().to_string().contains("QueryArg"));
    let bounded_text = [free(1, 0, ParamType::Text, ParamValue::Text("a".into()), ParamValue::Text("b".into()))];
    assert!(check_free_params(&bounded_text, ArgumentAbi::QueryArg).is_err());
    // The existing author-source rules cover the new argument type: an author cannot add methods to it or build a
    // byte slice from a host pointer itself (only the trusted shim does).
    let rules = |text: &str| scan_source("agent/mod.rs", text).into_iter().map(|f| f.rule).collect::<Vec<_>>();
    assert!(rules("verus! {\nimpl crate::gendb_arguments::QueryArg {\n}\n}\n").contains(&rule::IMPL_OWNERSHIP));
    assert!(rules("verus! {\nfn f(p: *const u8) -> &'static [u8] { unsafe { std::slice::from_raw_parts(p, 1) } }\n}\n").contains(&rule::UNSAFE));
}

/// Every submodule `gendb_entry.rs` declares is written (fixed or generated), the entry names its identity, and the
/// Verus worker bound equals the host's.
#[test]
fn fixed_entry_texts_are_consistent() {
    let declared: Vec<&str> = ENTRY_SOURCE.lines().filter_map(|l| l.strip_prefix("pub mod ").and_then(|r| r.strip_suffix(';'))).collect();
    assert_eq!(declared, ENTRY_SUBMODULES);
    assert!(ENTRY_SOURCE.contains(ENTRY_IDENTITY));
    let parallel = include_str!("../../obligations/gendb_entry/parallel.rs");
    assert!(parallel.contains(&format!("pub const MAX_WORKERS: usize = {};", gendb_runtime::abi::MAX_WORKERS)));
}

/// The `link` names the fixed entry texts and the generated source module use: the fixed definitions, plus one
/// checked lemma. Anything else would make an optional toolkit item part of the claim unnoticed.
#[test]
fn claim_uses_only_the_fixed_link_definitions() {
    let source = source_module(&two_tables(), &[2, 6], "fixture", &STATEMENT_SOURCE);
    let texts = [
        ENTRY_SOURCE,
        include_str!("../../obligations/gendb_entry/work.rs"),
        include_str!("../../obligations/gendb_entry/source_check.rs"),
        include_str!("../../obligations/gendb_entry/layout.rs"),
        include_str!("../../obligations/gendb_entry/parallel.rs"),
        include_str!("../../obligations/gendb_entry/runtime.rs"),
        source.as_str(),
    ];
    let mut used: Vec<String> = texts.iter().flat_map(|t| link_names(t)).collect();
    used.sort();
    used.dedup();
    for expected in ["link::query::view_rows", "link::query::proj_all", "link::source::rows_in_columns", "link::source::lemma_source_in_domain"] {
        assert!(used.iter().any(|u| u == expected), "scanner missed {expected}: {used:?}");
    }
    for name in &used {
        assert!(FIXED_LINK_DEFINITIONS.contains(&name.as_str()) || name == "link::source::lemma_source_in_domain", "the claim uses {name}");
    }
    // Each fixed definition is defined in the candidate library's link module.
    let link: String = library::module_files(CANDIDATE_MODULES).iter().filter(|f| f.path.starts_with("link")).map(|f| f.text).collect();
    for item in FIXED_LINK_DEFINITIONS {
        let name = item.rsplit("::").next().unwrap();
        assert!(link.contains(&format!("pub open spec fn {name}(")) || link.contains(&format!("pub struct {name} ")), "{item} is not defined");
    }
}

/// `link::<module>::<name>` for every `crate::link::` path in `text` (`use` lists expanded).
fn link_names(text: &str) -> Vec<String> {
    let mut names = Vec::new();
    for (at, _) in text.match_indices("crate::link::") {
        let rest = &text[at + "crate::link::".len()..];
        let Some((module, tail)) = rest.split_once("::") else { continue };
        let items: Vec<&str> = match tail.strip_prefix('{') {
            Some(list) => list.split('}').next().unwrap_or("").split(',').map(str::trim).collect(),
            None => vec![tail.split(|c: char| !(c.is_alphanumeric() || c == '_')).next().unwrap_or("")],
        };
        names.extend(items.into_iter().filter(|i| !i.is_empty()).map(|i| format!("link::{module}::{i}")));
    }
    names
}

/// The framework-only check crate drops the shim and the `agent` declaration and keeps only the entry's submodules;
/// every other file is unchanged.
#[test]
fn framework_check_crate_has_no_author_module() {
    let file = |path: &str, text: &str| FrameworkSource { path: path.into(), text: text.into() };
    let framework = vec![
        file("lib.rs", "// root\npub mod query;\npub mod gendb_entry;\npub mod agent;\nmod gendb_shim;\n"),
        file("query.rs", "// query"),
        file("gendb_entry.rs", ENTRY_SOURCE),
        file("gendb_shim.rs", "// shim"),
    ];
    let check = framework_check_files(&framework);
    let paths: Vec<&str> = check.iter().map(|f| f.path.as_str()).collect();
    assert_eq!(paths, ["lib.rs", "query.rs", "gendb_entry.rs"]);
    assert_eq!(check[0].text, "// root\npub mod query;\npub mod gendb_entry;\n");
    assert_eq!(check[1].text, "// query");
    assert!(check[2].text.contains("pub mod binder;\npub mod layout;") && !check[2].text.contains("abi_query"));
}

// ---------------------------------------------------------------------------------------- storage and query crates v4

use gendb_frontend::ast::{decode, Translation};
use gendb_frontend::columns::{analyze, source_declaration};
use gendb_frontend::params::Instance;
use crate::verus::{rule, scan_source, RefusalFinding};
use gendb_registry::{
    author_definition, closure_definition, definitions_for, ConstraintMode, CrateKind, Origin, Presence, DEFINITIONS, STORED_PARTS_SOURCE,
};
use std::collections::{BTreeMap, BTreeSet};

/// `SELECT c FROM t` over `t(c integer, d date)` (table 0) and `u(e bigint)` (table 1), both NOT NULL.
fn small_statement() -> Instance {
    small_statement_with(r#""constraints": []"#)
}

/// [`small_statement`] whose dataset declares `PRIMARY KEY (c)` on `t` (`constraints`: `t`'s AST constraints field).
fn small_constrained_statement() -> Instance {
    small_statement_with(
        r#""constraints": [{"kind": "key", "name": null, "primary": true, "columns": [0], "nulls_distinct": true, "deferrable": false, "initially_deferred": false}]"#,
    )
}

fn small_statement_with(constraints: &str) -> Instance {
    let doc = r#"{"format": "gendb-sql-ast-v1", "status": "ok", "frontend": {"identity": "unit"}, "sql": "SELECT c FROM t",
        "schema": {"tables": [
            {"name": "t", "columns": [{"name": "c", "type": {"kind": "int4"}, "nullable": false}, {"name": "d", "type": {"kind": "date"}, "nullable": false}], CONSTRAINTS},
            {"name": "u", "columns": [{"name": "e", "type": {"kind": "int8"}, "nullable": false}]}]},
        "output": {"names": ["c"], "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}], "pg_types": ["int4"]},
        "root": 3, "nodes": [
          {"id": 0, "tag": "Table", "table": 0, "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}, {"type": {"kind": "date"}, "nullable": false, "dscale": null}]},
          {"id": 1, "tag": "Col", "index": 0, "type": {"type": {"kind": "int4"}, "nullable": false, "dscale": null}},
          {"id": 2, "tag": "Project", "exprs": [1], "input": 0, "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}]},
          {"id": 3, "tag": "OrderedQuery", "body": 2, "keys": [], "limit": null, "offset": 0}]}"#;
    let Translation::Ok(doc) = decode(&doc.replace("CONSTRAINTS", constraints)).unwrap() else { panic!("refused") };
    Instance::concrete(&doc).unwrap()
}

struct SmallCrates {
    name: StorageName,
    storage: Vec<FrameworkSource>,
    query: Vec<FrameworkSource>,
}

/// Storage `t_all` of both columns of `t`, and the query crate of `small_statement` reading it, with author files.
fn small_crates() -> SmallCrates {
    small_crates_of(&small_statement())
}

/// The storage crate of [`small_crates`] opting in to the declared constraints of [`small_constrained_statement`]
/// (storage entry v2), with the same author files.
fn small_v2_storage() -> Vec<FrameworkSource> {
    small_storage_of(&small_constrained_statement(), true)
}

/// Storage `t_all` (both columns of `t`) over the schema of `inst`, opting in when `uses_declared_constraints`, with
/// its interface and builder author files.
fn small_storage_of(inst: &Instance, uses_declared_constraints: bool) -> Vec<FrameworkSource> {
    let name = StorageName::new("t_all").unwrap();
    let declaration = DeclaredSource::for_storage(&inst.doc.tables, &BTreeMap::from([(0, BTreeSet::from([0, 1]))])).unwrap();
    let mut storage = storage_crate_files(&inst.doc.tables, &name, &declaration, uses_declared_constraints).unwrap();
    storage.extend([
        FrameworkSource { path: "stores/t_all/interface/mod.rs".into(), text: "// interface".into() },
        FrameworkSource { path: "builder/mod.rs".into(), text: "// builder/mod.rs".into() },
    ]);
    storage
}

/// [`small_crates`] for the statement instance `inst` (the storage crate is the unconstrained one either way).
fn small_crates_of(inst: &Instance) -> SmallCrates {
    let name = StorageName::new("t_all").unwrap();
    let declaration = DeclaredSource::for_storage(&inst.doc.tables, &BTreeMap::from([(0, BTreeSet::from([0, 1]))])).unwrap();
    let interface = vec![FrameworkSource { path: "stores/t_all/interface/mod.rs".into(), text: "// interface".into() }];
    let author = |path: &str| FrameworkSource { path: path.into(), text: format!("// {path}") };
    let mut storage = storage_crate_files(&small_statement().doc.tables, &name, &declaration, false).unwrap();
    storage.extend([interface[0].clone(), author("builder/mod.rs")]);
    let delivered = source_declaration(&inst.doc, &analyze(&inst.doc).unwrap()).unwrap();
    let uses = [StorageUse { name: &name, declaration: &declaration, interface: &interface }];
    let mut query = query_crate_files(inst, &delivered, &uses, "unit").unwrap();
    query.push(author("agent/mod.rs"));
    SmallCrates { name, storage, query }
}

/// The engine crate over the constrained schema of [`small_constrained_statement`] reading storage `t_all` (the same
/// declaration and interface as [`small_crates`]), with the embedded toolkit and the author's `agent/mod.rs`.
fn small_engine() -> Vec<FrameworkSource> {
    let inst = small_constrained_statement();
    let name = StorageName::new("t_all").unwrap();
    let declaration = DeclaredSource::for_storage(&inst.doc.tables, &BTreeMap::from([(0, BTreeSet::from([0, 1]))])).unwrap();
    let interface = vec![FrameworkSource { path: "stores/t_all/interface/mod.rs".into(), text: "// interface".into() }];
    let uses = [StorageUse { name: &name, declaration: &declaration, interface: &interface }];
    let mut engine = engine_crate_files(&inst.doc.tables, &uses, "unit").unwrap();
    engine.push(FrameworkSource { path: "agent/mod.rs".into(), text: "// agent/mod.rs".into() });
    engine
}

/// The registry describes the assembled crates exactly: every file of a crate belongs to a definition of its kind and
/// constraint mode, every definition of a kind and mode is in the crate, the files the registry marks shared are the
/// storage's closure, and every single-file source it names is the text the crates of its mode carry.
#[test]
fn registry_matches_the_assembled_crates() {
    let c = small_crates();
    let declared = small_crates_of(&small_constrained_statement());
    let v2_storage = small_v2_storage();
    let engine = small_engine();
    let storage = c.name.as_str();
    let crates = [
        (CrateKind::Storage, ConstraintMode::Unconstrained, &c.storage),
        (CrateKind::Query, ConstraintMode::Unconstrained, &c.query),
        (CrateKind::Query, ConstraintMode::Declared, &declared.query),
        (CrateKind::Storage, ConstraintMode::Declared, &v2_storage),
        (CrateKind::Engine, ConstraintMode::Declared, &engine),
    ];
    for (kind, mode, files) in crates {
        for f in files.iter() {
            assert!(definitions_for(kind, mode).any(|d| d.covers(&f.path, storage)), "{kind:?} {mode:?}: {} is in no definition", f.path);
        }
        for d in definitions_for(kind, mode) {
            assert!(files.iter().any(|f| d.covers(&f.path, storage)), "{kind:?} {mode:?}: definition {} has no file", d.name);
        }
    }
    let shared: BTreeSet<&str> = c.storage.iter().filter(|f| closure_definition(&f.path, storage).is_some()).map(|f| f.path.as_str()).collect();
    assert!(shared.contains("stores/t_all/interface/mod.rs") && shared.contains("gendb_entry/stored.rs") && shared.contains("schema.rs"));
    for excluded in ["lib.rs", "stores.rs", "gendb_entry.rs", "gendb_source.rs", "gendb_entry/storage.rs", "builder/mod.rs"] {
        assert!(!shared.contains(excluded), "{excluded} is not shared");
    }
    assert_eq!(compare_storage_closure(&c.storage, &c.query, &c.name), Ok(()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    for d in DEFINITIONS {
        let (Origin::Source { path }, Some(crate_path)) = (d.origin, d.crate_path) else { continue };
        // Optional definitions are in only some crates (tests/registry_optional_definitions.rs checks them).
        if !path.ends_with(".rs") || path.contains(',') || crate_path.contains("**") || matches!(d.presence, Presence::Optional(_)) {
            continue;
        }
        let source = std::fs::read_to_string(root.join(path)).unwrap_or_else(|e| panic!("{}: {path}: {e}", d.name));
        let unconstrained = d.modes.contains(&ConstraintMode::Unconstrained);
        let query = if unconstrained { &c.query } else { &declared.query };
        let storage = if unconstrained { &c.storage } else { &v2_storage };
        let kind = match d.presence {
            Presence::StorageOnly => storage,
            Presence::EngineOnly => &engine,
            _ => query,
        };
        assert_eq!(text_of(kind, crate_path), source, "{}: the crates do not carry {path}", d.name);
    }
    assert_eq!(text_of(&c.storage, "gendb_entry/stored.rs"), STORED_PARTS_SOURCE);
}

/// The statement check crate keeps every storage-independent file of the query crate byte for byte; only its root and
/// the entry root are reduced (no storages, author module, shim or entry items).
#[test]
fn statement_check_files_are_the_query_crate_statement_files() {
    let c = small_crates();
    let check = query_statement_check_files(&small_statement(), "unit").unwrap();
    let paths: BTreeSet<&str> = check.iter().map(|f| f.path.as_str()).collect();
    assert_eq!(paths.len(), check.len(), "unique paths");
    for f in &check {
        match f.path.as_str() {
            "lib.rs" | "gendb_entry.rs" => {}
            path => assert_eq!(f.text, text_of(&c.query, path), "{path} differs from the query crate"),
        }
    }
    let not_kept: Vec<&str> = c.query.iter().map(|f| f.path.as_str()).filter(|p| !paths.contains(p)).collect();
    assert_eq!(not_kept, ["stores.rs", "stores/t_all/mod.rs", "stores/t_all/declaration.rs", "stores/t_all/interface/mod.rs", "gendb_entry/stores.rs", "agent/mod.rs"]);
    let root = text_of(&check, "lib.rs");
    assert!(root.contains("pub mod schema;\npub mod query;\npub mod gendb_params;\npub mod gendb_abi;\npub mod gendb_arguments;\npub mod gendb_entry;\n"), "{root}");
    let root_modules: Vec<&str> = root.lines().filter_map(|l| l.trim_start_matches("pub ").strip_prefix("mod ")?.strip_suffix(';')).collect();
    for absent in ["stores", "agent", "gendb_shim"] {
        assert!(!root_modules.contains(&absent), "{absent}: {root}");
    }
    let entry = text_of(&check, "gendb_entry.rs");
    let declared: Vec<&str> = entry.lines().filter_map(|l| l.strip_prefix("pub mod ")?.strip_suffix(';')).collect();
    assert_eq!(declared, ["runtime", "parallel", "layout", "work", "source_check", "stored", "results"]);
    assert!(!paths.contains("gendb_constraints.rs") && !root.contains("gendb_constraints"), "no declared constraints, no module");
    // Under declared constraints the check crate also carries the query crate's gendb_constraints.rs (so the preflight
    // proves lemma_declared_schema), declared in its root; its other statement files are unchanged.
    let constrained = small_crates_of(&small_constrained_statement());
    let constrained_check = query_statement_check_files(&small_constrained_statement(), "unit").unwrap();
    assert_eq!(text_of(&constrained_check, "gendb_constraints.rs"), text_of(&constrained.query, "gendb_constraints.rs"));
    assert!(text_of(&constrained_check, "lib.rs").contains("pub mod schema;\npub mod gendb_constraints;\npub mod query;\n"));
    assert!(text_of(&constrained_check, "lib.rs").contains(QUERY_ENTRY_V5_IDENTITY));
    for f in check.iter().filter(|f| f.path != "lib.rs") {
        assert_eq!(text_of(&constrained_check, &f.path), f.text, "{}", f.path);
    }
}

/// The entry is chosen by the instance: v4 and no `gendb_constraints.rs` without declared constraints (the crate is the
/// one assembled before constraints could be declared), v5 with the generated module, declared in the root, when a
/// table declares one. The column schema, statement, storage modules and closure are the same in both crates, so the
/// unconstrained storage composes with the constrained query by the unchanged rule.
#[test]
fn declared_constraints_select_entry_v5_and_carry_their_module() {
    let (plain, declared) = (small_crates(), small_crates_of(&small_constrained_statement()));
    assert_eq!(query_entry(&small_statement()), QUERY_ENTRY_V4);
    assert_eq!(query_entry(&small_constrained_statement()), QUERY_ENTRY_V5);
    assert_eq!(text_of(&plain.query, "gendb_entry.rs"), QUERY_ENTRY_SOURCE);
    assert_eq!(text_of(&declared.query, "gendb_entry.rs"), QUERY_ENTRY_V5_SOURCE);
    assert!(!plain.query.iter().any(|f| f.path == "gendb_constraints.rs") && !text_of(&plain.query, "lib.rs").contains("gendb_constraints"));
    let module = text_of(&declared.query, "gendb_constraints.rs");
    assert!(module.contains("pub open spec fn declared_db(db: Database) -> Database") && module.contains("primary: true"), "{module}");
    assert!(text_of(&declared.query, "lib.rs").contains("pub mod schema;\npub mod gendb_constraints;\npub mod query;\n"));
    let differing: Vec<&str> = declared.query.iter().map(|f| f.path.as_str()).filter(|p| plain.query.iter().all(|f| f.path != *p || text_of(&plain.query, p) != text_of(&declared.query, p))).collect();
    assert_eq!(differing, ["lib.rs", "gendb_constraints.rs", "gendb_entry.rs", "gendb_entry/stores.rs"], "only the root, module, entry and the stores header differ");
    assert_eq!(compare_storage_closure(&plain.storage, &declared.query, &plain.name), Ok(()));
    assert_eq!(check_storage_composition(&plain.storage, &declared.query, &plain.name), Ok(()));
}

/// Drift guard: the query entry v5 is the entry v4 with exactly the documented changes: its own header comment, the
/// two imports of the hypothesis and `bound_db`'s doc comment and conjunct. Everything else, the claim included, is
/// the v4 text byte for byte.
#[test]
fn query_entry_v5_is_v4_plus_the_declared_hypothesis() {
    let body = |entry: &'static str| &entry[entry.find("use vstd::prelude::*;").expect("an import")..];
    let expected = body(QUERY_ENTRY_SOURCE)
        .replacen(
            "use crate::schema::schema_spec;\n",
            "use crate::schema::schema_spec;\nuse crate::gendb_constraints::declared_db;\nuse crate::spec::constraints::constraints_hold;\n",
            1,
        )
        .replacen(
            "/// `db` is a database of the schema, in the semantics' input domain, whose stored relations the parts of every\n\
             /// storage use represent.\n",
            "/// `db` is a database of the schema, in the semantics' input domain, satisfying the declared integrity constraints\n\
             /// (`constraints_hold(declared_db(db))`: over all of `db`'s tables and columns), whose stored relations the parts of\n\
             /// every storage use represent.\n",
            1,
        )
        .replacen("    &&& db_wf(db)\n    &&& stored_ok(sv, db)\n", "    &&& db_wf(db)\n    &&& constraints_hold(declared_db(db))\n    &&& stored_ok(sv, db)\n", 1);
    assert_eq!(body(QUERY_ENTRY_V5_SOURCE), expected);
    assert_ne!(expected, body(QUERY_ENTRY_SOURCE), "every documented change applied");
    // Each entry names only its own identity (records check the identity by containment).
    assert!(QUERY_ENTRY_V5_SOURCE.contains(QUERY_ENTRY_V5_IDENTITY) && !QUERY_ENTRY_V5_SOURCE.contains(QUERY_ENTRY_IDENTITY));
    assert!(!QUERY_ENTRY_SOURCE.contains(QUERY_ENTRY_V5_IDENTITY));
}

/// The storage crate opting in is the v1 crate with the module, the entry v2 and its identity in generated headers; its
/// closure is the v1 crate's byte for byte, and without the opt-in the crate is the same in every constraint mode. The
/// opt-in in a run without declarations is refused by name, before any file is written.
#[test]
fn storage_opt_in_selects_entry_v2_and_keeps_the_closure() {
    let (plain, v2) = (small_crates().storage, small_v2_storage());
    assert_eq!(storage_entry(false), STORAGE_ENTRY_V1);
    assert_eq!(storage_entry(true), STORAGE_ENTRY_V2);
    let pairs = |files: &[FrameworkSource]| -> Vec<(String, String)> { files.iter().map(|f| (f.path.clone(), f.text.clone())).collect() };
    assert_eq!(pairs(&small_storage_of(&small_constrained_statement(), false)), pairs(&plain), "without the opt-in: the v1 crate in every mode");
    assert_eq!(text_of(&v2, "gendb_entry.rs"), STORAGE_ENTRY_V2_SOURCE);
    assert_eq!(text_of(&v2, "gendb_constraints.rs"), text_of(&small_crates_of(&small_constrained_statement()).query, "gendb_constraints.rs"));
    assert!(text_of(&v2, "lib.rs").contains("pub mod schema;\npub mod gendb_constraints;\npub mod stores;\n") && text_of(&v2, "lib.rs").contains(STORAGE_ENTRY_V2_IDENTITY));
    let differing: Vec<&str> =
        v2.iter().map(|f| f.path.as_str()).filter(|p| plain.iter().all(|f| f.path != *p || text_of(&plain, p) != text_of(&v2, p))).collect();
    assert_eq!(differing, ["lib.rs", "gendb_constraints.rs", "gendb_source.rs", "gendb_entry.rs", "gendb_entry/binder.rs", "gendb_entry/storage.rs"]);
    for header in ["gendb_source.rs", "gendb_entry/binder.rs", "gendb_entry/storage.rs"] {
        assert_eq!(text_of(&v2, header).replace(STORAGE_ENTRY_V2_IDENTITY, STORAGE_ENTRY_IDENTITY), text_of(&plain, header), "{header}: only the header names the entry");
    }
    let name = StorageName::new("t_all").unwrap();
    assert_eq!(storage_closure(&plain, &name), storage_closure(&v2, &name));
    let declared_query = small_crates_of(&small_constrained_statement()).query;
    assert_eq!(check_storage_composition(&v2, &declared_query, &name), Ok(()));
    let inst = small_statement();
    let declaration = DeclaredSource::for_storage(&inst.doc.tables, &BTreeMap::from([(0, BTreeSet::from([0, 1]))])).unwrap();
    let refused = storage_crate_files(&inst.doc.tables, &name, &declaration, true).unwrap_err();
    assert_eq!(refused.failure_class(), "refusal");
    assert!(refused.to_string().starts_with("declared_constraints_unavailable: storage t_all sets uses_declared_constraints"), "{refused}");
}

/// Drift guard: the storage entry v2 is the entry v1 with exactly the documented changes: its own header comment, the
/// two imports of the hypothesis, `source_witnessed`, the precondition of `abi_build_storage`, and the declared
/// constraints as one more premise (with doc wording) of both theorems. Everything else is the v1 text byte for byte.
#[test]
fn storage_entry_v2_is_v1_plus_the_declared_hypothesis() {
    let body = |entry: &'static str| &entry[entry.find("use vstd::prelude::*;").expect("an import")..];
    let expected = body(STORAGE_ENTRY_SOURCE)
        .replacen(
            "use crate::spec::typing::db_wf;\n",
            "use crate::spec::typing::db_wf;\nuse crate::gendb_constraints::declared_db;\nuse crate::spec::constraints::constraints_hold;\n",
            1,
        )
        .replacen(
            "/// Fixed builder contract.",
            "/// Some full database of the schema, in the semantics' input domain and satisfying the declared integrity constraints\n\
             /// (`constraints_hold(declared_db(db))`: over all of its tables and columns), delivers `v` under the source binding.\n\
             /// The builder may use the constraints only through such a witness, by row position and delivered column.\n\
             pub open spec fn source_witnessed(v: SourceView) -> bool {\n    exists|db: Database|\n        db.schema == schema_spec() && \
             db_wf(db) && constraints_hold(declared_db(db)) && #[trigger] source_columns_are_tables(v, db)\n}\n\n/// Fixed builder contract.",
            1,
        )
        .replacen(
            "    ensures storage_build_meets(columns@, workers, r),\n",
            "    requires column_source(columns@) is Some ==> source_witnessed(delivered_source(columns@)),\n    ensures storage_build_meets(columns@, workers, r),\n",
            1,
        )
        .replacen("/// domain whose tables the delivered columns are (the trusted source binding).", "/// domain satisfying the declared constraints whose tables the delivered columns are (the trusted source binding).", 1)
        .replacen(
            "/// On the real source tables the build never reports `InvalidInput`: the delivered columns of a `db_wf` database are\n\
             /// in the declared column domain.",
            "/// On the real source tables the build never reports `InvalidInput`: the delivered columns of a `db_wf` database\n\
             /// satisfying the declared constraints are in the declared column domain.",
            1,
        )
        .replace("        db_wf(db),\n        source_columns_are_tables", "        db_wf(db),\n        constraints_hold(declared_db(db)),\n        source_columns_are_tables");
    assert_eq!(body(STORAGE_ENTRY_V2_SOURCE), expected);
    assert_eq!(expected.matches("constraints_hold(declared_db(db)),\n").count(), 2, "both theorems take the premise");
    // Each entry names only its own identity (records check the identity by containment).
    assert!(STORAGE_ENTRY_V2_SOURCE.contains(STORAGE_ENTRY_V2_IDENTITY) && !STORAGE_ENTRY_V2_SOURCE.contains(STORAGE_ENTRY_IDENTITY));
    assert!(!STORAGE_ENTRY_SOURCE.contains(STORAGE_ENTRY_V2_IDENTITY));
}

fn text_of<'a>(files: &'a [FrameworkSource], path: &str) -> &'a str {
    &files.iter().find(|f| f.path == path).unwrap_or_else(|| panic!("{path} missing")).text
}

/// The public names the two entry roots define (functions, types, constants, re-exports; `pub` and `pub(..)`).
fn public_names(entry: &str) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for line in entry.lines() {
        // `pub(..)` items of an entry root are visible to the whole crate as well.
        let restricted = line.strip_prefix("pub(").and_then(|r| r.split_once(") ")).map(|(_, rest)| rest);
        let Some(rest) = line.strip_prefix("pub ").or(restricted) else { continue };
        let words: Vec<&str> = rest.split(|c: char| !(c.is_alphanumeric() || c == '_')).filter(|w| !w.is_empty()).collect();
        let name = match words.as_slice() {
            ["mod", ..] => continue,
            ["use", path @ ..] => path.last().copied(),
            _ => words.iter().find(|w| !matches!(**w, "open" | "closed" | "spec" | "proof" | "fn" | "struct" | "enum" | "const")).copied(),
        };
        names.insert(name.expect("named item").to_string());
    }
    names
}

/// The storage entry and the query entries v4 and v5 share no public name with each other's crate kind, so interface
/// code that names an item of one entry root fails to compile in the other crate; each declares exactly the
/// submodules its assembly writes.
#[test]
fn entry_roots_are_disjoint_and_complete() {
    for storage_entry in [STORAGE_ENTRY_SOURCE, STORAGE_ENTRY_V2_SOURCE] {
        let storage = public_names(storage_entry);
        for query_entry in [QUERY_ENTRY_SOURCE, QUERY_ENTRY_V5_SOURCE] {
            let query = public_names(query_entry);
            assert!(storage.contains("abi_build_storage") && query.contains("abi_query") && query.contains("Answer"), "{storage:?} {query:?}");
            assert_eq!(storage.intersection(&query).collect::<Vec<_>>(), Vec::<&String>::new());
        }
    }
    assert_eq!(public_names(QUERY_ENTRY_SOURCE), public_names(QUERY_ENTRY_V5_SOURCE), "v5 adds no public name");
    let mut v2_names = public_names(STORAGE_ENTRY_SOURCE);
    v2_names.insert("source_witnessed".into());
    assert_eq!(public_names(STORAGE_ENTRY_V2_SOURCE), v2_names, "v2 adds exactly source_witnessed");
    let (c, declared, v2) = (small_crates(), small_crates_of(&small_constrained_statement()), small_v2_storage());
    for (entry, files, identity) in [
        (STORAGE_ENTRY_SOURCE, &c.storage, STORAGE_ENTRY_IDENTITY),
        (STORAGE_ENTRY_V2_SOURCE, &v2, STORAGE_ENTRY_V2_IDENTITY),
        (QUERY_ENTRY_SOURCE, &c.query, QUERY_ENTRY_IDENTITY),
        (QUERY_ENTRY_V5_SOURCE, &declared.query, QUERY_ENTRY_V5_IDENTITY),
    ] {
        for module in entry.lines().filter_map(|l| l.strip_prefix("pub mod ").and_then(|r| r.strip_suffix(';'))) {
            text_of(files, &format!("gendb_entry/{module}.rs"));
        }
        assert!(entry.contains(identity));
    }
}

/// Storages that do not store a demanded column are refused with the named reason (`missing_input`); names are
/// lowercase identifiers; the shim is added and declared only through `with_trusted_shim`.
#[test]
fn coverage_names_and_shim() {
    let inst = small_statement();
    let delivered = source_declaration(&inst.doc, &analyze(&inst.doc).unwrap()).unwrap();
    let name = StorageName::new("t_dates").unwrap();
    let only_d = DeclaredSource::for_storage(&inst.doc.tables, &BTreeMap::from([(0, BTreeSet::from([1]))])).unwrap();
    let interface = [FrameworkSource { path: "stores/t_dates/interface/mod.rs".into(), text: String::new() }];
    let uses = [StorageUse { name: &name, declaration: &only_d, interface: &interface }];
    let refused = query_crate_files(&inst, &delivered, &uses, "unit").unwrap_err();
    assert_eq!(refused.failure_class(), "missing_input");
    assert!(refused.to_string().starts_with("storage_does_not_cover_demand: no storage stores t.c"), "{refused}");
    for bad in ["", "Lineitem", "1x", "a-b", "mod", "self", &"x".repeat(65)] {
        assert!(StorageName::new(bad).is_err(), "{bad:?}");
    }
    assert!(DeclaredSource::for_storage(&inst.doc.tables, &BTreeMap::from([(0, BTreeSet::from([7]))])).is_err());
    let c = small_crates();
    let with_shim = with_trusted_shim(c.query.clone(), "// shim");
    assert!(text_of(&with_shim, "lib.rs").ends_with("pub mod agent;\nmod gendb_shim;\n") && text_of(&with_shim, "gendb_shim.rs") == "// shim");
    assert!(!c.query.iter().any(|f| f.path == "gendb_shim.rs"));
}

/// Composition applies the central author-source scan (`verus::scan_source`, the one freeze runs) to every author file
/// of both builds: an agent's method on the framework's `StoredParts`, a `module_path!` in a (shared, identical)
/// interface and an implementation in another storage's interface (outside this storage's closure) are refused; the
/// fixture-shaped author files compose.
#[test]
fn composition_applies_the_central_source_rules() {
    let c = small_crates();
    assert_eq!(check_storage_composition(&c.storage, &c.query, &c.name), Ok(()));
    let set = |files: &[FrameworkSource], path: &str, text: &str| -> Vec<FrameworkSource> {
        let mut files = files.to_vec();
        match files.iter_mut().find(|f| f.path == path) {
            Some(f) => f.text = text.into(),
            None => files.push(FrameworkSource { path: path.into(), text: text.into() }),
        }
        files
    };
    let rules_of = |e: CompositionError| match e {
        CompositionError::SourceRules(findings) => findings.iter().map(|f| (f.file.clone(), f.rule)).collect::<Vec<_>>(),
        other => panic!("expected source-rule findings, got {other}"),
    };
    let foreign_impl = "use crate::gendb_entry::stored::StoredParts;\nverus! {\nimpl StoredParts { pub open spec fn peek(&self) -> bool { true } }\n}\n";
    let refused = check_storage_composition(&c.storage, &set(&c.query, "agent/mod.rs", foreign_impl), &c.name).unwrap_err();
    assert!(refused.to_string().starts_with("author-source rules: agent/mod.rs:3: impl_ownership:"), "{refused}");
    assert_eq!(rules_of(refused), vec![("agent/mod.rs".to_string(), rule::IMPL_OWNERSHIP)]);
    let interface = "stores/t_all/interface/mod.rs";
    let named = "verus! {\npub open spec fn crate_named() -> bool { module_path!()@.len() == 0 }\n}\n";
    let refused = check_storage_composition(&set(&c.storage, interface, named), &set(&c.query, interface, named), &c.name).unwrap_err();
    assert_eq!(rules_of(refused), vec![(interface.to_string(), rule::MACRO), (interface.to_string(), rule::MACRO)]);
    let other = set(&c.query, "stores/other/interface/mod.rs", "use crate::exec::value::EVal;\nverus! {\nimpl EVal { }\n}\n");
    assert_eq!(rules_of(check_storage_composition(&c.storage, &other, &c.name).unwrap_err()), vec![(
        "stores/other/interface/mod.rs".to_string(),
        rule::IMPL_OWNERSHIP
    )]);
    // Framework files are not author files: the scan skips them (the fixed fork/join file names vstd threads).
    assert_eq!(author_source_findings(&c.query), vec![]);
}

/// Names a glob import of an entry root must not shadow: the std prelude, the extern prelude crates and the vstd prelude.
const PRELUDE_NAMES: &[&str] = &[
    "Option", "Some", "None", "Result", "Ok", "Err", "Vec", "Box", "String", "ToString", "ToOwned", "Clone", "Copy", "Send",
    "Sync", "Sized", "Unpin", "Drop", "Fn", "FnMut", "FnOnce", "Default", "Eq", "PartialEq", "Ord", "PartialOrd", "Iterator",
    "IntoIterator", "Extend", "DoubleEndedIterator", "ExactSizeIterator", "AsRef", "AsMut", "Into", "From", "TryFrom",
    "TryInto", "FromIterator", "drop", "std", "core", "alloc", "vstd", "Seq", "Set", "Map", "Multiset", "View", "Ghost",
    "Tracked", "int", "nat", "seq", "set", "map", "vec", "verus",
];

/// Whether `text` defines a trait at the start of a line (`trait`, `pub trait`, `pub(..) trait`, `unsafe trait`).
fn defines_trait(text: &str) -> bool {
    text.lines().map(str::trim_start).any(|line| {
        let line = line.strip_prefix("pub(").and_then(|r| r.split_once(") ")).map_or(line, |(_, rest)| rest);
        let line = line.strip_prefix("pub ").unwrap_or(line);
        line.strip_prefix("unsafe ").unwrap_or(line).starts_with("trait ")
    })
}

/// The kind-specific framework files of both crate kinds (the entry roots, the generated roots and modules, the
/// trusted shims) follow the author-source rules that keep closure meaning independent of the rest of a crate
/// (implementation ownership, supported macros, no rebinding); the entry roots define no trait and no public name of a
/// prelude, so a glob import of an entry root cannot bring a method into scope or shadow a prelude name in one kind only.
#[test]
fn per_kind_framework_files_follow_the_source_rules() {
    let c = small_crates();
    let storage = with_trusted_shim(c.storage.clone(), gendb_runtime::abi::GENDB_STORAGE_SHIM_SOURCE);
    let query = with_trusted_shim(c.query.clone(), gendb_runtime::abi::GENDB_QUERY_SHIM_V4_SOURCE);
    let declared = with_trusted_shim(small_crates_of(&small_constrained_statement()).query, gendb_runtime::abi::GENDB_QUERY_SHIM_V4_SOURCE);
    let v2_storage = with_trusted_shim(small_v2_storage(), gendb_runtime::abi::GENDB_STORAGE_SHIM_SOURCE);
    let engine = with_trusted_shim(small_engine(), gendb_runtime::abi::GENDB_ENGINE_SHIM_SOURCE);
    let meaning_rules = [rule::IMPL_OWNERSHIP, rule::MACRO, rule::MACRO_IMPORT];
    let mut checked = BTreeSet::new();
    for (kind, files) in [("storage", &storage), ("query", &query), ("query v5", &declared), ("storage v2", &v2_storage), ("engine", &engine)] {
        let per_kind = files.iter().filter(|f| closure_definition(&f.path, c.name.as_str()).is_none() && author_definition(&f.path).is_none());
        for f in per_kind {
            let findings: Vec<_> = scan_source(&f.path, &f.text).into_iter().filter(|x| meaning_rules.contains(&x.rule)).collect();
            assert_eq!(findings, vec![], "{kind}: {}", f.path);
            checked.insert(f.path.clone());
        }
    }
    let expected = [
        "lib.rs", "stores.rs", "gendb_entry.rs", "gendb_source.rs", "gendb_entry/binder.rs", "gendb_entry/storage.rs", "query.rs",
        "gendb_params.rs", "gendb_arguments.rs", "gendb_entry/stores.rs", "gendb_shim.rs", "gendb_constraints.rs",
        "gendb_entry/results.rs", "gendb_ast_codec.rs", "gendb_entry/schema_exec.rs",
    ];
    let toolkit = engine_toolkit_files().into_iter().map(|f| f.path);
    assert_eq!(checked, expected.iter().map(|p| p.to_string()).chain(toolkit).collect::<BTreeSet<_>>());
    for entry in [STORAGE_ENTRY_SOURCE, STORAGE_ENTRY_V2_SOURCE, QUERY_ENTRY_SOURCE, QUERY_ENTRY_V5_SOURCE, ENGINE_ENTRY_SOURCE] {
        assert!(!defines_trait(entry));
        let prelude: Vec<String> = public_names(entry).into_iter().filter(|n| PRELUDE_NAMES.contains(&n.as_str())).collect();
        assert_eq!(prelude, Vec::<String>::new());
    }
    assert!(defines_trait("pub trait T {}") && defines_trait("pub(crate) trait T {}") && !defines_trait("// a trait here"));
}

/// Freezing scans author files only, so the framework text of every crate kind must itself avoid what the rules for
/// Verus's cycle-check gaps refuse in author files (trait objects, vstd's rwlock, external trait impls outside the
/// allowlist, bounded associated types, `impl Trait` types): no framework file of a v3 candidate, storage v1/v2, derived
/// storage, query v4/v5 or statement check crate has a finding of these rules, with one reviewed exception:
/// `WorkerTask`'s `type Output: Send + 'static`. Its bound names only the auto trait `Send`, which has no methods and
/// which authors cannot implement (`unsafe impl` is refused), and a lifetime, so the impls it leaves out of the call
/// graph reach no function. The trusted shims (`gendb_shim.rs`) are plain Rust that Verus never checks (trusted to
/// return, trusted assumption trusted_shim_returns): they name no trait object or rwlock, and the trait rules, which close gaps of
/// Verus's checks, do not apply to them (their `abort_on_panic` takes an argument-position `impl FnOnce`). The
/// generated flat storage files, frozen as author files, pass the whole scan. A storage crate with a nullable column
/// (its nullable source module, binder and shim) is scanned the same way.
#[test]
fn framework_files_avoid_the_verus_cycle_gaps() {
    use gendb_frontend::ast::{ColumnDef, PgType, TableDef};
    use gendb_runtime::abi::{
        GENDB_ENGINE_SHIM_SOURCE, GENDB_QUERY_SHIM_V4_SOURCE, GENDB_SHIM_SOURCE, GENDB_STORAGE_DERIVED_SHIM_SOURCE, GENDB_STORAGE_NULLABLE_SHIM_SOURCE,
        GENDB_STORAGE_SHIM_SOURCE,
    };
    let inst = small_statement();
    let c = small_crates();
    let delivered = source_declaration(&inst.doc, &analyze(&inst.doc).unwrap()).unwrap();
    let declaration = DeclaredSource::for_storage(&inst.doc.tables, &BTreeMap::from([(0, BTreeSet::from([0, 1]))])).unwrap();
    let interface = [FrameworkSource { path: "stores/t_all/interface/mod.rs".into(), text: "// interface".into() }];
    let uses = [StorageUse { name: &c.name, declaration: &declaration, interface: &interface }];
    let copy = StorageName::new("t_copy").unwrap();
    let derived = derived_storage_crate_files(&inst.doc.tables, &copy, &declaration, Derivation { sources: &uses, extends: Some(0) }, false).unwrap();
    let column = |name: &str, ty, nullable| ColumnDef { name: name.into(), ty, nullable };
    let nullable_schema = vec![TableDef {
        name: "n".into(),
        columns: vec![column("a", PgType::Int4, false), column("b", PgType::Text, true), column("c", PgType::Numeric { typmod: Some((12, 2)) }, true)],
        constraints: vec![],
    }];
    let nullable_flat = flat_storage(&nullable_schema, 0).unwrap();
    let nullable_storage = storage_crate_files(&nullable_schema, &nullable_flat.name, &nullable_flat.declaration, false).unwrap();
    let crates = [
        ("v3 candidate", with_trusted_shim(candidate_framework_files(&inst, &delivered, "unit").unwrap(), GENDB_SHIM_SOURCE)),
        ("storage", with_trusted_shim(c.storage.clone(), GENDB_STORAGE_SHIM_SOURCE)),
        ("storage v2", with_trusted_shim(small_v2_storage(), GENDB_STORAGE_SHIM_SOURCE)),
        ("derived storage", with_trusted_shim(derived, GENDB_STORAGE_DERIVED_SHIM_SOURCE)),
        ("query", with_trusted_shim(c.query.clone(), GENDB_QUERY_SHIM_V4_SOURCE)),
        ("query v5", with_trusted_shim(small_crates_of(&small_constrained_statement()).query, GENDB_QUERY_SHIM_V4_SOURCE)),
        ("statement check", query_statement_check_files(&inst, "unit").unwrap()),
        ("engine", with_trusted_shim(small_engine(), GENDB_ENGINE_SHIM_SOURCE)),
        ("nullable storage", with_trusted_shim(nullable_storage, GENDB_STORAGE_NULLABLE_SHIM_SOURCE)),
    ];
    let cycle_gap_rules = [rule::DYN_TRAIT_OBJECT, rule::VSTD_RWLOCK, rule::EXTERNAL_TRAIT_IMPL, rule::ASSOCIATED_TYPE_BOUND, rule::IMPL_TRAIT_TYPE];
    let worker_output = |f: &RefusalFinding| {
        f.file == "gendb_entry/parallel.rs" && f.rule == rule::ASSOCIATED_TYPE_BOUND && f.detail == "associated type `Output` declares a bound"
    };
    let mut scanned = BTreeSet::new();
    let (mut exceptions, mut output_declarations) = (BTreeSet::new(), BTreeSet::new());
    for (kind, files) in &crates {
        for f in files.iter().filter(|f| author_definition(&f.path).is_none()) {
            if let Some(line) = f.text.lines().position(|l| l.trim_start().starts_with("type Output: Send + 'static;")) {
                output_declarations.insert((f.path.clone(), line + 1));
            }
            let findings = scan_source(&f.path, &f.text);
            assert!(!findings.iter().any(|x| x.detail.starts_with("cannot lex")), "{kind}: {}: {findings:?}", f.path);
            let rules = if f.path == "gendb_shim.rs" { &cycle_gap_rules[..2] } else { &cycle_gap_rules[..] };
            let (reviewed, named): (Vec<_>, Vec<_>) = findings.into_iter().filter(|x| rules.contains(&x.rule)).partition(worker_output);
            assert_eq!(named, vec![], "{kind}: {}", f.path);
            exceptions.extend(reviewed.into_iter().map(|x| (x.file, x.line)));
            scanned.insert(f.path.clone());
        }
    }
    assert_eq!(output_declarations.len(), 1, "{output_declarations:?}");
    assert_eq!(exceptions, output_declarations);
    for path in [
        "gendb_entry/parallel.rs", "gendb_entry/runtime.rs", "gendb_entry/stored.rs", "gendb_shim.rs", "gendb_entry/sources.rs", "gendb_ast_codec.rs",
        "gendb_entry/schema_exec.rs",
    ] {
        assert!(scanned.contains(path), "{path} was not scanned");
    }
    for table_id in 0..inst.doc.tables.len() {
        for f in flat_storage(&inst.doc.tables, table_id).unwrap().files {
            assert_eq!(scan_source(&f.path, &f.text), vec![], "{}", f.path);
        }
    }
    for f in &nullable_flat.files {
        assert_eq!(scan_source(&f.path, &f.text), vec![], "{}", f.path);
    }
}

/// The proved property `termination` is not a trusted assumption, and every entry lists each assumption it relies on.
#[test]
fn every_entry_lists_the_assumptions_termination_relies_on() {
    assert_eq!(PROVED_PROPERTIES.iter().map(|p| p.id).collect::<Vec<_>>(), ["termination"]);
    let lists: [(&str, &[TrustedAssumption]); 8] = [
        ("entry v3", TRUSTED_ASSUMPTIONS),
        ("storage v1", STORAGE_TRUSTED_ASSUMPTIONS),
        ("storage v2", STORAGE_V2_TRUSTED_ASSUMPTIONS),
        ("derived storage", STORAGE_DERIVED_TRUSTED_ASSUMPTIONS),
        ("derived storage v2", STORAGE_DERIVED_V2_TRUSTED_ASSUMPTIONS),
        ("query v4", QUERY_TRUSTED_ASSUMPTIONS),
        ("query v5", QUERY_V5_TRUSTED_ASSUMPTIONS),
        ("engine v1", ENGINE_TRUSTED_ASSUMPTIONS),
    ];
    for (entry, list) in lists {
        let ids: BTreeSet<&str> = list.iter().map(|a| a.id).collect();
        assert_eq!(ids.len(), list.len(), "{entry}: an assumption is listed twice");
        for property in PROVED_PROPERTIES {
            assert!(!ids.contains(property.id), "{entry}: {} is proved, not assumed", property.id);
            for id in property.relies_on {
                assert!(ids.contains(id), "{entry}: {} relies on {id}, which the entry does not list", property.id);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------- engine crates

/// An engine crate carries a storage's closure byte for byte (it composes with the storage build by the unchanged rule),
/// the engine-only files (entry, codec, generated `schema_exec`, toolkit) outside every closure, and the query crates'
/// generated `stores.rs` with comments naming its own entry. The toolkit is `sqlspec/engine_link/` embedded byte for
/// byte without its `examples/`. Without declared constraints the assembly refuses by name; coverage is a separate
/// admission check.
#[test]
fn engine_crate_carries_the_closure_and_its_own_files() {
    let c = small_crates();
    let engine = small_engine();
    assert_eq!(compare_storage_closure(&c.storage, &engine, &c.name), Ok(()));
    assert_eq!(check_storage_composition(&c.storage, &engine, &c.name), Ok(()));
    assert_eq!(text_of(&engine, "gendb_entry.rs"), ENGINE_ENTRY_SOURCE);
    assert_eq!(text_of(&engine, ENGINE_CODEC_PATH), gendb_runtime::abi::ENGINE_CODEC_SOURCE);
    for engine_only in ["gendb_entry.rs", ENGINE_CODEC_PATH, "gendb_entry/schema_exec.rs", "engine_link/mod.rs", "gendb_constraints.rs"] {
        assert!(closure_definition(engine_only, c.name.as_str()).is_none(), "{engine_only} is in no closure");
    }
    let root = text_of(&engine, "lib.rs");
    assert!(root.contains("pub mod engine_link;\npub mod schema;\npub mod gendb_constraints;\npub mod stores;\npub mod gendb_abi;\npub mod gendb_ast_codec;\npub mod gendb_entry;\npub mod agent;\n"), "{root}");
    for absent in ["query.rs", "gendb_params.rs", "gendb_arguments.rs"] {
        assert!(!engine.iter().any(|f| f.path == absent), "{absent}");
    }
    let stores = text_of(&engine, "gendb_entry/stores.rs");
    assert!(stores.contains("`abi_engine_query`'s `uses`") && !stores.contains("`abi_query`"), "{stores}");
    let schema_exec = text_of(&engine, "gendb_entry/schema_exec.rs");
    assert!(schema_exec.contains("let t1 = ETableSchema { columns: vec![Column { ty: SqlType::Int8, nullable: false }], constraints: Vec::new() };"), "{schema_exec}");

    let plain = small_statement();
    let name = StorageName::new("t_all").unwrap();
    let declaration = DeclaredSource::for_storage(&plain.doc.tables, &BTreeMap::from([(0, BTreeSet::from([0, 1]))])).unwrap();
    let interface = vec![FrameworkSource { path: "stores/t_all/interface/mod.rs".into(), text: "// interface".into() }];
    let uses = [StorageUse { name: &name, declaration: &declaration, interface: &interface }];
    let refused = engine_crate_files(&plain.doc.tables, &uses, "unit").unwrap_err();
    assert!(refused.to_string().starts_with("engine_requires_declared_constraints") && refused.failure_class() == "refusal", "{refused}");
    let constrained = small_constrained_statement();
    let missing = check_engine_coverage(&constrained.doc.tables, &uses).unwrap_err().to_string();
    assert_eq!(missing, "engine_storage_coverage_incomplete: no storage use stores u.e");
    let everything = DeclaredSource::for_storage(&constrained.doc.tables, &BTreeMap::from([(0, BTreeSet::from([0, 1])), (1, BTreeSet::from([0]))])).unwrap();
    let all = StorageName::new("all").unwrap();
    let interface_all = vec![FrameworkSource { path: "stores/all/interface/mod.rs".into(), text: "// interface".into() }];
    assert_eq!(check_engine_coverage(&constrained.doc.tables, &[StorageUse { name: &all, declaration: &everything, interface: &interface_all }]), Ok(()));

    // The toolkit is exactly the `.rs` files of `sqlspec/engine_link/` outside `examples/`, byte for byte, root first.
    let folder = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../sqlspec/engine_link");
    let mut on_disk = BTreeMap::new();
    for entry in std::fs::read_dir(&folder).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "rs") {
            let name = path.file_name().unwrap().to_string_lossy();
            on_disk.insert(format!("{ENGINE_TOOLKIT_DIRECTORY}{name}"), std::fs::read_to_string(&path).unwrap());
        }
    }
    let toolkit = engine_toolkit_files();
    assert_eq!(toolkit[0].path, "engine_link/mod.rs");
    let embedded: BTreeMap<String, String> = toolkit.iter().map(|f| (f.path.clone(), f.text.clone())).collect();
    assert_eq!(embedded.len(), toolkit.len(), "unique paths");
    assert_eq!(embedded, on_disk, "the embedded toolkit is the folder's files");
    let carried: BTreeMap<String, String> =
        engine.iter().filter(|f| f.path.starts_with(ENGINE_TOOLKIT_DIRECTORY)).map(|f| (f.path.clone(), f.text.clone())).collect();
    assert_eq!(carried, embedded);
    let modules: Vec<&str> = embedded["engine_link/mod.rs"].lines().filter_map(|l| l.strip_prefix("pub mod ")?.strip_suffix(';')).collect();
    let files: BTreeSet<String> = modules.iter().map(|m| format!("{ENGINE_TOOLKIT_DIRECTORY}{m}.rs")).collect();
    assert_eq!(files, embedded.keys().filter(|p| p.as_str() != "engine_link/mod.rs").cloned().collect(), "the root declares every file");
}

// --------------------------------------------------------------------------- flat access, version 0, unchanged crates

use crate::verus::engine_rules::{EngineLine, EngineRuleSet};

/// SHA-256 of a crate's files in assembly order (each path, a zero byte, the text's length and the text).
fn files_digest(files: &[FrameworkSource]) -> String {
    use sha2::{Digest, Sha256};
    let mut hash = Sha256::new();
    for f in files {
        hash.update(f.path.as_bytes());
        hash.update([0u8]);
        hash.update((f.text.len() as u64).to_le_bytes());
        hash.update(f.text.as_bytes());
    }
    hash.finalize().iter().map(|b| format!("{b:02x}")).collect()
}

/// The interface files of a flat storage (`stores/<name>/interface/**`).
fn flat_interface(flat: &FlatStorage) -> Vec<FrameworkSource> {
    flat.files.iter().filter(|f| f.path.starts_with(&flat.name.interface_prefix())).cloned().collect()
}

/// The flat storage of every table of the constrained schema of [`small_constrained_statement`] (`t(c int4, d date)`
/// with a primary key, `u(e int8)`) with its interface files.
fn small_flats() -> (Instance, Vec<(FlatStorage, Vec<FrameworkSource>)>) {
    let inst = small_constrained_statement();
    let flats = (0..inst.doc.tables.len()).map(|t| flat_storage(&inst.doc.tables, t).unwrap()).map(|f| { let i = flat_interface(&f); (f, i) }).collect();
    (inst, flats)
}

fn uses_of(flats: &[(FlatStorage, Vec<FrameworkSource>)]) -> Vec<StorageUse<'_>> {
    flats.iter().map(|(f, i)| StorageUse { name: &f.name, declaration: &f.declaration, interface: i }).collect()
}

/// An engine crate over the flat storage of every table carries the flat access module `flat_tables.rs` (declared after
/// the entry, before the author's module), in no storage closure and not an author file, with the whole-database
/// functions; it composes with every flat storage build by the unchanged rule. Version 0's `agent/mod.rs` is the same
/// text for every schema, passes the central and static-item scans and the general line's rules, and is refused by the
/// schema-engine line's evaluator rule. A storage named like a flat storage whose interface differs is not a flat use.
#[test]
fn flat_engine_crate_carries_flat_tables_and_version_0() {
    let (inst, flats) = small_flats();
    let schema = &inst.doc.tables;
    let uses = uses_of(&flats);
    for (k, u) in uses.iter().enumerate() {
        assert_eq!(generated_flat_table(schema, u), Some(k));
    }
    let agent = interpreter_engine(schema, &uses).unwrap();
    assert_eq!(agent.iter().map(|f| f.path.as_str()).collect::<Vec<_>>(), ["agent/mod.rs"]);
    let mut engine = engine_crate_files(schema, &uses, "unit").unwrap();
    engine.extend(agent.clone());
    assert!(text_of(&engine, "lib.rs").ends_with("pub mod gendb_entry;\npub mod flat_tables;\npub mod agent;\n"), "{}", text_of(&engine, "lib.rs"));
    let access = text_of(&engine, FlatAccessSite::Engine.path());
    for item in [
        "pub const TABLE_COUNT: usize = 2;",
        "pub open spec fn flat_table(t: int) -> bool {\n    t == 0 || t == 1\n}",
        "pub fn table_rows(stores: &Stores, t: usize, Ghost(db): Ghost<Database>) -> (n: usize)",
        "pub fn materialize_table(stores: &mut Stores, t: usize, Ghost(db): Ghost<Database>) -> (rows: Vec<ERow>)",
        "pub fn column_slice(stores: &mut Stores, t: usize, c: usize, lo: usize, hi: usize, Ghost(db): Ghost<Database>) -> (s: ColumnSlice)",
        "pub proof fn lemma_flat_table_unique(sv: StoresView, a: Database, b: Database, t: int)",
        "pub fn materialize_database(stores: &mut Stores, Ghost(db): Ghost<Database>) -> (edb: EDatabase)",
        "pub proof fn lemma_flat_database_unique(sv: StoresView, a: Database, b: Database)",
        "use crate::gendb_entry::stores::{stored_ok, Stores, StoresView};",
    ] {
        assert!(access.contains(item), "{item}\n{access}");
    }
    assert_eq!(scan_source("flat_tables.rs", access), vec![], "the flat access module follows every author-source rule");
    assert!(author_definition("flat_tables.rs").is_none());
    for item in ["pub mod plain;", "pub proof fn lemma_flat_plain(sv: StoresView, db: Database, t: int)", "pub open spec fn flat_layout(t: int) -> Seq<int>",
        "slice_fits(s, schema_spec()[t as int].columns[c as int].ty),"] {
        assert!(access.contains(item), "{item}");
    }
    assert_eq!(text_of(&engine, &FlatAccessSite::Engine.plain_path()), PLAIN_COLUMNS, "the vocabulary, byte for byte");
    assert!(author_definition("flat_tables/plain.rs").is_none());
    for (flat, _) in &flats {
        assert!(closure_definition("flat_tables.rs", flat.name.as_str()).is_none() && closure_definition("flat_tables/plain.rs", flat.name.as_str()).is_none());
        let mut storage = storage_crate_files(schema, &flat.name, &flat.declaration, false).unwrap();
        storage.extend(flat.files.iter().cloned());
        assert_eq!(check_storage_composition(&storage, &engine, &flat.name), Ok(()), "{}", flat.name);
    }

    // Version 0: one schema-free text; the evaluator is allowed on the general line only.
    let text = &agent[0].text;
    let (other, other_flats) = {
        let inst = small_statement();
        let flats: Vec<_> = (0..inst.doc.tables.len()).map(|t| flat_storage(&inst.doc.tables, t).unwrap()).map(|f| { let i = flat_interface(&f); (f, i) }).collect();
        (inst, flats)
    };
    assert_eq!(&interpreter_engine(&other.doc.tables, &uses_of(&other_flats)).unwrap()[0].text, text);
    assert_eq!(scan_source("agent/mod.rs", text), vec![]);
    assert_eq!(crate::verus::scan_static_items("agent/mod.rs", text), vec![]);
    let constants = crate::verus::engine_rules::TemplateConstants::default();
    let general = EngineRuleSet::for_line(EngineLine::General, constants.clone(), &[]);
    assert_eq!(general.scan_agent_source("agent/mod.rs", text), vec![]);
    let schema_engine = EngineRuleSet::for_line(EngineLine::SchemaEngine, constants, schema);
    let refused: BTreeSet<&str> = schema_engine.scan_agent_source("agent/mod.rs", text).iter().map(|f| f.rule).collect();
    assert_eq!(refused, BTreeSet::from([rule::WHOLE_STATEMENT_EVALUATOR]));

    // Without a flat storage of every table, version 0 is refused by name; the engine crate keeps the access module of
    // the flat tables it has, without the whole-database functions.
    let refused = interpreter_engine(schema, &uses[..1]).unwrap_err().to_string();
    assert!(refused.starts_with("interpreter_engine_needs_flat_tables") && refused.contains("table u"), "{refused}");
    let partial = engine_crate_files(schema, &uses[..1], "unit").unwrap();
    let partial_access = text_of(&partial, "flat_tables.rs");
    assert!(partial_access.contains("pub open spec fn flat_table(t: int) -> bool {\n    t == 0\n}") && !partial_access.contains("materialize_database"));

    // A storage with a flat storage's name whose interface differs is not a flat use: no access module.
    let (flat, _) = &flats[0];
    let changed = vec![FrameworkSource { path: format!("{}mod.rs", flat.name.interface_prefix()), text: "// another interface".into() }];
    let impostor = [StorageUse { name: &flat.name, declaration: &flat.declaration, interface: &changed }];
    assert_eq!(generated_flat_table(schema, &impostor[0]), None);
    let files = engine_crate_files(schema, &impostor, "unit").unwrap();
    assert!(!files.iter().any(|f| f.path == "flat_tables.rs") && !text_of(&files, "lib.rs").contains("flat_tables"));
}

/// The schema of [`small_constrained_statement`] with column `d` of `t` nullable.
fn small_nullable_schema() -> Vec<gendb_frontend::ast::TableDef> {
    let mut tables = small_constrained_statement().doc.tables;
    tables[0].columns[1].nullable = true;
    tables
}

/// The header lines only a uniform module has (it says what the module is for).
fn without_uniform_header(text: &str) -> String {
    text.lines().filter(|l| !l.starts_with("// Uniform access") && !l.starts_with("// crate's storages;") && !l.starts_with("// for a column that is not")).map(|l| format!("{l}\n")).collect()
}

/// Stage runs: every engine crate assembled with [`FlatAccess::Uniform`] carries `flat_tables.rs`
/// with its nullable items, whatever its storages. In the shape of the TPC-H head (one flat storage, one other
/// storage, no nullable column) `nullable_column` is `false`, `column_slice` requires `!nullable_column`,
/// `nullable_column_slice` is `unreached()` and `plain_table` is the flat table; in a crate without a flat use every
/// reader is `unreached()` and `flat_table` is `false`; in a crate with a nullable flat column the module is the
/// as-used module plus its header note. Each follows the central author-source rules, is no author file and in no
/// storage closure; [`FlatAccess::AsUsed`] is [`engine_crate_files`] exactly (the golden digests above stay).
#[test]
fn stage_crates_carry_the_uniform_flat_access() {
    let (inst, flats) = small_flats();
    let schema = &inst.doc.tables;
    let flat_uses = uses_of(&flats);
    let other = StorageName::new("u_store").unwrap();
    let u_declaration = DeclaredSource::for_storage(schema, &BTreeMap::from([(1, BTreeSet::from([0]))])).unwrap();
    let u_interface = vec![FrameworkSource { path: "stores/u_store/interface/mod.rs".into(), text: "// interface".into() }];
    let head_shape = [flat_uses[0], StorageUse { name: &other, declaration: &u_declaration, interface: &u_interface }];
    let uniform = engine_crate_files_with(schema, &head_shape, "unit", FlatAccess::Uniform).unwrap();
    let as_used = engine_crate_files(schema, &head_shape, "unit").unwrap();
    assert_eq!(files_digest(&engine_crate_files_with(schema, &head_shape, "unit", FlatAccess::AsUsed).unwrap()), files_digest(&as_used));
    let access = text_of(&uniform, FlatAccessSite::Engine.path());
    for item in [
        "// Uniform access (an engine crate of a stage run)",
        "pub const TABLE_COUNT: usize = 2;",
        "pub open spec fn flat_table(t: int) -> bool {\n    t == 0\n}",
        "pub open spec fn nullable_column(t: int, c: int) -> bool {\n    false\n}",
        "pub proof fn lemma_nullable_column(t: int, c: int)",
        "        schema_spec()[0].columns[1].nullable == false,",
        "        !nullable_column(t as int, c as int),\n        lo < hi <= db.tables[t as int].len(),",
        "pub open spec fn plain_table(t: int) -> bool {\n    t == 0\n}",
        "        flat_table(t),\n        plain_table(t),\n    ensures",
    ] {
        assert!(access.contains(item), "{item}\n{access}");
    }
    let nullable_slice = &access[access.find("pub fn nullable_column_slice(").unwrap()..];
    assert!(nullable_slice[nullable_slice.find("{\n").unwrap()..].starts_with("{\n    vstd::pervasive::unreached()\n}\n"), "{nullable_slice}");
    let as_used_access = text_of(&as_used, FlatAccessSite::Engine.path());
    assert!(!as_used_access.contains("nullable_column") && !as_used_access.contains("plain_table"), "as used: no nullable items without a nullable column");
    assert!(text_of(&uniform, "lib.rs").ends_with("pub mod gendb_entry;\npub mod flat_tables;\npub mod agent;\n"));

    // No flat use: the module is there, every reader `unreached()`, every table outside `flat_table`.
    let t_all = StorageName::new("t_all").unwrap();
    let t_declaration = DeclaredSource::for_storage(schema, &BTreeMap::from([(0, BTreeSet::from([0, 1]))])).unwrap();
    let t_interface = vec![FrameworkSource { path: "stores/t_all/interface/mod.rs".into(), text: "// interface".into() }];
    let no_flat = [StorageUse { name: &t_all, declaration: &t_declaration, interface: &t_interface }, head_shape[1]];
    let bare = engine_crate_files_with(schema, &no_flat, "unit", FlatAccess::Uniform).unwrap();
    assert!(!engine_crate_files(schema, &no_flat, "unit").unwrap().iter().any(|f| f.path == "flat_tables.rs"), "as used: no module");
    let bare_access = text_of(&bare, FlatAccessSite::Engine.path());
    for item in [
        "// No storage of this crate is a generated flat storage.",
        "pub const TABLE_COUNT: usize = 2;",
        "pub open spec fn flat_table(t: int) -> bool {\n    false\n}",
        "pub fn is_flat_table(t: usize) -> (r: bool)\n    ensures\n        r == flat_table(t as int),\n{\n    false\n}",
        "pub open spec fn nullable_column(t: int, c: int) -> bool {\n    false\n}",
        "pub open spec fn plain_table(t: int) -> bool {\n    false\n}",
        "pub open spec fn flat_parts(sv: StoresView, t: int) -> Seq<PartView> {\n    { Seq::empty() }\n}",
    ] {
        assert!(bare_access.contains(item), "{item}\n{bare_access}");
    }
    for reader in ["pub fn table_rows(", "pub fn materialize_table(", "pub fn column_slice(", "pub fn nullable_column_slice("] {
        let body = &bare_access[bare_access.find(reader).unwrap()..];
        assert!(body[body.find("{\n").unwrap()..].starts_with("{\n    vstd::pervasive::unreached()\n}\n"), "{reader}: {body}");
    }
    for lemma in ["pub proof fn lemma_flat_table_unique(", "pub proof fn lemma_nullable_column(", "pub proof fn lemma_flat_plain("] {
        let body = &bare_access[bare_access.find(lemma).unwrap()..];
        assert!(body[body.find("{\n").unwrap()..].starts_with("{\n}\n"), "{lemma}: empty body\n{body}");
    }
    assert_eq!(bare_access.matches('{').count(), bare_access.matches('}').count(), "balanced braces");

    // A nullable flat column: the uniform module is the as-used one plus its header note.
    let nullable_schema = &small_nullable_schema();
    let nullable_flats: Vec<_> = (0..nullable_schema.len()).map(|t| flat_storage(nullable_schema, t).unwrap()).map(|f| { let i = flat_interface(&f); (f, i) }).collect();
    let nullable_uses = uses_of(&nullable_flats);
    let uniform_nullable = engine_crate_files_with(nullable_schema, &nullable_uses, "unit", FlatAccess::Uniform).unwrap();
    let as_used_nullable = engine_crate_files(nullable_schema, &nullable_uses, "unit").unwrap();
    let as_used_text = text_of(&as_used_nullable, "flat_tables.rs");
    assert!(as_used_text.contains("pub open spec fn nullable_column(t: int, c: int) -> bool {\n    (t == 0 && (c == 1))\n}"), "{as_used_text}");
    assert_eq!(without_uniform_header(text_of(&uniform_nullable, "flat_tables.rs")), as_used_text);
    assert_eq!(files_digest(&uniform_nullable.iter().filter(|f| f.path != "flat_tables.rs").cloned().collect::<Vec<_>>()),
        files_digest(&as_used_nullable.iter().filter(|f| f.path != "flat_tables.rs").cloned().collect::<Vec<_>>()), "every other file is the same");

    for (what, files) in [("head shape", &uniform), ("no flat use", &bare), ("nullable", &uniform_nullable)] {
        let text = text_of(files, "flat_tables.rs");
        assert_eq!(scan_source("flat_tables.rs", text), vec![], "{what}: the module follows every author-source rule");
        assert_eq!(text_of(files, &FlatAccessSite::Engine.plain_path()), PLAIN_COLUMNS, "{what}");
    }
    assert!(author_definition("flat_tables.rs").is_none() && closure_definition("flat_tables.rs", "u_store").is_none());
}

/// A storage crate built from a flat storage carries `sources_flat.rs` over its sources (`gendb_entry::sources`),
/// declared before the builder, without the whole-database functions; it is in no storage closure, not an author file,
/// and follows every author-source rule. The new storage's closure is unchanged by it.
#[test]
fn derived_crate_over_a_flat_source_carries_sources_flat() {
    let inst = small_statement();
    let schema = &inst.doc.tables;
    let flat = flat_storage(schema, 0).unwrap();
    let interface = flat_interface(&flat);
    let sources = [StorageUse { name: &flat.name, declaration: &flat.declaration, interface: &interface }];
    let name = StorageName::new("t_copy").unwrap();
    let derived = derived_storage_crate_files(schema, &name, &flat.declaration, Derivation { sources: &sources, extends: Some(0) }, false).unwrap();
    assert!(text_of(&derived, "lib.rs").ends_with("pub mod gendb_entry;\npub mod sources_flat;\npub mod builder;\n"), "{}", text_of(&derived, "lib.rs"));
    let access = text_of(&derived, FlatAccessSite::DerivedSources.path());
    assert!(access.contains("use crate::gendb_entry::sources::{stored_ok, Stores, StoresView};") && access.contains("pub fn column_slice("));
    assert!(!access.contains("materialize_database") && !access.contains("schema_exec"));
    assert_eq!(scan_source("sources_flat.rs", access), vec![]);
    assert!(author_definition("sources_flat.rs").is_none() && author_definition("sources_flat/plain.rs").is_none());
    assert_eq!(text_of(&derived, &FlatAccessSite::DerivedSources.plain_path()), PLAIN_COLUMNS, "the vocabulary, byte for byte");
    for storage in [flat.name.as_str(), name.as_str()] {
        for path in ["sources_flat.rs", "sources_flat/plain.rs", "flat_tables.rs", "flat_tables/plain.rs"] {
            assert!(closure_definition(path, storage).is_none(), "{path} is in no closure");
        }
    }
    // Without the flat source (the same declaration, another interface) there is no access module.
    let other = [FrameworkSource { path: format!("{}mod.rs", flat.name.interface_prefix()), text: "// interface".into() }];
    let plain = [StorageUse { name: &flat.name, declaration: &flat.declaration, interface: &other }];
    let files = derived_storage_crate_files(schema, &name, &flat.declaration, Derivation { sources: &plain, extends: Some(0) }, false).unwrap();
    assert!(!files.iter().any(|f| f.path == "sources_flat.rs"));
}

/// The plain-columns vocabulary is schema free: as a storage's interface file it passes the central author-source scan,
/// the static-item rule and the general line's storage and agent scans over a schema with column names that share
/// segments with its identifiers (`text`, `parts`, `rows`, `value`), and it names no table or column of its own.
#[test]
fn plain_columns_vocabulary_is_schema_free() {
    let name = StorageName::new("kept").unwrap();
    let file = plain_columns_interface_file(&name);
    assert_eq!((file.path.as_str(), file.text.as_str()), ("stores/kept/interface/plain.rs", PLAIN_COLUMNS));
    assert!(PLAIN_COLUMNS.contains(PLAIN_COLUMNS_IDENTITY));
    assert_eq!(scan_source(&file.path, &file.text), vec![]);
    assert_eq!(crate::verus::scan_static_items(&file.path, &file.text), vec![]);
    let names = crate::verus::engine_rules::SchemaNames::from_names(["lineitem", "part", "orders"], ["l_comment", "p_name", "o_orderdate", "c_phone"]);
    let general = EngineRuleSet::general_with_names(crate::verus::engine_rules::TemplateConstants::default(), names);
    assert_eq!(general.scan_storage_source(&file.path, &file.text), vec![]);
    assert_eq!(general.scan_agent_source(&file.path, &file.text), vec![]);
}

// --------------------------------------------------------------------- whole-schema storages (storage family instances)

/// A storage built from the flat storage of every table that stores every column of every table (a storage family's
/// instance) carries `schema_exec.rs` and `whole_schema.rs`, declared before its builder, and an
/// engine crate that reads it carries `whole_schema.rs`, declared before the agent; both texts are in no storage closure
/// and are not author files. A derived storage of one table, a reordered declaration and an engine crate over the flat
/// storages only carry neither (the golden digests above cover crates without them byte for byte).
#[test]
fn whole_schema_storages_carry_their_generated_files() {
    let (inst, flats) = small_flats();
    let schema = &inst.doc.tables;
    let sources = uses_of(&flats);
    let every = BTreeMap::from([(0, BTreeSet::from([0, 1])), (1, BTreeSet::from([0]))]);
    let whole = DeclaredSource::for_storage(schema, &every).unwrap();
    assert!(whole_schema_declaration(schema, &whole));
    assert!(!whole_schema_declaration(schema, &flats[0].0.declaration), "one table of two");
    let mut reordered = whole.clone();
    reordered.tables.swap(0, 1);
    assert!(!whole_schema_declaration(schema, &reordered), "tables in table order");
    let name = StorageName::new("plainfam").unwrap();
    let derived = derived_storage_crate_files(schema, &name, &whole, Derivation { sources: &sources, extends: None }, false).unwrap();
    assert!(text_of(&derived, "lib.rs").ends_with("pub mod sources_flat;\npub mod schema_exec;\npub mod whole_schema;\npub mod builder;\n"), "{}", text_of(&derived, "lib.rs"));
    let lemma = text_of(&derived, WHOLE_SCHEMA_PATH);
    assert!(lemma.contains(WHOLE_SCHEMA_GENERATOR) && lemma.contains("pub proof fn lemma_plainfam(db: Database)"));
    assert!(lemma.contains("crate::stores::plainfam::declaration::stored_relations(db) == db.tables") && lemma.contains("pub const TABLE_COUNT: usize = 2;"));
    assert!(lemma.contains("let cols = crate::stores::plainfam::declaration::stored_cols_t1();"), "one block per table");
    assert!(lemma.contains("pub proof fn lemma_schema_shape()") && lemma.contains("pub open spec fn stored_type(ty: SqlType) -> bool"));
    assert!(lemma.contains("assert(schema_spec()[1].columns[0].ty == (SqlType::Int8)) by (compute);"), "the shape by compute");
    let schema_exec = text_of(&derived, STORAGE_SCHEMA_EXEC_PATH);
    assert!(schema_exec.contains("pub fn schema_exec() -> (s: Vec<ETableSchema>)") && schema_exec.contains(WHOLE_SCHEMA_GENERATOR));
    for path in [WHOLE_SCHEMA_PATH, STORAGE_SCHEMA_EXEC_PATH] {
        assert!(author_definition(path).is_none() && closure_definition(path, name.as_str()).is_none(), "{path}: framework, in no closure");
        assert_eq!(scan_source(path, text_of(&derived, path)), vec![]);
    }
    // The storage crate's executable schema is the engine crate's text, its header naming this generator.
    let interface = [FrameworkSource { path: "stores/plainfam/interface/mod.rs".into(), text: "// interface".into() }];
    let family_use = [StorageUse { name: &name, declaration: &whole, interface: &interface }];
    let engine = engine_crate_files_with(schema, &family_use, "unit", FlatAccess::Uniform).unwrap();
    let engine_schema_exec = text_of(&engine, "gendb_entry/schema_exec.rs");
    assert_eq!(engine_schema_exec.replace(ENGINE_ENTRY_IDENTITY, WHOLE_SCHEMA_GENERATOR), schema_exec);
    assert!(text_of(&engine, "lib.rs").ends_with("pub mod flat_tables;\npub mod whole_schema;\npub mod agent;\n"), "{}", text_of(&engine, "lib.rs"));
    assert_eq!(text_of(&engine, WHOLE_SCHEMA_PATH), lemma, "the same lemma in the storage crate and the engine crate");
    // No whole-schema file elsewhere: a derived storage of one table, the flat storages' engine crate.
    let one = derived_storage_crate_files(schema, &StorageName::new("t_copy").unwrap(), &flats[0].0.declaration, Derivation { sources: &sources[..1], extends: Some(0) }, false).unwrap();
    assert!(!one.iter().any(|f| f.path == WHOLE_SCHEMA_PATH || f.path == STORAGE_SCHEMA_EXEC_PATH));
    let flat_engine = engine_crate_files_with(schema, &sources, "unit", FlatAccess::Uniform).unwrap();
    assert!(!flat_engine.iter().any(|f| f.path == WHOLE_SCHEMA_PATH));
}

/// The public items of a flat access module with their signatures: every `pub fn` and `pub proof fn` from its name to
/// the opening brace of its body (parameters, result, `requires` and `ensures`), and the name of every other public item.
fn public_signatures(text: &str) -> Vec<String> {
    let mut items = vec![];
    let mut rest = text;
    while let Some(at) = rest.find("\npub ") {
        rest = &rest[at + 1..];
        let line = &rest[..rest.find('\n').unwrap_or(rest.len())];
        if line.starts_with("pub fn ") || line.starts_with("pub proof fn ") {
            items.push(rest[..rest.find("\n{\n").expect("a body")].to_string());
        } else {
            items.push(line[..line.find(['(', '{', ':', ';']).unwrap_or(line.len())].to_string());
        }
    }
    items
}

/// A storage family's instance (a whole-schema derived storage) reads its flat sources uniformly (one family builder text
/// for every workload). Over the NOT NULL schema its `sources_flat.rs` carries the nullable items:
/// `nullable_column` false, `lemma_nullable_column` with the declared nullability of every column, `column_slice` for
/// `!nullable_column(t, c)`, `nullable_column_slice` `unreached()` and `plain_table` every table, with the instance's
/// header note; its public items and signatures are those of the instance over a schema with a nullable column, whose
/// module is the as-used text byte for byte (no note). A derived storage of one table keeps the as-used module.
#[test]
fn family_instances_offer_the_nullable_items_over_every_schema() {
    let (inst, plain_flats) = small_flats();
    let nullable_schema = small_nullable_schema();
    let nullable_flats: Vec<_> = (0..nullable_schema.len()).map(|t| flat_storage(&nullable_schema, t).unwrap()).map(|f| { let i = flat_interface(&f); (f, i) }).collect();
    let name = StorageName::new("plainfam").unwrap();
    let every = BTreeMap::from([(0, BTreeSet::from([0, 1])), (1, BTreeSet::from([0]))]);
    let instance_access = |schema: &[gendb_frontend::ast::TableDef], flats: &[(FlatStorage, Vec<FrameworkSource>)]| -> (String, String) {
        let whole = DeclaredSource::for_storage(schema, &every).unwrap();
        assert!(whole_schema_declaration(schema, &whole));
        let sources = uses_of(flats);
        let files = derived_storage_crate_files(schema, &name, &whole, Derivation { sources: &sources, extends: None }, false).unwrap();
        assert_eq!(text_of(&files, &FlatAccessSite::DerivedSources.plain_path()), PLAIN_COLUMNS);
        let as_used = super::flat_tables::flat_access_files_with(schema, &sources, FlatAccessSite::DerivedSources, FlatAccess::AsUsed);
        (text_of(&files, FlatAccessSite::DerivedSources.path()).to_string(), as_used[0].text.clone())
    };
    let (plain, plain_as_used) = instance_access(&inst.doc.tables, &plain_flats);
    for item in [
        "// Uniform access (a storage family's instance)",
        "use crate::gendb_entry::sources::{stored_ok, Stores, StoresView};",
        "pub open spec fn flat_table(t: int) -> bool {\n    t == 0 || t == 1\n}",
        "pub open spec fn nullable_column(t: int, c: int) -> bool {\n    false\n}",
        "pub proof fn lemma_nullable_column(t: int, c: int)",
        "        schema_spec()[0].columns[1].nullable == false,",
        "        schema_spec()[1].columns[0].nullable == false,",
        "        !nullable_column(t as int, c as int),\n        lo < hi <= db.tables[t as int].len(),",
        "pub open spec fn plain_table(t: int) -> bool {\n    t == 0 || t == 1\n}",
        "        flat_table(t),\n        plain_table(t),\n    ensures",
    ] {
        assert!(plain.contains(item), "{item}\n{plain}");
    }
    let nullable_slice = &plain[plain.find("pub fn nullable_column_slice(").unwrap()..];
    assert!(nullable_slice[nullable_slice.find("{\n").unwrap()..].starts_with("{\n    vstd::pervasive::unreached()\n}\n"), "{nullable_slice}");
    assert!(!plain.contains("materialize_database") && !plain_as_used.contains("nullable_column"), "as used: no nullable items over NOT NULL columns");
    assert_eq!(scan_source("sources_flat.rs", &plain), vec![], "the uniform module follows every author-source rule");

    let (nullable, nullable_as_used) = instance_access(&nullable_schema, &nullable_flats);
    assert_eq!(nullable, nullable_as_used, "over a nullable flat column the instance's module is the as-used text byte for byte");
    assert!(nullable.contains("pub open spec fn nullable_column(t: int, c: int) -> bool {\n    (t == 0 && (c == 1))\n}") && !nullable.contains("// Uniform access"));
    assert_eq!(public_signatures(&plain), public_signatures(&nullable), "the same public items and signatures over both schemas");
    for item in ["nullable_column_slice", "lemma_nullable_column", "nullable_column", "plain_table", "column_slice", "lemma_flat_plain"] {
        assert!(public_signatures(&plain).iter().any(|s| s.contains(&format!(" {item}(")) || s.ends_with(&format!(" {item}"))), "{item}");
    }

    // A derived storage of one table (no family instance) keeps the as-used module: no nullable items, no note.
    let sources = uses_of(&plain_flats);
    let one = derived_storage_crate_files(&inst.doc.tables, &StorageName::new("t_copy").unwrap(), &plain_flats[0].0.declaration, Derivation { sources: &sources[..1], extends: Some(0) }, false).unwrap();
    let one_access = text_of(&one, FlatAccessSite::DerivedSources.path());
    assert!(!one_access.contains("nullable_column") && !one_access.contains("// Uniform access"), "{one_access}");
}
