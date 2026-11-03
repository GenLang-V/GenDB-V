//! The fixed entry v3 end to end at the proof boundary, on a tiny non-TPC-H parameterized filtered projection
//! (`fixtures/verus_params`):
//!   SELECT id + $3 AS shifted, reading, tag FROM sensor WHERE reading >= $1 AND day < $2
//! with `$1 numeric(10,2)` free, `$2 date` FIXED (the middle placeholder) and `$3 integer` free, over a two-table
//! schema whose source table is not table 0 and whose delivered columns are not contiguous.
//!
//! SQL + parameter requests -> frontend AST -> `params::{declare, instantiate}` -> `columns::{analyze,
//! source_declaration}` -> `obligations::candidate_framework_files` (the one assembly) + a fixture agent
//! (`fixtures/verus_params/agent.rs`, hand-written framework test input, not an author output) -> freeze -> ONE
//! pinned Verus `--no-cheating` verify+compile of the whole crate, whose checked items include
//! `gendb_entry::theorem_end_to_end` over the executed `abi_build`/`abi_query`, the generated binder, source and
//! parameter modules. Negative variants (verify only), one per proof-boundary bypass: a wrong answer, a wrong SQL
//! error code, an unjustified Capacity, a representation of different data, a parameter read from the wrong slot, an
//! extra precondition on `query`, and a forged WorkerFailure token.
//!
//! `text_template_statement_check_verifies`: the query entry v4's statement check crate (what every preflight verifies
//! before an author runs) for a template with free `text` parameters (`<>`, NOT LIKE), an integer and a date: the emitted
//! text domain (`text_ok`), the example binding (empty texts), the typing transfer, the query-only argument type
//! `QueryArg` and the generated binder with its verified NUL decision, in ONE `--no-cheating` Verus run.
//!
//! The generation test needs the pinned frontend Python only. The Verus tests also need the pinned Verus
//! (`GENDB_VERUS_HOME`, default `<repository>/toolchains`); run them with `--ignored`.
use gendb_frontend::ast::Translation;
use gendb_frontend::columns::{analyze, source_declaration};
use gendb_frontend::params::{declare, instantiate, parse_arguments, BindingRequest, Instance, ParamRequest, ParamValue};
use gendb_frontend::parser::SqlParser;
use gendb_verification::obligations::{candidate_framework_files, framework_check_files, query_statement_check_files};
use gendb_verification::verus::{
    freeze_crate, freeze_framework_crate, run_verus, CodegenOptions, FrameworkSource, FrozenCrate, VerusMode, VerusOptions,
    VerusOutcome, VerusToolchain,
};
use std::path::{Path, PathBuf};

const AGENT: &str = include_str!("fixtures/verus_params/agent.rs");

fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/verus_params")
}

fn scratch(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let d = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("verus-params-entry-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn requests() -> Vec<ParamRequest> {
    serde_json::from_str(&std::fs::read_to_string(fixtures().join("params.json")).unwrap()).unwrap()
}

/// The translated fixture statement for these parameter requests.
fn translate(sql: &Path, requests: &[ParamRequest]) -> gendb_frontend::ast::AstDocument {
    let placeholders: Vec<_> = requests.iter().map(|r| r.placeholder()).collect();
    let parser = SqlParser::from_environment().unwrap();
    let (_, t) = parser.translate(&fixtures().join("schema.sql"), sql, "postgres", &placeholders).unwrap();
    let Translation::Ok(doc) = t else { panic!("fixture SQL refused: {t:?}") };
    doc
}

fn framework_files(inst: &Instance, identity: &str) -> Vec<FrameworkSource> {
    let delivered = source_declaration(&inst.doc, &analyze(&inst.doc).unwrap()).unwrap();
    candidate_framework_files(inst, &delivered, identity).unwrap()
}

/// The fixture statement with `$2` fixed: the instance and its framework files.
fn instance() -> (Instance, Vec<FrameworkSource>) {
    let reqs = requests();
    let doc = translate(&fixtures().join("query.sql"), &reqs);
    let inst = instantiate(&doc, &declare(&doc, &reqs).unwrap()).unwrap();
    let files = framework_files(&inst, "verus_params fixture");
    (inst, files)
}

fn text<'a>(files: &'a [FrameworkSource], path: &str) -> &'a str {
    &files.iter().find(|f| f.path == path).unwrap_or_else(|| panic!("{path} missing")).text
}

/// Generation only (no Verus). The fixed middle parameter leaves dense slots `$1 -> 0`, `$3 -> 1`: the emitted
/// statement reads `ps[0]` for `$1` and `ps[1]` for `$3`, the fixed date is a literal, and the generated argument
/// binder maps ABI argument 1 to `$3` (integer). Host conversion follows the same slots. The crate holds every file
/// admission requires.
#[test]
fn params_fixture_sources_generate() {
    let (inst, files) = instance();
    let slots: Vec<(u32, usize)> = inst.free.iter().map(|f| (f.index, f.slot)).collect();
    assert_eq!(slots, [(1, 0), (3, 1)]);
    let query = text(&files, "query.rs");
    assert!(query.contains("&&& ps.len() == 2"), "{query}");
    assert!(query.contains("&&& type_lit(ps[0]) == Some(nn(ScalarTy::Numeric { scale: 2 }))"));
    assert!(query.contains("&&& type_lit(ps[1]) == Some(nn(ScalarTy::Int4))"));
    assert!(query.contains("Literal::Date { y: 2020, m: 6, d: 30 }"), "the fixed $2 is a literal");
    assert!(!query.contains("ps[2]"));
    let params = text(&files, "gendb_params.rs");
    for needle in [
        "// Slot 0 = $1 numeric(10,2) (ABI argument 0 = ParamArg::Num).",
        "// Slot 1 = $3 integer (ABI argument 1 = ParamArg::Int).",
        "seq![Literal::Num { coeff: self.p0 as int, scale: 2 }, Literal::Int { v: self.p1 as int, kind: IntKind::Int4 }]",
        "if !(-50000i128 <= p.p0 && p.p0 <= 99999i128) {",
        "if !(-2147483648i64 <= p.p1 && p.p1 <= 2147483647i64) {",
    ] {
        assert!(params.contains(needle), "gendb_params lacks {needle}:\n{params}");
    }
    let source = text(&files, "gendb_source.rs");
    assert!(source.contains("pub open spec fn source_table_t0() -> nat {\n    1\n}"), "{source}");
    assert!(source.contains("seq![0nat, 2, 3, 4]"));
    let binder = text(&files, "gendb_entry/binder.rs");
    assert!(binder.contains("columns.len() == 4 && columns[0] is I32 && columns[1] is I128 && columns[2] is I32 && columns[3] is Utf8"));
    // Host conversion: one text per free slot, in slot order ($1 then $3); `$2` is not an argument.
    let args = parse_arguments(&inst.free, &["12.50".into(), "-7".into()]).unwrap();
    assert_eq!(args, [ParamValue::Num(1250), ParamValue::Int(-7)]);
    assert!(parse_arguments(&inst.free, &["12.50".into(), "2020-06-30".into(), "-7".into()]).is_err());
    // The crate layout admission expects, and nothing of the retired per-query contract.
    for required in gendb_artifacts::verus::VERUS_V3_REQUIRED_FRAMEWORK {
        text(&files, required);
    }
    for legacy in ["gendb_contract.rs", "gendb_link_query.rs"] {
        assert!(!files.iter().any(|f| f.path == legacy), "{legacy} is not part of a candidate crate");
    }
    assert!(text(&files, "lib.rs").contains("pub mod link;\npub mod query;\npub mod gendb_source;\npub mod gendb_params;\n"));
    assert!(text(&files, "link.rs").contains("pub mod source;") && !files.iter().any(|f| f.path == "link/mod.rs"));
}

fn freeze(work: &Path, name: &str, framework: &[FrameworkSource], agent: &str) -> FrozenCrate {
    let dir = work.join(name).join("agent");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("mod.rs"), agent).unwrap();
    freeze_crate(&dir, framework, &work.join(name).join("frozen")).unwrap_or_else(|e| panic!("{name}: {e:?}"))
}

fn options(name: &str) -> VerusOptions {
    VerusOptions { crate_name: name.into(), codegen: CodegenOptions { opt_level: 2, target_cpu: None }, num_threads: Some(8) }
}

/// Replace exactly one occurrence of `from` (the variant must differ from the fixture).
fn variant(from: &str, to: &str) -> String {
    assert_eq!(AGENT.matches(from).count(), 1, "variant anchor {from:?} must occur once");
    AGENT.replacen(from, to, 1)
}

#[test]
#[ignore = "runs the pinned Verus toolchain and frontend; cargo test -p gendb-verification --test verus_params_entry -- --ignored"]
fn verified_params_entry_checks_and_refuses_bypasses() {
    let work = scratch("entry");
    let (_, framework) = instance();
    let toolchain = VerusToolchain::from_env().unwrap();

    // One whole-crate --no-cheating Verus run that also compiles the library a host would serve.
    let frozen = freeze(&work, "candidate", &framework, AGENT);
    let built = run_verus(&toolchain, &frozen, &options("params_fixture"), VerusMode::VerifyAndCompile, &work.join("candidate/verus-build")).unwrap();
    assert_eq!(built.outcome, VerusOutcome::Compiled, "{}", built.rendered_errors());
    let summary = built.verification.clone().unwrap();
    assert!(summary.is_verifying_entire_crate && summary.errors == 0, "{summary:?}");

    // Negative variants: each must fail verification, at the fixed proof boundary.
    let negatives: Vec<(&str, String)> = vec![
        ("wrong-rows", variant(NEG_ROWS.0, NEG_ROWS.1)),
        ("wrong-error-code", variant(NEG_ERROR.0, NEG_ERROR.1)),
        ("unjustified-capacity", variant(NEG_CAPACITY.0, NEG_CAPACITY.1)),
        ("different-data", variant(NEG_SOURCE.0, NEG_SOURCE.1)),
        ("wrong-parameter-slot", variant(NEG_SLOT.0, NEG_SLOT.1)),
        ("extra-precondition", variant(NEG_PRE.0, NEG_PRE.1)),
        ("forged-worker-failure", variant(NEG_FORGED.0, NEG_FORGED.1)),
    ];
    let mut rejected = vec![];
    for (name, agent) in &negatives {
        let frozen = freeze(&work, name, &framework, agent);
        let run = run_verus(&toolchain, &frozen, &options(&name.replace('-', "_")), VerusMode::Verify, &work.join(name).join("verus")).unwrap();
        assert!(run.outcome != VerusOutcome::Verified && run.outcome != VerusOutcome::Compiled, "{name} must be rejected");
        rejected.push(serde_json::json!({"variant": name, "outcome": run.outcome, "errors": run.rendered_errors()}));
    }
    let evidence = serde_json::json!({
        "wall_ns": built.wall_ns,
        "verification": summary,
        "library": built.artifact,
        "negatives": rejected,
    });
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

// Negative variants: (anchor in the fixture agent, replacement). Each anchor occurs exactly once.
const NEG_ROWS: (&str, &str) = ("    Ok(Answer::Rows(out))\n}", "    Ok(Answer::Rows(Vec::new()))\n}");
const NEG_ERROR: (&str, &str) =
    ("return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));", "return Ok(Answer::SqlError(SqlError::DivisionByZero));");
const NEG_CAPACITY: (&str, &str) = ("    let ghost pv = parts_view(parts@);", "    return Ok(Answer::Capacity);\n    let ghost pv = parts_view(parts@);");
const NEG_SOURCE: (&str, &str) = ("OwnedPart::I128(copy(src.t0_f1)),", "OwnedPart::I128(filled(src.t0_f1.len(), 0i128)),");
const NEG_SLOT: (&str, &str) = ("let shift = params.p1;", "let shift = (params.p0 % 1000) as i64;");
const NEG_PRE: (&str, &str) = ("        param_domain(params@),\n", "        param_domain(params@),\n        params.p1 >= 0,\n");
const NEG_FORGED: (&str, &str) = (
    "    let ghost pv = parts_view(parts@);",
    "    return Err(QueryError::WorkerFailed(crate::gendb_entry::runtime::WorkerFailure { _private: () }));\n    let ghost pv = parts_view(parts@);",
);

/// The generated modules for statements the fixture does not exercise, in the framework-only check crate
/// (`framework_check_files`: no agent, no entry items): (a) the fixture statement with EVERY parameter fixed (empty
/// `Params`, `param_domain(ps) = ps.len() == 0`), and (b) `SELECT COUNT(*) FROM site`, whose one source table is
/// delivered only through a row-count carrier column of type `char(3)` (Utf8 first field; the relation is the
/// projection onto no column). One whole-crate `--no-cheating` Verus run each.
#[test]
#[ignore = "runs the pinned Verus toolchain and frontend; cargo test -p gendb-verification --test verus_params_entry -- --ignored"]
fn generated_modules_verify_for_fixed_and_carrier_statements() {
    let work = scratch("generated");
    let toolchain = VerusToolchain::from_env().unwrap();
    // (a) every parameter fixed.
    let mut reqs = requests();
    for (r, v) in reqs.iter_mut().zip(["12.50", "2020-06-30", "-7"]) {
        r.binding = BindingRequest::Fixed(v.into());
    }
    let doc = translate(&fixtures().join("query.sql"), &reqs);
    let fixed = instantiate(&doc, &declare(&doc, &reqs).unwrap()).unwrap();
    assert!(fixed.free.is_empty());
    // (b) a row-count carrier.
    let sql = work.join("count.sql");
    std::fs::write(&sql, "SELECT COUNT(*) AS n FROM site;\n").unwrap();
    let carrier = Instance::concrete(&translate(&sql, &[])).unwrap();
    let mut evidence = vec![];
    for (name, inst) in [("all_fixed", fixed), ("row_count_carrier", carrier)] {
        let delivered = source_declaration(&inst.doc, &analyze(&inst.doc).unwrap()).unwrap();
        if name == "row_count_carrier" {
            assert!(delivered.tables.len() == 1 && delivered.tables[0].columns.len() == 1 && delivered.tables[0].columns[0].row_count_only);
        }
        let files = candidate_framework_files(&inst, &delivered, name).unwrap();
        assert!(text(&files, "gendb_params.rs").contains("pub struct Params {\n}"));
        // Framework files, not author text: none is scanned by the refusal list (the fork/join file names vstd threads).
        let check = framework_check_files(&files);
        let unscanned: Vec<&str> = check.iter().map(|f| f.path.as_str()).collect();
        let frozen = freeze_framework_crate(&check, &unscanned, &work.join(name).join("frozen")).unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let run = run_verus(&toolchain, &frozen, &options(name), VerusMode::Verify, &work.join(name).join("verus")).unwrap();
        assert_eq!(run.outcome, VerusOutcome::Verified, "{name}: {}", run.rendered_errors());
        let summary = run.verification.clone().unwrap();
        assert!(summary.is_verifying_entire_crate && summary.errors == 0, "{summary:?}");
        evidence.push(serde_json::json!({"statement": name, "verification": summary}));
    }
    std::fs::write(work.join("generated-modules.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("generated-modules.json").display());
}

/// A template with two free `text` parameters and a free integer over the fixture schema, checked as the preflight
/// checks every statement (`query_statement_check_files`: library, schema, statement, parameter module, ABI and
/// argument types, shared entry submodules), in one whole-crate `--no-cheating` Verus run.
#[test]
#[ignore = "runs the pinned Verus toolchain and frontend; cargo test -p gendb-verification --test verus_params_entry -- --ignored"]
fn text_template_statement_check_verifies() {
    let work = scratch("text");
    let sql = work.join("text.sql");
    let statement = "SELECT id, tag FROM sensor WHERE tag <> $1 AND tag NOT LIKE $2 AND id < $3 AND day < $4";
    std::fs::write(&sql, format!("{statement};\n")).unwrap();
    let free = |index: u32, ty: &str| ParamRequest { index, name: None, sql_type: ty.into(), binding: BindingRequest::Free { min: None, max: None } };
    let reqs = [free(1, "text"), free(2, "text"), free(3, "integer"), free(4, "date")];
    let doc = translate(&sql, &reqs);
    let inst = instantiate(&doc, &declare(&doc, &reqs).unwrap()).unwrap();
    let files = query_statement_check_files(&inst, "text template").unwrap();
    let params = text(&files, "gendb_params.rs");
    for needle in ["pub p0: &'static [u8],", "pub p1: &'static [u8],", "fn text_arg_ok(b: &[u8]) -> (r: bool)", "pub fn bind_params(args: &[QueryArg])"] {
        assert!(params.contains(needle), "gendb_params lacks {needle}:\n{params}");
    }
    let query = text(&files, "query.rs");
    assert!(query.contains("&&& match ps[1] { Literal::Text(b) => text_ok(b), _ => false }"));
    assert!(query.contains("    assert(param_typed(param_example())) by (compute);\n") && query.contains("    assert(param_domain(param_example()));\n"));
    assert!(text(&files, "gendb_arguments.rs").contains("Text(&'static [u8]),"));
    let unscanned: Vec<&str> = files.iter().map(|f| f.path.as_str()).collect();
    let frozen = freeze_framework_crate(&files, &unscanned, &work.join("frozen")).unwrap_or_else(|e| panic!("{e:?}"));
    let toolchain = VerusToolchain::from_env().unwrap();
    let run = run_verus(&toolchain, &frozen, &options("text_template"), VerusMode::Verify, &work.join("verus")).unwrap();
    std::fs::write(work.join("run.json"), serde_json::to_vec_pretty(&run.record()).unwrap()).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Verified, "{}: {}{}", run.detail, run.rendered_errors(), run.stderr);
    let summary = run.verification.clone().unwrap();
    assert!(summary.is_verifying_entire_crate && summary.errors == 0, "{summary:?}");
    let evidence = serde_json::json!({"statement": statement, "wall_ns": run.wall_ns, "verification": summary});
    std::fs::write(work.join("text-template.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("text-template.json").display());
}
