//! The meaning of a template (a statement with free parameters) at a binding `ps`.
//!
//! A template's parameter `$n` in slot `k` is the value `ps[k]`; `param_typed` states the declared types (`type_lit`),
//! `param_domain` adds the declared bounds (a `text` value: no NUL byte, `text_ok`; any byte string otherwise, so the
//! proof domain includes non-UTF-8 strings the host never sends). A template has no `query_spec`/`query_exec`; its
//! `lemma_query_wf_at` covers EVERY typed binding: typing is evaluated at one binding (`param_example`, the declared
//! minima, the empty text for a text slot) and transferred by the
//! library theorem `bridge::params::lemma_ordered_teq`, whose premise the emitted proof establishes node by node (two
//! chains over `ps` and the example, one equivalence step per node, linear in the AST).

use super::constructors::{constructor, Names, SpecNames};
use super::EmitError;
use crate::ast::{schema, ChildMode, FieldKind, FieldValue};
use crate::params::{FreeParam, Instance, ParamType, ParamValue};
use std::collections::BTreeMap;
use std::fmt::Write;

/// `param_typed`, `param_domain`, `param_example`, `query_spec_at` and `lemma_query_wf_at` of a template.
pub(super) fn emit_template(out: &mut String, inst: &Instance) -> Result<(), EmitError> {
    emit_parameter_interface(out, &inst.free)?;
    let slots: BTreeMap<u32, usize> = inst.free.iter().map(|f| (f.index, f.slot)).collect();
    emit_query_spec_at(out, inst, &slots)?;
    emit_lemma_query_wf_at(out, inst, &slots)
}

/// The declared slots, types and domain of the free parameters, and one binding in the domain (the minima) with its
/// membership lemma.
fn emit_parameter_interface(out: &mut String, free: &[FreeParam]) -> Result<(), EmitError> {
    writeln!(out, "/// Free statement parameters, `ps[slot]`:").unwrap();
    for f in free {
        let domain = match f.bounds() {
            Some(_) => format!("in {}", f.domain_text()),
            None => "without a NUL byte".into(),
        };
        writeln!(out, "/// - slot {}: `${}` {} {domain}", f.slot, f.index, f.ty.sql_name()).unwrap();
    }
    writeln!(out, "/// Every value has its declared static type (`type_lit`).\npub open spec fn param_typed(ps: Seq<Literal>) -> bool {{").unwrap();
    writeln!(out, "    &&& ps.len() == {}", free.len()).unwrap();
    for f in free {
        writeln!(out, "    &&& type_lit(ps[{}]) == Some(nn({}))", f.slot, f.ty.verus_scalar_ty()).unwrap();
    }
    let has_text = free.iter().any(|f| f.bounds().is_none());
    let domain_doc = if has_text { "typed, every ordered value within its inclusive bounds and every text without a NUL byte" } else { "typed, and every value within its inclusive bounds" };
    writeln!(out, "}}\n\n/// The declared domain: {domain_doc}.").unwrap();
    writeln!(out, "pub open spec fn param_domain(ps: Seq<Literal>) -> bool {{\n    &&& param_typed(ps)").unwrap();
    for f in free {
        writeln!(out, "    &&& {}", bound_condition(f, "ps")).unwrap();
    }
    writeln!(out, "}}\n").unwrap();
    let example = free.iter().map(|f| value_literal(f.ty, &example_value(f))).collect::<Result<Vec<_>, _>>()?;
    writeln!(out, "/// One binding in the domain: the declared minima{}.", if has_text { " (the empty text in a text slot)" } else { "" }).unwrap();
    writeln!(out, "pub open spec fn param_example() -> Seq<Literal> {{\n    seq![{}]\n}}\n", example.join(", ")).unwrap();
    writeln!(out, "pub proof fn lemma_param_example()\n    ensures param_domain(param_example()),\n{{").unwrap();
    if has_text {
        // `by (compute)` cannot evaluate the quantifier of `text_ok` (the pinned Verus panics on it): the types and
        // ordered bounds are computed, the text slots (`text_ok` of the empty text) are left to the solver.
        writeln!(out, "    assert(param_typed(param_example())) by (compute);").unwrap();
        for f in free.iter().filter(|f| f.bounds().is_some()) {
            writeln!(out, "    assert({}) by (compute);", bound_condition(f, "param_example()")).unwrap();
        }
    }
    let by_compute = if has_text { "" } else { " by (compute)" };
    writeln!(out, "    assert(param_domain(param_example())){by_compute};\n}}\n").unwrap();
    Ok(())
}

/// `query_spec_at(ps)`: the AST chain with free parameter `$n` rendered `ps[slot]`.
fn emit_query_spec_at(out: &mut String, inst: &Instance, slots: &BTreeMap<u32, usize>) -> Result<(), EmitError> {
    let doc = &inst.doc;
    writeln!(out, "/// The query's AST at binding `ps` of the free parameters (spec).").unwrap();
    writeln!(out, "pub open spec fn query_spec_at(ps: Seq<Literal>) -> OrderedQuery {{").unwrap();
    let mut names = SpecNames::with_params("n", "ps", slots);
    for (i, node) in doc.nodes.iter().enumerate() {
        writeln!(out, "    let n{i} = {};", constructor(node, &mut names)?).unwrap();
    }
    writeln!(out, "    n{}\n}}\n", doc.root).unwrap();
    Ok(())
}

/// Typing at every typed binding: evaluated at `param_example()`, then transferred node by node. Chain `a` is the AST
/// at `ps`, chain `b` at the example `p0`; each node gets one typing-equivalence step (and list steps via the sort's
/// `teq_intro`), so the premise of `lemma_ordered_teq` is established linearly in the AST.
fn emit_lemma_query_wf_at(out: &mut String, inst: &Instance, slots: &BTreeMap<u32, usize>) -> Result<(), EmitError> {
    let doc = &inst.doc;
    writeln!(out, "/// The AST is well-typed for the schema at every typed binding: typing evaluated at `param_example()`,").unwrap();
    writeln!(out, "/// transferred by `lemma_ordered_teq` (the two ASTs differ only in literals of equal static type).").unwrap();
    writeln!(out, "pub proof fn lemma_query_wf_at(ps: Seq<Literal>)\n    requires param_typed(ps),\n    ensures wf_ordered(schema_spec(), query_spec_at(ps)),\n{{").unwrap();
    // `by (compute)` evaluates closed terms only: the example is named by its function, not by a local.
    writeln!(out, "    assert(wf_ordered(schema_spec(), query_spec_at(param_example()))) by (compute);").unwrap();
    writeln!(out, "    let p0 = param_example();\n    lemma_param_example();").unwrap();
    let sch = schema();
    let (mut a, mut b) = (SpecNames::with_params("a", "ps", slots), SpecNames::with_params("b", "p0", slots));
    for (i, node) in doc.nodes.iter().enumerate() {
        writeln!(out, "    let a{i} = {};\n    let b{i} = {};", constructor(node, &mut a)?, constructor(node, &mut b)?).unwrap();
        let kind = &sch.kinds[&node.tag];
        for ((_, field_kind), value) in kind.fields.iter().zip(&node.fields) {
            if let (FieldKind::Child(ChildMode::Seq, sort), FieldValue::Children(cs)) = (field_kind, value)
                && let Some(intro) = &sch.sorts[sort].teq_intro
            {
                writeln!(out, "    {intro}({}, {});", a.list("", cs, sort), b.list("", cs, sort)).unwrap();
            }
        }
        if let Some(teq) = &sch.sorts[&kind.sort].teq {
            writeln!(out, "    assert({teq}(a{i}, b{i}));").unwrap();
        }
    }
    let r = doc.root;
    writeln!(out, "    assert(query_spec_at(ps) == a{r} && query_spec_at(p0) == b{r});").unwrap();
    writeln!(out, "    lemma_ordered_teq(schema_spec(), query_spec_at(ps), query_spec_at(p0));\n}}\n").unwrap();
    Ok(())
}

/// The Verus literal of a parameter value.
fn value_literal(ty: ParamType, v: &ParamValue) -> Result<String, EmitError> {
    constructor(&ty.literal_node(v), &mut SpecNames::plain(""))
}

/// The slot's value in `param_example`: the declared minimum, or the empty text (the least text in every collation).
fn example_value(f: &FreeParam) -> ParamValue {
    match f.bounds() {
        Some((min, _)) => min.clone(),
        None => ParamValue::Text(String::new()),
    }
}

/// `{binding}[slot]` lies within the declared domain (numeric at the declared scale, dates by day number, text without
/// NUL).
fn bound_condition(f: &FreeParam, binding: &str) -> String {
    let (k, ps) = (f.slot, binding);
    let Some((min, max)) = f.bounds() else {
        return format!("match {ps}[{k}] {{ Literal::Text(b) => text_ok(b), _ => false }}");
    };
    match (f.ty, min, max) {
        (ParamType::Int4 | ParamType::Int8, ParamValue::Int(lo), ParamValue::Int(hi)) => {
            format!("match {ps}[{k}] {{ Literal::Int {{ v, .. }} => {lo} <= v <= {hi}, _ => false }}")
        }
        (ParamType::Numeric { scale, .. }, ParamValue::Num(lo), ParamValue::Num(hi)) => {
            format!("match {ps}[{k}] {{ Literal::Num {{ coeff, scale }} => scale == {scale} && {lo} <= coeff <= {hi}, _ => false }}")
        }
        (ParamType::Date, ParamValue::Date { y: y0, m: m0, d: d0 }, ParamValue::Date { y: y1, m: m1, d: d1 }) => format!(
            "match {ps}[{k}] {{ Literal::Date {{ y, m, d }} => date_from_civil({y0}, {m0}, {d0}) <= date_from_civil(y, m, d) <= date_from_civil({y1}, {m1}, {d1}), _ => false }}"
        ),
        _ => unreachable!("bounds of ${} are not of its type", f.index),
    }
}
