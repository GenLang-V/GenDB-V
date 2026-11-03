//! Constructor rendering, generic over the encoding schema's variant forms and field kinds, and the let-chains built
//! from it. A chain names node `i` of a post-order arena `{prefix}{i}`, so each constructor refers to its children by
//! name and the chain is linear in the AST size.
//!
//! Spec and exec renderings differ only in how they name children, lists, byte strings and parameters (`Names`):
//! spec values are plain names and `seq![..]` literals (with a template's free parameter `$n` rendered `ps[slot]`);
//! exec values bind lists and byte vectors to variables first, each with one extensional-equality step against the
//! ghost spec chain.

use super::{EmitError, EmitRefusal};
use crate::ast::{schema, ChildMode, FieldKind, FieldValue, Form, Machine, Node, ScalarTy, SortSpec};
use std::collections::BTreeMap;
use std::fmt::Write;

/// `let {prefix}{i} = <node i>;` for every node of a post-order arena (spec values).
pub fn spec_chain(out: &mut String, nodes: &[Node], prefix: &str) -> Result<(), EmitError> {
    for (i, n) in nodes.iter().enumerate() {
        writeln!(out, "    let {prefix}{i} = {};", constructor(n, &mut SpecNames::plain(prefix))?).unwrap();
    }
    Ok(())
}

/// The exec twin of an arena: per node a ghost spec value `{prefix}g{i}`, the exec value `{prefix}e{i}` and one view
/// step `assert(view(e) == g)` (lists and byte strings bound first with an extensional step).
pub fn exec_chain(out: &mut String, nodes: &[Node], prefix: &str) -> Result<(), EmitError> {
    let sch = schema();
    for (i, n) in nodes.iter().enumerate() {
        writeln!(out, "    let ghost {prefix}g{i} = {};", constructor(n, &mut SpecNames::plain(&format!("{prefix}g")))?).unwrap();
        let mut names = ExecNames { prefix: prefix.to_owned(), node: i, prelude: String::new() };
        let exec = constructor(n, &mut names)?;
        out.push_str(&names.prelude);
        writeln!(out, "    let {prefix}e{i} = {exec};").unwrap();
        writeln!(out, "    assert({}({prefix}e{i}) == {prefix}g{i});", sch.sorts[&sch.kinds[&n.tag].sort].view).unwrap();
    }
    Ok(())
}

/// How one side names the parts of a constructor application.
pub(super) trait Names {
    /// The type name of `sort` on this side (spec or exec).
    fn sort_type<'s>(&self, sort: &'s SortSpec) -> &'s str;
    fn child(&self, c: usize) -> String;
    /// A child list (field `field` of child sort `sort`).
    fn list(&mut self, field: &str, elems: &[usize], sort: &str) -> String;
    /// A byte string, given as its comma-separated `u8` literals.
    fn bytes(&mut self, bytes: &str) -> String;
    /// The value of statement parameter `$index` (form `param`).
    fn param(&mut self, index: u32) -> Result<String, EmitError>;
}

/// Spec values: the plain let-chain (`n{i}`), the ghost chain of `query_exec` (`g{i}`) or a template chain, with a name
/// prefix; in a template, free parameter `$n` is `{var}[slot]`.
pub(super) struct SpecNames {
    prefix: String,
    /// The binding variable and the slot of each free parameter index (templates only).
    params: Option<(String, BTreeMap<u32, usize>)>,
}

impl SpecNames {
    pub(super) fn plain(prefix: &str) -> Self {
        SpecNames { prefix: prefix.to_owned(), params: None }
    }

    pub(super) fn with_params(prefix: &str, var: &str, slots: &BTreeMap<u32, usize>) -> Self {
        SpecNames { prefix: prefix.to_owned(), params: Some((var.to_owned(), slots.clone())) }
    }
}

fn unbound(index: u32) -> EmitError {
    EmitError { reason: EmitRefusal::UnboundParameters, detail: format!("${index} has no value here (a template has no exec AST)") }
}

impl Names for SpecNames {
    fn sort_type<'s>(&self, sort: &'s SortSpec) -> &'s str {
        &sort.spec
    }

    fn child(&self, c: usize) -> String {
        format!("{}{c}", self.prefix)
    }

    fn list(&mut self, _: &str, elems: &[usize], _: &str) -> String {
        format!("seq![{}]", elems.iter().map(|&c| self.child(c)).collect::<Vec<_>>().join(", "))
    }

    fn bytes(&mut self, bytes: &str) -> String {
        format!("seq![{bytes}]")
    }

    fn param(&mut self, index: u32) -> Result<String, EmitError> {
        match &self.params {
            Some((var, slots)) => slots.get(&index).map(|k| format!("{var}[{k}]")).ok_or_else(|| unbound(index)),
            None => Err(unbound(index)),
        }
    }
}

/// Exec values of node `node`: lists and byte vectors are bound to variables first, each with one extensional-equality
/// step against the ghost chain (`prelude`).
struct ExecNames {
    prefix: String,
    node: usize,
    prelude: String,
}

impl Names for ExecNames {
    fn sort_type<'s>(&self, sort: &'s SortSpec) -> &'s str {
        &sort.exec
    }

    fn child(&self, c: usize) -> String {
        format!("{}e{c}", self.prefix)
    }

    fn list(&mut self, field: &str, elems: &[usize], sort: &str) -> String {
        let s = &schema().sorts[sort];
        let name = format!("{}l{}_{field}", self.prefix, self.node);
        let items = elems.iter().map(|&c| self.child(c)).collect::<Vec<_>>().join(", ");
        let ghosts = elems.iter().map(|c| format!("{}g{c}", self.prefix)).collect::<Vec<_>>().join(", ");
        writeln!(self.prelude, "    let {name}: Vec<{}> = vec![{items}];", s.exec).unwrap();
        let list_view = s.list_view.as_deref().expect("sorts used in seq fields declare list_view");
        writeln!(self.prelude, "    assert({list_view}({name}@) =~= seq![{ghosts}]);").unwrap();
        name
    }

    fn bytes(&mut self, bytes: &str) -> String {
        let name = format!("{}b{}", self.prefix, self.node);
        writeln!(self.prelude, "    let {name}: Vec<u8> = vec![{bytes}];\n    assert({name}@ =~= seq![{bytes}]);").unwrap();
        name
    }

    fn param(&mut self, index: u32) -> Result<String, EmitError> {
        Err(unbound(index))
    }
}

/// One constructor application for node `n`, generic over the schema's variant form and field kinds.
pub(super) fn constructor(n: &Node, names: &mut dyn Names) -> Result<String, EmitError> {
    let sch = schema();
    let kind = &sch.kinds[&n.tag];
    if kind.form == Form::Param {
        return names.param(n.param_index().expect("a param node has an index"));
    }
    let ty = names.sort_type(&sch.sorts[&kind.sort]);
    let mut args = Vec::with_capacity(kind.fields.len());
    for ((name, field_kind), value) in kind.fields.iter().zip(&n.fields) {
        let arg = match (field_kind, value) {
            (FieldKind::Child(ChildMode::Ref, _), FieldValue::Child(c)) => names.child(*c),
            (FieldKind::Child(ChildMode::Box, _), FieldValue::Child(c)) => format!("Box::new({})", names.child(*c)),
            (FieldKind::Child(ChildMode::Seq, s), FieldValue::Children(cs)) => names.list(name, cs, s),
            (FieldKind::Int(m), FieldValue::Int(v)) => integer(n, name, *m, v)?,
            (FieldKind::Nat(m), FieldValue::Nat(v)) => integer(n, name, *m, &v.to_string())?,
            (FieldKind::OptNat(m), FieldValue::OptNat(v)) => match v {
                Some(v) => format!("Some({})", integer(n, name, *m, &v.to_string())?),
                None => "None".into(),
            },
            // Typed suffix: in spec code an unsuffixed negative literal is an `int`, not the field's machine type.
            (FieldKind::Fixed(m), FieldValue::Fixed(v)) => format!("{v}{}", if *m == Machine::I32 { "i32" } else { "i64" }),
            (FieldKind::Bool, FieldValue::Bool(b)) => b.to_string(),
            (FieldKind::Bytes, FieldValue::Bytes(s)) => names.bytes(&s.bytes().map(|b| format!("{b}u8")).collect::<Vec<_>>().join(", ")),
            (FieldKind::ScalarTy, FieldValue::ScalarTy(t)) => scalar_ty(t),
            (FieldKind::Enum(e), FieldValue::Enum(v)) => format!("{e}::{v}"),
            _ => unreachable!("decoded field {}.{name} disagrees with the schema", n.tag),
        };
        args.push((name, arg));
    }
    let named_fields = || args.iter().map(|(n, a)| format!("{n}: {a}")).collect::<Vec<_>>().join(", ");
    Ok(match kind.form {
        Form::Unit => format!("{ty}::{}", n.tag),
        Form::Tuple => format!("{ty}::{}({})", n.tag, args.iter().map(|(_, a)| a.as_str()).collect::<Vec<_>>().join(", ")),
        Form::Struct => format!("{ty}::{} {{ {} }}", n.tag, named_fields()),
        Form::Record => format!("{ty} {{ {} }}", named_fields()),
        Form::Param => unreachable!("handled above"),
    })
}

/// An integer literal. The module holds both the spec and the exec AST, so the value must also fit the exec
/// representation (otherwise the static refusal `executable_domain`).
fn integer(n: &Node, field: &str, m: Machine, v: &str) -> Result<String, EmitError> {
    if !m.fits(v) {
        return Err(EmitError {
            reason: EmitRefusal::ExecutableDomain,
            detail: format!("{}.{field} = {v} does not fit the exec representation {m:?}", n.tag),
        });
    }
    Ok(v.to_owned())
}

fn scalar_ty(t: &ScalarTy) -> String {
    match t.scale {
        Some(s) => format!("ScalarTy::{} {{ scale: {s} }}", t.kind),
        None => format!("ScalarTy::{}", t.kind),
    }
}
