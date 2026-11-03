//! Generator of `gendb_params.rs`, the parameter module of a candidate or query crate, from the free parameters of the
//! statement instance (`gendb_frontend::params::Instance::free`): free parameter `$index` is `ps[slot]` of
//! `crate::query::query_spec_at(ps)` and ABI argument `slot`.
//!
//! The module defines the bound values `Params` (field `p{slot}`, viewed as the binding `ps`), the argument view
//! `param_source` and the verified binder `bind_params`, which returns `Some` exactly when the arguments denote a
//! binding in the emitted domain `crate::query::param_domain`. The bounds given here only drive the executable
//! decision; Verus checks that decision against `param_domain`, so the domain is not restated. A statement without
//! free parameters gets an empty `Params` and the empty binding.
//!
//! The arguments are of the crate kind's argument type ([`ArgumentAbi`]): a v3 candidate binds the shared
//! `crate::gendb_abi::ParamArg` (integer, numeric, date; its text is unchanged), a query crate of the entry v4 binds
//! the query-only `crate::gendb_arguments::QueryArg`, which also carries `text` (its bytes as a `&'static [u8]` field,
//! viewed as `Literal::Text(bytes@)`).

use super::candidate::ENTRY_IDENTITY;
use super::AssemblyError;
use gendb_frontend::params::{FreeParam, ParamType, ParamValue, NUMERIC_PARAM_MAX_PRECISION};
use std::fmt::Write as _;

/// The argument type a parameter module binds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ArgumentAbi {
    /// `crate::gendb_abi::ParamArg` of the v3 candidate (ABI v3): integer, numeric and date parameters.
    SharedParamArg,
    /// `crate::gendb_arguments::QueryArg` of the query entry v4: also `text` parameters.
    QueryArg,
}

impl ArgumentAbi {
    fn type_name(self) -> &'static str {
        match self {
            ArgumentAbi::SharedParamArg => "ParamArg",
            ArgumentAbi::QueryArg => "QueryArg",
        }
    }

    /// The module's imports (the v3 text is unchanged).
    fn imports(self) -> &'static str {
        match self {
            ArgumentAbi::SharedParamArg => "use vstd::prelude::*;\n\
                use crate::gendb_abi::{CivilDate, ParamArg};\n\
                use crate::spec::ast::Literal;\n\
                use crate::spec::int::IntKind;\n\
                use crate::exec::ast::{ELiteral, view_lit};\n\
                use crate::exec::expr::lit_exec;\n\
                use crate::exec::datetime::{date_from_civil_exec, days_in_month_exec};\n\
                use crate::query::{param_domain, param_typed};\n\nverus! {\n\n",
            ArgumentAbi::QueryArg => "use vstd::prelude::*;\n\
                use crate::gendb_abi::CivilDate;\n\
                use crate::gendb_arguments::QueryArg;\n\
                use crate::spec::ast::Literal;\n\
                use crate::spec::int::IntKind;\n\
                use crate::spec::typing::text_ok;\n\
                use crate::exec::ast::{ELiteral, view_lit};\n\
                use crate::exec::expr::lit_exec;\n\
                use crate::exec::datetime::{date_from_civil_exec, days_in_month_exec};\n\
                use crate::query::{param_domain, param_typed};\n\nverus! {\n\n",
        }
    }
}

/// The generator's precondition: slots are dense and in ascending placeholder order (slot `k` at position `k`), each
/// ordered parameter's bounds are values of its type with `min <= max`, a text parameter has the text domain, and the
/// argument type carries every parameter type (text only in `QueryArg`).
pub(super) fn check_free_params(free: &[FreeParam], abi: ArgumentAbi) -> Result<(), AssemblyError> {
    for (k, p) in free.iter().enumerate() {
        if p.slot != k {
            return Err(AssemblyError::Params(format!(
                "parameter ${} has slot {} at position {k}: slots must be dense and in order",
                p.index, p.slot
            )));
        }
        if k > 0 && free[k - 1].index >= p.index {
            return Err(AssemblyError::Params("free parameters must be in ascending placeholder order".into()));
        }
        if p.ty == ParamType::Text && abi == ArgumentAbi::SharedParamArg {
            return Err(AssemblyError::Params(format!(
                "parameter ${}: text parameters need the query entry v4 argument type (gendb_arguments::QueryArg); the v3 ParamArg has no text",
                p.index
            )));
        }
        let domain_typed = match (p.ty, p.bounds()) {
            (ParamType::Int4 | ParamType::Int8, Some((ParamValue::Int(_), ParamValue::Int(_)))) => true,
            (ParamType::Numeric { precision, .. }, Some((ParamValue::Num(_), ParamValue::Num(_)))) => precision <= NUMERIC_PARAM_MAX_PRECISION,
            (ParamType::Date, Some((ParamValue::Date { .. }, ParamValue::Date { .. }))) => true,
            (ParamType::Text, None) => true,
            _ => false,
        };
        // Same-variant values compare field by field (dates as (y, m, d)).
        if !(domain_typed && p.bounds().is_none_or(|(min, max)| min <= max)) {
            return Err(AssemblyError::Params(format!("parameter ${}: bounds do not match its type or are empty", p.index)));
        }
    }
    Ok(())
}

/// `gendb_params.rs` of the free parameters `free` binding arguments of type `abi` (checked by
/// [`check_free_params`]). `identity` names the statement in the header only.
pub(super) fn params_module(free: &[FreeParam], identity: &str, abi: ArgumentAbi) -> String {
    let mut o = String::new();
    write_header(&mut o, free, identity, abi);
    o.push_str(abi.imports());
    write_params_type(&mut o, free);
    write_argument_view(&mut o, free, abi);
    if free.iter().any(|p| p.ty == ParamType::Text) {
        write_text_decision(&mut o);
    }
    write_domain_decision(&mut o, free);
    write_binder(&mut o, free, abi);
    o.push_str("} // verus!\n");
    o
}

fn write_header(o: &mut String, free: &[FreeParam], identity: &str, abi: ArgumentAbi) {
    let _ = writeln!(o, "// FRAMEWORK FILE, GENERATED by gendb_verification::obligations ({ENTRY_IDENTITY}) from the parameter");
    let _ = writeln!(o, "// declaration of {identity}: statement arguments (ABI slot order) -> the binding `ps` of `crate::query::query_spec_at`.");
    let _ = writeln!(o, "// The domain is the emitted `crate::query::param_domain` (not restated); `bind_params` decides it exactly.");
    if free.is_empty() {
        o.push_str("// No free parameter: the only binding is the empty one.\n");
    }
    for p in free {
        let _ = writeln!(o, "// Slot {} = ${} {} (ABI argument {} = {}::{}).", p.slot, p.index, p.ty.sql_name(), p.slot, abi.type_name(), arg_variant(p.ty));
    }
}

/// `Params` and its view: the binding `ps`, one literal per slot.
fn write_params_type(o: &mut String, free: &[FreeParam]) {
    o.push_str("/// The bound values of the free parameters (field `p{k}` = slot k). Created by the entry (`bind_params`); its view\n/// is the binding `ps` at which the claim is stated.\npub struct Params {\n");
    for p in free {
        let _ = writeln!(o, "    /// `${}` {}\n    pub p{}: {},", p.index, p.ty.sql_name(), p.slot, field_type(p.ty));
    }
    o.push_str("}\n\nimpl View for Params {\n    type V = Seq<Literal>;\n\n    open spec fn view(&self) -> Seq<Literal> {\n");
    let literals = free.iter().map(|p| spec_literal(p.ty, &format!("self.p{}", p.slot))).collect::<Vec<_>>().join(", ");
    let _ = writeln!(o, "        seq![{literals}]\n    }}\n}}\n");
}

/// `arg_literal_{k}`, `param_literals` and `param_source`: the binding the ABI arguments denote, if it is in the
/// declared domain.
fn write_argument_view(o: &mut String, free: &[FreeParam], abi: ArgumentAbi) {
    let arg = abi.type_name();
    for p in free {
        let k = p.slot;
        let _ = writeln!(
            o,
            "/// The literal of argument `a` for slot {k} (`${}`), if it has the slot's kind.\npub open spec fn arg_literal_{k}(a: {arg}) -> Option<Literal> {{\n    match a {{\n        {arg}::{}(x) => Some({}),\n        _ => None,\n    }}\n}}\n",
            p.index,
            arg_variant(p.ty),
            spec_literal(p.ty, "x")
        );
    }
    let _ = writeln!(o, "/// The literals of `args` when their count and kinds match the slots.\npub open spec fn param_literals(args: Seq<{arg}>) -> Option<Seq<Literal>> {{");
    let _ = write!(o, "    if args.len() == {}", free.len());
    for p in free {
        let _ = write!(o, " && arg_literal_{0}(args[{0}]) is Some", p.slot);
    }
    let literals = free.iter().map(|p| format!("arg_literal_{0}(args[{0}])->Some_0", p.slot)).collect::<Vec<_>>().join(", ");
    let _ = writeln!(o, " {{\n        Some(seq![{literals}])\n    }} else {{\n        None\n    }}\n}}\n");
    let _ = writeln!(
        o,
        "/// The binding the arguments denote, when it lies in the declared domain `crate::query::param_domain`.\n\
         pub open spec fn param_source(args: Seq<{arg}>) -> Option<Seq<Literal>> {{\n    match param_literals(args) {{\n        Some(ps) => if param_domain(ps) {{ Some(ps) }} else {{ None }},\n        None => None,\n    }}\n}}\n",
    );
}

/// `text_arg_ok`: the verified decision of `text_ok` (no NUL byte) over a text argument's bytes.
fn write_text_decision(o: &mut String) {
    o.push_str(
        "/// Decides `text_ok(b@)`: the argument has no NUL byte (the SQL text domain).\n\
         fn text_arg_ok(b: &[u8]) -> (r: bool)\n    ensures r == text_ok(b@),\n{\n    let mut i: usize = 0;\n\
         \x20   while i < b.len()\n        invariant\n            i <= b@.len(),\n            forall|j: int| 0 <= j < i ==> #[trigger] b@[j] != 0u8,\n\
         \x20       decreases b@.len() - i,\n    {\n        if b[i] == 0u8 {\n            assert(b@[i as int] == 0u8);\n            return false;\n        }\n\
         \x20       i += 1;\n    }\n    true\n}\n\n",
    );
}

/// `params_in_domain`: types by the verified literal evaluator (`lit_exec`), bounds compared directly (dates as
/// verified day numbers), text by `text_arg_ok` (a text literal is always typed).
fn write_domain_decision(o: &mut String, free: &[FreeParam]) {
    o.push_str("/// Decides `param_domain(p@)` (types by the verified literal evaluator, bounds by the verified day number).\nfn params_in_domain(p: &Params) -> (b: bool)\n    ensures b == param_domain(p@),\n{\n    let ghost ps = p@;\n");
    for p in free {
        let k = p.slot;
        let f = format!("p.p{k}");
        let Some((min, max)) = p.bounds() else {
            let _ = writeln!(o, "    assert(ps[{k}] == Literal::Text({f}@));");
            let _ = writeln!(o, "    if !text_arg_ok({f}) {{\n        return false;\n    }}");
            continue;
        };
        let _ = writeln!(o, "    let l{k} = {};", exec_literal(p.ty, &f));
        let _ = writeln!(o, "    assert(view_lit(l{k}) == ps[{k}]);");
        let _ = writeln!(o, "    if lit_exec(&l{k}).is_err() {{\n        assert(!param_typed(ps));\n        return false;\n    }}");
        match (p.ty, min, max) {
            (ParamType::Int4 | ParamType::Int8, ParamValue::Int(a), ParamValue::Int(b)) => {
                let _ = writeln!(o, "    if !({a}i64 <= {f} && {f} <= {b}i64) {{\n        return false;\n    }}");
            }
            (ParamType::Numeric { .. }, ParamValue::Num(a), ParamValue::Num(b)) => {
                let _ = writeln!(o, "    if !({a}i128 <= {f} && {f} <= {b}i128) {{\n        return false;\n    }}");
            }
            (ParamType::Date, ParamValue::Date { y: y0, m: m0, d: d0 }, ParamValue::Date { y: y1, m: m1, d: d1 }) => {
                let _ = writeln!(o, "    let _dim{k} = days_in_month_exec({f}.y as i64, {f}.m as i64);");
                let _ = writeln!(o, "    let day{k} = date_from_civil_exec({f}.y as i64, {f}.m as i64, {f}.d as i64);");
                let _ = writeln!(
                    o,
                    "    if !(date_from_civil_exec({y0}, {m0}, {d0}) <= day{k} && day{k} <= date_from_civil_exec({y1}, {m1}, {d1})) {{\n        return false;\n    }}"
                );
            }
            _ => unreachable!("bounds of their type, by check_free_params"),
        }
    }
    o.push_str("    true\n}\n\n");
}

/// `bind_params`: the entry's verified parameter binder.
fn write_binder(o: &mut String, free: &[FreeParam], abi: ArgumentAbi) {
    let arg = abi.type_name();
    let _ = writeln!(
        o,
        "/// The verified parameter binder of the entry: `Some(p)` exactly when the arguments denote a binding in the\n\
         /// declared domain, and then `p@` is that binding.\npub fn bind_params(args: &[{arg}]) -> (r: Option<Params>)\n    ensures\n        r matches Some(p) ==> param_source(args@) == Some(p@),\n        r is None ==> param_source(args@) is None,\n{{",
    );
    let _ = writeln!(o, "    if args.len() != {} {{\n        return None;\n    }}", free.len());
    for p in free {
        let _ = writeln!(o, "    let p{0} = match args[{0}] {{\n        {arg}::{1}(x) => x,\n        _ => return None,\n    }};", p.slot, arg_variant(p.ty));
    }
    let fields = free.iter().map(|p| format!("p{}", p.slot)).collect::<Vec<_>>().join(", ");
    let _ = writeln!(o, "    let p = Params {{ {fields} }};");
    o.push_str("    assert(param_literals(args@) == Some(p@));\n    if !params_in_domain(&p) {\n        return None;\n    }\n    Some(p)\n}\n\n");
}

/// Rust type of a `Params` field (and of the argument's payload). A text field borrows the host's argument bytes, like a
/// stored part, for the whole call (`crate::gendb_arguments`).
fn field_type(ty: ParamType) -> &'static str {
    match ty {
        ParamType::Int4 | ParamType::Int8 => "i64",
        ParamType::Numeric { .. } => "i128",
        ParamType::Date => "CivilDate",
        ParamType::Text => "&'static [u8]",
    }
}

/// The argument variant of the type (the same names in `ParamArg` and `QueryArg`).
fn arg_variant(ty: ParamType) -> &'static str {
    match ty {
        ParamType::Int4 | ParamType::Int8 => "Int",
        ParamType::Numeric { .. } => "Num",
        ParamType::Date => "Date",
        ParamType::Text => "Text",
    }
}

/// The spec `Literal` of value `x` (an expression of the field type).
fn spec_literal(ty: ParamType, x: &str) -> String {
    match ty {
        ParamType::Int4 => format!("Literal::Int {{ v: {x} as int, kind: IntKind::Int4 }}"),
        ParamType::Int8 => format!("Literal::Int {{ v: {x} as int, kind: IntKind::Int8 }}"),
        ParamType::Numeric { scale, .. } => format!("Literal::Num {{ coeff: {x} as int, scale: {scale} }}"),
        ParamType::Date => format!("Literal::Date {{ y: {x}.y as int, m: {x}.m as int, d: {x}.d as int }}"),
        ParamType::Text => format!("Literal::Text({x}@)"),
    }
}

/// The exec `ELiteral` of value `x` of an ordered type (text is decided by `text_arg_ok`).
fn exec_literal(ty: ParamType, x: &str) -> String {
    match ty {
        ParamType::Int4 => format!("ELiteral::Int {{ v: {x}, kind: IntKind::Int4 }}"),
        ParamType::Int8 => format!("ELiteral::Int {{ v: {x}, kind: IntKind::Int8 }}"),
        ParamType::Numeric { scale, .. } => format!("ELiteral::Num {{ coeff: {x}, scale: {scale} }}"),
        ParamType::Date => format!("ELiteral::Date {{ y: {x}.y, m: {x}.m, d: {x}.d }}"),
        ParamType::Text => unreachable!("text arguments are decided by text_arg_ok"),
    }
}
