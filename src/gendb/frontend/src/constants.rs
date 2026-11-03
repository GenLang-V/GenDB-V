//! Constant subexpressions that raise an SQL error: such a statement is refused after parsing.
//!
//! PostgreSQL evaluates the constant subexpressions of a statement while planning it (`eval_const_expressions`), so
//! their errors are raised whatever the data: `SELECT z FROM e WHERE z = 1/0` raises 22012 on an empty table, and so do
//! `CASE WHEN x > 0 THEN x ELSE 1/0 END` when no row takes the ELSE branch and `COALESCE(x, 1/0)` when no `x` is NULL.
//! SQLSpec evaluates an expression only when a row reaches it, so it would answer these statements with rows. They are
//! refused here, before any meaning is emitted, so no claim is made for them.
//!
//! **Constants.** A constant is a maximal literal-only expression or condition of the statement: literals and
//! operators, no column, no statement parameter `$n`, no subquery (anywhere in the statement, subqueries included).
//! Parameters are not constants: PostgreSQL folds a bound parameter only in a custom plan of a prepared statement, so
//! its outcome depends on the plan, and SQLSpec's row-by-row evaluation is one of PostgreSQL's outcomes. The
//! subject-independent part of LIKE is a constant too: PostgreSQL evaluates `s LIKE p ESCAPE e` as
//! `s ~~ like_escape(p, e)` and folds `like_escape` when `p` and `e` are constants, so an escape string of more than one
//! character raises 22025 whatever the subject (SQLSpec checks it before the subject as well, `spec::fns::like`).
//! The schema's CHECK constraints are not part of the statement and are not checked here.
//!
//! **Evaluation.** Each constant is evaluated exactly as SQLSpec defines it ([`eval`], [`functions`]: a transcription of
//! `spec::eval` and its operators on the machine representation of SQLSpec's executable interpreter). Refusals:
//! - `constant_expression_error`: the evaluation raises an SQL error (detail: its SQLSTATE; sql: the constant);
//! - `constant_expression_capacity`: an intermediate leaves the executable interpreter's machine domain (its outcome
//!   `Capacity`), so whether the constant raises is not decided.
//!
//! A literal the executable AST cannot represent and ill-typed operands are left to the emitter (`executable_domain`)
//! and to the verified typing check.
//!
//! **More than PostgreSQL.** PostgreSQL stops folding after a constant FALSE operand of AND, a constant TRUE operand of
//! OR and a non-NULL COALESCE argument, and it skips the branch a constant CASE condition does not take. Every constant
//! is checked here, so `false AND x = 1/0` and `CASE WHEN true THEN x ELSE 1/0 END` are refused although PostgreSQL
//! returns rows. A condition, CASE or COALESCE that is literal-only as a whole is one constant, evaluated as SQLSpec
//! does: lazy CASE (`COALESCE(1, 1/0)` and `CASE WHEN 1 > 0 THEN 1 ELSE 1/0 END` pass, as in PostgreSQL), strict AND and
//! OR (`false AND 1/0 = 1` is refused).
//!
//! **Trust.** Part of the trusted translator, and refusal-only: an accepted document is unchanged, so a mistake here
//! refuses too much or lets a statement through as before, but never changes a meaning. SQLSpec's verified interpreter
//! is not called: it is Verus code that the pinned Verus checks and compiles per statement
//! (`gendb_verification::reference`), and `gendb_sqlspec` depends on this crate; translation runs without Verus, also
//! when serving. Evaluation recurses over a constant, whose depth the Python parser bounds (`frontend_resource_limit`).

mod eval;
mod functions;
mod render;

use crate::ast::{schema, AstDocument, FieldValue, Node, Refusal};
use eval::{Evaluator, Stop};
use serde_json::json;

/// A constant raises an SQL error.
pub const CONSTANT_EXPRESSION_ERROR: &str = "constant_expression_error";
/// A constant leaves the machine domain of SQLSpec's executable interpreter.
pub const CONSTANT_EXPRESSION_CAPACITY: &str = "constant_expression_capacity";

/// The refusal reasons of this check and their meanings (the parser's own reasons are in
/// `parser/gendb_sql_frontend/refusal.py`).
pub const REASONS: [(&str, &str); 2] = [
    (
        CONSTANT_EXPRESSION_ERROR,
        "a constant subexpression (literals and operators only: no column, parameter or subquery) raises an SQL error in \
         SQLSpec; PostgreSQL evaluates constants while planning, so the statement raises it even when no row reaches it",
    ),
    (
        CONSTANT_EXPRESSION_CAPACITY,
        "a constant subexpression leaves the machine domain of SQLSpec's executable interpreter (Capacity), so whether \
         it raises an SQL error is not decided",
    ),
];

/// One constant of a statement.
enum Constant {
    /// A maximal literal-only expression or condition.
    Subtree(usize),
    /// `like_escape(pattern, escape)` of the LIKE call `call` whose pattern and escape are literal-only and whose
    /// subject is not.
    LikeEscape { call: usize, pattern: usize, escape: usize },
}

/// The refusal of the first constant of `doc` (in node order) whose evaluation raises an SQL error or leaves the
/// machine domain; `None` when every constant has a value or is left undecided.
pub fn refusal(doc: &AstDocument) -> Option<Refusal> {
    let nodes = &doc.nodes;
    let eval = Evaluator { nodes };
    constants(nodes).iter().find_map(|constant| match evaluate(&eval, constant) {
        Ok(()) | Err(Stop::Undecided) => None,
        Err(stop) => Some(refusal_of(nodes, constant, stop)),
    })
}

/// The refusal document of `refusal` for the statement `doc`, laid out as the parser writes documents (one line per
/// top-level key); `crate::ast::decode` reads it back as `refusal`.
pub fn refusal_document(doc: &AstDocument, refusal: &Refusal) -> String {
    let meaning = REASONS.iter().find(|(reason, _)| *reason == refusal.reason).map_or("", |(_, meaning)| meaning);
    let record = json!({"reason": refusal.reason, "meaning": meaning, "detail": refusal.detail, "path": refusal.path, "sql": refusal.sql});
    let lines = [
        ("format", json!(schema().format)),
        ("status", json!("refused")),
        ("frontend", doc.frontend.clone()),
        ("sql", json!(doc.sql)),
        ("refusal", record),
    ];
    let body: Vec<String> = lines.iter().map(|(key, value)| format!(" {}: {value}", json!(key))).collect();
    format!("{{\n{}\n}}\n", body.join(",\n"))
}

fn evaluate(eval: &Evaluator, constant: &Constant) -> Result<(), Stop> {
    match *constant {
        Constant::Subtree(id) if sort(&eval.nodes[id]) == "pred" => eval.pred(id).map(drop),
        Constant::Subtree(id) => eval.expr(id).map(drop),
        Constant::LikeEscape { pattern, escape, .. } => functions::like_escape(&eval.expr(pattern)?, &eval.expr(escape)?),
    }
}

/// The refusal of `constant`, whose evaluation stopped with an SQL error or `Capacity`.
fn refusal_of(nodes: &[Node], constant: &Constant, stop: Stop) -> Refusal {
    let (reason, detail) = match stop {
        Stop::Sql(error) => (
            CONSTANT_EXPRESSION_ERROR,
            format!(
                "SQLSTATE {} ({}): SQLSpec raises it whenever this constant is evaluated, and PostgreSQL evaluates the \
                 constant while planning",
                error.sqlstate(),
                error.condition()
            ),
        ),
        _ => (
            CONSTANT_EXPRESSION_CAPACITY,
            "an intermediate value of this constant leaves the machine domain of SQLSpec's executable interpreter \
             (Capacity)"
                .to_string(),
        ),
    };
    let (id, sql) = match *constant {
        Constant::Subtree(id) => (id, render::render(nodes, id)),
        Constant::LikeEscape { call, pattern, escape } => {
            (call, format!("LIKE {} ESCAPE {}", render::render(nodes, pattern), render::render(nodes, escape)))
        }
    };
    Refusal { reason: reason.into(), detail, path: node_path(nodes, id), sql }
}

/// The constants of the statement, in node order (children before parents).
fn constants(nodes: &[Node]) -> Vec<Constant> {
    let literal_only = literal_only(nodes);
    let parents = parents(nodes);
    let mut out = Vec::new();
    for (id, n) in nodes.iter().enumerate() {
        let in_constant = parents[id].as_ref().is_some_and(|(parent, _)| literal_only[*parent]);
        if literal_only[id] && matches!(sort(n), "expr" | "pred") && !in_constant {
            out.push(Constant::Subtree(id));
        } else if n.tag == "Call"
            && !literal_only[id]
            && matches!(n.field("f"), Some(FieldValue::Enum(f)) if f == "Like")
            && let Some(&[_, pattern, escape]) = n.children("args")
            && literal_only[pattern]
            && literal_only[escape]
        {
            out.push(Constant::LikeEscape { call: id, pattern, escape });
        }
    }
    out
}

/// Per node: it is a literal, expression or condition built from literals and operators only. No `Col` or `Param`,
/// and no subquery (a query node is never literal-only).
fn literal_only(nodes: &[Node]) -> Vec<bool> {
    let mut out: Vec<bool> = Vec::with_capacity(nodes.len());
    for n in nodes {
        let scalar = matches!(sort(n), "literal" | "expr" | "pred") && !matches!(n.tag.as_str(), "Col" | "Param");
        out.push(scalar && children(n).iter().all(|(_, child)| out[*child]));
    }
    out
}

fn sort(n: &Node) -> &'static str {
    schema().kinds[&n.tag].sort.as_str()
}

/// The children of `n` with their field labels (`b`, `args[1]`).
fn children(n: &Node) -> Vec<(String, usize)> {
    let fields = schema().kinds[&n.tag].fields.iter().zip(&n.fields);
    fields
        .flat_map(|((name, _), value)| match value {
            FieldValue::Child(c) => vec![(name.clone(), *c)],
            FieldValue::Children(cs) => cs.iter().enumerate().map(|(k, c)| (format!("{name}[{k}]"), *c)).collect(),
            _ => Vec::new(),
        })
        .collect()
}

/// Per node: its parent and the parent's field label, `None` for the root.
fn parents(nodes: &[Node]) -> Vec<Option<(usize, String)>> {
    let mut out = vec![None; nodes.len()];
    for (id, n) in nodes.iter().enumerate() {
        for (label, child) in children(n) {
            out[child] = Some((id, label));
        }
    }
    out
}

/// Where node `id` is: the field path from the root, e.g. `OrderedQuery.body/Filter.pred/Cmp.b`.
fn node_path(nodes: &[Node], id: usize) -> String {
    let parents = parents(nodes);
    let mut steps = Vec::new();
    let mut at = id;
    while let Some((parent, label)) = &parents[at] {
        steps.push(format!("{}.{label}", nodes[*parent].tag));
        at = *parent;
    }
    steps.reverse();
    steps.join("/")
}
