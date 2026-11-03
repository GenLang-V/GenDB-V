//! SQL text of a constant subexpression, rendered from the AST for refusal messages (a document keeps no source
//! positions). The resolver's implicit casts appear as `CAST`, interval fields as PostgreSQL's interval text, and the
//! `char(n)` padding of a LIKE subject as `bpchar_pad(s, n)`.

use crate::ast::{FieldValue, Node};

/// The SQL text of the expression or condition `id`, without enclosing parentheses.
pub(super) fn render(nodes: &[Node], id: usize) -> String {
    let text = Renderer { nodes }.node(id);
    match text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        Some(inner) if balanced(inner) => inner.to_string(),
        _ => text,
    }
}

/// The parentheses of `s` never close more than they opened (so stripping an outer pair kept a matching pair).
fn balanced(s: &str) -> bool {
    let mut depth = 0i64;
    for c in s.chars() {
        depth += match c {
            '(' => 1,
            ')' => -1,
            _ => 0,
        };
        if depth < 0 {
            return false;
        }
    }
    depth == 0
}

struct Renderer<'a> {
    nodes: &'a [Node],
}

impl Renderer<'_> {
    fn node(&self, id: usize) -> String {
        let n = &self.nodes[id];
        let child = |name: &str| self.node(n.child(name).unwrap_or_else(|| unreachable!("decoded {} has {name}", n.tag)));
        let word = |name: &str| match n.field(name) {
            Some(FieldValue::Enum(s) | FieldValue::Int(s)) => s.clone(),
            Some(FieldValue::Nat(v)) => v.to_string(),
            Some(FieldValue::Fixed(v)) => v.to_string(),
            Some(FieldValue::Bool(b)) => b.to_string(),
            _ => String::new(),
        };
        match n.tag.as_str() {
            "Lit" => child("lit"),
            "Null" => "NULL".into(),
            "Bool" => word("value"),
            "Int" => word("v"),
            "Num" => decimal(&word("coeff"), word("scale").parse().unwrap_or(0)),
            "Date" => format!("DATE '{:0>4}-{:0>2}-{:0>2}'", word("y"), word("m"), word("d")),
            "Text" => match n.field("bytes") {
                Some(FieldValue::Bytes(s)) => format!("'{}'", s.replace('\'', "''")),
                _ => String::new(),
            },
            "Neg" => format!("-({})", child("arg")),
            "Arith" => {
                let op = match word("op").as_str() {
                    "Add" => "+",
                    "Sub" => "-",
                    _ => "*",
                };
                format!("({} {op} {})", child("a"), child("b"))
            }
            "Cast" => {
                let target = match word("cast").as_str() {
                    "Int4ToInt8" => "bigint",
                    "IntToNumeric" => "numeric",
                    _ => "timestamp",
                };
                format!("CAST({} AS {target})", child("arg"))
            }
            "AddInterval" => {
                let fields: Vec<String> = [("months", "months"), ("days", "days"), ("micros", "microseconds")]
                    .iter()
                    .filter(|(name, _)| word(name) != "0")
                    .map(|(name, unit)| format!("{} {unit}", word(name)))
                    .collect();
                let interval = if fields.is_empty() { "0 days".to_string() } else { fields.join(" ") };
                format!("({} + INTERVAL '{interval}')", child("arg"))
            }
            "Call" => self.call(&word("f"), n.children("args").unwrap_or_default()),
            "If" => format!("CASE WHEN {} THEN {} ELSE {} END", child("cond"), child("then_e"), child("else_e")),
            "Cmp" => {
                let op = match word("op").as_str() {
                    "Eq" => "=",
                    "Ne" => "<>",
                    "Lt" => "<",
                    "Le" => "<=",
                    "Gt" => ">",
                    _ => ">=",
                };
                format!("({} {op} {})", child("a"), child("b"))
            }
            "And" => format!("({} AND {})", child("a"), child("b")),
            "Or" => format!("({} OR {})", child("a"), child("b")),
            "Not" => format!("(NOT {})", child("p")),
            "IsNull" => format!("({} IS NULL)", child("e")),
            "OfBool" => child("e"),
            other => format!("<{other}>"),
        }
    }

    fn call(&self, f: &str, args: &[usize]) -> String {
        let a: Vec<String> = args.iter().map(|&id| self.node(id)).collect();
        match (f, a.as_slice()) {
            ("DivInt4" | "DivInt8" | "DivNumeric", [x, y]) => format!("({x} / {y})"),
            ("Like", [s, p, e]) => format!("({s} LIKE {p} ESCAPE {e})"),
            ("Substring2", [s, start]) => format!("SUBSTRING({s} FROM {start})"),
            ("Substring3", [s, start, len]) => format!("SUBSTRING({s} FROM {start} FOR {len})"),
            ("ExtractYear", [x]) => format!("EXTRACT(YEAR FROM {x})"),
            ("ExtractMonth", [x]) => format!("EXTRACT(MONTH FROM {x})"),
            ("ExtractDay", [x]) => format!("EXTRACT(DAY FROM {x})"),
            _ => format!("{}({})", if f == "PadBpchar" { "bpchar_pad" } else { f }, a.join(", ")),
        }
    }
}

/// `coeff·10^-scale` as a decimal literal (`60`, scale 3 -> `0.060`).
fn decimal(coeff: &str, scale: usize) -> String {
    let (sign, digits) = coeff.strip_prefix('-').map_or(("", coeff), |d| ("-", d));
    if scale == 0 {
        return format!("{sign}{digits}");
    }
    let padded = format!("{digits:0>width$}", width = scale + 1);
    let (int, frac) = padded.split_at(padded.len() - scale);
    format!("{sign}{int}.{frac}")
}

#[cfg(test)]
mod tests {
    use super::decimal;

    #[test]
    fn decimals_keep_their_scale() {
        assert_eq!(decimal("60", 3), "0.060");
        assert_eq!(decimal("-150", 2), "-1.50");
        assert_eq!(decimal("7", 0), "7");
    }
}
