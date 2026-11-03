//! Candidate field values of the case generator: the literal constants of AST subtrees, the value domains of the ABI
//! source types, and small probe values.

use super::DAYS_1970_TO_2000;
use gendb_frontend::ast::{AstDocument, FieldValue, Node, PgType};
use gendb_frontend::columns::SourceType;
use gendb_sqlspec::pg_text::parse_date;

/// Group-key texts, in the order keys take them: ASCII, case, multi-byte UTF-8, the empty text and trailing spaces.
pub(super) const TEXT_KEYS: &[&str] = &["A", "B", "N", "R", "Z", "a", "z", "\u{e9}", "\u{df}", "\u{65e5}\u{672c}", "\u{1F600}", "", " ", "A ", "AB", "O", "F"];

/// The values of a non-text source type in its ABI unit (`None` for text).
pub(super) fn field_domain(ty: SourceType) -> Option<(i128, i128)> {
    match ty {
        SourceType::Decimal { p, .. } => {
            let max = 10i128.checked_pow(p.min(38)).map_or(i128::MAX, |x| x - 1);
            Some((-max, max))
        }
        // 0001-01-01 .. 9999-12-31 (valid PostgreSQL dates) in days since 1970-01-01.
        SourceType::Date32 => Some((-719162, 2932896)),
        SourceType::Int32 => Some((i32::MIN as i128, i32::MAX as i128)),
        SourceType::Int64 => Some((i64::MIN as i128, i64::MAX as i128)),
        SourceType::Utf8 => None,
    }
}

/// Small values of a non-text type (in its unit; the first is the default field value).
pub(super) fn small_values(ty: SourceType) -> Vec<i128> {
    match ty {
        SourceType::Decimal { s, .. } => {
            let one = 10i128.pow(s.min(30));
            vec![one, 2 * one, 3 * one + 1, 7, -one, 10 * one + 5]
        }
        SourceType::Date32 => vec![0, 1, 365, 9000, 10000],
        _ => vec![1, 2, 3, -1, 7],
    }
}

/// A text value is in the declared column domain: NUL-free; `varchar(n)` at most n characters; `char(n)` canonical
/// (at most n characters and no trailing space).
pub(super) fn text_fits(ty: &PgType, text: &str) -> bool {
    !text.contains('\0')
        && match ty {
            PgType::Varchar { max_chars: Some(n) } => text.chars().count() as u64 <= *n,
            PgType::Bpchar { n: Some(n) } => text.chars().count() as u64 <= *n && !text.ends_with(' '),
            _ => true,
        }
}

pub(super) fn int_field(f: Option<&FieldValue>) -> Option<i128> {
    match f? {
        FieldValue::Int(s) => s.parse().ok(),
        FieldValue::Fixed(x) => Some(*x as i128),
        FieldValue::Nat(x) => Some(*x as i128),
        _ => None,
    }
}

/// Literal constants of a subtree, in field units by kind.
#[derive(Default, Clone, Debug)]
pub(super) struct Constants {
    /// Date32 days.
    pub dates: Vec<i128>,
    /// Day shifts of the interval literals found (a month counted as 28, 30, 31 and 365/12 days).
    pub shifts: Vec<i128>,
    pub ints: Vec<i128>,
    /// `(coefficient, scale)`.
    pub nums: Vec<(i128, u32)>,
    pub texts: Vec<String>,
}

pub(super) fn children_of(n: &Node) -> Vec<usize> {
    let mut out = vec![];
    for f in &n.fields {
        match f {
            FieldValue::Child(c) => out.push(*c),
            FieldValue::Children(cs) => out.extend(cs),
            _ => {}
        }
    }
    out
}

/// Add the literal constants of the subtree at `root` of the node arena `nodes` (a statement's or a CHECK's) to `out`.
pub(super) fn collect_constants(nodes: &[Node], root: usize, out: &mut Constants) {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        let n = &nodes[id];
        match n.tag.as_str() {
            "Text" => {
                if let Some(FieldValue::Bytes(t)) = n.field("bytes") {
                    out.texts.push(t.clone());
                }
            }
            "Date" => {
                if let (Some(y), Some(m), Some(d)) = (int_field(n.field("y")), int_field(n.field("m")), int_field(n.field("d")))
                    && let Some(days_since_2000) = parse_date(&format!("{y:04}-{m:02}-{d:02}"))
                {
                    out.dates.push(days_since_2000 as i128 + DAYS_1970_TO_2000 as i128);
                }
            }
            "AddInterval" => {
                if let Some(d) = int_field(n.field("days")) {
                    out.shifts.push(d);
                }
                if let Some(m) = int_field(n.field("months")) {
                    out.shifts.extend([m * 31, m * 30, m * 28, m * 365 / 12]);
                    if m % 12 == 0 {
                        out.shifts.extend([m / 12 * 365, m / 12 * 366]);
                    }
                }
            }
            "Int" => out.ints.extend(int_field(n.field("v"))),
            "Num" => {
                if let (Some(c), Some(s)) = (int_field(n.field("coeff")), int_field(n.field("scale"))) {
                    out.nums.push((c, s as u32));
                }
            }
            _ => {}
        }
        stack.extend(children_of(n));
    }
}

/// Values of a field of type `ty` next to the constants `c` (each constant -1, itself, +1 in field units), inside the
/// type's domain, sorted and distinct.
pub(super) fn values_near(ty: SourceType, c: &Constants) -> Vec<i128> {
    let Some((lo, hi)) = field_domain(ty) else { return vec![] };
    let mut v = vec![];
    match ty {
        SourceType::Date32 => {
            let mut shifts = c.shifts.clone();
            shifts.push(0);
            for d in &c.dates {
                for s in &shifts {
                    v.extend([d + s - 1, d + s, d + s + 1]);
                }
            }
        }
        SourceType::Decimal { s, .. } => {
            for (coeff, cs) in c.nums.iter().copied().chain(c.ints.iter().map(|i| (*i, 0))) {
                if cs <= s
                    && let Some(x) = 10i128.checked_pow(s - cs).and_then(|m| coeff.checked_mul(m))
                {
                    v.extend([x - 1, x, x + 1]);
                }
            }
        }
        _ => {
            for x in c.ints.iter().copied().chain(c.nums.iter().filter(|(_, s)| *s == 0).map(|(x, _)| *x)) {
                v.extend([x - 1, x, x + 1]);
            }
        }
    }
    v.retain(|x| (lo..=hi).contains(x));
    v.sort_unstable();
    v.dedup();
    v
}

/// The expression under integer/numeric widening casts: the column a comparison reads.
pub(super) fn peel_casts(doc: &AstDocument, mut e: usize) -> usize {
    while doc.nodes[e].tag == "Cast" {
        match doc.nodes[e].child("arg") {
            Some(c) => e = c,
            None => break,
        }
    }
    e
}

/// The subtree reads a column or a table (it is not a constant operand).
pub(super) fn subtree_reads_data(doc: &AstDocument, root: usize) -> bool {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        let n = &doc.nodes[id];
        if matches!(n.tag.as_str(), "Col" | "Table" | "Subquery") {
            return true;
        }
        stack.extend(children_of(n));
    }
    false
}
