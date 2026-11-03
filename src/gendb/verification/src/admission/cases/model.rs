//! The generator's view of one statement instance (one admission binding): FROM occurrences, field slots, equality
//! classes, per-slot target values, and runs of the verified evaluator on assembled databases.

use super::constants::{Constants, collect_constants, field_domain, int_field, peel_casts, small_values, subtree_reads_data, text_fits, values_near};
use super::{CaseTables, CaseValue, complete_database};
use crate::admission::AdmissionError;
use gendb_frontend::ast::{AstDocument, FieldValue, PgType};
use gendb_frontend::columns::{ColumnDemand, NodeLayout, Slot, SourceDeclaration, SourceType};
use gendb_sqlspec::codec::RunOutcome;
use gendb_sqlspec::evaluator::EvaluatorLibrary;
use std::cell::Cell;
use std::collections::BTreeMap;

/// One row per FROM occurrence: `tuple[o]` is the row of occurrence `o` (its table's delivered columns).
pub(super) type Tuple = Vec<Vec<CaseValue>>;

pub struct Model<'a> {
    pub(super) doc: &'a AstDocument,
    pub(super) declaration: &'a SourceDeclaration,
    /// Per occurrence: its declaration table index.
    pub(super) occurrence_table: Vec<usize>,
    /// Occurrence node id -> occurrence index.
    occurrence_index: BTreeMap<usize, usize>,
    /// Field slots `(occurrence, delivered column position)`.
    pub(super) slots: Vec<(usize, usize)>,
    /// Equality classes over slot indices.
    pub(super) classes: Vec<Vec<usize>>,
    /// Per slot: values its column is compared with (field units).
    pub(super) targeted: Vec<Vec<CaseValue>>,
    /// Literal probes of the whole statement.
    everywhere: Constants,
    /// Slots of GROUP BY keys that are bare columns.
    pub(super) key_slots: Vec<usize>,
    /// ORDER BY output positions (for ties at the LIMIT boundary).
    order_columns: Vec<usize>,
    /// Per output position of the statement: the field slot it carries (a bare column), if any.
    output_slots: Vec<Option<usize>>,
    pub(super) limit: Option<u64>,
    pub(super) offset: u64,
    library: &'a EvaluatorLibrary,
    /// The evaluator's outcome on the empty database.
    empty: RunOutcome,
    /// Evaluator runs so far (recorded with the case set).
    pub(super) runs: Cell<u64>,
}

impl<'a> Model<'a> {
    /// The model of `doc` (a fully fixed instance) with its layout `demand`, over the statement's delivered columns
    /// `declaration`, labelled by `library` (the verified evaluator of `doc`).
    pub fn new(doc: &'a AstDocument, demand: &'a ColumnDemand, declaration: &'a SourceDeclaration, library: &'a EvaluatorLibrary) -> Result<Self, AdmissionError> {
        let mut occurrence_table = vec![];
        let mut occurrence_index = BTreeMap::new();
        for (node, table) in &demand.occurrences {
            let j = declaration
                .tables
                .iter()
                .position(|t| t.table_id == *table)
                .ok_or_else(|| AdmissionError::tool(format!("occurrence of table {table} is not delivered")))?;
            occurrence_index.insert(*node, occurrence_table.len());
            occurrence_table.push(j);
        }
        let slots: Vec<(usize, usize)> = occurrence_table
            .iter()
            .enumerate()
            .flat_map(|(o, j)| (0..declaration.tables[*j].columns.len()).map(move |k| (o, k)))
            .collect();
        let mut model = Model {
            doc,
            declaration,
            occurrence_table,
            occurrence_index,
            targeted: vec![vec![]; slots.len()],
            slots,
            classes: vec![],
            everywhere: Constants::default(),
            key_slots: vec![],
            order_columns: vec![],
            output_slots: vec![],
            limit: None,
            offset: 0,
            library,
            empty: RunOutcome::Rows(vec![]),
            runs: Cell::new(0),
        };
        collect_constants(&doc.nodes, doc.root, &mut model.everywhere);
        model.analyze_comparisons(demand);
        model.read_output_window(demand);
        model.empty = model.run(&vec![vec![]; declaration.tables.len()])?;
        Ok(model)
    }

    /// Output slots, ORDER BY columns, LIMIT and OFFSET of the statement root.
    fn read_output_window(&mut self, demand: &ColumnDemand) {
        let root = &self.doc.nodes[self.doc.root];
        if let Some(body) = root.child("body")
            && let NodeLayout::Query { output, .. } = &demand.layout[body]
        {
            self.output_slots = output.iter().map(|s| self.slot_of(*s)).collect();
        }
        for key in root.children("keys").unwrap_or_default() {
            if let Some(c) = int_field(self.doc.nodes[*key].field("col")) {
                self.order_columns.push(c as usize);
            }
        }
        self.limit = match root.field("limit") {
            Some(FieldValue::OptNat(l)) => *l,
            _ => None,
        };
        self.offset = match root.field("offset") {
            Some(FieldValue::Nat(o)) => *o,
            _ => 0,
        };
    }

    fn slot_of(&self, s: Slot) -> Option<usize> {
        match s {
            Slot::Base { occurrence, table, column } => {
                let o = *self.occurrence_index.get(&occurrence)?;
                let j = self.occurrence_table[o];
                debug_assert_eq!(self.declaration.tables[j].table_id, table);
                let k = self.declaration.tables[j].columns.iter().position(|c| c.ordinal == column)?;
                self.slots.iter().position(|x| *x == (o, k))
            }
            Slot::Computed { .. } => None,
        }
    }

    /// The field slot a (cast-peeled) column reference reads, if any.
    fn column_slot(&self, demand: &ColumnDemand, e: usize) -> Option<usize> {
        let e = peel_casts(self.doc, e);
        let n = &self.doc.nodes[e];
        if n.tag != "Col" {
            return None;
        }
        let i = int_field(n.field("index"))? as usize;
        match &demand.layout[e] {
            NodeLayout::Env { env } => self.slot_of(*env.get(i)?),
            _ => None,
        }
    }

    pub(super) fn ty(&self, p: usize) -> SourceType {
        let (o, k) = self.slots[p];
        self.declaration.tables[self.occurrence_table[o]].columns[k].ty
    }

    pub(super) fn pg_type(&self, p: usize) -> &PgType {
        let (o, k) = self.slots[p];
        let t = &self.declaration.tables[self.occurrence_table[o]];
        &self.doc.tables[t.table_id].columns[t.columns[k].ordinal].ty
    }

    /// Equality classes (`Col = Col` of one type), per-slot targets (constants a column is compared with, IN lists and
    /// subqueries of `ANY`), and bare GROUP BY key slots. Class members share their targets.
    fn analyze_comparisons(&mut self, demand: &ColumnDemand) {
        let mut equal_pairs = vec![];
        for n in &self.doc.nodes {
            match n.tag.as_str() {
                "Cmp" | "AnyCmp" => {
                    let Some(a) = n.child(if n.tag == "Cmp" { "a" } else { "e" }) else { continue };
                    let b = n.child("b");
                    let op = match n.field("op") {
                        Some(FieldValue::Enum(o)) => o.as_str(),
                        _ => "",
                    };
                    let (sa, sb) = (self.column_slot(demand, a), b.and_then(|b| self.column_slot(demand, b)));
                    if let (Some(x), Some(y)) = (sa, sb)
                        && op == "Eq"
                        && self.ty(x) == self.ty(y)
                    {
                        equal_pairs.push((x, y));
                    }
                    // A column compared with a constant operand: that operand's constants are its targets.
                    for (slot, other) in [(sa, b), (sb, Some(a))] {
                        if let (Some(p), Some(other)) = (slot, other)
                            && !subtree_reads_data(self.doc, other)
                        {
                            let mut c = Constants::default();
                            collect_constants(&self.doc.nodes, other, &mut c);
                            self.add_targets(p, &c);
                        }
                    }
                    // IN (list) / ANY: the subquery's constants.
                    if n.tag == "AnyCmp"
                        && let (Some(p), Some(q)) = (sa, n.child("q"))
                    {
                        let mut c = Constants::default();
                        collect_constants(&self.doc.nodes, q, &mut c);
                        self.add_targets(p, &c);
                    }
                }
                "Call" if matches!(n.field("f"), Some(FieldValue::Enum(f)) if f == "Like") => {
                    // `s LIKE p ESCAPE e` with a column subject and constant pattern: texts that match the pattern.
                    let args = n.children("args").unwrap_or_default();
                    let (Some(subject), Some(pattern)) = (args.first(), args.get(1)) else { continue };
                    let Some(p) = self.like_subject_slot(demand, *subject) else { continue };
                    if subtree_reads_data(self.doc, *pattern) {
                        continue;
                    }
                    let mut patterns = Constants::default();
                    collect_constants(&self.doc.nodes, *pattern, &mut patterns);
                    let mut escapes = Constants::default();
                    if let Some(e) = args.get(2) {
                        collect_constants(&self.doc.nodes, *e, &mut escapes);
                    }
                    let escape = escapes.texts.first().map_or(Some('\\'), |e| e.chars().next());
                    let matching: Vec<String> = patterns.texts.iter().flat_map(|t| like_matches(t, escape)).collect();
                    self.add_text_targets(p, &matching);
                }
                "GroupBy" => {
                    for key in n.children("keys").unwrap_or_default() {
                        if let Some(p) = self.column_slot(demand, *key) {
                            self.key_slots.push(p);
                        }
                    }
                }
                _ => {}
            }
        }
        for (a, b) in equal_pairs {
            self.join_classes(a, b);
        }
        for class in self.classes.clone() {
            let mut all: Vec<CaseValue> = class.iter().flat_map(|p| self.targeted[*p].clone()).collect();
            all.sort();
            all.dedup();
            for p in &class {
                self.targeted[*p] = all.clone();
            }
        }
        self.key_slots.sort_unstable();
        self.key_slots.dedup();
    }

    /// The slot a LIKE subject reads: a column, under casts or the blank padding of a `char(n)` subject.
    fn like_subject_slot(&self, demand: &ColumnDemand, e: usize) -> Option<usize> {
        let n = &self.doc.nodes[e];
        let padded = n.tag == "Call" && matches!(n.field("f"), Some(FieldValue::Enum(f)) if f == "PadBpchar");
        let column = if padded { *n.children("args")?.first()? } else { e };
        self.column_slot(demand, column)
    }

    /// Add the texts in `texts` that fit slot `p`'s column as its targets.
    fn add_text_targets(&mut self, p: usize, texts: &[String]) {
        for t in texts {
            let v = CaseValue::Text(t.clone());
            if text_fits(self.pg_type(p), t) && !self.targeted[p].contains(&v) {
                self.targeted[p].push(v);
            }
        }
    }

    fn join_classes(&mut self, a: usize, b: usize) {
        let ia = self.classes.iter().position(|c| c.contains(&a));
        let ib = self.classes.iter().position(|c| c.contains(&b));
        match (ia, ib) {
            (Some(i), Some(j)) if i != j => {
                let other = self.classes.remove(j.max(i));
                self.classes[j.min(i)].extend(other);
            }
            (Some(_), Some(_)) => {}
            (Some(i), None) => self.classes[i].push(b),
            (None, Some(j)) => self.classes[j].push(a),
            (None, None) => self.classes.push(vec![a, b]),
        }
    }

    fn add_targets(&mut self, p: usize, c: &Constants) {
        let ty = self.ty(p);
        let values: Vec<CaseValue> = if ty == SourceType::Utf8 {
            c.texts.iter().filter(|t| text_fits(self.pg_type(p), t)).cloned().map(CaseValue::Text).collect()
        } else {
            values_near(ty, c).into_iter().map(CaseValue::Num).collect()
        };
        for v in values {
            if !self.targeted[p].contains(&v) {
                self.targeted[p].push(v);
            }
        }
    }

    pub(super) fn class_of(&self, p: usize) -> Vec<usize> {
        self.classes.iter().find(|c| c.contains(&p)).cloned().unwrap_or_else(|| vec![p])
    }

    /// The slot of occurrence `o`'s delivered column `k`.
    pub(super) fn slot(&self, o: usize, k: usize) -> usize {
        self.slots.iter().position(|x| *x == (o, k)).expect("every (occurrence, delivered column) is a slot")
    }

    /// Set slot `p` and its whole equality class.
    pub(super) fn set_class(&self, t: &mut Tuple, p: usize, v: &CaseValue) {
        for q in self.class_of(p) {
            let (o, k) = self.slots[q];
            t[o][k] = v.clone();
        }
    }

    /// Set slot `p` alone.
    pub(super) fn put(&self, t: &mut Tuple, p: usize, v: CaseValue) {
        let (o, k) = self.slots[p];
        t[o][k] = v;
    }

    pub(super) fn get(&self, t: &Tuple, p: usize) -> CaseValue {
        let (o, k) = self.slots[p];
        t[o][k].clone()
    }

    /// Every candidate value of a slot (targets first).
    pub(super) fn candidates(&self, p: usize) -> Vec<CaseValue> {
        let ty = self.ty(p);
        let mut out = self.targeted[p].clone();
        if ty == SourceType::Utf8 {
            for t in self.everywhere.texts.iter().map(String::as_str).chain(["A", "B", "\u{e9}"]) {
                let v = CaseValue::Text(t.to_string());
                if text_fits(self.pg_type(p), t) && !out.contains(&v) {
                    out.push(v);
                }
            }
        } else {
            let (lo, hi) = field_domain(ty).expect("a non-text type has a numeric domain");
            for x in values_near(ty, &self.everywhere).into_iter().chain(small_values(ty)).chain([0, lo, hi]) {
                let v = CaseValue::Num(x);
                if (lo..=hi).contains(&x) && !out.contains(&v) {
                    out.push(v);
                }
            }
        }
        out
    }

    pub(super) fn base_value(&self, p: usize) -> CaseValue {
        if self.ty(p) == SourceType::Utf8 { CaseValue::Text("A".into()) } else { CaseValue::Num(small_values(self.ty(p))[0]) }
    }

    /// The database of `tuples`: each table holds the distinct rows of its occurrences, tuple by tuple; with
    /// `distinct`, a row equal to an earlier row of the same table is kept once.
    pub(super) fn assemble(&self, tuples: &[Tuple], distinct: bool) -> CaseTables {
        let mut tables: CaseTables = vec![vec![]; self.declaration.tables.len()];
        for t in tuples {
            let mut own: CaseTables = vec![vec![]; self.declaration.tables.len()];
            for (o, j) in self.occurrence_table.iter().enumerate() {
                if !own[*j].contains(&t[o]) {
                    own[*j].push(t[o].clone());
                }
            }
            for (j, rows) in own.into_iter().enumerate() {
                for r in rows {
                    if !distinct || !tables[j].contains(&r) {
                        tables[j].push(r);
                    }
                }
            }
        }
        tables
    }

    /// The verified evaluator's outcome on the complete database of a case's delivered tables.
    pub fn run(&self, tables: &CaseTables) -> Result<RunOutcome, AdmissionError> {
        self.runs.set(self.runs.get() + 1);
        self.library
            .run(&complete_database(&self.doc.tables, self.declaration, tables))
            .map_err(|e| AdmissionError::tool(format!("reference evaluator: {e}")))
    }

    /// The tuple's database has a result other than the empty input's.
    pub(super) fn qualifies(&self, t: &Tuple) -> Result<bool, AdmissionError> {
        Ok(match self.run(&self.assemble(std::slice::from_ref(t), true))? {
            RunOutcome::Rows(r) => RunOutcome::Rows(r) != self.empty,
            _ => false,
        })
    }

    /// Slot `p` (or its equality class) is carried by an ORDER BY output column.
    pub(super) fn ordered_key(&self, p: usize) -> bool {
        let class = self.class_of(p);
        self.order_columns.iter().any(|c| self.output_slots.get(*c).copied().flatten().is_some_and(|q| class.contains(&q)))
    }

    pub(super) fn slot_label(&self, p: usize) -> String {
        let (o, k) = self.slots[p];
        let t = &self.declaration.tables[self.occurrence_table[o]];
        format!("occurrence {o} ({}).{}", t.name, t.columns[k].name)
    }
}

/// Two texts that match the LIKE `pattern` with escape character `escape` (`None`: no escaping): every `%` as the empty
/// text and as `zz`, every `_` as `x` and as `y`, an escaped character as itself.
fn like_matches(pattern: &str, escape: Option<char>) -> [String; 2] {
    let (mut short, mut long) = (String::new(), String::new());
    let mut chars = pattern.chars();
    while let Some(c) = chars.next() {
        match c {
            c if Some(c) == escape => {
                if let Some(literal) = chars.next() {
                    short.push(literal);
                    long.push(literal);
                }
            }
            '%' => long.push_str("zz"),
            '_' => {
                short.push('x');
                long.push('y');
            }
            c => {
                short.push(c);
                long.push(c);
            }
        }
    }
    [short, long]
}

#[cfg(test)]
mod tests {
    use super::like_matches;

    #[test]
    fn like_matches_replace_wildcards_and_keep_escaped_characters() {
        assert_eq!(like_matches("%BRASS", Some('\\')), ["BRASS".to_string(), "zzBRASS".to_string()]);
        assert_eq!(like_matches("%special%requests%", Some('\\')), ["specialrequests".to_string(), "zzspecialzzrequestszz".to_string()]);
        assert_eq!(like_matches("a_\\%b", Some('\\')), ["ax%b".to_string(), "ay%b".to_string()]);
        assert_eq!(like_matches("a\\_", None), ["a\\x".to_string(), "a\\y".to_string()]);
    }
}
