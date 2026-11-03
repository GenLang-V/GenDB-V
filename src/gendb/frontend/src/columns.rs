//! Environment layout and source-column demand of a statement. Generic over the AST: any nesting, correlated
//! subqueries, derived tables, joins, templates. No query shape is refused here.
//!
//! **Layout.** `spec::eval` evaluates every expression, condition and aggregate argument in an environment
//! `ctx ++ row`: `ctx` is the environment of the enclosing evaluation (empty for the statement body; for a subquery, the
//! environment of the expression or condition that contains it), `row` a row of the node's input. `analyze` names
//! every position (`Slot`): a column of one FROM occurrence of a base table (`Base`), or a value computed by an
//! expression or aggregate node (`Computed`). A projection, GROUP BY key or subquery output that is a bare column
//! reference carries the referenced slot through.
//!
//! **Demand.** The semantics inspects stored values only
//! 1. where `Col(i)` reads position `i` of its environment (any depth: a correlated reference reads the outer
//!    occurrence's slot);
//! 2. where whole rows are observed: the statement's output rows, `Distinct` (row comparison), and the rows of a scalar
//!    subquery or of an `AnyCmp` (IN / ANY / ALL) subquery, whose columns become values;
//! 3. through row counts: every FROM occurrence enumerates its table's rows.
//!
//! `Exists` observes only whether its subquery has a row (row counts and the conditions deciding them, which are
//! reads); Filter, Product and LEFT JOIN copy rows without inspecting values; GROUP BY keys and aggregate arguments are
//! expressions (reads). A base column is **demanded** when a slot holding it is read (1) or observed (2). A computed
//! value's inputs are the reads of the expression that computes it, counted where that expression is evaluated (every
//! expression of the AST is evaluated, used or not, so its reads count unconditionally). Hence two databases that
//! agree on every table's rows restricted to the demanded columns (same row counts and order) have the same meaning,
//! errors included.
//!
//! The analysis is not trusted for soundness: the final claim quantifies over every database bound to the delivered
//! columns, so an omitted needed column leaves the claim unprovable, never wrong; columns that are not delivered remain
//! universally quantified. It decides provability and what the host binds.
//!
//! **Source declaration.** `source_declaration` maps the demand to what the ABI delivers: per distinct table (table id
//! order) its demanded columns in ordinal order with their representation and declared nullability (a nullable column
//! is delivered with its validity, one byte per row, 1 valid and 0 NULL). A table whose rows are counted but no column
//! is demanded delivers one NOT NULL column that carries the row count (the ABI transports rows only as columns).
//! Representation limits are named binding refusals, not query-shape refusals: `unbindable_source_type` (bool,
//! timestamp, numeric beyond precision 38), `no_bindable_column`. `declared_columns` applies the same rules to any
//! chosen columns (a storage declaration), which may also name a column that does not exist (`unknown_source_column`).
//!
//! Recursion follows the AST depth, which the parser bounds (Python recursion limit, `frontend_resource_limit`).

use crate::ast::{schema, AstDocument, FieldKind, FieldValue, Node, PgType, TableDef};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// What one environment or output position holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum Slot {
    /// Column `column` of base table `table`, read through the FROM occurrence `occurrence` (its `Table` node id).
    Base { occurrence: usize, table: usize, column: usize },
    /// The value computed by node `node` (an expression or aggregate).
    Computed { node: usize },
}

/// Layout of one node.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum NodeLayout {
    /// Literals, order keys and the statement root.
    None,
    /// An expression, condition or aggregate: the environment it is evaluated in.
    Env { env: Vec<Slot> },
    /// A query: the length of its context (a prefix of its children's environments) and its output row.
    Query { ctx_len: usize, output: Vec<Slot> },
}

/// Why a base column is demanded: the node ids that read it (`Col`) and that observe whole rows containing it.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct ColumnUses {
    pub read_by: Vec<usize>,
    pub observed_by: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ColumnDemand {
    /// Per node id.
    pub layout: Vec<NodeLayout>,
    /// FROM occurrences, `(Table node id, table id)`, in node order.
    pub occurrences: Vec<(usize, usize)>,
    /// Demanded base columns `(table id, column ordinal)`.
    pub columns: BTreeMap<(usize, usize), ColumnUses>,
    /// Tables whose rows the statement enumerates.
    pub tables: BTreeSet<usize>,
}

impl ColumnDemand {
    /// Demanded column ordinals of `table`.
    pub fn table_columns(&self, table: usize) -> Vec<usize> {
        self.columns.keys().filter(|(t, _)| *t == table).map(|(_, c)| *c).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LayoutError(pub String);

impl fmt::Display for LayoutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "layout: {}", self.0)
    }
}

impl std::error::Error for LayoutError {}

/// Query-consuming constructors that observe only the cardinality of their subquery (`spec::eval::eval_pred`).
const CARDINALITY_ONLY: &[&str] = &["Exists"];

/// Layout and demand of `doc` (a statement, a template or an instance).
pub fn analyze(doc: &AstDocument) -> Result<ColumnDemand, LayoutError> {
    let mut analysis = Analysis {
        doc,
        out: ColumnDemand { layout: vec![NodeLayout::None; doc.nodes.len()], occurrences: vec![], columns: BTreeMap::new(), tables: BTreeSet::new() },
    };
    let output = analysis.query(doc.body(), &[])?;
    analysis.observe(&output, doc.root);
    analysis.out.occurrences.sort_unstable();
    Ok(analysis.out)
}

/// Child `field` of a decoded node (the schema guarantees the field kind).
fn child(n: &Node, field: &str) -> usize {
    n.child(field).unwrap_or_else(|| unreachable!("{}.{field} is not a child", n.tag))
}

fn children<'n>(n: &'n Node, field: &str) -> &'n [usize] {
    n.children(field).unwrap_or_else(|| unreachable!("{}.{field} is not a child list", n.tag))
}

fn nat(n: &Node, field: &str) -> usize {
    match n.field(field) {
        Some(FieldValue::Nat(v)) => *v as usize,
        other => unreachable!("{}.{field} is not a nat: {other:?}", n.tag),
    }
}

struct Analysis<'a> {
    doc: &'a AstDocument,
    out: ColumnDemand,
}

impl<'a> Analysis<'a> {
    fn node(&self, id: usize) -> &'a Node {
        &self.doc.nodes[id]
    }

    /// The demand entry of `slot` when it holds a base column.
    fn uses_of(&mut self, slot: Slot) -> Option<&mut ColumnUses> {
        match slot {
            Slot::Base { table, column, .. } => Some(self.out.columns.entry((table, column)).or_default()),
            Slot::Computed { .. } => None,
        }
    }

    /// Node `by` observes the whole row `row`.
    fn observe(&mut self, row: &[Slot], by: usize) {
        for s in row {
            if let Some(uses) = self.uses_of(*s)
                && uses.observed_by.last() != Some(&by)
            {
                uses.observed_by.push(by);
            }
        }
    }

    /// The output slot of expression `e` in environment `env`: its source slot for a bare column reference.
    fn value_slot(&self, e: usize, env: &[Slot]) -> Slot {
        let n = self.node(e);
        match (n.tag.as_str(), n.field("index")) {
            ("Col", Some(FieldValue::Nat(i))) => env[*i as usize],
            _ => Slot::Computed { node: e },
        }
    }

    /// Query node `id` evaluated under context `ctx`; returns its output row.
    fn query(&mut self, id: usize, ctx: &[Slot]) -> Result<Vec<Slot>, LayoutError> {
        let n = self.node(id);
        let under = |input: &[Slot]| [ctx, input].concat();
        let output = match n.tag.as_str() {
            "Table" => {
                let table = nat(n, "table");
                self.out.occurrences.push((id, table));
                self.out.tables.insert(table);
                (0..self.doc.tables[table].columns.len()).map(|column| Slot::Base { occurrence: id, table, column }).collect()
            }
            "Filter" => {
                let input = self.query(child(n, "input"), ctx)?;
                self.scalar(child(n, "pred"), &under(&input))?;
                input
            }
            "Project" => {
                let input = self.query(child(n, "input"), ctx)?;
                let env = under(&input);
                let exprs = children(n, "exprs");
                for &e in exprs {
                    self.scalar(e, &env)?;
                }
                exprs.iter().map(|&e| self.value_slot(e, &env)).collect()
            }
            "Product" => [self.query(child(n, "left"), ctx)?, self.query(child(n, "right"), ctx)?].concat(),
            "LeftJoin" => {
                let row = [self.query(child(n, "left"), ctx)?, self.query(child(n, "right"), ctx)?].concat();
                self.scalar(child(n, "on"), &under(&row))?;
                row
            }
            "Aggregate" => {
                let input = self.query(child(n, "input"), ctx)?;
                let aggs = children(n, "aggs");
                for &a in aggs {
                    self.scalar(a, &under(&input))?;
                }
                aggs.iter().map(|&a| Slot::Computed { node: a }).collect()
            }
            "GroupBy" => {
                let input = self.query(child(n, "input"), ctx)?;
                let env = under(&input);
                let (keys, aggs) = (children(n, "keys"), children(n, "aggs"));
                for &e in keys.iter().chain(aggs) {
                    self.scalar(e, &env)?;
                }
                // A group's key value is its first member's (`spec::relation::group_rows`).
                keys.iter().map(|&k| self.value_slot(k, &env)).chain(aggs.iter().map(|&a| Slot::Computed { node: a })).collect()
            }
            "Distinct" => {
                let input = self.query(child(n, "input"), ctx)?;
                self.observe(&input, id);
                input
            }
            other => return Err(LayoutError(format!("node {id}: {other} is not a query constructor this analysis knows"))),
        };
        self.out.layout[id] = NodeLayout::Query { ctx_len: ctx.len(), output: output.clone() };
        Ok(output)
    }

    /// Expression, condition or aggregate `id` evaluated in `env`. Children of these sorts share `env`; a query child
    /// is a subquery with context `env`, whose rows become values unless the constructor observes only cardinality.
    fn scalar(&mut self, id: usize, env: &[Slot]) -> Result<(), LayoutError> {
        let n = self.node(id);
        self.out.layout[id] = NodeLayout::Env { env: env.to_vec() };
        if n.tag == "Col" {
            let i = nat(n, "index");
            let slot = *env.get(i).ok_or_else(|| LayoutError(format!("node {id}: Col({i}) outside its environment of {}", env.len())))?;
            if let Some(uses) = self.uses_of(slot) {
                uses.read_by.push(id);
            }
            return Ok(());
        }
        for ((_, kind), value) in schema().kinds[&n.tag].fields.iter().zip(&n.fields) {
            let FieldKind::Child(_, sort) = kind else { continue };
            let ids = match value {
                FieldValue::Child(c) => std::slice::from_ref(c),
                FieldValue::Children(cs) => cs.as_slice(),
                _ => unreachable!("child field"),
            };
            for &c in ids {
                match sort.as_str() {
                    "query" => {
                        let rows = self.query(c, env)?;
                        if !CARDINALITY_ONLY.contains(&n.tag.as_str()) {
                            self.observe(&rows, id);
                        }
                    }
                    "literal" => {}
                    _ => self.scalar(c, env)?,
                }
            }
        }
        Ok(())
    }
}

/// Representation of a delivered source column on the ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SourceType {
    /// `numeric(p, s)`, `p <= 38`: `i128` coefficient at scale `s`.
    Decimal { p: u32, s: u32 },
    /// `date`: `i32` days since 1970-01-01.
    Date32,
    /// `integer`: `i32`.
    Int32,
    /// `bigint`: `i64`.
    Int64,
    /// `text` / `varchar(n)` / `char(n)`: Utf8 offsets + bytes.
    Utf8,
}

/// Largest numeric precision the ABI delivers (an `i128` coefficient).
pub const SOURCE_DECIMAL_MAX_PRECISION: u64 = 38;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceColumn {
    pub ordinal: usize,
    pub name: String,
    pub ty: SourceType,
    /// Delivered only to carry the table's row count (no column of the table is demanded).
    pub row_count_only: bool,
    /// Declared nullable: delivered with its validity (one byte per row, 1 valid, 0 NULL). Serialized only when true,
    /// so the records of NOT NULL columns keep their form.
    #[serde(skip_serializing_if = "is_false")]
    pub nullable: bool,
}

fn is_false(b: &bool) -> bool {
    !*b
}

/// One distinct source table, `tables(v)[index]`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceTable {
    pub index: usize,
    pub table_id: usize,
    pub name: String,
    pub columns: Vec<SourceColumn>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceDeclaration {
    pub tables: Vec<SourceTable>,
}

/// Which representation limit of the ABI refused a binding. Serialized (and displayed) as the recorded reason string.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BindingRefusalReason {
    /// A demanded column has no ABI representation.
    UnbindableSourceType,
    /// A counted table has no NOT NULL column of an ABI type to carry its row count.
    NoBindableColumn,
    /// A chosen table or column is not in the schema (a storage declaration naming a column that does not exist).
    UnknownSourceColumn,
}

impl BindingRefusalReason {
    pub fn as_str(self) -> &'static str {
        match self {
            BindingRefusalReason::UnbindableSourceType => "unbindable_source_type",
            BindingRefusalReason::NoBindableColumn => "no_bindable_column",
            BindingRefusalReason::UnknownSourceColumn => "unknown_source_column",
        }
    }
}

impl fmt::Display for BindingRefusalReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A representation limit of the ABI binding (named; not a query-shape refusal).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BindingRefusal {
    pub reason: BindingRefusalReason,
    pub detail: String,
}

impl fmt::Display for BindingRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.reason, self.detail)
    }
}

impl std::error::Error for BindingRefusal {}

fn source_type(t: &PgType) -> Option<SourceType> {
    Some(match t {
        PgType::Numeric { typmod: Some((p, s)) } if *p <= SOURCE_DECIMAL_MAX_PRECISION => SourceType::Decimal { p: *p as u32, s: *s as u32 },
        PgType::Date => SourceType::Date32,
        PgType::Int4 => SourceType::Int32,
        PgType::Int8 => SourceType::Int64,
        PgType::Text | PgType::Varchar { .. } | PgType::Bpchar { .. } => SourceType::Utf8,
        _ => return None,
    })
}

/// The columns the ABI delivers for `doc` with demand `demand` (`analyze`).
pub fn source_declaration(doc: &AstDocument, demand: &ColumnDemand) -> Result<SourceDeclaration, BindingRefusal> {
    let selection = demand.tables.iter().map(|&t| (t, demand.table_columns(t).into_iter().collect())).collect();
    declared_columns(&doc.tables, &selection)
}

/// The columns the ABI delivers when `selection` maps each chosen table id of `schema` to its chosen column ordinals:
/// per table in id order, the chosen columns in ordinal order, or one row-count carrier when none is chosen. A
/// statement's demand (`source_declaration`) and a storage's chosen columns use the same rules.
pub fn declared_columns(schema: &[TableDef], selection: &BTreeMap<usize, BTreeSet<usize>>) -> Result<SourceDeclaration, BindingRefusal> {
    let unknown = |detail: String| BindingRefusal { reason: BindingRefusalReason::UnknownSourceColumn, detail };
    let mut tables = Vec::new();
    for (&t, chosen) in selection {
        let def = schema.get(t).ok_or_else(|| unknown(format!("table id {t} is not in the schema")))?;
        let mut columns = Vec::new();
        for &c in chosen {
            let col = def.columns.get(c).ok_or_else(|| unknown(format!("{}: column ordinal {c} is not in the table", def.name)))?;
            let refuse = |reason, why: &str| BindingRefusal { reason, detail: format!("{}.{} ({:?}) {why}", def.name, col.name, col.ty) };
            let ty = source_type(&col.ty)
                .ok_or_else(|| refuse(BindingRefusalReason::UnbindableSourceType, "has no ABI representation (numeric(p <= 38, s), date, integer, bigint, text)"))?;
            columns.push(SourceColumn { ordinal: c, name: col.name.clone(), ty, row_count_only: false, nullable: col.nullable });
        }
        if columns.is_empty() {
            columns.push(row_count_column(def)?);
        }
        tables.push(SourceTable { index: tables.len(), table_id: t, name: def.name.clone(), columns });
    }
    Ok(SourceDeclaration { tables })
}

/// The first NOT NULL column of an ABI type, delivered only to carry the row count of a table without demanded columns.
fn row_count_column(def: &TableDef) -> Result<SourceColumn, BindingRefusal> {
    def.columns
        .iter()
        .enumerate()
        .find_map(|(c, col)| if col.nullable { None } else { source_type(&col.ty).map(|ty| (c, col, ty)) })
        .map(|(c, col, ty)| SourceColumn { ordinal: c, name: col.name.clone(), ty, row_count_only: true, nullable: false })
        .ok_or_else(|| BindingRefusal {
            reason: BindingRefusalReason::NoBindableColumn,
            detail: format!("{}: no NOT NULL column of an ABI type carries its row count", def.name),
        })
}

/// Readable name of a slot for author inputs: `lineitem.l_orderkey@37` (occurrence = `Table` node id) or
/// `computed@12`.
pub fn slot_name(doc: &AstDocument, s: Slot) -> String {
    match s {
        Slot::Base { occurrence, table, column } => {
            let t = &doc.tables[table];
            format!("{}.{}@{occurrence}", t.name, t.columns[column].name)
        }
        Slot::Computed { node } => format!("computed@{node}"),
    }
}
