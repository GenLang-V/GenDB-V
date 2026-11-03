//! Generator of the fixed flat storages (`storage_policy` `fixed_flat`): for one table of the dataset schema, the
//! storage `flat_<table>` that stores every column of the table as plain typed arrays in source row order, written by
//! GenDB instead of an author. Its two author roots are generated here from the storage declaration alone:
//!
//! - `stores/flat_<table>/interface/mod.rs`: part constants, `represents`, the lossless lemma and the readers;
//! - `builder/mod.rs`: `flat_parts` (the delivered columns as parts), the lemma that they represent the delivered table,
//!   and `build`, which copies each delivered column into its part.
//!
//! The crate around them is the ordinary storage crate of the fixed storage entry v1 (`storage_crate_files`), checked
//! by the same whole-crate Verus run as every storage; nothing here is trusted: Verus checks what is emitted, and the
//! final claims are the fixed entries'. Generation is deterministic (no options, no data), so a package's sources can
//! be compared with a fresh generation for its declaration ([`flat_storage_of`]).
//!
//! Representation, fixed by the declared SQL type and never by the data (the canonical native columns of a capture,
//! `gendb_storage::io::NativeColumn`): bigint I64; integer I32; date I32 days since 1970-01-01; numeric(p, s) with
//! p <= 38 I128 coefficient (value = coefficient * 10^-s); text, varchar and char I64 offsets (rows + 1, positions in
//! the bytes part, as delivered) and U8 UTF-8 bytes. One part per column, two for text, in column order; nothing else
//! is stored (no sorting, partitioning, index, permutation, compression, dictionary or skip metadata). A nullable
//! column has one more part after its value part(s): its validity, U8, one byte per row (0: the row is NULL, and its
//! value bytes mean nothing), the capture's validity buffer as delivered. A table of NOT NULL columns generates exactly
//! the text it generated before nullable columns were stored. A type without a native column is refused.

use super::declared::{ColumnKind, DeclaredColumn, DeclaredSource, DeclaredType};
use super::source_module::case_split;
use super::storage_crate::StorageName;
use super::AssemblyError;
use crate::verus::FrameworkSource;
use gendb_frontend::ast::TableDef;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

/// Identity of this generator, recorded with every flat storage registration.
pub const FLAT_STORAGE_GENERATOR: &str = "gendb-flat-storage-v1";

/// Element type of one flat part (the `PartView` variant).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlatElem {
    I32,
    I64,
    I128,
    U8,
}

impl FlatElem {
    /// The `PartView` / `OwnedPart` variant name.
    pub fn variant(self) -> &'static str {
        match self {
            Self::I32 => "I32",
            Self::I64 => "I64",
            Self::I128 => "I128",
            Self::U8 => "U8",
        }
    }

    /// Rust element type.
    fn rust(self) -> &'static str {
        match self {
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::I128 => "i128",
            Self::U8 => "u8",
        }
    }

    /// The interface's spec accessor of this variant's elements.
    fn accessor(self) -> &'static str {
        match self {
            Self::I32 => "i32s",
            Self::I64 => "i64s",
            Self::I128 => "i128s",
            Self::U8 => "u8s",
        }
    }

    /// Bytes per element.
    pub fn width(self) -> u64 {
        match self {
            Self::I32 => 4,
            Self::I64 => 8,
            Self::I128 => 16,
            Self::U8 => 1,
        }
    }
}

/// Which buffer of its column a flat part holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlatBuffer {
    /// One value per row (fixed-width columns).
    Values,
    /// Text offsets, rows + 1.
    Offsets,
    /// Text bytes.
    Bytes,
    /// Validity of a nullable column, one byte per row (0: NULL).
    Validity,
}

/// One part of a flat storage: the column (table ordinal and name) and which of its buffers it holds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatPart {
    /// The part's constant in the interface (`L_SHIPDATE`, `L_COMMENT_OFFSETS`).
    pub constant: String,
    pub ordinal: usize,
    pub column: String,
    pub buffer: FlatBuffer,
    pub elem: FlatElem,
}

/// The flat storage of one table: its name, declaration (every column of the table), parts and generated author files
/// (paths relative to the crate's `src/`).
#[derive(Clone, Debug)]
pub struct FlatStorage {
    pub name: StorageName,
    pub table: String,
    pub declaration: DeclaredSource,
    pub parts: Vec<FlatPart>,
    pub files: Vec<FrameworkSource>,
}

/// The flat storage of table `table_id` of the dataset schema: every column of the table, in table order.
pub fn flat_storage(schema: &[TableDef], table_id: usize) -> Result<FlatStorage, AssemblyError> {
    let table = schema.get(table_id).ok_or_else(|| AssemblyError::Storage(format!("flat storage: table id {table_id} outside the schema")))?;
    let selection = BTreeMap::from([(table_id, (0..table.columns.len()).collect::<BTreeSet<usize>>())]);
    let declaration = DeclaredSource::for_storage(schema, &selection)
        .map_err(|e| AssemblyError::Storage(format!("flat_storage_unsupported_column: table {}: {e}", table.name)))?;
    let flat = flat_storage_of(&declaration)?;
    if flat.parts.iter().map(|p| p.ordinal).collect::<BTreeSet<_>>().len() != table.columns.len() {
        return Err(AssemblyError::Storage(format!("flat_storage_unsupported_column: table {} is not stored column for column", table.name)));
    }
    Ok(flat)
}

/// The flat storage of `declaration` (one table, its columns in table order, none a row-count carrier): the generation
/// both preparation and the eligibility check of an admitted package use.
pub fn flat_storage_of(declaration: &DeclaredSource) -> Result<FlatStorage, AssemblyError> {
    let refuse = |message: String| Err(AssemblyError::Storage(format!("flat_storage_unsupported_column: {message}")));
    let [table] = declaration.tables.as_slice() else {
        return refuse("a flat storage stores exactly one table".into());
    };
    if table.columns.is_empty() || table.columns.iter().any(|c| c.row_count_only) {
        return refuse(format!("table {} has no stored column", table.name));
    }
    if table.columns.windows(2).any(|w| w[0].ordinal >= w[1].ordinal) {
        return refuse(format!("table {}: columns are not in table order", table.name));
    }
    let name = StorageName::new(&format!("flat_{}", table.name))
        .map_err(|e| AssemblyError::Storage(format!("flat_storage_unsupported_column: table {}: {e}", table.name)))?;
    let mut identifiers = BTreeSet::from(FIXED_IDENTIFIERS.map(str::to_string));
    let mut parts = Vec::new();
    for c in &table.columns {
        if !is_plain_identifier(&c.name) {
            return refuse(format!("{}.{}: a column name must be a lowercase Rust identifier", table.name, c.name));
        }
        let upper = c.name.to_uppercase();
        let validity = format!("{upper}_VALIDITY");
        let mut names = match c.ty.kind() {
            ColumnKind::Utf8 => vec![format!("{upper}_OFFSETS"), format!("{upper}_BYTES"), format!("{}_value", c.name), format!("read_{}_at", c.name), format!("read_{}_range", c.name)],
            _ => vec![upper.clone(), format!("{}_value", c.name), format!("read_{}", c.name)],
        };
        if c.nullable {
            names.extend([validity.clone(), format!("read_{}_validity", c.name)]);
        }
        for n in names {
            if !identifiers.insert(n.clone()) {
                return refuse(format!("{}.{}: generated name {n} is not unique", table.name, c.name));
            }
        }
        let part = |constant: String, buffer, elem| FlatPart { constant, ordinal: c.ordinal, column: c.name.clone(), buffer, elem };
        match c.ty.kind() {
            ColumnKind::I32 => parts.push(part(upper, FlatBuffer::Values, FlatElem::I32)),
            ColumnKind::I64 => parts.push(part(upper, FlatBuffer::Values, FlatElem::I64)),
            ColumnKind::I128 => parts.push(part(upper, FlatBuffer::Values, FlatElem::I128)),
            ColumnKind::Utf8 => {
                parts.push(part(format!("{upper}_OFFSETS"), FlatBuffer::Offsets, FlatElem::I64));
                parts.push(part(format!("{upper}_BYTES"), FlatBuffer::Bytes, FlatElem::U8));
            }
        }
        if c.nullable {
            parts.push(part(validity, FlatBuffer::Validity, FlatElem::U8));
        }
    }
    let flat = FlatStorage { name: name.clone(), table: table.name.clone(), declaration: declaration.clone(), parts, files: vec![] };
    let files = vec![
        FrameworkSource { path: format!("{}mod.rs", name.interface_prefix()), text: interface_text(&flat) },
        FrameworkSource { path: "builder/mod.rs".into(), text: builder_text(&flat) },
    ];
    Ok(FlatStorage { files, ..flat })
}

/// Identifiers of the interface that do not depend on the columns.
const FIXED_IDENTIFIERS: [&str; 17] = [
    "PART_COUNT", "COLUMN_COUNT", "i32s", "i64s", "i128s", "u8s", "text_view", "row_at", "parts_wf", "represents",
    "lemma_represents_determines", "lemma_offsets_monotone", "lemma_bytes_within", "lemma_text_rows", "stored_rows", "text_rows", "flat_parts",
];

fn is_plain_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|c| c.is_ascii_lowercase()) && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
}

impl FlatStorage {
    /// The relation columns `(position in the relation, column)` of the one stored table.
    fn columns(&self) -> impl Iterator<Item = (usize, &DeclaredColumn)> {
        self.declaration.tables[0].columns.iter().enumerate()
    }

    /// The part index of `constant`.
    fn index(&self, constant: &str) -> usize {
        self.parts.iter().position(|p| p.constant == constant).expect("generated constant")
    }

    /// The kinds the stored columns use (the interface imports only what it names).
    fn uses(&self, ty: impl Fn(DeclaredType) -> bool) -> bool {
        self.columns().any(|(_, c)| ty(c.ty))
    }

    /// Whether some stored column is nullable (its interface then states validity parts).
    pub fn has_nullable(&self) -> bool {
        self.columns().any(|(_, c)| c.nullable)
    }
}

fn is_text(ty: DeclaredType) -> bool {
    ty.kind() == ColumnKind::Utf8
}

/// The SQL type as written in comments.
fn sql_name(ty: DeclaredType) -> String {
    match ty {
        DeclaredType::Int4 => "integer".into(),
        DeclaredType::Int8 => "bigint".into(),
        DeclaredType::Numeric { precision, scale } => format!("numeric({precision},{scale})"),
        DeclaredType::Date => "date".into(),
        DeclaredType::Text => "text".into(),
        DeclaredType::Varchar { max_chars } => format!("varchar({max_chars})"),
        DeclaredType::Bpchar { len } => format!("char({len})"),
    }
}

/// What a part's elements mean.
fn part_meaning(part: &FlatPart, ty: DeclaredType) -> &'static str {
    match (part.buffer, ty) {
        (FlatBuffer::Offsets, _) => "offsets (rows + 1) into the bytes part",
        (FlatBuffer::Bytes, _) => "UTF-8 bytes",
        (FlatBuffer::Validity, _) => "validity (0: NULL, otherwise the value part holds the value)",
        (_, DeclaredType::Date) => "days since 1970-01-01",
        (_, DeclaredType::Numeric { .. }) => "coefficient (value = coefficient * 10^-scale)",
        _ => "value",
    }
}

/// `parts[CONSTANT as int]`.
fn part_at(constant: &str, parts: &str) -> String {
    format!("{parts}[{constant} as int]")
}

/// The interface's text view of text column `upper` over `parts`.
fn text_view_of(upper: &str, parts: &str) -> String {
    format!("text_view({parts}, {upper}_OFFSETS as int, {upper}_BYTES as int)")
}

/// The validity bytes of nullable column `c` over `parts`.
fn validity_view(c: &DeclaredColumn, parts: &str) -> String {
    format!("u8s({})", part_at(&format!("{}_VALIDITY", c.name.to_uppercase()), parts))
}

/// The column view `f` the value form `DeclaredType::value_at` reads, over `parts`.
fn column_view(c: &DeclaredColumn, parts: &str) -> String {
    let upper = c.name.to_uppercase();
    match c.ty.kind() {
        ColumnKind::Utf8 => text_view_of(&upper, parts),
        ColumnKind::I32 => format!("i32s({})", part_at(&upper, parts)),
        ColumnKind::I64 => format!("i64s({})", part_at(&upper, parts)),
        ColumnKind::I128 => format!("i128s({})", part_at(&upper, parts)),
    }
}

fn interface_text(flat: &FlatStorage) -> String {
    let mut o = String::new();
    write_interface_header(&mut o, flat);
    o.push_str("use vstd::prelude::*;\nuse crate::gendb_entry::layout::PartView;\nuse crate::gendb_entry::stored::StoredParts;\n");
    if flat.uses(|t| t == DeclaredType::Date) {
        o.push_str("use crate::gendb_entry::source_check::date32_val;\n");
    }
    o.push_str("use crate::link::query::{text_at, text_wf, TextView};\nuse crate::spec::value::{Row, Val};\n\nverus! {\n\n");
    write_constants(&mut o, flat);
    write_accessors(&mut o);
    write_relation(&mut o, flat);
    write_text_helpers(&mut o);
    write_readers(&mut o, flat);
    o.push_str("} // verus!\n");
    o
}

fn write_interface_header(o: &mut String, flat: &FlatStorage) {
    let _ = writeln!(o, "//! Flat storage `{}` of table `{}` (generated by GenDB, {FLAT_STORAGE_GENERATOR}; not author code).", flat.name, flat.table);
    o.push_str(
        "//!\n\
         //! Every column of the table as a plain typed array in source row order: stored row `i` is source row `i`. One\n\
         //! part per column, two for a text column (offsets, bytes), in column order. No sorting, partitioning, index,\n\
         //! permutation, compression, dictionary or skip metadata. The element type follows the declared SQL type only:\n\
         //! bigint I64; integer I32; date I32 days since 1970-01-01; numeric(p,s) I128 coefficient (value =\n\
         //! coefficient * 10^-s); text, varchar and char I64 offsets (rows + 1, positions in the bytes part, the first not\n\
         //! necessarily 0) and U8 UTF-8 bytes, value `i` = bytes[offsets[i] .. offsets[i + 1]].\n\
         //!\n\
         //! `represents(parts, rels)`: `rels` is the one stored table and its row `i` is `row_at(parts, i)`. The readers\n\
         //! read extents through `StoredParts` and state what they return in terms of `rels`.\n\
         //!\n",
    );
    if flat.has_nullable() {
        o.push_str(
            "//! A nullable column has one more part after its value part(s): its validity, U8, one byte per row. Row `i` of\n\
             //! the column is SQL NULL exactly when its validity byte is 0; then its value bytes mean nothing. Its value\n\
             //! readers state the value of every row that is not NULL; `read_<column>_validity` states which rows are NULL.\n\
             //!\n",
        );
    }
    o.push_str("//! Parts:\n");
    for (index, part) in flat.parts.iter().enumerate() {
        let ty = flat.columns().find(|(_, c)| c.ordinal == part.ordinal).map(|(_, c)| c.ty).expect("part column");
        let _ = writeln!(o, "//!   {index:>2} {}: {} ({}), {} {}", part.constant, part.column, sql_name(ty), part.elem.variant(), part_meaning(part, ty));
    }
}

fn write_constants(o: &mut String, flat: &FlatStorage) {
    let _ = writeln!(o, "/// Number of parts.\npub const PART_COUNT: usize = {};\n", flat.parts.len());
    let _ = writeln!(o, "/// Number of columns: every column of `{}`, in table order.\npub const COLUMN_COUNT: usize = {};\n", flat.table, flat.declaration.tables[0].columns.len());
    for (index, part) in flat.parts.iter().enumerate() {
        let (k, c) = flat.columns().find(|(_, c)| c.ordinal == part.ordinal).expect("part column");
        let what = match part.buffer {
            FlatBuffer::Values => format!("{} {}, one per row", part.elem.variant(), part_meaning(part, c.ty)),
            FlatBuffer::Offsets => "I64 offsets into the bytes part, rows + 1".into(),
            FlatBuffer::Bytes => "U8 UTF-8 bytes".into(),
            FlatBuffer::Validity => "U8 validity, one per row (0: NULL)".into(),
        };
        let _ = writeln!(o, "/// Column {k} `{}` ({}): {what}.\npub const {}: usize = {index};\n", c.name, sql_name(c.ty), part.constant);
    }
}

fn write_accessors(o: &mut String) {
    for elem in [FlatElem::I32, FlatElem::I64, FlatElem::I128, FlatElem::U8] {
        let _ = writeln!(
            o,
            "/// The elements of {article} {v} part (empty for a part of another kind).\npub open spec fn {a}(p: PartView) -> Seq<{t}> {{\n    match p {{\n        PartView::{v}(s) => s,\n        _ => Seq::empty(),\n    }}\n}}\n",
            article = if elem == FlatElem::U8 { "a" } else { "an" },
            v = elem.variant(),
            a = elem.accessor(),
            t = elem.rust()
        );
    }
    o.push_str(
        "/// The text column whose offsets and bytes are the parts `offsets` and `bytes`.\n\
         pub open spec fn text_view(parts: Seq<PartView>, offsets: int, bytes: int) -> TextView {\n    \
         TextView { offsets: i64s(parts[offsets]), bytes: u8s(parts[bytes]) }\n}\n\n",
    );
}

fn write_relation(o: &mut String, flat: &FlatStorage) {
    for (k, c) in flat.columns() {
        let value = c.ty.value_at(&column_view(c, "parts"), "i");
        let (value, null) = if c.nullable {
            (format!("if {}[i] == 0 {{ Val::Null }} else {{ {value} }}", validity_view(c, "parts")), ", NULL when its validity byte is 0")
        } else {
            (value, "")
        };
        let _ = writeln!(
            o,
            "/// Column {k} `{}` ({}) of stored row `i`{null}.\npub open spec fn {}_value(parts: Seq<PartView>, i: int) -> Val {{\n    {value}\n}}\n",
            c.name,
            sql_name(c.ty),
            c.name,
        );
    }
    let values: Vec<String> = flat.columns().map(|(_, c)| format!("{}_value(parts, i)", c.name)).collect();
    let _ = writeln!(o, "/// Stored row `i`: every column's value, in table order.\npub open spec fn row_at(parts: Seq<PartView>, i: int) -> Row {{\n    seq![{}]\n}}\n", values.join(", "));
    o.push_str("/// The parts of a table of `n` rows: their kinds and lengths, text offsets well formed.\npub open spec fn parts_wf(parts: Seq<PartView>, n: int) -> bool {\n    &&& parts.len() == PART_COUNT\n");
    for (_, c) in flat.columns() {
        let upper = c.name.to_uppercase();
        if is_text(c.ty) {
            let _ = writeln!(o, "    &&& {} is I64 && {} is U8", part_at(&format!("{upper}_OFFSETS"), "parts"), part_at(&format!("{upper}_BYTES"), "parts"));
            let _ = writeln!(o, "    &&& text_wf({}, n)", text_view_of(&upper, "parts"));
        } else {
            let elem = flat.parts[flat.index(&upper)].elem;
            let _ = writeln!(o, "    &&& {} is {} && {}.len() == n", part_at(&upper, "parts"), elem.variant(), column_view(c, "parts"));
        }
        if c.nullable {
            let _ = writeln!(o, "    &&& {} is U8 && {}.len() == n", part_at(&format!("{upper}_VALIDITY"), "parts"), validity_view(c, "parts"));
        }
    }
    o.push_str(
        "}\n\n\
         /// The parts represent `rels`, the one stored table: row `i` of it is `row_at(parts, i)`.\n\
         pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {\n    \
         &&& rels.len() == 1\n    &&& parts_wf(parts, rels[0].len() as int)\n    \
         &&& forall|i: int| 0 <= i < rels[0].len() ==> #[trigger] rels[0][i] == row_at(parts, i)\n}\n\n\
         /// Lossless: the parts determine the table they represent.\n\
         pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)\n    \
         requires\n        represents(parts, a),\n        represents(parts, b),\n    ensures\n        a == b,\n{\n    \
         assert(a[0].len() == b[0].len());\n    assert(a[0] =~= b[0]);\n    assert(a =~= b);\n}\n\n",
    );
}

/// The interface's generic text lemmas and reader, shared by every text column's readers (the same text in every flat
/// storage).
fn write_text_helpers(o: &mut String) {
    o.push_str(TEXT_HELPERS);
}

/// See [`write_text_helpers`].
const TEXT_HELPERS: &str = r#"/// The offsets of a well-formed text column of `n` rows do not decrease.
pub proof fn lemma_offsets_monotone(t: TextView, n: int, a: int, b: int)
    requires
        text_wf(t, n),
        0 <= a <= b <= n,
    ensures
        t.offsets[a] <= t.offsets[b],
    decreases b - a,
{
    if a < b {
        lemma_offsets_monotone(t, n, a, b - 1);
    }
}

/// The bytes of rows `x..y` of a byte range `a..b` that contains them, taken from that range.
pub proof fn lemma_bytes_within(bytes: Seq<u8>, a: int, b: int, x: int, y: int)
    requires
        0 <= a <= x <= y <= b <= bytes.len(),
    ensures
        bytes.subrange(a, b).subrange(x - a, y - a) == bytes.subrange(x, y),
{
    assert(bytes.subrange(a, b).subrange(x - a, y - a) =~= bytes.subrange(x, y));
}

/// Rows `lo..hi` (at least one) of a well-formed text column `t` of `n` rows, given as the offsets of these rows
/// (`offsets`) and the bytes they address (`bytes`): the offsets do not decrease and row `lo + j` is
/// `bytes[offsets[j] - offsets[0] .. offsets[j + 1] - offsets[0]]`.
pub proof fn lemma_text_rows(t: TextView, n: int, lo: int, hi: int, offsets: Seq<i64>, bytes: Seq<u8>)
    requires
        text_wf(t, n),
        0 <= lo < hi <= n,
        offsets == t.offsets.subrange(lo, hi + 1),
        bytes == t.bytes.subrange(offsets[0] as int, offsets[hi - lo] as int),
    ensures
        0 <= offsets[0],
        offsets[hi - lo] <= t.bytes.len(),
        forall|a: int, b: int| 0 <= a <= b <= hi - lo ==> offsets[a] <= offsets[b],
        forall|j: int| 0 <= j < hi - lo ==> #[trigger] bytes.subrange(offsets[j] - offsets[0], offsets[j + 1] - offsets[0])
            == text_at(t, lo + j),
{
    assert(0 <= t.offsets[lo] <= t.offsets[lo + 1]);
    assert(t.offsets[hi - 1] <= t.offsets[hi] <= t.bytes.len());
    assert forall|a: int, b: int| 0 <= a <= b <= hi - lo implies offsets[a] <= offsets[b] by {
        lemma_offsets_monotone(t, n, lo + a, lo + b);
    }
    assert forall|j: int| 0 <= j < hi - lo implies #[trigger] bytes.subrange(offsets[j] - offsets[0], offsets[j + 1] - offsets[0])
        == text_at(t, lo + j) by {
        lemma_offsets_monotone(t, n, lo, lo + j);
        lemma_offsets_monotone(t, n, lo + j + 1, hi);
        assert(t.offsets[lo + j] <= t.offsets[lo + j + 1]);
        lemma_bytes_within(t.bytes, t.offsets[lo] as int, t.offsets[hi] as int, t.offsets[lo + j] as int, t.offsets[lo + j + 1] as int);
    }
}

/// Rows `lo..hi` (at least one) of the well-formed text column of `n` rows in parts `offsets_part` and `bytes_part`
/// (two requests): `r.0` holds the `hi - lo + 1` offsets of these rows as stored, `r.1` the bytes from `r.0[0]` to
/// `r.0[hi - lo]`; row `lo + j` is `r.1[r.0[j] - r.0[0] .. r.0[j + 1] - r.0[0]]`.
pub fn text_rows(s: &mut StoredParts, offsets_part: usize, bytes_part: usize, lo: usize, hi: usize, Ghost(n): Ghost<int>) -> (r: (&'static [i64], &'static [u8]))
    requires
        offsets_part < old(s)@.len(),
        bytes_part < old(s)@.len(),
        old(s)@[offsets_part as int] is I64,
        old(s)@[bytes_part as int] is U8,
        text_wf(text_view(old(s)@, offsets_part as int, bytes_part as int), n),
        lo < hi <= n,
    ensures
        final(s)@ == old(s)@,
        r.0@.len() == hi - lo + 1,
        0 <= r.0@[0],
        forall|a: int, b: int| 0 <= a <= b <= hi - lo ==> r.0@[a] <= r.0@[b],
        r.1@.len() == r.0@[hi - lo] - r.0@[0],
        forall|j: int| 0 <= j < hi - lo ==> #[trigger] r.1@.subrange(r.0@[j] - r.0@[0], r.0@[j + 1] - r.0@[0])
            == text_at(text_view(old(s)@, offsets_part as int, bytes_part as int), lo + j),
{
    let ghost t = text_view(s@, offsets_part as int, bytes_part as int);
    let offset_count = s.part_len(offsets_part);
    let byte_count = s.part_len(bytes_part);
    let offsets = s.extent_i64(offsets_part, lo, hi + 1);
    proof {
        assert(0 <= t.offsets[lo as int] <= t.offsets[lo + 1]);
        assert(t.offsets[hi - 1] <= t.offsets[hi as int] <= t.bytes.len());
        lemma_offsets_monotone(t, n, lo as int, hi as int);
    }
    let first = offsets[0];
    let last = offsets[hi - lo];
    let bytes = s.extent_u8(bytes_part, first as usize, last as usize);
    proof {
        lemma_text_rows(t, n, lo as int, hi as int, offsets@, bytes@);
    }
    (offsets, bytes)
}

"#;

fn write_readers(o: &mut String, flat: &FlatStorage) {
    let (_, first) = flat.columns().next().expect("a column");
    let upper = first.name.to_uppercase();
    let (count, adjust) = if is_text(first.ty) { (format!("{upper}_OFFSETS"), " - 1") } else { (upper.clone(), "") };
    let _ = writeln!(
        o,
        "/// Number of stored rows.\npub fn stored_rows(s: &StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (n: usize)\n    requires\n        represents(s@, rels),\n    ensures\n        n == rels[0].len(),\n{{\n    s.part_len({count}){adjust}\n}}\n"
    );
    for (k, c) in flat.columns() {
        let upper = c.name.to_uppercase();
        if c.nullable {
            write_validity_reader(o, k, c, &upper);
        }
        if is_text(c.ty) {
            write_text_readers(o, k, c, &upper);
        } else {
            let elem = flat.parts[flat.index(&upper)].elem;
            let value = format!("({})", c.ty.value_at("r@", "j"));
            // What the reader states of row `lo + j`: its value, or (nullable) that it is NULL or its value.
            let (fact, doc) = if c.nullable {
                (format!("is Null || rels[0][lo as int + j][{k}] == {value}"), ", every row that is not NULL")
            } else {
                (format!("== {value}"), "")
            };
            let _ = writeln!(
                o,
                "/// Column {k} `{name}` ({sql}) of stored rows `lo..hi` ({meaning}): `r[j]` is row `lo + j`{doc} (one request).\n\
                 pub fn read_{name}(s: &mut StoredParts, lo: usize, hi: usize, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (r: &'static [{t}])\n    \
                 requires\n        represents(old(s)@, rels),\n        lo <= hi <= rels[0].len(),\n    \
                 ensures\n        final(s)@ == old(s)@,\n        r@.len() == hi - lo,\n        \
                 forall|j: int| 0 <= j < hi - lo ==> #[trigger] rels[0][lo as int + j][{k}] {fact},\n{{\n    \
                 let r = s.extent_{t}({upper}, lo, hi);\n    \
                 proof {{\n        assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rels[0][lo as int + j][{k}] {fact} by {{\n            \
                 assert(rels[0][lo as int + j] == row_at(old(s)@, lo as int + j));\n        }}\n    }}\n    r\n}}\n",
                name = c.name,
                sql = sql_name(c.ty),
                meaning = part_meaning(&flat.parts[flat.index(&upper)], c.ty),
                t = elem.rust(),
            );
        }
    }
}

/// `read_<column>_validity`: the validity bytes of rows `lo..hi` of nullable column `c` (position `k`).
fn write_validity_reader(o: &mut String, k: usize, c: &DeclaredColumn, upper: &str) {
    let name = &c.name;
    let sql = sql_name(c.ty);
    let _ = writeln!(
        o,
        "/// Validity of column {k} `{name}` ({sql}) of stored rows `lo..hi`: row `lo + j` is NULL exactly when `r[j] == 0`\n\
         /// (one request).\n\
         pub fn read_{name}_validity(s: &mut StoredParts, lo: usize, hi: usize, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (r: &'static [u8])\n    \
         requires\n        represents(old(s)@, rels),\n        lo <= hi <= rels[0].len(),\n    \
         ensures\n        final(s)@ == old(s)@,\n        r@.len() == hi - lo,\n        \
         forall|j: int| 0 <= j < hi - lo ==> (#[trigger] rels[0][lo as int + j][{k}] is Null) == (r@[j] == 0),\n{{\n    \
         let r = s.extent_u8({upper}_VALIDITY, lo, hi);\n    \
         proof {{\n        assert forall|j: int| 0 <= j < hi - lo implies (#[trigger] rels[0][lo as int + j][{k}] is Null) == (r@[j] == 0) by {{\n            \
         assert(rels[0][lo as int + j] == row_at(old(s)@, lo as int + j));\n        }}\n    }}\n    r\n}}\n"
    );
}

fn write_text_readers(o: &mut String, k: usize, c: &DeclaredColumn, upper: &str) {
    let name = &c.name;
    let sql = sql_name(c.ty);
    // A nullable column's readers state the value of every row that is not NULL: `<row> is Null || <row> == <value>`
    // instead of `<row> == <value>`.
    let (doc, at_i, at_j) = if c.nullable {
        (", unless the row is NULL", format!(" is Null || rels[0][i as int][{k}] == "), format!("is Null || rels[0][lo as int + j][{k}] == "))
    } else {
        ("", " == ".to_string(), "== ".to_string())
    };
    let _ = writeln!(
        o,
        "/// Column {k} `{name}` ({sql}) of stored row `i`: its UTF-8 bytes{doc} (three requests).\n\
         pub fn read_{name}_at(s: &mut StoredParts, i: usize, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (r: &'static [u8])\n    \
         requires\n        represents(old(s)@, rels),\n        i < rels[0].len(),\n    \
         ensures\n        final(s)@ == old(s)@,\n        rels[0][i as int][{k}]{at_i}Val::Text(r@),\n{{\n    \
         let _offset_count = s.part_len({upper}_OFFSETS);\n    \
         let r = text_rows(s, {upper}_OFFSETS, {upper}_BYTES, i, i + 1, Ghost(rels[0].len() as int));\n    \
         proof {{\n        let j: int = 0;\n        \
         assert(r.1@.subrange(r.0@[j] - r.0@[0], r.0@[j + 1] - r.0@[0])\n            \
         == text_at(text_view(old(s)@, {upper}_OFFSETS as int, {upper}_BYTES as int), i + j));\n        \
         assert(rels[0][i as int] == row_at(old(s)@, i as int));\n        \
         assert(r.1@.subrange(r.0@[0] - r.0@[0], r.0@[1] - r.0@[0]) =~= r.1@);\n    }}\n    r.1\n}}\n"
    );
    let _ = writeln!(
        o,
        "/// Column {k} `{name}` ({sql}) of stored rows `lo..hi`, at least one (two requests): `r.0` holds the `hi - lo + 1`\n\
         /// offsets of these rows as stored, `r.1` the bytes from `r.0[0]` to `r.0[hi - lo]`; row `lo + j` is\n\
         /// `r.1[r.0[j] - r.0[0] .. r.0[j + 1] - r.0[0]]`{doc}.\n\
         pub fn read_{name}_range(s: &mut StoredParts, lo: usize, hi: usize, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (r: (&'static [i64], &'static [u8]))\n    \
         requires\n        represents(old(s)@, rels),\n        lo < hi <= rels[0].len(),\n    \
         ensures\n        final(s)@ == old(s)@,\n        r.0@.len() == hi - lo + 1,\n        \
         0 <= r.0@[0],\n        forall|a: int, b: int| 0 <= a <= b <= hi - lo ==> r.0@[a] <= r.0@[b],\n        \
         r.1@.len() == r.0@[hi - lo] - r.0@[0],\n        \
         forall|j: int| 0 <= j < hi - lo ==> #[trigger] rels[0][lo as int + j][{k}]\n            \
         {at_j}Val::Text(r.1@.subrange(r.0@[j] - r.0@[0], r.0@[j + 1] - r.0@[0])),\n{{\n    \
         let r = text_rows(s, {upper}_OFFSETS, {upper}_BYTES, lo, hi, Ghost(rels[0].len() as int));\n    \
         proof {{\n        assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rels[0][lo as int + j][{k}]\n            \
         {at_j}Val::Text(r.1@.subrange(r.0@[j] - r.0@[0], r.0@[j + 1] - r.0@[0])) by {{\n            \
         assert(rels[0][lo as int + j] == row_at(old(s)@, lo as int + j));\n        }}\n    }}\n    r\n}}\n"
    );
}

fn builder_text(flat: &FlatStorage) -> String {
    let mut o = String::new();
    let _ = writeln!(o, "//! Builder of flat storage `{}` (generated by GenDB, {FLAT_STORAGE_GENERATOR}; not author code).", flat.name);
    o.push_str(
        "//!\n\
         //! `build` copies every delivered column unchanged into its part, in column order: stored row `i` is delivered\n\
         //! row `i`. Its parts are the delivered buffers (`flat_parts`), and `lemma_delivered_buffers_represent` proves that\n\
         //! those buffers, read as parts, represent the delivered table. Where GenDB publishes a flat asset from the\n\
         //! capture's own column files instead of running this builder (the trusted host item `flat_capture_parts`), that\n\
         //! lemma, not the builder, connects the asset to the fixed claim.\n",
    );
    let _ = write!(
        o,
        "use vstd::prelude::*;\nuse crate::gendb_abi::OwnedPart;\nuse crate::gendb_entry::layout::{{owned_parts_view, PartView}};\n\
         use crate::gendb_entry::parallel::{{Dispatch, MAX_WORKERS}};\nuse crate::gendb_entry::runtime::QueryError;\nuse crate::gendb_source::*;\n\
         use crate::stores::{}::interface::*;\n\nverus! {{\n\n",
        flat.name
    );
    write_flat_parts(&mut o, flat);
    write_buffers_lemma(&mut o, flat);
    write_build(&mut o, flat);
    for elem in [FlatElem::I32, FlatElem::I64, FlatElem::I128, FlatElem::U8] {
        if flat.parts.iter().any(|p| p.elem == elem) {
            let t = elem.rust();
            let _ = writeln!(
                o,
                "/// A copy of `s`.\nfn copy_{t}(s: &[{t}]) -> (r: Vec<{t}>)\n    ensures\n        r@ == s@,\n{{\n    \
                 let mut r: Vec<{t}> = Vec::with_capacity(s.len());\n    let mut i: usize = 0;\n    while i < s.len()\n        \
                 invariant\n            i <= s@.len(),\n            r@ == s@.subrange(0, i as int),\n        decreases s@.len() - i,\n    {{\n        \
                 r.push(s[i]);\n        i += 1;\n    }}\n    proof {{\n        assert(r@ =~= s@);\n    }}\n    r\n}}\n"
            );
        }
    }
    o.push_str("} // verus!\n");
    o
}

/// The delivered field of part `part` (`t0_f{k}`, `.offsets` or `.bytes`) as written after `v.` or `src.`.
fn delivered_field(flat: &FlatStorage, part: &FlatPart) -> String {
    let (k, _) = flat.columns().find(|(_, c)| c.ordinal == part.ordinal).expect("part column");
    match part.buffer {
        FlatBuffer::Values => format!("t0_f{k}"),
        FlatBuffer::Offsets => format!("t0_f{k}.offsets"),
        FlatBuffer::Bytes => format!("t0_f{k}.bytes"),
        FlatBuffer::Validity => format!("t0_v{k}"),
    }
}

fn write_flat_parts(o: &mut String, flat: &FlatStorage) {
    let parts: Vec<String> = flat.parts.iter().map(|p| format!("PartView::{}(v.{})", p.elem.variant(), delivered_field(flat, p))).collect();
    let _ = writeln!(
        o,
        "/// The delivered columns as parts, in the interface's part order.\npub open spec fn flat_parts(v: SourceView) -> Seq<PartView> {{\n    seq![\n        {},\n    ]\n}}\n",
        parts.join(",\n        ")
    );
}

fn write_buffers_lemma(o: &mut String, flat: &FlatStorage) {
    o.push_str(
        "/// The delivered buffers, read as parts, represent the delivered table.\n\
         pub proof fn lemma_delivered_buffers_represent(v: SourceView)\n    requires\n        source_wf(v),\n    \
         ensures\n        represents(flat_parts(v), tables(v)),\n{\n    let parts = flat_parts(v);\n    \
         assert(tables(v)[0] == table_t0(v));\n",
    );
    for part in &flat.parts {
        let _ = writeln!(o, "    assert(parts[{} as int] == PartView::{}(v.{}));", part.constant, part.elem.variant(), delivered_field(flat, part));
    }
    for (k, c) in flat.columns() {
        if is_text(c.ty) {
            let _ = writeln!(o, "    assert({} == v.t0_f{k});", text_view_of(&c.name.to_uppercase(), "parts"));
        }
    }
    let n = flat.declaration.tables[0].columns.len();
    let _ = write!(
        o,
        "    let rel = table_t0(v);\n    assert forall|i: int| 0 <= i < rel.len() implies #[trigger] rel[i] == row_at(parts, i) by {{\n        \
         assert forall|k: int| 0 <= k < {n} implies #[trigger] rel[i][k] == row_at(parts, i)[k] by {{\n    {}        }}\n        \
         assert(rel[i] =~= row_at(parts, i));\n    }}\n}}\n\n",
        case_split(n, "k")
    );
}

fn write_build(o: &mut String, flat: &FlatStorage) {
    let pushes: Vec<String> =
        flat.parts.iter().map(|p| format!("parts.push(OwnedPart::{}(copy_{}(src.{})));", p.elem.variant(), p.elem.rust(), delivered_field(flat, p))).collect();
    let _ = write!(
        o,
        "/// Copy every delivered column into its part (the fixed storage entry's builder).\n\
         pub fn build(src: &SourceRef, _workers: usize, _dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)\n    \
         requires\n        source_wf(src@),\n        in_domain(tables(src@)),\n        1 <= _workers <= MAX_WORKERS,\n    \
         ensures\n        r matches Ok(p) ==> owned_parts_view(p@) == flat_parts(src@) && represents(owned_parts_view(p@), tables(src@)),\n        \
         r matches Err(e) ==> e is WorkerFailed,\n{{\n    let mut parts: Vec<OwnedPart> = Vec::new();\n    {}\n    \
         proof {{\n        let view = owned_parts_view(parts@);\n        \
         assert forall|k: int| 0 <= k < PART_COUNT implies #[trigger] view[k] == flat_parts(src@)[k] by {{\n    {}        }}\n        \
         assert(view =~= flat_parts(src@));\n        lemma_delivered_buffers_represent(src@);\n    }}\n    Ok(parts)\n}}\n\n",
        pushes.join("\n    "),
        case_split(flat.parts.len(), "k")
    );
}
