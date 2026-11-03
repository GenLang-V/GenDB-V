//! The plain-columns vocabulary (identity `gendb-plain-columns-v1`): one fixed, schema-free Verus text that states how
//! the columns of one relation are held as plain typed arrays, located by part index and typed by the declared column
//! types, never by name (general-engine line: the schema-name rule).
//!
//! It has two homes, always the same bytes:
//! - a storage interface may carry it as a module of its own (for example `stores/<storage>/interface/plain.rs`
//!   with `pub mod plain;` in the interface root, [`plain_columns_interface_file`]) and state its `represents` with it.
//!   It is then the storage's own interface code: in the storage's closure, carried byte for byte by every crate that
//!   reads the storage, scanned and checked by Verus there like any interface file;
//! - the generated flat access modules (`crate::sources_flat` in storage crates built from flat storages,
//!   `crate::flat_tables` in engine crates) carry it as their submodule `plain` and state with it what every flat
//!   storage's parts hold (`lemma_flat_plain`).
//!
//! A storage built from a flat storage can therefore keep the flat parts (`extends`) and restate them without naming
//! the flat storage or its columns: its builder gets `plain_columns` of the flat parts from `crate::sources_flat`, and
//! the two copies of the vocabulary are the same open definitions, which Verus unfolds to the same terms. Nothing here
//! is trusted: the text is checked by Verus in every crate that carries it.

use super::storage_crate::StorageName;
use crate::verus::FrameworkSource;

/// Identity of the plain-columns vocabulary, named in its text.
pub const PLAIN_COLUMNS_IDENTITY: &str = "gendb-plain-columns-v1";

/// The file name of the vocabulary inside a storage interface (`stores/<storage>/interface/plain.rs`).
pub const PLAIN_COLUMNS_FILE: &str = "plain.rs";

/// The vocabulary as a file of storage `name`'s interface (`stores/<name>/interface/plain.rs`; the interface root
/// declares `pub mod plain;`).
pub fn plain_columns_interface_file(name: &StorageName) -> FrameworkSource {
    FrameworkSource { path: format!("{}{PLAIN_COLUMNS_FILE}", name.interface_prefix()), text: PLAIN_COLUMNS.into() }
}

/// The vocabulary's text (the same in every crate and every home).
pub const PLAIN_COLUMNS: &str = r#"//! Plain columns (GenDB, gendb-plain-columns-v1; the same text everywhere, schema free): how the columns of one
//! relation are held as plain typed arrays, located by part index and typed by the declared column types (data), never
//! by name.
//!
//! - `plain_column(parts, p, ty, rows, c)`: column `c` of `rows`, of SQL type `ty`, is held from part `p`: integer I32,
//!   date I32 days since 1970-01-01, bigint I64, numeric I128 coefficients at the type's scale, text, varchar and char
//!   I64 offsets (rows + 1, not decreasing, the first not necessarily 0) at `p` and U8 bytes at `p + 1`.
//! - `plain_columns(parts, rows, cols, at)`: every column `k` of `rows` (types `cols`, at least one) from part `at[k]`.
//! - `lemma_plain_columns_determine`: the parts determine the rows (lossless).
//! - `read_plain`: rows `lo..hi` of one plainly held column, as stored (no copy), with each value's meaning; the
//!   slice's variant follows the column type (`plain_slice_fits`).
//! - `lemma_proj_identity`: a relation is its own projection onto all of its columns in order.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::source_check::date32_val;
use crate::gendb_entry::stored::StoredParts;
use crate::link::query::{proj_all, text_at, text_wf, TextView};
use crate::link::source::lemma_proj_all_index;
use crate::spec::types::{Column, SqlType};
use crate::spec::value::{Row, Val};

verus! {

/// Whether a column of type `ty` is held as text (offsets and bytes: two parts).
pub open spec fn is_text(ty: SqlType) -> bool {
    ty is Text || ty is Varchar || ty is Bpchar
}

/// The parts a plainly held column of type `ty` takes.
pub open spec fn plain_width(ty: SqlType) -> int {
    if is_text(ty) { 2 } else { 1 }
}

/// The text column whose offsets are part `p` and whose bytes are part `p + 1`.
pub open spec fn plain_text(parts: Seq<PartView>, p: int) -> TextView {
    TextView { offsets: parts[p]->I64_0, bytes: parts[p + 1]->U8_0 }
}

/// The values of a non-text column of type `ty` held in part `part` (rows `0..n`) are `rows[i][c]`.
pub open spec fn plain_values(part: PartView, ty: SqlType, rows: Seq<Row>, c: int) -> bool {
    let n = rows.len() as int;
    match ty {
        SqlType::Int4 => part is I32 && part->I32_0.len() == n
            && forall|i: int| 0 <= i < n ==> #[trigger] rows[i][c] == Val::Int(part->I32_0[i] as int),
        SqlType::Date => part is I32 && part->I32_0.len() == n
            && forall|i: int| 0 <= i < n ==> #[trigger] rows[i][c] == date32_val(part->I32_0[i]),
        SqlType::Int8 => part is I64 && part->I64_0.len() == n
            && forall|i: int| 0 <= i < n ==> #[trigger] rows[i][c] == Val::Int(part->I64_0[i] as int),
        SqlType::Numeric { scale, .. } => part is I128 && part->I128_0.len() == n
            && forall|i: int| 0 <= i < n ==> #[trigger] rows[i][c] == Val::Num { coeff: part->I128_0[i] as int, scale: scale as nat },
        _ => false,
    }
}

/// Column `c` of `rows` (the value at position `c` of every row), of type `ty`, is held plainly from part `p`.
pub open spec fn plain_column(parts: Seq<PartView>, p: int, ty: SqlType, rows: Seq<Row>, c: int) -> bool {
    let n = rows.len() as int;
    0 <= p && p + plain_width(ty) <= parts.len() && if is_text(ty) {
        parts[p] is I64 && parts[p + 1] is U8 && text_wf(plain_text(parts, p), n)
            && forall|i: int| 0 <= i < n ==> #[trigger] rows[i][c] == Val::Text(text_at(plain_text(parts, p), i))
    } else {
        plain_values(parts[p], ty, rows, c)
    }
}

/// The relation `rows` with column types `cols` (at least one) is held plainly in `parts`: column `k` from part `at[k]`,
/// and every row has one value per column.
pub open spec fn plain_columns(parts: Seq<PartView>, rows: Seq<Row>, cols: Seq<Column>, at: Seq<int>) -> bool {
    &&& cols.len() >= 1
    &&& at.len() == cols.len()
    &&& forall|i: int| 0 <= i < rows.len() ==> #[trigger] rows[i].len() == cols.len()
    &&& forall|k: int| 0 <= k < cols.len() ==> #[trigger] plain_column(parts, at[k], cols[k].ty, rows, k)
}

/// Two relations whose column `c` the same parts hold have the same row count and the same values in that column.
pub proof fn lemma_plain_column_determines(parts: Seq<PartView>, p: int, ty: SqlType, a: Seq<Row>, b: Seq<Row>, c: int)
    requires
        plain_column(parts, p, ty, a, c),
        plain_column(parts, p, ty, b, c),
    ensures
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i][c] == b[i][c],
{
    if is_text(ty) {
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i][c] == b[i][c] by {
            assert(a[i][c] == Val::Text(text_at(plain_text(parts, p), i)));
            assert(b[i][c] == Val::Text(text_at(plain_text(parts, p), i)));
        }
    } else {
        match ty {
            SqlType::Int4 => {
                assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i][c] == b[i][c] by {
                    assert(a[i][c] == Val::Int(parts[p]->I32_0[i] as int) && b[i][c] == Val::Int(parts[p]->I32_0[i] as int));
                }
            },
            SqlType::Date => {
                assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i][c] == b[i][c] by {
                    assert(a[i][c] == date32_val(parts[p]->I32_0[i]) && b[i][c] == date32_val(parts[p]->I32_0[i]));
                }
            },
            SqlType::Int8 => {
                assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i][c] == b[i][c] by {
                    assert(a[i][c] == Val::Int(parts[p]->I64_0[i] as int) && b[i][c] == Val::Int(parts[p]->I64_0[i] as int));
                }
            },
            SqlType::Numeric { scale, .. } => {
                assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i][c] == b[i][c] by {
                    let v = Val::Num { coeff: parts[p]->I128_0[i] as int, scale: scale as nat };
                    assert(a[i][c] == v && b[i][c] == v);
                }
            },
            _ => {},
        }
    }
}

/// Lossless: two relations the same parts hold plainly (the same types and part indices) are equal.
pub proof fn lemma_plain_columns_determine(parts: Seq<PartView>, a: Seq<Row>, b: Seq<Row>, cols: Seq<Column>, at: Seq<int>)
    requires
        plain_columns(parts, a, cols, at),
        plain_columns(parts, b, cols, at),
    ensures
        a == b,
{
    assert(plain_column(parts, at[0], cols[0].ty, a, 0) && plain_column(parts, at[0], cols[0].ty, b, 0));
    lemma_plain_column_determines(parts, at[0], cols[0].ty, a, b, 0);
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == b[i] by {
        assert forall|k: int| 0 <= k < cols.len() implies #[trigger] a[i][k] == b[i][k] by {
            assert(plain_column(parts, at[k], cols[k].ty, a, k) && plain_column(parts, at[k], cols[k].ty, b, k));
            lemma_plain_column_determines(parts, at[k], cols[k].ty, a, b, k);
        }
        assert(a[i].len() == cols.len() && b[i].len() == cols.len());
        assert(a[i] =~= b[i]);
    }
    assert(a =~= b);
}

/// A relation whose rows have `n` columns is its own projection onto columns `0..n`.
pub proof fn lemma_proj_identity(rows: Seq<Row>, cols: Seq<nat>, n: nat)
    requires
        cols.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] cols[k] == k,
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] rows[i].len() == n,
    ensures
        proj_all(rows, cols) == rows,
{
    lemma_proj_all_index(rows, cols);
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, cols)[i] == rows[i] by {
        assert(proj_all(rows, cols)[i] =~= rows[i]);
    }
    assert(proj_all(rows, cols) =~= rows);
}

/// Rows `lo..hi` of one plainly held column, as its parts hold them (no copy).
pub enum PlainSlice {
    /// `integer`.
    Int32(&'static [i32]),
    /// `date`: days since 1970-01-01.
    Date(&'static [i32]),
    /// `bigint`.
    Int64(&'static [i64]),
    /// `numeric(p, s)`: coefficients at the scale given.
    Numeric(&'static [i128], u32),
    /// `text`, `varchar`, `char`: the rows' offsets as stored (one more than the rows) and the bytes from the first
    /// offset to the last.
    Text(&'static [i64], &'static [u8]),
}

/// The number of rows a slice holds.
pub open spec fn plain_slice_len(s: PlainSlice) -> int {
    match s {
        PlainSlice::Int32(v) => v@.len() as int,
        PlainSlice::Date(v) => v@.len() as int,
        PlainSlice::Int64(v) => v@.len() as int,
        PlainSlice::Numeric(v, _) => v@.len() as int,
        PlainSlice::Text(o, _) => o@.len() - 1,
    }
}

/// A text slice's offsets start non-negative, do not decrease and address exactly its bytes.
pub open spec fn plain_slice_wf(s: PlainSlice) -> bool {
    match s {
        PlainSlice::Text(o, b) => o@.len() >= 1 && 0 <= o@[0] && (forall|x: int, y: int| 0 <= x <= y < o@.len() ==> o@[x] <= o@[y])
            && b@.len() == o@[o@.len() - 1] - o@[0],
        _ => true,
    }
}

/// The slice's variant follows the column type `ty` it was read with.
pub open spec fn plain_slice_fits(s: PlainSlice, ty: SqlType) -> bool {
    match s {
        PlainSlice::Int32(_) => ty is Int4,
        PlainSlice::Date(_) => ty is Date,
        PlainSlice::Int64(_) => ty is Int8,
        PlainSlice::Numeric(_, scale) => ty is Numeric && ty->Numeric_scale == scale,
        PlainSlice::Text(_, _) => is_text(ty),
    }
}

/// The SQL value of row `j` of a slice.
pub open spec fn plain_value(s: PlainSlice, j: int) -> Val {
    match s {
        PlainSlice::Int32(v) => Val::Int(v@[j] as int),
        PlainSlice::Date(v) => date32_val(v@[j]),
        PlainSlice::Int64(v) => Val::Int(v@[j] as int),
        PlainSlice::Numeric(v, scale) => Val::Num { coeff: v@[j] as int, scale: scale as nat },
        PlainSlice::Text(o, b) => Val::Text(b@.subrange(o@[j] - o@[0], o@[j + 1] - o@[0])),
    }
}

/// The offsets of a well-formed text column of `n` rows do not decrease.
pub proof fn lemma_plain_offsets_monotone(t: TextView, n: int, a: int, b: int)
    requires
        text_wf(t, n),
        0 <= a <= b <= n,
    ensures
        t.offsets[a] <= t.offsets[b],
    decreases b - a,
{
    if a < b {
        lemma_plain_offsets_monotone(t, n, a, b - 1);
    }
}

/// The bytes of rows `x..y` of a byte range `a..b` that contains them, taken from that range.
proof fn lemma_plain_bytes_within(bytes: Seq<u8>, a: int, b: int, x: int, y: int)
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
proof fn lemma_plain_text_rows(t: TextView, n: int, lo: int, hi: int, offsets: Seq<i64>, bytes: Seq<u8>)
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
        lemma_plain_offsets_monotone(t, n, lo + a, lo + b);
    }
    assert forall|j: int| 0 <= j < hi - lo implies #[trigger] bytes.subrange(offsets[j] - offsets[0], offsets[j + 1] - offsets[0])
        == text_at(t, lo + j) by {
        lemma_plain_offsets_monotone(t, n, lo, lo + j);
        lemma_plain_offsets_monotone(t, n, lo + j + 1, hi);
        assert(t.offsets[lo + j] <= t.offsets[lo + j + 1]);
        lemma_plain_bytes_within(t.bytes, t.offsets[lo] as int, t.offsets[hi] as int, t.offsets[lo + j] as int, t.offsets[lo + j + 1] as int);
    }
}

/// Rows `lo..hi` (at least one) of column `c` of `rows`, held plainly from part `p` with type `ty`, as stored (no copy):
/// row `lo + j` of the column is `plain_value(s, j)`.
pub fn read_plain(st: &mut StoredParts, p: usize, ty: SqlType, lo: usize, hi: usize, Ghost(rows): Ghost<Seq<Row>>, Ghost(c): Ghost<int>) -> (s: PlainSlice)
    requires
        plain_column(old(st)@, p as int, ty, rows, c),
        lo < hi <= rows.len(),
    ensures
        final(st)@ == old(st)@,
        plain_slice_wf(s),
        plain_slice_fits(s, ty),
        plain_slice_len(s) == hi - lo,
        forall|j: int| 0 <= j < hi - lo ==> #[trigger] rows[lo + j][c] == plain_value(s, j),
{
    let ghost parts = st@;
    let ghost pi = p as int;
    match ty {
        SqlType::Int4 => {
            let v = st.extent_i32(p, lo, hi);
            let s = PlainSlice::Int32(v);
            proof {
                assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rows[lo + j][c] == plain_value(s, j) by {
                    assert(rows[lo + j][c] == Val::Int(parts[pi]->I32_0[lo + j] as int));
                }
            }
            s
        },
        SqlType::Date => {
            let v = st.extent_i32(p, lo, hi);
            let s = PlainSlice::Date(v);
            proof {
                assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rows[lo + j][c] == plain_value(s, j) by {
                    assert(rows[lo + j][c] == date32_val(parts[pi]->I32_0[lo + j]));
                }
            }
            s
        },
        SqlType::Int8 => {
            let v = st.extent_i64(p, lo, hi);
            let s = PlainSlice::Int64(v);
            proof {
                assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rows[lo + j][c] == plain_value(s, j) by {
                    assert(rows[lo + j][c] == Val::Int(parts[pi]->I64_0[lo + j] as int));
                }
            }
            s
        },
        SqlType::Numeric { precision: _, scale } => {
            let v = st.extent_i128(p, lo, hi);
            let s = PlainSlice::Numeric(v, scale);
            proof {
                assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rows[lo + j][c] == plain_value(s, j) by {
                    assert(rows[lo + j][c] == Val::Num { coeff: parts[pi]->I128_0[lo + j] as int, scale: scale as nat });
                }
            }
            s
        },
        SqlType::Text | SqlType::Varchar { .. } | SqlType::Bpchar { .. } => {
            let ghost t = plain_text(parts, pi);
            let ghost n = rows.len() as int;
            // The part count and the part lengths are machine sizes: `p + 1`, `hi + 1` and the byte range fit.
            let _part_count = st.part_count();
            let _offset_count = st.part_len(p);
            let _byte_count = st.part_len(p + 1);
            let o = st.extent_i64(p, lo, hi + 1);
            proof {
                assert(0 <= t.offsets[lo as int] <= t.offsets[lo + 1]);
                assert(t.offsets[hi - 1] <= t.offsets[hi as int] <= t.bytes.len());
                lemma_plain_offsets_monotone(t, n, lo as int, hi as int);
            }
            let first = o[0];
            let last = o[hi - lo];
            let b = st.extent_u8(p + 1, first as usize, last as usize);
            let s = PlainSlice::Text(o, b);
            proof {
                lemma_plain_text_rows(t, n, lo as int, hi as int, o@, b@);
                assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rows[lo + j][c] == plain_value(s, j) by {
                    assert(rows[lo + j][c] == Val::Text(text_at(t, lo + j)));
                }
            }
            s
        },
        _ => {
            proof {
                assert(false);
            }
            PlainSlice::Int64(st.extent_i64(p, lo, hi))
        },
    }
}

} // verus!
"#;
