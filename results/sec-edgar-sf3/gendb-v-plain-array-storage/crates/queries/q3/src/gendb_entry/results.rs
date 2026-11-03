// FRAMEWORK FILE: columnar query results of GenDB query crates (`verification/obligations/gendb_entry/results.rs`).
//
// Copied unchanged into every query crate (entry v4 and v5) as `crate::gendb_entry::results`; storage crates do not
// carry it. Authors cannot edit it; they may build `ResultColumns` and call the helpers. Checked by Verus with
// `--no-cheating` together with the candidate; no `assume`, `admit` or `external_body`.
//
// A query may answer `Answer::Columns(c)` instead of `Answer::Rows(rows)`: one vector per output column instead of
// one `Vec<EVal>` per output row, so producing a row allocates nothing. The meaning is fixed here and used by the
// entry's claim: the answer is `columns_view(c)` (row `i`, column `k` is `column_value(c.columns[k], i)`), and the
// claim also requires `columns_wf(c)` (every column holds exactly `c.rows` values; text offsets are monotone and
// inside the bytes). The values are the same VERUS_SQL values an `EVal` row gives (`EVal::view`): `Int` is
// `Val::Int`, `Num` is `Val::Num` at the column's scale, `Date` is `Val::Date` (days since 1970-01-01), `Text` is
// `Val::Text` of the byte range, and `Values` carries any value (NULL, booleans, timestamps, mixed scales) as `EVal`.
// The trusted shim encodes a columnar answer into the same result wire as row answers (row by row), so the host and
// the trusted base are unchanged.
//
// Helpers: `text_column` / `push_text` build a text column on the calling thread; `lemma_columns_view` states the
// view pointwise and `lemma_columns_view_eq` gives `columns_view(c) == rows` from pointwise equality, so proofs about
// `Seq<Row>` outputs (for example `link::query::result_ok`) apply unchanged.
use vstd::prelude::*;
use crate::exec::value::EVal;
use crate::spec::value::{Row, Val};

verus! {

/// One output column of a columnar answer.
pub enum ResultColumn {
    /// `integer`/`bigint` values.
    Int(Vec<i64>),
    /// `numeric` coefficients, all at `scale`.
    Num { coeffs: Vec<i128>, scale: u32 },
    /// `date` values: days since 1970-01-01.
    Date(Vec<i32>),
    /// `text` values: value `i` is `bytes[offsets[i] .. offsets[i + 1]]` (`rows + 1` offsets).
    Text { offsets: Vec<usize>, bytes: Vec<u8> },
    /// Any values (NULL, booleans, timestamps, mixed numeric scales), one per row.
    Values(Vec<EVal>),
}

/// A columnar answer: `rows` result rows, one `ResultColumn` per output column in output order.
pub struct ResultColumns {
    pub rows: usize,
    pub columns: Vec<ResultColumn>,
}

/// Column `c` holds exactly `rows` values.
pub open spec fn column_wf(c: ResultColumn, rows: nat) -> bool {
    match c {
        ResultColumn::Int(v) => v@.len() == rows,
        ResultColumn::Num { coeffs, scale: _ } => coeffs@.len() == rows,
        ResultColumn::Date(v) => v@.len() == rows,
        ResultColumn::Text { offsets, bytes } => {
            &&& offsets@.len() == rows + 1
            &&& forall|i: int| 0 <= i < rows ==> #[trigger] offsets@[i] <= offsets@[i + 1] && offsets@[i + 1] <= bytes@.len()
        },
        ResultColumn::Values(v) => v@.len() == rows,
    }
}

/// Value `i` of column `c` (meaningful when `column_wf(c, rows)` and `i < rows`).
pub open spec fn column_value(c: ResultColumn, i: int) -> Val {
    match c {
        ResultColumn::Int(v) => Val::Int(v@[i] as int),
        ResultColumn::Num { coeffs, scale } => Val::Num { coeff: coeffs@[i] as int, scale: scale as nat },
        ResultColumn::Date(v) => Val::Date(v@[i] as int),
        ResultColumn::Text { offsets, bytes } => Val::Text(bytes@.subrange(offsets@[i] as int, offsets@[i + 1] as int)),
        ResultColumn::Values(v) => v@[i]@,
    }
}

/// Every column holds exactly `r.rows` values.
pub open spec fn columns_wf(r: ResultColumns) -> bool {
    forall|k: int| 0 <= k < r.columns@.len() ==> column_wf(#[trigger] r.columns@[k], r.rows as nat)
}

/// The result rows of a columnar answer: row `i` has `column_value(columns[k], i)` at position `k`.
pub open spec fn columns_view(r: ResultColumns) -> Seq<Row> {
    Seq::new(r.rows as nat, |i: int| Seq::new(r.columns@.len(), |k: int| column_value(r.columns@[k], i)))
}

/// Pointwise form of `columns_view`.
pub proof fn lemma_columns_view(r: ResultColumns, i: int, k: int)
    requires 0 <= i < r.rows, 0 <= k < r.columns@.len(),
    ensures
        columns_view(r).len() == r.rows,
        columns_view(r)[i].len() == r.columns@.len(),
        columns_view(r)[i][k] == column_value(r.columns@[k], i),
{
}

/// `columns_view(r)` equals `rows` when they agree in shape and at every position.
pub proof fn lemma_columns_view_eq(r: ResultColumns, rows: Seq<Row>)
    requires
        rows.len() == r.rows,
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] rows[i].len() == r.columns@.len(),
        forall|i: int, k: int| 0 <= i < rows.len() && 0 <= k < r.columns@.len() ==> #[trigger] rows[i][k] == column_value(r.columns@[k], i),
    ensures columns_view(r) == rows,
{
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] columns_view(r)[i] == rows[i] by {
        assert(columns_view(r)[i] =~= rows[i]);
    }
    assert(columns_view(r) =~= rows);
}

/// An empty text column under construction: offsets `[0]`, no bytes (calling thread; may allocate).
pub fn text_column() -> (r: (Vec<usize>, Vec<u8>))
    ensures r.0@ == seq![0usize], r.1@ == Seq::<u8>::empty(),
{
    let mut offsets: Vec<usize> = Vec::new();
    offsets.push(0);
    proof {
        assert(offsets@ =~= seq![0usize]);
    }
    (offsets, Vec::new())
}

/// Append one text value to a text column under construction (calling thread; may allocate). The last offset is the
/// byte length before and after, so the column stays well formed (`column_wf`) for one more row.
pub fn push_text(offsets: &mut Vec<usize>, bytes: &mut Vec<u8>, value: &[u8])
    requires
        old(offsets)@.len() >= 1,
        old(offsets)@.last() == old(bytes)@.len(),
        old(bytes)@.len() + value@.len() <= usize::MAX,
    ensures
        final(bytes)@ == old(bytes)@ + value@,
        final(offsets)@ == old(offsets)@.push(final(bytes)@.len() as usize),
        final(offsets)@.last() == final(bytes)@.len(),
{
    let n = value.len();
    let mut j: usize = 0;
    while j < n
        invariant
            n == value@.len(),
            j <= n,
            bytes@ == old(bytes)@ + value@.subrange(0, j as int),
            old(bytes)@.len() + n <= usize::MAX,
        decreases n - j,
    {
        bytes.push(value[j]);
        j = j + 1;
        proof {
            assert(bytes@ =~= old(bytes)@ + value@.subrange(0, j as int));
        }
    }
    proof {
        assert(value@.subrange(0, n as int) =~= value@);
    }
    let len = bytes.len();
    offsets.push(len);
}

} // verus!
