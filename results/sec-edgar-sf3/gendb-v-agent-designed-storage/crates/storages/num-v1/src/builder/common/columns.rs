//! Column copies and row orders for builders: a text column as a flat text list (offsets rebased to 0), and the
//! permutation of row positions that lists a text column's rows in nondecreasing byte order.
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use super::sort::{par_sort, TextOrder, SortOrder, sorted_by, all_ok};
use super::icommon::text::{subslice, text_entry, text_parts_wf};
use super::icommon::perm::{ident, is_permutation};

verus! {

/// The column's text values as a flat text list: value `i` is row `i`'s value.
pub fn copy_text(o: &TextOrder) -> (r: (Vec<u64>, Vec<u8>))
    requires o.wf(),
    ensures
        text_parts_wf(r.0@, r.1@, o.rows as int),
        forall|i: int| 0 <= i < o.rows ==> #[trigger] text_entry(r.0@, r.1@, i) == o.value(i as u64),
{
    let n = o.rows as usize;
    if n == 0 {
        let off: Vec<u64> = vec![0u64; 1];
        let bytes: Vec<u8> = Vec::new();
        return (off, bytes);
    }
    let base = o.offsets[0];
    proof {
        assert(0 <= o.offsets@[0] <= o.offsets@[1] <= o.bytes@.len());
    }
    let mut off: Vec<u64> = Vec::with_capacity(n);
    off.push(0);
    let mut i: usize = 0;
    while i < n
        invariant
            o.wf(), n == o.rows, i <= n, base == o.offsets@[0],
            off@.len() == i + 1,
            forall|k: int| 0 <= k <= i ==> #[trigger] off@[k] == o.offsets@[k] - base,
            base <= o.offsets@[i as int] <= o.bytes@.len(),
        decreases n - i,
    {
        let next = o.offsets[i + 1];
        assert(o.offsets@[i as int] <= next);
        off.push((next - base) as u64);
        i = i + 1;
    }
    let end = o.offsets[n];
    proof {
        lemma_offsets_below_end(o, 0);
        assert(o.offsets@[n - 1] <= o.offsets@[n as int] <= o.bytes@.len());
    }
    assert(end <= o.bytes.len());
    let bytes = vstd::slice::slice_to_vec(subslice(o.bytes, base as usize, end as usize));
    proof {
        assert forall|a: int, b: int| 0 <= a <= b <= n implies #[trigger] off@[a] <= #[trigger] off@[b] by {
            lemma_offsets_monotone(o, a, b);
        }
        assert(off@[n as int] <= bytes@.len());
        assert forall|k: int| 0 <= k < n implies #[trigger] text_entry(off@, bytes@, k) == o.value(k as u64) by {
            assert(o.offsets@[k] <= o.offsets@[k + 1]);
            lemma_offsets_below_end(o, k + 1);
            assert(text_entry(off@, bytes@, k) =~= o.bytes@.subrange(o.offsets@[k] as int, o.offsets@[k + 1] as int));
        }
    }
    (off, bytes)
}

/// Offsets never decrease.
proof fn lemma_offsets_monotone(o: &TextOrder, a: int, b: int)
    requires o.wf(), 0 <= a <= b <= o.rows,
    ensures o.offsets@[a] <= o.offsets@[b],
    decreases b - a,
{
    if a < b {
        assert(o.offsets@[a] <= o.offsets@[a + 1]);
        lemma_offsets_monotone(o, a + 1, b);
    }
}

/// Offsets never pass the last one.
proof fn lemma_offsets_below_end(o: &TextOrder, k: int)
    requires o.wf(), 0 <= k <= o.rows,
    ensures o.offsets@[k] <= o.offsets@[o.rows as int],
    decreases o.rows - k,
{
    if k < o.rows {
        lemma_offsets_below_end(o, k + 1);
    }
}

/// The row positions `0..rows`.
fn row_positions(rows: u64) -> (r: Vec<u64>)
    requires rows < usize::MAX,
    ensures r@ == ident(rows as nat),
{
    let mut r: Vec<u64> = Vec::with_capacity(rows as usize);
    let mut i: u64 = 0;
    while i < rows
        invariant i <= rows, r@ == ident(i as nat),
        decreases rows - i,
    {
        r.push(i);
        i = i + 1;
        proof {
            assert(r@ =~= ident(i as nat));
        }
    }
    r
}

/// The permutation of row positions listing the column's rows in nondecreasing byte order.
pub fn sort_permutation(o: TextOrder, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<u64>, QueryError>)
    requires o.wf(), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> is_permutation(p@, o.rows as nat)
            && (forall|k: int| 0 <= k < p@.len() ==> #[trigger] p@[k] < o.rows)
            && (forall|a: int, b: int| 0 <= a < b < p@.len()
                ==> lex_cmp(o.value(#[trigger] p@[a]), o.value(#[trigger] p@[b])) <= 0),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ids = row_positions(o.rows);
    proof {
        assert forall|i: int| 0 <= i < ids@.len() implies o.ok(#[trigger] ids@[i]) by {}
    }
    let p = par_sort(o, ids, workers, dispatch)?;
    proof {
        assert forall|k: int| 0 <= k < p@.len() implies #[trigger] p@[k] < o.rows by {
            assert(o.ok(p@[k]));
        }
        assert forall|a: int, b: int| 0 <= a < b < p@.len()
            implies lex_cmp(o.value(#[trigger] p@[a]), o.value(#[trigger] p@[b])) <= 0 by {
            assert(o.le(p@[a], p@[b]));
        }
    }
    Ok(p)
}

} // verus!
