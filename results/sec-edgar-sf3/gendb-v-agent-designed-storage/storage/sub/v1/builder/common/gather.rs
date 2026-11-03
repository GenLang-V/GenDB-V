//! Gathers: a column read through a list of row positions (`out[k] = src[idx[k]]`), to store a column in another
//! row order, and the sparse form of a nullable text column (its non-NULL rows and their values).
use vstd::prelude::*;
use super::sort::{TextOrder, SortOrder};
use super::dict::{emit_text_list, row_in};
use super::icommon::text::{text_entry, text_parts_wf};

verus! {

/// `out[k] = src[idx[k]]` for every position of `idx`.
pub fn gather<T: Copy>(src: &[T], idx: &Vec<u64>) -> (out: Vec<T>)
    requires forall|k: int| 0 <= k < idx@.len() ==> #[trigger] idx@[k] < src@.len(),
    ensures out@.len() == idx@.len(), forall|k: int| 0 <= k < idx@.len() ==> #[trigger] out@[k] == src@[idx@[k] as int],
{
    let n = idx.len();
    let mut out: Vec<T> = Vec::with_capacity(n);
    let mut k: usize = 0;
    while k < n
        invariant
            n == idx@.len(), k <= n,
            forall|t: int| 0 <= t < idx@.len() ==> #[trigger] idx@[t] < src@.len(),
            out@.len() == k,
            forall|t: int| 0 <= t < k ==> #[trigger] out@[t] == src@[idx@[t] as int],
        decreases n - k,
    {
        let j = idx[k];
        assert(j < src.len());
        out.push(src[j as usize]);
        k = k + 1;
    }
    out
}

/// The same for a computed column.
pub fn gather_vec<T: Copy>(src: &Vec<T>, idx: &Vec<u64>) -> (out: Vec<T>)
    requires forall|k: int| 0 <= k < idx@.len() ==> #[trigger] idx@[k] < src@.len(),
    ensures out@.len() == idx@.len(), forall|k: int| 0 <= k < idx@.len() ==> #[trigger] out@[k] == src@[idx@[k] as int],
{
    gather(src.as_slice(), idx)
}

/// The non-NULL rows of a nullable text column (validity `valid`, 0: NULL), increasing, and their values as a text
/// list (value `k` belongs to row `rows[k]`).
pub fn sparse_text(o: &TextOrder, valid: &'static [u8]) -> (r: (Vec<u64>, Vec<u64>, Vec<u8>))
    requires o.wf(), valid@.len() == o.rows,
    ensures
        forall|a: int, b: int| 0 <= a < b < r.0@.len() ==> #[trigger] r.0@[a] < #[trigger] r.0@[b],
        forall|k: int| 0 <= k < r.0@.len() ==> #[trigger] r.0@[k] < o.rows && valid@[r.0@[k] as int] != 0,
        forall|i: int| 0 <= i < o.rows && valid@[i] != 0 ==> r.0@.contains(i as u64),
        text_parts_wf(r.1@, r.2@, r.0@.len() as int),
        forall|k: int| 0 <= k < r.0@.len() ==> #[trigger] text_entry(r.1@, r.2@, k) == o.value(r.0@[k]),
{
    let n = o.rows;
    let mut rows: Vec<u64> = Vec::new();
    let mut i: u64 = 0;
    while i < n
        invariant
            o.wf(), n == o.rows, valid@.len() == n, i <= n,
            forall|a: int, b: int| 0 <= a < b < rows@.len() ==> #[trigger] rows@[a] < #[trigger] rows@[b],
            forall|k: int| 0 <= k < rows@.len() ==> #[trigger] rows@[k] < i && valid@[rows@[k] as int] != 0,
            forall|t: int| 0 <= t < i && valid@[t] != 0 ==> rows@.contains(t as u64),
        decreases n - i,
    {
        if valid[i as usize] != 0 {
            let ghost before = rows@;
            rows.push(i);
            proof {
                assert forall|t: int| 0 <= t < i + 1 && valid@[t] != 0 implies rows@.contains(t as u64) by {
                    if t < i {
                        let k = choose|k: int| 0 <= k < before.len() && before[k] == t as u64;
                        assert(rows@[k] == t as u64);
                    } else {
                        assert(rows@[before.len() as int] == i);
                    }
                }
            }
        }
        i = i + 1;
    }
    let (off, bytes) = emit_text_list(o, &rows);
    (rows, off, bytes)
}

} // verus!
