//! Sorted dictionary encoding of a text column: the distinct values of the column's non-NULL rows in strictly
//! increasing byte order (as representative row ids), and per row the position of its value in that dictionary.
//! Built by a parallel sort of the row ids by value (`sort::par_sort`), one deduplicating pass that also assigns
//! every row its code, and an emitter that writes a list of values as text parts (U64 offsets + U8 bytes).
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::order::{lemma_lex_cmp_antisym, lemma_lex_cmp_trans};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use super::sort::{par_sort, text_value, lex_cmp_slices, TextOrder, SortOrder, sorted_by, all_ok};
use super::icommon::text::{text_entry, text_parts_wf, text_strictly_sorted, lemma_lex_cmp_lt_trans};

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// Row `i` takes part in the dictionary: the column is NOT NULL, or the row's validity byte is nonzero.
pub open spec fn row_in(valid: Seq<u8>, nullable: bool, i: int) -> bool {
    !nullable || valid[i] != 0
}

/// Representative row ids of a dictionary: rows of the column, values strictly increasing.
pub open spec fn dict_ids_ok(o: TextOrder, ids: Seq<u64>) -> bool {
    &&& forall|k: int| 0 <= k < ids.len() ==> #[trigger] ids[k] < o.rows
    &&& forall|a: int, b: int| 0 <= a < b < ids.len() ==> lex_cmp(o.value(#[trigger] ids[a]), o.value(#[trigger] ids[b])) < 0
}

/// Every row in the dictionary has the code of its value.
pub open spec fn codes_ok(o: TextOrder, valid: Seq<u8>, nullable: bool, ids: Seq<u64>, codes: Seq<u64>) -> bool {
    &&& codes.len() == o.rows
    &&& forall|i: int| 0 <= i < o.rows && row_in(valid, nullable, i)
        ==> (#[trigger] codes[i]) < ids.len() && o.value(ids[codes[i] as int]) == o.value(i as u64)
}

/// A dictionary of a text column and the code of every row.
pub struct TextDict {
    /// Representative row of each dictionary value, in strictly increasing value order.
    pub ids: Vec<u64>,
    /// Per row: dictionary position of its value (0 for rows outside the dictionary).
    pub codes: Vec<u64>,
}

/// The rows that take part, in increasing order.
fn participating_rows(o: &TextOrder, valid: &'static [u8], nullable: bool) -> (ids: Vec<u64>)
    requires o.wf(), nullable ==> valid@.len() == o.rows,
    ensures
        all_ok(*o, ids@),
        forall|a: int, b: int| 0 <= a < b < ids@.len() ==> #[trigger] ids@[a] < #[trigger] ids@[b],
        forall|i: int| 0 <= i < o.rows && row_in(valid@, nullable, i) ==> ids@.contains(i as u64),
{
    let mut ids: Vec<u64> = Vec::new();
    let mut i: u64 = 0;
    while i < o.rows
        invariant
            o.wf(), nullable ==> valid@.len() == o.rows, i <= o.rows,
            all_ok(*o, ids@),
            forall|k: int| 0 <= k < ids@.len() ==> #[trigger] ids@[k] < i,
            forall|a: int, b: int| 0 <= a < b < ids@.len() ==> #[trigger] ids@[a] < #[trigger] ids@[b],
            forall|r: int| 0 <= r < i && row_in(valid@, nullable, r) ==> ids@.contains(r as u64),
        decreases o.rows - i,
    {
        let take = !nullable || valid[i as usize] != 0;
        let ghost before = ids@;
        if take {
            ids.push(i);
            proof {
                assert forall|r: int| 0 <= r < i + 1 && row_in(valid@, nullable, r) implies ids@.contains(r as u64) by {
                    if r < i {
                        let k = choose|k: int| 0 <= k < before.len() && before[k] == r as u64;
                        assert(ids@[k] == r as u64);
                    } else {
                        assert(ids@[before.len() as int] == i);
                    }
                }
            }
        } else {
            proof {
                assert forall|r: int| 0 <= r < i + 1 && row_in(valid@, nullable, r) implies ids@.contains(r as u64) by {
                    if r == i {
                        assert(!row_in(valid@, nullable, r));
                    }
                }
            }
        }
        i = i + 1;
    }
    ids
}

/// Strictly increasing values below `n` number at most `n`.
proof fn lemma_rows_bound(s: Seq<u64>, n: int)
    requires
        forall|a: int, b: int| 0 <= a < b < s.len() ==> #[trigger] s[a] < #[trigger] s[b],
        forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] < n,
        n >= 0,
    ensures s.len() <= n,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|k: int| 0 <= k < t.len() implies #[trigger] t[k] < s.last() by {
            assert(s[k] < s[s.len() - 1]);
        }
        assert(s[s.len() - 1] < n);
        lemma_rows_bound(t, s.last() as int);
    }
}

/// A sequence with the multiset of a sequence without duplicates has no duplicates.
proof fn lemma_no_duplicates_transfer<A>(a: Seq<A>, b: Seq<A>)
    requires a.to_multiset() == b.to_multiset(), b.no_duplicates(),
    ensures a.no_duplicates(),
{
    b.lemma_multiset_has_no_duplicates();
    a.lemma_multiset_has_no_duplicates_conv();
}

/// Strictly increasing values have no duplicates.
proof fn lemma_increasing_no_duplicates(s: Seq<u64>)
    requires forall|a: int, b: int| 0 <= a < b < s.len() ==> #[trigger] s[a] < #[trigger] s[b],
    ensures s.no_duplicates(),
{
    assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j implies s[i] != s[j] by {
        if i < j {
            assert(s[i] < s[j]);
        } else {
            assert(s[j] < s[i]);
        }
    }
}

/// Text equality of two rows, `no_unwind`.
fn same_value(o: &TextOrder, a: u64, b: u64) -> (r: bool)
    requires o.wf(), a < o.rows, b < o.rows,
    ensures r == (o.value(a) == o.value(b)), r == (lex_cmp(o.value(a), o.value(b)) == 0),
    no_unwind
{
    proof {
        assert(0 <= o.offsets@[a as int] <= o.offsets@[a + 1] <= o.bytes@.len());
        assert(0 <= o.offsets@[b as int] <= o.offsets@[b + 1] <= o.bytes@.len());
    }
    let (x, xn) = text_value(o.offsets, o.bytes, a as usize);
    let (y, yn) = text_value(o.offsets, o.bytes, b as usize);
    proof { lemma_lex_cmp_zero(x@, y@); }
    lex_cmp_slices(x, xn, y, yn) == 0
}

/// Dictionary of the participating rows of a text column and the code of every row.
pub fn build_text_dict(o: TextOrder, valid: &'static [u8], nullable: bool, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<TextDict, QueryError>)
    requires
        o.wf(),
        nullable ==> valid@.len() == o.rows,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(d) ==> dict_ids_ok(o, d.ids@) && codes_ok(o, valid@, nullable, d.ids@, d.codes@)
            && d.ids@.len() <= o.rows,
        r matches Err(e) ==> e is WorkerFailed,
{
    let rows = participating_rows(&o, valid, nullable);
    let ghost rows_view = rows@;
    let sorted = par_sort(o, rows, workers, dispatch)?;
    proof {
        lemma_increasing_no_duplicates(rows_view);
        lemma_no_duplicates_transfer(sorted@, rows_view);
    }
    let n = sorted.len();
    let mut codes: Vec<u64> = vec![0u64; o.rows as usize];
    let mut ids: Vec<u64> = Vec::new();
    let mut q: usize = 0;
    while q < n
        invariant
            o.wf(),
            n == sorted@.len(),
            q <= n,
            sorted_by(o, sorted@), all_ok(o, sorted@), sorted@.no_duplicates(),
            codes@.len() == o.rows,
            dict_ids_ok(o, ids@),
            ids@.len() <= q,
            q > 0 ==> ids@.len() > 0 && o.value(ids@.last()) == o.value(sorted@[q - 1]),
            q == 0 ==> ids@.len() == 0,
            forall|p: int| 0 <= p < q ==> (#[trigger] codes@[sorted@[p] as int]) < ids@.len()
                && o.value(ids@[codes@[sorted@[p] as int] as int]) == o.value(sorted@[p]),
        decreases n - q,
    {
        let x = sorted[q];
        let fresh = if q == 0 { true } else { !same_value(&o, ids[ids.len() - 1], x) };
        let ghost ids_before = ids@;
        if fresh {
            proof {
                if q > 0 {
                    let last = ids@.last();
                    assert(o.le(sorted@[q - 1], sorted@[q as int]));
                    assert(lex_cmp(o.value(last), o.value(x)) <= 0);
                    assert(lex_cmp(o.value(last), o.value(x)) < 0);
                    assert forall|a: int| 0 <= a < ids@.len() implies lex_cmp(o.value(#[trigger] ids@[a]), o.value(x)) < 0 by {
                        if a < ids@.len() - 1 {
                            assert(lex_cmp(o.value(ids@[a]), o.value(last)) < 0);
                            lemma_lex_cmp_lt_trans(o.value(ids@[a]), o.value(last), o.value(x));
                        }
                    }
                }
            }
            ids.push(x);
            proof {
                assert forall|a: int, b: int| 0 <= a < b < ids@.len()
                    implies lex_cmp(o.value(#[trigger] ids@[a]), o.value(#[trigger] ids@[b])) < 0 by {
                    if b == ids@.len() - 1 {
                        assert(ids@[b] == x);
                        assert(ids@[a] == ids_before[a]);
                    } else {
                        assert(ids@[a] == ids_before[a] && ids@[b] == ids_before[b]);
                    }
                }
            }
        }
        let code = (ids.len() - 1) as u64;
        let ghost codes_before = codes@;
        codes[x as usize] = code;
        proof {
            assert(o.value(ids@[code as int]) == o.value(x));
            assert forall|p: int| 0 <= p < q + 1 implies (#[trigger] codes@[sorted@[p] as int]) < ids@.len()
                && o.value(ids@[codes@[sorted@[p] as int] as int]) == o.value(sorted@[p]) by {
                if p < q {
                    assert(sorted@[p] != sorted@[q as int]);
                    assert(codes@[sorted@[p] as int] == codes_before[sorted@[p] as int]);
                    assert(ids@[codes_before[sorted@[p] as int] as int] == ids_before[codes_before[sorted@[p] as int] as int]);
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert forall|k: int| 0 <= k < rows_view.len() implies #[trigger] rows_view[k] < o.rows by {
            assert(o.ok(rows_view[k]));
        }
        lemma_rows_bound(rows_view, o.rows as int);
        assert(sorted@.len() == sorted@.to_multiset().len());
        assert(rows_view.len() == rows_view.to_multiset().len());
        assert forall|i: int| 0 <= i < o.rows && row_in(valid@, nullable, i)
            implies (#[trigger] codes@[i]) < ids@.len() && o.value(ids@[codes@[i] as int]) == o.value(i as u64) by {
            assert(rows_view.contains(i as u64));
            assert(rows_view.to_multiset().count(i as u64) > 0);
            assert(sorted@.to_multiset().count(i as u64) > 0);
            assert(sorted@.contains(i as u64));
            let p = choose|p: int| 0 <= p < sorted@.len() && sorted@[p] == i as u64;
            assert(codes@[sorted@[p] as int] < ids@.len());
        }
    }
    Ok(TextDict { ids, codes })
}

/// The values of rows `ids` of a text column, in that order, as text parts (U64 offsets + U8 bytes).
pub fn emit_text_list(o: &TextOrder, ids: &Vec<u64>) -> (r: (Vec<u64>, Vec<u8>))
    requires
        o.wf(),
        forall|k: int| 0 <= k < ids@.len() ==> #[trigger] ids@[k] < o.rows,
    ensures
        text_parts_wf(r.0@, r.1@, ids@.len() as int),
        forall|k: int| 0 <= k < ids@.len() ==> #[trigger] text_entry(r.0@, r.1@, k) == o.value(ids@[k]),
{
    let n = ids.len();
    let mut off: Vec<u64> = Vec::with_capacity(n);
    let mut bytes: Vec<u8> = Vec::new();
    off.push(0);
    let mut k: usize = 0;
    while k < n
        invariant
            o.wf(),
            n == ids@.len(),
            forall|t: int| 0 <= t < ids@.len() ==> #[trigger] ids@[t] < o.rows,
            k <= n,
            off@.len() == k + 1,
            off@[k as int] == bytes@.len(),
            forall|a: int, b: int| 0 <= a <= b <= k ==> #[trigger] off@[a] <= #[trigger] off@[b],
            forall|t: int| 0 <= t < k ==> #[trigger] text_entry(off@, bytes@, t) == o.value(ids@[t]),
        decreases n - k,
    {
        let id = ids[k];
        proof {
            assert(0 <= o.offsets@[id as int] <= o.offsets@[id + 1] <= o.bytes@.len());
        }
        let (v, _vn) = text_value(o.offsets, o.bytes, id as usize);
        let ghost before = bytes@;
        let ghost off_before = off@;
        bytes.extend_from_slice(v);
        proof {
            assert(bytes@ =~= before + v@);
        }
        let end = bytes.len() as u64;
        off.push(end);
        proof {
            assert forall|a: int, b: int| 0 <= a <= b <= k + 1 implies #[trigger] off@[a] <= #[trigger] off@[b] by {
                if b == k + 1 && a <= k {
                    assert(off@[a] == off_before[a] && off_before[a] <= off_before[k as int]);
                }
                if b <= k {
                    assert(off@[a] == off_before[a] && off@[b] == off_before[b]);
                }
            }
            assert forall|t: int| 0 <= t < k + 1 implies #[trigger] text_entry(off@, bytes@, t) == o.value(ids@[t]) by {
                if t < k {
                    assert(off@[t] == off_before[t] && off@[t + 1] == off_before[t + 1]);
                    assert(off_before[t] <= off_before[t + 1] && off_before[t + 1] <= off_before[k as int]);
                    assert(text_entry(off_before, before, t) == o.value(ids@[t]));
                    assert(bytes@.subrange(off@[t] as int, off@[t + 1] as int)
                        =~= before.subrange(off@[t] as int, off@[t + 1] as int));
                } else {
                    assert(bytes@.subrange(off@[t] as int, off@[t + 1] as int) =~= v@);
                }
            }
        }
        k = k + 1;
    }
    (off, bytes)
}

/// A dictionary's values strictly increase, so its emitted text list is a sorted dictionary.
pub proof fn lemma_emitted_sorted(o: TextOrder, ids: Seq<u64>, off: Seq<u64>, bytes: Seq<u8>)
    requires
        dict_ids_ok(o, ids),
        forall|k: int| 0 <= k < ids.len() ==> #[trigger] text_entry(off, bytes, k) == o.value(ids[k]),
    ensures
        text_strictly_sorted(off, bytes, ids.len() as int),
{
    assert forall|a: int, b: int| 0 <= a < b < ids.len()
        implies lex_cmp(#[trigger] text_entry(off, bytes, a), #[trigger] text_entry(off, bytes, b)) < 0 by {
        assert(lex_cmp(o.value(ids[a]), o.value(ids[b])) < 0);
    }
}

} // verus!
