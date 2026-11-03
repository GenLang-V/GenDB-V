//! Storage `ps_suppidx`: a secondary index of table partsupp on ps_suppkey (stored relation: the ps_suppkey column
//! of every canonical partsupp row, `rels[0][r] == [ps_suppkey of row r]`), built from storage `suppliers`.
//!
//! Parts:
//! - `META` (I64 `[mode, kmin]`);
//! - mode `MODE_DIRECTORY` (1), a dense directory over the keys `kmin .. kmin + nkeys`: `OFFS` (U32, `nkeys + 1 >= 1`
//!   offsets, from 0 to `rows`, nondecreasing) and `PERM` (U32, `rows` canonical row numbers). Entry `e` is the
//!   range `PERM[OFFS[e] .. OFFS[e + 1]]`: exactly the rows whose key is `kmin + e` (`directory_ok`: every row of the
//!   range has that key, every row appears in `PERM`, and the range length is the number of rows with that key,
//!   `count_key`). Every key lies in `kmin .. kmin + nkeys`, so a key outside has no row. `KEYS` is empty;
//! - any other mode (the fallback for key ranges too wide for a dense directory): `KEYS` (I64) holds the key of
//!   every row as a one-row index entry; `OFFS` and `PERM` are empty.
//! Every stored value is a row position, an offset, or a key of the index; nothing else is derived.
//! (The layout and its lemmas follow the admitted index `orders_custidx`.)
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};

verus! {

/// Part index of the header `[mode, kmin]` (I64).
pub const META: usize = 0;
/// Part index of the directory offsets (U32).
pub const OFFS: usize = 1;
/// Part index of the permutation of canonical rows (U32).
pub const PERM: usize = 2;
/// Part index of the fallback keys (I64).
pub const KEYS: usize = 3;
/// Number of parts.
pub const SUPPIDX_PARTS: usize = 4;
/// The mode of a dense directory.
pub const MODE_DIRECTORY: i64 = 1;

/// The values of an I64 part (empty for another kind).
pub open spec fn idx_i64s(p: PartView) -> Seq<i64> {
    match p {
        PartView::I64(s) => s,
        _ => Seq::empty(),
    }
}

/// The values of a U32 part (empty for another kind).
pub open spec fn idx_u32s(p: PartView) -> Seq<u32> {
    match p {
        PartView::U32(s) => s,
        _ => Seq::empty(),
    }
}

/// Number of the rows `0 .. m` of `rel` whose key (column 0) is the integer `v`.
pub open spec fn count_key(rel: Seq<Row>, v: int, m: int) -> nat
    decreases m,
{
    if m <= 0 {
        0
    } else {
        count_key(rel, v, m - 1) + if rel[m - 1][0] == Val::Int(v) { 1nat } else { 0nat }
    }
}

/// Position `j` of the permutation lies in directory entry `e`.
pub open spec fn in_entry(offs: Seq<u32>, e: int, j: int) -> bool {
    offs[e] <= j < offs[e + 1]
}

/// Row `r` appears in the permutation.
pub open spec fn listed(perm: Seq<u32>, r: int) -> bool {
    exists|j: int| 0 <= j < perm.len() && perm[j] == r
}

/// The key of row `r` is an integer in `kmin .. kmin + k`.
pub open spec fn key_in_range(rel: Seq<Row>, kmin: int, k: int, r: int) -> bool {
    rel[r][0] is Int && kmin <= rel[r][0]->Int_0 < kmin + k
}

/// A dense directory over the keys `kmin .. kmin + k` of the `n = rel.len()` rows.
pub open spec fn directory_ok(kmin: int, k: int, offs: Seq<u32>, perm: Seq<u32>, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    &&& 0 <= k
    &&& offs.len() == k + 1
    &&& offs[0] == 0
    &&& offs[k] == n
    &&& forall|e: int| 0 <= e < k ==> #[trigger] offs[e] <= offs[e + 1]
    &&& perm.len() == n
    &&& forall|e: int| 0 <= e < k ==> #[trigger] offs[e + 1] - offs[e] == count_key(rel, kmin + e, n)
    &&& forall|e: int, j: int| 0 <= e < k && #[trigger] in_entry(offs, e, j) ==>
            perm[j] < n && rel[perm[j] as int][0] == Val::Int(kmin + e)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] key_in_range(rel, kmin, k, r)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] listed(perm, r)
}

/// The parts index the ps_suppkey column `rels[0]` (one-column rows, canonical order).
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == SUPPIDX_PARTS
    &&& rels.len() == 1
    &&& forall|r: int| 0 <= r < rels[0].len() ==> (#[trigger] rels[0][r]).len() == 1
    &&& parts[META as int] is I64 && parts[OFFS as int] is U32 && parts[PERM as int] is U32 && parts[KEYS as int] is I64
    &&& idx_i64s(parts[META as int]).len() == 2
    &&& if idx_i64s(parts[META as int])[0] == MODE_DIRECTORY {
            &&& idx_u32s(parts[OFFS as int]).len() >= 1
            &&& directory_ok(idx_i64s(parts[META as int])[1] as int, idx_u32s(parts[OFFS as int]).len() - 1,
                    idx_u32s(parts[OFFS as int]), idx_u32s(parts[PERM as int]), rels[0])
        } else {
            &&& idx_i64s(parts[KEYS as int]).len() == rels[0].len()
            &&& forall|r: int| 0 <= r < rels[0].len() ==>
                    #[trigger] rels[0][r][0] == Val::Int(idx_i64s(parts[KEYS as int])[r] as int)
        }
}

/// A position below `offs[k]` lies in some directory entry (the offsets are nondecreasing from `offs[0] == 0`).
pub proof fn lemma_find_entry(offs: Seq<u32>, k: int, j: int) -> (e: int)
    requires
        0 <= k,
        offs.len() == k + 1,
        offs[0] == 0,
        forall|e: int| 0 <= e < k ==> #[trigger] offs[e] <= offs[e + 1],
        0 <= j < offs[k],
    ensures
        0 <= e < k,
        in_entry(offs, e, j),
    decreases k,
{
    if j >= offs[k - 1] {
        k - 1
    } else {
        lemma_find_entry(offs.subrange(0, k), k - 1, j)
    }
}

/// The parts determine the relation they index: every row is listed in exactly the entry of its key (directory),
/// or its key is stored (fallback).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    let meta = idx_i64s(parts[META as int]);
    let (ra, rb) = (a[0], b[0]);
    assert(ra.len() == rb.len());
    assert forall|r: int| 0 <= r < ra.len() implies ra[r] == rb[r] by {
        if meta[0] == MODE_DIRECTORY {
            let (offs, perm) = (idx_u32s(parts[OFFS as int]), idx_u32s(parts[PERM as int]));
            let (kmin, k) = (meta[1] as int, offs.len() - 1);
            assert(listed(perm, r));
            let j = choose|j: int| 0 <= j < perm.len() && perm[j] == r;
            let e = lemma_find_entry(offs, k, j);
            assert(ra[perm[j] as int][0] == Val::Int(kmin + e));
            assert(rb[perm[j] as int][0] == Val::Int(kmin + e));
        } else {
            assert(ra[r][0] == rb[r][0]);
        }
        assert(ra[r] =~= rb[r]);
    }
    assert(ra =~= rb);
    assert(a =~= b);
}

/// No row of `rel[..m]` has key `v`: the count is zero.
pub proof fn lemma_count_none(rel: Seq<Row>, v: int, m: int)
    requires forall|r: int| 0 <= r < m ==> #[trigger] rel[r][0] != Val::Int(v),
    ensures count_key(rel, v, m) == 0,
    decreases m,
{
    if m > 0 {
        lemma_count_none(rel, v, m - 1);
    }
}

/// Under a dense directory, a key outside `kmin .. kmin + k` has no row.
pub proof fn lemma_directory_outside(kmin: int, k: int, offs: Seq<u32>, perm: Seq<u32>, rel: Seq<Row>, v: int)
    requires
        directory_ok(kmin, k, offs, perm, rel),
        !(kmin <= v < kmin + k),
    ensures
        count_key(rel, v, rel.len() as int) == 0,
{
    assert forall|r: int| 0 <= r < rel.len() implies #[trigger] rel[r][0] != Val::Int(v) by {
        assert(key_in_range(rel, kmin, k, r));
    }
    lemma_count_none(rel, v, rel.len() as int);
}

} // verus!
