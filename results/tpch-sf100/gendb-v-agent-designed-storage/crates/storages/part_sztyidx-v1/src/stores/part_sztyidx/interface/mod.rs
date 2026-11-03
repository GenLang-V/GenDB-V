//! Storage `part_sztyidx`: a secondary composite index of table part on (p_size, p_type) (stored relation: the
//! p_type and p_size columns of every canonical part row, `rels[0][r] == [p_type of row r, p_size of row r]`).
//!
//! Parts:
//! - `META` (I64 `[mode, kmin]`);
//! - `TOFFS` (U64, `T + 1 >= 1` offsets) and `TBYTES` (U8): the `T` key texts of p_type, `key_text(t)` for `t < T`
//!   (the index's key dictionary, always present);
//! - mode `MODE_DIRECTORY` (1), a dense directory over the composite keys `e < nkeys`, key `e` standing for
//!   (p_size `kmin + e / T`, p_type `key_text(e % T)`): `OFFS` (U32, `nkeys + 1 >= 1` offsets, from 0 to `rows`,
//!   nondecreasing) and `PERM` (U32, `rows` canonical row numbers). Entry `e` is the range
//!   `PERM[OFFS[e] .. OFFS[e + 1]]`: exactly the rows whose (p_size, p_type) is key `e`, in strictly increasing row
//!   order (`directory_ok`: every row of the range has that key, every row appears in `PERM`, no row appears
//!   twice). `KEYS` and `TENT` are empty;
//! - any other mode (the fallback for key ranges too wide for a dense directory): `KEYS` (I64) holds the p_size and
//!   `TENT` (U64) the key text number of every row as a one-row index entry; `OFFS` and `PERM` are empty.
//! Every stored value is a row position, an offset, or a key of the index; nothing else is derived.
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
/// Part index of the key text offsets (U64).
pub const TOFFS: usize = 3;
/// Part index of the key text bytes (U8).
pub const TBYTES: usize = 4;
/// Part index of the fallback p_size keys (I64).
pub const KEYS: usize = 5;
/// Part index of the fallback key text numbers (U64).
pub const TENT: usize = 6;
/// Number of parts.
pub const STYIDX_PARTS: usize = 7;
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

/// The values of a U64 part (empty for another kind).
pub open spec fn idx_u64s(p: PartView) -> Seq<u64> {
    match p {
        PartView::U64(s) => s,
        _ => Seq::empty(),
    }
}

/// The values of a U8 part (empty for another kind).
pub open spec fn idx_u8s(p: PartView) -> Seq<u8> {
    match p {
        PartView::U8(s) => s,
        _ => Seq::empty(),
    }
}

/// Key text `t`: `bytes[offs[t] .. offs[t + 1]]`.
pub open spec fn key_text(offs: Seq<u64>, bytes: Seq<u8>, t: int) -> Seq<u8> {
    bytes.subrange(offs[t] as int, offs[t + 1] as int)
}

/// `T` key texts: `T + 1` nondecreasing offsets inside the bytes.
pub open spec fn texts_ok(offs: Seq<u64>, bytes: Seq<u8>) -> bool {
    &&& offs.len() >= 1
    &&& forall|t: int| 0 <= t < offs.len() - 1 ==> #[trigger] offs[t] <= offs[t + 1] && offs[t + 1] <= bytes.len()
}

/// Position `j` of the permutation lies in directory entry `e`.
pub open spec fn in_entry(offs: Seq<u32>, e: int, j: int) -> bool {
    offs[e] <= j < offs[e + 1]
}

/// Row `r` appears in the permutation.
pub open spec fn listed(perm: Seq<u32>, r: int) -> bool {
    exists|j: int| 0 <= j < perm.len() && perm[j] == r
}

/// Row `rr` of the relation has the composite key `e`: p_size `kmin + e / nt` and p_type key text `e % nt`.
pub open spec fn has_key(rr: Row, kmin: int, nt: int, toffs: Seq<u64>, tbytes: Seq<u8>, e: int) -> bool {
    &&& rr[1] == Val::Int(kmin + e / nt)
    &&& rr[0] == Val::Text(key_text(toffs, tbytes, e % nt))
}

/// A dense directory over the `k = offs.len() - 1` composite keys of the `n = rel.len()` rows (`nt` key texts):
/// every row of an entry has its key, every row is listed exactly once, rows increase inside an entry.
pub open spec fn directory_ok(kmin: int, nt: int, toffs: Seq<u64>, tbytes: Seq<u8>, offs: Seq<u32>, perm: Seq<u32>, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    let k = offs.len() - 1;
    &&& offs.len() >= 1
    &&& (k == 0 || nt >= 1)
    &&& offs[0] == 0
    &&& offs[k] == n
    &&& forall|e: int| 0 <= e < k ==> #[trigger] offs[e] <= offs[e + 1]
    &&& perm.len() == n
    &&& forall|e: int, j: int| 0 <= e < k && #[trigger] in_entry(offs, e, j) ==>
            perm[j] < n && has_key(rel[perm[j] as int], kmin, nt, toffs, tbytes, e)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] listed(perm, r)
    &&& forall|j1: int, j2: int| 0 <= j1 < n && 0 <= j2 < n && j1 != j2 ==> #[trigger] perm[j1] != #[trigger] perm[j2]
    &&& forall|e: int, j1: int, j2: int| 0 <= e < k && #[trigger] in_entry(offs, e, j1) && #[trigger] in_entry(offs, e, j2)
            && j1 < j2 ==> perm[j1] < perm[j2]
}

/// The parts index the p_type and p_size columns `rels[0]` (two-column rows, canonical order).
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    let toffs = idx_u64s(parts[TOFFS as int]);
    let tbytes = idx_u8s(parts[TBYTES as int]);
    let nt = toffs.len() - 1;
    &&& parts.len() == STYIDX_PARTS
    &&& rels.len() == 1
    &&& forall|r: int| 0 <= r < rels[0].len() ==> (#[trigger] rels[0][r]).len() == 2
    &&& parts[META as int] is I64 && parts[OFFS as int] is U32 && parts[PERM as int] is U32
    &&& parts[TOFFS as int] is U64 && parts[TBYTES as int] is U8 && parts[KEYS as int] is I64 && parts[TENT as int] is U64
    &&& idx_i64s(parts[META as int]).len() == 2
    &&& texts_ok(toffs, tbytes)
    &&& if idx_i64s(parts[META as int])[0] == MODE_DIRECTORY {
            directory_ok(idx_i64s(parts[META as int])[1] as int, nt, toffs, tbytes,
                idx_u32s(parts[OFFS as int]), idx_u32s(parts[PERM as int]), rels[0])
        } else {
            &&& idx_i64s(parts[KEYS as int]).len() == rels[0].len()
            &&& idx_u64s(parts[TENT as int]).len() == rels[0].len()
            &&& forall|r: int| 0 <= r < rels[0].len() ==> {
                    &&& idx_u64s(parts[TENT as int])[r] < nt
                    &&& #[trigger] rels[0][r][1] == Val::Int(idx_i64s(parts[KEYS as int])[r] as int)
                    &&& rels[0][r][0] == Val::Text(key_text(toffs, tbytes, idx_u64s(parts[TENT as int])[r] as int))
                }
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

/// The parts determine the relation they index: every row is listed in the entry of its key (directory), or its
/// keys are stored (fallback).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    let meta = idx_i64s(parts[META as int]);
    let (toffs, tbytes) = (idx_u64s(parts[TOFFS as int]), idx_u8s(parts[TBYTES as int]));
    let nt = toffs.len() - 1;
    let (ra, rb) = (a[0], b[0]);
    if meta[0] == MODE_DIRECTORY {
        let offs = idx_u32s(parts[OFFS as int]);
        assert(ra.len() == offs[offs.len() - 1] && rb.len() == offs[offs.len() - 1]);
    }
    assert(ra.len() == rb.len());
    assert forall|r: int| 0 <= r < ra.len() implies ra[r] == rb[r] by {
        if meta[0] == MODE_DIRECTORY {
            let (offs, perm) = (idx_u32s(parts[OFFS as int]), idx_u32s(parts[PERM as int]));
            let (kmin, k) = (meta[1] as int, offs.len() - 1);
            assert(listed(perm, r));
            let j = choose|j: int| 0 <= j < perm.len() && perm[j] == r;
            let e = lemma_find_entry(offs, k, j);
            assert(has_key(ra[perm[j] as int], kmin, nt, toffs, tbytes, e));
            assert(has_key(rb[perm[j] as int], kmin, nt, toffs, tbytes, e));
        } else {
            assert(ra[r][1] == rb[r][1]);
        }
        assert(ra[r] =~= rb[r]);
    }
    assert(ra =~= rb);
    assert(a =~= b);
}

/// Composite key `e` of `nt >= 1` key texts has p_size number `e / nt` and key text `e % nt < nt`; the keys of
/// p_size number `s` are `s * nt .. s * nt + nt`.
pub proof fn lemma_key_split(e: int, nt: int, s: int)
    requires 0 <= e, nt >= 1,
    ensures
        0 <= e % nt < nt,
        e / nt >= 0,
        e / nt == s <==> s * nt <= e < s * nt + nt,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(e, nt);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(e, nt);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(e, nt);
    let q = e / nt;
    if q == s {
        assert(nt * q == s * nt) by (nonlinear_arith) requires q == s;
    } else if q < s {
        assert(nt * q + nt <= s * nt) by (nonlinear_arith) requires q < s, nt >= 1;
    } else {
        assert(nt * q >= s * nt + nt) by (nonlinear_arith) requires q > s, nt >= 1;
    }
}

} // verus!
