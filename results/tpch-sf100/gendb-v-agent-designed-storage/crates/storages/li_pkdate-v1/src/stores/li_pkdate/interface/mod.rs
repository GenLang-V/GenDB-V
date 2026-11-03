//! Storage `li_pkdate`: storage `facts` unchanged (its 75 parts, inherited), followed by a composite index of lineitem
//! on `(l_partkey, l_shipdate)`.
//!
//! What this interface states about the inherited parts (the stored relation is lineitem projected on
//! `[l_partkey, l_suppkey, l_quantity, l_shipdate]`, canonical row order):
//! - part `LI_LAYOUT` is U64 `[n, bsize]` (`bsize >= 1` rows per block);
//! - every column below is frame-of-reference coded over blocks of `bsize` rows: the value of stored row `s` is
//!   `base[s / bsize] + code[s]` (I64 bases, U16 or U32 codes; the row map has U64 bases);
//! - the row map (`LI_PERM_*`): stored row `s` is canonical row `map_at(s)`, a bijection of `[0, n)`;
//! - canonical row `map_at(s)` is `[Int(key_at(s)), Int(supp_at(s)), Num(qty_at(s), 2), Date(date_at(s))]`.
//!
//! The new parts:
//! - `IDX_META` (I64 `[mode, kmin, dbase]`): mode `MODE_INDEX` (1) when the index is present;
//! - `IDX_OFFS` (U32, `nkeys + 1` nondecreasing offsets at most `n`): a dense directory over the keys
//!   `kmin .. kmin + nkeys`;
//! - `IDX_ROWS` (U32, `n`): index position `p` holds stored row `irow(p)`, a bijection of `[0, n)`; every position lies
//!   in the directory entry of its row's key (`in_entry`), so entry `e` (positions `offs[e] .. offs[e + 1]`) holds
//!   exactly the stored rows of key `kmin + e` (`lemma_entry_exact`) and a key outside the range has no row;
//! - `IDX_DATES` (U16, `n`): `dbase + dates[p]` is the l_shipdate of `irow(p)`, nondecreasing along each entry.
//! Every new value is a row position, an offset or a key of the index; no other column value is stored.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};

verus! {

// ------------------------------------------------------------------------------------------------ part indices

/// lineitem: U64 `[rows, block rows]`.
pub const LI_LAYOUT: usize = 0;
/// lineitem: U32 codes of the canonical row of each stored row.
pub const LI_PERM_CODES: usize = 2;
/// lineitem: U64 block bases of canonical rows.
pub const LI_PERM_BASE: usize = 3;
/// lineitem: U32 codes of l_partkey.
pub const LI_PARTKEY_CODES: usize = 6;
/// lineitem: I64 block bases of l_partkey.
pub const LI_PARTKEY_BASE: usize = 7;
/// lineitem: U32 codes of l_suppkey.
pub const LI_SUPPKEY_CODES: usize = 8;
/// lineitem: I64 block bases of l_suppkey.
pub const LI_SUPPKEY_BASE: usize = 9;
/// lineitem: U16 codes of l_quantity (coefficients of scale 2).
pub const LI_QUANTITY_CODES: usize = 12;
/// lineitem: I64 block bases of l_quantity.
pub const LI_QUANTITY_BASE: usize = 13;
/// lineitem: U16 codes of l_shipdate (days since 2000-01-01).
pub const LI_SHIPDATE_CODES: usize = 28;
/// lineitem: I64 block bases of l_shipdate.
pub const LI_SHIPDATE_BASE: usize = 29;
/// Number of inherited parts (storage facts).
pub const FACTS_PARTS: usize = 75;
/// Index header: I64 `[mode, kmin, dbase]`.
pub const IDX_META: usize = 75;
/// Directory offsets: U32, `nkeys + 1` index positions.
pub const IDX_OFFS: usize = 76;
/// Index rows: U32, the stored row at each index position.
pub const IDX_ROWS: usize = 77;
/// Index date keys: U16, `l_shipdate - dbase` at each index position.
pub const IDX_DATES: usize = 78;
/// Number of parts of storage li_pkdate.
pub const LI_PKDATE_PARTS: usize = 79;
/// The mode of a present index.
pub const MODE_INDEX: i64 = 1;

// ------------------------------------------------------------------------------------------------ part views

pub open spec fn u16s(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

pub open spec fn u32s(p: PartView) -> Seq<u32> {
    match p {
        PartView::U32(s) => s,
        _ => Seq::empty(),
    }
}

pub open spec fn u64s(p: PartView) -> Seq<u64> {
    match p {
        PartView::U64(s) => s,
        _ => Seq::empty(),
    }
}

pub open spec fn i64s(p: PartView) -> Seq<i64> {
    match p {
        PartView::I64(s) => s,
        _ => Seq::empty(),
    }
}

// ------------------------------------------------------------------------------------------------ lineitem values

/// Number of lineitem rows.
pub open spec fn n_rows(parts: Seq<PartView>) -> int {
    u64s(parts[LI_LAYOUT as int])[0] as int
}

/// Rows per block of every frame-of-reference column.
pub open spec fn bsize(parts: Seq<PartView>) -> int {
    u64s(parts[LI_LAYOUT as int])[1] as int
}

/// Canonical row of stored row `s`.
pub open spec fn map_at(parts: Seq<PartView>, s: int) -> int {
    u64s(parts[LI_PERM_BASE as int])[s / bsize(parts)] + u32s(parts[LI_PERM_CODES as int])[s]
}

/// l_partkey of stored row `s`.
pub open spec fn key_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_PARTKEY_BASE as int])[s / bsize(parts)] + u32s(parts[LI_PARTKEY_CODES as int])[s]
}

/// l_suppkey of stored row `s`.
pub open spec fn supp_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_SUPPKEY_BASE as int])[s / bsize(parts)] + u32s(parts[LI_SUPPKEY_CODES as int])[s]
}

/// l_quantity coefficient (scale 2) of stored row `s`.
pub open spec fn qty_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_QUANTITY_BASE as int])[s / bsize(parts)] + u16s(parts[LI_QUANTITY_CODES as int])[s]
}

/// l_shipdate (days since 2000-01-01) of stored row `s`.
pub open spec fn date_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_SHIPDATE_BASE as int])[s / bsize(parts)] + u16s(parts[LI_SHIPDATE_CODES as int])[s]
}

/// A frame-of-reference column over `n` rows: one code per row, bases covering every block.
pub open spec fn for_len_ok(codes: int, bases: int, n: int, bs: int) -> bool {
    codes == n && bases * bs >= n
}

/// The layout and the column parts this interface reads.
pub open spec fn li_shape(parts: Seq<PartView>, n: int) -> bool {
    let bs = bsize(parts);
    &&& parts.len() == LI_PKDATE_PARTS
    &&& parts[LI_LAYOUT as int] is U64 && u64s(parts[LI_LAYOUT as int]).len() == 2
    &&& n_rows(parts) == n
    &&& bs >= 1
    &&& parts[LI_PERM_CODES as int] is U32 && parts[LI_PERM_BASE as int] is U64
    &&& for_len_ok(u32s(parts[LI_PERM_CODES as int]).len() as int, u64s(parts[LI_PERM_BASE as int]).len() as int, n, bs)
    &&& parts[LI_PARTKEY_CODES as int] is U32 && parts[LI_PARTKEY_BASE as int] is I64
    &&& for_len_ok(u32s(parts[LI_PARTKEY_CODES as int]).len() as int, i64s(parts[LI_PARTKEY_BASE as int]).len() as int, n, bs)
    &&& parts[LI_SUPPKEY_CODES as int] is U32 && parts[LI_SUPPKEY_BASE as int] is I64
    &&& for_len_ok(u32s(parts[LI_SUPPKEY_CODES as int]).len() as int, i64s(parts[LI_SUPPKEY_BASE as int]).len() as int, n, bs)
    &&& parts[LI_QUANTITY_CODES as int] is U16 && parts[LI_QUANTITY_BASE as int] is I64
    &&& for_len_ok(u16s(parts[LI_QUANTITY_CODES as int]).len() as int, i64s(parts[LI_QUANTITY_BASE as int]).len() as int, n, bs)
    &&& parts[LI_SHIPDATE_CODES as int] is U16 && parts[LI_SHIPDATE_BASE as int] is I64
    &&& for_len_ok(u16s(parts[LI_SHIPDATE_CODES as int]).len() as int, i64s(parts[LI_SHIPDATE_BASE as int]).len() as int, n, bs)
}

/// Canonical row `r` is the image of some stored row.
pub open spec fn mapped(parts: Seq<PartView>, n: int, r: int) -> bool {
    exists|s: int| 0 <= s < n && #[trigger] map_at(parts, s) == r
}

/// The row map is a bijection of `[0, n)`.
pub open spec fn row_map_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& forall|s: int| 0 <= s < n ==> 0 <= #[trigger] map_at(parts, s) < n
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] map_at(parts, a) != #[trigger] map_at(parts, b)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] mapped(parts, n, r)
}

/// A stored relation row `[l_partkey, l_suppkey, l_quantity, l_shipdate]`.
pub open spec fn li_row(k: int, su: int, q: int, d: int) -> Row {
    seq![Val::Int(k), Val::Int(su), Val::Num { coeff: q, scale: 2 }, Val::Date(d)]
}

/// Canonical row `map_at(s)` holds the values of stored row `s`.
pub open spec fn rows_ok(parts: Seq<PartView>, rel: Seq<Row>) -> bool {
    forall|s: int| 0 <= s < rel.len() ==>
        rel[#[trigger] map_at(parts, s)] == li_row(key_at(parts, s), supp_at(parts, s), qty_at(parts, s), date_at(parts, s))
}

// ------------------------------------------------------------------------------------------------ the index

/// Index header `[mode, kmin, dbase]`.
pub open spec fn idx_meta(parts: Seq<PartView>) -> Seq<i64> {
    i64s(parts[IDX_META as int])
}

/// Directory offsets.
pub open spec fn idx_offs(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[IDX_OFFS as int])
}

/// Index rows.
pub open spec fn idx_rows(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[IDX_ROWS as int])
}

/// Index date codes.
pub open spec fn idx_dates(parts: Seq<PartView>) -> Seq<u16> {
    u16s(parts[IDX_DATES as int])
}

/// The index is present.
pub open spec fn has_idx(parts: Seq<PartView>) -> bool {
    idx_meta(parts)[0] == MODE_INDEX
}

/// First key of the directory's range.
pub open spec fn idx_kmin(parts: Seq<PartView>) -> int {
    idx_meta(parts)[1] as int
}

/// Base day of the date keys.
pub open spec fn idx_dbase(parts: Seq<PartView>) -> int {
    idx_meta(parts)[2] as int
}

/// Number of keys of the directory's range.
pub open spec fn idx_nkeys(parts: Seq<PartView>) -> int {
    idx_offs(parts).len() - 1
}

/// Stored row at index position `p`.
pub open spec fn irow(parts: Seq<PartView>, p: int) -> int {
    idx_rows(parts)[p] as int
}

/// Index position `p` lies in the directory entry of its row's key.
pub open spec fn in_entry(parts: Seq<PartView>, p: int) -> bool {
    let e = key_at(parts, irow(parts, p)) - idx_kmin(parts);
    &&& 0 <= e < idx_nkeys(parts)
    &&& idx_offs(parts)[e] <= p < idx_offs(parts)[e + 1]
}

/// Stored row `s` is at some index position.
pub open spec fn indexed(parts: Seq<PartView>, n: int, s: int) -> bool {
    exists|p: int| 0 <= p < n && #[trigger] irow(parts, p) == s
}

/// The date key at position `p` is the row's l_shipdate.
pub open spec fn date_key_ok(parts: Seq<PartView>, p: int) -> bool {
    idx_dbase(parts) + idx_dates(parts)[p] == date_at(parts, irow(parts, p))
}

/// Date keys do not decrease from position `p` to `p + 1` within one key.
pub open spec fn date_sorted_at(parts: Seq<PartView>, p: int) -> bool {
    key_at(parts, irow(parts, p)) == key_at(parts, irow(parts, p + 1)) ==> idx_dates(parts)[p] <= idx_dates(parts)[p + 1]
}

/// The index over the `n` stored rows.
pub open spec fn idx_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts[IDX_META as int] is I64 && idx_meta(parts).len() == 3
    &&& parts[IDX_OFFS as int] is U32
    &&& parts[IDX_ROWS as int] is U32
    &&& parts[IDX_DATES as int] is U16
    &&& has_idx(parts) ==> {
        &&& idx_offs(parts).len() >= 1
        &&& idx_offs(parts)[idx_nkeys(parts)] <= n
        &&& forall|e: int| 0 <= e < idx_nkeys(parts) ==> #[trigger] idx_offs(parts)[e] <= idx_offs(parts)[e + 1]
        &&& idx_rows(parts).len() == n
        &&& idx_dates(parts).len() == n
        &&& forall|p: int| 0 <= p < n ==> 0 <= #[trigger] irow(parts, p) < n
        &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] irow(parts, a) != #[trigger] irow(parts, b)
        &&& forall|s: int| 0 <= s < n ==> #[trigger] indexed(parts, n, s)
        &&& forall|p: int| 0 <= p < n ==> #[trigger] in_entry(parts, p)
        &&& forall|p: int| 0 <= p < n ==> #[trigger] date_key_ok(parts, p)
        &&& forall|p: int| 0 <= p < n - 1 ==> #[trigger] date_sorted_at(parts, p)
    }
}

// ------------------------------------------------------------------------------------------------ represents

/// The inherited parts hold lineitem's `[l_partkey, l_suppkey, l_quantity, l_shipdate]` under the row map; the new
/// parts are the composite index.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& rels.len() == 1
    &&& li_shape(parts, rels[0].len() as int)
    &&& row_map_ok(parts, rels[0].len() as int)
    &&& rows_ok(parts, rels[0])
    &&& idx_ok(parts, rels[0].len() as int)
}

/// The parts determine the relation: every canonical row is the image of a stored row whose values are stored.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    let n = a[0].len() as int;
    assert(b[0].len() == n);
    assert forall|r: int| 0 <= r < n implies a[0][r] == b[0][r] by {
        assert(mapped(parts, n, r));
        let s = choose|s: int| 0 <= s < n && #[trigger] map_at(parts, s) == r;
        assert(a[0][map_at(parts, s)] == b[0][map_at(parts, s)]);
    }
    assert(a[0] =~= b[0]);
    assert(a =~= b);
}

/// Offsets are nondecreasing over any span of entries.
pub proof fn lemma_offs_mono(parts: Seq<PartView>, n: int, a: int, b: int)
    requires
        idx_ok(parts, n),
        has_idx(parts),
        0 <= a <= b <= idx_nkeys(parts),
    ensures
        idx_offs(parts)[a] <= idx_offs(parts)[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(parts, n, a, b - 1);
        assert(idx_offs(parts)[b - 1] <= idx_offs(parts)[b]);
    }
}

/// The positions of entry `e` are exactly the positions whose stored row has key `kmin + e`.
pub proof fn lemma_entry_exact(parts: Seq<PartView>, n: int, e: int, p: int)
    requires
        idx_ok(parts, n),
        has_idx(parts),
        0 <= e < idx_nkeys(parts),
        0 <= p < n,
    ensures
        (idx_offs(parts)[e] <= p < idx_offs(parts)[e + 1]) <==> key_at(parts, irow(parts, p)) == idx_kmin(parts) + e,
        idx_offs(parts)[e] <= idx_offs(parts)[e + 1] <= n,
{
    assert(in_entry(parts, p));
    let f = key_at(parts, irow(parts, p)) - idx_kmin(parts);
    lemma_offs_mono(parts, n, e + 1, idx_nkeys(parts));
    if idx_offs(parts)[e] <= p < idx_offs(parts)[e + 1] && f != e {
        if f < e {
            lemma_offs_mono(parts, n, f + 1, e);
        } else {
            lemma_offs_mono(parts, n, e + 1, f);
        }
    }
}

/// A key outside the directory's range has no row.
pub proof fn lemma_outside_none(parts: Seq<PartView>, n: int, k: int, p: int)
    requires
        idx_ok(parts, n),
        has_idx(parts),
        !(idx_kmin(parts) <= k < idx_kmin(parts) + idx_nkeys(parts)),
        0 <= p < n,
    ensures
        key_at(parts, irow(parts, p)) != k,
{
    assert(in_entry(parts, p));
}

/// Within one entry, the date keys never decrease between any two positions.
pub proof fn lemma_dates_sorted(parts: Seq<PartView>, n: int, e: int, a: int, b: int)
    requires
        idx_ok(parts, n),
        has_idx(parts),
        0 <= e < idx_nkeys(parts),
        idx_offs(parts)[e] <= a <= b < idx_offs(parts)[e + 1],
    ensures
        idx_dates(parts)[a] <= idx_dates(parts)[b],
    decreases b - a,
{
    lemma_offs_mono(parts, n, e + 1, idx_nkeys(parts));
    if a < b {
        lemma_dates_sorted(parts, n, e, a, b - 1);
        lemma_entry_exact(parts, n, e, b - 1);
        lemma_entry_exact(parts, n, e, b);
        assert(date_sorted_at(parts, b - 1));
    }
}

} // verus!
