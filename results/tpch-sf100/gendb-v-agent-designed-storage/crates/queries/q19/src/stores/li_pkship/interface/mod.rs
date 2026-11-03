//! Storage `li_pkship`: storage `facts` unchanged (its 75 parts, inherited), followed by a composite index of
//! lineitem on `(l_partkey, l_shipinstruct, l_shipmode)`.
//!
//! What this interface states about the inherited parts (the stored relation is lineitem projected on
//! `[l_partkey, l_quantity, l_extendedprice, l_discount, l_shipinstruct, l_shipmode]`, canonical row order):
//! - part `LI_LAYOUT` is U64 `[n, bsize]` (`bsize >= 1` rows per block);
//! - every numeric/integer column below is frame-of-reference coded over blocks of `bsize` rows: the value of stored
//!   row `s` is `base[s / bsize] + code[s]` (I64 bases; U32, U16 or U8 codes; the row map has U64 bases);
//! - l_shipinstruct and l_shipmode are dictionary coded: the entry index of stored row `s` is
//!   `base[s / bsize] + code[s]` (U64 bases, U8 codes), inside the dictionary (U64 offsets + U8 bytes; entry `i` is
//!   `bytes[offs[i] .. offs[i + 1]]`);
//! - the row map (`LI_PERM_*`): stored row `s` is canonical row `map_at(s)`, a bijection of `[0, n)`;
//! - canonical row `map_at(s)` is `[Int(key), Num(qty, 2), Num(price, 2), Num(disc, 2), Text(si), Text(sm)]` of
//!   stored row `s`.
//!
//! The new parts:
//! - `IDX_META` (I64 `[mode, kmin]`): mode `MODE_INDEX` (1) when the index is present;
//! - `IDX_OFFS` (U32, `nkeys + 1` nondecreasing offsets at most `n`): a dense directory over the l_partkey keys
//!   `kmin .. kmin + nkeys`;
//! - `IDX_ROWS` (U32, `n`): index position `p` holds stored row `irow(p)`, a bijection of `[0, n)`; every position lies
//!   in the directory entry of its row's l_partkey (`in_entry`), so entry `e` (positions `offs[e] .. offs[e + 1]`)
//!   holds exactly the stored rows of key `kmin + e` (`lemma_entry_exact`) and a key outside the range has no row;
//! - `IDX_SHIP` (U8, `n`): the second key of position `p`, `16 * si + sm` with `si`, `sm` the l_shipinstruct and
//!   l_shipmode dictionary indices of `irow(p)` (both below 16 when the index is present), nondecreasing along each
//!   entry.
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
/// lineitem: U16 codes of l_quantity (coefficients of scale 2).
pub const LI_QUANTITY_CODES: usize = 12;
/// lineitem: I64 block bases of l_quantity.
pub const LI_QUANTITY_BASE: usize = 13;
/// lineitem: U32 codes of l_extendedprice (coefficients of scale 2).
pub const LI_PRICE_CODES: usize = 14;
/// lineitem: I64 block bases of l_extendedprice.
pub const LI_PRICE_BASE: usize = 15;
/// lineitem: U8 codes of l_discount (coefficients of scale 2).
pub const LI_DISCOUNT_CODES: usize = 16;
/// lineitem: I64 block bases of l_discount.
pub const LI_DISCOUNT_BASE: usize = 17;
/// lineitem: U8 codes of l_shipinstruct dictionary indices.
pub const LI_SI_CODES: usize = 37;
/// lineitem: U64 block bases of l_shipinstruct dictionary indices.
pub const LI_SI_BASE: usize = 38;
/// lineitem: U64 offsets of the l_shipinstruct dictionary.
pub const LI_SI_DOFFS: usize = 39;
/// lineitem: U8 bytes of the l_shipinstruct dictionary.
pub const LI_SI_DBYTES: usize = 40;
/// lineitem: U8 codes of l_shipmode dictionary indices.
pub const LI_SM_CODES: usize = 41;
/// lineitem: U64 block bases of l_shipmode dictionary indices.
pub const LI_SM_BASE: usize = 42;
/// lineitem: U64 offsets of the l_shipmode dictionary.
pub const LI_SM_DOFFS: usize = 43;
/// lineitem: U8 bytes of the l_shipmode dictionary.
pub const LI_SM_DBYTES: usize = 44;
/// Number of inherited parts (storage facts).
pub const FACTS_PARTS: usize = 75;
/// Index header: I64 `[mode, kmin]`.
pub const IDX_META: usize = 75;
/// Directory offsets: U32, `nkeys + 1` index positions.
pub const IDX_OFFS: usize = 76;
/// Index rows: U32, the stored row at each index position.
pub const IDX_ROWS: usize = 77;
/// Index ship keys: U8, `16 * si + sm` at each index position.
pub const IDX_SHIP: usize = 78;
/// Number of parts of storage li_pkship.
pub const LI_PKSHIP_PARTS: usize = 79;
/// The mode of a present index.
pub const MODE_INDEX: i64 = 1;

// ------------------------------------------------------------------------------------------------ part views

pub open spec fn u8s(p: PartView) -> Seq<u8> {
    match p {
        PartView::U8(s) => s,
        _ => Seq::empty(),
    }
}

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

/// l_quantity coefficient (scale 2) of stored row `s`.
pub open spec fn qty_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_QUANTITY_BASE as int])[s / bsize(parts)] + u16s(parts[LI_QUANTITY_CODES as int])[s]
}

/// l_extendedprice coefficient (scale 2) of stored row `s`.
pub open spec fn price_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_PRICE_BASE as int])[s / bsize(parts)] + u32s(parts[LI_PRICE_CODES as int])[s]
}

/// l_discount coefficient (scale 2) of stored row `s`.
pub open spec fn disc_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_DISCOUNT_BASE as int])[s / bsize(parts)] + u8s(parts[LI_DISCOUNT_CODES as int])[s]
}

/// l_shipinstruct dictionary index of stored row `s`.
pub open spec fn si_at(parts: Seq<PartView>, s: int) -> int {
    u64s(parts[LI_SI_BASE as int])[s / bsize(parts)] + u8s(parts[LI_SI_CODES as int])[s]
}

/// l_shipmode dictionary index of stored row `s`.
pub open spec fn sm_at(parts: Seq<PartView>, s: int) -> int {
    u64s(parts[LI_SM_BASE as int])[s / bsize(parts)] + u8s(parts[LI_SM_CODES as int])[s]
}

/// Entry `i` of a dictionary: `bytes[offs[i] .. offs[i + 1]]`.
pub open spec fn dict_text(offs: Seq<u64>, bytes: Seq<u8>, i: int) -> Seq<u8> {
    bytes.subrange(offs[i] as int, offs[i + 1] as int)
}

/// Entry `i` of a dictionary is a byte range inside its bytes.
pub open spec fn dict_range_ok(offs: Seq<u64>, bytes: Seq<u8>, i: int) -> bool {
    offs[i] <= offs[i + 1] && offs[i + 1] <= bytes.len()
}

/// A dictionary of `offs.len() - 1 >= 0` entries, each a byte range of `bytes`.
pub open spec fn dict_ok(offs: Seq<u64>, bytes: Seq<u8>) -> bool {
    &&& offs.len() >= 1
    &&& forall|i: int| 0 <= i < offs.len() - 1 ==> #[trigger] dict_range_ok(offs, bytes, i)
}

/// The l_shipinstruct dictionary offsets and bytes.
pub open spec fn si_offs(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[LI_SI_DOFFS as int])
}

pub open spec fn si_bytes(parts: Seq<PartView>) -> Seq<u8> {
    u8s(parts[LI_SI_DBYTES as int])
}

/// The l_shipmode dictionary offsets and bytes.
pub open spec fn sm_offs(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[LI_SM_DOFFS as int])
}

pub open spec fn sm_bytes(parts: Seq<PartView>) -> Seq<u8> {
    u8s(parts[LI_SM_DBYTES as int])
}

/// l_shipinstruct entry `i`.
pub open spec fn si_text(parts: Seq<PartView>, i: int) -> Seq<u8> {
    dict_text(si_offs(parts), si_bytes(parts), i)
}

/// l_shipmode entry `i`.
pub open spec fn sm_text(parts: Seq<PartView>, i: int) -> Seq<u8> {
    dict_text(sm_offs(parts), sm_bytes(parts), i)
}

/// A frame-of-reference column over `n` rows: one code per row, bases covering every block.
pub open spec fn for_len_ok(codes: int, bases: int, n: int, bs: int) -> bool {
    codes == n && bases * bs >= n
}

/// The layout and the column parts this interface reads.
pub open spec fn li_shape(parts: Seq<PartView>, n: int) -> bool {
    let bs = bsize(parts);
    &&& parts.len() == LI_PKSHIP_PARTS
    &&& parts[LI_LAYOUT as int] is U64 && u64s(parts[LI_LAYOUT as int]).len() == 2
    &&& n_rows(parts) == n
    &&& bs >= 1
    &&& parts[LI_PERM_CODES as int] is U32 && parts[LI_PERM_BASE as int] is U64
    &&& for_len_ok(u32s(parts[LI_PERM_CODES as int]).len() as int, u64s(parts[LI_PERM_BASE as int]).len() as int, n, bs)
    &&& parts[LI_PARTKEY_CODES as int] is U32 && parts[LI_PARTKEY_BASE as int] is I64
    &&& for_len_ok(u32s(parts[LI_PARTKEY_CODES as int]).len() as int, i64s(parts[LI_PARTKEY_BASE as int]).len() as int, n, bs)
    &&& parts[LI_QUANTITY_CODES as int] is U16 && parts[LI_QUANTITY_BASE as int] is I64
    &&& for_len_ok(u16s(parts[LI_QUANTITY_CODES as int]).len() as int, i64s(parts[LI_QUANTITY_BASE as int]).len() as int, n, bs)
    &&& parts[LI_PRICE_CODES as int] is U32 && parts[LI_PRICE_BASE as int] is I64
    &&& for_len_ok(u32s(parts[LI_PRICE_CODES as int]).len() as int, i64s(parts[LI_PRICE_BASE as int]).len() as int, n, bs)
    &&& parts[LI_DISCOUNT_CODES as int] is U8 && parts[LI_DISCOUNT_BASE as int] is I64
    &&& for_len_ok(u8s(parts[LI_DISCOUNT_CODES as int]).len() as int, i64s(parts[LI_DISCOUNT_BASE as int]).len() as int, n, bs)
    &&& parts[LI_SI_CODES as int] is U8 && parts[LI_SI_BASE as int] is U64
    &&& for_len_ok(u8s(parts[LI_SI_CODES as int]).len() as int, u64s(parts[LI_SI_BASE as int]).len() as int, n, bs)
    &&& parts[LI_SM_CODES as int] is U8 && parts[LI_SM_BASE as int] is U64
    &&& for_len_ok(u8s(parts[LI_SM_CODES as int]).len() as int, u64s(parts[LI_SM_BASE as int]).len() as int, n, bs)
    &&& parts[LI_SI_DOFFS as int] is U64 && parts[LI_SI_DBYTES as int] is U8
    &&& dict_ok(si_offs(parts), si_bytes(parts))
    &&& parts[LI_SM_DOFFS as int] is U64 && parts[LI_SM_DBYTES as int] is U8
    &&& dict_ok(sm_offs(parts), sm_bytes(parts))
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

/// A stored relation row `[l_partkey, l_quantity, l_extendedprice, l_discount, l_shipinstruct, l_shipmode]`.
pub open spec fn li_row(k: int, q: int, pr: int, d: int, si: Seq<u8>, sm: Seq<u8>) -> Row {
    seq![Val::Int(k), Val::Num { coeff: q, scale: 2 }, Val::Num { coeff: pr, scale: 2 }, Val::Num { coeff: d, scale: 2 },
        Val::Text(si), Val::Text(sm)]
}

/// The relation row of stored row `s`.
pub open spec fn row_at(parts: Seq<PartView>, s: int) -> Row {
    li_row(key_at(parts, s), qty_at(parts, s), price_at(parts, s), disc_at(parts, s),
        si_text(parts, si_at(parts, s)), sm_text(parts, sm_at(parts, s)))
}

/// Stored row `s`'s dictionary indices lie inside their dictionaries.
pub open spec fn dict_idx_ok(parts: Seq<PartView>, s: int) -> bool {
    &&& 0 <= si_at(parts, s) < si_offs(parts).len() - 1
    &&& 0 <= sm_at(parts, s) < sm_offs(parts).len() - 1
}

/// Canonical row `map_at(s)` holds the values of stored row `s`.
pub open spec fn rows_ok(parts: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& forall|s: int| 0 <= s < rel.len() ==> rel[#[trigger] map_at(parts, s)] == row_at(parts, s)
    &&& forall|s: int| 0 <= s < rel.len() ==> #[trigger] dict_idx_ok(parts, s)
}

// ------------------------------------------------------------------------------------------------ the index

/// Index header `[mode, kmin]`.
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

/// Index ship keys.
pub open spec fn idx_ship(parts: Seq<PartView>) -> Seq<u8> {
    u8s(parts[IDX_SHIP as int])
}

/// The index is present.
pub open spec fn has_idx(parts: Seq<PartView>) -> bool {
    idx_meta(parts)[0] == MODE_INDEX
}

/// First key of the directory's range.
pub open spec fn idx_kmin(parts: Seq<PartView>) -> int {
    idx_meta(parts)[1] as int
}

/// Number of keys of the directory's range.
pub open spec fn idx_nkeys(parts: Seq<PartView>) -> int {
    idx_offs(parts).len() - 1
}

/// Stored row at index position `p`.
pub open spec fn irow(parts: Seq<PartView>, p: int) -> int {
    idx_rows(parts)[p] as int
}

/// The ship key of stored row `s`: `16 * si + sm`.
pub open spec fn ship_of(parts: Seq<PartView>, s: int) -> int {
    16 * si_at(parts, s) + sm_at(parts, s)
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

/// The ship key at position `p` is its row's, with both dictionary indices below 16.
pub open spec fn ship_key_ok(parts: Seq<PartView>, p: int) -> bool {
    &&& idx_ship(parts)[p] == ship_of(parts, irow(parts, p))
    &&& 0 <= si_at(parts, irow(parts, p)) < 16
    &&& 0 <= sm_at(parts, irow(parts, p)) < 16
}

/// Ship keys do not decrease from position `p` to `p + 1` within one l_partkey.
pub open spec fn ship_sorted_at(parts: Seq<PartView>, p: int) -> bool {
    key_at(parts, irow(parts, p)) == key_at(parts, irow(parts, p + 1)) ==> idx_ship(parts)[p] <= idx_ship(parts)[p + 1]
}

/// The index over the `n` stored rows.
pub open spec fn idx_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts[IDX_META as int] is I64 && idx_meta(parts).len() == 2
    &&& parts[IDX_OFFS as int] is U32
    &&& parts[IDX_ROWS as int] is U32
    &&& parts[IDX_SHIP as int] is U8
    &&& has_idx(parts) ==> {
        &&& idx_offs(parts).len() >= 1
        &&& idx_offs(parts)[idx_nkeys(parts)] <= n
        &&& forall|e: int| 0 <= e < idx_nkeys(parts) ==> #[trigger] idx_offs(parts)[e] <= idx_offs(parts)[e + 1]
        &&& idx_rows(parts).len() == n
        &&& idx_ship(parts).len() == n
        &&& forall|p: int| 0 <= p < n ==> 0 <= #[trigger] irow(parts, p) < n
        &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] irow(parts, a) != #[trigger] irow(parts, b)
        &&& forall|s: int| 0 <= s < n ==> #[trigger] indexed(parts, n, s)
        &&& forall|p: int| 0 <= p < n ==> #[trigger] in_entry(parts, p)
        &&& forall|p: int| 0 <= p < n ==> #[trigger] ship_key_ok(parts, p)
        &&& forall|p: int| 0 <= p < n - 1 ==> #[trigger] ship_sorted_at(parts, p)
    }
}

// ------------------------------------------------------------------------------------------------ represents

/// The inherited parts hold lineitem's `[l_partkey, l_quantity, l_extendedprice, l_discount, l_shipinstruct,
/// l_shipmode]` under the row map; the new parts are the composite index.
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

} // verus!
