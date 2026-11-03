//! Storage `li_partdir`: storage `facts` unchanged (its 75 parts, inherited), followed by a dense directory over the
//! l_partkey key index of facts.
//!
//! What this interface states about the inherited parts (only what lineitem lookups by l_partkey need; the stored
//! relation is lineitem projected on `[l_partkey, l_quantity, l_extendedprice]`, canonical row order):
//! - part `LI_LAYOUT` is U64 `[n, bsize]` (`bsize >= 1` rows per block);
//! - every column below is frame-of-reference coded over blocks of `bsize` rows: the value of stored row `s` is
//!   `base[s / bsize] + code[s]` (U64 or I64 bases, U16 or U32 codes);
//! - the row map column (`LI_PERM_*`): stored row `s` is canonical row `map_at(s)`, a bijection of `[0, n)`;
//! - the stored rows' values: canonical row `map_at(s)` is `[Int(key_at(s)), Num(qty_at(s), 2), Num(price_at(s), 2)]`
//!   (numeric coefficients of scale 2).
//!
//! The new parts:
//! - `DIR_META` (I64 `[mode, kmin]`): mode `MODE_DIRECTORY` (1) when the directory is present;
//! - `DIR_OFFS` (U32, `nkeys + 1` offsets). In directory mode the key index of facts (`LI_KEYIDX_*`: index position
//!   `p` holds stored row `irow(p)`, a bijection of `[0, n)`) puts every position `p` in the entry of its key:
//!   `e = key_at(irow(p)) - kmin` lies in `[0, nkeys)` and `offs[e] <= p < offs[e + 1]`; offsets are nondecreasing and
//!   at most `n`. So positions `offs[k - kmin] .. offs[k - kmin + 1]` hold exactly the stored rows of key `k`
//!   (`lemma_entry_exact`), and a key outside `[kmin, kmin + nkeys)` has no row.
//! Every new value is a row position or the first key of the directory's range: no column value is stored.
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
pub const LI_EXTENDEDPRICE_CODES: usize = 14;
/// lineitem: I64 block bases of l_extendedprice.
pub const LI_EXTENDEDPRICE_BASE: usize = 15;
/// lineitem: U32 codes of the stored row at each position of the l_partkey key index.
pub const LI_KEYIDX_CODES: usize = 45;
/// lineitem: U64 block bases of the l_partkey key index.
pub const LI_KEYIDX_BASE: usize = 46;
/// Number of inherited parts (storage facts).
pub const FACTS_PARTS: usize = 75;
/// Directory header: I64 `[mode, kmin]`.
pub const DIR_META: usize = 75;
/// Directory offsets: U32, `nkeys + 1` positions of the key index.
pub const DIR_OFFS: usize = 76;
/// Number of parts of storage li_partdir.
pub const LI_PARTDIR_PARTS: usize = 77;
/// The mode of a present directory.
pub const MODE_DIRECTORY: i64 = 1;

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

/// l_quantity coefficient (scale 2) of stored row `s`.
pub open spec fn qty_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_QUANTITY_BASE as int])[s / bsize(parts)] + u16s(parts[LI_QUANTITY_CODES as int])[s]
}

/// l_extendedprice coefficient (scale 2) of stored row `s`.
pub open spec fn price_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_EXTENDEDPRICE_BASE as int])[s / bsize(parts)] + u32s(parts[LI_EXTENDEDPRICE_CODES as int])[s]
}

/// Stored row at position `p` of the l_partkey key index.
pub open spec fn irow(parts: Seq<PartView>, p: int) -> int {
    u64s(parts[LI_KEYIDX_BASE as int])[p / bsize(parts)] + u32s(parts[LI_KEYIDX_CODES as int])[p]
}

/// A frame-of-reference column over `n` rows: one code per row, bases covering every block.
pub open spec fn for_len_ok(codes: int, bases: int, n: int, bs: int) -> bool {
    codes == n && bases * bs >= n
}

/// The layout and the column parts this interface reads.
pub open spec fn li_shape(parts: Seq<PartView>, n: int) -> bool {
    let bs = bsize(parts);
    &&& parts.len() == LI_PARTDIR_PARTS
    &&& parts[LI_LAYOUT as int] is U64 && u64s(parts[LI_LAYOUT as int]).len() == 2
    &&& n_rows(parts) == n
    &&& bs >= 1
    &&& parts[LI_PERM_CODES as int] is U32 && parts[LI_PERM_BASE as int] is U64
    &&& for_len_ok(u32s(parts[LI_PERM_CODES as int]).len() as int, u64s(parts[LI_PERM_BASE as int]).len() as int, n, bs)
    &&& parts[LI_PARTKEY_CODES as int] is U32 && parts[LI_PARTKEY_BASE as int] is I64
    &&& for_len_ok(u32s(parts[LI_PARTKEY_CODES as int]).len() as int, i64s(parts[LI_PARTKEY_BASE as int]).len() as int, n, bs)
    &&& parts[LI_QUANTITY_CODES as int] is U16 && parts[LI_QUANTITY_BASE as int] is I64
    &&& for_len_ok(u16s(parts[LI_QUANTITY_CODES as int]).len() as int, i64s(parts[LI_QUANTITY_BASE as int]).len() as int, n, bs)
    &&& parts[LI_EXTENDEDPRICE_CODES as int] is U32 && parts[LI_EXTENDEDPRICE_BASE as int] is I64
    &&& for_len_ok(u32s(parts[LI_EXTENDEDPRICE_CODES as int]).len() as int,
            i64s(parts[LI_EXTENDEDPRICE_BASE as int]).len() as int, n, bs)
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

/// A stored relation row `[l_partkey, l_quantity, l_extendedprice]`.
pub open spec fn li_row(k: int, q: int, x: int) -> Row {
    seq![Val::Int(k), Val::Num { coeff: q, scale: 2 }, Val::Num { coeff: x, scale: 2 }]
}

/// Canonical row `map_at(s)` holds the values of stored row `s`.
pub open spec fn rows_ok(parts: Seq<PartView>, rel: Seq<Row>) -> bool {
    forall|s: int| 0 <= s < rel.len() ==>
        rel[#[trigger] map_at(parts, s)] == li_row(key_at(parts, s), qty_at(parts, s), price_at(parts, s))
}

// ------------------------------------------------------------------------------------------------ the directory

/// Directory header `[mode, kmin]`.
pub open spec fn dir_meta(parts: Seq<PartView>) -> Seq<i64> {
    i64s(parts[DIR_META as int])
}

/// Directory offsets.
pub open spec fn dir_offs(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[DIR_OFFS as int])
}

/// The directory is present.
pub open spec fn has_dir(parts: Seq<PartView>) -> bool {
    dir_meta(parts)[0] == MODE_DIRECTORY
}

/// First key of the directory's range.
pub open spec fn dir_kmin(parts: Seq<PartView>) -> int {
    dir_meta(parts)[1] as int
}

/// Number of keys of the directory's range.
pub open spec fn dir_nkeys(parts: Seq<PartView>) -> int {
    dir_offs(parts).len() - 1
}

/// Index position `p` lies in the directory entry of its key.
pub open spec fn in_entry(parts: Seq<PartView>, p: int) -> bool {
    let e = key_at(parts, irow(parts, p)) - dir_kmin(parts);
    &&& 0 <= e < dir_nkeys(parts)
    &&& dir_offs(parts)[e] <= p < dir_offs(parts)[e + 1]
}

/// Stored row `s` is at some position of the key index.
pub open spec fn indexed(parts: Seq<PartView>, n: int, s: int) -> bool {
    exists|p: int| 0 <= p < n && #[trigger] irow(parts, p) == s
}

/// The directory over the `n` positions of the key index (`DIR_META`, `DIR_OFFS`).
pub open spec fn dir_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts[DIR_META as int] is I64 && dir_meta(parts).len() == 2
    &&& parts[DIR_OFFS as int] is U32
    &&& has_dir(parts) ==> {
        &&& dir_offs(parts).len() >= 1
        &&& dir_offs(parts)[dir_nkeys(parts)] <= n
        &&& forall|e: int| 0 <= e < dir_nkeys(parts) ==> #[trigger] dir_offs(parts)[e] <= dir_offs(parts)[e + 1]
        &&& parts[LI_KEYIDX_CODES as int] is U32 && parts[LI_KEYIDX_BASE as int] is U64
        &&& for_len_ok(u32s(parts[LI_KEYIDX_CODES as int]).len() as int, u64s(parts[LI_KEYIDX_BASE as int]).len() as int,
                n, bsize(parts))
        &&& forall|p: int| 0 <= p < n ==> 0 <= #[trigger] irow(parts, p) < n
        &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] irow(parts, a) != #[trigger] irow(parts, b)
        &&& forall|s: int| 0 <= s < n ==> #[trigger] indexed(parts, n, s)
        &&& forall|p: int| 0 <= p < n ==> #[trigger] in_entry(parts, p)
    }
}

// ------------------------------------------------------------------------------------------------ represents

/// The inherited parts hold lineitem's `[l_partkey, l_quantity, l_extendedprice]` under the row map; the new parts
/// are the directory.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& rels.len() == 1
    &&& li_shape(parts, rels[0].len() as int)
    &&& row_map_ok(parts, rels[0].len() as int)
    &&& rows_ok(parts, rels[0])
    &&& dir_ok(parts, rels[0].len() as int)
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
        dir_ok(parts, n),
        has_dir(parts),
        0 <= a <= b <= dir_nkeys(parts),
    ensures
        dir_offs(parts)[a] <= dir_offs(parts)[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(parts, n, a, b - 1);
        assert(dir_offs(parts)[b - 1] <= dir_offs(parts)[b]);
    }
}

/// The positions of entry `e` are exactly the positions whose stored row has key `kmin + e`.
pub proof fn lemma_entry_exact(parts: Seq<PartView>, n: int, e: int, p: int)
    requires
        dir_ok(parts, n),
        has_dir(parts),
        0 <= e < dir_nkeys(parts),
        0 <= p < n,
    ensures
        (dir_offs(parts)[e] <= p < dir_offs(parts)[e + 1]) <==> key_at(parts, irow(parts, p)) == dir_kmin(parts) + e,
        dir_offs(parts)[e] <= dir_offs(parts)[e + 1] <= n,
{
    assert(in_entry(parts, p));
    let f = key_at(parts, irow(parts, p)) - dir_kmin(parts);
    lemma_offs_mono(parts, n, e + 1, dir_nkeys(parts));
    if dir_offs(parts)[e] <= p < dir_offs(parts)[e + 1] && f != e {
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
        dir_ok(parts, n),
        has_dir(parts),
        !(dir_kmin(parts) <= k < dir_kmin(parts) + dir_nkeys(parts)),
        0 <= p < n,
    ensures
        key_at(parts, irow(parts, p)) != k,
{
    assert(in_entry(parts, p));
}

} // verus!
