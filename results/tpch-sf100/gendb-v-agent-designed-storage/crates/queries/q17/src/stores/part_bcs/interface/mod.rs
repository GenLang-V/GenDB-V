//! Storage `part_bcs`: storage `custpart` unchanged (its 50 parts, inherited), followed by a composite index of part
//! on `(p_brand, p_container, p_size)`.
//!
//! What this interface states about the inherited parts (the stored relation is part projected on
//! `[p_partkey, p_brand, p_size, p_container]`, canonical row order: stored row `r` is canonical row `r`):
//! - part `PA_LAYOUT` is U64 `[n, bsize]` (`bsize >= 1` rows per block);
//! - p_partkey and p_size of row `r` are `base[r / bsize] + code[r]` (I64 bases; U32 and U8 codes);
//! - p_brand and p_container are dictionary coded: the entry index of row `r` is `base[r / bsize] + code[r]` (U64
//!   bases, U8 codes), inside its dictionary (U64 offsets + U8 bytes; entry `i` is `bytes[offs[i] .. offs[i + 1]]`).
//!
//! The new parts (`IDX_META` I64 `[mode, smin, ns]`, `IDX_OFFS` U32, `IDX_PERM` U32): in mode `MODE_INDEX` (1) every
//! p_size lies in `smin .. smin + ns`, and the composite key of row `r` is
//! `comp(r) = (brand index * nc + container index) * ns + (p_size - smin)` (`nc` the number of container entries), so
//! the keys of the `nb * nc * ns` entries enumerate (brand, container, size) in that order. `IDX_PERM` is a
//! bijection of the rows, and `IDX_OFFS` (`nb * nc * ns + 1` nondecreasing offsets) a dense directory over it: entry
//! `e` (positions `offs[e] .. offs[e + 1]`) holds exactly the rows whose composite key is `e`. So the rows of one
//! brand and container with p_size in an interval are one contiguous range of positions. Every new value is a row
//! position, an offset or a key bound of the index; no column value is stored.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};

verus! {

// ------------------------------------------------------------------------------------------------ part indices

/// part: U64 `[rows, block rows]` (custpart's `PART_FIRST + PA_LAYOUT`).
pub const PA_LAYOUT: usize = 21;
/// part: U32 codes of p_partkey.
pub const PA_PARTKEY_CODES: usize = 23;
/// part: I64 block bases of p_partkey.
pub const PA_PARTKEY_BASE: usize = 24;
/// part: U8 codes of p_brand dictionary indices.
pub const PA_BRAND_CODES: usize = 31;
/// part: U64 block bases of p_brand dictionary indices.
pub const PA_BRAND_BASE: usize = 32;
/// part: U64 offsets of the p_brand dictionary.
pub const PA_BRAND_DOFFS: usize = 33;
/// part: U8 bytes of the p_brand dictionary.
pub const PA_BRAND_DBYTES: usize = 34;
/// part: U8 codes of p_size.
pub const PA_SIZE_CODES: usize = 39;
/// part: I64 block bases of p_size.
pub const PA_SIZE_BASE: usize = 40;
/// part: U8 codes of p_container dictionary indices.
pub const PA_CONT_CODES: usize = 41;
/// part: U64 block bases of p_container dictionary indices.
pub const PA_CONT_BASE: usize = 42;
/// part: U64 offsets of the p_container dictionary.
pub const PA_CONT_DOFFS: usize = 43;
/// part: U8 bytes of the p_container dictionary.
pub const PA_CONT_DBYTES: usize = 44;
/// Number of inherited parts (storage custpart).
pub const CUSTPART_PARTS: usize = 50;
/// Index header: I64 `[mode, smin, ns]`.
pub const IDX_META: usize = 50;
/// Directory offsets: U32, `nb * nc * ns + 1` index positions.
pub const IDX_OFFS: usize = 51;
/// Index rows: U32, the part row at each index position.
pub const IDX_PERM: usize = 52;
/// Number of parts of storage part_bcs.
pub const PART_BCS_PARTS: usize = 53;
/// The mode of a present index.
pub const MODE_INDEX: i64 = 1;

// ------------------------------------------------------------------------------------------------ part views

pub open spec fn u8s(p: PartView) -> Seq<u8> {
    match p {
        PartView::U8(s) => s,
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

// ------------------------------------------------------------------------------------------------ part values

/// Number of part rows.
pub open spec fn n_rows(parts: Seq<PartView>) -> int {
    u64s(parts[PA_LAYOUT as int])[0] as int
}

/// Rows per block of every frame-of-reference column.
pub open spec fn bsize(parts: Seq<PartView>) -> int {
    u64s(parts[PA_LAYOUT as int])[1] as int
}

/// p_partkey of row `r`.
pub open spec fn pkey_at(parts: Seq<PartView>, r: int) -> int {
    i64s(parts[PA_PARTKEY_BASE as int])[r / bsize(parts)] + u32s(parts[PA_PARTKEY_CODES as int])[r]
}

/// p_size of row `r`.
pub open spec fn size_at(parts: Seq<PartView>, r: int) -> int {
    i64s(parts[PA_SIZE_BASE as int])[r / bsize(parts)] + u8s(parts[PA_SIZE_CODES as int])[r]
}

/// p_brand dictionary index of row `r`.
pub open spec fn bi_at(parts: Seq<PartView>, r: int) -> int {
    u64s(parts[PA_BRAND_BASE as int])[r / bsize(parts)] + u8s(parts[PA_BRAND_CODES as int])[r]
}

/// p_container dictionary index of row `r`.
pub open spec fn ci_at(parts: Seq<PartView>, r: int) -> int {
    u64s(parts[PA_CONT_BASE as int])[r / bsize(parts)] + u8s(parts[PA_CONT_CODES as int])[r]
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

pub open spec fn b_offs(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[PA_BRAND_DOFFS as int])
}

pub open spec fn b_bytes(parts: Seq<PartView>) -> Seq<u8> {
    u8s(parts[PA_BRAND_DBYTES as int])
}

pub open spec fn c_offs(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[PA_CONT_DOFFS as int])
}

pub open spec fn c_bytes(parts: Seq<PartView>) -> Seq<u8> {
    u8s(parts[PA_CONT_DBYTES as int])
}

/// Number of p_brand dictionary entries.
pub open spec fn n_brands(parts: Seq<PartView>) -> int {
    b_offs(parts).len() - 1
}

/// Number of p_container dictionary entries.
pub open spec fn n_conts(parts: Seq<PartView>) -> int {
    c_offs(parts).len() - 1
}

/// p_brand entry `i`.
pub open spec fn b_text(parts: Seq<PartView>, i: int) -> Seq<u8> {
    dict_text(b_offs(parts), b_bytes(parts), i)
}

/// p_container entry `i`.
pub open spec fn c_text(parts: Seq<PartView>, i: int) -> Seq<u8> {
    dict_text(c_offs(parts), c_bytes(parts), i)
}

/// A frame-of-reference column over `n` rows: one code per row, bases covering every block.
pub open spec fn for_len_ok(codes: int, bases: int, n: int, bs: int) -> bool {
    codes == n && bases * bs >= n
}

/// The layout and the column parts this interface reads.
pub open spec fn pa_shape(parts: Seq<PartView>, n: int) -> bool {
    let bs = bsize(parts);
    &&& parts.len() == PART_BCS_PARTS
    &&& parts[PA_LAYOUT as int] is U64 && u64s(parts[PA_LAYOUT as int]).len() == 2
    &&& n_rows(parts) == n
    &&& bs >= 1
    &&& parts[PA_PARTKEY_CODES as int] is U32 && parts[PA_PARTKEY_BASE as int] is I64
    &&& for_len_ok(u32s(parts[PA_PARTKEY_CODES as int]).len() as int, i64s(parts[PA_PARTKEY_BASE as int]).len() as int, n, bs)
    &&& parts[PA_SIZE_CODES as int] is U8 && parts[PA_SIZE_BASE as int] is I64
    &&& for_len_ok(u8s(parts[PA_SIZE_CODES as int]).len() as int, i64s(parts[PA_SIZE_BASE as int]).len() as int, n, bs)
    &&& parts[PA_BRAND_CODES as int] is U8 && parts[PA_BRAND_BASE as int] is U64
    &&& for_len_ok(u8s(parts[PA_BRAND_CODES as int]).len() as int, u64s(parts[PA_BRAND_BASE as int]).len() as int, n, bs)
    &&& parts[PA_CONT_CODES as int] is U8 && parts[PA_CONT_BASE as int] is U64
    &&& for_len_ok(u8s(parts[PA_CONT_CODES as int]).len() as int, u64s(parts[PA_CONT_BASE as int]).len() as int, n, bs)
    &&& parts[PA_BRAND_DOFFS as int] is U64 && parts[PA_BRAND_DBYTES as int] is U8
    &&& dict_ok(b_offs(parts), b_bytes(parts))
    &&& parts[PA_CONT_DOFFS as int] is U64 && parts[PA_CONT_DBYTES as int] is U8
    &&& dict_ok(c_offs(parts), c_bytes(parts))
}

/// A stored relation row `[p_partkey, p_brand, p_size, p_container]`.
pub open spec fn pa_row(k: int, b: Seq<u8>, sz: int, c: Seq<u8>) -> Row {
    seq![Val::Int(k), Val::Text(b), Val::Int(sz), Val::Text(c)]
}

/// The relation row of row `r`.
pub open spec fn row_at(parts: Seq<PartView>, r: int) -> Row {
    pa_row(pkey_at(parts, r), b_text(parts, bi_at(parts, r)), size_at(parts, r), c_text(parts, ci_at(parts, r)))
}

/// Row `r`'s dictionary indices lie inside their dictionaries.
pub open spec fn dict_idx_ok(parts: Seq<PartView>, r: int) -> bool {
    &&& 0 <= bi_at(parts, r) < n_brands(parts)
    &&& 0 <= ci_at(parts, r) < n_conts(parts)
}

/// Row `r` of the relation holds the values of row `r`.
pub open spec fn rows_ok(parts: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& forall|r: int| 0 <= r < rel.len() ==> #[trigger] rel[r] == row_at(parts, r)
    &&& forall|r: int| 0 <= r < rel.len() ==> #[trigger] dict_idx_ok(parts, r)
}

// ------------------------------------------------------------------------------------------------ the index

/// Index header `[mode, smin, ns]`.
pub open spec fn idx_meta(parts: Seq<PartView>) -> Seq<i64> {
    i64s(parts[IDX_META as int])
}

/// Directory offsets.
pub open spec fn idx_offs(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[IDX_OFFS as int])
}

/// Index rows.
pub open spec fn idx_perm(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[IDX_PERM as int])
}

/// The index is present.
pub open spec fn has_idx(parts: Seq<PartView>) -> bool {
    idx_meta(parts)[0] == MODE_INDEX
}

/// The smallest p_size of the key range.
pub open spec fn idx_smin(parts: Seq<PartView>) -> int {
    idx_meta(parts)[1] as int
}

/// The number of p_size values of the key range.
pub open spec fn idx_ns(parts: Seq<PartView>) -> int {
    idx_meta(parts)[2] as int
}

/// Number of directory entries.
pub open spec fn idx_nkeys(parts: Seq<PartView>) -> int {
    idx_offs(parts).len() - 1
}

/// Part row at index position `p`.
pub open spec fn prow(parts: Seq<PartView>, p: int) -> int {
    idx_perm(parts)[p] as int
}

/// The composite key of row `r`.
pub open spec fn comp_at(parts: Seq<PartView>, r: int) -> int {
    (bi_at(parts, r) * n_conts(parts) + ci_at(parts, r)) * idx_ns(parts) + (size_at(parts, r) - idx_smin(parts))
}

/// Row `r`'s p_size lies in the key range.
pub open spec fn size_in(parts: Seq<PartView>, r: int) -> bool {
    idx_smin(parts) <= size_at(parts, r) < idx_smin(parts) + idx_ns(parts)
}

/// Index position `p` lies in the directory entry of its row's composite key.
pub open spec fn in_entry(parts: Seq<PartView>, p: int) -> bool {
    let e = comp_at(parts, prow(parts, p));
    &&& 0 <= e < idx_nkeys(parts)
    &&& idx_offs(parts)[e] <= p < idx_offs(parts)[e + 1]
}

/// Row `r` is at some index position.
pub open spec fn listed(parts: Seq<PartView>, n: int, r: int) -> bool {
    exists|p: int| 0 <= p < n && #[trigger] prow(parts, p) == r
}

/// The index over the `n` rows.
pub open spec fn idx_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts[IDX_META as int] is I64 && idx_meta(parts).len() == 3
    &&& parts[IDX_OFFS as int] is U32
    &&& parts[IDX_PERM as int] is U32
    &&& has_idx(parts) ==> {
        &&& idx_ns(parts) >= 1
        &&& idx_offs(parts).len() == n_brands(parts) * n_conts(parts) * idx_ns(parts) + 1
        &&& idx_offs(parts)[idx_nkeys(parts)] <= n
        &&& forall|e: int| 0 <= e < idx_nkeys(parts) ==> #[trigger] idx_offs(parts)[e] <= idx_offs(parts)[e + 1]
        &&& idx_perm(parts).len() == n
        &&& forall|p: int| 0 <= p < n ==> 0 <= #[trigger] prow(parts, p) < n
        &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] prow(parts, a) != #[trigger] prow(parts, b)
        &&& forall|r: int| 0 <= r < n ==> #[trigger] listed(parts, n, r)
        &&& forall|r: int| 0 <= r < n ==> #[trigger] size_in(parts, r)
        &&& forall|p: int| 0 <= p < n ==> #[trigger] in_entry(parts, p)
    }
}

// ------------------------------------------------------------------------------------------------ represents

/// The inherited parts hold part's `[p_partkey, p_brand, p_size, p_container]` row for row; the new parts are the
/// composite index.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& rels.len() == 1
    &&& pa_shape(parts, rels[0].len() as int)
    &&& rows_ok(parts, rels[0])
    &&& idx_ok(parts, rels[0].len() as int)
}

/// The parts determine the relation: every row's values are stored.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    let n = a[0].len() as int;
    assert(b[0].len() == n);
    assert forall|r: int| 0 <= r < n implies a[0][r] == b[0][r] by {
        assert(a[0][r] == row_at(parts, r));
        assert(b[0][r] == row_at(parts, r));
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

/// The positions of entries `e0 .. e1` are exactly the positions whose row's composite key lies in `e0 .. e1`.
pub proof fn lemma_entries_exact(parts: Seq<PartView>, n: int, e0: int, e1: int, p: int)
    requires
        idx_ok(parts, n),
        has_idx(parts),
        0 <= e0 <= e1 <= idx_nkeys(parts),
        0 <= p < n,
    ensures
        (idx_offs(parts)[e0] <= p < idx_offs(parts)[e1]) <==> (e0 <= comp_at(parts, prow(parts, p)) < e1),
        idx_offs(parts)[e0] <= idx_offs(parts)[e1] <= n,
{
    assert(in_entry(parts, p));
    let f = comp_at(parts, prow(parts, p));
    lemma_offs_mono(parts, n, e0, e1);
    lemma_offs_mono(parts, n, e1, idx_nkeys(parts));
    if idx_offs(parts)[e0] <= p < idx_offs(parts)[e1] {
        if f < e0 {
            lemma_offs_mono(parts, n, f + 1, e0);
        } else if f >= e1 {
            lemma_offs_mono(parts, n, e1, f);
        }
    } else if e0 <= f < e1 {
        lemma_offs_mono(parts, n, e0, f);
        lemma_offs_mono(parts, n, f + 1, e1);
    }
}

} // verus!
