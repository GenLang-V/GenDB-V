//! Storage `part_nameidx`: storage `custpart` unchanged (its 50 parts, inherited), followed by one U32 part
//! `NAME_PERM`: the part rows in nondecreasing bytewise p_name order.
//!
//! What this interface states about the inherited parts (only what lookups of part rows by p_name need; the stored
//! relation is part projected on `[p_partkey, p_name]`, canonical row order, stored row `r` is canonical row `r`):
//! - part `PA_LAYOUT` is U64 `[n, bsize]` (`bsize >= 1` rows per block);
//! - p_partkey of row `r` is `base[r / bsize] + code[r]` (`PA_PARTKEY_BASE` I64, `PA_PARTKEY_CODES` U32);
//! - p_name of row `r` is `bytes[offs[r] .. offs[r + 1]]` (`PA_NAME_OFFS` U64, `n + 1` offsets; `PA_NAME_BYTES` U8).
//!
//! The new part `NAME_PERM` (U32) is either empty (no index) or holds `n` row positions: a bijection of `[0, n)`
//! along which the names never decrease (`lex_cmp`, bytewise; ties in any order). So the rows whose name lies in
//! a bytewise interval (for example: starts with a given prefix) are one contiguous range of positions. Every
//! stored value is a row position: no column value is stored.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
use crate::spec::text::lex_cmp;

verus! {

// ------------------------------------------------------------------------------------------------ part indices

/// part: U64 `[rows, block rows]` (custpart's `PART_FIRST + PA_LAYOUT`).
pub const PA_LAYOUT: usize = 21;
/// part: U32 codes of p_partkey.
pub const PA_PARTKEY_CODES: usize = 23;
/// part: I64 block bases of p_partkey.
pub const PA_PARTKEY_BASE: usize = 24;
/// part: U64 offsets of p_name (`rows + 1`).
pub const PA_NAME_OFFS: usize = 25;
/// part: U8 bytes of p_name.
pub const PA_NAME_BYTES: usize = 26;
/// Number of inherited parts (storage custpart).
pub const CUSTPART_PARTS: usize = 50;
/// The name order: U32 row positions (empty, or one per part row).
pub const NAME_PERM: usize = 50;
/// Number of parts of storage part_nameidx.
pub const NAMEIDX_PARTS: usize = 51;

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

/// Rows per block of the p_partkey column.
pub open spec fn bsize(parts: Seq<PartView>) -> int {
    u64s(parts[PA_LAYOUT as int])[1] as int
}

/// p_partkey of row `r`.
pub open spec fn pkey_at(parts: Seq<PartView>, r: int) -> int {
    i64s(parts[PA_PARTKEY_BASE as int])[r / bsize(parts)] + u32s(parts[PA_PARTKEY_CODES as int])[r]
}

/// The p_name offsets.
pub open spec fn name_offs(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[PA_NAME_OFFS as int])
}

/// The p_name bytes.
pub open spec fn name_bytes(parts: Seq<PartView>) -> Seq<u8> {
    u8s(parts[PA_NAME_BYTES as int])
}

/// p_name of row `r`.
pub open spec fn name_at(parts: Seq<PartView>, r: int) -> Seq<u8> {
    name_bytes(parts).subrange(name_offs(parts)[r] as int, name_offs(parts)[r + 1] as int)
}

/// The name order.
pub open spec fn perm(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[NAME_PERM as int])
}

/// Row `r`'s name is a byte range inside the bytes part.
pub open spec fn name_range_ok(parts: Seq<PartView>, r: int) -> bool {
    name_offs(parts)[r] <= name_offs(parts)[r + 1] && name_offs(parts)[r + 1] <= name_bytes(parts).len()
}

/// The layout, the p_partkey and p_name columns of `n` rows, and the kind of the new part.
pub open spec fn pa_shape(parts: Seq<PartView>, n: int) -> bool {
    &&& parts.len() == NAMEIDX_PARTS
    &&& parts[PA_LAYOUT as int] is U64 && u64s(parts[PA_LAYOUT as int]).len() == 2
    &&& n_rows(parts) == n
    &&& bsize(parts) >= 1
    &&& parts[PA_PARTKEY_CODES as int] is U32 && u32s(parts[PA_PARTKEY_CODES as int]).len() == n
    &&& parts[PA_PARTKEY_BASE as int] is I64 && i64s(parts[PA_PARTKEY_BASE as int]).len() * bsize(parts) >= n
    &&& parts[PA_NAME_OFFS as int] is U64 && name_offs(parts).len() == n + 1
    &&& parts[PA_NAME_BYTES as int] is U8
    &&& forall|r: int| 0 <= r < n ==> #[trigger] name_range_ok(parts, r)
    &&& parts[NAME_PERM as int] is U32
}

/// A stored relation row `[p_partkey, p_name]`.
pub open spec fn pa_row(k: int, name: Seq<u8>) -> Row {
    seq![Val::Int(k), Val::Text(name)]
}

/// Row `r` of the relation holds the values of stored row `r`.
pub open spec fn rows_ok(parts: Seq<PartView>, rel: Seq<Row>) -> bool {
    forall|r: int| 0 <= r < rel.len() ==> #[trigger] rel[r] == pa_row(pkey_at(parts, r), name_at(parts, r))
}

/// Row `r` appears in the name order.
pub open spec fn listed(parts: Seq<PartView>, n: int, r: int) -> bool {
    exists|i: int| 0 <= i < n && #[trigger] perm(parts)[i] == r
}

/// The names at positions `i` and `i + 1` of the name order are in order.
pub open spec fn name_le_at(parts: Seq<PartView>, i: int) -> bool {
    lex_cmp(name_at(parts, perm(parts)[i] as int), name_at(parts, perm(parts)[i + 1] as int)) <= 0
}

/// The name order is present.
pub open spec fn has_perm(parts: Seq<PartView>) -> bool {
    perm(parts).len() == n_rows(parts) && n_rows(parts) > 0
}

/// The name order over `n` rows: empty, or a bijection of `[0, n)` along which the names never decrease.
pub open spec fn perm_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& perm(parts).len() == 0 || perm(parts).len() == n
    &&& perm(parts).len() == n ==> {
        &&& forall|i: int| 0 <= i < n ==> #[trigger] perm(parts)[i] < n
        &&& forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> #[trigger] perm(parts)[i] != #[trigger] perm(parts)[j]
        &&& forall|r: int| 0 <= r < n ==> #[trigger] listed(parts, n, r)
        &&& forall|i: int| 0 <= i < n - 1 ==> #[trigger] name_le_at(parts, i)
    }
}

// ------------------------------------------------------------------------------------------------ represents

/// The inherited parts hold part's `[p_partkey, p_name]` row for row; the new part is the name order.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& rels.len() == 1
    &&& pa_shape(parts, rels[0].len() as int)
    &&& rows_ok(parts, rels[0])
    &&& perm_ok(parts, rels[0].len() as int)
}

/// The parts determine the relation: every row's values are stored.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    assert(a[0].len() == b[0].len());
    assert forall|r: int| 0 <= r < a[0].len() implies a[0][r] == b[0][r] by {
        assert(a[0][r] == pa_row(pkey_at(parts, r), name_at(parts, r)));
        assert(b[0][r] == pa_row(pkey_at(parts, r), name_at(parts, r)));
    }
    assert(a[0] =~= b[0]);
    assert(a =~= b);
}

/// Names never decrease between any two positions of the name order.
pub proof fn lemma_name_order(parts: Seq<PartView>, n: int, i: int, j: int)
    requires
        perm_ok(parts, n),
        perm(parts).len() == n,
        0 <= i <= j < n,
    ensures
        lex_cmp(name_at(parts, perm(parts)[i] as int), name_at(parts, perm(parts)[j] as int)) <= 0,
    decreases j - i,
{
    if i == j {
        crate::bridge::equality::lemma_lex_cmp_zero(name_at(parts, perm(parts)[i] as int), name_at(parts, perm(parts)[i] as int));
    } else {
        lemma_name_order(parts, n, i, j - 1);
        assert(name_le_at(parts, j - 1));
        crate::bridge::order::lemma_lex_cmp_trans(
            name_at(parts, perm(parts)[i] as int),
            name_at(parts, perm(parts)[j - 1] as int),
            name_at(parts, perm(parts)[j] as int));
    }
}

} // verus!
