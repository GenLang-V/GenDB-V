//! Storage `factext_trislice`: storage `factext_trisig` unchanged (its 13 parts, inherited: the 12 parts of
//! `factext` - the long text columns of lineitem (l_comment) and orders (o_clerk, o_comment), in canonical row order,
//! stored row `j` is source row `j` - and part `ORDERS_SIG`, the 128-bit byte-trigram signature (`trisig::sig_of`,
//! two words) of o_comment of every canonical orders row, words of row `r` at `2 r` and `2 r + 1`), followed by
//! two U64 parts `ORDERS_SLICES0`, `ORDERS_SLICES1`: the same signature bits, bit-sliced. Plane `q` (0..64) of part
//! `ORDERS_SLICES0 + h` holds bit `q` of signature word `h`; a plane is a bitmap over the orders
//! rows, `plane_words(n) = ceil(n / 64)` words; bit `r % 64` of its word `r / 64` (at `q * plane_words(n) + r / 64`)
//! is that bit of row `r` (`slices_ok`). A LIKE pattern needing `k` signature bits reads only those
//! `k` planes: the AND of their words is a superset of the rows that can match.
//!
//! The inherited parts are described exactly as in `factext` (this module is its interface text, with
//! `base_represents` its `represents`):
//!
//! Every table has the same frame: part `*_LAYOUT` (U64 `[rows, block rows]`), part `*_GROUPS` (U64 uniform group
//! starts: group `g` holds the stored rows `g * block .. min((g + 1) * block, rows)`; `block` is `BLOCK_ROWS`, or 1
//! when some block's values exceed a code width), then per column:
//! - bigint / numeric / date: a code part (U8, U16 or U32, one per row) and an I64 base part (one per group); the
//!   value of stored row `j` in group `g` is `base[g] + code[j]` (`colfmt::for_at`), numerics as coefficients of
//!   scale 2, dates as days since 2000-01-01; a zone part (I64, one per group) bounds a group's values from above
//!   (the base bounds them from below);
//! - low-cardinality text: a dictionary (U64 offsets + U8 bytes, entries strictly increasing bytewise, so
//!   distinct) and FOR codes (U64 bases) of each row's entry index;
//! - other text: U64 offsets (`rows + 1`, from 0) and U8 bytes.
//! A clustered table also has a row map column (`*_PERM_CODES` U32 + `*_PERM_BASE` U64): stored row `j` is canonical
//! row `for_at(.., j)`, a bijection (`colfmt::perm_col_at`), and its column predicates hold over
//! `colfmt::perm_rows` (`lemma_stored_rows_multiset`: the same multiset of rows as the relation). Other tables keep
//! canonical order: stored row `j` is canonical row `j`.
//! A table's parts sit at `<TABLE>_FIRST + <PREFIX>_<PART>`; `represents` states `<table>_ok` over that range.
//! Values are exact: nothing is rounded, clipped or derived.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
pub mod common;
pub mod trisig;
use common::colfmt::*;
use common::keyidx::{keyidx_ok, fidx};
use trisig::sig_of;

verus! {

/// Rows per group of every table (one-row groups are the fallback when a block's values exceed a code width).
pub const BLOCK_ROWS: usize = 65536;

/// The frame of a table of `n` rows: `tp[0]` is U64 `[n, block rows]`, `tp[1]` the uniform groups of that block size.
pub open spec fn table_layout_ok(tp: Seq<PartView>, n: int) -> bool {
    &&& tp.len() >= 2
    &&& tp[0] is U64
    &&& u64s(tp[0]).len() == 2
    &&& u64s(tp[0])[0] == n
    &&& groups_part_ok(tp[1], n, u64s(tp[0])[1] as int)
}


// ---------------------------------------------------------------------------------------------- lineitem

/// First part of table lineitem in this storage.
pub const LINEITEM_FIRST: usize = 0;
/// Number of parts of table lineitem.
pub const LT_PARTS: usize = 4;
/// lineitem: U64 [rows, block rows].
pub const LT_LAYOUT: usize = 0;
/// lineitem: U64 group starts.
pub const LT_GROUPS: usize = 1;
/// lineitem: U64 offsets of l_comment.
pub const LT_COMMENT_OFFS: usize = 2;
/// lineitem: U8 bytes of l_comment.
pub const LT_COMMENT_BYTES: usize = 3;

/// Table lineitem (1 columns, canonical row order) in its parts `tp`:
/// column 0 l_comment: text, U64 offsets + U8 bytes.
pub open spec fn lineitem_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == LT_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 1)
    &&& text_col_at(tp, LT_COMMENT_OFFS as int, LT_COMMENT_BYTES as int, rel, 0)
}

/// The parts of table lineitem determine its rows.
pub proof fn lemma_lineitem_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires lineitem_ok(tp, a), lineitem_ok(tp, b),
    ensures a == b,
{
    assert forall|j: int, c: int| 0 <= j < a.len() && 0 <= c < 1 implies #[trigger] a[j][c] == b[j][c] by {
        if c == 0 {
            assert(a[j][0] == b[j][0]);
        }
    }
    lemma_rows_eq(a, b, 1);
}

// ---------------------------------------------------------------------------------------------- orders

/// First part of table orders in this storage.
pub const ORDERS_FIRST: usize = 4;
/// Number of parts of table orders.
pub const OT_PARTS: usize = 8;
/// orders: U64 [rows, block rows].
pub const OT_LAYOUT: usize = 0;
/// orders: U64 group starts.
pub const OT_GROUPS: usize = 1;
/// orders: U32 codes of dictionary indices of o_clerk.
pub const OT_CLERK_CODES: usize = 2;
/// orders: U64 group bases of dictionary indices of o_clerk.
pub const OT_CLERK_BASE: usize = 3;
/// orders: U64 dictionary offsets of o_clerk.
pub const OT_CLERK_DICT_OFFS: usize = 4;
/// orders: U8 dictionary bytes of o_clerk.
pub const OT_CLERK_DICT_BYTES: usize = 5;
/// orders: U64 offsets of o_comment.
pub const OT_COMMENT_OFFS: usize = 6;
/// orders: U8 bytes of o_comment.
pub const OT_COMMENT_BYTES: usize = 7;

/// Table orders (2 columns, canonical row order) in its parts `tp`:
/// column 0 o_clerk: text, sorted dictionary; FOR u32 codes of entry indices + U64 bases.
/// column 1 o_comment: text, U64 offsets + U8 bytes.
pub open spec fn orders_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == OT_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 2)
    &&& tp[OT_CLERK_CODES as int] is U32
    &&& dict_col_at(tp, OT_GROUPS as int, OT_CLERK_CODES as int, OT_CLERK_BASE as int, OT_CLERK_DICT_OFFS as int, OT_CLERK_DICT_BYTES as int, rel, 0)
    &&& text_col_at(tp, OT_COMMENT_OFFS as int, OT_COMMENT_BYTES as int, rel, 1)
}

/// The parts of table orders determine its rows.
pub proof fn lemma_orders_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires orders_ok(tp, a), orders_ok(tp, b),
    ensures a == b,
{
    assert forall|j: int, c: int| 0 <= j < a.len() && 0 <= c < 2 implies #[trigger] a[j][c] == b[j][c] by {
        if c == 0 {
            assert(a[j][0] == b[j][0]);
        } else if c == 1 {
            assert(a[j][1] == b[j][1]);
        }
    }
    lemma_rows_eq(a, b, 2);
}

/// Number of parts of storage factext (the inherited parts).
pub const FACTEXT_PARTS: usize = 12;

/// The inherited parts hold every table of storage factext, each over its own part range (`<table>_ok`).
pub open spec fn base_represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == FACTEXT_PARTS
    &&& rels.len() == 2
    &&& lineitem_ok(parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LT_PARTS) as int), rels[0])
    &&& orders_ok(parts.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OT_PARTS) as int), rels[1])
}

/// The inherited parts determine the relations they represent (complete lossless storage).
pub proof fn lemma_base_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires base_represents(parts, a), base_represents(parts, b),
    ensures a == b,
{
    lemma_lineitem_determines(parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LT_PARTS) as int), a[0], b[0]);
    lemma_orders_determines(parts.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OT_PARTS) as int), a[1], b[1]);
    assert(a =~= b);
}

// ---------------------------------------------------------------------------------------------- signatures

/// Part index of the o_comment trigram signatures (U64, two words per canonical orders row).
pub const ORDERS_SIG: usize = 12;
/// Number of parts of storage factext_trisig (inherited by this storage).
pub const FACTEXT_TRISIG_PARTS: usize = 13;
/// Part index of the o_comment offsets (U64, rows + 1).
pub const O_COMMENT_OFFS_PART: usize = 10;
/// Part index of the o_comment bytes (U8).
pub const O_COMMENT_BYTES_PART: usize = 11;

/// The o_comment text of canonical orders row `r` in the parts.
pub open spec fn comment_at(parts: Seq<PartView>, r: int) -> Seq<u8> {
    text_of(u64s(parts[O_COMMENT_OFFS_PART as int]), u8s(parts[O_COMMENT_BYTES_PART as int]), r)
}

/// Part `ORDERS_SIG` holds the signature of o_comment of every orders row (`n` rows): word `w` of row `r` at
/// `2 r + w`.
pub open spec fn sigs_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts[ORDERS_SIG as int] is U64
    &&& u64s(parts[ORDERS_SIG as int]).len() == 2 * n
    &&& forall|r: int| 0 <= r < n ==> {
            &&& #[trigger] u64s(parts[ORDERS_SIG as int])[2 * r] == sig_of(comment_at(parts, r), 0)
            &&& u64s(parts[ORDERS_SIG as int])[2 * r + 1] == sig_of(comment_at(parts, r), 1)
        }
}

/// Part index of the bit-sliced signature word 0 (U64, 64 planes of `plane_words(n)` words: signature bits 0..64).
pub const ORDERS_SLICES0: usize = 13;
/// Part index of the bit-sliced signature word 1 (U64, 64 planes: signature bits 64..128).
pub const ORDERS_SLICES1: usize = 14;
/// Number of parts of storage factext_trislice.
pub const FACTEXT_TRISLICE_PARTS: usize = 15;

/// Bit `i` (0..64) of the word `x`.
pub open spec fn bit_at(x: u64, i: int) -> bool {
    (x >> (i as u64)) & 1u64 == 1u64
}

/// Words per plane over `n` rows (one bit per row, 64 rows per word).
pub open spec fn plane_words(n: int) -> int {
    (n + 63) / 64
}

/// The bit of row `r` in plane `q` of the slices `sl` (`nw` words per plane, plane `q` at `q * nw`).
pub open spec fn slice_bit(sl: Seq<u64>, nw: int, q: int, r: int) -> bool {
    bit_at(sl[q * nw + r / 64], r % 64)
}

/// Bit `q` of signature word `h` of row `r` in the signature words `sg` (two per row).
pub open spec fn sig_bit(sg: Seq<u64>, h: int, q: int, r: int) -> bool {
    bit_at(sg[2 * r + h], q)
}

/// Part `ORDERS_SLICES0 + h` (`h` = 0, 1) holds, for each of the `n` orders rows and each bit `q` (0..64), bit `q`
/// of the row's signature word `h` (part `ORDERS_SIG`).
pub open spec fn slice_half_ok(parts: Seq<PartView>, n: int, h: int) -> bool {
    &&& parts[ORDERS_SLICES0 as int + h] is U64
    &&& u64s(parts[ORDERS_SLICES0 as int + h]).len() == 64 * plane_words(n)
    &&& forall|q: int, r: int| 0 <= q < 64 && 0 <= r < n ==>
            #[trigger] slice_bit(u64s(parts[ORDERS_SLICES0 as int + h]), plane_words(n), q, r)
                == sig_bit(u64s(parts[ORDERS_SIG as int]), h, q, r)
}

/// Both signature words, bit-sliced.
pub open spec fn slices_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& slice_half_ok(parts, n, 0)
    &&& slice_half_ok(parts, n, 1)
}

/// The inherited parts of factext_trisig (those of factext, then the signatures), then the bit-sliced signatures.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == FACTEXT_TRISLICE_PARTS
    &&& base_represents(parts.subrange(0, FACTEXT_PARTS as int), rels)
    &&& sigs_ok(parts, rels[1].len() as int)
    &&& slices_ok(parts, rels[1].len() as int)
}

/// The parts determine the relations they represent (the inherited parts already do).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    lemma_base_determines(parts.subrange(0, FACTEXT_PARTS as int), a, b);
}

/// Under `represents`, o_comment of orders row `r` is `comment_at(parts, r)`, its signature is part `ORDERS_SIG` at
/// `r`, and the o_comment parts are well-formed text parts of every orders row.
pub proof fn lemma_comment_sig(parts: Seq<PartView>, rels: Seq<Seq<Row>>, r: int)
    requires
        represents(parts, rels),
        0 <= r < rels[1].len(),
    ensures
        rels[1][r][1] == Val::Text(comment_at(parts, r)),
        u64s(parts[ORDERS_SIG as int])[2 * r] == sig_of(comment_at(parts, r), 0),
        u64s(parts[ORDERS_SIG as int])[2 * r + 1] == sig_of(comment_at(parts, r), 1),
        text_parts_wf(u64s(parts[O_COMMENT_OFFS_PART as int]), u8s(parts[O_COMMENT_BYTES_PART as int]), rels[1].len() as int),
        parts[O_COMMENT_OFFS_PART as int] is U64,
        parts[O_COMMENT_BYTES_PART as int] is U8,
{
    let base = parts.subrange(0, FACTEXT_PARTS as int);
    let tp = base.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OT_PARTS) as int);
    assert(tp[OT_COMMENT_OFFS as int] == parts[O_COMMENT_OFFS_PART as int]);
    assert(tp[OT_COMMENT_BYTES as int] == parts[O_COMMENT_BYTES_PART as int]);
}

} // verus!
