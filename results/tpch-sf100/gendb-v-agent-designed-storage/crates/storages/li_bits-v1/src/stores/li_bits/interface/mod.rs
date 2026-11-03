//! Storage `li_bits`: storage `facts` unchanged (its 75 parts, inherited, described by facts' own `represents`),
//! followed by bitmap indexes over facts' stored lineitem rows (stored order).
//!
//! A bitmap has one bit per stored row, 64 rows per U64 word: bit `i` of word `w` is stored row `64 w + i`
//! (`row_bit`). A bitmap part holds several bitmaps of `nw` words each, one after the other (bitmap `k` is words
//! `k * nw .. k * nw + nw`). Every bitmap is an index of one lineitem column: key -> the set of its own rows.
//! - `DISC_BITS`: equality-encoded index of l_discount: bitmap `k` marks the rows whose discount (coefficient at
//!   scale 2) equals `DISC_KEYS[k]`;
//! - `QTY_BITS`: range-encoded index of l_quantity: bitmap `t` marks the rows whose quantity (coefficient at scale
//!   2) is below `QTY_KEYS[t]`;
//! - `SHIP_BITS`: range-encoded index of l_shipdate per row group of facts: bitmap `t` marks the rows of group `g`
//!   whose shipdate (days since 1970-01-01) is below `SHIP_KEYS[g * ns + t]`.
//! The builder chooses the keys (discount 0.00..0.10, quantity 1..51, the month starts after each group's
//! smallest shipdate); `bits_ok` states only what each bit means, for whatever keys the parts hold. Values are
//! the frame-of-reference decodings of facts' parts (`FC::for_at`), the ones facts' `represents` relates to the rows.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::Row;
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;

verus! {

/// Layout (U64, 4 entries): words per bitmap `nw`, discount keys `nd`, quantity keys `nq`, shipdate keys per group `ns`.
pub const BITS_LAYOUT: usize = 75;
/// Discount keys (I64, `nd`).
pub const DISC_KEYS: usize = 76;
/// Discount bitmaps (U64, `nd * nw`).
pub const DISC_BITS: usize = 77;
/// Quantity keys (I64, `nq`).
pub const QTY_KEYS: usize = 78;
/// Quantity bitmaps (U64, `nq * nw`).
pub const QTY_BITS: usize = 79;
/// Shipdate keys per row group (I64, `ng * ns`).
pub const SHIP_KEYS: usize = 80;
/// Shipdate bitmaps (U64, `ns * nw`).
pub const SHIP_BITS: usize = 81;
/// Number of parts of storage li_bits.
pub const LI_BITS_PARTS: usize = 82;

/// The inherited parts (storage facts).
pub open spec fn facts_parts(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(0, F::FACTS_PARTS as int)
}

/// Bit `i` (`0 <= i < 64`) of word `x`.
pub open spec fn bit(x: u64, i: int) -> bool {
    (x >> (i as u64)) & 1u64 == 1u64
}

/// The bit of stored row `j` in bitmap `k` of a bitmap part with `nw` words per bitmap.
pub open spec fn row_bit(words: Seq<u64>, nw: int, k: int, j: int) -> bool {
    bit(words[k * nw + j / 64], j % 64)
}

/// The row groups of facts' lineitem rows.
pub open spec fn gsv(fp: Seq<PartView>) -> Seq<u64> {
    FC::u64s(fp[F::LI_GROUPS as int])
}

/// Number of stored lineitem rows.
pub open spec fn n_rows(fp: Seq<PartView>) -> int {
    crate::gendb_entry::stored::part_len(fp[F::LI_SHIPDATE_CODES as int]) as int
}

/// Discount coefficient (scale 2) of stored row `j`.
pub open spec fn disc_at(fp: Seq<PartView>, j: int) -> int {
    FC::for_at(gsv(fp), fp[F::LI_DISCOUNT_BASE as int], fp[F::LI_DISCOUNT_CODES as int], j)
}

/// Quantity coefficient (scale 2) of stored row `j`.
pub open spec fn qty_at(fp: Seq<PartView>, j: int) -> int {
    FC::for_at(gsv(fp), fp[F::LI_QUANTITY_BASE as int], fp[F::LI_QUANTITY_CODES as int], j)
}

/// Shipdate (days) of stored row `j`.
pub open spec fn ship_at(fp: Seq<PartView>, j: int) -> int {
    FC::for_at(gsv(fp), fp[F::LI_SHIPDATE_BASE as int], fp[F::LI_SHIPDATE_CODES as int], j)
}

/// Words per bitmap.
pub open spec fn n_words(parts: Seq<PartView>) -> int { FC::u64s(parts[BITS_LAYOUT as int])[0] as int }
/// Discount keys.
pub open spec fn n_disc(parts: Seq<PartView>) -> int { FC::u64s(parts[BITS_LAYOUT as int])[1] as int }
/// Quantity keys.
pub open spec fn n_qty(parts: Seq<PartView>) -> int { FC::u64s(parts[BITS_LAYOUT as int])[2] as int }
/// Shipdate keys per group.
pub open spec fn n_ship(parts: Seq<PartView>) -> int { FC::u64s(parts[BITS_LAYOUT as int])[3] as int }

/// Shapes of the bitmap parts.
pub open spec fn bits_shape(parts: Seq<PartView>) -> bool {
    let fp = facts_parts(parts);
    let nw = n_words(parts);
    let ng = gsv(fp).len() - 1;
    &&& parts[BITS_LAYOUT as int] is U64 && FC::u64s(parts[BITS_LAYOUT as int]).len() == 4
    &&& n_rows(fp) <= nw * 64
    &&& parts[DISC_KEYS as int] is I64 && FC::i64s(parts[DISC_KEYS as int]).len() == n_disc(parts)
    &&& parts[DISC_BITS as int] is U64 && FC::u64s(parts[DISC_BITS as int]).len() == n_disc(parts) * nw
    &&& parts[QTY_KEYS as int] is I64 && FC::i64s(parts[QTY_KEYS as int]).len() == n_qty(parts)
    &&& parts[QTY_BITS as int] is U64 && FC::u64s(parts[QTY_BITS as int]).len() == n_qty(parts) * nw
    &&& parts[SHIP_KEYS as int] is I64 && FC::i64s(parts[SHIP_KEYS as int]).len() == ng * n_ship(parts)
    &&& parts[SHIP_BITS as int] is U64 && FC::u64s(parts[SHIP_BITS as int]).len() == n_ship(parts) * nw
}

/// Discount bitmap `k` marks the rows whose discount is key `k`.
pub open spec fn disc_bit_ok(parts: Seq<PartView>, k: int, j: int) -> bool {
    row_bit(FC::u64s(parts[DISC_BITS as int]), n_words(parts), k, j)
        == (disc_at(facts_parts(parts), j) == FC::i64s(parts[DISC_KEYS as int])[k])
}

/// Quantity bitmap `t` marks the rows whose quantity is below key `t`.
pub open spec fn qty_bit_ok(parts: Seq<PartView>, t: int, j: int) -> bool {
    row_bit(FC::u64s(parts[QTY_BITS as int]), n_words(parts), t, j)
        == (qty_at(facts_parts(parts), j) < FC::i64s(parts[QTY_KEYS as int])[t])
}

/// Shipdate bitmap `t` marks the rows whose shipdate is below key `t` of their group.
pub open spec fn ship_bit_ok(parts: Seq<PartView>, t: int, j: int) -> bool {
    let fp = facts_parts(parts);
    row_bit(FC::u64s(parts[SHIP_BITS as int]), n_words(parts), t, j)
        == (ship_at(fp, j) < FC::i64s(parts[SHIP_KEYS as int])[FC::group_of(gsv(fp), j) * n_ship(parts) + t])
}

/// What every bit of the bitmap parts means.
pub open spec fn bits_ok(parts: Seq<PartView>) -> bool {
    let n = n_rows(facts_parts(parts));
    &&& bits_shape(parts)
    &&& forall|k: int, j: int| 0 <= k < n_disc(parts) && 0 <= j < n ==> #[trigger] disc_bit_ok(parts, k, j)
    &&& forall|t: int, j: int| 0 <= t < n_qty(parts) && 0 <= j < n ==> #[trigger] qty_bit_ok(parts, t, j)
    &&& forall|t: int, j: int| 0 <= t < n_ship(parts) && 0 <= j < n ==> #[trigger] ship_bit_ok(parts, t, j)
}

/// facts' relations in the inherited parts; the bitmap parts index facts' stored lineitem rows.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == LI_BITS_PARTS
    &&& F::represents(facts_parts(parts), rels)
    &&& bits_ok(parts)
}

/// The parts determine the relations they represent (facts is lossless).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    F::lemma_represents_determines(facts_parts(parts), a, b);
}

} // verus!
