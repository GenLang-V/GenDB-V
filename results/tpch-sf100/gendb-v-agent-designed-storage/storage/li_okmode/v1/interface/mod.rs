//! Storage `li_okmode`: storage `li_okruns` unchanged (its 76 parts, inherited: storage `facts`' 75 parts and the
//! l_orderkey run starts), followed by two bitmap families over facts' stored lineitem rows (stored order).
//!
//! A bitmap has one bit per stored row, 64 rows per U64 word: bit `i` of word `w` is stored row `64 w + i`
//! (`row_bit`); bits of rows at or past the row count are 0. With `nw` words per bitmap:
//! - `RUN_BITS` (`nw` words): the run offsets of l_orderkey as a bitmap: row `j` is set exactly when it starts a
//!   maximal run of equal l_orderkey (`j == 0` or its key differs from row `j - 1`'s);
//! - `MODE_BITS` (`nm * nw` words, bitmap `k` at words `k * nw ..`): equality-encoded bitmap index of l_shipmode:
//!   bitmap `k` marks the rows whose l_shipmode dictionary index (group base + code) is `k`.
//! `nw == 0` (with empty bitmap parts) is the fallback "no bitmaps"; otherwise `nw * 64` covers every row.
//! Values are the frame-of-reference decodings of facts' parts as storage `li_okruns` reads them (`okey_at`), the
//! ones facts' `represents` relates to the rows.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::Row;
use crate::stores::facts::interface as F;
use crate::stores::li_okruns::interface as LR;
use F::common::colfmt::{u8s, u64s};

verus! {

/// Parts of storage li_okruns, kept unchanged in front.
pub const OKRUNS_PARTS: usize = 76;
/// Layout (U64, 2 entries): words per bitmap `nw`, l_shipmode bitmaps `nm`.
pub const OKM_LAYOUT: usize = 76;
/// Run-start bitmap (U64, `nw`).
pub const RUN_BITS: usize = 77;
/// l_shipmode bitmaps (U64, `nm * nw`).
pub const MODE_BITS: usize = 78;
/// Number of parts of storage li_okmode.
pub const LI_OKMODE_PARTS: usize = 79;

/// The inherited parts (storage li_okruns).
pub open spec fn okruns_parts(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(0, OKRUNS_PARTS as int)
}

/// Bit `i` (`0 <= i < 64`) of word `x`.
pub open spec fn bit(x: u64, i: int) -> bool {
    (x >> (i as u64)) & 1u64 == 1u64
}

/// The bit of stored row `j` in bitmap `k` of a bitmap part with `nw` words per bitmap.
pub open spec fn row_bit(words: Seq<u64>, nw: int, k: int, j: int) -> bool {
    bit(words[k * nw + j / 64], j % 64)
}

/// Stored lineitem rows.
pub open spec fn n_rows(parts: Seq<PartView>) -> int {
    LR::li_rows(parts)
}

/// Row `j` starts a maximal run of equal l_orderkey.
pub open spec fn run_start(parts: Seq<PartView>, j: int) -> bool {
    j == 0 || LR::okey_at(parts, j) != LR::okey_at(parts, j - 1)
}

/// l_shipmode dictionary index of stored row `j` (group base + code).
pub open spec fn mode_at(parts: Seq<PartView>, j: int) -> int {
    u64s(parts[F::LI_SHIPMODE_BASE as int])[j / LR::li_bsize(parts)] + u8s(parts[F::LI_SHIPMODE_CODES as int])[j]
}

/// Words per bitmap.
pub open spec fn n_words(parts: Seq<PartView>) -> int {
    u64s(parts[OKM_LAYOUT as int])[0] as int
}

/// Number of l_shipmode bitmaps.
pub open spec fn n_modes(parts: Seq<PartView>) -> int {
    u64s(parts[OKM_LAYOUT as int])[1] as int
}

/// Shapes of the bitmap parts.
pub open spec fn okm_shape(parts: Seq<PartView>) -> bool {
    let nw = n_words(parts);
    &&& parts[OKM_LAYOUT as int] is U64 && u64s(parts[OKM_LAYOUT as int]).len() == 2
    &&& parts[RUN_BITS as int] is U64 && u64s(parts[RUN_BITS as int]).len() == nw
    &&& parts[MODE_BITS as int] is U64 && u64s(parts[MODE_BITS as int]).len() == n_modes(parts) * nw
    &&& nw > 0 ==> n_rows(parts) <= nw * 64
}

/// The run-start bit of row `j` (`j < nw * 64`).
pub open spec fn run_bit_ok(parts: Seq<PartView>, j: int) -> bool {
    row_bit(u64s(parts[RUN_BITS as int]), n_words(parts), 0, j) == (j < n_rows(parts) && run_start(parts, j))
}

/// The bit of row `j` in l_shipmode bitmap `k`.
pub open spec fn mode_bit_ok(parts: Seq<PartView>, k: int, j: int) -> bool {
    row_bit(u64s(parts[MODE_BITS as int]), n_words(parts), k, j) == (j < n_rows(parts) && mode_at(parts, j) == k)
}

/// What every bit of the bitmap parts means (when present).
pub open spec fn okm_ok(parts: Seq<PartView>) -> bool {
    let nw = n_words(parts);
    &&& okm_shape(parts)
    &&& forall|j: int| 0 <= j < nw * 64 ==> #[trigger] run_bit_ok(parts, j)
    &&& forall|k: int, j: int| 0 <= k < n_modes(parts) && 0 <= j < nw * 64 ==> #[trigger] mode_bit_ok(parts, k, j)
}

/// li_okruns' relations (facts' rows and the run starts) in the inherited parts; the bitmaps index facts' stored
/// lineitem rows.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == LI_OKMODE_PARTS
    &&& LR::represents(okruns_parts(parts), rels)
    &&& okm_ok(parts)
}

/// The parts determine the relations they represent (li_okruns, hence facts, is lossless).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    LR::lemma_represents_determines(okruns_parts(parts), a, b);
}

} // verus!
