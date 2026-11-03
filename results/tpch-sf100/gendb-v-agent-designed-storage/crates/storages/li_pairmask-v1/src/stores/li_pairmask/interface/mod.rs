//! Storage `li_pairmask`: storage `facts` unchanged (its 75 parts, inherited, described by facts' own `represents`),
//! followed by one skip-metadata part over lineitem: per chunk of `MASK_ROWS` stored lineitem rows, the set of
//! (l_returnflag, l_linestatus) dictionary-code pairs that occur in the chunk, as a 64-bit mask.
//!
//! facts stores l_returnflag and l_linestatus as U8 codes (sorted-dictionary indices; part `LI_RETURNFLAG_CODES` and
//! `LI_LINESTATUS_CODES`). Part `PAIR_MASKS` (U64) holds one mask per chunk `c` (stored rows
//! `[c * MASK_ROWS, (c + 1) * MASK_ROWS)`): for every stored row `j` both codes are below 8 and bit
//! `rf_code * 8 + ls_code` of mask `j / MASK_ROWS` is set (`masks_ok`). A clear bit therefore means no row of the
//! chunk holds that pair, so a scan grouped by the two columns can skip reading both code columns of a chunk with
//! one pair, and read only one of them for a chunk with two pairs that differ in one column.
//! The part is empty when some code is 8 or more (or lineitem is empty): then it states nothing.
//! It holds no column value and nothing of another table: only which code pairs occur in a chunk (as a zone map).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::Row;
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;

verus! {

/// Part of the pair masks (U64, one per chunk of `MASK_ROWS` stored lineitem rows).
pub const PAIR_MASKS: usize = 75;
/// Number of parts of storage li_pairmask.
pub const LI_PAIRMASK_PARTS: usize = 76;
/// Stored lineitem rows per mask.
pub const MASK_ROWS: usize = 2048;

/// The inherited parts (storage facts).
pub open spec fn facts_parts(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(0, F::FACTS_PARTS as int)
}

/// The pair masks.
pub open spec fn pair_masks(parts: Seq<PartView>) -> Seq<u64> {
    match parts[PAIR_MASKS as int] {
        PartView::U64(s) => s,
        _ => Seq::empty(),
    }
}

/// The l_returnflag codes of facts' stored lineitem rows.
pub open spec fn rf_codes(parts: Seq<PartView>) -> Seq<u8> {
    FC::u8s(parts[(F::LINEITEM_FIRST + F::LI_RETURNFLAG_CODES) as int])
}

/// The l_linestatus codes of facts' stored lineitem rows.
pub open spec fn ls_codes(parts: Seq<PartView>) -> Seq<u8> {
    FC::u8s(parts[(F::LINEITEM_FIRST + F::LI_LINESTATUS_CODES) as int])
}

/// Bit `x` of mask `mk` is set.
pub open spec fn pair_bit(mk: u64, x: u64) -> bool {
    (mk >> x) & 1u64 == 1u64
}

/// Row `j`'s codes are below 8 and its pair's bit is set in the mask of its chunk.
pub open spec fn row_marked(rc: Seq<u8>, lc: Seq<u8>, mk: Seq<u64>, j: int) -> bool {
    &&& rc[j] < 8 && lc[j] < 8
    &&& pair_bit(mk[j / (MASK_ROWS as int)], (rc[j] * 8 + lc[j]) as u64)
}

/// The masks cover every stored row's code pair (or are empty, stating nothing).
pub open spec fn masks_ok(rc: Seq<u8>, lc: Seq<u8>, mk: Seq<u64>) -> bool {
    mk.len() > 0 ==> {
        &&& lc.len() == rc.len()
        &&& rc.len() <= mk.len() * MASK_ROWS
        &&& forall|j: int| 0 <= j < rc.len() ==> #[trigger] row_marked(rc, lc, mk, j)
    }
}

/// facts' relations in the inherited parts, then the pair masks of the stored lineitem rows.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == LI_PAIRMASK_PARTS
    &&& F::represents(facts_parts(parts), rels)
    &&& parts[PAIR_MASKS as int] is U64
    &&& masks_ok(rf_codes(parts), ls_codes(parts), pair_masks(parts))
}

/// The parts determine the relations they represent (facts is lossless).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    F::lemma_represents_determines(facts_parts(parts), a, b);
}

} // verus!
