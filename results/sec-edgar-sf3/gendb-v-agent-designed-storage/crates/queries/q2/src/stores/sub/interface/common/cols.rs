//! Column encodings over stored parts, as SQL values per row: `i32` and `i128` columns, NULL validity bytes
//! (0: NULL), flat text (U64 offsets + U8 bytes, row `i` is value `i`) and dictionary text (U64 codes per row into a
//! text list). Every accessor returns the empty sequence for a part of another element type, so a layout predicate
//! states each part's type separately.
use vstd::prelude::*;
use crate::spec::value::Val;
use crate::gendb_entry::layout::PartView;
use super::text::{text_entry, text_parts_wf, u64_part, u8_part};

verus! {

pub open spec fn i32_part(p: PartView) -> Seq<i32> {
    match p {
        PartView::I32(s) => s,
        _ => Seq::empty(),
    }
}

pub open spec fn i128_part(p: PartView) -> Seq<i128> {
    match p {
        PartView::I128(s) => s,
        _ => Seq::empty(),
    }
}

/// Number of elements of a part (any type).
pub open spec fn part_size(p: PartView) -> nat {
    match p {
        PartView::I8(s) => s.len(),
        PartView::I16(s) => s.len(),
        PartView::I32(s) => s.len(),
        PartView::I64(s) => s.len(),
        PartView::I128(s) => s.len(),
        PartView::U8(s) => s.len(),
        PartView::U16(s) => s.len(),
        PartView::U32(s) => s.len(),
        PartView::U64(s) => s.len(),
    }
}

/// Row `i` of an `int4` column stored in `I32` part `p`.
pub open spec fn int_at(parts: Seq<PartView>, p: int, i: int) -> Val {
    Val::Int(i32_part(parts[p])[i] as int)
}

/// Row `i` of a nullable column: NULL when validity part `pv` holds 0 at `i`, else `v`.
pub open spec fn or_null_at(parts: Seq<PartView>, pv: int, i: int, v: Val) -> Val {
    if u8_part(parts[pv])[i] == 0 { Val::Null } else { v }
}

/// Row `i` of a flat text column: value `i` of the text list in parts `po` (offsets), `pb` (bytes).
pub open spec fn flat_text_at(parts: Seq<PartView>, po: int, pb: int, i: int) -> Val {
    Val::Text(text_entry(u64_part(parts[po]), u8_part(parts[pb]), i))
}

/// Row `i` of a dictionary text column: the dictionary value (parts `po`, `pb`) at the row's code (part `pc`).
pub open spec fn dict_text_at(parts: Seq<PartView>, pc: int, po: int, pb: int, i: int) -> Val {
    Val::Text(text_entry(u64_part(parts[po]), u8_part(parts[pb]), u64_part(parts[pc])[i] as int))
}

/// `I32` part `p` holds `n` values.
pub open spec fn i32_col_ok(parts: Seq<PartView>, p: int, n: int) -> bool {
    &&& parts[p] is I32
    &&& i32_part(parts[p]).len() == n
}

/// `U8` part `p` holds `n` validity bytes.
pub open spec fn valid_col_ok(parts: Seq<PartView>, p: int, n: int) -> bool {
    &&& parts[p] is U8
    &&& u8_part(parts[p]).len() == n
}

/// Parts `po` (U64 offsets) and `pb` (U8 bytes) hold a text list of `n` values.
pub open spec fn text_col_ok(parts: Seq<PartView>, po: int, pb: int, n: int) -> bool {
    &&& parts[po] is U64
    &&& parts[pb] is U8
    &&& text_parts_wf(u64_part(parts[po]), u8_part(parts[pb]), n)
}

/// Number of values of the text list in parts `po`, `pb` (one less than its offsets).
pub open spec fn text_count(parts: Seq<PartView>, po: int) -> int {
    u64_part(parts[po]).len() - 1
}

/// Part `pc` holds `n` codes; every code of a row in the column (validity `pv` nonzero, or every row when
/// `pv < 0`) is a position of the dictionary in parts `po`, `pb`.
pub open spec fn dict_col_ok(parts: Seq<PartView>, pc: int, po: int, pb: int, pv: int, n: int) -> bool {
    &&& parts[pc] is U64
    &&& u64_part(parts[pc]).len() == n
    &&& text_col_ok(parts, po, pb, text_count(parts, po))
    &&& text_count(parts, po) >= 0
    &&& forall|i: int| 0 <= i < n && (pv < 0 || u8_part(parts[pv])[i] != 0)
        ==> #[trigger] u64_part(parts[pc])[i] < text_count(parts, po)
}

/// The `U64` part `p`.
pub open spec fn u64s(parts: Seq<PartView>, p: usize) -> Seq<u64> {
    u64_part(parts[p as int])
}

/// Value `k` of the text list in parts `po` (offsets) and `po + 1` (bytes).
pub open spec fn list_entry(parts: Seq<PartView>, po: usize, k: int) -> Seq<u8> {
    text_entry(u64_part(parts[po as int]), u8_part(parts[po + 1]), k)
}

/// Parts `po`, `po + 1` hold a sorted dictionary (`text_strictly_sorted`) of `text_count(parts, po)` values.
pub open spec fn sorted_list_ok(parts: Seq<PartView>, po: usize) -> bool {
    &&& text_count(parts, po as int) >= 0
    &&& text_col_ok(parts, po as int, po + 1, text_count(parts, po as int))
    &&& super::text::text_strictly_sorted(u64_part(parts[po as int]), u8_part(parts[po + 1]), text_count(parts, po as int))
}

/// Row `i` of a dictionary text column with codes in part `pc` into the list at `po`: NULL when `pv >= 0` and
/// validity part `pv` holds 0 at `i`.
pub open spec fn coded_text_at(parts: Seq<PartView>, pc: usize, pv: int, po: usize, i: int) -> Val {
    if pv >= 0 && u8_part(parts[pv])[i] == 0 {
        Val::Null
    } else {
        Val::Text(list_entry(parts, po, u64s(parts, pc)[i] as int))
    }
}

/// Codes part `pc` (`n` entries) points into the list at `po` for every row that is not NULL (validity `pv`, or
/// every row when `pv < 0`).
pub open spec fn coded_col_ok(parts: Seq<PartView>, pc: usize, pv: int, po: usize, n: int) -> bool {
    &&& parts[pc as int] is U64
    &&& u64s(parts, pc).len() == n
    &&& pv >= 0 ==> parts[pv] is U8 && u8_part(parts[pv]).len() == n
    &&& sorted_list_ok(parts, po)
    &&& forall|i: int| 0 <= i < n && !(pv >= 0 && u8_part(parts[pv])[i] == 0)
        ==> #[trigger] u64s(parts, pc)[i] < text_count(parts, po as int)
}

} // verus!
