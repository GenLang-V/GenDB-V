//! Storage `sub_sic`: storage `sub_fy` (its 46 parts: storage `sub`'s 44, then `fy_order` and `adsh_rank`, inherited
//! unchanged) extended by the permutation `sic_order`.
//!
//! Layout of the inherited parts (part indices are the `P_*` constants; `n` = row count, every per-row part has `n`
//! entries): the `sub` table (one row per filing) in canonical row order, column by column.
//! - `int4` columns: one `I32` part each (`cik`, `sic`, `period`, `fy`, `filed`, `prevrpt`, `nciks`, `wksi`).
//! - nullable columns: one more `U8` validity part (0: the row is NULL; the value part's entry then means nothing).
//! - text columns: flat text, a `U64` offsets part (`n + 1` entries) and a `U8` bytes part; row `i` is
//!   `bytes[offsets[i] .. offsets[i + 1]]` (`common::text::text_entry`).
//! - `name`: dictionary text: `U64` codes per row into a sorted dictionary (distinct names in strictly increasing
//!   byte order, `common::text::text_strictly_sorted`): equal codes are equal names, code order is name order.
//! - `adsh_order` (`P_ADSH_ORDER`, `U64`, `n` entries): a permutation of the row positions `0..n` that lists the
//!   rows by nondecreasing `adsh` (byte order).
//! The new parts:
//! - `fy_order` (`P_FY_ORDER`, `U64`, `n` entries): a permutation of the row positions `0..n` that lists the rows by
//!   the key `(fy, cik, name code, row)` (`row_key`, lexicographic; NULL `fy` first). The rows of one fiscal year are
//!   one contiguous range (found by binary search), inside it grouped by `cik` and then by `name`.
//! - `adsh_rank` (`P_ADSH_RANK`, `U64`, `n` entries): the position of each row in `adsh_order`
//!   (`adsh_order[adsh_rank[i]] == i`): the rank of the row's `adsh` among all rows, for example to look the row up in
//!   another sorted list of the same `adsh` values near that rank.
//! - `sic_order` (`P_SIC_ORDER`, `U64`, `n` entries): a permutation of the row positions `0..n` that lists the rows by
//!   the key `(sic, cik, row)` (`sic_key`, lexicographic; NULL `sic` first). The rows of a `sic` range are one
//!   contiguous range (found by binary search), inside it ordered by `(sic, cik)`.
//! Row `i` of the relation is `sub_row_ok(parts, rels[0][i], i)`: each column's value from its parts.
use vstd::prelude::*;
use crate::spec::value::{Row, Val};
use crate::spec::text::lex_cmp;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
pub mod common;
use common::text::{text_entry, text_parts_wf, text_strictly_sorted, u64_part, u8_part};
use common::cols::*;
use common::perm::is_permutation;

verus! {

pub const P_ADSH_OFF: usize = 0;
pub const P_ADSH_BYTES: usize = 1;
pub const P_ADSH_ORDER: usize = 2;
pub const P_CIK: usize = 3;
pub const P_NAME_CODES: usize = 4;
pub const P_NAME_DICT_OFF: usize = 5;
pub const P_NAME_DICT_BYTES: usize = 6;
pub const P_SIC: usize = 7;
pub const P_SIC_VALID: usize = 8;
pub const P_COUNTRYBA_OFF: usize = 9;
pub const P_COUNTRYBA_BYTES: usize = 10;
pub const P_COUNTRYBA_VALID: usize = 11;
pub const P_STPRBA_OFF: usize = 12;
pub const P_STPRBA_BYTES: usize = 13;
pub const P_STPRBA_VALID: usize = 14;
pub const P_CITYBA_OFF: usize = 15;
pub const P_CITYBA_BYTES: usize = 16;
pub const P_CITYBA_VALID: usize = 17;
pub const P_COUNTRYINC_OFF: usize = 18;
pub const P_COUNTRYINC_BYTES: usize = 19;
pub const P_COUNTRYINC_VALID: usize = 20;
pub const P_FORM_OFF: usize = 21;
pub const P_FORM_BYTES: usize = 22;
pub const P_PERIOD: usize = 23;
pub const P_PERIOD_VALID: usize = 24;
pub const P_FY: usize = 25;
pub const P_FY_VALID: usize = 26;
pub const P_FP_OFF: usize = 27;
pub const P_FP_BYTES: usize = 28;
pub const P_FP_VALID: usize = 29;
pub const P_FILED: usize = 30;
pub const P_ACCEPTED_OFF: usize = 31;
pub const P_ACCEPTED_BYTES: usize = 32;
pub const P_PREVRPT: usize = 33;
pub const P_NCIKS: usize = 34;
pub const P_AFS_OFF: usize = 35;
pub const P_AFS_BYTES: usize = 36;
pub const P_AFS_VALID: usize = 37;
pub const P_WKSI: usize = 38;
pub const P_FYE_OFF: usize = 39;
pub const P_FYE_BYTES: usize = 40;
pub const P_FYE_VALID: usize = 41;
pub const P_INSTANCE_OFF: usize = 42;
pub const P_INSTANCE_BYTES: usize = 43;
pub const P_FY_ORDER: usize = 44;
pub const P_ADSH_RANK: usize = 45;
pub const P_SIC_ORDER: usize = 46;
pub const PART_COUNT: usize = 47;

/// Row count: the length of the `cik` part.
pub open spec fn row_count(parts: Seq<PartView>) -> int {
    i32_part(parts[P_CIK as int]).len() as int
}

/// `adsh` of row `i` (bytes).
pub open spec fn adsh_bytes(parts: Seq<PartView>, i: int) -> Seq<u8> {
    text_entry(u64_part(parts[P_ADSH_OFF as int]), u8_part(parts[P_ADSH_BYTES as int]), i)
}

/// The sort permutation of `adsh`.
pub open spec fn adsh_order(parts: Seq<PartView>) -> Seq<u64> {
    u64_part(parts[P_ADSH_ORDER as int])
}

/// The fiscal-year order: a permutation of the rows.
pub open spec fn fy_order(parts: Seq<PartView>) -> Seq<u64> {
    u64_part(parts[P_FY_ORDER as int])
}

/// The rank of each row in `adsh_order`.
pub open spec fn adsh_rank(parts: Seq<PartView>) -> Seq<u64> {
    u64_part(parts[P_ADSH_RANK as int])
}

/// The sic order: a permutation of the rows.
pub open spec fn sic_order(parts: Seq<PartView>) -> Seq<u64> {
    u64_part(parts[P_SIC_ORDER as int])
}

/// Sort word of `sic` of row `i`: 0 when NULL, else `sic + 2^31 + 1` (order preserving, above every NULL).
pub open spec fn sic_word(parts: Seq<PartView>, i: int) -> u64 {
    if u8_part(parts[P_SIC_VALID as int])[i] == 0 {
        0
    } else {
        (i32_part(parts[P_SIC as int])[i] as int + 0x8000_0001) as u64
    }
}

/// The sort key of row `i` in `sic_order`: `(sic word, cik word, 0, row)`.
pub open spec fn sic_key(parts: Seq<PartView>, i: int) -> (u64, u64, u64, u64) {
    (sic_word(parts, i), cik_word(parts, i), 0, i as u64)
}

/// Sort word of `fy` of row `i`: 0 when NULL, else `fy + 2^31 + 1` (order preserving, above every NULL).
pub open spec fn fy_word(parts: Seq<PartView>, i: int) -> u64 {
    if u8_part(parts[P_FY_VALID as int])[i] == 0 {
        0
    } else {
        (i32_part(parts[P_FY as int])[i] as int + 0x8000_0001) as u64
    }
}

/// Sort word of `cik` of row `i`: `cik + 2^31` (order preserving, nonnegative).
pub open spec fn cik_word(parts: Seq<PartView>, i: int) -> u64 {
    (i32_part(parts[P_CIK as int])[i] as int + 0x8000_0000) as u64
}

/// The sort key of row `i` in `fy_order`: `(fy word, cik word, name code, row)`.
pub open spec fn row_key(parts: Seq<PartView>, i: int) -> (u64, u64, u64, u64) {
    (fy_word(parts, i), cik_word(parts, i), u64_part(parts[P_NAME_CODES as int])[i], i as u64)
}

/// Lexicographic order of sort keys.
pub open spec fn key_le(a: (u64, u64, u64, u64), b: (u64, u64, u64, u64)) -> bool {
    a.0 < b.0 || (a.0 == b.0 && (a.1 < b.1 || (a.1 == b.1 && (a.2 < b.2 || (a.2 == b.2 && a.3 <= b.3)))))
}

/// Every part has its type and length; `fy_order` is a permutation sorted by `row_key`; `adsh_rank` inverts
/// `adsh_order`; `sic_order` is a permutation sorted by `sic_key`.
pub open spec fn sub_layout_ok(parts: Seq<PartView>) -> bool {
    let n = row_count(parts);
    &&& parts.len() == PART_COUNT
    &&& text_col_ok(parts, P_ADSH_OFF as int, P_ADSH_BYTES as int, n)
    &&& parts[P_ADSH_ORDER as int] is U64
    &&& is_permutation(adsh_order(parts), n as nat)
    &&& forall|a: int, b: int| 0 <= a < b < n
        ==> lex_cmp(adsh_bytes(parts, #[trigger] adsh_order(parts)[a] as int), adsh_bytes(parts, #[trigger] adsh_order(parts)[b] as int)) <= 0
    &&& i32_col_ok(parts, P_CIK as int, n)
    &&& dict_col_ok(parts, P_NAME_CODES as int, P_NAME_DICT_OFF as int, P_NAME_DICT_BYTES as int, -1, n)
    &&& text_strictly_sorted(u64_part(parts[P_NAME_DICT_OFF as int]), u8_part(parts[P_NAME_DICT_BYTES as int]),
        text_count(parts, P_NAME_DICT_OFF as int))
    &&& i32_col_ok(parts, P_SIC as int, n) && valid_col_ok(parts, P_SIC_VALID as int, n)
    &&& text_col_ok(parts, P_COUNTRYBA_OFF as int, P_COUNTRYBA_BYTES as int, n) && valid_col_ok(parts, P_COUNTRYBA_VALID as int, n)
    &&& text_col_ok(parts, P_STPRBA_OFF as int, P_STPRBA_BYTES as int, n) && valid_col_ok(parts, P_STPRBA_VALID as int, n)
    &&& text_col_ok(parts, P_CITYBA_OFF as int, P_CITYBA_BYTES as int, n) && valid_col_ok(parts, P_CITYBA_VALID as int, n)
    &&& text_col_ok(parts, P_COUNTRYINC_OFF as int, P_COUNTRYINC_BYTES as int, n) && valid_col_ok(parts, P_COUNTRYINC_VALID as int, n)
    &&& text_col_ok(parts, P_FORM_OFF as int, P_FORM_BYTES as int, n)
    &&& i32_col_ok(parts, P_PERIOD as int, n) && valid_col_ok(parts, P_PERIOD_VALID as int, n)
    &&& i32_col_ok(parts, P_FY as int, n) && valid_col_ok(parts, P_FY_VALID as int, n)
    &&& text_col_ok(parts, P_FP_OFF as int, P_FP_BYTES as int, n) && valid_col_ok(parts, P_FP_VALID as int, n)
    &&& i32_col_ok(parts, P_FILED as int, n)
    &&& text_col_ok(parts, P_ACCEPTED_OFF as int, P_ACCEPTED_BYTES as int, n)
    &&& i32_col_ok(parts, P_PREVRPT as int, n)
    &&& i32_col_ok(parts, P_NCIKS as int, n)
    &&& text_col_ok(parts, P_AFS_OFF as int, P_AFS_BYTES as int, n) && valid_col_ok(parts, P_AFS_VALID as int, n)
    &&& i32_col_ok(parts, P_WKSI as int, n)
    &&& text_col_ok(parts, P_FYE_OFF as int, P_FYE_BYTES as int, n) && valid_col_ok(parts, P_FYE_VALID as int, n)
    &&& text_col_ok(parts, P_INSTANCE_OFF as int, P_INSTANCE_BYTES as int, n)
    &&& parts[P_FY_ORDER as int] is U64
    &&& is_permutation(fy_order(parts), n as nat)
    &&& forall|a: int, b: int| 0 <= a < b < n
        ==> key_le(row_key(parts, #[trigger] fy_order(parts)[a] as int), row_key(parts, #[trigger] fy_order(parts)[b] as int))
    &&& parts[P_ADSH_RANK as int] is U64
    &&& adsh_rank(parts).len() == n
    &&& forall|q: int| 0 <= q < n ==> adsh_rank(parts)[#[trigger] adsh_order(parts)[q] as int] == q
    &&& parts[P_SIC_ORDER as int] is U64
    &&& is_permutation(sic_order(parts), n as nat)
    &&& forall|a: int, b: int| 0 <= a < b < n
        ==> key_le(sic_key(parts, #[trigger] sic_order(parts)[a] as int), sic_key(parts, #[trigger] sic_order(parts)[b] as int))
}

/// Row `i` of `sub` from the parts: one value per column, in column order.
pub open spec fn sub_row_ok(parts: Seq<PartView>, r: Row, i: int) -> bool {
    &&& r.len() == 20
    &&& r[0] == flat_text_at(parts, P_ADSH_OFF as int, P_ADSH_BYTES as int, i)
    &&& r[1] == int_at(parts, P_CIK as int, i)
    &&& r[2] == dict_text_at(parts, P_NAME_CODES as int, P_NAME_DICT_OFF as int, P_NAME_DICT_BYTES as int, i)
    &&& r[3] == or_null_at(parts, P_SIC_VALID as int, i, int_at(parts, P_SIC as int, i))
    &&& r[4] == or_null_at(parts, P_COUNTRYBA_VALID as int, i, flat_text_at(parts, P_COUNTRYBA_OFF as int, P_COUNTRYBA_BYTES as int, i))
    &&& r[5] == or_null_at(parts, P_STPRBA_VALID as int, i, flat_text_at(parts, P_STPRBA_OFF as int, P_STPRBA_BYTES as int, i))
    &&& r[6] == or_null_at(parts, P_CITYBA_VALID as int, i, flat_text_at(parts, P_CITYBA_OFF as int, P_CITYBA_BYTES as int, i))
    &&& r[7] == or_null_at(parts, P_COUNTRYINC_VALID as int, i, flat_text_at(parts, P_COUNTRYINC_OFF as int, P_COUNTRYINC_BYTES as int, i))
    &&& r[8] == flat_text_at(parts, P_FORM_OFF as int, P_FORM_BYTES as int, i)
    &&& r[9] == or_null_at(parts, P_PERIOD_VALID as int, i, int_at(parts, P_PERIOD as int, i))
    &&& r[10] == or_null_at(parts, P_FY_VALID as int, i, int_at(parts, P_FY as int, i))
    &&& r[11] == or_null_at(parts, P_FP_VALID as int, i, flat_text_at(parts, P_FP_OFF as int, P_FP_BYTES as int, i))
    &&& r[12] == int_at(parts, P_FILED as int, i)
    &&& r[13] == flat_text_at(parts, P_ACCEPTED_OFF as int, P_ACCEPTED_BYTES as int, i)
    &&& r[14] == int_at(parts, P_PREVRPT as int, i)
    &&& r[15] == int_at(parts, P_NCIKS as int, i)
    &&& r[16] == or_null_at(parts, P_AFS_VALID as int, i, flat_text_at(parts, P_AFS_OFF as int, P_AFS_BYTES as int, i))
    &&& r[17] == int_at(parts, P_WKSI as int, i)
    &&& r[18] == or_null_at(parts, P_FYE_VALID as int, i, flat_text_at(parts, P_FYE_OFF as int, P_FYE_BYTES as int, i))
    &&& r[19] == flat_text_at(parts, P_INSTANCE_OFF as int, P_INSTANCE_BYTES as int, i)
}

/// The parts hold the `sub` relation row for row, in canonical row order.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& sub_layout_ok(parts)
    &&& rels.len() == 1
    &&& rels[0].len() == row_count(parts)
    &&& forall|i: int| 0 <= i < row_count(parts) ==> sub_row_ok(parts, #[trigger] rels[0][i], i)
}

/// Lossless: every value of every row is a function of the parts.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    assert forall|i: int| 0 <= i < a[0].len() implies #[trigger] a[0][i] == b[0][i] by {
        assert(sub_row_ok(parts, a[0][i], i) && sub_row_ok(parts, b[0][i], i));
        assert(a[0][i] =~= b[0][i]);
    }
    assert(a[0] =~= b[0]);
    assert(a =~= b);
}

/// Number of rows.
pub fn read_row_count(st: &StoredParts) -> (n: usize)
    requires st@.len() == PART_COUNT, sub_layout_ok(st@),
    ensures n == row_count(st@),
{
    st.part_len(P_CIK)
}

} // verus!
