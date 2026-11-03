//! Storage `tag_tv`: storage `tag` (its 28 parts, inherited unchanged) extended by a (tag, version) key index over
//! its `tv_order`.
//!
//! Inherited layout (part indices are the `P_*` constants; every per-row part has `n` entries, row `i` is relation
//! row `i`):
//! - text columns (`tag`, `version`, `datatype`, `iord`, `crdr`, `tlabel`, `doc`): a `U64` code per row into a sorted
//!   dictionary (distinct values in strictly increasing byte order, `common::text::text_strictly_sorted`): equal codes
//!   are equal values and code order is byte order. Nullable columns have a `U8` validity part (0: NULL; the code then
//!   means nothing).
//! - `custom`, `abstract`: `I32`.
//! - `tv_order` (`P_TV_ORDER`, `U64`, `n` entries): a permutation of the row positions listing the rows by
//!   nondecreasing (tag code, version code), i.e. by (tag, version) in byte order.
//! The new parts (the index keys of `tv_order`, so a (tag, version) lookup reads two short sequential ranges instead of
//! the rows behind the permutation):
//! - `tag_first` (`P_TAG_FIRST`, `U64`, `T + 1` entries for `T` tag codes): `tag_first[c]` is the number of `tv_order`
//!   positions whose row has a tag code below `c`, so the rows of tag code `c` are the positions
//!   `[tag_first[c], tag_first[c + 1])` (`tag_first_ok`).
//! - `tv_version` (`P_TV_VERSION`, `U64`, `n` entries): the version code of the row at each `tv_order` position
//!   (`tv_version[k] == version code of row tv_order[k]`), nondecreasing inside one tag code's positions.
use vstd::prelude::*;
use crate::spec::value::{Row, Val};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
pub mod common;
use common::cols::{i32_part, u64s, coded_text_at, coded_col_ok};
use common::perm::is_permutation;

verus! {

pub const P_TAG_CODES: usize = 0;
pub const P_TAG_OFF: usize = 1;
pub const P_TAG_BYTES: usize = 2;
pub const P_VERSION_CODES: usize = 3;
pub const P_VERSION_OFF: usize = 4;
pub const P_VERSION_BYTES: usize = 5;
pub const P_TV_ORDER: usize = 6;
pub const P_CUSTOM: usize = 7;
pub const P_ABSTRACT: usize = 8;
pub const P_DATATYPE_CODES: usize = 9;
pub const P_DATATYPE_VALID: usize = 10;
pub const P_DATATYPE_OFF: usize = 11;
pub const P_DATATYPE_BYTES: usize = 12;
pub const P_IORD_CODES: usize = 13;
pub const P_IORD_OFF: usize = 14;
pub const P_IORD_BYTES: usize = 15;
pub const P_CRDR_CODES: usize = 16;
pub const P_CRDR_VALID: usize = 17;
pub const P_CRDR_OFF: usize = 18;
pub const P_CRDR_BYTES: usize = 19;
pub const P_TLABEL_CODES: usize = 20;
pub const P_TLABEL_VALID: usize = 21;
pub const P_TLABEL_OFF: usize = 22;
pub const P_TLABEL_BYTES: usize = 23;
pub const P_DOC_CODES: usize = 24;
pub const P_DOC_VALID: usize = 25;
pub const P_DOC_OFF: usize = 26;
pub const P_DOC_BYTES: usize = 27;
pub const P_TAG_FIRST: usize = 28;
pub const P_TV_VERSION: usize = 29;
pub const PART_COUNT: usize = 30;

/// Row count `n`.
pub open spec fn row_count(parts: Seq<PartView>) -> int {
    i32_part(parts[P_CUSTOM as int]).len() as int
}

/// `(a0, a1)` sorts before or together with `(b0, b1)` lexicographically.
pub open spec fn pair_le(a0: u64, a1: u64, b0: u64, b1: u64) -> bool {
    a0 < b0 || (a0 == b0 && a1 <= b1)
}

/// Tag code of the row at `tv_order` position `k`.
pub open spec fn tv_tag(parts: Seq<PartView>, k: int) -> u64 {
    u64s(parts, P_TAG_CODES)[u64s(parts, P_TV_ORDER)[k] as int]
}

/// `tag_first` cuts the `tv_order` positions by tag code: below `tag_first[c]` exactly the positions whose row's tag
/// code is below `c` (`c` up to the tag count).
pub open spec fn tag_first_ok(parts: Seq<PartView>) -> bool {
    let n = row_count(parts);
    let first = u64s(parts, P_TAG_FIRST);
    let nt = common::cols::text_count(parts, P_TAG_OFF as int);
    &&& parts[P_TAG_FIRST as int] is U64
    &&& first.len() == nt + 1
    &&& forall|c: int| 0 <= c <= nt ==> #[trigger] first[c] <= n
    &&& forall|c: int, k: int| 0 <= c <= nt && 0 <= k < n ==> (k < #[trigger] first[c] <==> #[trigger] tv_tag(parts, k) < c)
}

/// `tv_version` holds the version code of the row at each `tv_order` position.
pub open spec fn tv_version_ok(parts: Seq<PartView>) -> bool {
    let n = row_count(parts);
    &&& parts[P_TV_VERSION as int] is U64
    &&& u64s(parts, P_TV_VERSION).len() == n
    &&& forall|k: int| 0 <= k < n ==> #[trigger] u64s(parts, P_TV_VERSION)[k] == u64s(parts, P_VERSION_CODES)[u64s(parts, P_TV_ORDER)[k] as int]
}

/// Every part has its type and length; `tv_order` is a permutation sorted by (tag code, version code); the key index
/// describes it.
pub open spec fn tag_layout_ok(parts: Seq<PartView>) -> bool {
    let n = row_count(parts);
    let order = u64s(parts, P_TV_ORDER);
    let tc = u64s(parts, P_TAG_CODES);
    let vc = u64s(parts, P_VERSION_CODES);
    &&& parts.len() == PART_COUNT
    &&& parts[P_CUSTOM as int] is I32 && parts[P_ABSTRACT as int] is I32 && parts[P_TV_ORDER as int] is U64
    &&& i32_part(parts[P_ABSTRACT as int]).len() == n
    &&& coded_col_ok(parts, P_TAG_CODES, -1, P_TAG_OFF, n)
    &&& coded_col_ok(parts, P_VERSION_CODES, -1, P_VERSION_OFF, n)
    &&& is_permutation(order, n as nat)
    &&& forall|a: int, b: int| 0 <= a < b < n
        ==> pair_le(tc[#[trigger] order[a] as int], vc[order[a] as int], tc[#[trigger] order[b] as int], vc[order[b] as int])
    &&& coded_col_ok(parts, P_DATATYPE_CODES, P_DATATYPE_VALID as int, P_DATATYPE_OFF, n)
    &&& coded_col_ok(parts, P_IORD_CODES, -1, P_IORD_OFF, n)
    &&& coded_col_ok(parts, P_CRDR_CODES, P_CRDR_VALID as int, P_CRDR_OFF, n)
    &&& coded_col_ok(parts, P_TLABEL_CODES, P_TLABEL_VALID as int, P_TLABEL_OFF, n)
    &&& coded_col_ok(parts, P_DOC_CODES, P_DOC_VALID as int, P_DOC_OFF, n)
    &&& tag_first_ok(parts)
    &&& tv_version_ok(parts)
}

/// Row `i` of `tag` from the parts: one value per column, in column order.
pub open spec fn tag_row_ok(parts: Seq<PartView>, r: Row, i: int) -> bool {
    &&& r.len() == 9
    &&& r[0] == coded_text_at(parts, P_TAG_CODES, -1, P_TAG_OFF, i)
    &&& r[1] == coded_text_at(parts, P_VERSION_CODES, -1, P_VERSION_OFF, i)
    &&& r[2] == Val::Int(i32_part(parts[P_CUSTOM as int])[i] as int)
    &&& r[3] == Val::Int(i32_part(parts[P_ABSTRACT as int])[i] as int)
    &&& r[4] == coded_text_at(parts, P_DATATYPE_CODES, P_DATATYPE_VALID as int, P_DATATYPE_OFF, i)
    &&& r[5] == coded_text_at(parts, P_IORD_CODES, -1, P_IORD_OFF, i)
    &&& r[6] == coded_text_at(parts, P_CRDR_CODES, P_CRDR_VALID as int, P_CRDR_OFF, i)
    &&& r[7] == coded_text_at(parts, P_TLABEL_CODES, P_TLABEL_VALID as int, P_TLABEL_OFF, i)
    &&& r[8] == coded_text_at(parts, P_DOC_CODES, P_DOC_VALID as int, P_DOC_OFF, i)
}

/// The parts hold the `tag` relation row for row, in canonical row order.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& tag_layout_ok(parts)
    &&& rels.len() == 1
    &&& rels[0].len() == row_count(parts)
    &&& forall|i: int| 0 <= i < row_count(parts) ==> tag_row_ok(parts, #[trigger] rels[0][i], i)
}

/// Lossless: every value of every row is a function of the parts.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    assert forall|i: int| 0 <= i < a[0].len() implies #[trigger] a[0][i] == b[0][i] by {
        assert(tag_row_ok(parts, a[0][i], i) && tag_row_ok(parts, b[0][i], i));
        assert(a[0][i] =~= b[0][i]);
    }
    assert(a[0] =~= b[0]);
    assert(a =~= b);
}

/// Number of rows.
pub fn read_row_count(st: &StoredParts) -> (n: usize)
    requires tag_layout_ok(st@),
    ensures n == row_count(st@),
{
    st.part_len(P_CUSTOM)
}

} // verus!
