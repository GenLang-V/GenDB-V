//! Storage `cust_phoneidx`: storage `custpart` unchanged (its 50 parts, inherited), followed by two parts that
//! order the customer rows by country code, `SUBSTRING(c_phone, 1, 2)`:
//! - `PHONE_PERM` (U32): empty (no index) or `n` row positions, a bijection of `[0, n)`;
//! - `PHONE_RUNS` (U64): empty (no index) or `m + 1 >= 2` run starts from 0 to `n`, strictly increasing: every
//!   position of run `t`, `PHONE_RUNS[t] .. PHONE_RUNS[t + 1]`, names a row with the country code of the run's first
//!   row (`same_code_at`). So the rows of any set of country codes are a union of whole runs.
//! The builder orders rows by their first two phone bytes, then by row (stable), so a run lists its rows in
//! ascending row order; that is a performance property only and is not stated here.
//!
//! What this interface states about the inherited parts (the stored relation is customer projected on `[c_phone]`,
//! canonical row order, stored row `r` is canonical row `r`): c_phone of row `r` is `bytes[offs[r] .. offs[r + 1]]`
//! (`CU_PHONE_OFFS` U64, `n + 1` offsets; `CU_PHONE_BYTES` U8). Every new stored value is a row position or a run
//! offset: no column value is stored.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
use crate::spec::chars::chars;
use crate::spec::fns::substring::{char_range, substring_end};

verus! {

// ------------------------------------------------------------------------------------------------ part indices

/// customer: U64 offsets of c_phone (`rows + 1`; custpart's `CUSTOMER_FIRST + CU_PHONE_OFFS`).
pub const CU_PHONE_OFFS: usize = 10;
/// customer: U8 bytes of c_phone.
pub const CU_PHONE_BYTES: usize = 11;
/// Number of inherited parts (storage custpart).
pub const CUSTPART_PARTS: usize = 50;
/// The country-code order: U32 row positions (empty, or one per customer row).
pub const PHONE_PERM: usize = 50;
/// The run starts of the country-code order: U64 positions (empty, or `m + 1` from 0 to `n`).
pub const PHONE_RUNS: usize = 51;
/// Number of parts of storage cust_phoneidx.
pub const PHONEIDX_PARTS: usize = 52;

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

// ------------------------------------------------------------------------------------------------ part values

/// `SUBSTRING(b FROM 1 FOR 2)`: the first two characters of the text `b`.
pub open spec fn country_code(b: Seq<u8>) -> Seq<u8> {
    char_range(chars(b), 1, substring_end(1, 2))
}

/// The c_phone offsets.
pub open spec fn phone_offs(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[CU_PHONE_OFFS as int])
}

/// The c_phone bytes.
pub open spec fn phone_bytes(parts: Seq<PartView>) -> Seq<u8> {
    u8s(parts[CU_PHONE_BYTES as int])
}

/// c_phone of row `r`.
pub open spec fn phone_at(parts: Seq<PartView>, r: int) -> Seq<u8> {
    phone_bytes(parts).subrange(phone_offs(parts)[r] as int, phone_offs(parts)[r + 1] as int)
}

/// The country-code order.
pub open spec fn perm(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[PHONE_PERM as int])
}

/// The run starts.
pub open spec fn runs(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[PHONE_RUNS as int])
}

/// Row `r`'s phone is a byte range inside the bytes part.
pub open spec fn phone_range_ok(parts: Seq<PartView>, r: int) -> bool {
    phone_offs(parts)[r] <= phone_offs(parts)[r + 1] && phone_offs(parts)[r + 1] <= phone_bytes(parts).len()
}

/// The c_phone column of `n` rows and the kinds of the new parts.
pub open spec fn cu_shape(parts: Seq<PartView>, n: int) -> bool {
    &&& parts.len() == PHONEIDX_PARTS
    &&& parts[CU_PHONE_OFFS as int] is U64 && phone_offs(parts).len() == n + 1
    &&& parts[CU_PHONE_BYTES as int] is U8
    &&& forall|r: int| 0 <= r < n ==> #[trigger] phone_range_ok(parts, r)
    &&& parts[PHONE_PERM as int] is U32
    &&& parts[PHONE_RUNS as int] is U64
}

/// A stored relation row `[c_phone]`.
pub open spec fn cu_row(phone: Seq<u8>) -> Row {
    seq![Val::Text(phone)]
}

/// Row `r` of the relation holds the values of stored row `r`.
pub open spec fn rows_ok(parts: Seq<PartView>, rel: Seq<Row>) -> bool {
    forall|r: int| 0 <= r < rel.len() ==> #[trigger] rel[r] == cu_row(phone_at(parts, r))
}

/// Row `r` appears in the order.
pub open spec fn listed(p: Seq<u32>, r: int) -> bool {
    exists|i: int| 0 <= i < p.len() && #[trigger] p[i] == r
}

/// Position `j` lies in run `t`.
pub open spec fn in_run(rs: Seq<u64>, t: int, j: int) -> bool {
    rs[t] <= j < rs[t + 1]
}

/// The row at position `j` has the country code of the first row of run `t`.
pub open spec fn same_code_at(parts: Seq<PartView>, t: int, j: int) -> bool {
    country_code(phone_at(parts, perm(parts)[j] as int)) == country_code(phone_at(parts, perm(parts)[runs(parts)[t] as int] as int))
}

/// The index is present.
pub open spec fn has_index(parts: Seq<PartView>) -> bool {
    perm(parts).len() > 0
}

/// The country-code order over `n` rows: absent (both parts empty), or a bijection of `[0, n)` cut into runs of
/// one country code each.
pub open spec fn index_ok(parts: Seq<PartView>, n: int) -> bool {
    let (p, rs) = (perm(parts), runs(parts));
    let m = rs.len() - 1;
    &&& p.len() == 0 ==> rs.len() == 0
    &&& p.len() > 0 ==> {
        &&& p.len() == n
        &&& forall|i: int| 0 <= i < n ==> #[trigger] p[i] < n
        &&& forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> #[trigger] p[i] != #[trigger] p[j]
        &&& forall|r: int| 0 <= r < n ==> #[trigger] listed(p, r)
        &&& rs.len() >= 2
        &&& rs[0] == 0
        &&& rs[m] == n
        &&& forall|t: int| 0 <= t < m ==> #[trigger] rs[t] < rs[t + 1]
        &&& forall|t: int, j: int| 0 <= t < m && #[trigger] in_run(rs, t, j) ==> same_code_at(parts, t, j)
    }
}

// ------------------------------------------------------------------------------------------------ represents

/// The inherited parts hold customer's `[c_phone]` row for row; the new parts are the country-code order.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& rels.len() == 1
    &&& cu_shape(parts, rels[0].len() as int)
    &&& rows_ok(parts, rels[0])
    &&& index_ok(parts, rels[0].len() as int)
}

/// The parts determine the relation: every row's value is stored.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    assert(a[0].len() == b[0].len());
    assert forall|r: int| 0 <= r < a[0].len() implies a[0][r] == b[0][r] by {
        assert(a[0][r] == cu_row(phone_at(parts, r)));
        assert(b[0][r] == cu_row(phone_at(parts, r)));
    }
    assert(a[0] =~= b[0]);
    assert(a =~= b);
}

/// Runs cover their positions: run starts never decrease between any two runs `a <= b`.
pub proof fn lemma_runs_mono(rs: Seq<u64>, m: int, a: int, b: int)
    requires
        0 <= a <= b <= m < rs.len(),
        forall|t: int| 0 <= t < m ==> #[trigger] rs[t] < rs[t + 1],
    ensures
        rs[a] <= rs[b],
        a < b ==> rs[a] < rs[b],
    decreases b - a,
{
    if a < b {
        lemma_runs_mono(rs, m, a, b - 1);
    }
}

} // verus!
