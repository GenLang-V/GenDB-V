//! The two key directories of storage `factsdir`, over the inherited parts of storage `facts` (indices here are
//! indices into this storage's parts; lineitem's parts come first, orders' start at `ORDERS_FIRST`).
//!
//! - l_partkey directory (`PDIR_META` I64 `[mode, kmin]`, `PDIR_OFFS` U32, `nkeys + 1` offsets). In mode
//!   `MODE_DIRECTORY` the l_partkey key index of lineitem (`LI_KEYIDX_*`, kind 2: index position `p` holds stored
//!   row `pdir_irow(p)`) puts every position `p` in the entry of its key: `e = li_key(pdir_irow(p)) - kmin` lies in
//!   `[0, nkeys)` and `offs[e] <= p < offs[e + 1]`; offsets are nondecreasing from `offs[0] == 0` to
//!   `offs[nkeys] == n`. So the positions `offs[e] .. offs[e + 1]` hold exactly the stored rows of key `kmin + e`
//!   (`lemma_pdir_entry_exact`), and consecutive entries tile the index.
//! - o_orderkey directory (`ODIR_META` I64 `[mode, kmin]`, `ODIR_ROWS` U32, one entry per key of `[kmin, kmin +
//!   nkeys)`). In mode `MODE_DIRECTORY` entry `e` is `ODIR_NONE` or a stored orders row whose o_orderkey is
//!   `kmin + e`, and the entry of every stored orders row's key is not `ODIR_NONE` (complete): a key whose entry is
//!   `ODIR_NONE`, or outside the range, has no orders row.
//! Values: keys are bigint values; offsets are index positions (`0 .. lineitem rows`); orders entries are stored
//! orders rows. Every stored value is a row position or the first key of a directory's range: no column value.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use super::common::colfmt::{u32s, u64s, i64s};
use super::{LI_LAYOUT, LI_PARTKEY_CODES, LI_PARTKEY_BASE, LI_KEYIDX_CODES, LI_KEYIDX_BASE, LI_KEYIDX_KIND, ORDERS_FIRST,
    OR_LAYOUT, OR_ORDERKEY_CODES, OR_ORDERKEY_BASE, FACTS_PARTS};

verus! {

/// l_partkey directory header: I64 `[mode, kmin]`.
pub const PDIR_META: usize = 75;
/// l_partkey directory offsets: U32, `nkeys + 1` positions of the l_partkey key index.
pub const PDIR_OFFS: usize = 76;
/// o_orderkey directory header: I64 `[mode, kmin]`.
pub const ODIR_META: usize = 77;
/// o_orderkey directory entries: U32 stored orders rows (or `ODIR_NONE`), one per key.
pub const ODIR_ROWS: usize = 78;
/// Number of parts of storage factsdir.
pub const FACTSDIR_PARTS: usize = 79;
/// The mode of a present directory.
pub const MODE_DIRECTORY: i64 = 1;
/// An o_orderkey directory entry for a key no orders row has.
pub const ODIR_NONE: u32 = 0xffff_ffff;

// ------------------------------------------------------------------------------------------------ lineitem keys

/// Rows per block of lineitem's frame-of-reference columns.
pub open spec fn li_bs(parts: Seq<PartView>) -> int {
    u64s(parts[LI_LAYOUT as int])[1] as int
}

/// l_partkey of stored lineitem row `s`.
pub open spec fn li_key(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[LI_PARTKEY_BASE as int])[s / li_bs(parts)] + u32s(parts[LI_PARTKEY_CODES as int])[s]
}

/// Stored lineitem row at position `p` of the l_partkey key index.
pub open spec fn pdir_irow(parts: Seq<PartView>, p: int) -> int {
    u64s(parts[LI_KEYIDX_BASE as int])[p / li_bs(parts)] + u32s(parts[LI_KEYIDX_CODES as int])[p]
}

/// l_partkey directory header.
pub open spec fn pdir_meta(parts: Seq<PartView>) -> Seq<i64> {
    i64s(parts[PDIR_META as int])
}

/// l_partkey directory offsets.
pub open spec fn pdir_offs(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[PDIR_OFFS as int])
}

/// The l_partkey directory is present.
pub open spec fn has_pdir(parts: Seq<PartView>) -> bool {
    pdir_meta(parts)[0] == MODE_DIRECTORY
}

/// First key of the l_partkey directory's range.
pub open spec fn pdir_kmin(parts: Seq<PartView>) -> int {
    pdir_meta(parts)[1] as int
}

/// Number of keys of the l_partkey directory's range.
pub open spec fn pdir_nkeys(parts: Seq<PartView>) -> int {
    pdir_offs(parts).len() - 1
}

/// Index position `p` lies in the directory entry of its key.
pub open spec fn in_pentry(parts: Seq<PartView>, p: int) -> bool {
    let e = li_key(parts, pdir_irow(parts, p)) - pdir_kmin(parts);
    &&& 0 <= e < pdir_nkeys(parts)
    &&& pdir_offs(parts)[e] <= p < pdir_offs(parts)[e + 1]
}

/// The l_partkey directory over the `n` positions of lineitem's l_partkey key index (kind 2).
pub open spec fn pdir_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts.len() == FACTSDIR_PARTS
    &&& parts[PDIR_META as int] is I64 && pdir_meta(parts).len() == 2
    &&& parts[PDIR_OFFS as int] is U32
    &&& has_pdir(parts) ==> {
        &&& u64s(parts[LI_KEYIDX_KIND as int]).len() == 1 && u64s(parts[LI_KEYIDX_KIND as int])[0] == 2
        &&& pdir_offs(parts).len() >= 1
        &&& pdir_offs(parts)[0] == 0
        &&& pdir_offs(parts)[pdir_nkeys(parts)] == n
        &&& forall|e: int| 0 <= e < pdir_nkeys(parts) ==> #[trigger] pdir_offs(parts)[e] <= pdir_offs(parts)[e + 1]
        &&& forall|p: int| 0 <= p < n ==> #[trigger] in_pentry(parts, p)
    }
}

/// Offsets are nondecreasing over any span of entries.
pub proof fn lemma_pdir_mono(parts: Seq<PartView>, n: int, a: int, b: int)
    requires
        pdir_ok(parts, n),
        has_pdir(parts),
        0 <= a <= b <= pdir_nkeys(parts),
    ensures
        pdir_offs(parts)[a] <= pdir_offs(parts)[b],
    decreases b - a,
{
    if a < b {
        lemma_pdir_mono(parts, n, a, b - 1);
        assert(pdir_offs(parts)[b - 1] <= pdir_offs(parts)[b]);
    }
}

/// The positions of entry `e` are exactly the positions whose stored row has key `kmin + e`.
pub proof fn lemma_pdir_entry_exact(parts: Seq<PartView>, n: int, e: int, p: int)
    requires
        pdir_ok(parts, n),
        has_pdir(parts),
        0 <= e < pdir_nkeys(parts),
        0 <= p < n,
    ensures
        (pdir_offs(parts)[e] <= p < pdir_offs(parts)[e + 1]) <==> li_key(parts, pdir_irow(parts, p)) == pdir_kmin(parts) + e,
        pdir_offs(parts)[e] <= pdir_offs(parts)[e + 1] <= n,
{
    assert(in_pentry(parts, p));
    let f = li_key(parts, pdir_irow(parts, p)) - pdir_kmin(parts);
    lemma_pdir_mono(parts, n, e + 1, pdir_nkeys(parts));
    if pdir_offs(parts)[e] <= p < pdir_offs(parts)[e + 1] && f != e {
        if f < e {
            lemma_pdir_mono(parts, n, f + 1, e);
        } else {
            lemma_pdir_mono(parts, n, e + 1, f);
        }
    }
}

// ------------------------------------------------------------------------------------------------ orders keys

/// Rows per block of orders' frame-of-reference columns.
pub open spec fn or_bs(parts: Seq<PartView>) -> int {
    u64s(parts[(ORDERS_FIRST + OR_LAYOUT) as int])[1] as int
}

/// o_orderkey of stored orders row `p`.
pub open spec fn or_key(parts: Seq<PartView>, p: int) -> int {
    i64s(parts[(ORDERS_FIRST + OR_ORDERKEY_BASE) as int])[p / or_bs(parts)]
        + u32s(parts[(ORDERS_FIRST + OR_ORDERKEY_CODES) as int])[p]
}

/// o_orderkey directory header.
pub open spec fn odir_meta(parts: Seq<PartView>) -> Seq<i64> {
    i64s(parts[ODIR_META as int])
}

/// o_orderkey directory entries.
pub open spec fn odir_rows(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[ODIR_ROWS as int])
}

/// The o_orderkey directory is present.
pub open spec fn has_odir(parts: Seq<PartView>) -> bool {
    odir_meta(parts)[0] == MODE_DIRECTORY
}

/// First key of the o_orderkey directory's range.
pub open spec fn odir_kmin(parts: Seq<PartView>) -> int {
    odir_meta(parts)[1] as int
}

/// Entry `e` names a stored orders row (of `n` rows) with key `kmin + e`, or is `ODIR_NONE`.
pub open spec fn oentry_sound(parts: Seq<PartView>, n: int, e: int) -> bool {
    let r = odir_rows(parts)[e];
    r == ODIR_NONE || (r < n && or_key(parts, r as int) == odir_kmin(parts) + e)
}

/// The key of stored orders row `p` has an entry in the range that is not `ODIR_NONE`.
pub open spec fn oentry_complete(parts: Seq<PartView>, p: int) -> bool {
    let e = or_key(parts, p) - odir_kmin(parts);
    &&& 0 <= e < odir_rows(parts).len()
    &&& odir_rows(parts)[e] != ODIR_NONE
}

/// The o_orderkey directory over the `n` stored orders rows.
pub open spec fn odir_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts.len() == FACTSDIR_PARTS
    &&& parts[ODIR_META as int] is I64 && odir_meta(parts).len() == 2
    &&& parts[ODIR_ROWS as int] is U32
    &&& has_odir(parts) ==> {
        &&& n < ODIR_NONE
        &&& forall|e: int| 0 <= e < odir_rows(parts).len() ==> #[trigger] oentry_sound(parts, n, e)
        &&& forall|p: int| 0 <= p < n ==> #[trigger] oentry_complete(parts, p)
    }
}

/// A key outside the o_orderkey directory's range, or whose entry is `ODIR_NONE`, belongs to no stored orders row.
pub proof fn lemma_odir_absent(parts: Seq<PartView>, n: int, k: int, p: int)
    requires
        odir_ok(parts, n),
        has_odir(parts),
        0 <= p < n,
        !(0 <= k - odir_kmin(parts) < odir_rows(parts).len()) || odir_rows(parts)[k - odir_kmin(parts)] == ODIR_NONE,
    ensures
        or_key(parts, p) != k,
{
    assert(oentry_complete(parts, p));
}

} // verus!
