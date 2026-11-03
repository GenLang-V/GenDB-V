//! Storage `suppliers_rank`: storage `suppliers` (partsupp, supplier, nation, region) with its 48 parts unchanged in
//! front, extended by two indexes over its rows:
//!
//! - `SBAL` (U32): the supplier rows in descending s_acctbal order (a permutation of the supplier rows; ties in any
//!   order). Empty when the builder could not order them (then it states nothing).
//! - `PSMETA` (I64 `[mode, kmin]`), `PSOFFS` (U32), `PSPERM` (U32): in mode `MODE_DIRECTORY`, a dense directory over
//!   the ps_suppkey values `kmin .. kmin + nk` (`nk = PSOFFS.len() - 1`): the positions `offs[e] .. offs[e + 1]` of the
//!   permutation `PSPERM` of the partsupp rows hold exactly the rows whose ps_suppkey is `kmin + e`
//!   (`lemma_key_rows`); every other mode states nothing.
//!
//! Both are positions only (no column value is copied): a supplier "top balances first" walk reaches each supplier's
//! partsupp rows without scanning partsupp.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
use crate::stores::suppliers::interface as si;

verus! {

/// Parts of storage suppliers, kept unchanged in front.
pub const SUPPLIERS_PARTS: usize = 48;
/// U32: supplier rows by descending s_acctbal (or empty).
pub const SBAL: usize = 48;
/// I64 `[mode, kmin]` of the ps_suppkey directory.
pub const PSMETA: usize = 49;
/// U32 directory offsets (`nk + 1`).
pub const PSOFFS: usize = 50;
/// U32 partsupp rows grouped by ps_suppkey.
pub const PSPERM: usize = 51;
/// Number of parts of storage suppliers_rank.
pub const RANK_PARTS: usize = 52;
/// `PSMETA[0]` of a dense directory.
pub const MODE_DIRECTORY: i64 = 1;

/// The values of a U32 part (empty for another kind).
pub open spec fn u32s_of(p: PartView) -> Seq<u32> {
    match p {
        PartView::U32(s) => s,
        _ => Seq::empty(),
    }
}

/// The values of an I64 part (empty for another kind).
pub open spec fn i64s_of(p: PartView) -> Seq<i64> {
    match p {
        PartView::I64(s) => s,
        _ => Seq::empty(),
    }
}

// ------------------------------------------------------------------------------------------------ permutations

/// Row `r` appears in `v`.
pub open spec fn listed(v: Seq<u32>, r: int) -> bool {
    exists|i: int| 0 <= i < v.len() && v[i] == r
}

/// `v` is a bijection of `[0, n)`.
pub open spec fn perm_ok(v: Seq<u32>, n: int) -> bool {
    &&& v.len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] v[i] < n
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] v[a] != #[trigger] v[b]
    &&& forall|r: int| 0 <= r < n ==> #[trigger] listed(v, r)
}

// ------------------------------------------------------------------------------------------------ SBAL

/// s_acctbal coefficient (scale 2) of supplier row `j`.
pub open spec fn bal(s: Seq<Row>, j: int) -> int {
    match s[j][5] {
        Val::Num { coeff, .. } => coeff,
        _ => 0,
    }
}

/// Positions `i` and `i + 1` of `sb` are in descending s_acctbal order.
pub open spec fn desc_at(sb: Seq<u32>, s: Seq<Row>, i: int) -> bool {
    bal(s, sb[i] as int) >= bal(s, sb[i + 1] as int)
}

/// `sb` is empty, or lists every supplier row once in descending s_acctbal order.
pub open spec fn sbal_ok(sb: Seq<u32>, s: Seq<Row>) -> bool {
    sb.len() == 0 || {
        &&& perm_ok(sb, s.len() as int)
        &&& forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] desc_at(sb, s, i)
    }
}

/// Descending order between any two positions.
pub proof fn lemma_desc(sb: Seq<u32>, s: Seq<Row>, i: int, j: int)
    requires sbal_ok(sb, s), sb.len() > 0, 0 <= i <= j < s.len(),
    ensures bal(s, sb[i] as int) >= bal(s, sb[j] as int),
    decreases j - i,
{
    if i < j {
        lemma_desc(sb, s, i + 1, j);
        assert(desc_at(sb, s, i));
    }
}

// ------------------------------------------------------------------------------------------------ ps_suppkey directory

/// Position `p` lies in entry `e`.
pub open spec fn in_entry(offs: Seq<u32>, e: int, p: int) -> bool {
    offs[e] <= p < offs[e + 1]
}

/// Adjacent offsets are ordered.
pub open spec fn offs_le(offs: Seq<u32>, e: int) -> bool {
    offs[e] <= offs[e + 1]
}

/// In directory mode: offsets from 0 to the row count, nondecreasing; the permutation lists every partsupp row once;
/// the rows of entry `e` have ps_suppkey `kmin + e`.
pub open spec fn psdir_ok(meta: Seq<i64>, offs: Seq<u32>, perm: Seq<u32>, ps: Seq<Row>) -> bool {
    &&& meta.len() == 2
    &&& meta[0] == MODE_DIRECTORY ==> {
        &&& offs.len() >= 1
        &&& offs[0] == 0
        &&& offs[offs.len() - 1] == ps.len()
        &&& forall|e: int| 0 <= e < offs.len() - 1 ==> #[trigger] offs_le(offs, e)
        &&& perm_ok(perm, ps.len() as int)
        &&& forall|e: int, p: int| 0 <= e < offs.len() - 1 && #[trigger] in_entry(offs, e, p)
                ==> ps[perm[p] as int][1] == Val::Int(meta[1] + e)
    }
}

/// Offsets are nondecreasing between any two entries.
pub proof fn lemma_offs_mono(meta: Seq<i64>, offs: Seq<u32>, perm: Seq<u32>, ps: Seq<Row>, e1: int, e2: int)
    requires psdir_ok(meta, offs, perm, ps), meta[0] == MODE_DIRECTORY, 0 <= e1 <= e2 < offs.len(),
    ensures offs[e1] <= offs[e2],
    decreases e2 - e1,
{
    if e1 < e2 {
        lemma_offs_mono(meta, offs, perm, ps, e1 + 1, e2);
        assert(offs_le(offs, e1));
    }
}

/// Every position lies in some entry.
pub proof fn lemma_find_entry(meta: Seq<i64>, offs: Seq<u32>, perm: Seq<u32>, ps: Seq<Row>, p: int) -> (e: int)
    requires psdir_ok(meta, offs, perm, ps), meta[0] == MODE_DIRECTORY, 0 <= p < ps.len(),
    ensures 0 <= e < offs.len() - 1, in_entry(offs, e, p),
{
    // The last entry whose start is at most `p`.
    let nk = offs.len() - 1;
    lemma_last_start(meta, offs, perm, ps, p, nk)
}

/// The last entry below `hi` whose start is at most `p` (`offs[hi] > p`).
proof fn lemma_last_start(meta: Seq<i64>, offs: Seq<u32>, perm: Seq<u32>, ps: Seq<Row>, p: int, hi: int) -> (e: int)
    requires
        psdir_ok(meta, offs, perm, ps), meta[0] == MODE_DIRECTORY, 0 <= p < ps.len(),
        1 <= hi <= offs.len() - 1, offs[hi] > p,
    ensures 0 <= e < hi, in_entry(offs, e, p),
    decreases hi,
{
    if offs[hi - 1] <= p {
        hi - 1
    } else {
        lemma_last_start(meta, offs, perm, ps, p, hi - 1)
    }
}

/// The partsupp rows of ps_suppkey `v` are exactly the rows at the positions of entry `v - kmin` (none when `v` is
/// outside the directory's key range).
pub proof fn lemma_key_rows(meta: Seq<i64>, offs: Seq<u32>, perm: Seq<u32>, ps: Seq<Row>, v: int, k: int)
    requires psdir_ok(meta, offs, perm, ps), meta[0] == MODE_DIRECTORY, 0 <= k < ps.len(), ps[k][1] == Val::Int(v),
    ensures
        0 <= v - meta[1] < offs.len() - 1,
        exists|p: int| #[trigger] in_entry(offs, v - meta[1], p) && perm[p] == k,
{
    assert(listed(perm, k));
    let p = choose|p: int| 0 <= p < perm.len() && perm[p] == k;
    let e = lemma_find_entry(meta, offs, perm, ps, p);
    assert(ps[perm[p] as int][1] == Val::Int(meta[1] + e));
    assert(in_entry(offs, v - meta[1], p));
}

// ------------------------------------------------------------------------------------------------ represents

/// The suppliers parts hold partsupp, supplier, nation and region (suppliers' `represents`); `SBAL` orders the
/// supplier rows by s_acctbal and the directory groups the partsupp rows by ps_suppkey.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == RANK_PARTS
    &&& si::represents(parts.subrange(0, SUPPLIERS_PARTS as int), rels)
    &&& parts[SBAL as int] is U32
    &&& parts[PSMETA as int] is I64
    &&& parts[PSOFFS as int] is U32
    &&& parts[PSPERM as int] is U32
    &&& sbal_ok(u32s_of(parts[SBAL as int]), rels[1])
    &&& psdir_ok(i64s_of(parts[PSMETA as int]), u32s_of(parts[PSOFFS as int]), u32s_of(parts[PSPERM as int]), rels[0])
}

/// The parts determine the relations they represent (those of suppliers).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    si::lemma_represents_determines(parts.subrange(0, SUPPLIERS_PARTS as int), a, b);
}

} // verus!
