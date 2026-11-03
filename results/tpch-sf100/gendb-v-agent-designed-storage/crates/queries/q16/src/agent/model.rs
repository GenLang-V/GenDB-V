//! The kernel's model over the column handles (`tables::Cols`): what a part row's group code is in a round, and
//! which (group, supplier row) pairs a range of part rows yields.
//!
//! A round's lookup tables (`QualTabs`) give per brand dictionary index a brand term and per type dictionary index a
//! type term (`NONE32` when the entry does not take part), and the distinct sizes of the IN list. A part row's code is
//! `bterm[brand] + tterm[type] + slot(size)` when both terms exist and its size is listed (`code_of`). A pair
//! `(g, s)` of part rows `[lo, hi)` (`pair_in`) is a part row `j` there with code `g`, a partsupp row `i` with `j`'s
//! key and a supplier row `s` with `i`'s suppkey. What the codes mean (brand `<> $1`, type `NOT LIKE $2`, the round's
//! window) is the driver's business; this model only needs the tables' shape (`tabs_shape`).
use vstd::prelude::*;
use super::tables::*;

verus! {

/// "No entry" in the brand and type term tables.
pub const NONE32: u32 = 0xFFFF_FFFF;

/// The per-round lookup tables of the part filter.
pub struct QualTabs {
    /// Per brand dictionary index: the brand's term, or `NONE32`.
    pub bterm: Vec<u32>,
    /// Per type dictionary index: the type's term, or `NONE32`.
    pub tterm: Vec<u32>,
    /// The distinct sizes of the IN list.
    pub sizes: Vec<i64>,
}

/// Every pair of terms plus a size slot stays below `ng` (so codes are local groups), and below `2^31`.
pub open spec fn tabs_shape(q: QualTabs, nb: int, nt: int, ng: int) -> bool {
    &&& q.bterm@.len() == nb
    &&& q.tterm@.len() == nt
    &&& q.sizes@.len() <= 8
    &&& ng <= 0x4000_0000
    &&& q.sizes@.no_duplicates()
    &&& forall|b: int, t: int| 0 <= b < nb && 0 <= t < nt && #[trigger] q.bterm@[b] != NONE32 && #[trigger] q.tterm@[t] != NONE32
        ==> q.bterm@[b] + q.tterm@[t] + q.sizes@.len() <= ng
}

/// The slot of size `v` in the list (meaningful when listed).
pub open spec fn slot_of(sizes: Seq<i64>, v: int) -> int {
    choose|z: int| 0 <= z < sizes.len() && sizes[z] == v
}

pub open spec fn listed(sizes: Seq<i64>, v: int) -> bool {
    exists|z: int| 0 <= z < sizes.len() && sizes[z] == v
}

/// Brand and type dictionary indices and the size of part row `j`.
pub open spec fn bidx(p: PCols, j: int) -> int {
    fu8(p.brand_c@, p.brand_b@, p.bs as int, j)
}

pub open spec fn tidx(p: PCols, j: int) -> int {
    fu8(p.type_c@, p.type_b@, p.bs as int, j)
}

pub open spec fn sval(p: PCols, j: int) -> int {
    fv8(p.size_c@, p.size_b@, p.bs as int, j)
}

/// Part row `j` takes part in the round.
pub open spec fn coded(q: QualTabs, p: PCols, j: int) -> bool {
    &&& 0 <= bidx(p, j) < q.bterm@.len()
    &&& 0 <= tidx(p, j) < q.tterm@.len()
    &&& q.bterm@[bidx(p, j)] != NONE32
    &&& q.tterm@[tidx(p, j)] != NONE32
    &&& listed(q.sizes@, sval(p, j))
}

/// The group code of a coded part row.
pub open spec fn code_of(q: QualTabs, p: PCols, j: int) -> int {
    q.bterm@[bidx(p, j)] + q.tterm@[tidx(p, j)] + slot_of(q.sizes@, sval(p, j))
}

/// Keys and suppkeys of the stored rows.
pub open spec fn pkey(p: PCols, j: int) -> int {
    fv32(p.key_c@, p.key_b@, p.bs as int, j)
}

pub open spec fn pskey(ps: PSCols, i: int) -> int {
    fv32(ps.key_c@, ps.key_b@, ps.bs as int, i)
}

pub open spec fn pssupp(ps: PSCols, i: int) -> int {
    fv32(ps.supp_c@, ps.supp_b@, ps.bs as int, i)
}

pub open spec fn skey(s: SCols, r: int) -> int {
    fv32(s.key_c@, s.key_b@, s.bs as int, r)
}

/// `(g, r)` is a pair of part rows `[lo, hi)`: part row `j` there with code `g`, partsupp row `i` of `j`'s key, and
/// supplier row `r` of `i`'s suppkey.
pub open spec fn pair_at(q: QualTabs, c: Cols, j: int, i: int, g: int, r: int) -> bool {
    &&& 0 <= j < c.p.n
    &&& coded(q, c.p, j)
    &&& code_of(q, c.p, j) == g
    &&& 0 <= i < c.ps.n
    &&& pskey(c.ps, i) == pkey(c.p, j)
    &&& 0 <= r < c.s.n
    &&& skey(c.s, r) == pssupp(c.ps, i)
}

pub open spec fn pair_in(q: QualTabs, c: Cols, lo: int, hi: int, g: int, r: int) -> bool {
    exists|j: int, i: int| lo <= j < hi && #[trigger] pair_at(q, c, j, i, g, r)
}

/// What the kernel needs of the column handles: lengths, frames, the key indexes, and every key and suppkey inside
/// `i64` (`cols_ok` gives all of it, `lemma_shape`).
pub open spec fn shape_ok(c: Cols) -> bool {
    &&& c.e32@ == Seq::<u32>::empty()
    &&& c.e64@ == Seq::<u64>::empty()
    &&& frame_ok(c.p.n as int, c.p.bs as int, c.p.ng as int)
    &&& frame_ok(c.ps.n as int, c.ps.bs as int, c.ps.ng as int)
    &&& frame_ok(c.s.n as int, c.s.bs as int, c.s.ng as int)
    &&& c.p.key_c@.len() == c.p.n && c.p.key_b@.len() == c.p.ng
    &&& c.p.brand_c@.len() == c.p.n && c.p.brand_b@.len() == c.p.ng
    &&& c.p.type_c@.len() == c.p.n && c.p.type_b@.len() == c.p.ng
    &&& c.p.size_c@.len() == c.p.n && c.p.size_b@.len() == c.p.ng
    &&& c.ps.key_c@.len() == c.ps.n && c.ps.key_b@.len() == c.ps.ng
    &&& c.ps.supp_c@.len() == c.ps.n && c.ps.supp_b@.len() == c.ps.ng
    &&& c.s.key_c@.len() == c.s.n && c.s.key_b@.len() == c.s.ng
    &&& crate::stores::suppliers::interface::common::keyidx::keyidx_ok(c.ps.key_c@, c.ps.key_b@, c.e32@, c.e64@,
            c.ps.bs as int, c.ps.kind, c.ps.n as int)
    &&& crate::stores::suppliers::interface::common::keyidx::keyidx_ok(c.s.key_c@, c.s.key_b@, c.e32@, c.e64@,
            c.s.bs as int, c.s.kind, c.s.n as int)
    &&& forall|j: int| 0 <= j < c.p.n ==> #[trigger] i64r(pkey(c.p, j))
    &&& forall|i: int| 0 <= i < c.ps.n ==> #[trigger] i64r(pskey(c.ps, i))
    &&& forall|i: int| 0 <= i < c.ps.n ==> #[trigger] i64r(pssupp(c.ps, i))
    &&& forall|r: int| 0 <= r < c.s.n ==> #[trigger] i64r(skey(c.s, r))
    &&& runs_hold(c.ps)
}

/// The column handles of the statement's tables have the kernel's shape.
pub proof fn lemma_shape(c: Cols, t: Tabs)
    requires cols_ok(c, t),
    ensures shape_ok(c),
{
    assert forall|j: int| 0 <= j < c.p.n implies #[trigger] i64r(pkey(c.p, j)) by {
        assert(part_row_ok(c.p, t.p[j], j));
    }
    assert forall|i: int| 0 <= i < c.ps.n implies #[trigger] i64r(pskey(c.ps, i)) by {
        assert(ps_row_ok(c.ps, t.ps[i], i));
    }
    assert forall|i: int| 0 <= i < c.ps.n implies #[trigger] i64r(pssupp(c.ps, i)) by {
        assert(ps_row_ok(c.ps, t.ps[i], i));
    }
    assert forall|r: int| 0 <= r < c.s.n implies #[trigger] i64r(skey(c.s, r)) by {
        assert(supp_row_ok(c.s, t.s[r], r));
    }
}

} // verus!
