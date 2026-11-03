//! The (p_brand, p_type, p_size) index of storage `part_btsidx` in the terms of the part handle `tables::PCols`.
//!
//! `part_btsidx` extends `custpart` by a dense directory `offs` over the composite key
//! `comp(j) = (brand entry * nt + type entry) * ns + (p_size - smin)` and a permutation `perm` of the part rows
//! sorted by it. Its interface states the key with its own copies of the inherited dictionaries; `open_xidx` checks
//! at run time that those are custpart's dictionaries (they are the same linked parts), so every index position
//! lies in the directory entry of its row's key in custpart's dictionary indices (`xidx_ok`). Then the positions
//! of entry `e` hold exactly the part rows whose key is `e` (`lemma_entry_exact`), i.e. one (brand, type, size)
//! group (`lemma_comp_inj`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::source::lemma_proj_all_index;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::layout::PartView;
use crate::stores::part_btsidx::interface as xi;
use crate::stores::part_btsidx::declaration as xd;
use super::tables::*;
use super::model::*;
use super::answer::lemma_dict_inj;

verus! {

/// The index over custpart's part rows.
#[derive(Clone, Copy)]
pub struct XIdx {
    /// `nk + 1` directory offsets (index positions).
    pub offs: &'static [u32],
    /// The part row at each index position.
    pub perm: &'static [u32],
    /// The smallest p_size of the key range and the number of sizes in it.
    pub smin: i64,
    pub ns: usize,
    /// Type dictionary entries.
    pub nt: usize,
    /// Directory entries: brand entries * `nt` * `ns`.
    pub nk: usize,
}

/// The composite key of part row `j`.
pub open spec fn comp(c: Cols, x: XIdx, j: int) -> int {
    (bidx(c.p, j) * x.nt + tidx(c.p, j)) * x.ns + (sval(c.p, j) - x.smin)
}

/// Index position `p` lies in the directory entry of its row's key.
pub open spec fn in_ent(c: Cols, x: XIdx, p: int) -> bool {
    let f = comp(c, x, x.perm@[p] as int);
    0 <= f < x.nk && x.offs@[f] <= p < x.offs@[f + 1]
}

/// Part row `j` is at some index position.
pub open spec fn has_pos(c: Cols, x: XIdx, j: int) -> bool {
    exists|p: int| 0 <= p < c.p.n && x.perm@[p] == j
}

/// The index facts over the part handle.
pub open spec fn xidx_ok(c: Cols, x: XIdx) -> bool {
    &&& x.ns >= 1
    &&& x.nt == c.p.type_o@.len() - 1
    &&& x.nk == (c.p.brand_o@.len() - 1) * x.nt * x.ns
    &&& x.offs@.len() == x.nk + 1
    &&& x.offs@[x.nk as int] <= c.p.n
    &&& forall|e: int| 0 <= e < x.nk ==> #[trigger] x.offs@[e] <= x.offs@[e + 1]
    &&& x.perm@.len() == c.p.n
    &&& forall|p: int| 0 <= p < c.p.n ==> (#[trigger] x.perm@[p]) < c.p.n
    &&& forall|p: int| 0 <= p < c.p.n ==> #[trigger] in_ent(c, x, p)
    &&& forall|j: int| 0 <= j < c.p.n ==> #[trigger] has_pos(c, x, j)
    &&& forall|j: int| 0 <= j < c.p.n ==> x.smin <= #[trigger] sval(c.p, j) < x.smin + x.ns
}

/// Offsets never decrease over a span of entries.
pub proof fn lemma_offs_mono(c: Cols, x: XIdx, a: int, b: int)
    requires xidx_ok(c, x), 0 <= a <= b <= x.nk,
    ensures x.offs@[a] <= x.offs@[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(c, x, a, b - 1);
        assert(x.offs@[b - 1] <= x.offs@[b]);
    }
}

/// The positions of entry `e` are exactly the positions whose row has key `e`; they lie inside the permutation.
pub proof fn lemma_entry_exact(c: Cols, x: XIdx, e: int, p: int)
    requires xidx_ok(c, x), 0 <= e < x.nk, 0 <= p < c.p.n,
    ensures
        (x.offs@[e] <= p < x.offs@[e + 1]) <==> comp(c, x, x.perm@[p] as int) == e,
        x.offs@[e] <= x.offs@[e + 1] <= c.p.n,
{
    assert(in_ent(c, x, p));
    let f = comp(c, x, x.perm@[p] as int);
    lemma_offs_mono(c, x, e + 1, x.nk as int);
    if x.offs@[e] <= p < x.offs@[e + 1] {
        if f < e {
            lemma_offs_mono(c, x, f + 1, e);
        } else if f > e {
            lemma_offs_mono(c, x, e + 1, f);
        }
    }
}

/// Mixed-radix uniqueness of the composite key.
pub proof fn lemma_comp_inj(b1: int, t1: int, s1: int, b2: int, t2: int, s2: int, nt: int, ns: int)
    requires
        0 <= t1 < nt, 0 <= t2 < nt, 0 <= s1 < ns, 0 <= s2 < ns,
        (b1 * nt + t1) * ns + s1 == (b2 * nt + t2) * ns + s2,
    ensures b1 == b2, t1 == t2, s1 == s2,
{
    let g = (b1 * nt + t1) * ns + s1;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(g, ns, b1 * nt + t1, s1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(g, ns, b2 * nt + t2, s2);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(b1 * nt + t1, nt, b1, t1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(b1 * nt + t1, nt, b2, t2);
}

/// The composite key of in-range indices lies below `nb * nt * ns`.
pub proof fn lemma_comp_bound(b: int, t: int, s: int, nb: int, nt: int, ns: int)
    requires 0 <= b < nb, 0 <= t < nt, 0 <= s < ns,
    ensures 0 <= (b * nt + t) * ns + s < nb * nt * ns,
{
    assert(b * nt + t < nb * nt) by (nonlinear_arith) requires 0 <= b < nb, 0 <= t < nt;
    assert(0 <= b * nt) by (nonlinear_arith) requires 0 <= b, 0 <= nt;
    let g = b * nt + t;
    assert(g * ns + s < (nb * nt) * ns) by (nonlinear_arith) requires 0 <= g < nb * nt, 0 <= s < ns;
    assert(0 <= g * ns) by (nonlinear_arith) requires 0 <= g, 0 <= ns;
    assert((nb * nt) * ns == nb * nt * ns) by (nonlinear_arith);
}

/// Equal slices.
fn same_u64(a: &[u64], b: &[u64]) -> (r: bool)
    ensures r ==> a@ == b@,
{
    if a.len() != b.len() {
        return false;
    }
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant n == a@.len(), n == b@.len(), i <= n, forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

fn same_u8(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r ==> a@ == b@,
{
    if a.len() != b.len() {
        return false;
    }
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant n == a@.len(), n == b@.len(), i <= n, forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// Row `j`'s index entries are custpart's: same dictionary indices and size, so the same composite key.
proof fn lemma_row_same(parts: Seq<PartView>, rel: Seq<Row>, c: Cols, tp: Row, x: XIdx, j: int)
    requires
        rel[j] == xi::row_at(parts, j),
        xi::dict_idx_ok(parts, j),
        rel[j][1] == tp[3], rel[j][2] == tp[4], rel[j][3] == tp[5],
        part_row_ok(c.p, tp, j),
        crate::stores::custpart::interface::common::colfmt::dict_sorted(c.p.brand_o@, c.p.brand_y@, c.p.brand_o@.len() - 1),
        crate::stores::custpart::interface::common::colfmt::dict_sorted(c.p.type_o@, c.p.type_y@, c.p.type_o@.len() - 1),
        xi::b_offs(parts) == c.p.brand_o@, xi::b_bytes(parts) == c.p.brand_y@,
        xi::t_offs(parts) == c.p.type_o@, xi::t_bytes(parts) == c.p.type_y@,
        x.nt as int == xi::n_types(parts), x.ns as int == xi::idx_ns(parts), x.smin as int == xi::idx_smin(parts),
    ensures
        xi::comp_at(parts, j) == comp(c, x, j),
        xi::size_at(parts, j) == sval(c.p, j),
{
    let (bi, ti) = (xi::bi_at(parts, j), xi::ti_at(parts, j));
    assert(xi::b_text(parts, bi) == txt(c.p.brand_o@, c.p.brand_y@, bi));
    assert(xi::t_text(parts, ti) == txt(c.p.type_o@, c.p.type_y@, ti));
    lemma_dict_inj(c.p.brand_o@, c.p.brand_y@, bi, bidx(c.p, j));
    lemma_dict_inj(c.p.type_o@, c.p.type_y@, ti, tidx(c.p, j));
}

/// The index relation's rows carry part's p_brand, p_type and p_size (both are projections of table 3).
proof fn lemma_rel_cols(db: Database, rel: Seq<Row>, t: Tabs)
    requires
        db.schema == crate::schema::schema_spec(), crate::spec::typing::db_wf(db),
        rel == xd::stored_relations(db)[0],
        t.p == db.tables[3],
    ensures
        rel.len() == t.p.len(),
        forall|j: int| 0 <= j < rel.len() ==> (#[trigger] rel[j])[1] == t.p[j][3] && rel[j][2] == t.p[j][4] && rel[j][3] == t.p[j][5],
{
    xd::lemma_stored_relations(db);
    lemma_proj_all_index(db.tables[3], xd::stored_cols_t0());
    assert(xd::stored_cols_t0() == seq![0nat, 3, 4, 5]);
}

/// The index of storage `part_btsidx`, when present and stated with custpart's dictionaries.
pub fn open_xidx(st: &mut StoredParts, c: &Cols, Ghost(t): Ghost<Tabs>, Ghost(db): Ghost<Database>) -> (r: Option<XIdx>)
    requires
        xi::represents(old(st)@, xd::stored_relations(db)),
        db.schema == crate::schema::schema_spec(), crate::spec::typing::db_wf(db),
        cols_ok(*c, t),
        t.p == db.tables[3],
    ensures
        final(st)@ == old(st)@,
        r matches Some(x) ==> xidx_ok(*c, x),
{
    let ghost parts = st@;
    let ghost rel = xd::stored_relations(db)[0];
    proof {
        lemma_rel_cols(db, rel, t);
    }
    let meta = st.extent_i64(xi::IDX_META, 0, 3);
    proof {
        assert(meta@ =~= xi::idx_meta(parts));
    }
    if meta[0] != xi::MODE_INDEX || meta[2] < 1 || meta[2] > 0x10_0000 {
        return None;
    }
    let lb = st.part_len(xi::PA_BRAND_DOFFS);
    let bo = st.extent_u64(xi::PA_BRAND_DOFFS, 0, lb);
    let lb = st.part_len(xi::PA_BRAND_DBYTES);
    let by = st.extent_u8(xi::PA_BRAND_DBYTES, 0, lb);
    let lt = st.part_len(xi::PA_TYPE_DOFFS);
    let to = st.extent_u64(xi::PA_TYPE_DOFFS, 0, lt);
    let lt = st.part_len(xi::PA_TYPE_DBYTES);
    let ty = st.extent_u8(xi::PA_TYPE_DBYTES, 0, lt);
    proof {
        assert(bo@ =~= xi::b_offs(parts));
        assert(by@ =~= xi::b_bytes(parts));
        assert(to@ =~= xi::t_offs(parts));
        assert(ty@ =~= xi::t_bytes(parts));
    }
    if !same_u64(bo, c.p.brand_o) || !same_u8(by, c.p.brand_y) || !same_u64(to, c.p.type_o) || !same_u8(ty, c.p.type_y) {
        return None;
    }
    let lo = st.part_len(xi::IDX_OFFS);
    let offs = st.extent_u32(xi::IDX_OFFS, 0, lo);
    let n = c.p.n;
    let perm = st.extent_u32(xi::IDX_PERM, 0, n);
    proof {
        assert(offs@ =~= xi::idx_offs(parts));
        assert(perm@ =~= xi::idx_perm(parts));
        assert(xi::has_idx(parts));
    }
    let m2 = meta[2];
    let ns = m2 as usize;
    proof {
        assert(m2 == xi::idx_meta(parts)[2]);
        assert(m2 >= 1);
        assert(ns as int == m2 as int);
    }
    let nt = c.p.type_o.len() - 1;
    let x = XIdx { offs, perm, smin: meta[1], ns, nt, nk: lo - 1 };
    proof {
        let n = c.p.n as int;
        assert(xi::idx_ns(parts) == ns as int);
        assert(xi::n_types(parts) == nt as int);
        assert(xi::n_brands(parts) == c.p.brand_o@.len() - 1);
        assert forall|p: int| 0 <= p < n implies #[trigger] in_ent(*c, x, p) by {
            assert(xi::in_entry(parts, p));
            let j = xi::prow(parts, p);
            assert(0 <= j < n);
            assert(part_row_ok(c.p, t.p[j], j));
            lemma_row_same(parts, rel, *c, t.p[j], x, j);
        }
        assert forall|j: int| 0 <= j < n implies #[trigger] has_pos(*c, x, j) by {
            assert(xi::listed(parts, n, j));
            let p = choose|p: int| 0 <= p < n && #[trigger] xi::prow(parts, p) == j;
            assert(x.perm@[p] == j);
        }
        assert forall|j: int| 0 <= j < n implies x.smin <= #[trigger] sval(c.p, j) < x.smin + x.ns by {
            assert(xi::size_in(parts, j));
            assert(part_row_ok(c.p, t.p[j], j));
            lemma_row_same(parts, rel, *c, t.p[j], x, j);
        }
        assert forall|p: int| 0 <= p < n implies (#[trigger] x.perm@[p]) < n by {
            assert(0 <= xi::prow(parts, p) < n);
        }
        assert forall|e: int| 0 <= e < x.nk implies #[trigger] x.offs@[e] <= x.offs@[e + 1] by {
            assert(xi::idx_offs(parts)[e] <= xi::idx_offs(parts)[e + 1]);
        }
    }
    Some(x)
}

} // verus!
