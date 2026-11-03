//! The distinct supplier rows of one (brand, type, size) group, three ways.
//!
//! - `grp_set(b, tt, v)`: the supplier rows `x` the subquery keeps that share a key with a partsupp row of some
//!   part row of brand entry `b`, type entry `tt` and size `v` (`part_hit`);
//! - `pos_set(lo, hi)`: the same over the part rows at index positions `[lo, hi)` (what the counting kernel sees);
//!   for the positions of the group's directory entry the two are equal (`lemma_pos_grp`);
//! - the SQL count: for a brand differing from `$1` and a type not matching `$2`, `grp_set` has as many elements as
//!   the group's COUNT(DISTINCT ps_suppkey) (`lemma_grp_card`, supplier keys are unique); any other brand or type
//!   has no kept row, so its count is 0 (`lemma_kc_zero`).
use vstd::prelude::*;
use crate::spec::value::*;
use super::tables::*;
use super::model::*;
use super::sqlq::{Prm, like_true, in_sizes};
use super::answer::*;
use super::bind::{keys_unique, fk_supp};
use super::supp::cc_row;
use super::round::kc;
use super::xidx::*;

verus! {

/// Partsupp row `i` has part row `j`'s key and supplier row `x`'s key.
pub open spec fn ps_link(c: Cols, i: int, j: int, x: int) -> bool {
    &&& 0 <= i < c.ps.n
    &&& pskey(c.ps, i) == pkey(c.p, j)
    &&& skey(c.s, x) == pssupp(c.ps, i)
}

/// Supplier row `x` supplies part row `j`.
pub open spec fn part_hit(c: Cols, j: int, x: int) -> bool {
    exists|i: int| #[trigger] ps_link(c, i, j, x)
}

/// Part row `j` is in the group of brand entry `b`, type entry `tt` and size `v`.
pub open spec fn in_grp(c: Cols, j: int, b: int, tt: int, v: int) -> bool {
    0 <= j < c.p.n && bidx(c.p, j) == b && tidx(c.p, j) == tt && sval(c.p, j) == v
}

/// The kept supplier rows of a group.
pub open spec fn grp_set(c: Cols, b: int, tt: int, v: int) -> Set<int> {
    Set::range(0, c.s.n as int).filter(|x: int| !cc_row(c.s, x)
        && exists|j: int| #[trigger] in_grp(c, j, b, tt, v) && part_hit(c, j, x))
}

/// The kept supplier rows of the part rows at index positions `[lo, hi)`.
pub open spec fn pos_set(c: Cols, xi: XIdx, lo: int, hi: int) -> Set<int> {
    Set::range(0, c.s.n as int).filter(|x: int| !cc_row(c.s, x)
        && exists|p: int| lo <= p < hi && #[trigger] part_hit(c, xi.perm@[p] as int, x))
}

/// The directory entry of brand entry `b`, type entry `tt` and size `v` (in the key range).
pub open spec fn ent_of(xi: XIdx, b: int, tt: int, v: int) -> int {
    (b * xi.nt + tt) * xi.ns + (v - xi.smin)
}

/// The positions of a group's directory entry hold exactly its part rows.
pub proof fn lemma_pos_grp(c: Cols, t: Tabs, xi: XIdx, b: int, tt: int, v: int)
    requires
        xidx_ok(c, xi),
        cols_ok(c, t),
        0 <= b < c.p.brand_o@.len() - 1, 0 <= tt < xi.nt, xi.smin <= v < xi.smin + xi.ns,
    ensures ({
        let e = ent_of(xi, b, tt, v);
        &&& 0 <= e < xi.nk
        &&& pos_set(c, xi, xi.offs@[e] as int, xi.offs@[e + 1] as int) == grp_set(c, b, tt, v)
    }),
{
    let e = ent_of(xi, b, tt, v);
    let nb = c.p.brand_o@.len() - 1;
    lemma_comp_bound(b, tt, v - xi.smin, nb, xi.nt as int, xi.ns as int);
    let (lo, hi) = (xi.offs@[e] as int, xi.offs@[e + 1] as int);
    let ps = pos_set(c, xi, lo, hi);
    let gs = grp_set(c, b, tt, v);
    assert forall|x: int| #[trigger] ps.contains(x) <==> gs.contains(x) by {
        if ps.contains(x) {
            let p = choose|p: int| lo <= p < hi && #[trigger] part_hit(c, xi.perm@[p] as int, x);
            lemma_offs_mono(c, xi, e + 1, xi.nk as int);
            lemma_entry_exact(c, xi, e, p);
            let j = xi.perm@[p] as int;
            assert(0 <= j < c.p.n);
            lemma_row_ranges(c, t, xi, j);
            lemma_comp_inj(bidx(c.p, j), tidx(c.p, j), sval(c.p, j) - xi.smin, b, tt, v - xi.smin, xi.nt as int, xi.ns as int);
            assert(in_grp(c, j, b, tt, v));
        }
        if gs.contains(x) {
            let j = choose|j: int| #[trigger] in_grp(c, j, b, tt, v) && part_hit(c, j, x);
            assert(has_pos(c, xi, j));
            let p = choose|p: int| 0 <= p < c.p.n && xi.perm@[p] == j;
            lemma_entry_exact(c, xi, e, p);
            assert(lo <= p < hi && part_hit(c, xi.perm@[p] as int, x));
        }
    }
    assert(ps =~= gs);
}

/// A part row's dictionary indices and size offset lie in the key ranges.
pub proof fn lemma_row_ranges(c: Cols, t: Tabs, xi: XIdx, j: int)
    requires xidx_ok(c, xi), cols_ok(c, t), 0 <= j < c.p.n,
    ensures 0 <= tidx(c.p, j) < xi.nt, 0 <= sval(c.p, j) - xi.smin < xi.ns,
{
    assert(part_row_ok(c.p, t.p[j], j));
}

/// Supplier keys identify supplier rows.
pub proof fn lemma_skeys_uniq(c: Cols, t: Tabs, r1: int, r2: int)
    requires cols_ok(c, t), keys_unique(t), 0 <= r1 < c.s.n, 0 <= r2 < c.s.n, skey(c.s, r1) == skey(c.s, r2),
    ensures r1 == r2,
{
    assert(supp_row_ok(c.s, t.s[r1], r1));
    assert(supp_row_ok(c.s, t.s[r2], r2));
    assert(t.s[r1][0] == t.s[r2][0]);
}

/// A part row has the SQL key of (`b`, `tt`, `z`) exactly when it is in that group.
proof fn lemma_key_grp(c: Cols, t: Tabs, sizes: Seq<i64>, j: int, b: int, tt: int, z: int)
    requires
        cols_ok(c, t), 0 <= j < c.p.n,
        0 <= b < c.p.brand_o@.len() - 1, 0 <= tt < c.p.type_o@.len() - 1, 0 <= z < sizes.len(),
    ensures prow_key(t, j) == key_bt(c, sizes, b, tt, z) <==> in_grp(c, j, b, tt, sizes[z] as int),
{
    lemma_prow_key(c, t, j);
    assert(part_row_ok(c.p, t.p[j], j));
    let k1 = prow_key(t, j);
    let k2 = key_bt(c, sizes, b, tt, z);
    if k1 == k2 {
        assert(k1[0] == k2[0] && k1[1] == k2[1] && k1[2] == k2[2]);
        lemma_dict_inj(c.p.brand_o@, c.p.brand_y@, bidx(c.p, j), b);
        lemma_dict_inj(c.p.type_o@, c.p.type_y@, tidx(c.p, j), tt);
    }
    if in_grp(c, j, b, tt, sizes[z] as int) {
        assert(k1 =~= k2);
    }
}

/// A group of a brand differing from `$1`, a type not matching `$2` and a listed size: its kept supplier rows are as
/// many as its distinct suppkeys.
pub proof fn lemma_grp_card(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, b: int, tt: int, z: int)
    requires
        cols_ok(c, t), keys_unique(t), fk_supp(t),
        0 <= b < c.p.brand_o@.len() - 1, 0 <= tt < c.p.type_o@.len() - 1, 0 <= z < sizes.len(),
        txt(c.p.brand_o@, c.p.brand_y@, b) != m.brand,
        !like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, tt)), m.pat),
        m.sizes.contains(sizes[z] as int),
    ensures grp_set(c, b, tt, sizes[z] as int).len() == kc(c, t, m, sizes, b, tt, z),
{
    let v = sizes[z] as int;
    let ds = grp_set(c, b, tt, v);
    let k = key_bt(c, sizes, b, tt, z);
    let ks = kv(t, m, k);
    let f = |x: int| t.s[x][0];
    lemma_tabs_typed(c, t);
    // Every kept supplier row's key is a distinct suppkey of the key.
    assert forall|x: int| #[trigger] ds.contains(x) implies ks.contains(f(x)) by {
        let j = choose|j: int| #[trigger] in_grp(c, j, b, tt, v) && part_hit(c, j, x);
        let i = choose|i: int| #[trigger] ps_link(c, i, j, x);
        assert(srow_of(c, i, x));
        lemma_qual_cols(c, t, m, i, j, x);
        lemma_key_grp(c, t, sizes, j, b, tt, z);
        assert(qual(t, m, i, j));
        assert(ps_row_ok(c.ps, t.ps[i], i));
        assert(supp_row_ok(c.s, t.s[x], x));
        lemma_kv_has(t, m, k, f(x));
    }
    // Every distinct suppkey of the key is some kept supplier row's key.
    assert forall|v2: Val| #[trigger] ks.contains(v2) implies exists|x: int| ds.contains(x) && f(x) == v2 by {
        lemma_kv_has(t, m, k, v2);
        let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k && t.ps[i][1] == v2;
        lemma_srow_exists(c, t, i);
        let x = choose|x: int| #[trigger] srow_of(c, i, x);
        lemma_qual_cols(c, t, m, i, j, x);
        lemma_key_grp(c, t, sizes, j, b, tt, z);
        assert(ps_link(c, i, j, x));
        assert(part_hit(c, j, x));
        assert(ds.contains(x));
        assert(ps_row_ok(c.ps, t.ps[i], i));
        assert(supp_row_ok(c.s, t.s[x], x));
    }
    // Supplier keys are unique.
    assert(ds.injective_on(f)) by {
        assert forall|x1: int, x2: int| ds.contains(x1) && ds.contains(x2) && #[trigger] f(x1) == #[trigger] f(x2) implies x1 == x2 by {
            assert(supp_row_ok(c.s, t.s[x1], x1));
            assert(supp_row_ok(c.s, t.s[x2], x2));
            lemma_skeys_uniq(c, t, x1, x2);
        }
        assert(ds.to_iset().injective_on(f)) by {
            assert forall|x1: int, x2: int| ds.to_iset().contains(x1) && ds.to_iset().contains(x2) && #[trigger] f(x1) == #[trigger] f(x2)
                implies x1 == x2 by {
                assert(ds.contains(x1) && ds.contains(x2));
            }
        }
    }
    assert(ds.map(f) =~= ks) by {
        assert forall|v2: Val| ds.map(f).contains(v2) <==> ks.contains(v2) by {
            ds.lemma_map_contains(f, v2);
        }
    }
    vstd::set_lib::lemma_map_size(ds, ks, f);
}

/// A brand equal to `$1` or a type matching `$2` has no kept row: its count is 0.
pub proof fn lemma_kc_zero(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, b: int, tt: int, z: int)
    requires
        cols_ok(c, t), keys_unique(t), fk_supp(t),
        0 <= b < c.p.brand_o@.len() - 1, 0 <= tt < c.p.type_o@.len() - 1, 0 <= z < sizes.len(),
        txt(c.p.brand_o@, c.p.brand_y@, b) == m.brand
            || like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, tt)), m.pat),
    ensures kc(c, t, m, sizes, b, tt, z) == 0,
{
    let k = key_bt(c, sizes, b, tt, z);
    let ks = kv(t, m, k);
    lemma_tabs_typed(c, t);
    assert forall|v2: Val| !ks.contains(v2) by {
        lemma_kv_has(t, m, k, v2);
        if ks.contains(v2) {
            let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k && t.ps[i][1] == v2;
            lemma_srow_exists(c, t, i);
            let x = choose|x: int| #[trigger] srow_of(c, i, x);
            lemma_qual_cols(c, t, m, i, j, x);
            lemma_key_grp(c, t, sizes, j, b, tt, z);
        }
    }
    assert(ks =~= Set::empty());
}

/// The group of a size outside the index's key range, or of an empty directory entry, has no part row.
pub proof fn lemma_grp_empty(c: Cols, b: int, tt: int, v: int)
    requires forall|j: int| 0 <= j < c.p.n ==> !(#[trigger] in_grp(c, j, b, tt, v)),
    ensures grp_set(c, b, tt, v).len() == 0,
{
    assert(grp_set(c, b, tt, v) =~= Set::empty());
}

} // verus!
