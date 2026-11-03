//! From the kernel's counts to the statement's groups.
//!
//! A kept row of the WHERE is a pair (partsupp row `i`, part row `j`) satisfying `qual` (`lemma_kept_has`); the
//! distinct suppkeys of a key `k` (`kv`, the COUNT(DISTINCT) argument set of `common::distinct`) are those of the
//! kept pairs whose part row has key `k` (`lemma_kv_has`). In stored terms (`lemma_qual_cols`): the part row's key
//! equals the partsupp row's, its brand entry differs from `$1`, its type entry does not match `$2`, its size is
//! listed, and the supplier row of the suppkey (unique key, it exists by the foreign key) is not excluded. A round's
//! tables (`round_tabs`) code exactly the part rows of its brand/type window that pass the part conditions
//! (`lemma_round_coded`), so the kernel's distinct supplier rows of a group map one-to-one onto the distinct
//! suppkeys of its key (`lemma_group_card`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::*;
use crate::link::join::{keep, lemma_keep_members};
use super::common::relops::*;
use super::common::distinct::*;
use super::sqlq::*;
use super::sqlrel::*;
use super::tables::*;
use super::model::*;
use super::bind::{keys_unique, fk_supp, has_supp};
use super::supp::{cc_row, comment};
use super::count::{dset, in_some};
use super::common::marks::bit_at;

verus! {

// ------------------------------------------------------------------------------------------------ kept rows

/// Partsupp row `i` and part row `j` make a kept row.
pub open spec fn qual(t: Tabs, m: Prm, i: int, j: int) -> bool {
    0 <= i < t.ps.len() && 0 <= j < t.p.len() && q_row(t, m, t.ps[i] + t.p[j])
}

/// The kept rows are exactly the qualifying pairs.
pub proof fn lemma_kept_has(t: Tabs, m: Prm, x: Row)
    requires tabs_typed(t),
    ensures kept(t, m).contains(x) <==> exists|i: int, j: int| #[trigger] qual(t, m, i, j) && x == t.ps[i] + t.p[j],
{
    lemma_keep_members(prod(t), q_f(t, m));
    if kept(t, m).contains(x) {
        let q = choose|q: int| 0 <= q < kept(t, m).len() && kept(t, m)[q] == x;
        assert(prod(t).contains(x) && q_f(t, m)(x));
        lemma_product_split(t.ps, t.p, x);
        let (i, j) = choose|i: int, j: int| 0 <= i < t.ps.len() && 0 <= j < t.p.len() && x == #[trigger] t.ps[i] + #[trigger] t.p[j];
        assert(qual(t, m, i, j));
    }
    if exists|i: int, j: int| #[trigger] qual(t, m, i, j) && x == t.ps[i] + t.p[j] {
        let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && x == t.ps[i] + t.p[j];
        lemma_product_has(t.ps, t.p, i, j);
        lemma_keep_has(prod(t), q_f(t, m), x);
    }
}

/// The distinct suppkeys of key `k` among the kept rows.
pub open spec fn kv(t: Tabs, m: Prm, k: Row) -> Set<Val> {
    key_vals(keys_of(kept(t, m)), args_of(kept(t, m)), k)
}

/// The part key `p_brand, p_type, p_size` of part row `j`.
pub open spec fn prow_key(t: Tabs, j: int) -> Row {
    seq![t.p[j][3], t.p[j][4], t.p[j][5]]
}

/// A kept row's key and argument.
proof fn lemma_pair_key(t: Tabs, i: int, j: int)
    requires tabs_typed(t), 0 <= i < t.ps.len(), 0 <= j < t.p.len(),
    ensures key_of(t.ps[i] + t.p[j]) == prow_key(t, j), (t.ps[i] + t.p[j])[1] == t.ps[i][1],
{
    assert(ps_typed(t.ps[i]) && p_typed(t.p[j]));
    let x = t.ps[i] + t.p[j];
    assert(x[8] == t.p[j][3] && x[9] == t.p[j][4] && x[10] == t.p[j][5]);
    assert(key_of(x) =~= prow_key(t, j));
}

/// `kv(k)` holds `v` exactly when some qualifying pair with part key `k` has suppkey `v`.
pub proof fn lemma_kv_has(t: Tabs, m: Prm, k: Row, v: Val)
    requires tabs_typed(t),
    ensures kv(t, m, k).contains(v) <==> exists|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k && t.ps[i][1] == v,
{
    let ks = kept(t, m);
    let keys = keys_of(ks);
    let args = args_of(ks);
    lemma_key_vals(keys, args, k, v);
    if kv(t, m, k).contains(v) {
        let q = choose|q: int| 0 <= q < keys.len() && keys[q] == k && (#[trigger] args[q])[0] == v;
        assert(ks.contains(ks[q]));
        lemma_kept_has(t, m, ks[q]);
        let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && ks[q] == t.ps[i] + t.p[j];
        lemma_pair_key(t, i, j);
        assert(keys[q] == key_of(ks[q]));
        assert(args[q] == arg_of(ks[q]));
    }
    if exists|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k && t.ps[i][1] == v {
        let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k && t.ps[i][1] == v;
        lemma_kept_has(t, m, t.ps[i] + t.p[j]);
        let q = choose|q: int| 0 <= q < ks.len() && ks[q] == t.ps[i] + t.p[j];
        lemma_pair_key(t, i, j);
        assert(keys[q] == key_of(ks[q]));
        assert(args[q] == arg_of(ks[q]));
        assert(args[q][0] == v);
    }
}

/// The keys of the kept rows are exactly the part keys of qualifying pairs.
pub proof fn lemma_keys_has(t: Tabs, m: Prm, k: Row)
    requires tabs_typed(t),
    ensures keys_of(kept(t, m)).contains(k) <==> exists|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k,
{
    let ks = kept(t, m);
    let keys = keys_of(ks);
    if keys.contains(k) {
        let q = choose|q: int| 0 <= q < keys.len() && keys[q] == k;
        assert(ks.contains(ks[q]));
        lemma_kept_has(t, m, ks[q]);
        let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && ks[q] == t.ps[i] + t.p[j];
        lemma_pair_key(t, i, j);
    }
    if exists|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k {
        let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k;
        lemma_kept_has(t, m, t.ps[i] + t.p[j]);
        let q = choose|q: int| 0 <= q < ks.len() && ks[q] == t.ps[i] + t.p[j];
        lemma_pair_key(t, i, j);
        assert(keys[q] == k);
    }
}

// ------------------------------------------------------------------------------------------------ stored terms

/// Part row `j`'s brand entry differs from `$1`.
pub open spec fn bsel(c: Cols, m: Prm, j: int) -> bool {
    txt(c.p.brand_o@, c.p.brand_y@, bidx(c.p, j)) != m.brand
}

/// Part row `j`'s type entry does not match `$2`.
pub open spec fn tsel(c: Cols, m: Prm, j: int) -> bool {
    !like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, tidx(c.p, j))), m.pat)
}

/// The supplier row `r` of partsupp row `i`'s suppkey.
pub open spec fn srow_of(c: Cols, i: int, r: int) -> bool {
    0 <= r < c.s.n && skey(c.s, r) == pssupp(c.ps, i)
}

/// A qualifying pair in stored terms, through the supplier row `r` of its suppkey.
pub proof fn lemma_qual_cols(c: Cols, t: Tabs, m: Prm, i: int, j: int, r: int)
    requires
        cols_ok(c, t), keys_unique(t),
        0 <= i < t.ps.len(), 0 <= j < t.p.len(),
        srow_of(c, i, r),
    ensures
        qual(t, m, i, j) <==> (pskey(c.ps, i) == pkey(c.p, j) && bsel(c, m, j) && tsel(c, m, j)
            && in_sizes(m, Val::Int(sval(c.p, j))) && !cc_row(c.s, r)),
{
    assert(part_row_ok(c.p, t.p[j], j));
    assert(ps_row_ok(c.ps, t.ps[i], i));
    assert(supp_row_ok(c.s, t.s[r], r));
    let x = t.ps[i] + t.p[j];
    assert(x[0] == t.ps[i][0] && x[1] == t.ps[i][1] && x[5] == t.p[j][0]);
    assert(x[8] == t.p[j][3] && x[9] == t.p[j][4] && x[10] == t.p[j][5]);
    // NOT IN through the supplier row of the suppkey.
    assert(in_sub(t.s, x[1]) == cc_row(c.s, r)) by {
        if in_sub(t.s, x[1]) {
            let q = choose|q: int| 0 <= q < t.s.len() && #[trigger] t.s[q][0] == x[1] && cc_true(t.s[q][6]);
            assert(supp_row_ok(c.s, t.s[q], q));
            assert(t.s[q][0] == t.s[r][0]);
            assert(q == r);
        }
        if cc_row(c.s, r) {
            assert(t.s[r][0] == x[1]);
            assert(t.s[r][6] == Val::Text(comment(c.s, r)));
        }
    }
    assert((x[8] != Val::Text(m.brand)) == bsel(c, m, j));
}

/// Every partsupp row has the supplier row of its suppkey.
pub proof fn lemma_srow_exists(c: Cols, t: Tabs, i: int)
    requires cols_ok(c, t), fk_supp(t), 0 <= i < t.ps.len(),
    ensures exists|r: int| #[trigger] srow_of(c, i, r),
{
    assert(has_supp(t, t.ps[i][1]));
    let r = choose|r: int| 0 <= r < t.s.len() && #[trigger] t.s[r][0] == t.ps[i][1];
    assert(supp_row_ok(c.s, t.s[r], r));
    assert(ps_row_ok(c.ps, t.ps[i], i));
    assert(srow_of(c, i, r));
}

/// The part key of part row `j` from its dictionary entries and size.
pub proof fn lemma_prow_key(c: Cols, t: Tabs, j: int)
    requires cols_ok(c, t), 0 <= j < t.p.len(),
    ensures prow_key(t, j) == seq![Val::Text(txt(c.p.brand_o@, c.p.brand_y@, bidx(c.p, j))),
        Val::Text(txt(c.p.type_o@, c.p.type_y@, tidx(c.p, j))), Val::Int(sval(c.p, j))],
{
    assert(part_row_ok(c.p, t.p[j], j));
    assert(prow_key(t, j) =~= seq![Val::Text(txt(c.p.brand_o@, c.p.brand_y@, bidx(c.p, j))),
        Val::Text(txt(c.p.type_o@, c.p.type_y@, tidx(c.p, j))), Val::Int(sval(c.p, j))]);
}

// ------------------------------------------------------------------------------------------------ rounds

/// A round: brand dictionary indices `[b0, b1)`, type dictionary indices `[t0, t1)`, `ns` listed sizes.
pub struct Rnd {
    pub b0: int,
    pub b1: int,
    pub t0: int,
    pub t1: int,
    pub ns: int,
}

/// The round's local group of brand `b`, type `t` and size slot `z`.
pub open spec fn gid(r: Rnd, b: int, t: int, z: int) -> int {
    ((b - r.b0) * (r.t1 - r.t0) + (t - r.t0)) * r.ns + z
}

/// The round's number of local groups.
pub open spec fn rng(r: Rnd) -> int {
    (r.b1 - r.b0) * (r.t1 - r.t0) * r.ns
}

/// Brand `b`, type `t` and slot `z` lie in the round.
pub open spec fn in_round(r: Rnd, b: int, t: int, z: int) -> bool {
    r.b0 <= b < r.b1 && r.t0 <= t < r.t1 && 0 <= z < r.ns
}

/// The round's lookup tables: terms exactly for the window's entries passing `<> $1` and `NOT LIKE $2`, and the
/// distinct listed sizes in ascending order.
pub open spec fn round_tabs(q: QualTabs, c: Cols, m: Prm, r: Rnd) -> bool {
    &&& 0 <= r.b0 <= r.b1 <= q.bterm@.len()
    &&& 0 <= r.t0 <= r.t1 <= q.tterm@.len()
    &&& q.bterm@.len() == c.p.brand_o@.len() - 1
    &&& q.tterm@.len() == c.p.type_o@.len() - 1
    &&& r.ns == q.sizes@.len()
    &&& 1 <= r.ns <= 8
    &&& rng(r) <= 0x4000_0000
    &&& forall|b: int| 0 <= b < q.bterm@.len() ==> #[trigger] q.bterm@[b] as int == if r.b0 <= b < r.b1
        && txt(c.p.brand_o@, c.p.brand_y@, b) != m.brand { (b - r.b0) * (r.t1 - r.t0) * r.ns } else { NONE32 as int }
    &&& forall|t: int| 0 <= t < q.tterm@.len() ==> #[trigger] q.tterm@[t] as int == if r.t0 <= t < r.t1
        && !like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, t)), m.pat) { (t - r.t0) * r.ns } else { NONE32 as int }
    &&& forall|a: int, b: int| 0 <= a < b < q.sizes@.len() ==> #[trigger] q.sizes@[a] < #[trigger] q.sizes@[b]
    &&& forall|v: int| #[trigger] listed(q.sizes@, v) <==> m.sizes.contains(v)
}

/// Mixed-radix uniqueness: equal local groups are equal (brand, type, slot).
pub proof fn lemma_gid_inj(r: Rnd, b1: int, t1: int, z1: int, b2: int, t2: int, z2: int)
    requires in_round(r, b1, t1, z1), in_round(r, b2, t2, z2), gid(r, b1, t1, z1) == gid(r, b2, t2, z2),
    ensures b1 == b2, t1 == t2, z1 == z2,
{
    let tw = r.t1 - r.t0;
    let a1 = (b1 - r.b0) * tw + (t1 - r.t0);
    let a2 = (b2 - r.b0) * tw + (t2 - r.t0);
    let g = gid(r, b1, t1, z1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(g, r.ns, a1, z1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(g, r.ns, a2, z2);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a1, tw, b1 - r.b0, t1 - r.t0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a1, tw, b2 - r.b0, t2 - r.t0);
}

/// The local group is below the round's group count, and splits into its brand and type terms.
pub proof fn lemma_gid_bound(r: Rnd, b: int, t: int, z: int)
    requires in_round(r, b, t, z),
    ensures
        0 <= gid(r, b, t, z) < rng(r),
        gid(r, b, t, z) == (b - r.b0) * (r.t1 - r.t0) * r.ns + (t - r.t0) * r.ns + z,
        (b - r.b0) * (r.t1 - r.t0) * r.ns + (t - r.t0) * r.ns + r.ns <= rng(r),
        0 <= (b - r.b0) * (r.t1 - r.t0) * r.ns,
        0 <= (t - r.t0) * r.ns,
{
    let tw = r.t1 - r.t0;
    let (bb, tt) = (b - r.b0, t - r.t0);
    assert(gid(r, b, t, z) == bb * tw * r.ns + tt * r.ns + z) by (nonlinear_arith)
        requires gid(r, b, t, z) == (bb * tw + tt) * r.ns + z;
    assert(bb * tw * r.ns + tt * r.ns + r.ns <= rng(r)) by (nonlinear_arith)
        requires 0 <= bb < r.b1 - r.b0, 0 <= tt < tw, r.ns >= 1, rng(r) == (r.b1 - r.b0) * tw * r.ns;
    assert(0 <= bb * tw * r.ns) by (nonlinear_arith) requires bb >= 0, tw >= 0, r.ns >= 0;
    assert(0 <= tt * r.ns) by (nonlinear_arith) requires tt >= 0, r.ns >= 0;
}

/// A round's tables have the kernel's shape.
pub proof fn lemma_round_shape(q: QualTabs, c: Cols, m: Prm, r: Rnd)
    requires round_tabs(q, c, m, r),
    ensures tabs_shape(q, q.bterm@.len() as int, q.tterm@.len() as int, rng(r)),
{
    assert forall|b: int, t: int| 0 <= b < q.bterm@.len() && 0 <= t < q.tterm@.len() && #[trigger] q.bterm@[b] != NONE32
        && #[trigger] q.tterm@[t] != NONE32 implies q.bterm@[b] + q.tterm@[t] + q.sizes@.len() <= rng(r) by {
        lemma_gid_bound(r, b, t, 0);
    }
    assert(q.sizes@.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < q.sizes@.len() && 0 <= b < q.sizes@.len() && a != b
            implies q.sizes@[a] != q.sizes@[b] by {
            if a < b { assert(q.sizes@[a] < q.sizes@[b]); } else { assert(q.sizes@[b] < q.sizes@[a]); }
        }
    }
}

/// A part row is coded in the round exactly when it lies in the window and passes the part conditions; its code is
/// its local group.
pub proof fn lemma_round_coded(q: QualTabs, c: Cols, t: Tabs, m: Prm, r: Rnd, j: int)
    requires cols_ok(c, t), round_tabs(q, c, m, r), 0 <= j < c.p.n,
    ensures
        coded(q, c.p, j) <==> (r.b0 <= bidx(c.p, j) < r.b1 && r.t0 <= tidx(c.p, j) < r.t1 && bsel(c, m, j)
            && tsel(c, m, j) && in_sizes(m, Val::Int(sval(c.p, j)))),
        coded(q, c.p, j) ==> in_round(r, bidx(c.p, j), tidx(c.p, j), slot_of(q.sizes@, sval(c.p, j)))
            && code_of(q, c.p, j) == gid(r, bidx(c.p, j), tidx(c.p, j), slot_of(q.sizes@, sval(c.p, j)))
            && q.sizes@[slot_of(q.sizes@, sval(c.p, j))] == sval(c.p, j),
{
    assert(part_row_ok(c.p, t.p[j], j));
    let (b, tt, v) = (bidx(c.p, j), tidx(c.p, j), sval(c.p, j));
    assert(0 <= b < q.bterm@.len() && 0 <= tt < q.tterm@.len());
    assert(listed(q.sizes@, v) == m.sizes.contains(v));
    if r.b0 <= b < r.b1 && bsel(c, m, j) && r.t0 <= tt < r.t1 && tsel(c, m, j) {
        lemma_gid_bound(r, b, tt, 0);
    }
    if coded(q, c.p, j) {
        let z = slot_of(q.sizes@, v);
        assert(0 <= z < q.sizes@.len() && q.sizes@[z] == v);
        lemma_gid_bound(r, b, tt, z);
    }
}

/// Dictionary entries are distinct texts.
pub proof fn lemma_dict_inj(o: Seq<u64>, y: Seq<u8>, a: int, b: int)
    requires
        crate::stores::custpart::interface::common::colfmt::dict_sorted(o, y, o.len() - 1),
        0 <= a < o.len() - 1, 0 <= b < o.len() - 1,
        txt(o, y, a) == txt(o, y, b),
    ensures a == b,
{
    if a != b {
        crate::stores::custpart::interface::common::colfmt::lemma_dict_distinct(o, y, o.len() - 1, a, b);
        assert(crate::stores::custpart::interface::common::colfmt::text_of(o, y, a) == txt(o, y, a));
        assert(crate::stores::custpart::interface::common::colfmt::text_of(o, y, b) == txt(o, y, b));
    }
}

/// The SQL key of brand entry `b`, type entry `tt` and listed size slot `z`.
pub open spec fn key_bt(c: Cols, sizes: Seq<i64>, b: int, tt: int, z: int) -> Row {
    seq![Val::Text(txt(c.p.brand_o@, c.p.brand_y@, b)), Val::Text(txt(c.p.type_o@, c.p.type_y@, tt)),
        Val::Int(sizes[z] as int)]
}

/// A part row has the key of (`b`, `tt`, `z`) exactly when its entries are `b`, `tt` and its size is slot `z`'s.
proof fn lemma_key_bt(c: Cols, t: Tabs, q: QualTabs, m: Prm, r: Rnd, j: int, b: int, tt: int, z: int)
    requires
        cols_ok(c, t), round_tabs(q, c, m, r), 0 <= j < c.p.n,
        in_round(r, b, tt, z),
    ensures
        prow_key(t, j) == key_bt(c, q.sizes@, b, tt, z)
            <==> (bidx(c.p, j) == b && tidx(c.p, j) == tt && sval(c.p, j) == q.sizes@[z]),
{
    lemma_prow_key(c, t, j);
    assert(part_row_ok(c.p, t.p[j], j));
    let k1 = prow_key(t, j);
    let k2 = key_bt(c, q.sizes@, b, tt, z);
    if k1 == k2 {
        assert(k1[0] == k2[0] && k1[1] == k2[1] && k1[2] == k2[2]);
        lemma_dict_inj(c.p.brand_o@, c.p.brand_y@, bidx(c.p, j), b);
        lemma_dict_inj(c.p.type_o@, c.p.type_y@, tidx(c.p, j), tt);
    }
    if bidx(c.p, j) == b && tidx(c.p, j) == tt && sval(c.p, j) == q.sizes@[z] {
        assert(k1 =~= k2);
    }
}

/// The round's distinct supplier rows of local group `g`: the rows with a pair of `g` that the subquery keeps.
pub open spec fn pset(q: QualTabs, c: Cols, g: int) -> Set<int> {
    Set::range(0, c.s.n as int).filter(|x: int| pair_in(q, c, 0, c.p.n as int, g, x) && !cc_row(c.s, x))
}

/// The round's distinct supplier rows of a local group have the size of the SQL key's distinct suppkeys.
pub proof fn lemma_group_card(c: Cols, t: Tabs, m: Prm, q: QualTabs, r: Rnd, b: int, tt: int, z: int)
    requires
        cols_ok(c, t), keys_unique(t), fk_supp(t),
        round_tabs(q, c, m, r),
        in_round(r, b, tt, z),
    ensures
        pset(q, c, gid(r, b, tt, z)).len() == kv(t, m, key_bt(c, q.sizes@, b, tt, z)).len(),
{
    let g = gid(r, b, tt, z);
    let ds = pset(q, c, g);
    let k = key_bt(c, q.sizes@, b, tt, z);
    let ks = kv(t, m, k);
    let f = |x: int| t.s[x][0];
    lemma_tabs_typed(c, t);
    // Every distinct supplier row's key is a distinct suppkey of the key.
    assert forall|x: int| #[trigger] ds.contains(x) implies ks.contains(f(x)) by {
        assert(pair_in(q, c, 0, c.p.n as int, g, x) && !cc_row(c.s, x));
        let (j, i) = choose|j: int, i: int| 0 <= j < c.p.n && #[trigger] pair_at(q, c, j, i, g, x);
        lemma_round_coded(q, c, t, m, r, j);
        let zj = slot_of(q.sizes@, sval(c.p, j));
        lemma_gid_inj(r, bidx(c.p, j), tidx(c.p, j), zj, b, tt, z);
        assert(srow_of(c, i, x));
        lemma_qual_cols(c, t, m, i, j, x);
        lemma_key_bt(c, t, q, m, r, j, b, tt, z);
        assert(ps_row_ok(c.ps, t.ps[i], i));
        assert(supp_row_ok(c.s, t.s[x], x));
        lemma_kv_has(t, m, k, f(x));
    }
    // Every distinct suppkey of the key is some distinct supplier row's key.
    assert forall|v: Val| #[trigger] ks.contains(v) implies exists|x: int| ds.contains(x) && f(x) == v by {
        lemma_kv_has(t, m, k, v);
        let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k && t.ps[i][1] == v;
        lemma_srow_exists(c, t, i);
        let x = choose|x: int| #[trigger] srow_of(c, i, x);
        lemma_qual_cols(c, t, m, i, j, x);
        lemma_key_bt(c, t, q, m, r, j, b, tt, z);
        lemma_round_coded(q, c, t, m, r, j);
        assert(listed(q.sizes@, sval(c.p, j)));
        let zj = slot_of(q.sizes@, sval(c.p, j));
        lemma_round_shape(q, c, m, r);
        assert(q.sizes@.no_duplicates());
        assert(zj == z) by {
            if zj != z { assert(q.sizes@[zj] == q.sizes@[z]); }
        }
        assert(pair_at(q, c, j, i, g, x));
        assert(pair_in(q, c, 0, c.p.n as int, g, x));
        assert(ds.contains(x));
        assert(ps_row_ok(c.ps, t.ps[i], i));
        assert(supp_row_ok(c.s, t.s[x], x));
    }
    // Supplier keys are unique.
    assert(ds.injective_on(f)) by {
        assert forall|x1: int, x2: int| ds.contains(x1) && ds.contains(x2) && #[trigger] f(x1) == #[trigger] f(x2) implies x1 == x2 by {}
        assert(ds.to_iset().injective_on(f)) by {
            assert forall|x1: int, x2: int| ds.to_iset().contains(x1) && ds.to_iset().contains(x2) && #[trigger] f(x1) == #[trigger] f(x2)
                implies x1 == x2 by {
                assert(ds.contains(x1) && ds.contains(x2));
            }
        }
    }
    assert(ds.map(f) =~= ks) by {
        assert forall|v: Val| ds.map(f).contains(v) <==> ks.contains(v) by {
            ds.lemma_map_contains(f, v);
        }
    }
    vstd::set_lib::lemma_map_size(ds, ks, f);
}

/// The column handles' row facts give the statement's value shapes.
pub proof fn lemma_tabs_typed(c: Cols, t: Tabs)
    requires cols_ok(c, t),
    ensures tabs_typed(t),
{
    assert forall|j: int| 0 <= j < t.p.len() implies #[trigger] p_typed(t.p[j]) by {
        assert(part_row_ok(c.p, t.p[j], j));
    }
    assert forall|i: int| 0 <= i < t.ps.len() implies #[trigger] ps_typed(t.ps[i]) by {
        assert(ps_row_ok(c.ps, t.ps[i], i));
    }
    assert forall|j: int| 0 <= j < t.s.len() implies #[trigger] s_shape(t.s[j]) by {
        assert(supp_row_ok(c.s, t.s[j], j));
    }
}

} // verus!
