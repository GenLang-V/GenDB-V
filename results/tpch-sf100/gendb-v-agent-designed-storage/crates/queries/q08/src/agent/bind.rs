//! Binding of the scan to the SQL meaning (logic only; `decode` derives the model from the stored parts).
//!
//! `dmodel` states what the decoded columns are in terms of the database's tables: the stored lineitem rows
//! (`lrows`, a permutation of the projected lineitem relation), the stored orders rows (canonical row `omap[p]` of
//! orders at stored position `p`), and customer, part, supplier and nation in canonical order, with the part filter
//! and the nation statuses. Under it each stored lineitem row's scan contribution `lc` is the SQL contribution
//! `lhit` of its row (`lemma_row_eq`), so every accumulator field over all stored rows is the corresponding sum over
//! the joined rows (`lemma_bind_field`) and the scan's accumulators are the year groups' sums (`lemma_bind`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::Literal;
use crate::link::expr::ival;
use crate::link::join::{sum_of, keep};
use crate::link::query::{proj, proj_all};
use super::sql::*;
use super::group::*;
use super::norm::*;
use super::join::*;
use super::model::*;
use super::kernel::{PFilter, pkey, ptype, pmatch, pm_of};

verus! {

// ------------------------------------------------------------------------------------------------ accumulator fields

/// Field `k` of the accumulators: 0..4 for 1995 (count, volume, `$1` count, `$1` volume, mass), 5..9 for 1996.
pub open spec fn afield(s: AccS, k: int) -> int {
    if k == 0 { s.c0 } else if k == 1 { s.v0 } else if k == 2 { s.hc0 } else if k == 3 { s.hv0 } else if k == 4 { s.m0 }
    else if k == 5 { s.c1 } else if k == 6 { s.v1 } else if k == 7 { s.hc1 } else if k == 8 { s.hv1 } else { s.m1 }
}

pub open spec fn kyear(k: int) -> int {
    if k < 5 { 1995 } else { 1996 }
}

pub open spec fn kpos(k: int) -> int {
    if k < 5 { k } else { k - 5 }
}

/// The weight of field `k` on one contribution.
pub open spec fn wsel(k: int) -> spec_fn(LHit) -> int {
    |h: LHit| if h.year != kyear(k) { 0int }
        else if kpos(k) == 0 { 1int }
        else if kpos(k) == 1 { h.vol }
        else if kpos(k) == 2 { if h.hit { 1int } else { 0int } }
        else if kpos(k) == 3 { if h.hit { h.vol } else { 0int } }
        else { abs(h.vol) }
}

/// The weight of field `k` on one joined row.
pub open spec fn wrow(b0: Seq<u8>, k: int) -> spec_fn(Row) -> int {
    if kpos(k) == 0 { w_cnt(kyear(k)) }
    else if kpos(k) == 1 { w_vol(kyear(k)) }
    else if kpos(k) == 2 { w_hcnt(b0, kyear(k)) }
    else if kpos(k) == 3 { w_hvol(b0, kyear(k)) }
    else { w_mass(kyear(k)) }
}

proof fn lemma_weight(b0: Seq<u8>, k: int)
    requires 0 <= k < 10,
    ensures weight_of(wrow(b0, k), wsel(k), b0),
{
    assert forall|x: Row| #[trigger] wrow(b0, k)(x)
        == wsel(k)(LHit { year: jyear(x), vol: vol_of(x), hit: x[54] == Val::Text(b0) }) by {
        let h = LHit { year: jyear(x), vol: vol_of(x), hit: x[54] == Val::Text(b0) };
        if kpos(k) == 0 {
            assert(wrow(b0, k)(x) == w_cnt(kyear(k))(x));
        } else if kpos(k) == 1 {
            assert(wrow(b0, k)(x) == w_vol(kyear(k))(x));
        } else if kpos(k) == 2 {
            assert(wrow(b0, k)(x) == w_hcnt(b0, kyear(k))(x));
        } else if kpos(k) == 3 {
            assert(wrow(b0, k)(x) == w_hvol(b0, kyear(k))(x));
        } else {
            assert(wrow(b0, k)(x) == w_mass(kyear(k))(x));
        }
    }
}

proof fn lemma_afield(h: Option<LHit>, a: AccS, b: AccS, k: int)
    requires 0 <= k < 10,
    ensures
        afield(acc_of(h), k) == hterm(h, wsel(k)),
        afield(acc_add(a, b), k) == afield(a, k) + afield(b, k),
        afield(acc_zero(), k) == 0,
{
    if let Some(v) = h {
        assert(absv(v.vol) == abs(v.vol));
    }
}

/// Field `k` over the stored lineitem rows `[0, b)`, row by row.
pub open spec fn fsum(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, b: int, k: int) -> int
    decreases b,
{
    if b <= 0 { 0 } else { fsum(m, pm, ns, b - 1, k) + hterm(lc(m, pm, ns, b - 1), wsel(k)) }
}

proof fn lemma_acc_field(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, b: int, k: int)
    requires 0 <= b, 0 <= k < 10,
    ensures afield(acc_range(m, pm, ns, 0, b), k) == fsum(m, pm, ns, b, k),
    decreases b,
{
    if b > 0 {
        lemma_acc_field(m, pm, ns, b - 1, k);
        lemma_afield(lc(m, pm, ns, b - 1), acc_range(m, pm, ns, 0, b - 1), acc_of(lc(m, pm, ns, b - 1)), k);
    } else {
        lemma_afield(None, acc_zero(), acc_zero(), k);
    }
}

// ------------------------------------------------------------------------------------------------ the decoded model

/// Stored lineitem row `j`'s columns.
pub open spec fn lrow_ok(m: Cols, l: Row, j: int) -> bool {
    &&& l[0] == Val::Int(lk(m, j))
    &&& l[1] == Val::Int(lp(m, j))
    &&& l[2] == Val::Int(ls(m, j))
    &&& l[5] == (Val::Num { coeff: le(m, j), scale: 2 })
    &&& l[6] == (Val::Num { coeff: ld(m, j), scale: 2 })
}

/// Stored orders row `p`'s columns, in the canonical orders row `o`.
pub open spec fn orow_ok(m: Cols, o: Row, p: int) -> bool {
    &&& o[0] == Val::Int(okey(m, p))
    &&& o[1] == Val::Int(oc(m, p))
    &&& o[4] == Val::Date(od(m, p))
}

/// Canonical orders row `i` is stored somewhere.
pub open spec fn ocovered(omap: Seq<int>, i: int) -> bool {
    exists|p: int| 0 <= p < omap.len() && omap[p] == i
}

/// The region of nation row `n1` is named `$2`.
pub open spec fn nat_reg(db: Database, ps: Seq<Literal>, n1: Row) -> bool {
    match find(db.tables[7], n1[2]) {
        Some(r) => r[1] == Val::Text(txt(ps[1])),
        None => false,
    }
}

pub open spec fn cust_ok(db: Database, m: Cols) -> bool {
    &&& db.tables[2].len() == m.n_c
    &&& forall|i: int| 0 <= i < m.n_c ==> (#[trigger] db.tables[2][i])[0] == Val::Int(ck(m, i))
        && db.tables[2][i][3] == Val::Int(cn(m, i))
}

pub open spec fn supp_ok(db: Database, m: Cols) -> bool {
    &&& db.tables[5].len() == m.n_s
    &&& forall|i: int| 0 <= i < m.n_s ==> (#[trigger] db.tables[5][i])[0] == Val::Int(sk(m, i))
        && db.tables[5][i][3] == Val::Int(sn(m, i))
}

pub open spec fn part_ok(db: Database, ps: Seq<Literal>, f: PFilter) -> bool {
    &&& db.tables[3].len() == f.n_p
    &&& forall|i: int| 0 <= i < f.n_p ==> (#[trigger] db.tables[3][i])[0] == Val::Int(pkey(f, i))
        && (db.tables[3][i][4] == Val::Text(txt(ps[2]))) == (f.has_t && ptype(f, i) == f.t)
}

pub open spec fn nation_ok(db: Database, ps: Seq<Literal>, ns: NStat) -> bool {
    &&& nstat_wf(ns)
    &&& db.tables[6].len() == ns.keys.len()
    &&& forall|i: int| 0 <= i < ns.keys.len() ==> (#[trigger] db.tables[6][i])[0] == Val::Int(ns.keys[i] as int)
        && (db.tables[6][i][1] == Val::Text(txt(ps[0]))) == ns.name[i]
        && ns.reg[i] == nat_reg(db, ps, db.tables[6][i])
}

pub open spec fn orders_ok(db: Database, m: Cols, omap: Seq<int>) -> bool {
    &&& db.tables[1].len() == m.n_o && omap.len() == m.n_o
    &&& forall|p: int| 0 <= p < m.n_o ==> 0 <= #[trigger] omap[p] < m.n_o && orow_ok(m, db.tables[1][omap[p]], p)
    &&& forall|i: int| 0 <= i < m.n_o ==> #[trigger] ocovered(omap, i)
}

/// The decoded columns in terms of the database's tables.
pub open spec fn dmodel(db: Database, ps: Seq<Literal>, m: Cols, f: PFilter, ns: NStat, lrows: Seq<Row>, omap: Seq<int>) -> bool {
    &&& join_ok(db)
    &&& m.lo == d95() && m.hi == d96e()
    &&& lrows.len() == m.n_l
    &&& forall|j: int| 0 <= j < m.n_l ==> lrow_ok(m, #[trigger] lrows[j], j)
    &&& orders_ok(db, m, omap)
    &&& cust_ok(db, m)
    &&& part_ok(db, ps, f)
    &&& supp_ok(db, m)
    &&& nation_ok(db, ps, ns)
}

// ------------------------------------------------------------------------------------------------ lookups

proof fn lemma_found_at(t: Seq<Row>, v: Val, i: int)
    requires key0(t), 0 <= i < t.len(), t[i][0] == v,
    ensures find(t, v) == Some(t[i]),
{
    lemma_find(t, v);
}

proof fn lemma_found_none(t: Seq<Row>, v: Val)
    requires key0(t), forall|i: int| 0 <= i < t.len() ==> (#[trigger] t[i])[0] != v,
    ensures find(t, v) is None,
{
    lemma_find(t, v);
}

proof fn lemma_part(db: Database, ps: Seq<Literal>, f: PFilter, v: int)
    requires join_ok(db), part_ok(db, ps, f),
    ensures pmatch(f, v) == (find(db.tables[3], Val::Int(v)) matches Some(p) && p[4] == Val::Text(txt(ps[2]))),
{
    let t = db.tables[3];
    if exists|i: int| 0 <= i < f.n_p && #[trigger] pkey(f, i) == v {
        let i = choose|i: int| 0 <= i < f.n_p && #[trigger] pkey(f, i) == v;
        assert(t[i][0] == Val::Int(v));
        lemma_found_at(t, Val::Int(v), i);
        if pmatch(f, v) {
            let i2 = choose|i2: int| 0 <= i2 < f.n_p && #[trigger] pkey(f, i2) == v && ptype(f, i2) == f.t;
            assert(t[i2][0] == Val::Int(v));
            assert(i2 == i);
        }
    } else {
        assert forall|i: int| 0 <= i < t.len() implies (#[trigger] t[i])[0] != Val::Int(v) by {
            assert(t[i][0] == Val::Int(pkey(f, i)));
        }
        lemma_found_none(t, Val::Int(v));
    }
}

proof fn lemma_cust(db: Database, m: Cols, k: int)
    requires join_ok(db), cust_ok(db, m),
    ensures
        cfind(m, k) matches Some(ci) ==> 0 <= ci < m.n_c && find(db.tables[2], Val::Int(k)) == Some(db.tables[2][ci]),
        cfind(m, k) is None ==> find(db.tables[2], Val::Int(k)) is None,
{
    let t = db.tables[2];
    if exists|i: int| 0 <= i < m.n_c && #[trigger] ck(m, i) == k {
        let i = choose|i: int| 0 <= i < m.n_c && #[trigger] ck(m, i) == k;
        assert(cfind(m, k) == Some(i));
        lemma_found_at(t, Val::Int(k), i);
    } else {
        assert forall|i: int| 0 <= i < t.len() implies (#[trigger] t[i])[0] != Val::Int(k) by {
            assert(t[i][0] == Val::Int(ck(m, i)));
        }
        lemma_found_none(t, Val::Int(k));
    }
}

proof fn lemma_supp(db: Database, m: Cols, k: int)
    requires join_ok(db), supp_ok(db, m),
    ensures
        sfind(m, k) matches Some(si) ==> 0 <= si < m.n_s && find(db.tables[5], Val::Int(k)) == Some(db.tables[5][si]),
        sfind(m, k) is None ==> find(db.tables[5], Val::Int(k)) is None,
{
    let t = db.tables[5];
    if exists|i: int| 0 <= i < m.n_s && #[trigger] sk(m, i) == k {
        let i = choose|i: int| 0 <= i < m.n_s && #[trigger] sk(m, i) == k;
        assert(sfind(m, k) == Some(i));
        lemma_found_at(t, Val::Int(k), i);
    } else {
        assert forall|i: int| 0 <= i < t.len() implies (#[trigger] t[i])[0] != Val::Int(k) by {
            assert(t[i][0] == Val::Int(sk(m, i)));
        }
        lemma_found_none(t, Val::Int(k));
    }
}

proof fn lemma_nat(db: Database, ps: Seq<Literal>, ns: NStat, k: int)
    requires join_ok(db), nation_ok(db, ps, ns),
    ensures
        nfind(ns, k) matches Some(ni) ==> 0 <= ni < ns.keys.len() && find(db.tables[6], Val::Int(k)) == Some(db.tables[6][ni]),
        nfind(ns, k) is None ==> find(db.tables[6], Val::Int(k)) is None,
        nreg(ns, k) == (find(db.tables[6], Val::Int(k)) matches Some(n1) && nat_reg(db, ps, n1)),
{
    let t = db.tables[6];
    if exists|i: int| 0 <= i < ns.keys.len() && #[trigger] ns.keys[i] == k {
        let i = choose|i: int| 0 <= i < ns.keys.len() && #[trigger] ns.keys[i] == k;
        assert(nfind(ns, k) == Some(i));
        assert(t[i][0] == Val::Int(k));
        lemma_found_at(t, Val::Int(k), i);
    } else {
        assert forall|i: int| 0 <= i < t.len() implies (#[trigger] t[i])[0] != Val::Int(k) by {
            assert(t[i][0] == Val::Int(ns.keys[i] as int));
        }
        lemma_found_none(t, Val::Int(k));
    }
}

proof fn lemma_order(db: Database, m: Cols, omap: Seq<int>, k: int)
    requires join_ok(db), orders_ok(db, m, omap),
    ensures
        rpos(m, k) < m.n_o ==> 0 <= omap[rpos(m, k)] < m.n_o
            && find(db.tables[1], Val::Int(k)) == Some(db.tables[1][omap[rpos(m, k)]]),
        rpos(m, k) >= m.n_o ==> find(db.tables[1], Val::Int(k)) is None,
{
    let t = db.tables[1];
    lemma_rpos(m, k);
    let p = rpos(m, k);
    if p < m.n_o {
        assert(orow_ok(m, t[omap[p]], p));
        lemma_found_at(t, Val::Int(k), omap[p]);
    } else {
        assert forall|i: int| 0 <= i < t.len() implies (#[trigger] t[i])[0] != Val::Int(k) by {
            assert(ocovered(omap, i));
            let q = choose|q: int| 0 <= q < omap.len() && omap[q] == i;
            assert(orow_ok(m, t[omap[q]], q));
            assert(okey(m, q) != k);
        }
        lemma_found_none(t, Val::Int(k));
    }
}

// ------------------------------------------------------------------------------------------------ one row

/// A stored lineitem row's scan contribution is its SQL contribution.
pub proof fn lemma_row_eq(db: Database, ps: Seq<Literal>, m: Cols, f: PFilter, ns: NStat, lrows: Seq<Row>, omap: Seq<int>, j: int)
    requires dmodel(db, ps, m, f, ns, lrows, omap), 0 <= j < m.n_l,
    ensures lc(m, pm_of(f), ns, j) == lhit(db, ps, lrows[j]),
{
    let t = db.tables;
    let l = lrows[j];
    assert(lrow_ok(m, l, j));
    lemma_part(db, ps, f, lp(m, j));
    assert(pm_of(f)(lp(m, j)) == pmatch(f, lp(m, j)));
    if !pmatch(f, lp(m, j)) {
        return;
    }
    let pr = find(t[3], l[1])->Some_0;
    lemma_supp(db, m, ls(m, j));
    lemma_rpos(m, lk(m, j));
    lemma_order(db, m, omap, lk(m, j));
    let p = rpos(m, lk(m, j));
    if sfind(m, ls(m, j)) is None {
        // lhit: no supplier; lc: no supplier after the other lookups.
        if p < m.n_o {
            let o = t[1][omap[p]];
            assert(orow_ok(m, o, p));
            if m.lo <= od(m, p) <= m.hi {
                lemma_cust(db, m, oc(m, p));
                if let Some(ci) = cfind(m, oc(m, p)) {
                    lemma_nat(db, ps, ns, cn(m, ci));
                }
            }
        }
        return;
    }
    let si = sfind(m, ls(m, j))->Some_0;
    let s = t[5][si];
    assert(s[3] == Val::Int(sn(m, si)));
    if p >= m.n_o {
        return;
    }
    let o = t[1][omap[p]];
    assert(orow_ok(m, o, p));
    assert(dval(o[4]) == od(m, p));
    if !(m.lo <= od(m, p) <= m.hi) {
        return;
    }
    lemma_cust(db, m, oc(m, p));
    if cfind(m, oc(m, p)) is None {
        return;
    }
    let ci = cfind(m, oc(m, p))->Some_0;
    let c = t[2][ci];
    assert(c[3] == Val::Int(cn(m, ci)));
    lemma_nat(db, ps, ns, cn(m, ci));
    lemma_nat(db, ps, ns, sn(m, si));
    if !nreg(ns, cn(m, ci)) {
        return;
    }
    if let Some(ni) = nfind(ns, sn(m, si)) {
        let n2 = t[6][ni];
        assert(n2[1] == Val::Text(txt(ps[0])) <==> ns.name[ni]);
        assert(ival(l[5]) == le(m, j) && ival(l[6]) == ld(m, j));
    }
}

// ------------------------------------------------------------------------------------------------ sums

/// The SQL term of a lineitem row for field `k`.
pub open spec fn lterm(db: Database, ps: Seq<Literal>, k: int) -> spec_fn(Row) -> int {
    |l: Row| hterm(lhit(db, ps, l), wsel(k))
}

proof fn lemma_fsum_rows(db: Database, ps: Seq<Literal>, m: Cols, f: PFilter, ns: NStat, lrows: Seq<Row>, omap: Seq<int>,
    b: int, k: int)
    requires dmodel(db, ps, m, f, ns, lrows, omap), 0 <= b <= m.n_l,
    ensures fsum(m, pm_of(f), ns, b, k) == sum_of(lrows.take(b), lterm(db, ps, k)),
    decreases b,
{
    if b > 0 {
        lemma_fsum_rows(db, ps, m, f, ns, lrows, omap, b - 1, k);
        lemma_row_eq(db, ps, m, f, ns, lrows, omap, b - 1);
        assert(lrows.take(b).drop_last() =~= lrows.take(b - 1));
        assert(lrows.take(b).last() == lrows[b - 1]);
    } else {
        assert(lrows.take(0) =~= Seq::<Row>::empty());
    }
}

/// `lhit` reads columns 0, 1, 2, 5 and 6 of the lineitem row only.
proof fn lemma_lhit_proj(db: Database, ps: Seq<Literal>, l: Row, cols: Seq<nat>)
    requires
        l.len() == 16,
        cols.len() == 15,
        forall|c: int| 0 <= c < 15 ==> #[trigger] cols[c] == c,
    ensures lhit(db, ps, proj(l, cols)) == lhit(db, ps, l),
{
    let pl = proj(l, cols);
    assert(pl[0] == l[0] && pl[1] == l[1] && pl[2] == l[2] && pl[5] == l[5] && pl[6] == l[6]);
}

/// Field `k` of the scan over all stored lineitem rows is the sum of field `k`'s weight over the joined rows.
pub proof fn lemma_bind_field(db: Database, ps: Seq<Literal>, m: Cols, f: PFilter, ns: NStat, lrows: Seq<Row>,
    omap: Seq<int>, k: int)
    requires
        db_ok(db),
        dmodel(db, ps, m, f, ns, lrows, omap),
        0 <= k < 10,
        lrows.to_multiset() == proj_all(db.tables[0], crate::stores::factsdir::declaration::stored_cols_t0()).to_multiset(),
    ensures afield(acc_range(m, pm_of(f), ns, 0, m.n_l as int), k) == sum_of(jrows(db), jterm(ps, wrow(txt(ps[0]), k))),
{
    let t0 = db.tables[0];
    let cols = crate::stores::factsdir::declaration::stored_cols_t0();
    let rel = proj_all(t0, cols);
    let lt = lterm(db, ps, k);
    let b0 = txt(ps[0]);
    let w = wrow(b0, k);
    lemma_acc_field(m, pm_of(f), ns, m.n_l as int, k);
    lemma_fsum_rows(db, ps, m, f, ns, lrows, omap, m.n_l as int, k);
    assert(lrows.take(m.n_l as int) =~= lrows);
    crate::link::join::lemma_sum_of_perm(lrows, rel, lt);
    let pm = |r: Row| proj(r, cols);
    assert(rel =~= t0.map_values(pm));
    crate::link::join::lemma_sum_of_map(t0, pm, lt);
    assert(sum_of(lrows, lt) == sum_of(t0, |r: Row| lt(pm(r))));
    lemma_tables_typed(db);
    assert forall|i: int| 0 <= i < t0.len() implies #[trigger] lt(proj(t0[i], cols)) == c1f(db, jterm(ps, w))(t0[i]) by {
        assert(li_typed(t0[i]));
        assert(cols =~= seq![0nat, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
        lemma_lhit_proj(db, ps, t0[i], cols);
        lemma_weight(b0, k);
        lemma_c1_lhit(db, ps, w, wsel(k), t0[i]);
    }
    crate::link::join::lemma_sum_of_ext(t0, |r: Row| lt(pm(r)), c1f(db, jterm(ps, w)));
    lemma_collapse_all(db, ps, w);
    assert(afield(acc_range(m, pm_of(f), ns, 0, m.n_l as int), k) == sum_of(lrows, lt));
}

/// The scan's accumulators of both years against the year groups of the inner rows.
pub open spec fn acc_meets(db: Database, ps: Seq<Literal>, s: AccS) -> bool {
    let zs = inner_rows(db, ps);
    let b0 = txt(ps[0]);
    let (k5, k6) = (ykey(1995), ykey(1996));
    &&& s.c0 == gcnt(zs, k5) && s.v0 == gsum1(zs, k5) && s.hc0 == hcnt(b0, zs, k5) && s.hv0 == gsum0(b0, zs, k5)
    &&& s.m0 == gmass(zs, k5)
    &&& s.c1 == gcnt(zs, k6) && s.v1 == gsum1(zs, k6) && s.hc1 == hcnt(b0, zs, k6) && s.hv1 == gsum0(b0, zs, k6)
    &&& s.m1 == gmass(zs, k6)
}

/// Under the decoded model the scan over all stored lineitem rows gives the year groups' sums.
pub proof fn lemma_bind(db: Database, ps: Seq<Literal>, m: Cols, f: PFilter, ns: NStat, lrows: Seq<Row>, omap: Seq<int>)
    requires
        db_ok(db),
        dmodel(db, ps, m, f, ns, lrows, omap),
        lrows.to_multiset() == proj_all(db.tables[0], crate::stores::factsdir::declaration::stored_cols_t0()).to_multiset(),
    ensures acc_meets(db, ps, acc_range(m, pm_of(f), ns, 0, m.n_l as int)),
{
    let s = acc_range(m, pm_of(f), ns, 0, m.n_l as int);
    let b0 = txt(ps[0]);
    let rows = jrows(db);
    assert forall|k: int| 0 <= k < 10 implies #[trigger] afield(s, k) == sum_of(rows, jterm(ps, wrow(b0, k))) by {
        lemma_bind_field(db, ps, m, f, ns, lrows, omap, k);
    }
    lemma_accs(ps, rows, 1995);
    lemma_accs(ps, rows, 1996);
    assert(inner_rows(db, ps) == keep(rows, |x: Row| jqual(ps, x)).map_values(|x: Row| inner_row(x)));
    assert(afield(s, 0) == sum_of(rows, jterm(ps, wrow(b0, 0))));
    assert(afield(s, 1) == sum_of(rows, jterm(ps, wrow(b0, 1))));
    assert(afield(s, 2) == sum_of(rows, jterm(ps, wrow(b0, 2))));
    assert(afield(s, 3) == sum_of(rows, jterm(ps, wrow(b0, 3))));
    assert(afield(s, 4) == sum_of(rows, jterm(ps, wrow(b0, 4))));
    assert(afield(s, 5) == sum_of(rows, jterm(ps, wrow(b0, 5))));
    assert(afield(s, 6) == sum_of(rows, jterm(ps, wrow(b0, 6))));
    assert(afield(s, 7) == sum_of(rows, jterm(ps, wrow(b0, 7))));
    assert(afield(s, 8) == sum_of(rows, jterm(ps, wrow(b0, 8))));
    assert(afield(s, 9) == sum_of(rows, jterm(ps, wrow(b0, 9))));
}

} // verus!
