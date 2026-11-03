//! The groups of the normal forms in terms of the scan and the grouping: the outer GROUP BY's sums and keys are
//! the grouping's `psum` and `gks`; the inner GROUP BY (by cik) has as many groups as there are distinct ciks
//! (`dciks`); the total of all qualifying rows is the grouping's total.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::query::{QuerySpec, gsum, gcount, gkeys, hit, lemma_gkeys, lemma_nodup_same_multiset};
use crate::agent::common::wide::*;
use crate::agent::scan::{NumCols, rsum, rcnt};
use crate::agent::keys::{SubCols, rank_key, lemma_qlist};
use crate::agent::groups::{KeyCols, psum, gks, dciks, lemma_gks, lemma_dciks};
use crate::agent::groups;
use crate::agent::run::totals_ok;
use crate::agent::nf::fromwhere::*;
use crate::agent::nf::group::*;
use crate::agent::nf::sums::*;
use crate::agent::nf::glue::*;

verus! {

pub open spec fn okey_sub_fn() -> spec_fn(Row) -> Row {
    |y: Row| okey_sub(y)
}

pub open spec fn ikey_sub_fn() -> spec_fn(Row) -> Row {
    |y: Row| ikey_sub(y)
}

pub open spec fn unit_row_fn() -> spec_fn(Row) -> Row {
    |y: Row| Seq::<Val>::empty()
}

/// All qualifying rows in one group.
pub open spec fn g_unit(p0: Seq<u8>, p1: int) -> QuerySpec {
    sum_spec(jq_fn(p0, p1), unit_row_fn())
}

/// What the scan and the grouping's inputs are, for a database.
pub open spec fn world(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>) -> bool {
    &&& rows_view(db, num, sub, kc, p1)
    &&& tables_shaped(db)
    &&& totals_ok(num, sub, p0, tot, seen, num.n as int)
    &&& qr.len() == sub.qlist(sub.n as int).len()
    &&& forall|t: int| 0 <= t < qr.len() ==> #[trigger] qr[t] as int == sub.qlist(sub.n as int)[t]
}

/// The rank of qualifying position `a` and its sub row.
proof fn lemma_rank_row(sub: &SubCols, qr: Seq<usize>, a: int)
    requires
        qr.len() == sub.qlist(sub.n as int).len(),
        forall|t: int| 0 <= t < qr.len() ==> #[trigger] qr[t] as int == sub.qlist(sub.n as int)[t],
        0 <= a < qr.len(),
    ensures 0 <= qr[a] < sub.n, rank_key(sub, a) == sub.key(qr[a] as int),
{
    lemma_qlist(sub, sub.n as int);
}

/// The outer group `k`: its SUM is `psum`, and it is a group exactly when `gks` holds it.
pub proof fn lemma_outer_group(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, k: Row)
    requires world(db, num, sub, kc, p0, p1, qr, tot, seen),
    ensures
        gsum(g_out(p0, p1), joined(db), k, 0) == psum(kc, qr, tot, seen, k, qr.len() as int),
        (gcount(g_out(p0, p1), joined(db), k) > 0) == gks(kc, qr, seen, qr.len() as int).contains(k),
{
    let g = g_out(p0, p1);
    let nq = qr.len() as int;
    assert forall|x: Row, y: Row| shape_num(x) && shape_sub(y) implies #[trigger] (g.key)(x + y) == okey_sub_fn()(y) by {
        assert((x + y)[11] == y[2] && (x + y)[10] == y[1]);
        assert(okey(x + y) =~= okey_sub(y));
    }
    lemma_group_by_subs(db, p0, p1, g.key, okey_sub_fn(), k);
    assert forall|j: int| 0 <= j < sub.n implies #[trigger] okey_sub_fn()(db.tables[0][j]) == okey_fn(kc)(j) by {
        assert(okey_sub(db.tables[0][j]) =~= kc.okey(j));
    }
    lemma_subs_ranks(db, num, sub, kc, p0, p1, okey_sub_fn(), okey_fn(kc), k);
    lemma_psum_rk(num, sub, kc, p0, qr, tot, seen, k, nq);
    lemma_rk_cnt(num, sub, p0, okey_fn(kc), k, nq);
    lemma_gks(kc, qr, seen, nq);
    if gcount(g, joined(db), k) > 0 {
        let a = choose|a: int| 0 <= a < nq && okey_fn(kc)(sub.qlist(sub.n as int)[a]) == k
            && #[trigger] rcnt(num, p0, rank_key(sub, a), 0, num.n as int) > 0;
        assert(seen[a]);
        assert(kc.okey(qr[a] as int) == k);
    }
    if gks(kc, qr, seen, nq).contains(k) {
        let id = choose|id: int| 0 <= id < nq && seen[id] && #[trigger] kc.okey(qr[id] as int) == k;
        assert(rcnt(num, p0, rank_key(sub, id), 0, num.n as int) > 0);
        assert(okey_fn(kc)(sub.qlist(sub.n as int)[id]) == k);
    }
}

/// The inner groups (by cik) are the distinct ciks; their number is `dciks`'s.
pub proof fn lemma_inner_keys(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>)
    requires world(db, num, sub, kc, p0, p1, qr, tot, seen),
    ensures
        gkeys(g_in(p0, p1), joined(db)).len() == dciks(kc, qr, seen, qr.len() as int).len(),
{
    let g = g_in(p0, p1);
    let nq = qr.len() as int;
    let ks = gkeys(g, joined(db));
    let dc = dciks(kc, qr, seen, nq);
    let dk = dc.map_values(|c: int| seq![Val::Int(c)]);
    assert forall|x: Row, y: Row| shape_num(x) && shape_sub(y) implies #[trigger] (g.key)(x + y) == ikey_sub_fn()(y) by {
        assert((x + y)[10] == y[1]);
        assert(ikey(x + y) =~= ikey_sub(y));
    }
    assert forall|j: int| 0 <= j < sub.n implies #[trigger] ikey_sub_fn()(db.tables[0][j]) == ikey_fn(kc)(j) by {
        assert(ikey_sub(db.tables[0][j]) =~= seq![Val::Int(kc.cik(j))]);
    }
    lemma_gkeys(g, joined(db));
    lemma_dciks(kc, qr, seen, nq);
    lemma_dciks_nodup(kc, qr, seen, nq);
    assert forall|k: Row| ks.contains(k) <==> dk.contains(k) by {
        lemma_group_by_subs(db, p0, p1, g.key, ikey_sub_fn(), k);
        lemma_subs_ranks(db, num, sub, kc, p0, p1, ikey_sub_fn(), ikey_fn(kc), k);
        lemma_rk_cnt(num, sub, p0, ikey_fn(kc), k, nq);
        if ks.contains(k) {
            let a = choose|a: int| 0 <= a < nq && ikey_fn(kc)(sub.qlist(sub.n as int)[a]) == k
                && #[trigger] rcnt(num, p0, rank_key(sub, a), 0, num.n as int) > 0;
            assert(seen[a]);
            let c = kc.cik(qr[a] as int);
            assert(dc.contains(c));
            let t = choose|t: int| 0 <= t < dc.len() && dc[t] == c;
            assert(dk[t] == k);
        }
        if dk.contains(k) {
            let t = choose|t: int| 0 <= t < dk.len() && dk[t] == k;
            assert(dc.contains(dc[t]));
            let id = choose|id: int| 0 <= id < nq && seen[id] && #[trigger] kc.cik(qr[id] as int) == dc[t];
            assert(rcnt(num, p0, rank_key(sub, id), 0, num.n as int) > 0);
            assert(ikey_fn(kc)(sub.qlist(sub.n as int)[id]) == k);
        }
    }
    assert(dk.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < dk.len() && 0 <= b < dk.len() && a != b implies dk[a] != dk[b] by {
            assert(dc[a] != dc[b]);
            if dk[a] == dk[b] {
                assert(dk[a][0] == dk[b][0]);
            }
        }
    }
    lemma_nodup_same_multiset(ks, dk);
    ks.to_multiset_ensures();
    dk.to_multiset_ensures();
}

/// `dciks` has no duplicates.
pub proof fn lemma_dciks_nodup(kc: &KeyCols, qr: Seq<usize>, seen: Seq<bool>, m: int)
    requires 0 <= m <= qr.len(), m <= seen.len(),
    ensures dciks(kc, qr, seen, m).no_duplicates(),
    decreases m,
{
    if m > 0 {
        lemma_dciks_nodup(kc, qr, seen, m - 1);
    }
}

/// A one-group normal form: the group's SUM is the SUM over all qualifying rows.
proof fn lemma_unit_qsum(g: QuerySpec, xs: Seq<Row>)
    requires forall|x: Row| #[trigger] (g.key)(x) == Seq::<Val>::empty(),
    ensures gsum(g, xs, Seq::<Val>::empty(), 0) == qsum(g, xs),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_unit_qsum(g, xs.drop_last());
        assert(hit(g, xs.last(), Seq::<Val>::empty()) == (g.qual)(xs.last()));
    }
}

/// `qsum` reads only the condition and the argument.
proof fn lemma_qsum_same(g1: QuerySpec, g2: QuerySpec, xs: Seq<Row>)
    requires g1.qual == g2.qual, g1.arg == g2.arg,
    ensures qsum(g1, xs) == qsum(g2, xs),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qsum_same(g1, g2, xs.drop_last());
    }
}

/// The SUM over all qualifying rows is the grouping's total.
pub proof fn lemma_total(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>)
    requires world(db, num, sub, kc, p0, p1, qr, tot, seen),
    ensures qsum(g_in(p0, p1), joined(db)) == groups::tsum(qr, tot, seen, qr.len() as int),
{
    let g = g_unit(p0, p1);
    let e = Seq::<Val>::empty();
    assert forall|x: Row, y: Row| shape_num(x) && shape_sub(y) implies #[trigger] (g.key)(x + y) == unit_row_fn()(y) by {}
    lemma_group_by_subs(db, p0, p1, g.key, unit_row_fn(), e);
    assert forall|j: int| 0 <= j < sub.n implies #[trigger] unit_row_fn()(db.tables[0][j]) == unit_fn()(j) by {}
    lemma_subs_ranks(db, num, sub, kc, p0, p1, unit_row_fn(), unit_fn(), e);
    lemma_psum_rk(num, sub, kc, p0, qr, tot, seen, e, qr.len() as int);
    assert forall|x: Row| #[trigger] (g.key)(x) == e by {}
    lemma_unit_qsum(g, joined(db));
    lemma_qsum_same(g, g_in(p0, p1), joined(db));
}

} // verus!
