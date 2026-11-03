//! ORDER BY total DESC LIMIT 100 over the body's rows: the rows of the picked groups (largest SUM first, none
//! smaller than an unpicked candidate), then the other candidates sorted, are a sorted permutation of the body's
//! rows whose first `min(100, n)` rows are the picked ones.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::bridge::order::{keys_ok, all_keys_ok, key_ok, key_val, lemma_sort_rows};
use crate::bridge::typing::val_family;
use crate::link::query::{gsum, gkeys, full_row, lemma_gkeys, lemma_nodup_same_multiset};
use crate::link::join::{keep, lemma_keep_members};
use crate::query::query_spec_at;
use crate::agent::nf::ast::*;
use crate::agent::nf::fromwhere::*;
use crate::agent::nf::group::coeff;
use crate::agent::nf::sums::*;
use crate::agent::nf::body::*;

verus! {

/// The outer group `k`'s SUM and row.
pub open spec fn osum(db: Database, p0: Seq<u8>, p1: int, k: Row) -> int {
    gsum(g_out(p0, p1), joined(db), k, 0)
}

pub open spec fn orow(db: Database, p0: Seq<u8>, p1: int, k: Row) -> Row {
    full_row(g_out(p0, p1), joined(db), k)
}

/// The rows of the groups `idx` of the key list `ks`.
pub open spec fn rows_at(db: Database, p0: Seq<u8>, p1: int, ks: Seq<Row>, idx: Seq<int>) -> Seq<Row> {
    idx.map_values(|i: int| orow(db, p0, p1, ks[i]))
}

/// The candidates not picked, in order.
pub open spec fn unpicked(cand: Seq<int>, pick: Seq<int>) -> Seq<int>
    decreases cand.len(),
{
    if cand.len() == 0 {
        Seq::empty()
    } else if pick.contains(cand.last()) {
        unpicked(cand.drop_last(), pick)
    } else {
        unpicked(cand.drop_last(), pick).push(cand.last())
    }
}

proof fn lemma_unpicked(cand: Seq<int>, pick: Seq<int>)
    requires cand.no_duplicates(),
    ensures
        unpicked(cand, pick).no_duplicates(),
        forall|x: int| #[trigger] unpicked(cand, pick).contains(x) <==> (cand.contains(x) && !pick.contains(x)),
    decreases cand.len(),
{
    if cand.len() > 0 {
        let ci = cand.drop_last();
        assert(ci.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < ci.len() && 0 <= b < ci.len() && a != b implies ci[a] != ci[b] by {
                assert(ci[a] == cand[a] && ci[b] == cand[b]);
            }
        }
        lemma_unpicked(ci, pick);
        let u = unpicked(cand, pick);
        let ui = unpicked(ci, pick);
        let x0 = cand.last();
        assert(!ci.contains(x0)) by {
            if ci.contains(x0) {
                let a = choose|a: int| 0 <= a < ci.len() && ci[a] == x0;
                assert(cand[a] == cand[cand.len() - 1]);
            }
        }
        assert forall|x: int| #[trigger] u.contains(x) <==> (cand.contains(x) && !pick.contains(x)) by {
            if cand.contains(x) {
                let a = choose|a: int| 0 <= a < cand.len() && cand[a] == x;
                if a < cand.len() - 1 {
                    assert(ci[a] == x);
                }
            }
            if ci.contains(x) {
                let a = choose|a: int| 0 <= a < ci.len() && ci[a] == x;
                assert(cand[a] == x);
            }
            if !pick.contains(x0) {
                if u.contains(x) && x != x0 {
                    let a = choose|a: int| 0 <= a < u.len() && u[a] == x;
                    assert(ui[a] == x);
                }
                if ui.contains(x) {
                    let a = choose|a: int| 0 <= a < ui.len() && ui[a] == x;
                    assert(u[a] == x);
                }
                if x == x0 {
                    assert(u[ui.len() as int] == x0);
                }
            }
        }
        if !pick.contains(x0) {
            assert(u.no_duplicates()) by {
                assert forall|a: int, b: int| 0 <= a < u.len() && 0 <= b < u.len() && a != b implies u[a] != u[b] by {
                    if a < ui.len() && b < ui.len() {
                        assert(u[a] == ui[a] && u[b] == ui[b]);
                    } else if a < ui.len() {
                        assert(u[a] == ui[a]);
                        assert(ui.contains(ui[a]));
                    } else {
                        assert(u[b] == ui[b]);
                        assert(ui.contains(ui[b]));
                    }
                }
            }
        }
    }
}

/// The facts of the answer for one database.
pub open spec fn picked_ok(db: Database, p0: Seq<u8>, p1: int, ac: int, asc: nat, ks: Seq<Row>, cand: Seq<int>,
    pick: Seq<int>) -> bool {
    &&& ks.no_duplicates()
    &&& forall|k: Row| #[trigger] ks.contains(k) <==> gkeys(g_out(p0, p1), joined(db)).contains(k)
    &&& forall|t: int| 0 <= t < cand.len() ==> 0 <= #[trigger] cand[t] < ks.len()
    &&& forall|t1: int, t2: int| 0 <= t1 < t2 < cand.len() ==> #[trigger] cand[t1] < #[trigger] cand[t2]
    &&& forall|i: int| 0 <= i < ks.len() ==> ((num_cmp(osum(db, p0, p1, #[trigger] ks[i]), 4, ac, asc) > 0) == cand.contains(i))
    &&& pick.no_duplicates()
    &&& forall|u: int| 0 <= u < pick.len() ==> cand.contains(#[trigger] pick[u])
    &&& pick.len() == if cand.len() < 100 { cand.len() } else { 100 }
    &&& forall|u: int, v: int| 0 <= u < v < pick.len() ==>
        osum(db, p0, p1, ks[#[trigger] pick[u]]) >= osum(db, p0, p1, ks[#[trigger] pick[v]])
    &&& forall|u: int, t: int| 0 <= u < pick.len() && 0 <= t < cand.len() && !pick.contains(cand[t]) ==>
        osum(db, p0, p1, ks[#[trigger] pick[u]]) >= osum(db, p0, p1, ks[#[trigger] cand[t]])
}

/// A group key's row and its injectivity.
pub proof fn lemma_orow(db: Database, p0: Seq<u8>, p1: int, k: Row)
    requires tables_shaped(db), gkeys(g_out(p0, p1), joined(db)).contains(k),
    ensures
        orow(db, p0, p1, k) == seq![k[0], k[1], Val::Num { coeff: osum(db, p0, p1, k), scale: 4 }],
        k.len() == 2,
        orow(db, p0, p1, k).subrange(0, 2) == k,
{
    let t = choose|t: int| 0 <= t < gkeys(g_out(p0, p1), joined(db)).len() && gkeys(g_out(p0, p1), joined(db))[t] == k;
    lemma_outer_row(db, p0, p1, t);
    assert(orow(db, p0, p1, k).subrange(0, 2) =~= k);
}

/// The ORDER BY comparison of two group rows.
proof fn lemma_cmp_rows(db: Database, p0: Seq<u8>, p1: int, k1: Row, k2: Row)
    requires tables_shaped(db), gkeys(g_out(p0, p1), joined(db)).contains(k1), gkeys(g_out(p0, p1), joined(db)).contains(k2),
    ensures
        (keys_cmp(order_keys(), orow(db, p0, p1, k1), orow(db, p0, p1, k2)) <= 0) == (osum(db, p0, p1, k1) >= osum(db, p0, p1, k2)),
{
    lemma_orow(db, p0, p1, k1);
    lemma_orow(db, p0, p1, k2);
    let (s1, s2) = (osum(db, p0, p1, k1), osum(db, p0, p1, k2));
    let (r1, r2) = (orow(db, p0, p1, k1), orow(db, p0, p1, k2));
    let k = order_keys()[0];
    assert(r1[2] == Val::Num { coeff: s1, scale: 4 });
    assert(r2[2] == Val::Num { coeff: s2, scale: 4 });
    assert(pow10(0) == 1);
    assert(align(s1, 4, 4) == s1);
    assert(align(s2, 4, 4) == s2);
    let c = num_cmp(s1, 4, s2, 4);
    assert(c == sign(s1 - s2));
    assert(compare(r1[2], r2[2]) == Some(c));
    assert(key_cmp(k, r1, r2) == -c);
    assert(order_keys().drop_first() =~= Seq::<OrderKey>::empty());
    reveal_with_fuel(keys_cmp, 2);
    assert(keys_cmp(order_keys(), r1, r2) == -c);
}

/// Every row of `rows_at(ks, idx)` is the row of a group key.
proof fn lemma_rows_keys(db: Database, p0: Seq<u8>, p1: int, ac: int, asc: nat, ks: Seq<Row>, idx: Seq<int>, x: Row)
    requires
        forall|k: Row| #[trigger] ks.contains(k) <==> gkeys(g_out(p0, p1), joined(db)).contains(k),
        forall|t: int| 0 <= t < idx.len() ==> 0 <= #[trigger] idx[t] < ks.len(),
        rows_at(db, p0, p1, ks, idx).contains(x),
    ensures exists|t: int| 0 <= t < idx.len() && x == orow(db, p0, p1, ks[idx[t]]) && gkeys(g_out(p0, p1), joined(db)).contains(#[trigger] ks[idx[t]]),
{
    let t = choose|t: int| 0 <= t < rows_at(db, p0, p1, ks, idx).len() && rows_at(db, p0, p1, ks, idx)[t] == x;
    assert(ks.contains(ks[idx[t]]));
}

/// The rows of the unpicked candidates, sorted, and the permutation of the body's rows.
pub open spec fn rest_sorted(db: Database, p0: Seq<u8>, p1: int, ks: Seq<Row>, cand: Seq<int>, pick: Seq<int>) -> Seq<Row> {
    sort_rows(order_keys(), rows_at(db, p0, p1, ks, unpicked(cand, pick)))
}

pub open spec fn perm(db: Database, p0: Seq<u8>, p1: int, ks: Seq<Row>, cand: Seq<int>, pick: Seq<int>) -> Seq<Row> {
    rows_at(db, p0, p1, ks, pick) + rest_sorted(db, p0, p1, ks, cand, pick)
}

/// Shared facts of the parts.
proof fn lemma_basic(db: Database, p0: Seq<u8>, p1: int, ac: int, asc: nat, ks: Seq<Row>, cand: Seq<int>, pick: Seq<int>)
    requires tables_shaped(db), picked_ok(db, p0, p1, ac, asc, ks, cand, pick),
    ensures ({
        let rest = unpicked(cand, pick);
        let rr = rows_at(db, p0, p1, ks, rest);
        let rs = rest_sorted(db, p0, p1, ks, cand, pick);
        &&& cand.no_duplicates()
        &&& rest.no_duplicates()
        &&& forall|x: int| #[trigger] rest.contains(x) <==> (cand.contains(x) && !pick.contains(x))
        &&& forall|t: int| 0 <= t < rest.len() ==> 0 <= #[trigger] rest[t] < ks.len()
        &&& forall|u: int| 0 <= u < pick.len() ==> 0 <= #[trigger] pick[u] < ks.len()
        &&& forall|i: int| 0 <= i < ks.len() ==> gkeys(g_out(p0, p1), joined(db)).contains(#[trigger] ks[i])
        &&& forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j ==>
            orow(db, p0, p1, #[trigger] ks[i]) != orow(db, p0, p1, #[trigger] ks[j])
        &&& sorted_by(order_keys(), rs)
        &&& rs.to_multiset() == rr.to_multiset()
        &&& rs.len() == rr.len()
        &&& rs.no_duplicates() && rr.no_duplicates()
        &&& forall|x: Row| #[trigger] rs.contains(x) <==> rr.contains(x)
    }),
{
    assert(cand.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < cand.len() && 0 <= b < cand.len() && a != b implies cand[a] != cand[b] by {
            if a < b { assert(cand[a] < cand[b]); } else { assert(cand[b] < cand[a]); }
        }
    }
    lemma_unpicked(cand, pick);
    let rest = unpicked(cand, pick);
    assert forall|t: int| 0 <= t < rest.len() implies 0 <= #[trigger] rest[t] < ks.len() by {
        assert(rest.contains(rest[t]));
        let a = choose|a: int| 0 <= a < cand.len() && cand[a] == rest[t];
    }
    assert forall|u: int| 0 <= u < pick.len() implies 0 <= #[trigger] pick[u] < ks.len() by {
        let a = choose|a: int| 0 <= a < cand.len() && cand[a] == pick[u];
    }
    assert forall|i: int| 0 <= i < ks.len() implies gkeys(g_out(p0, p1), joined(db)).contains(#[trigger] ks[i]) by {
        assert(ks.contains(ks[i]));
    }
    assert forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j implies
        orow(db, p0, p1, #[trigger] ks[i]) != orow(db, p0, p1, #[trigger] ks[j]) by {
        assert(ks.contains(ks[i]) && ks.contains(ks[j]));
        lemma_orow(db, p0, p1, ks[i]);
        lemma_orow(db, p0, p1, ks[j]);
        if orow(db, p0, p1, ks[i]) == orow(db, p0, p1, ks[j]) {
            assert(ks[i] == ks[j]);
        }
    }
    let rr = rows_at(db, p0, p1, ks, rest);
    lemma_rows_nodup(db, p0, p1, ks, rest);
    let fam = val_family(Val::Num { coeff: 0, scale: 4 });
    let fams = seq![fam];
    assert(all_keys_ok(order_keys(), fams, rr)) by {
        assert forall|t: int| 0 <= t < rr.len() implies keys_ok(order_keys(), fams, #[trigger] rr[t]) by {
            assert(ks.contains(ks[rest[t]]));
            lemma_orow(db, p0, p1, ks[rest[t]]);
            assert(key_ok(order_keys()[0], fams[0], rr[t]));
        }
    }
    lemma_sort_rows(order_keys(), fams, rr);
    let rs = sort_rows(order_keys(), rr);
    rs.to_multiset_ensures();
    rr.to_multiset_ensures();
    rr.lemma_multiset_has_no_duplicates();
    rs.lemma_multiset_has_no_duplicates_conv();
    assert forall|x: Row| #[trigger] rs.contains(x) <==> rr.contains(x) by {
        assert(rs.to_multiset().count(x) == rr.to_multiset().count(x));
    }
}

/// The candidates' rows are the body's rows.
proof fn lemma_cand_body(db: Database, ps: Seq<Literal>, p0: Seq<u8>, p1: int, ac: int, asc: nat, ks: Seq<Row>,
    cand: Seq<int>, pick: Seq<int>)
    requires tables_shaped(db), picked_ok(db, p0, p1, ac, asc, ks, cand, pick),
    ensures ({
        let cr = rows_at(db, p0, p1, ks, cand);
        let body = keep(gb_rows(db, p0, p1), above_fn(ac, asc));
        &&& cr.no_duplicates()
        &&& cr.to_multiset() == body.to_multiset()
    }),
{
    lemma_basic(db, p0, p1, ac, asc, ks, cand, pick);
    let gk = gkeys(g_out(p0, p1), joined(db));
    lemma_gkeys(g_out(p0, p1), joined(db));
    let h = above_fn(ac, asc);
    let body = keep(gb_rows(db, p0, p1), h);
    let cr = rows_at(db, p0, p1, ks, cand);
    lemma_rows_nodup(db, p0, p1, ks, cand);
    lemma_body_nodup(db, p0, p1, ac, asc);
    assert forall|x: Row| #[trigger] cr.contains(x) <==> body.contains(x) by {
        lemma_keep_has(gb_rows(db, p0, p1), h, x);
        if cr.contains(x) {
            let t = choose|t: int| 0 <= t < cr.len() && cr[t] == x;
            let k = ks[cand[t]];
            assert(gk.contains(k));
            let gt = choose|gt: int| 0 <= gt < gk.len() && gk[gt] == k;
            assert(gb_rows(db, p0, p1)[gt] == x);
            lemma_orow(db, p0, p1, k);
            assert(coeff(x[2]) == osum(db, p0, p1, k));
            assert(cand.contains(cand[t]));
        }
        if body.contains(x) {
            let gt = choose|gt: int| 0 <= gt < gb_rows(db, p0, p1).len() && gb_rows(db, p0, p1)[gt] == x;
            let k = gk[gt];
            assert(gk.contains(k));
            assert(ks.contains(k));
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
            lemma_orow(db, p0, p1, k);
            assert(coeff(x[2]) == osum(db, p0, p1, k));
            assert(cand.contains(i));
            let t = choose|t: int| 0 <= t < cand.len() && cand[t] == i;
            assert(cr[t] == x);
        }
    }
    lemma_nodup_same_multiset(cr, body);
}

/// The permutation holds the candidates' rows once each.
proof fn lemma_perm_rows(db: Database, p0: Seq<u8>, p1: int, ac: int, asc: nat, ks: Seq<Row>, cand: Seq<int>,
    pick: Seq<int>)
    requires tables_shaped(db), picked_ok(db, p0, p1, ac, asc, ks, cand, pick),
    ensures ({
        let p = perm(db, p0, p1, ks, cand, pick);
        let cr = rows_at(db, p0, p1, ks, cand);
        &&& p.no_duplicates()
        &&& forall|x: Row| #[trigger] p.contains(x) <==> cr.contains(x)
    }),
{
    lemma_basic(db, p0, p1, ac, asc, ks, cand, pick);
    let rest = unpicked(cand, pick);
    let o = rows_at(db, p0, p1, ks, pick);
    let rr = rows_at(db, p0, p1, ks, rest);
    let rs = rest_sorted(db, p0, p1, ks, cand, pick);
    let cr = rows_at(db, p0, p1, ks, cand);
    let p = perm(db, p0, p1, ks, cand, pick);
    lemma_rows_nodup(db, p0, p1, ks, pick);
    assert forall|a: int, b: int| 0 <= a < p.len() && 0 <= b < p.len() && a != b implies p[a] != p[b] by {
        if a < o.len() && b < o.len() {
            assert(p[a] == o[a] && p[b] == o[b]);
        } else if a >= o.len() && b >= o.len() {
            assert(p[a] == rs[a - o.len()] && p[b] == rs[b - o.len()]);
        } else {
            let (ia, ib) = if a < o.len() { (a, b) } else { (b, a) };
            assert(p[ia] == o[ia]);
            assert(p[ib] == rs[ib - o.len()]);
            assert(rs.contains(rs[ib - o.len()]));
            assert(rr.contains(p[ib]));
            let tr = choose|tr: int| 0 <= tr < rr.len() && rr[tr] == p[ib];
            assert(rest.contains(rest[tr]));
            if p[ia] == p[ib] {
                assert(orow(db, p0, p1, ks[pick[ia]]) == orow(db, p0, p1, ks[rest[tr]]));
                assert(pick[ia] == rest[tr]);
                assert(pick.contains(pick[ia]));
            }
        }
    }
    assert forall|x: Row| #[trigger] p.contains(x) <==> cr.contains(x) by {
        if p.contains(x) {
            let a = choose|a: int| 0 <= a < p.len() && p[a] == x;
            if a < o.len() {
                assert(o[a] == x);
                assert(cand.contains(pick[a]));
                let t = choose|t: int| 0 <= t < cand.len() && cand[t] == pick[a];
                assert(cr[t] == x);
            } else {
                assert(rs[a - o.len()] == x);
                assert(rs.contains(x));
                assert(rr.contains(x));
                let tr = choose|tr: int| 0 <= tr < rr.len() && rr[tr] == x;
                assert(rest.contains(rest[tr]));
                let t = choose|t: int| 0 <= t < cand.len() && cand[t] == rest[tr];
                assert(cr[t] == x);
            }
        }
        if cr.contains(x) {
            let t = choose|t: int| 0 <= t < cr.len() && cr[t] == x;
            if pick.contains(cand[t]) {
                let u = choose|u: int| 0 <= u < pick.len() && pick[u] == cand[t];
                assert(p[u] == o[u]);
            } else {
                assert(rest.contains(cand[t]));
                let tr = choose|tr: int| 0 <= tr < rest.len() && rest[tr] == cand[t];
                assert(rr[tr] == x);
                assert(rr.contains(x));
                assert(rs.contains(x));
                let a = choose|a: int| 0 <= a < rs.len() && rs[a] == x;
                assert(p[o.len() + a] == x);
            }
        }
    }
}

/// The permutation is sorted.
proof fn lemma_perm_sorted(db: Database, p0: Seq<u8>, p1: int, ac: int, asc: nat, ks: Seq<Row>, cand: Seq<int>,
    pick: Seq<int>)
    requires tables_shaped(db), picked_ok(db, p0, p1, ac, asc, ks, cand, pick),
    ensures sorted_by(order_keys(), perm(db, p0, p1, ks, cand, pick)),
{
    lemma_basic(db, p0, p1, ac, asc, ks, cand, pick);
    let rest = unpicked(cand, pick);
    let o = rows_at(db, p0, p1, ks, pick);
    let rr = rows_at(db, p0, p1, ks, rest);
    let rs = rest_sorted(db, p0, p1, ks, cand, pick);
    let p = perm(db, p0, p1, ks, cand, pick);
    assert forall|a: int, b: int| 0 <= a < b < p.len() implies keys_cmp(order_keys(), #[trigger] p[a], #[trigger] p[b]) <= 0 by {
        if b < o.len() {
            assert(p[a] == o[a] && p[b] == o[b]);
            lemma_cmp_rows(db, p0, p1, ks[pick[a]], ks[pick[b]]);
        } else if a >= o.len() {
            assert(p[a] == rs[a - o.len()] && p[b] == rs[b - o.len()]);
        } else {
            assert(p[a] == o[a]);
            assert(p[b] == rs[b - o.len()]);
            assert(rs.contains(rs[b - o.len()]));
            assert(rr.contains(p[b]));
            let tr = choose|tr: int| 0 <= tr < rr.len() && rr[tr] == p[b];
            assert(rest.contains(rest[tr]));
            let t = choose|t: int| 0 <= t < cand.len() && cand[t] == rest[tr];
            assert(!pick.contains(cand[t]));
            lemma_cmp_rows(db, p0, p1, ks[pick[a]], ks[cand[t]]);
        }
    }
}

/// The answer's rows are an allowed outcome of the statement.
pub proof fn lemma_answer_ok(db: Database, ps: Seq<Literal>, p0: Seq<u8>, p1: int, ac: int, asc: nat,
    ks: Seq<Row>, cand: Seq<int>, pick: Seq<int>)
    requires
        binding(ps, p0, p1), tables_shaped(db), vals_ok(db),
        avg_in(db, p0, p1) == Ok::<Val, SqlError>(Val::Num { coeff: ac, scale: asc }),
        picked_ok(db, p0, p1, ac, asc, ks, cand, pick),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(rows_at(db, p0, p1, ks, pick))),
{
    let oq = query_spec_at(ps);
    lemma_query_parts(ps);
    lemma_body_rows(db, ps, p0, p1, ac, asc);
    let body = keep(gb_rows(db, p0, p1), above_fn(ac, asc));
    let cr = rows_at(db, p0, p1, ks, cand);
    let p = perm(db, p0, p1, ks, cand, pick);
    let o = rows_at(db, p0, p1, ks, pick);
    lemma_cand_body(db, ps, p0, p1, ac, asc, ks, cand, pick);
    lemma_perm_rows(db, p0, p1, ac, asc, ks, cand, pick);
    lemma_perm_sorted(db, p0, p1, ac, asc, ks, cand, pick);
    lemma_nodup_same_multiset(p, cr);
    p.to_multiset_ensures();
    cr.to_multiset_ensures();
    body.to_multiset_ensures();
    assert(p.len() == cr.len());
    assert(cr.len() == cand.len());
    assert(slice_rows(p, 0, Some(100nat)) =~= o);
    crate::link::outcome::lemma_outcome_sorted(db, oq, body, p);
}

/// The rows of distinct indices are distinct.
proof fn lemma_rows_nodup(db: Database, p0: Seq<u8>, p1: int, ks: Seq<Row>, idx: Seq<int>)
    requires
        idx.no_duplicates(),
        forall|t: int| 0 <= t < idx.len() ==> 0 <= #[trigger] idx[t] < ks.len(),
        forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j ==>
            orow(db, p0, p1, #[trigger] ks[i]) != orow(db, p0, p1, #[trigger] ks[j]),
    ensures rows_at(db, p0, p1, ks, idx).no_duplicates(),
{
    let r = rows_at(db, p0, p1, ks, idx);
    assert forall|a: int, b: int| 0 <= a < r.len() && 0 <= b < r.len() && a != b implies r[a] != r[b] by {
        assert(idx[a] != idx[b]);
    }
}

/// The body's rows have no duplicates.
proof fn lemma_body_nodup(db: Database, p0: Seq<u8>, p1: int, ac: int, asc: nat)
    requires tables_shaped(db),
    ensures keep(gb_rows(db, p0, p1), above_fn(ac, asc)).no_duplicates(),
{
    let gk = gkeys(g_out(p0, p1), joined(db));
    lemma_gkeys(g_out(p0, p1), joined(db));
    let rows = gb_rows(db, p0, p1);
    assert(rows.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < rows.len() && 0 <= b < rows.len() && a != b implies rows[a] != rows[b] by {
            assert(gk.contains(gk[a]) && gk.contains(gk[b]));
            lemma_orow(db, p0, p1, gk[a]);
            lemma_orow(db, p0, p1, gk[b]);
            if rows[a] == rows[b] {
                assert(gk[a] == gk[b]);
            }
        }
    }
    lemma_keep_nodup(rows, above_fn(ac, asc));
}

/// `keep` of a duplicate-free sequence has no duplicates.
proof fn lemma_keep_nodup(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    requires rows.no_duplicates(),
    ensures keep(rows, f).no_duplicates(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert(ri.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < ri.len() && 0 <= b < ri.len() && a != b implies ri[a] != ri[b] by {
                assert(ri[a] == rows[a] && ri[b] == rows[b]);
            }
        }
        lemma_keep_nodup(ri, f);
        lemma_keep_members(ri, f);
        let k = keep(rows, f);
        let ki = keep(ri, f);
        if f(rows.last()) {
            assert forall|a: int, b: int| 0 <= a < k.len() && 0 <= b < k.len() && a != b implies k[a] != k[b] by {
                if a < ki.len() && b < ki.len() {
                    assert(k[a] == ki[a] && k[b] == ki[b]);
                } else {
                    let i = if a < ki.len() { a } else { b };
                    assert(k[i] == ki[i]);
                    assert(ri.contains(ki[i]));
                    let m = choose|m: int| 0 <= m < ri.len() && ri[m] == ki[i];
                    assert(rows[m] == ki[i]);
                    assert(rows[rows.len() - 1] == rows.last());
                }
            }
        }
    }
}

/// A row is in `keep(rows, f)` exactly when it is a row of `rows` satisfying `f`.
proof fn lemma_keep_has(rows: Seq<Row>, f: spec_fn(Row) -> bool, x: Row)
    ensures keep(rows, f).contains(x) <==> (rows.contains(x) && f(x)),
    decreases rows.len(),
{
    lemma_keep_members(rows, f);
    if rows.len() > 0 {
        let ri = rows.drop_last();
        lemma_keep_has(ri, f, x);
        let k = keep(rows, f);
        let ki = keep(ri, f);
        if rows.contains(x) && f(x) {
            let m = choose|m: int| 0 <= m < rows.len() && rows[m] == x;
            if m < rows.len() - 1 {
                assert(ri[m] == x);
                let a = choose|a: int| 0 <= a < ki.len() && ki[a] == x;
                if f(rows.last()) {
                    assert(k[a] == x);
                }
            } else {
                assert(k[ki.len() as int] == x);
            }
        }
        if k.contains(x) {
            let a = choose|a: int| 0 <= a < k.len() && k[a] == x;
            assert(rows.contains(k[a]) && f(k[a]));
        }
    }
}

} // verus!
