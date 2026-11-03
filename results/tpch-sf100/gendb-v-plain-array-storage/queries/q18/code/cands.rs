//! The output candidates: for every order key whose quantity sum exceeds `$1` (the scan's hits), its orders row
//! and that order's customer row (`lookup`), with the sum and the ORDER BY values. The candidates are exactly the
//! qualifying orders (`ord_ok`), once each (`cands_ok`).
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::common::keysum::*;
use crate::agent::common::runscan::*;
use crate::agent::lookup::*;
use crate::agent::subquery::*;
use crate::agent::groups::*;
use crate::agent::topk::Cand;

verus! {

/// One candidate: a qualifying order, a customer row of its customer key, its sum and ORDER BY values.
pub open spec fn cand_ok(c: Cand, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& (c.o as int) < n_o(sv) && (c.c as int) < n_c(sv)
    &&& ck(sv)[c.c as int] == oc(sv)[c.o as int]
    &&& c.sum as int == order_sum(sv, c.o as int)
    &&& c.price == otp(sv)[c.o as int] && c.date == od(sv)[c.o as int]
    &&& ord_ok(sv, ps, c.o as int)
}

/// The candidates are the qualifying orders, once each.
pub open spec fn cands_ok(cs: Seq<Cand>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& forall|t: int| 0 <= t < cs.len() ==> cand_ok(#[trigger] cs[t], sv, ps)
    &&& forall|a: int, b: int| 0 <= a < cs.len() && 0 <= b < cs.len() && a != b ==> cs[a].o != cs[b].o
    &&& forall|j: int| 0 <= j < n_o(sv) && #[trigger] ord_ok(sv, ps, j) ==> exists|t: int| 0 <= t < cs.len() && cs[t].o == j
}

/// The columns the candidates read are the stored ones.
pub open spec fn cand_cols_ok(okey: &'static [i64], ocust: &'static [i64], oprice: &'static [i128], odate: &'static [i32],
    no: usize, ckey: &'static [i64], nc: usize, sv: StoresView) -> bool
{
    &&& okey@ == ok(sv) && ocust@ == oc(sv) && oprice@ == otp(sv) && odate@ == od(sv) && ckey@ == ck(sv)
    &&& no as int == n_o(sv) && nc as int == n_c(sv)
    &&& cols_facts(sv)
}

/// The candidates of the hits.
pub fn build_cands(hits: &Vec<Hit>, okey: &'static [i64], ocust: &'static [i64], oprice: &'static [i128],
    odate: &'static [i32], no: usize, ckey: &'static [i64], nc: usize, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (cs: Vec<Cand>)
    requires
        cand_cols_ok(okey, ocust, oprice, odate, no, ckey, nc, sv),
        hits_all(lk(sv), lq(sv), thr_of(ps), 0, n_l(sv), hits@),
    ensures cands_ok(cs@, sv, ps),
{
    let mut cs: Vec<Cand> = Vec::new();
    let ghost mut srcs: Seq<int> = Seq::empty();
    let nh = hits.len();
    let mut t: usize = 0;
    while t < nh
        invariant
            nh == hits@.len(), t <= nh,
            cand_cols_ok(okey, ocust, oprice, odate, no, ckey, nc, sv),
            hits_all(lk(sv), lq(sv), thr_of(ps), 0, n_l(sv), hits@),
            srcs.len() == cs@.len(),
            forall|e: int| 0 <= e < cs@.len() ==> cand_ok(#[trigger] cs@[e], sv, ps),
            forall|e: int| 0 <= e < cs@.len() ==> 0 <= #[trigger] srcs[e] < t && hits@[srcs[e]].key == ok(sv)[cs@[e].o as int],
            forall|a: int, b: int| 0 <= a < cs@.len() && 0 <= b < cs@.len() && a != b ==> cs@[a].o != cs@[b].o,
            forall|j: int, u: int| #![trigger ord_ok(sv, ps, j), hits@[u]] 0 <= j < n_o(sv) && ord_ok(sv, ps, j) && 0 <= u < t && hits@[u].key == ok(sv)[j]
                ==> exists|e: int| 0 <= e < cs@.len() && cs@[e].o == j,
        decreases nh - t,
    {
        let h = hits[t];
        proof {
            assert(hits@[t as int] == h);
            assert(h.sum as int == ksum(lk(sv), lq(sv), h.key, 0, n_l(sv)) && h.sum > thr_of(ps)
                && kcount(lk(sv), h.key, 0, n_l(sv)) > 0);
            assert(in_sub(sv, ps, h.key as int));
        }
        let o = find_order(okey, no, h.key);
        let c = if o < no { find_cust(ckey, nc, ocust[o]) } else { nc };
        let ghost before = cs@;
        if o < no && c < nc {
            let cand = Cand { o, c, sum: h.sum, price: oprice[o], date: odate[o] };
            proof {
                assert(has_key(ck(sv), oc(sv)[o as int]));
                assert(ord_ok(sv, ps, o as int));
                assert(cand_ok(cand, sv, ps));
                // the order differs from every earlier candidate's: their keys are earlier hits' keys
                assert forall|e: int| 0 <= e < before.len() implies before[e].o != o by {
                    let u = srcs[e];
                    assert(hits@[u].key != hits@[t as int].key);
                }
            }
            cs.push(cand);
            proof {
                srcs = srcs.push(t as int);
                assert forall|e: int| 0 <= e < cs@.len() implies cand_ok(#[trigger] cs@[e], sv, ps) by {
                    if e < before.len() { assert(cs@[e] == before[e]); }
                }
                assert forall|e: int| 0 <= e < cs@.len() implies 0 <= #[trigger] srcs[e] < t + 1
                    && hits@[srcs[e]].key == ok(sv)[cs@[e].o as int] by {
                    if e < before.len() { assert(cs@[e] == before[e]); }
                }
                assert forall|a: int, b: int| 0 <= a < cs@.len() && 0 <= b < cs@.len() && a != b implies cs@[a].o != cs@[b].o by {
                    if a < before.len() && b < before.len() {
                        assert(cs@[a] == before[a] && cs@[b] == before[b]);
                    } else if a < before.len() {
                        assert(cs@[a] == before[a]);
                    } else {
                        assert(cs@[b] == before[b]);
                    }
                }
            }
        }
        proof {
            let cur = cs@;
            assert forall|j: int, u: int| #![trigger ord_ok(sv, ps, j), hits@[u]] 0 <= j < n_o(sv) && ord_ok(sv, ps, j) && 0 <= u < t + 1 && hits@[u].key == ok(sv)[j]
                implies exists|e: int| 0 <= e < cur.len() && cur[e].o == j by {
                if u < t {
                    // an earlier hit: its candidate is still there
                    let e = choose|e: int| 0 <= e < before.len() && before[e].o == j;
                    assert(cur[e] == before[e]);
                } else {
                    // this hit: the lookups find order j (unique key) and a customer of j's customer key
                    assert(ok(sv)[j] == h.key);
                    assert(has_key(ok(sv), h.key));
                    assert(o < no);
                    assert(ok(sv)[o as int] == ok(sv)[j]);
                    assert(o as int == j);
                    assert(has_key(ck(sv), oc(sv)[j]));
                    assert(c < nc);
                    assert(cur[cur.len() - 1].o == j);
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] ord_ok(sv, ps, j) implies exists|e: int| 0 <= e < cs@.len() && cs@[e].o == j by {
            let v = ok(sv)[j];
            assert(in_sub(sv, ps, v as int));
            assert(has_hit(hits@, v));
            let u = choose|u: int| 0 <= u < hits@.len() && #[trigger] hits@[u].key == v;
        }
    }
    cs
}

} // verus!
