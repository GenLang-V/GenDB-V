//! The lookup chain of one lineitem row (order, customer, qualifying nation, supplier) and its multiplicity:
//! with the found rows, `line_mult` of every group key is 1 for the group of the customer's nation and 0 otherwise
//! (`lemma_line_hit`); a missing or failing link makes it 0 for every key (`key_dead`, `lemma_line_miss_*`).
//! `qlist_ok` describes the qualifying-nation list the calling thread builds: every nation row whose region is named
//! `$1`, with its key and its group (distinct names).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::query::*;
use crate::agent::q5spec::*;
use crate::agent::lookup::*;

verus! {

/// No lineitem row with order key `kv` takes part in any group.
pub open spec fn key_dead(rs: Rels, prm: Prm, kv: Val) -> bool {
    forall|k: Row, l: Row| l[0] == kv ==> #[trigger] line_mult(rs, prm, k, l) == 0
}

/// The qualifying-nation list: entry `q` is nation row `qrow[q]` with key `qkey[q]`, joined by exactly one region
/// row named `$1`, in group `qgrp[q]` (named `gnames[qgrp[q]]`); every nation row joined by such a region row is
/// listed; group names are distinct.
pub open spec fn qlist_ok(rs: Rels, prm: Prm, qkey: Seq<i64>, qgrp: Seq<usize>, qrow: Seq<int>, gnames: Seq<Seq<u8>>) -> bool {
    &&& qkey.len() == qgrp.len()
    &&& qrow.len() == qkey.len()
    &&& forall|q: int| 0 <= q < qkey.len() ==> qentry_ok(rs, prm, qkey, qgrp, qrow, gnames, q)
    &&& forall|i: int| 0 <= i < rs.n.len() && r_cnt(rs.r, #[trigger] rs.n[i], prm.name) != 0 ==>
            exists|q: int| 0 <= q < qkey.len() && qrow[q] == i
    &&& forall|a: int, b: int| 0 <= a < gnames.len() && 0 <= b < gnames.len() && a != b ==> #[trigger] gnames[a] != #[trigger] gnames[b]
}

/// One entry of the qualifying-nation list.
pub open spec fn qentry_ok(rs: Rels, prm: Prm, qkey: Seq<i64>, qgrp: Seq<usize>, qrow: Seq<int>, gnames: Seq<Seq<u8>>, q: int) -> bool {
    &&& 0 <= qrow[q] < rs.n.len()
    &&& rs.n[qrow[q]][0] == Val::Int(qkey[q] as int)
    &&& r_cnt(rs.r, rs.n[qrow[q]], prm.name) == 1
    &&& qgrp[q] < gnames.len()
    &&& rs.n[qrow[q]][1] == Val::Text(gnames[qgrp[q] as int])
}

/// The group key of group `gi`.
pub open spec fn gkey(gnames: Seq<Seq<u8>>, gi: int) -> Row {
    name_key(gnames[gi])
}

/// Distinct group names give distinct group keys.
pub proof fn lemma_gkey_eq(gnames: Seq<Seq<u8>>, a: int, b: int)
    requires
        0 <= a < gnames.len(), 0 <= b < gnames.len(),
        forall|x: int, y: int| 0 <= x < gnames.len() && 0 <= y < gnames.len() && x != y ==> #[trigger] gnames[x] != #[trigger] gnames[y],
    ensures (gkey(gnames, a) == gkey(gnames, b)) == (a == b),
{
    if gkey(gnames, a) == gkey(gnames, b) {
        assert(gkey(gnames, a)[0] == gkey(gnames, b)[0]);
    }
}

/// The order of the key exists but lies outside the date window: dead key.
pub proof fn lemma_dead_window(rs: Rels, prm: Prm, oi: int)
    requires keys_unique(rs.o), 0 <= oi < rs.o.len(), !date_ok(rs.o[oi], prm),
    ensures key_dead(rs, prm, rs.o[oi][0]),
{
    assert forall|k: Row, l: Row| l[0] == rs.o[oi][0] implies #[trigger] line_mult(rs, prm, k, l) == 0 by {
        lemma_mult_out_of_window(rs, prm, k, l, oi);
    }
}

/// No order holds the key: dead key.
pub proof fn lemma_dead_no_order(rs: Rels, prm: Prm, kv: Val)
    requires forall|i: int| 0 <= i < rs.o.len() ==> #[trigger] rs.o[i][0] != kv,
    ensures key_dead(rs, prm, kv),
{
    assert forall|k: Row, l: Row| l[0] == kv implies #[trigger] line_mult(rs, prm, k, l) == 0 by {
        lemma_mult_no_order(rs, prm, k, l);
    }
}

/// The order is in the window but no customer holds its customer key: dead key.
pub proof fn lemma_dead_no_customer(rs: Rels, prm: Prm, oi: int)
    requires
        keys_unique(rs.o), 0 <= oi < rs.o.len(), date_ok(rs.o[oi], prm),
        forall|i: int| 0 <= i < rs.c.len() ==> #[trigger] rs.c[i][0] != rs.o[oi][1],
    ensures key_dead(rs, prm, rs.o[oi][0]),
{
    assert forall|k: Row, l: Row| l[0] == rs.o[oi][0] implies #[trigger] line_mult(rs, prm, k, l) == 0 by {
        lemma_mult_order(rs, prm, k, l, oi);
        lemma_c_cnt_none(rs, rs.o[oi], l, k, prm.name);
    }
}

/// The customer's nation key is not in the qualifying list: dead key.
pub proof fn lemma_dead_nation(rs: Rels, prm: Prm, qkey: Seq<i64>, qgrp: Seq<usize>, qrow: Seq<int>, gnames: Seq<Seq<u8>>,
    oi: int, ci: int, cnk: i64)
    requires
        keys_unique(rs.o), keys_unique(rs.c),
        qlist_ok(rs, prm, qkey, qgrp, qrow, gnames),
        0 <= oi < rs.o.len(), date_ok(rs.o[oi], prm),
        0 <= ci < rs.c.len(), rs.c[ci][0] == rs.o[oi][1], rs.c[ci][3] == Val::Int(cnk as int),
        forall|q: int| 0 <= q < qkey.len() ==> #[trigger] qkey[q] != cnk,
    ensures key_dead(rs, prm, rs.o[oi][0]),
{
    assert forall|i: int| 0 <= i < rs.n.len() && #[trigger] rs.n[i][0] == rs.c[ci][3] implies r_cnt(rs.r, rs.n[i], prm.name) == 0 by {
        if r_cnt(rs.r, rs.n[i], prm.name) != 0 {
            let q = choose|q: int| 0 <= q < qkey.len() && qrow[q] == i;
            assert(qentry_ok(rs, prm, qkey, qgrp, qrow, gnames, q));
            assert(qkey[q] == cnk);
        }
    }
    assert forall|k: Row, l: Row| l[0] == rs.o[oi][0] implies #[trigger] line_mult(rs, prm, k, l) == 0 by {
        lemma_mult_order(rs, prm, k, l, oi);
        lemma_c_cnt_found(rs, rs.o[oi], l, k, prm.name, ci);
        lemma_s_cnt_zero_nation(rs, rs.c[ci], l, k, prm.name);
    }
}

/// The live chain of an order (window, customer, qualifying nation entry `qq`).
pub open spec fn order_live(rs: Rels, prm: Prm, qkey: Seq<i64>, qgrp: Seq<usize>, kv: Val, oi: int, ci: int, qq: int, cnk: i64) -> bool {
    &&& 0 <= oi < rs.o.len() && rs.o[oi][0] == kv && date_ok(rs.o[oi], prm)
    &&& 0 <= ci < rs.c.len() && rs.c[ci][0] == rs.o[oi][1] && rs.c[ci][3] == Val::Int(cnk as int)
    &&& 0 <= qq < qkey.len() && qkey[qq] == cnk
}

/// A lineitem row of a live order whose supplier is missing or in another nation takes part in no group.
pub proof fn lemma_line_miss(rs: Rels, prm: Prm, qkey: Seq<i64>, qgrp: Seq<usize>, qrow: Seq<int>, gnames: Seq<Seq<u8>>,
    l: Row, oi: int, ci: int, qq: int, cnk: i64, k: Row)
    requires
        keys_unique(rs.o), keys_unique(rs.c), keys_unique(rs.s),
        order_live(rs, prm, qkey, qgrp, l[0], oi, ci, qq, cnk),
        (forall|i: int| 0 <= i < rs.s.len() ==> #[trigger] rs.s[i][0] != l[2])
            || exists|si: int| 0 <= si < rs.s.len() && rs.s[si][0] == l[2] && rs.s[si][3] != Val::Int(cnk as int),
    ensures line_mult(rs, prm, k, l) == 0,
{
    lemma_mult_order(rs, prm, k, l, oi);
    lemma_c_cnt_found(rs, rs.o[oi], l, k, prm.name, ci);
    if forall|i: int| 0 <= i < rs.s.len() ==> #[trigger] rs.s[i][0] != l[2] {
        lemma_s_cnt_none(rs, rs.c[ci], l, k, prm.name);
    } else {
        let si = choose|si: int| 0 <= si < rs.s.len() && rs.s[si][0] == l[2] && rs.s[si][3] != Val::Int(cnk as int);
        lemma_s_cnt_found(rs, rs.c[ci], l, k, prm.name, si);
    }
}

/// A lineitem row of a live order whose supplier is in the customer's nation: multiplicity 1 in the group of that
/// nation, 0 in every other group.
pub proof fn lemma_line_hit(rs: Rels, prm: Prm, qkey: Seq<i64>, qgrp: Seq<usize>, qrow: Seq<int>, gnames: Seq<Seq<u8>>,
    l: Row, oi: int, ci: int, qq: int, cnk: i64, si: int, k: Row)
    requires
        keys_unique(rs.o), keys_unique(rs.c), keys_unique(rs.s), keys_unique(rs.n),
        qlist_ok(rs, prm, qkey, qgrp, qrow, gnames),
        order_live(rs, prm, qkey, qgrp, l[0], oi, ci, qq, cnk),
        0 <= si < rs.s.len(), rs.s[si][0] == l[2], rs.s[si][3] == Val::Int(cnk as int),
    ensures line_mult(rs, prm, k, l) == if k == gkey(gnames, qgrp[qq] as int) { 1int } else { 0int },
{
    assert(qentry_ok(rs, prm, qkey, qgrp, qrow, gnames, qq));
    let ni = qrow[qq];
    lemma_mult_order(rs, prm, k, l, oi);
    lemma_c_cnt_found(rs, rs.o[oi], l, k, prm.name, ci);
    lemma_s_cnt_found(rs, rs.c[ci], l, k, prm.name, si);
    lemma_n_cnt_found(rs, rs.s[si], k, prm.name, ni);
    assert(seq![rs.n[ni][1]] == gkey(gnames, qgrp[qq] as int));
}

} // verus!
