//! From the scan totals to the normal form: the accumulators of group `k` over the product of the stored
//! relations are the sums of `contrib` over lineitem rows (`lemma_acc_nf`), in any row order (`lemma_acc_rows`);
//! a group with a qualifying row is the group of a qualifying nation (`lemma_group_witness`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::query::*;
use crate::link::join::*;
use crate::agent::q5spec::*;
use crate::agent::algebra::*;
use crate::agent::chain::*;
use crate::agent::common::sums::*;

verus! {

/// Widths of the stored relations in FROM order.
pub open spec fn sws() -> Seq<nat> {
    seq![8nat, 7, 15, 7, 4, 3]
}

pub proof fn lemma_sws_offsets()
    ensures offsets(sws()) == seq![0nat, 8, 15, 30, 37, 41, 44],
{
    assert(offsets(sws()) == seq![0nat, 8, 15, 30, 37, 41, 44]) by (compute);
}

/// Every row of the product of the stored relations has 44 columns, one row of each relation at its offset.
pub proof fn lemma_xs_rows(rs: Rels)
    requires rels_widths(rs),
    ensures
        forall|m: int| 0 <= m < xs_of(rs).len() ==> parts_ok(#[trigger] xs_of(rs)[m], sws(),
            |i: int, x: Row| pts_of(rs)[i].contains(x)),
{
    let ws = sws();
    let ok = |i: int, x: Row| pts_of(rs)[i].contains(x);
    let pts = pts_of(rs);
    assert(inputs_ok(pts, inputs6(), ws, ok)) by {
        assert forall|i: int, k: int| 0 <= i < inputs6().len() && 0 <= k < pts[inputs6()[i] as int].len() implies
            (#[trigger] pts[inputs6()[i] as int][k]).len() == ws[i] && ok(i, pts[inputs6()[i] as int][k]) by {
            assert(inputs6()[i] == i);
            assert(pts[i].contains(pts[i][k]));
            if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else {}
        }
    }
    lemma_joined_parts(pts, inputs6(), ws, ok);
    crate::agent::sqlrow::lemma_joined6(pts, inputs6());
}

/// One accumulator with lineitem weight `wsel(m, .)`.
proof fn lemma_acc_one(rs: Rels, prm: Prm, k: Row, m: int)
    requires rels_widths(rs),
    ensures sum_of(xs_of(rs), |y: Row| t_of(prm, k, |l: Row| wsel(m, l), y)) == sum_of(rs.l, contrib_fn(rs, prm, k, m)),
{
    let w = |l: Row| wsel(m, l);
    lemma_group_sum(rs, prm, k, w);
    assert forall|i: int| 0 <= i < rs.l.len() implies
        (|l: Row| line_mult(rs, prm, k, l) * w(l))(#[trigger] rs.l[i]) == contrib_fn(rs, prm, k, m)(rs.l[i]) by {}
    lemma_sum_of_ext(rs.l, |l: Row| line_mult(rs, prm, k, l) * w(l), contrib_fn(rs, prm, k, m));
}

/// The three accumulators of group `k` over the product are sums over lineitem rows.
pub proof fn lemma_acc_nf(rs: Rels, prm: Prm, k: Row)
    requires rels_widths(rs),
    ensures
        gcount(q5_g(prm), xs_of(rs), k) == sum_of(rs.l, contrib_fn(rs, prm, k, 0)),
        gsum(q5_g(prm), xs_of(rs), k, 0) == sum_of(rs.l, contrib_fn(rs, prm, k, 1)),
        gabs(q5_g(prm), xs_of(rs), k, 0) == sum_of(rs.l, contrib_fn(rs, prm, k, 2)),
{
    let g = q5_g(prm);
    let xs = xs_of(rs);
    lemma_acc_sum_of(g, xs, k, 0);
    lemma_xs_rows(rs);
    let ws = sws();
    lemma_sws_offsets();
    lemma_acc_one(rs, prm, k, 0);
    lemma_acc_one(rs, prm, k, 1);
    lemma_acc_one(rs, prm, k, 2);
    let w0 = |l: Row| wsel(0, l);
    let w1 = |l: Row| wsel(1, l);
    let w2 = |l: Row| wsel(2, l);
    assert forall|i: int| 0 <= i < xs.len() implies (count_term(g, k))(#[trigger] xs[i]) == (|y: Row| t_of(prm, k, w0, y))(xs[i]) by {}
    lemma_sum_of_ext(xs, count_term(g, k), |y: Row| t_of(prm, k, w0, y));
    assert forall|i: int| 0 <= i < xs.len() implies (sum_term(g, k, 0))(#[trigger] xs[i]) == (|y: Row| t_of(prm, k, w1, y))(xs[i]) by {
        let y = xs[i];
        assert(parts_ok(y, ws, |i: int, x: Row| pts_of(rs)[i].contains(x)));
        assert(y.len() == 44);
        assert(line_of(y)[5] == y[20] && line_of(y)[6] == y[21]);
    }
    lemma_sum_of_ext(xs, sum_term(g, k, 0), |y: Row| t_of(prm, k, w1, y));
    assert forall|i: int| 0 <= i < xs.len() implies (abs_term(g, k, 0))(#[trigger] xs[i]) == (|y: Row| t_of(prm, k, w2, y))(xs[i]) by {
        let y = xs[i];
        assert(parts_ok(y, ws, |i: int, x: Row| pts_of(rs)[i].contains(x)));
        assert(y.len() == 44);
        assert(line_of(y)[5] == y[20] && line_of(y)[6] == y[21]);
    }
    lemma_sum_of_ext(xs, abs_term(g, k, 0), |y: Row| t_of(prm, k, w2, y));
}

/// Sums over lineitem rows do not depend on their order.
pub proof fn lemma_acc_rows(rs: Rels, rows: Seq<Row>, prm: Prm, k: Row, m: int)
    requires rows.to_multiset() == rs.l.to_multiset(),
    ensures sum_of(rows.subrange(0, rows.len() as int), contrib_fn(rs, prm, k, m)) == sum_of(rs.l, contrib_fn(rs, prm, k, m)),
{
    lemma_sum_range_all(rows, contrib_fn(rs, prm, k, m));
    lemma_sum_of_perm(rows, rs.l, contrib_fn(rs, prm, k, m));
}

/// A group with a qualifying row of the product is the group of a qualifying nation.
pub proof fn lemma_group_witness(rs: Rels, prm: Prm, qkey: Seq<i64>, qgrp: Seq<usize>, qrow: Seq<int>,
    gnames: Seq<Seq<u8>>, k: Row)
    requires
        rels_widths(rs),
        qlist_ok(rs, prm, qkey, qgrp, qrow, gnames),
        gcount(q5_g(prm), xs_of(rs), k) > 0,
    ensures exists|gi: int| 0 <= gi < gnames.len() && k == #[trigger] gkey(gnames, gi),
{
    let g = q5_g(prm);
    let xs = xs_of(rs);
    lemma_count_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    let y = xs[m];
    lemma_xs_rows(rs);
    let ws = sws();
    let ok = |i: int, x: Row| pts_of(rs)[i].contains(x);
    lemma_sws_offsets();
    assert(parts_ok(y, ws, ok));
    lemma_parts_at(y, ws, ok, 4);
    lemma_parts_at(y, ws, ok, 5);
    let n = y.subrange(37, 41);
    let r = y.subrange(41, 44);
    assert(rs.n.contains(n));
    assert(rs.r.contains(r));
    let ni = choose|i: int| 0 <= i < rs.n.len() && rs.n[i] == n;
    let ri = choose|i: int| 0 <= i < rs.r.len() && rs.r[i] == r;
    // the region row joins the nation row with r_name = $1
    assert(n[2] == y[39] && r[0] == y[41] && r[1] == y[42] && n[1] == y[38]);
    let f = |x: Row| r_term(n, prm.name, x);
    assert(f(rs.r[ri]) == 1);
    lemma_sum_of_remove(rs.r, ri, f);
    let rest = rs.r.remove(ri);
    assert forall|i: int| 0 <= i < rest.len() implies f(#[trigger] rest[i]) >= 0 by {}
    lemma_sum_range_nonneg(rest, f, 0, rest.len() as int);
    lemma_sum_range_all(rest, f);
    assert(r_cnt(rs.r, rs.n[ni], prm.name) >= 1);
    let q = choose|q: int| 0 <= q < qkey.len() && qrow[q] == ni;
    assert(qentry_ok(rs, prm, qkey, qgrp, qrow, gnames, q));
    let gi = qgrp[q] as int;
    assert(k == q5_key(y));
    assert(k =~= gkey(gnames, gi));
}

} // verus!
