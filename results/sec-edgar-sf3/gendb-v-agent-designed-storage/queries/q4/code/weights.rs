//! The weights of one group key `k` (count, value sum, absolute value sum, rows of one cik): on the kept rows they are
//! the group's member values (`lemma_q_weights`), on one contribution its fields when it has the key, else 0
//! (`lemma_c_weights`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::join::sum_of;
use crate::agent::common::sums::*;
use crate::agent::sem::ival;
use crate::agent::group::*;
use crate::agent::chain::mini;
use crate::agent::levels::*;
use crate::agent::filing::*;
use crate::agent::join::{coeff_phi, abs_phi};

verus! {

pub open spec fn wm(w: spec_fn(Row) -> int) -> spec_fn(Row) -> int { |x: Row| w(mini(x)) }

pub open spec fn w_cnt(k: Row) -> spec_fn(Row) -> int { |m: Row| if m.subrange(0, 3) == k { 1int } else { 0 } }
pub open spec fn w_sum(k: Row) -> spec_fn(Row) -> int { |m: Row| if m.subrange(0, 3) == k { coeff(m[4]) } else { 0 } }
pub open spec fn w_abs(k: Row) -> spec_fn(Row) -> int { |m: Row| if m.subrange(0, 3) == k { abs(coeff(m[4])) } else { 0 } }
pub open spec fn w_occ(k: Row, ck: int) -> spec_fn(Row) -> int {
    |m: Row| if m.subrange(0, 3) == k && m[3] == Val::Int(ck) { 1int } else { 0 }
}

/// The group members' values as weighted sums over the kept rows.
pub proof fn lemma_q_weights(q: Seq<Row>, b1: Seq<u8>, k: Row)
    requires forall|i: int| 0 <= i < q.len() ==> qrow(b1, #[trigger] q[i]),
    ensures
        mvals(q, k).len() == sum_of(q, wm(w_cnt(k))),
        isum(mvals(q, k)) == sum_of(q, wm(w_sum(k))),
        iabs(mvals(q, k)) == sum_of(q, wm(w_abs(k))),
        forall|ck: int| #[trigger] mciks(q, k).contains(ck) <==> sum_of(q, wm(w_occ(k, ck))) > 0,
        forall|ck: int| sum_of(q, wm(w_occ(k, ck))) >= 0,
    decreases q.len(),
{
    if q.len() > 0 {
        let qi = q.drop_last();
        assert forall|i: int| 0 <= i < qi.len() implies qrow(b1, #[trigger] qi[i]) by { assert(qi[i] == q[i]); }
        lemma_q_weights(qi, b1, k);
        let x = q.last();
        assert(qrow(b1, q[q.len() - 1]));
        let m = mini(x);
        assert(m.subrange(0, 3) =~= kq(x));
        assert(m[3] == x[10] && m[4] == x[7]);
        let (ci, cv) = (mciks(qi, k), mvals(qi, k));
        assert forall|ck: int| #[trigger] mciks(q, k).contains(ck) <==> sum_of(q, wm(w_occ(k, ck))) > 0 by {
            assert(sum_of(q, wm(w_occ(k, ck))) == sum_of(qi, wm(w_occ(k, ck))) + wm(w_occ(k, ck))(x));
            if kq(x) == k {
                assert(mciks(q, k) == ci.push(ival(x[10])));
                if ci.contains(ck) {
                    let i = choose|i: int| 0 <= i < ci.len() && ci[i] == ck;
                    assert(mciks(q, k)[i] == ck);
                }
                if mciks(q, k).contains(ck) && !ci.contains(ck) {
                    let i = choose|i: int| 0 <= i < mciks(q, k).len() && mciks(q, k)[i] == ck;
                    if i < ci.len() { assert(ci[i] == ck); }
                }
                assert(mciks(q, k)[ci.len() as int] == ival(x[10]));
            } else {
                assert(mciks(q, k) == ci);
            }
        }
        assert forall|ck: int| sum_of(q, wm(w_occ(k, ck))) >= 0 by {
            assert(sum_of(q, wm(w_occ(k, ck))) == sum_of(qi, wm(w_occ(k, ck))) + wm(w_occ(k, ck))(x));
        }
        if kq(x) == k {
            assert(mvals(q, k) == cv.push(coeff(x[7])));
            assert(mvals(q, k).drop_last() =~= cv);
        } else {
            assert(mvals(q, k) == cv);
        }
    } else {
        assert forall|ck: int| #[trigger] mciks(q, k).contains(ck) <==> sum_of(q, wm(w_occ(k, ck))) > 0 by {}
    }
}

/// The key of a contribution's rows.
pub open spec fn keyc(db: Database, cx: Cx, c: CS) -> Row {
    seq![Val::Int(sic_of(db, cx, c.f)), tl_val(cx, c.slot), Val::Text(cx.b1)]
}

/// A run-pair sum of a weight that is a constant multiple (0 or 1) of another.
proof fn lemma_rps_scale(num: Seq<crate::gendb_entry::layout::PartView>, rs: int, re: int, nq: int,
    phi: spec_fn(Val) -> int, g: spec_fn(Val) -> int, on: bool)
    requires forall|v: Val| #[trigger] phi(v) == if on { g(v) } else { 0 },
    ensures run_pair_sum(num, rs, re, nq, phi) == if on { run_pair_sum(num, rs, re, nq, g) } else { 0 },
{
    let a = run_pair_term(num, nq, phi);
    let b = run_pair_term(num, nq, g);
    if on {
        assert forall|i: int| rs <= i < re implies #[trigger] a(i) == b(i) by {}
        lemma_rsum_ext(rs, re, a, b);
    } else {
        assert forall|i: int| rs <= i < re implies #[trigger] a(i) == 0 by {}
        lemma_rsum_zero(rs, re, a);
    }
}

/// One contribution's weights: its count, value sum, absolute sum, when it has the key (and the cik).
pub proof fn lemma_c_weights(db: Database, cx: Cx, c: CS, k: Row, ck: int)
    ensures
        csum(db, cx, c, w_cnt(k)) == if keyc(db, cx, c) == k { run_pair_cnt(cx.num, c.rs, c.re, c.nq) } else { 0 },
        csum(db, cx, c, w_sum(k)) == if keyc(db, cx, c) == k { run_pair_sum(cx.num, c.rs, c.re, c.nq, coeff_phi()) } else { 0 },
        csum(db, cx, c, w_abs(k)) == if keyc(db, cx, c) == k { run_pair_sum(cx.num, c.rs, c.re, c.nq, abs_phi()) } else { 0 },
        csum(db, cx, c, w_occ(k, ck)) == if keyc(db, cx, c) == k && cik_of(db, cx, c.f) == ck {
            run_pair_cnt(cx.num, c.rs, c.re, c.nq) } else { 0 },
{
    let (sic, tl, cik) = (sic_of(db, cx, c.f), tl_val(cx, c.slot), cik_of(db, cx, c.f));
    let key = keyc(db, cx, c);
    let on = key == k;
    let p1 = phi_of(cx.b1, sic, tl, cik, w_cnt(k));
    let p2 = phi_of(cx.b1, sic, tl, cik, w_sum(k));
    let p3 = phi_of(cx.b1, sic, tl, cik, w_abs(k));
    let p4 = phi_of(cx.b1, sic, tl, cik, w_occ(k, ck));
    assert forall|v: Val| #[trigger] p1(v) == if on { const1()(v) } else { 0 } by {
        assert(seq![Val::Int(sic), tl, Val::Text(cx.b1), Val::Int(cik), v].subrange(0, 3) =~= key);
    }
    assert forall|v: Val| #[trigger] p2(v) == if on { coeff_phi()(v) } else { 0 } by {
        assert(seq![Val::Int(sic), tl, Val::Text(cx.b1), Val::Int(cik), v].subrange(0, 3) =~= key);
    }
    assert forall|v: Val| #[trigger] p3(v) == if on { abs_phi()(v) } else { 0 } by {
        assert(seq![Val::Int(sic), tl, Val::Text(cx.b1), Val::Int(cik), v].subrange(0, 3) =~= key);
    }
    assert forall|v: Val| #[trigger] p4(v) == if on && cik == ck { const1()(v) } else { 0 } by {
        assert(seq![Val::Int(sic), tl, Val::Text(cx.b1), Val::Int(cik), v].subrange(0, 3) =~= key);
    }
    lemma_rps_scale(cx.num, c.rs, c.re, c.nq, phi_of(cx.b1, sic, tl, cik, w_cnt(k)), const1(), on);
    lemma_rps_scale(cx.num, c.rs, c.re, c.nq, phi_of(cx.b1, sic, tl, cik, w_sum(k)), coeff_phi(), on);
    lemma_rps_scale(cx.num, c.rs, c.re, c.nq, phi_of(cx.b1, sic, tl, cik, w_abs(k)), abs_phi(), on);
    lemma_rps_scale(cx.num, c.rs, c.re, c.nq, phi_of(cx.b1, sic, tl, cik, w_occ(k, ck)), const1(), on && cik == ck);
}

} // verus!
