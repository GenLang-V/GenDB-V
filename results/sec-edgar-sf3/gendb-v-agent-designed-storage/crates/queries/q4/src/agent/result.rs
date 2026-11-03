//! From the aggregated groups to the statement's rows. A group key of the kept rows is `key(cx, sic, slot)` for the
//! (sic, tlabel slot) of some contribution; its member count, sum, absolute sum and cik set are the contributions'
//! accumulators of that (sic, slot) (`lemma_group_vals`). With every group finished (`key_done`) the emitted groups'
//! rows are exactly the HAVING rows (`lemma_result_rows`), and a capacity witness names a group outside its domain
//! (`lemma_cap`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::join::{sum_of, keep};
use crate::agent::common::sums::*;
use crate::agent::common::groups::*;
use crate::agent::group::*;
use crate::agent::chain::mini;
use crate::agent::levels::*;
use crate::agent::filing::*;
use crate::agent::join::*;
use crate::agent::weights::*;
use crate::agent::agg::*;
use crate::stores::tag_tv::interface as T;

verus! {

pub open spec fn key(cx: Cx, s: int, sl: int) -> Row { seq![Val::Int(s), tl_val(cx, sl), Val::Text(cx.b1)] }

pub open spec fn qr(db: Database, cx: Cx) -> Seq<Row> { qrows(db, cx.b0, cx.b1, cx.lo, cx.hi) }

/// The aggregation's inputs: every contribution (in order), the filings' sic and cik.
pub open spec fn ag_ok(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>) -> bool {
    &&& cx_ok(db, cx)
    &&& cs_seq(cs) == all_cs(cx, cx.fil.len() as int)
    &&& forall|k: int| 0 <= k < cs.len() ==> contrib_ok(cx.num, #[trigger] cs[k])
    &&& forall|k: int| 0 <= k < cs.len() ==> (#[trigger] cs[k]).f < cx.fil.len() && cs[k].slot <= ntl(cx)
    &&& fs.len() == cx.fil.len() && fc.len() == cx.fil.len()
    &&& forall|f: int| 0 <= f < cx.fil.len() ==> #[trigger] fs[f] as int == sic_of(db, cx, f) && fc[f] as int == cik_of(db, cx, f)
}

// ------------------------------------------------------------------------------------------------ sums

pub open spec fn ct(db: Database, cx: Cx, cs: Seq<Contrib>, w: spec_fn(Row) -> int) -> spec_fn(int) -> int {
    |i: int| csum(db, cx, cs_of(cs[i]), w)
}

pub proof fn lemma_lsum_rsum(db: Database, cx: Cx, cs: Seq<Contrib>, w: spec_fn(Row) -> int)
    ensures lsum(db, cx, cs_seq(cs), w) == rsum(0, cs.len() as int, ct(db, cx, cs, w)),
    decreases cs.len(),
{
    if cs.len() > 0 {
        let ci = cs.drop_last();
        lemma_lsum_rsum(db, cx, ci, w);
        assert(cs_seq(cs).drop_last() =~= cs_seq(ci));
        assert(cs_seq(cs).last() == cs_of(cs.last()));
        assert forall|i: int| 0 <= i < ci.len() implies #[trigger] ct(db, cx, ci, w)(i) == ct(db, cx, cs, w)(i) by {
            assert(ci[i] == cs[i]);
        }
        lemma_rsum_ext(0, ci.len() as int, ct(db, cx, ci, w), ct(db, cx, cs, w));
    }
}

/// A nonnegative sum is at least each term.
pub proof fn lemma_rsum_ge_term(lo: int, hi: int, h: spec_fn(int) -> int, i: int)
    requires lo <= i < hi, forall|k: int| lo <= k < hi ==> #[trigger] h(k) >= 0,
    ensures rsum(lo, hi, h) >= h(i),
{
    lemma_rsum_split(lo, i, hi, h);
    lemma_rsum_split(i, i + 1, hi, h);
    lemma_rsum_nonneg(lo, i, h);
    lemma_rsum_nonneg(i + 1, hi, h);
    assert(rsum(i, i + 1, h) == h(i)) by { assert(rsum(i, i, h) == 0); }
}

/// A nonnegative sum is at least each window's.
pub proof fn lemma_rsum_ge_window(lo: int, b: int, e: int, hi: int, h: spec_fn(int) -> int)
    requires lo <= b <= e <= hi, forall|k: int| lo <= k < hi ==> #[trigger] h(k) >= 0,
    ensures rsum(lo, hi, h) >= rsum(b, e, h),
{
    lemma_rsum_split(lo, b, hi, h);
    lemma_rsum_split(b, e, hi, h);
    lemma_rsum_nonneg(lo, b, h);
    lemma_rsum_nonneg(e, hi, h);
}

/// A nonzero sum has a nonzero term.
pub proof fn lemma_rsum_nonzero(lo: int, hi: int, h: spec_fn(int) -> int)
    requires rsum(lo, hi, h) != 0,
    ensures exists|i: int| lo <= i < hi && #[trigger] h(i) != 0,
{
    if !(exists|i: int| lo <= i < hi && #[trigger] h(i) != 0) {
        lemma_rsum_zero(lo, hi, h);
    }
}

// ------------------------------------------------------------------------------------------------ keys

/// Distinct tlabel slots have distinct values.
pub proof fn lemma_tl_inj(cx: Cx, s1: int, s2: int)
    requires T::tag_layout_ok(cx.tag), 0 <= s1 <= ntl(cx), 0 <= s2 <= ntl(cx),
    ensures (tl_val(cx, s1) == tl_val(cx, s2)) == (s1 == s2),
{
    if s1 < ntl(cx) && s2 < ntl(cx) {
        let tag = cx.tag;
        crate::stores::tag_tv::interface::common::text::lemma_dict_codes(
            crate::stores::tag_tv::interface::common::text::u64_part(tag[T::P_TLABEL_OFF as int]),
            crate::stores::tag_tv::interface::common::text::u8_part(tag[T::P_TLABEL_OFF + 1]), ntl(cx), s1, s2);
    }
}

pub proof fn lemma_key_eq(cx: Cx, s1: int, l1: int, s2: int, l2: int)
    requires T::tag_layout_ok(cx.tag), 0 <= l1 <= ntl(cx), 0 <= l2 <= ntl(cx),
    ensures (key(cx, s1, l1) == key(cx, s2, l2)) == (s1 == s2 && l1 == l2),
{
    lemma_tl_inj(cx, l1, l2);
    if key(cx, s1, l1) == key(cx, s2, l2) {
        assert(key(cx, s1, l1)[0] == key(cx, s2, l2)[0]);
        assert(key(cx, s1, l1)[1] == key(cx, s2, l2)[1]);
    }
}

/// Contribution `i`'s key is `key(cx, s, sl)` exactly when it has (sic, slot) = (s, sl).
pub proof fn lemma_key_km(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, i: int, s: int, sl: int)
    requires ag_ok(db, cx, cs, fs, fc), 0 <= i < cs.len(), 0 <= sl <= ntl(cx),
    ensures
        keyc(db, cx, cs_of(cs[i])) == key(cx, fs[cs[i].f as int] as int, cs[i].slot as int),
        (keyc(db, cx, cs_of(cs[i])) == key(cx, s, sl)) == km(fs, cs, i, s, sl),
{
    let f = cs[i].f as int;
    assert(cs[i].f < cx.fil.len() && cs[i].slot <= ntl(cx));
    assert(fs[f] as int == sic_of(db, cx, f));
    assert(keyc(db, cx, cs_of(cs[i])) =~= key(cx, fs[f] as int, cs[i].slot as int));
    lemma_key_eq(cx, fs[f] as int, cs[i].slot as int, s, sl);
}

// ------------------------------------------------------------------------------------------------ group values

pub open spec fn xs_t(num: Seq<crate::gendb_entry::layout::PartView>, fs: Seq<i32>, cs: Seq<Contrib>, s: int, sl: int) -> spec_fn(int) -> int {
    |i: int| if km(fs, cs, i, s, sl) { c_sum(num, cs_of(cs[i])) } else { 0 }
}
pub open spec fn xm_t(num: Seq<crate::gendb_entry::layout::PartView>, fs: Seq<i32>, cs: Seq<Contrib>, s: int, sl: int) -> spec_fn(int) -> int {
    |i: int| if km(fs, cs, i, s, sl) { c_mass(num, cs_of(cs[i])) } else { 0 }
}
pub open spec fn occ_t(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, s: int, sl: int, ck: int) -> spec_fn(int) -> int {
    |i: int| if km(fs, cs, i, s, sl) && fc[cs[i].f as int] as int == ck { cs[i].cnt as int } else { 0 }
}

proof fn lemma_ct_i(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, s: int, sl: int, ck: int, i: int)
    requires ag_ok(db, cx, cs, fs, fc), 0 <= sl <= ntl(cx), 0 <= i < cs.len(),
    ensures ({
        let k = key(cx, s, sl);
        &&& ct(db, cx, cs, w_cnt(k))(i) == cnt_t(fs, cs, s, sl)(i)
        &&& ct(db, cx, cs, w_sum(k))(i) == xs_t(cx.num, fs, cs, s, sl)(i)
        &&& ct(db, cx, cs, w_abs(k))(i) == xm_t(cx.num, fs, cs, s, sl)(i)
        &&& ct(db, cx, cs, w_occ(k, ck))(i) == occ_t(fs, fc, cs, s, sl, ck)(i)
    }),
{
    let k = key(cx, s, sl);
    lemma_c_weights(db, cx, cs_of(cs[i]), k, ck);
    lemma_key_km(db, cx, cs, fs, fc, i, s, sl);
    assert(contrib_ok(cx.num, cs[i]));
    let f = cs[i].f as int;
    assert(cs[i].f < cx.fil.len());
    assert(fc[f] as int == cik_of(db, cx, f));
}

/// The kept rows' weighted sums of a key are the contributions' sums.
proof fn lemma_weight_sums(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, s: int, sl: int, ck: int)
    requires ag_ok(db, cx, cs, fs, fc), 0 <= sl <= ntl(cx),
    ensures ({
        let (q, k, n) = (qr(db, cx), key(cx, s, sl), cs.len() as int);
        &&& sum_of(q, wm(w_cnt(k))) == acnt(fs, cs, 0, n, s, sl)
        &&& sum_of(q, wm(w_sum(k))) == rsum(0, n, xs_t(cx.num, fs, cs, s, sl))
        &&& sum_of(q, wm(w_abs(k))) == rsum(0, n, xm_t(cx.num, fs, cs, s, sl))
        &&& sum_of(q, wm(w_occ(k, ck))) == rsum(0, n, occ_t(fs, fc, cs, s, sl, ck))
    }),
{
    let (q, k, n) = (qr(db, cx), key(cx, s, sl), cs.len() as int);
    let nf = cx.fil.len() as int;
    lemma_all(db, cx, w_cnt(k));
    lemma_all(db, cx, w_sum(k));
    lemma_all(db, cx, w_abs(k));
    lemma_all(db, cx, w_occ(k, ck));
    assert(wm(w_cnt(k)) =~= |x: Row| w_cnt(k)(mini(x)));
    assert(wm(w_sum(k)) =~= |x: Row| w_sum(k)(mini(x)));
    assert(wm(w_abs(k)) =~= |x: Row| w_abs(k)(mini(x)));
    assert(wm(w_occ(k, ck)) =~= |x: Row| w_occ(k, ck)(mini(x)));
    lemma_lsum_rsum(db, cx, cs, w_cnt(k));
    lemma_lsum_rsum(db, cx, cs, w_sum(k));
    lemma_lsum_rsum(db, cx, cs, w_abs(k));
    lemma_lsum_rsum(db, cx, cs, w_occ(k, ck));
    assert forall|i: int| 0 <= i < n implies #[trigger] ct(db, cx, cs, w_cnt(k))(i) == cnt_t(fs, cs, s, sl)(i) by {
        lemma_ct_i(db, cx, cs, fs, fc, s, sl, ck, i);
    }
    assert forall|i: int| 0 <= i < n implies #[trigger] ct(db, cx, cs, w_sum(k))(i) == xs_t(cx.num, fs, cs, s, sl)(i) by {
        lemma_ct_i(db, cx, cs, fs, fc, s, sl, ck, i);
    }
    assert forall|i: int| 0 <= i < n implies #[trigger] ct(db, cx, cs, w_abs(k))(i) == xm_t(cx.num, fs, cs, s, sl)(i) by {
        lemma_ct_i(db, cx, cs, fs, fc, s, sl, ck, i);
    }
    assert forall|i: int| 0 <= i < n implies #[trigger] ct(db, cx, cs, w_occ(k, ck))(i) == occ_t(fs, fc, cs, s, sl, ck)(i) by {
        lemma_ct_i(db, cx, cs, fs, fc, s, sl, ck, i);
    }
    lemma_rsum_ext(0, n, ct(db, cx, cs, w_cnt(k)), cnt_t(fs, cs, s, sl));
    lemma_rsum_ext(0, n, ct(db, cx, cs, w_sum(k)), xs_t(cx.num, fs, cs, s, sl));
    lemma_rsum_ext(0, n, ct(db, cx, cs, w_abs(k)), xm_t(cx.num, fs, cs, s, sl));
    lemma_rsum_ext(0, n, ct(db, cx, cs, w_occ(k, ck)), occ_t(fs, fc, cs, s, sl, ck));
}

/// The members of group `key(cx, s, sl)`: count, sum, absolute sum, cik set.
pub proof fn lemma_group_vals(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, s: int, sl: int)
    requires ag_ok(db, cx, cs, fs, fc), 0 <= sl <= ntl(cx),
    ensures ({
        let (q, k, n) = (qr(db, cx), key(cx, s, sl), cs.len() as int);
        &&& mvals(q, k).len() == acnt(fs, cs, 0, n, s, sl)
        &&& isum(mvals(q, k)) == rsum(0, n, xs_t(cx.num, fs, cs, s, sl))
        &&& iabs(mvals(q, k)) == rsum(0, n, xm_t(cx.num, fs, cs, s, sl))
        &&& mciks(q, k).to_set() == aciks(fs, fc, cs, 0, n, s, sl)
    }),
{
    let (q, k, n) = (qr(db, cx), key(cx, s, sl), cs.len() as int);
    lemma_qrows_shape(db, cx.b0, cx.b1, cx.lo, cx.hi);
    lemma_q_weights(q, cx.b1, k);
    lemma_weight_sums(db, cx, cs, fs, fc, s, sl, 0);
    assert forall|ck: int| #[trigger] mciks(q, k).to_set().contains(ck) == aciks(fs, fc, cs, 0, n, s, sl).contains(ck) by {
        lemma_weight_sums(db, cx, cs, fs, fc, s, sl, ck);
        lemma_aciks_mem(fs, fc, cs, 0, n, s, sl, ck);
        let h = occ_t(fs, fc, cs, s, sl, ck);
        assert forall|i: int| 0 <= i < n implies #[trigger] h(i) >= 0 by {}
        if rsum(0, n, h) > 0 {
            lemma_rsum_nonzero(0, n, h);
            let i = choose|i: int| 0 <= i < n && #[trigger] h(i) != 0;
            assert(km(fs, cs, i, s, sl) && fc[cs[i].f as int] as int == ck);
        }
        if aciks(fs, fc, cs, 0, n, s, sl).contains(ck) {
            let i = choose|i: int| 0 <= i < n && #[trigger] km(fs, cs, i, s, sl) && fc[cs[i].f as int] as int == ck;
            assert(contrib_ok(cx.num, cs[i]));
            lemma_rsum_ge_term(0, n, h, i);
        }
        lemma_rsum_nonneg(0, n, h);
    }
    assert(mciks(q, k).to_set() =~= aciks(fs, fc, cs, 0, n, s, sl));
}

/// A key of the kept rows is the key of some contribution.
pub proof fn lemma_key_witness(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, k: Row)
    requires ag_ok(db, cx, cs, fs, fc), qr(db, cx).map_values(|x: Row| kq(x)).contains(k),
    ensures exists|i: int| 0 <= i < cs.len() && k == key(cx, fs[(#[trigger] cs[i]).f as int] as int, cs[i].slot as int),
{
    let (q, n) = (qr(db, cx), cs.len() as int);
    lemma_key_members(q, k);
    lemma_qrows_shape(db, cx.b0, cx.b1, cx.lo, cx.hi);
    lemma_q_weights(q, cx.b1, k);
    lemma_all(db, cx, w_cnt(k));
    assert(wm(w_cnt(k)) =~= |x: Row| w_cnt(k)(mini(x)));
    lemma_lsum_rsum(db, cx, cs, w_cnt(k));
    lemma_rsum_nonzero(0, n, ct(db, cx, cs, w_cnt(k)));
    let i = choose|i: int| 0 <= i < n && #[trigger] ct(db, cx, cs, w_cnt(k))(i) != 0;
    lemma_c_weights(db, cx, cs_of(cs[i]), k, 0);
    lemma_key_km(db, cx, cs, fs, fc, i, 0, 0);
}

/// A group with members is a key of the kept rows.
pub proof fn lemma_members_key(q: Seq<Row>, k: Row)
    requires mvals(q, k).len() > 0,
    ensures q.map_values(|x: Row| kq(x)).contains(k),
    decreases q.len(),
{
    let qi = q.drop_last();
    if kq(q.last()) == k {
        assert(q.map_values(|x: Row| kq(x))[q.len() - 1] == k);
    } else {
        lemma_members_key(qi, k);
        let qm = qi.map_values(|x: Row| kq(x));
        let i = choose|i: int| 0 <= i < qm.len() && #[trigger] qm[i] == k;
        assert(qi[i] == q[i]);
        assert(q.map_values(|x: Row| kq(x))[i] == k);
    }
}

// ------------------------------------------------------------------------------------------------ rows

pub open spec fn grp_row(cx: Cx, g: Grp) -> Row {
    key(cx, g.sic as int, g.slot as int) + seq![Val::Int(g.dcnt as int), num4(g.sum as int), g.avg@]
}

pub open spec fn grp_rows(cx: Cx, gs: Seq<Grp>) -> Seq<Row> { gs.map_values(|g: Grp| grp_row(cx, g)) }

pub proof fn lemma_keep_mem(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    requires rows.no_duplicates(),
    ensures
        keep(rows, f).no_duplicates(),
        forall|x: Row| #[trigger] keep(rows, f).contains(x) <==> rows.contains(x) && f(x),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert(ri.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < j < ri.len() implies ri[i] != ri[j] by { assert(ri[i] == rows[i] && ri[j] == rows[j]); }
        }
        lemma_keep_mem(ri, f);
        let x = rows.last();
        assert(!ri.contains(x)) by {
            if ri.contains(x) {
                let i = choose|i: int| 0 <= i < ri.len() && ri[i] == x;
                assert(rows[i] == rows[rows.len() - 1]);
            }
        }
        let kr = keep(ri, f);
        assert forall|y: Row| #[trigger] keep(rows, f).contains(y) <==> rows.contains(y) && f(y) by {
            if rows.contains(y) {
                let i = choose|i: int| 0 <= i < rows.len() && rows[i] == y;
                if i < ri.len() { assert(ri[i] == y); }
            }
            if ri.contains(y) {
                let i = choose|i: int| 0 <= i < ri.len() && ri[i] == y;
                assert(rows[i] == y);
            }
            if f(x) {
                assert(keep(rows, f) == kr.push(x));
                if kr.contains(y) {
                    let i = choose|i: int| 0 <= i < kr.len() && kr[i] == y;
                    assert(kr.push(x)[i] == y);
                }
                if kr.push(x).contains(y) && y != x {
                    let i = choose|i: int| 0 <= i < kr.len() + 1 && kr.push(x)[i] == y;
                    assert(i < kr.len());
                    assert(kr[i] == y);
                }
                if y == x { assert(kr.push(x)[kr.len() as int] == y); }
            } else {
                assert(keep(rows, f) == kr);
            }
        }
        if f(x) {
            assert(keep(rows, f) == kr.push(x));
            assert(!kr.contains(x));
            assert forall|i: int, j: int| 0 <= i < j < kr.len() + 1 implies kr.push(x)[i] != kr.push(x)[j] by {
                if j == kr.len() { assert(kr.contains(kr.push(x)[i])) by { assert(kr[i] == kr.push(x)[i]); } }
            }
        }
    }
}

/// The GROUP BY rows have no duplicates and are the keys' rows.
pub proof fn lemma_grows_mem(q: Seq<Row>)
    ensures
        grows(q).no_duplicates(),
        forall|r: Row| #[trigger] grows(q).contains(r) <==> exists|k: Row| q.map_values(|x: Row| kq(x)).contains(k) && r == k + gvals(q, k),
{
    let ks = q.map_values(|x: Row| kq(x));
    lemma_dk(ks);
    let d = dk(ks);
    let g = grows(q);
    assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]).len() == 3 by {
        assert(d.contains(d[i]));
        let j = choose|j: int| 0 <= j < ks.len() && ks[j] == d[i];
    }
    assert forall|i: int, j: int| 0 <= i < j < g.len() implies g[i] != g[j] by {
        assert(g[i] == d[i] + gvals(q, d[i]) && g[j] == d[j] + gvals(q, d[j]));
        if g[i] == g[j] {
            assert(g[i].subrange(0, 3) =~= d[i]);
            assert(g[j].subrange(0, 3) =~= d[j]);
        }
    }
    assert forall|r: Row| #[trigger] g.contains(r) <==> exists|k: Row| ks.contains(k) && r == k + gvals(q, k) by {
        if g.contains(r) {
            let i = choose|i: int| 0 <= i < g.len() && g[i] == r;
            assert(d.contains(d[i]));
            assert(ks.contains(d[i]) && r == d[i] + gvals(q, d[i]));
        }
        if exists|k: Row| ks.contains(k) && r == k + gvals(q, k) {
            let k = choose|k: Row| ks.contains(k) && r == k + gvals(q, k);
            assert(d.contains(k));
            let i = choose|i: int| 0 <= i < d.len() && d[i] == k;
            assert(g[i] == r);
        }
    }
}

pub open spec fn res_pre(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, gs: Seq<Grp>) -> bool {
    &&& ag_ok(db, cx, cs, fs, fc)
    &&& forall|k: int| 0 <= k < cs.len() ==> (#[trigger] cs[k]).ok
    &&& forall|i: int| 0 <= i < gs.len() ==> grp_ok(fs, fc, cs, ntl(cx) + 1, #[trigger] gs[i])
    &&& gkeys_distinct(gs)
    &&& forall|s: int, sl: int| 0 <= sl < ntl(cx) + 1 ==> #[trigger] key_done(fs, fc, cs, gs, s, sl)
}

/// With every contribution exact, a key's members are its accumulators.
proof fn lemma_exact_vals(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, s: int, sl: int)
    requires ag_ok(db, cx, cs, fs, fc), forall|k: int| 0 <= k < cs.len() ==> (#[trigger] cs[k]).ok, 0 <= sl <= ntl(cx),
    ensures ({
        let (q, k, n) = (qr(db, cx), key(cx, s, sl), cs.len() as int);
        &&& isum(mvals(q, k)) == asum(fs, cs, 0, n, s, sl)
        &&& iabs(mvals(q, k)) == amass(fs, cs, 0, n, s, sl)
        &&& mvals(q, k).len() == acnt(fs, cs, 0, n, s, sl)
        &&& mciks(q, k).to_set() == aciks(fs, fc, cs, 0, n, s, sl)
    }),
{
    let n = cs.len() as int;
    lemma_group_vals(db, cx, cs, fs, fc, s, sl);
    assert forall|i: int| 0 <= i < n implies #[trigger] xs_t(cx.num, fs, cs, s, sl)(i) == sum_t(fs, cs, s, sl)(i) by {
        assert(contrib_ok(cx.num, cs[i]) && cs[i].ok);
    }
    lemma_rsum_ext(0, n, xs_t(cx.num, fs, cs, s, sl), sum_t(fs, cs, s, sl));
    assert forall|i: int| 0 <= i < n implies #[trigger] xm_t(cx.num, fs, cs, s, sl)(i) == mass_t(fs, cs, s, sl)(i) by {
        assert(contrib_ok(cx.num, cs[i]) && cs[i].ok);
    }
    lemma_rsum_ext(0, n, xm_t(cx.num, fs, cs, s, sl), mass_t(fs, cs, s, sl));
}

/// A key of the kept rows is a finished (sic, slot) with contributions.
proof fn lemma_key_done_of(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, gs: Seq<Grp>, k: Row)
    requires res_pre(db, cx, cs, fs, fc, gs), qr(db, cx).map_values(|x: Row| kq(x)).contains(k),
    ensures exists|s: int, sl: int| 0 <= sl <= ntl(cx) && k == key(cx, s, sl) && #[trigger] ahas(fs, cs, 0, cs.len() as int, s, sl)
        && key_done(fs, fc, cs, gs, s, sl),
{
    lemma_key_witness(db, cx, cs, fs, fc, k);
    let i = choose|i: int| 0 <= i < cs.len() && k == key(cx, fs[(#[trigger] cs[i]).f as int] as int, cs[i].slot as int);
    let (s, sl) = (fs[cs[i].f as int] as int, cs[i].slot as int);
    assert(cs[i].f < cx.fil.len() && cs[i].slot <= ntl(cx));
    assert(km(fs, cs, i, s, sl));
    assert(ahas(fs, cs, 0, cs.len() as int, s, sl));
    assert(key_done(fs, fc, cs, gs, s, sl));
}

proof fn lemma_fits_all(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, gs: Seq<Grp>)
    requires res_pre(db, cx, cs, fs, fc, gs),
    ensures forall|k: Row| qr(db, cx).map_values(|x: Row| kq(x)).contains(k) ==> #[trigger] group_fits(qr(db, cx), k),
{
    assert forall|k: Row| qr(db, cx).map_values(|x: Row| kq(x)).contains(k) implies #[trigger] group_fits(qr(db, cx), k) by {
        lemma_key_done_of(db, cx, cs, fs, fc, gs, k);
        let (s, sl) = choose|s: int, sl: int| 0 <= sl <= ntl(cx) && k == key(cx, s, sl) && #[trigger] ahas(fs, cs, 0, cs.len() as int, s, sl)
            && key_done(fs, fc, cs, gs, s, sl);
        lemma_exact_vals(db, cx, cs, fs, fc, s, sl);
    }
}

/// An emitted group's row is a HAVING row.
proof fn lemma_rr_in(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, gs: Seq<Grp>, i: int)
    requires res_pre(db, cx, cs, fs, fc, gs), 0 <= i < gs.len(),
    ensures grows(qr(db, cx)).contains(grp_row(cx, gs[i])), having_ok(grp_row(cx, gs[i])),
{
    let (q, n) = (qr(db, cx), cs.len() as int);
    let g = gs[i];
    assert(grp_ok(fs, fc, cs, ntl(cx) + 1, g));
    let (s, sl) = (g.sic as int, g.slot as int);
    let k = key(cx, s, sl);
    lemma_exact_vals(db, cx, cs, fs, fc, s, sl);
    assert forall|j: int| 0 <= j < cs.len() implies #[trigger] cs[j].cnt > 0 by { assert(contrib_ok(cx.num, cs[j])); }
    lemma_acc_props_global(fs, fc, cs, s, sl);
    lemma_members_key(q, k);
    assert(gvals(q, k) =~= seq![Val::Int(g.dcnt as int), num4(g.sum as int), g.avg@]);
    lemma_grows_mem(q);
    assert(grows(q).contains(k + gvals(q, k)));
    assert(grp_row(cx, g)[3] == Val::Int(g.dcnt as int));
}

/// A HAVING row is an emitted group's row.
proof fn lemma_hk_in(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, gs: Seq<Grp>, r: Row)
    requires res_pre(db, cx, cs, fs, fc, gs), grows(qr(db, cx)).contains(r), having_ok(r),
    ensures exists|j: int| 0 <= j < gs.len() && r == grp_row(cx, #[trigger] gs[j]),
{
    // The sub layout is not needed here (its quantifiers only slow the solver down).
    hide(crate::stores::sub_sic::interface::sub_layout_ok);
    let (q, n) = (qr(db, cx), cs.len() as int);
    let ks = q.map_values(|x: Row| kq(x));
    lemma_grows_mem(q);
    let k = choose|k: Row| ks.contains(k) && r == k + gvals(q, k);
    lemma_key_done_of(db, cx, cs, fs, fc, gs, k);
    let (s, sl) = choose|s: int, sl: int| 0 <= sl <= ntl(cx) && k == key(cx, s, sl) && #[trigger] ahas(fs, cs, 0, cs.len() as int, s, sl)
        && key_done(fs, fc, cs, gs, s, sl);
    lemma_exact_vals(db, cx, cs, fs, fc, s, sl);
    assert(k.len() == 3);
    assert(r[3] == gvals(q, k)[0]);
    assert(aciks(fs, fc, cs, 0, n, s, sl).len() >= 2);
    let j = choose|j: int| 0 <= j < gs.len() && (#[trigger] gs[j]).sic as int == s && gs[j].slot as int == sl;
    let g = gs[j];
    assert(grp_ok(fs, fc, cs, ntl(cx) + 1, g));
    assert(gvals(q, k) =~= seq![Val::Int(g.dcnt as int), num4(g.sum as int), g.avg@]);
    assert(grp_row(cx, g) == r);
}

proof fn lemma_rr_nodup(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, gs: Seq<Grp>)
    requires res_pre(db, cx, cs, fs, fc, gs),
    ensures grp_rows(cx, gs).no_duplicates(),
{
    let rr = grp_rows(cx, gs);
    let ns = ntl(cx) + 1;
    assert forall|i: int, j: int| 0 <= i < j < rr.len() implies rr[i] != rr[j] by {
        let (gi, gj) = (gs[i], gs[j]);
        assert(grp_ok(fs, fc, cs, ns, gi) && grp_ok(fs, fc, cs, ns, gj));
        if rr[i] == rr[j] {
            assert(rr[i].subrange(0, 3) =~= key(cx, gi.sic as int, gi.slot as int));
            assert(rr[j].subrange(0, 3) =~= key(cx, gj.sic as int, gj.slot as int));
            lemma_key_eq(cx, gi.sic as int, gi.slot as int, gj.sic as int, gj.slot as int);
        }
    }
}

proof fn lemma_rr_mem(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, gs: Seq<Grp>, r: Row)
    requires res_pre(db, cx, cs, fs, fc, gs),
    ensures grp_rows(cx, gs).contains(r) <==> keep(grows(qr(db, cx)), |r: Row| having_ok(r)).contains(r),
{
    let q = qr(db, cx);
    let hv = |r: Row| having_ok(r);
    let rr = grp_rows(cx, gs);
    lemma_grows_mem(q);
    lemma_keep_mem(grows(q), hv);
    if rr.contains(r) {
        let i = choose|i: int| 0 <= i < rr.len() && rr[i] == r;
        lemma_rr_in(db, cx, cs, fs, fc, gs, i);
    }
    if keep(grows(q), hv).contains(r) {
        lemma_hk_in(db, cx, cs, fs, fc, gs, r);
        let j = choose|j: int| 0 <= j < gs.len() && r == grp_row(cx, #[trigger] gs[j]);
        assert(rr[j] == r);
    }
}

/// Every group fits and the emitted groups' rows are the HAVING rows (same multiset).
pub proof fn lemma_result_rows(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, gs: Seq<Grp>)
    requires res_pre(db, cx, cs, fs, fc, gs),
    ensures
        forall|k: Row| qr(db, cx).map_values(|x: Row| kq(x)).contains(k) ==> #[trigger] group_fits(qr(db, cx), k),
        grp_rows(cx, gs).to_multiset() == keep(grows(qr(db, cx)), |r: Row| having_ok(r)).to_multiset(),
        grp_rows(cx, gs).no_duplicates(),
{
    hide(res_pre);
    hide(grows);
    let q = qr(db, cx);
    let hv = |r: Row| having_ok(r);
    lemma_fits_all(db, cx, cs, fs, fc, gs);
    lemma_rr_nodup(db, cx, cs, fs, fc, gs);
    lemma_grows_mem(q);
    lemma_keep_mem(grows(q), hv);
    assert forall|r: Row| grp_rows(cx, gs).contains(r) <==> #[trigger] keep(grows(q), hv).contains(r) by {
        lemma_rr_mem(db, cx, cs, fs, fc, gs, r);
    }
    crate::link::query::lemma_nodup_same_multiset(grp_rows(cx, gs), keep(grows(q), hv));
}

/// `ahas` over all contributions: positive count.
proof fn lemma_acc_props_global(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, s: int, sl: int)
    requires ahas(fs, cs, 0, cs.len() as int, s, sl), forall|k: int| 0 <= k < cs.len() ==> (#[trigger] cs[k]).cnt > 0,
    ensures acnt(fs, cs, 0, cs.len() as int, s, sl) > 0,
{
    let n = cs.len() as int;
    let k = choose|k: int| 0 <= k < n && #[trigger] km(fs, cs, k, s, sl);
    assert forall|i: int| 0 <= i < n implies #[trigger] cnt_t(fs, cs, s, sl)(i) >= 0 by {}
    lemma_rsum_ge_term(0, n, cnt_t(fs, cs, s, sl), k);
}

// ------------------------------------------------------------------------------------------------ capacity

/// A capacity witness names a key of the kept rows outside its domain.
pub proof fn lemma_cap(db: Database, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, cap: Cap)
    requires ag_ok(db, cx, cs, fs, fc), cap_ok(fs, cs, cap),
    ensures ({
        let k = key(cx, fs[cs[cap.k@].f as int] as int, cs[cap.k@].slot as int);
        qr(db, cx).map_values(|x: Row| kq(x)).contains(k) && !group_fits(qr(db, cx), k)
    }),
{
    let (q, n) = (qr(db, cx), cs.len() as int);
    let j = cap.k@;
    let c = cs[j];
    assert(c.f < cx.fil.len() && c.slot <= ntl(cx));
    let (s, sl) = (fs[c.f as int] as int, c.slot as int);
    let k = key(cx, s, sl);
    assert(km(fs, cs, j, s, sl));
    lemma_group_vals(db, cx, cs, fs, fc, s, sl);
    assert forall|i: int| 0 <= i < n implies #[trigger] cs[i].cnt > 0 by { assert(contrib_ok(cx.num, cs[i])); }
    assert(ahas(fs, cs, 0, n, s, sl));
    lemma_acc_props_global(fs, fc, cs, s, sl);
    lemma_members_key(q, k);
    let hm = xm_t(cx.num, fs, cs, s, sl);
    assert forall|i: int| 0 <= i < n implies #[trigger] hm(i) >= 0 by {
        lemma_rsum_nonneg(cs_of(cs[i]).rs, cs_of(cs[i]).re, run_pair_term(cx.num, cs_of(cs[i]).nq, abs_phi()));
    }
    let (b, e) = (cap.b@, cap.e@);
    if cap.kind@ == 0 {
        assert(contrib_ok(cx.num, c));
        lemma_rsum_ge_term(0, n, hm, j);
    } else {
        // Inside the block every contribution is exact: its mass and sum are the fields.
        assert forall|i: int| b <= i < e implies #[trigger] hm(i) == mass_t(fs, cs, s, sl)(i)
            && xs_t(cx.num, fs, cs, s, sl)(i) == sum_t(fs, cs, s, sl)(i) by {
            assert(contrib_ok(cx.num, cs[i]) && cs[i].ok);
        }
        lemma_rsum_ext(b, e, hm, mass_t(fs, cs, s, sl));
        assert forall|i: int| b <= i < e implies #[trigger] xs_t(cx.num, fs, cs, s, sl)(i) == sum_t(fs, cs, s, sl)(i) by {
            assert(contrib_ok(cx.num, cs[i]) && cs[i].ok);
        }
        lemma_rsum_ext(b, e, xs_t(cx.num, fs, cs, s, sl), sum_t(fs, cs, s, sl));
        if cap.kind@ == 1 {
            lemma_rsum_ge_window(0, b, e, n, hm);
        } else {
            assert forall|i: int| 0 <= i < n && !(b <= i < e) implies #[trigger] hm(i) == 0 && xs_t(cx.num, fs, cs, s, sl)(i) == 0 by {
                assert(fs[cs[i].f as int] as int != s);
            }
            lemma_rsum_window(0, b, e, n, hm);
            assert forall|i: int| 0 <= i < n && !(b <= i < e) implies #[trigger] xs_t(cx.num, fs, cs, s, sl)(i) == 0 by {
                assert(fs[cs[i].f as int] as int != s);
            }
            lemma_rsum_window(0, b, e, n, xs_t(cx.num, fs, cs, s, sl));
            assert forall|i: int| 0 <= i < n && !(b <= i < e) implies !#[trigger] km(fs, cs, i, s, sl) by {
                assert(fs[cs[i].f as int] as int != s);
            }
            lemma_window(fs, fc, cs, 0, b, e, n, s, sl);
        }
    }
}

} // verus!
