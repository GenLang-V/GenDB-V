//! The answer rows: the groups kept by HAVING, sorted by decreasing sum, first 100 (`lemma_rows_answer`).
//!
//! The statement's body is `keep(outer group rows, sum > avg)`; the computation keeps the same groups in its own
//! group order (`kept_upto`) and sorts them by decreasing sum, so the sorted rows are a permutation of the body,
//! sorted by the ORDER BY key, and the answer is their first 100.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::fns::div::num_div_fits;
use crate::gendb_entry::layout::PartView;
use crate::query::query_spec_at;
use crate::link::query::{QuerySpec, gsum, gcount, gkeys, full_row, agg_outs, avg_of, lemma_gkeys, lemma_map_multiset};
use crate::link::join::{keep, lemma_keep_append, lemma_keep_push};
use crate::link::expr::i128_max;
use crate::agent::common::sort::{Filing, SumRef, DescSumOrder, SortOrder, sorted_by as sort_sorted};
use crate::agent::common::sums::*;
use crate::agent::ast::*;
use crate::agent::nf::*;
use crate::agent::scan::*;
use crate::agent::groups::*;
use crate::agent::link::*;
use crate::agent::eval::*;
use crate::agent::assemble::*;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// The output row of outer group `h`: name, cik, sum.
pub open spec fn rr(sp: Seq<PartView>, g: Groups, h: int) -> Row {
    kspec(sp, hkey(g, h, true), true) + seq![Val::Num { coeff: g.sum@[h] as int, scale: 4 }]
}

/// The HAVING condition on an output row, for the AVG value `Num { ac, asc }`.
pub open spec fn hv(ac: int, asc: nat) -> spec_fn(Row) -> bool {
    |r: Row| num_cmp(coeff(r[2]), 4, ac, asc) > 0
}

/// The groups `0..h` kept by HAVING, as references `(sum, index)`.
pub open spec fn kept_upto(g: Groups, ac: int, asc: nat, h: int) -> Seq<SumRef>
    decreases h,
{
    if h <= 0 {
        Seq::empty()
    } else {
        kept_upto(g, ac, asc, h - 1) + if num_cmp(g.sum@[h - 1] as int, 4, ac, asc) > 0 {
            seq![SumRef { sum: g.sum@[h - 1], idx: (h - 1) as u64 }]
        } else {
            Seq::<SumRef>::empty()
        }
    }
}

pub open spec fn rr_of(sp: Seq<PartView>, g: Groups) -> spec_fn(SumRef) -> Row {
    |e: SumRef| rr(sp, g, e.idx as int)
}

/// The kept references name the kept output rows.
pub proof fn lemma_kept_rows(sp: Seq<PartView>, g: Groups, ac: int, asc: nat, h: int)
    requires 0 <= h <= g.sum@.len(), g.sum@.len() <= u64::MAX,
    ensures
        kept_upto(g, ac, asc, h).map_values(rr_of(sp, g)) == keep(Seq::new(h as nat, |i: int| rr(sp, g, i)), hv(ac, asc)),
        forall|q: int| 0 <= q < kept_upto(g, ac, asc, h).len() ==> (#[trigger] kept_upto(g, ac, asc, h)[q]).idx < h
            && kept_upto(g, ac, asc, h)[q].sum == g.sum@[kept_upto(g, ac, asc, h)[q].idx as int],
    decreases h,
{
    let s = Seq::new(h as nat, |i: int| rr(sp, g, i));
    if h > 0 {
        lemma_kept_rows(sp, g, ac, asc, h - 1);
        let si = Seq::new((h - 1) as nat, |i: int| rr(sp, g, i));
        assert(s.drop_last() =~= si);
        assert(s.last() == rr(sp, g, h - 1));
        assert(rr(sp, g, h - 1)[2] == Val::Num { coeff: g.sum@[h - 1] as int, scale: 4 });
        let ki = kept_upto(g, ac, asc, h - 1);
        if num_cmp(g.sum@[h - 1] as int, 4, ac, asc) > 0 {
            let e = SumRef { sum: g.sum@[h - 1], idx: (h - 1) as u64 };
            assert(e.idx as int == h - 1);
            assert(kept_upto(g, ac, asc, h) == ki.push(e)) by {
                assert(ki + seq![e] =~= ki.push(e));
            }
            assert(ki.push(e).map_values(rr_of(sp, g)) =~= ki.map_values(rr_of(sp, g)).push(rr_of(sp, g)(e)));
            assert forall|q: int| 0 <= q < ki.push(e).len() implies (#[trigger] ki.push(e)[q]).idx < h
                && ki.push(e)[q].sum == g.sum@[ki.push(e)[q].idx as int] by {
                if q < ki.len() {
                    assert(ki.push(e)[q] == ki[q]);
                }
            }
        } else {
            assert(kept_upto(g, ac, asc, h) =~= ki);
        }
    } else {
        assert(kept_upto(g, ac, asc, h).map_values(rr_of(sp, g)) =~= Seq::<Row>::empty());
    }
}

/// The sorted kept references name groups.
pub proof fn lemma_sorted_kept(sp: Seq<PartView>, g: Groups, ac: int, asc: nat, sorted: Seq<SumRef>)
    requires
        g.sum@.len() <= u64::MAX,
        sorted.to_multiset() == kept_upto(g, ac, asc, g.sum@.len() as int).to_multiset(),
    ensures forall|q: int| 0 <= q < sorted.len() ==> (#[trigger] sorted[q]).idx < g.sum@.len(),
{
    let kept = kept_upto(g, ac, asc, g.sum@.len() as int);
    lemma_kept_rows(sp, g, ac, asc, g.sum@.len() as int);
    assert forall|q: int| 0 <= q < sorted.len() implies (#[trigger] sorted[q]).idx < g.sum@.len() by {
        assert(sorted.contains(sorted[q]));
        assert(sorted.to_multiset().count(sorted[q]) > 0);
        assert(kept.contains(sorted[q]));
    }
}

/// Equal multisets keep equal multisets.
pub proof fn lemma_keep_multiset(s: Seq<Row>, t: Seq<Row>, f: spec_fn(Row) -> bool)
    requires s.to_multiset() == t.to_multiset(),
    ensures keep(s, f).to_multiset() == keep(t, f).to_multiset(),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(t.len() == t.to_multiset().len());
        assert(t =~= Seq::<Row>::empty());
    } else {
        let x = s.last();
        let si = s.drop_last();
        assert(si.push(x) =~= s);
        assert(s.to_multiset().count(x) > 0);
        assert(t.contains(x));
        let i = choose|i: int| 0 <= i < t.len() && t[i] == x;
        let ti = t.remove(i);
        assert(ti.to_multiset() =~= t.to_multiset().remove(x));
        assert(si.to_multiset() =~= s.to_multiset().remove(x));
        lemma_keep_multiset(si, ti, f);
        let (a, one, b) = (t.take(i), seq![x], t.skip(i + 1));
        assert(t =~= a + one + b);
        assert(ti =~= a + b);
        lemma_keep_append(a + one, b, f);
        lemma_keep_append(a, one, f);
        lemma_keep_append(a, b, f);
        lemma_keep_push(si, x, f);
        lemma_keep_push(Seq::<Row>::empty(), x, f);
        assert(Seq::<Row>::empty().push(x) =~= one);
        assert(keep(Seq::<Row>::empty(), f) =~= Seq::<Row>::empty());
        let kx = keep(one, f);
        vstd::seq_lib::lemma_multiset_commutative(keep(a, f), kx);
        vstd::seq_lib::lemma_multiset_commutative(keep(a, f) + kx, keep(b, f));
        vstd::seq_lib::lemma_multiset_commutative(keep(a, f), keep(b, f));
        vstd::seq_lib::lemma_multiset_commutative(keep(si, f), kx);
        assert(keep(s, f) == keep(si, f) + kx) by {
            if f(x) {
                assert(keep(si, f).push(x) =~= keep(si, f) + kx);
            } else {
                assert(keep(si, f) =~= keep(si, f) + kx);
            }
        }
        assert(keep(t, f).to_multiset() =~= keep(ti, f).to_multiset().add(kx.to_multiset()));
    }
}

/// The SQL row of outer group `h` is its output row.
pub proof fn lemma_full_row_top(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, h: int)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, true), 0 <= h < g.sum@.len(),
    ensures
        full_row(g_top(p0, c.p1), joined(db), kspec(c.sp, hkey(g, h, true), true)) == rr(c.sp, g, h),
        gkeys(g_top(p0, c.p1), joined(db)).contains(kspec(c.sp, hkey(g, h, true), true)),
{
    let kk = kspec(c.sp, hkey(g, h, true), true);
    assert(gsel(p0, c.p1, true) == g_top(p0, c.p1));
    lemma_group_acc(db, c, p0, l, g, true, h);
    lemma_keys_match(db, c, p0, l, g, true);
    assert(key_list(c.sp, g, true)[h] == kk);
    assert(key_list(c.sp, g, true)[h] == kk);
    assert(key_list(c.sp, g, true).contains(kk));
    assert(gkeys(gsel(p0, c.p1, true), joined(db)).contains(kk));
    assert(gkeys(g_top(p0, c.p1), joined(db)).contains(kk));
    lemma_gkeys(g_top(p0, c.p1), joined(db));
    assert(gcount(g_top(p0, c.p1), joined(db), kk) > 0);
    let outs = agg_outs(g_top(p0, c.p1), joined(db), kk);
    assert(outs.len() == 1);
    assert(outs[0] == Val::Num { coeff: g.sum@[h] as int, scale: 4 });
    assert(full_row(g_top(p0, c.p1), joined(db), kk) =~= rr(c.sp, g, h));
}

/// Writing a coefficient at its own scale keeps it.
pub proof fn lemma_align_same(a: int, sc: nat)
    ensures align(a, sc, sc) == a,
{
    assert((sc - sc) as nat == 0nat);
    assert(pow10(0) == 1);
    assert(a * 1 == a);
}

/// The rows sorted by decreasing sum are sorted by the ORDER BY key.
pub proof fn lemma_sorted_rows(sp: Seq<PartView>, g: Groups, s: Seq<SumRef>)
    requires
        sort_sorted(DescSumOrder {}, s),
        forall|q: int| 0 <= q < s.len() ==> (#[trigger] s[q]).idx < g.sum@.len() && s[q].sum == g.sum@[s[q].idx as int],
    ensures sorted_by(order_keys(), s.map_values(rr_of(sp, g))),
{
    let p = s.map_values(rr_of(sp, g));
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(order_keys(), #[trigger] p[i], #[trigger] p[j]) <= 0 by {
        assert(DescSumOrder {}.le(s[i], s[j]));
        let (a, b) = (s[i].sum as int, s[j].sum as int);
        assert(p[i][2] == Val::Num { coeff: a, scale: 4 });
        assert(p[j][2] == Val::Num { coeff: b, scale: 4 });
        lemma_align_same(a, 4);
        lemma_align_same(b, 4);
        assert(num_cmp(a, 4, b, 4) == sign(a - b));
        assert(p[i] == rr(sp, g, s[i].idx as int) && p[j] == rr(sp, g, s[j].idx as int));
        assert(p[i].len() == 3 && p[j].len() == 3);
        let k0 = order_keys()[0];
        assert(k0 == OrderKey { col: 2, desc: true, nulls_first: true });
        assert(compare(p[i][2], p[j][2]) == Some(num_cmp(a, 4, b, 4)));
        assert(key_cmp(k0, p[i], p[j]) == -sign(a - b));
        assert(order_keys().drop_first() =~= Seq::<OrderKey>::empty());
        assert(keys_cmp(order_keys().drop_first(), p[i], p[j]) == 0);
    }
}

/// Every outer group row is a three-column row with a numeric sum at scale 4.
proof fn lemma_group_row_shape(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, kk: Row)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, true), gkeys(g_top(p0, c.p1), joined(db)).contains(kk),
    ensures ({
        let r = full_row(g_top(p0, c.p1), joined(db), kk);
        &&& r.len() == 3
        &&& r[2] is Num
        &&& r[2]->Num_scale == 4
        &&& exists|h: int| 0 <= h < g.sum@.len() && #[trigger] rr(c.sp, g, h) == r
    }),
{
    assert(gsel(p0, c.p1, true) == g_top(p0, c.p1));
    lemma_keys_match(db, c, p0, l, g, true);
    assert(key_list(c.sp, g, true).contains(kk));
    let h = choose|h: int| 0 <= h < key_list(c.sp, g, true).len() && key_list(c.sp, g, true)[h] == kk;
    lemma_full_row_top(db, c, p0, l, g, h);
    assert(rr(c.sp, g, h)[2] == Val::Num { coeff: g.sum@[h] as int, scale: 4 });
}

/// The answer rows are an allowed output of the statement.
pub proof fn lemma_rows_answer(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, cg: Groups,
    total: int, ac: int, asc: nat, sorted: Seq<SumRef>, out: Seq<Row>)
    requires
        bound(db, c), run_ok(c, p0, l), groups_ok(g, l, true), groups_ok(cg, l, false),
        int_in_range(IntKind::Int4, c.p1),
        total == rsum(0, cg.sum@.len() as int, |h: int| cg.sum@[h] as int),
        -i128_max() <= total <= i128_max(),
        cg.sum@.len() > 0,
        num_div_fits(total, 4, cg.sum@.len() as int, 0),
        avg_of(total, 4, cg.sum@.len()) == (Val::Num { coeff: ac, scale: asc }),
        g.sum@.len() <= u64::MAX,
        sorted.to_multiset() == kept_upto(g, ac, asc, g.sum@.len() as int).to_multiset(),
        sort_sorted(DescSumOrder {}, sorted),
        out == slice_rows(sorted.map_values(rr_of(c.sp, g)), 0, Some(100nat)),
    ensures ordered_ok(db, query_spec_at(lits(p0, c.p1)), Ok::<Relation, SqlError>(out)),
{
    let p1 = c.p1;
    let ps = lits(p0, p1);
    let xs = joined(db);
    let gt = g_top(p0, p1);
    let ng = g.sum@.len() as int;
    lemma_query_shape(ps);
    lemma_sum_caps(db, c, p0, l, g, true);
    lemma_sum_caps(db, c, p0, l, cg, false);
    // The AVG subquery's value.
    let gc = g_cik(p0, p1);
    lemma_keys_multiset(db, c, p0, l, cg, false);
    let kl = key_list(c.sp, cg, false);
    lemma_ssum_perm(gkeys(gc, xs), kl, cik_sum_fn(p0, p1, xs));
    lemma_ssum_index(kl, cik_sum_fn(p0, p1, xs));
    assert forall|h: int| 0 <= h < kl.len() implies cik_sum_fn(p0, p1, xs)(#[trigger] kl[h]) == cg.sum@[h] as int by {
        lemma_group_acc(db, c, p0, l, cg, false, h);
    }
    lemma_rsum_ext(0, kl.len() as int, |h: int| cik_sum_fn(p0, p1, xs)(kl[h]), |h: int| cg.sum@[h] as int);
    assert(cik_total(p0, p1, xs) == total);
    assert forall|r: Row| r.len() == 3 implies #[trigger] eval_query(db, r, q_avg(ps))
        == Ok::<Relation, SqlError>(seq![seq![Val::Num { coeff: ac, scale: asc }]]) by {
        lemma_eval_avg(db, p0, p1, r);
    }
    // The body: HAVING over the outer groups.
    lemma_eval_group_top(db, p0, p1);
    let grows = gkeys(gt, xs).map_values(|k: Row| full_row(gt, xs, k));
    assert forall|i: int| 0 <= i < grows.len() implies (#[trigger] eval_pred(db, Seq::<Val>::empty() + grows[i], pred_having(ps))) is Ok
        && eval_pred(db, Seq::<Val>::empty() + grows[i], pred_having(ps))->Ok_0 is True == hv(ac, asc)(grows[i]) by {
        let kk = gkeys(gt, xs)[i];
        assert(gkeys(gt, xs).contains(kk));
        lemma_group_row_shape(db, c, p0, l, g, kk);
        lemma_having_row(db, p0, p1, grows[i], ac, asc);
    }
    crate::agent::nf::lemma_filter_iff(db, Seq::<Val>::empty(), pred_having(ps), q_group_top(ps), grows, hv(ac, asc));
    let body = keep(grows, hv(ac, asc));
    assert(denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(body));
    // The sorted rows are a permutation of the body.
    let gl = key_list(c.sp, g, true);
    lemma_keys_multiset(db, c, p0, l, g, true);
    lemma_map_multiset(gkeys(gt, xs), gl, |k: Row| full_row(gt, xs, k));
    let rs = Seq::new(ng as nat, |i: int| rr(c.sp, g, i));
    let gm = gl.map_values(|k: Row| full_row(gt, xs, k));
    assert forall|h: int| 0 <= h < ng implies #[trigger] gm[h] == rs[h] by {
        lemma_full_row_top(db, c, p0, l, g, h);
    }
    assert(gm =~= rs);
    lemma_keep_multiset(grows, rs, hv(ac, asc));
    lemma_kept_rows(c.sp, g, ac, asc, ng);
    let kept = kept_upto(g, ac, asc, ng);
    lemma_map_multiset(sorted, kept, rr_of(c.sp, g));
    let p = sorted.map_values(rr_of(c.sp, g));
    assert(p.to_multiset() == body.to_multiset());
    // Sorted by the ORDER BY key.
    assert forall|q: int| 0 <= q < sorted.len() implies (#[trigger] sorted[q]).idx < g.sum@.len()
        && sorted[q].sum == g.sum@[sorted[q].idx as int] by {
        assert(sorted.contains(sorted[q]));
        assert(sorted.to_multiset().count(sorted[q]) > 0);
        assert(kept.contains(sorted[q]));
    }
    lemma_sorted_rows(c.sp, g, sorted);
    assert(sorted_by(query_spec_at(ps).keys, p));
}

} // verus!
