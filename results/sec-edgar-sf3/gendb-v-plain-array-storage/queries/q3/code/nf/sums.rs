//! The group accumulators over the joined rows `num x sub`, decomposed by sub row: the SUM (COUNT) of a group is
//! the sum over the sub rows with `fy = $2` and that group key of their per-sub totals over num (`tsum`, `tcnt`: the
//! num rows with that adsh and `uom = $1`). This is the shape the scan computes (one total per qualifying sub). Also:
//! the sum of every group's SUM over the group keys is the SUM over all qualifying rows (`lemma_ksum_total`), used for
//! the AVG of the per-cik totals.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::*;
use crate::link::join::{sum_of, sum_term, count_term, lemma_acc_sum_of, lemma_sum_of_product_swap, lemma_sum_of_ext,
    lemma_sum_of_zero};
use crate::link::query::{QuerySpec, hit, gcount, gsum, gkeys, lemma_gkeys, lemma_zero_count, lemma_push};
use crate::agent::nf::fromwhere::*;
use crate::agent::nf::group::*;

verus! {

/// Num row `x` belongs to sub row `y` (same adsh) and has `uom = $1`.
pub open spec fn hitp(p0: Seq<u8>, x: Row, y: Row) -> bool {
    x[0] == y[0] && x[5] == Val::Text(p0)
}

/// Sub row `y` has `fy = $2`.
pub open spec fn fyok(p1: int, y: Row) -> bool {
    y[10] == Val::Int(p1)
}

/// Num row `x`'s contribution to the total of sub `y`.
pub open spec fn tsum_fn(p0: Seq<u8>, y: Row) -> spec_fn(Row) -> int {
    |x: Row| if hitp(p0, x, y) { coeff(x[7]) } else { 0 }
}

pub open spec fn tcnt_fn(p0: Seq<u8>, y: Row) -> spec_fn(Row) -> int {
    |x: Row| if hitp(p0, x, y) { 1int } else { 0int }
}

/// The per-sub total: the value coefficients of the num rows of sub `y` with `uom = $1`.
pub open spec fn tsum(nums: Seq<Row>, p0: Seq<u8>, y: Row) -> int {
    sum_of(nums, tsum_fn(p0, y))
}

/// The number of those num rows.
pub open spec fn tcnt(nums: Seq<Row>, p0: Seq<u8>, y: Row) -> int {
    sum_of(nums, tcnt_fn(p0, y))
}

/// Sub row `y`'s contribution to group `k`'s SUM (COUNT).
pub open spec fn gsum_fn(nums: Seq<Row>, p0: Seq<u8>, p1: int, skey: spec_fn(Row) -> Row, k: Row) -> spec_fn(Row) -> int {
    |y: Row| if fyok(p1, y) && skey(y) == k { tsum(nums, p0, y) } else { 0 }
}

pub open spec fn gcnt_fn(nums: Seq<Row>, p0: Seq<u8>, p1: int, skey: spec_fn(Row) -> Row, k: Row) -> spec_fn(Row) -> int {
    |y: Row| if fyok(p1, y) && skey(y) == k { tcnt(nums, p0, y) } else { 0 }
}

/// A group's SUM by sub row: the totals of the sub rows with `fy = $2` and key `k` (`skey` on sub rows).
pub open spec fn gsum_subs(subs: Seq<Row>, nums: Seq<Row>, p0: Seq<u8>, p1: int, skey: spec_fn(Row) -> Row, k: Row) -> int {
    sum_of(subs, gsum_fn(nums, p0, p1, skey, k))
}

/// A group's COUNT by sub row.
pub open spec fn gcnt_subs(subs: Seq<Row>, nums: Seq<Row>, p0: Seq<u8>, p1: int, skey: spec_fn(Row) -> Row, k: Row) -> int {
    sum_of(subs, gcnt_fn(nums, p0, p1, skey, k))
}

/// The outer group key `(name, cik)` of a joined row and of its sub row.
pub open spec fn okey(x: Row) -> Row {
    seq![x[11], x[10]]
}

pub open spec fn okey_sub(y: Row) -> Row {
    seq![y[2], y[1]]
}

/// The inner group key `cik`.
pub open spec fn ikey(x: Row) -> Row {
    seq![x[10]]
}

pub open spec fn ikey_sub(y: Row) -> Row {
    seq![y[1]]
}

/// The normal forms of the two GROUP BYs.
pub open spec fn g_out(p0: Seq<u8>, p1: int) -> QuerySpec {
    sum_spec(jq_fn(p0, p1), |x: Row| okey(x))
}

pub open spec fn g_in(p0: Seq<u8>, p1: int) -> QuerySpec {
    sum_spec(jq_fn(p0, p1), |x: Row| ikey(x))
}

/// One joined row's contribution, by its two parts.
proof fn lemma_term_parts(p0: Seq<u8>, p1: int, key: spec_fn(Row) -> Row, skey: spec_fn(Row) -> Row, k: Row, x: Row, y: Row)
    requires shape_num(x), shape_sub(y), key(x + y) == skey(y),
    ensures ({
        let g = sum_spec(jq_fn(p0, p1), key);
        &&& sum_term(g, k, 0)(x + y) == if fyok(p1, y) && skey(y) == k { if hitp(p0, x, y) { coeff(x[7]) } else { 0 } } else { 0 }
        &&& count_term(g, k)(x + y) == if fyok(p1, y) && skey(y) == k { if hitp(p0, x, y) { 1int } else { 0int } } else { 0 }
    }),
{
    lemma_joined_shape(x, y);
}

/// A group's SUM and COUNT over the joined rows are its SUM and COUNT by sub row.
pub proof fn lemma_group_by_subs(db: Database, p0: Seq<u8>, p1: int, key: spec_fn(Row) -> Row, skey: spec_fn(Row) -> Row, k: Row)
    requires
        tables_shaped(db),
        forall|x: Row, y: Row| shape_num(x) && shape_sub(y) ==> #[trigger] key(x + y) == skey(y),
    ensures ({
        let g = sum_spec(jq_fn(p0, p1), key);
        let (subs, nums) = (db.tables[0], db.tables[1]);
        &&& gsum(g, joined(db), k, 0) == gsum_subs(subs, nums, p0, p1, skey, k)
        &&& gcount(g, joined(db), k) == gcnt_subs(subs, nums, p0, p1, skey, k)
    }),
{
    let g = sum_spec(jq_fn(p0, p1), key);
    let (subs, nums) = (db.tables[0], db.tables[1]);
    let fs = sum_term(g, k, 0);
    let fc = count_term(g, k);
    lemma_acc_sum_of(g, joined(db), k, 0);
    lemma_sum_of_product_swap(nums, subs, fs);
    lemma_sum_of_product_swap(nums, subs, fc);
    let outer_s = |y: Row| sum_of(nums, |x: Row| fs(x + y));
    let outer_c = |y: Row| sum_of(nums, |x: Row| fc(x + y));
    let want_s = gsum_fn(nums, p0, p1, skey, k);
    let want_c = gcnt_fn(nums, p0, p1, skey, k);
    assert forall|j: int| 0 <= j < subs.len() implies outer_s(#[trigger] subs[j]) == want_s(subs[j])
        && outer_c(subs[j]) == want_c(subs[j]) by {
        let y = subs[j];
        assert(shape_sub(y));
        assert forall|i: int| 0 <= i < nums.len() implies
            (|x: Row| fs(x + y))(#[trigger] nums[i]) == (if fyok(p1, y) && skey(y) == k {
                tsum_fn(p0, y)(nums[i]) } else { 0 })
            && (|x: Row| fc(x + y))(nums[i]) == (if fyok(p1, y) && skey(y) == k {
                tcnt_fn(p0, y)(nums[i]) } else { 0 }) by {
            assert(shape_num(nums[i]));
            lemma_term_parts(p0, p1, key, skey, k, nums[i], y);
        }
        if fyok(p1, y) && skey(y) == k {
            lemma_sum_of_ext(nums, |x: Row| fs(x + y), tsum_fn(p0, y));
            lemma_sum_of_ext(nums, |x: Row| fc(x + y), tcnt_fn(p0, y));
        } else {
            lemma_sum_of_zero(nums, |x: Row| fs(x + y));
            lemma_sum_of_zero(nums, |x: Row| fc(x + y));
        }
    }
    lemma_sum_of_ext(subs, outer_s, want_s);
    lemma_sum_of_ext(subs, outer_c, want_c);
    assert(gsum(g, joined(db), k, 0) == sum_of(joined(db), fs));
    assert(sum_of(joined(db), fs) == sum_of(subs, outer_s));
    assert(sum_of(subs, want_s) == gsum_subs(subs, nums, p0, p1, skey, k));
    assert(gcount(g, joined(db), k) == sum_of(joined(db), fc));
    assert(sum_of(joined(db), fc) == sum_of(subs, outer_c));
    assert(sum_of(subs, want_c) == gcnt_subs(subs, nums, p0, p1, skey, k));
}

// ------------------------------------------------------------------------------------- sums over group key lists

/// The sum of the groups' SUMs over the key list `ks`.
pub open spec fn ksum(g: QuerySpec, xs: Seq<Row>, ks: Seq<Row>) -> int
    decreases ks.len(),
{
    if ks.len() == 0 { 0 } else { ksum(g, xs, ks.drop_last()) + gsum(g, xs, ks.last(), 0) }
}

/// The SUM over all qualifying rows.
pub open spec fn qsum(g: QuerySpec, xs: Seq<Row>) -> int
    decreases xs.len(),
{
    if xs.len() == 0 { 0 } else { qsum(g, xs.drop_last()) + if (g.qual)(xs.last()) { (g.arg)(0, xs.last()) } else { 0 } }
}

/// One more row: a duplicate-free key list's sum grows by the row's argument when it holds the row's key.
proof fn lemma_ksum_push(g: QuerySpec, xs: Seq<Row>, r: Row, ks: Seq<Row>)
    requires ks.no_duplicates(),
    ensures
        ksum(g, xs.push(r), ks) == ksum(g, xs, ks)
            + if (g.qual)(r) && ks.contains((g.key)(r)) { (g.arg)(0, r) } else { 0 },
    decreases ks.len(),
{
    if ks.len() > 0 {
        let k0 = ks.drop_last();
        assert(k0.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < b < k0.len() implies k0[a] != k0[b] by {
                assert(k0[a] == ks[a] && k0[b] == ks[b]);
            }
        }
        lemma_ksum_push(g, xs, r, k0);
        lemma_push(g, xs, r, ks.last(), 0);
        let kr = (g.key)(r);
        if k0.contains(kr) {
            let t = choose|t: int| 0 <= t < k0.len() && k0[t] == kr;
            assert(ks[t] == kr);
            assert(ks.last() == ks[ks.len() - 1]);
            assert(ks.last() != kr);
        }
        if ks.contains(kr) && !k0.contains(kr) {
            let t = choose|t: int| 0 <= t < ks.len() && ks[t] == kr;
            if t < ks.len() - 1 {
                assert(k0[t] == kr);
            }
            assert(ks.last() == kr);
        }
        if !ks.contains(kr) {
            if ks.last() == kr {
                assert(ks[ks.len() - 1] == kr);
            }
            if k0.contains(kr) {
                let t = choose|t: int| 0 <= t < k0.len() && k0[t] == kr;
                assert(ks[t] == kr);
            }
        }
    }
}

/// A key list's sum is unchanged when the added key's group is empty.
proof fn lemma_ksum_push_key(g: QuerySpec, xs: Seq<Row>, ks: Seq<Row>, k: Row)
    ensures ksum(g, xs, ks.push(k)) == ksum(g, xs, ks) + gsum(g, xs, k, 0),
{
    assert(ks.push(k).drop_last() =~= ks);
}

/// The sum of every group's SUM is the SUM over all qualifying rows.
pub proof fn lemma_ksum_total(g: QuerySpec, xs: Seq<Row>)
    ensures ksum(g, xs, gkeys(g, xs)) == qsum(g, xs),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let r = xs.last();
        assert(xi.push(r) =~= xs);
        lemma_ksum_total(g, xi);
        let ks = gkeys(g, xi);
        lemma_gkeys(g, xi);
        lemma_ksum_push(g, xi, r, ks);
        let kr = (g.key)(r);
        if (g.qual)(r) && !ks.contains(kr) {
            assert(gkeys(g, xs) == ks.push(kr));
            lemma_ksum_push_key(g, xs, ks, kr);
            assert(gcount(g, xi, kr) == 0);
            lemma_zero_count(g, xi, kr, 0);
            lemma_push(g, xi, r, kr, 0);
        } else {
            assert(gkeys(g, xs) == ks);
        }
    }
}

/// `num_sum` of scale-4 numerics is their coefficient sum at scale 4 (scale 0 when empty).
pub proof fn lemma_num_sum_scale4(vs: Seq<Val>, cs: Seq<int>)
    requires vs.len() == cs.len(), forall|t: int| 0 <= t < vs.len() ==> #[trigger] vs[t] == (Val::Num { coeff: cs[t], scale: 4 }),
    ensures num_sum(vs) == (csum(cs), if vs.len() == 0 { 0nat } else { 4nat }),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let (vi, ci) = (vs.drop_last(), cs.drop_last());
        assert forall|t: int| 0 <= t < vi.len() implies #[trigger] vi[t] == (Val::Num { coeff: ci[t], scale: 4 }) by {
            assert(vi[t] == vs[t] && ci[t] == cs[t]);
        }
        lemma_num_sum_scale4(vi, ci);
        assert(vs.last() == vs[vs.len() - 1]);
        assert(crate::spec::numeric::pow10(0) == 1);
        let acc = num_sum(vi);
        if vi.len() == 0 {
            assert(crate::spec::numeric::align(acc.0, acc.1, 4) == 0) by (nonlinear_arith)
                requires acc.0 == 0, crate::spec::numeric::align(acc.0, acc.1, 4) == acc.0 * crate::spec::numeric::pow10((4 - acc.1) as nat);
        } else {
            assert(crate::spec::numeric::align(acc.0, 4, 4) == acc.0) by {
                assert((4 - 4) as nat == 0nat);
            }
        }
        assert(crate::spec::numeric::align(cs.last(), 4, 4) == cs.last()) by {
            assert((4 - 4) as nat == 0nat);
        }
    }
}

/// The sum of a sequence of integers.
pub open spec fn csum(cs: Seq<int>) -> int
    decreases cs.len(),
{
    if cs.len() == 0 { 0 } else { csum(cs.drop_last()) + cs.last() }
}

/// `ksum` is `csum` of the groups' SUMs.
pub proof fn lemma_ksum_csum(g: QuerySpec, xs: Seq<Row>, ks: Seq<Row>)
    ensures ksum(g, xs, ks) == csum(ks.map_values(|k: Row| gsum(g, xs, k, 0))),
    decreases ks.len(),
{
    if ks.len() > 0 {
        lemma_ksum_csum(g, xs, ks.drop_last());
        assert(ks.map_values(|k: Row| gsum(g, xs, k, 0)).drop_last() =~= ks.drop_last().map_values(|k: Row| gsum(g, xs, k, 0)));
    }
}

} // verus!
