//! The general path: every stored lineitem row in the shipdate window joined with every stored part row (a nested
//! loop), exact in `i128` with an absolute-mass check. It assumes nothing of the layout beyond `represents` (no
//! dense keys, any group sizes and bases); the query runs it only when the fast path's conditions fail.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::join::sum_of;
use crate::gendb_entry::layout::PartView;
use crate::stores::custpart::interface::common::colfmt as cpc;
use crate::stores::custpart::interface::common::read as cpr;
use crate::stores::custpart::interface::{PA_GROUPS, PA_PARTKEY_BASE, PA_PARTKEY_CODES, PA_TYPE_BASE, PA_TYPE_CODES};
use crate::stores::facts::interface::common::colfmt::*;
use super::model::*;
use super::terms::*;
use super::kernel::*;

verus! {

/// The totals the answer needs: the promotion sum and the sum (scale 4), whether some joined row qualifies, and
/// whether some promotion row qualifies.
#[derive(Clone, Copy)]
pub struct Tot {
    pub psum: i128,
    pub sum: i128,
    pub any: bool,
    pub pany: bool,
}

/// `Tot` of all stored lineitem rows, inside the capacity bound of the SUM masses.
pub open spec fn tot_ok(t: Tot, fp: Seq<PartView>, cp: Seq<PartView>, w: Win) -> bool {
    let (lo, hi, n) = (w.lo as int, w.hi as int, n_li(fp));
    &&& t.psum == tot(fp, cp, 2, lo, hi, 0, n)
    &&& t.sum == tot(fp, cp, 3, lo, hi, 0, n)
    &&& t.any == (tot(fp, cp, 0, lo, hi, 0, n) > 0)
    &&& t.pany == (tot(fp, cp, 1, lo, hi, 0, n) > 0)
    &&& tot(fp, cp, 4, lo, hi, 0, n) <= i128::MAX
}

/// The sum of non-negative terms is non-negative and at least any prefix's.
pub proof fn lemma_sum_nonneg(rows: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) >= 0,
    ensures sum_of(rows, f) >= 0,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies f(#[trigger] d[i]) >= 0 by {
            assert(d[i] == rows[i]);
        }
        lemma_sum_nonneg(d, f);
    }
}

/// The terms of the count, the promotion count and the mass are non-negative, so are their inner sums.
pub proof fn lemma_inner_nonneg(cp: Seq<PartView>, k: int, lo: int, hi: int, a: Row)
    requires k == 0 || k == 1 || k == 4 || k == 5,
    ensures inner(cp, k, lo, hi)(a) >= 0,
{
    let f = |b: Row| term(k, lo, hi)(a + b);
    assert forall|i: int| 0 <= i < pa_rows(cp).len() implies f(#[trigger] pa_rows(cp)[i]) >= 0 by {
        let z = a + pa_rows(cp)[i];
        lemma_contrib_bounds(zq(lo, hi, z), zp(z), zv(z));
    }
    lemma_sum_nonneg(pa_rows(cp), f);
}

/// `tot` of a non-negative accumulator is non-negative.
pub proof fn lemma_tot_nonneg(fp: Seq<PartView>, cp: Seq<PartView>, k: int, lo: int, hi: int, a: int, b: int)
    requires k == 0 || k == 1 || k == 4 || k == 5, 0 <= a <= b <= n_li(fp),
    ensures tot(fp, cp, k, lo, hi, a, b) >= 0,
{
    let rows = li_rows(fp).subrange(a, b);
    assert forall|i: int| 0 <= i < rows.len() implies inner(cp, k, lo, hi)(#[trigger] rows[i]) >= 0 by {
        lemma_inner_nonneg(cp, k, lo, hi, rows[i]);
    }
    lemma_sum_nonneg(rows, inner(cp, k, lo, hi));
}

/// `|x| < A` and `|y| < B` bound the product by `A B`.
pub proof fn lemma_mul_bound(x: int, y: int, a: int, b: int)
    requires -a < x < a, -b < y < b, a > 0, b > 0,
    ensures -(a * b) < x * y < a * b,
{
    if x >= 0 && y >= 0 {
        assert(x * y < a * b) by (nonlinear_arith) requires 0 <= x < a, 0 <= y < b;
        assert(x * y >= 0) by (nonlinear_arith) requires x >= 0, y >= 0;
    } else if x < 0 && y < 0 {
        assert((-x) * (-y) < a * b) by (nonlinear_arith) requires 0 < -x < a, 0 < -y < b;
        assert(x * y == (-x) * (-y)) by (nonlinear_arith);
    } else if x < 0 {
        assert((-x) * y < a * b) by (nonlinear_arith) requires 0 < -x < a, 0 <= y < b;
        assert(x * y == -((-x) * y)) by (nonlinear_arith);
        assert((-x) * y >= 0) by (nonlinear_arith) requires -x > 0, y >= 0;
    } else {
        assert(x * (-y) < a * b) by (nonlinear_arith) requires 0 <= x < a, 0 < -y < b;
        assert(x * y == -(x * (-y))) by (nonlinear_arith);
        assert(x * (-y) >= 0) by (nonlinear_arith) requires x >= 0, -y > 0;
    }
}

/// The part row `j` decoded from its group's bases (any uniform block size).
pub proof fn lemma_part_row_vals(p: PaCols, cp: Seq<PartView>, j: int)
    requires
        pa_cols_ok(p, cp),
        0 <= j < p.n,
    ensures
        p.bsize >= 1,
        j / (p.bsize as int) < p.pk_base@.len(),
        j / (p.bsize as int) < p.ty_base@.len(),
        j < p.pk@.len(),
        j < p.ty@.len(),
        pkey_at(cp, j) == p.pk_base@[j / (p.bsize as int)] + p.pk@[j],
        tidx_at(cp, j) == p.ty_base@[j / (p.bsize as int)] + p.ty@[j],
        0 <= tidx_at(cp, j) < n_td(cp),
{
    let gp = cp[pp(PA_GROUPS)];
    let n = n_pa(cp);
    let bs = p.bsize as int;
    cpc::lemma_uniform_groups(gp, n, bs);
    cpc::lemma_nblocks(n, bs);
    cpr::lemma_div_lt(j, bs, cpc::nblocks_of(n, bs));
    cpr::lemma_for_row(gp, n, bs, cp[pp(PA_PARTKEY_BASE)], cp[pp(PA_PARTKEY_CODES)], j);
    cpr::lemma_for_row(gp, n, bs, cp[pp(PA_TYPE_BASE)], cp[pp(PA_TYPE_CODES)], j);
}

/// The inner sum of lineitem row `a` over the part rows `0 .. j`.
pub open spec fn inner_upto(cp: Seq<PartView>, k: int, lo: int, hi: int, a: Row, j: int) -> int {
    sum_of(pa_rows(cp).subrange(0, j), |b: Row| term(k, lo, hi)(a + b))
}

/// The partial accumulators of the general scan: rows `0 .. i` joined in full, row `i` joined with parts `0 .. j`.
pub open spec fn gen_ok(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, i: int, j: int, a: Row,
    psum: i128, sum: i128, mass: i128, any: bool, pany: bool) -> bool
{
    let (lo, hi) = (w.lo as int, w.hi as int);
    &&& psum == tot(fp, cp, 2, lo, hi, 0, i) + inner_upto(cp, 2, lo, hi, a, j)
    &&& sum == tot(fp, cp, 3, lo, hi, 0, i) + inner_upto(cp, 3, lo, hi, a, j)
    &&& mass == tot(fp, cp, 4, lo, hi, 0, i) + inner_upto(cp, 4, lo, hi, a, j)
    &&& any == (tot(fp, cp, 0, lo, hi, 0, i) + inner_upto(cp, 0, lo, hi, a, j) > 0)
    &&& pany == (tot(fp, cp, 1, lo, hi, 0, i) + inner_upto(cp, 1, lo, hi, a, j) > 0)
}

/// One part row more of the inner loop.
pub proof fn lemma_inner_step(cp: Seq<PartView>, k: int, lo: int, hi: int, a: Row, j: int)
    requires 0 <= j < n_pa(cp),
    ensures inner_upto(cp, k, lo, hi, a, j + 1) == inner_upto(cp, k, lo, hi, a, j) + term(k, lo, hi)(a + pa_rows(cp)[j]),
{
    lemma_sum_step(pa_rows(cp), |b: Row| term(k, lo, hi)(a + b), 0, j);
}

/// The complete inner loop is `inner`; the empty one is 0.
pub proof fn lemma_inner_ends(cp: Seq<PartView>, k: int, lo: int, hi: int, a: Row)
    ensures
        inner_upto(cp, k, lo, hi, a, n_pa(cp)) == inner(cp, k, lo, hi)(a),
        inner_upto(cp, k, lo, hi, a, 0) == 0,
{
    assert(pa_rows(cp).subrange(0, n_pa(cp)) =~= pa_rows(cp));
    assert(pa_rows(cp).subrange(0, 0).len() == 0);
}

/// The term of lineitem row `i` and part row `j` from their decoded values.
pub proof fn lemma_pair_term(fp: Seq<PartView>, cp: Seq<PartView>, k: int, lo: int, hi: int, i: int, j: int)
    requires 0 <= i < n_li(fp), 0 <= j < n_pa(cp),
    ensures
        term(k, lo, hi)(li_rows(fp)[i] + pa_rows(cp)[j]) == contrib(k,
            lpk_at(fp, i) == pkey_at(cp, j) && lo <= ship_at(fp, i) && ship_at(fp, i) < hi,
            promo_text(ptype_at(cp, j)), price_at(fp, i) * (100 - disc_at(fp, i))),
{
    lemma_li_row(fp, i);
    lemma_pa_row(cp, j);
    lemma_joined(li_rows(fp)[i], pa_rows(cp)[j]);
}

/// Totals of all stored lineitem rows by the nested loop; `None` when the absolute mass of the sum exceeds `i128`.
pub fn scan_general(c: &LiCols, p: &PaCols, promo: &Vec<bool>, w: Win,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>) -> (r: Option<Tot>)
    requires
        li_cols_ok(*c, fp),
        pa_cols_ok(*p, cp),
        promo_ok(promo@, cp),
    ensures
        r matches Some(t) ==> tot_ok(t, fp, cp, w),
        r is None ==> tot(fp, cp, 4, w.lo as int, w.hi as int, 0, n_li(fp)) > i128::MAX,
{
    let ghost (lo, hi) = (w.lo as int, w.hi as int);
    let ghost n = n_li(fp);
    let mut psum: i128 = 0;
    let mut sum: i128 = 0;
    let mut mass: i128 = 0;
    let mut any = false;
    let mut pany = false;
    proof {
        lemma_tot_empty(fp, cp, 0, lo, hi, 0);
        lemma_tot_empty(fp, cp, 1, lo, hi, 0);
        lemma_tot_empty(fp, cp, 2, lo, hi, 0);
        lemma_tot_empty(fp, cp, 3, lo, hi, 0);
        lemma_tot_empty(fp, cp, 4, lo, hi, 0);
    }
    let nd = promo.len();
    let mut g: usize = 0;
    while g < c.ng
        invariant
            nd == promo@.len(),
            li_cols_ok(*c, fp),
            pa_cols_ok(*p, cp),
            promo_ok(promo@, cp),
            g <= c.ng,
            lo == w.lo, hi == w.hi, n == n_li(fp),
            0 <= c.gs@[g as int] <= n,
            gen_ok(fp, cp, w, c.gs@[g as int] as int, 0, seq![], psum, sum, mass, any, pany),
            0 <= mass <= i128::MAX,
        decreases c.ng - g,
    {
        proof {
            lemma_groups_bounds(li_gs(fp), n, g + 1);
            lemma_groups_mono(li_gs(fp), n, g as int, g + 1);
        }
        let start = c.gs[g] as usize;
        let end = c.gs[g + 1] as usize;
        let sb = c.ship_base[g] as i128;
        let kb = c.pk_base[g] as i128;
        let pb = c.price_base[g] as i128;
        let db = c.disc_base[g] as i128;
        let mut i = start;
        while i < end
            invariant
                nd == promo@.len(),
                li_cols_ok(*c, fp),
                pa_cols_ok(*p, cp),
                promo_ok(promo@, cp),
                g < c.ng,
                lo == w.lo, hi == w.hi, n == n_li(fp),
                start == c.gs@[g as int], end == c.gs@[g + 1], start <= i <= end, end <= n,
                sb == c.ship_base@[g as int], kb == c.pk_base@[g as int],
                pb == c.price_base@[g as int], db == c.disc_base@[g as int],
                gen_ok(fp, cp, w, i as int, 0, seq![], psum, sum, mass, any, pany),
                0 <= mass <= i128::MAX,
            decreases end - i,
        {
            proof {
                lemma_li_vals(*c, fp, g as int, i as int);
                lemma_li_row(fp, i as int);
                lemma_inner_ends(cp, 0, lo, hi, seq![]);
                lemma_inner_ends(cp, 1, lo, hi, seq![]);
                lemma_inner_ends(cp, 2, lo, hi, seq![]);
                lemma_inner_ends(cp, 3, lo, hi, seq![]);
                lemma_inner_ends(cp, 4, lo, hi, seq![]);
            }
            let ghost a = li_rows(fp)[i as int];
            let s = sb + c.ship[i] as i128;
            let key = kb + c.pk[i] as i128;
            let price = pb + c.price[i] as i128;
            let disc = db + c.disc[i] as i128;
            proof {
                lemma_inner_ends(cp, 0, lo, hi, a);
                lemma_inner_ends(cp, 1, lo, hi, a);
                lemma_inner_ends(cp, 2, lo, hi, a);
                lemma_inner_ends(cp, 3, lo, hi, a);
                lemma_inner_ends(cp, 4, lo, hi, a);
            }
            if w.lo as i128 <= s && s < w.hi as i128 {
                proof {
                    assert(abs_lt(price_at(fp, i as int), p15()));
                    assert(abs_lt(disc_at(fp, i as int), p15()));
                    lemma_mul_bound(price as int, 100 - disc, 1_000_000_000_000_000, 2_000_000_000_000_000);
                    assert(1_000_000_000_000_000 * 2_000_000_000_000_000 == 2_000_000_000_000_000_000_000_000_000_000);
                }
                let v: i128 = price * (100 - disc);
                let av: i128 = if v < 0 { -v } else { v };
                let mut j: usize = 0;
                while j < p.n
                    invariant
                        li_cols_ok(*c, fp),
                        pa_cols_ok(*p, cp),
                        promo_ok(promo@, cp),
                        lo == w.lo, hi == w.hi, n == n_li(fp),
                        0 <= i < n,
                        a == li_rows(fp)[i as int],
                        key == lpk_at(fp, i as int),
                        lo <= ship_at(fp, i as int) < hi,
                        v == price_at(fp, i as int) * (100 - disc_at(fp, i as int)),
                        av == abs(v as int),
                        j <= p.n,
                        gen_ok(fp, cp, w, i as int, j as int, a, psum, sum, mass, any, pany),
                        0 <= mass <= i128::MAX,
                        -2_000_000_000_000_000_000_000_000_000_000 < v < 2_000_000_000_000_000_000_000_000_000_000,
                        nd == promo@.len(),
                    decreases p.n - j,
                {
                    proof {
                        lemma_part_row_vals(*p, cp, j as int);
                    }
                    let bj = (j as u64 / p.bsize) as usize;
                    let pk = p.pk_base[bj] as i128 + p.pk[j] as i128;
                    if pk == key {
                        proof {
                            assert(bj as int == j as int / (p.bsize as int));
                            assert(tidx_at(cp, j as int) == p.ty_base@[bj as int] + p.ty@[j as int]);
                        }
                        let idx = p.ty_base[bj] + p.ty[j] as u64;
                        let pr = promo[idx as usize];
                        proof {
                            assert(pr == promo_text(ptype_at(cp, j as int)));
                            lemma_pair_term(fp, cp, 0, lo, hi, i as int, j as int);
                            lemma_pair_term(fp, cp, 1, lo, hi, i as int, j as int);
                            lemma_pair_term(fp, cp, 2, lo, hi, i as int, j as int);
                            lemma_pair_term(fp, cp, 3, lo, hi, i as int, j as int);
                            lemma_pair_term(fp, cp, 4, lo, hi, i as int, j as int);
                            lemma_inner_step(cp, 0, lo, hi, a, j as int);
                            lemma_inner_step(cp, 1, lo, hi, a, j as int);
                            lemma_inner_step(cp, 2, lo, hi, a, j as int);
                            lemma_inner_step(cp, 3, lo, hi, a, j as int);
                            lemma_inner_step(cp, 4, lo, hi, a, j as int);
                            lemma_tot_nonneg(fp, cp, 0, lo, hi, 0, i as int);
                            lemma_tot_nonneg(fp, cp, 1, lo, hi, 0, i as int);
                            lemma_inner_upto_nonneg(cp, 0, lo, hi, a, j as int);
                            lemma_inner_upto_nonneg(cp, 1, lo, hi, a, j as int);
                            lemma_inner_upto_nonneg(cp, 4, lo, hi, a, j as int);
                            lemma_tot_nonneg(fp, cp, 4, lo, hi, 0, i as int);
                        }
                        if mass > i128::MAX - av {
                            proof {
                                lemma_mass_exceeds(fp, cp, w, i as int, a, j as int);
                            }
                            return None;
                        }
                        proof {
                            lemma_sum_bounds(fp, cp, w, i as int, a, j as int + 1);
                        }
                        mass = mass + av;
                        sum = sum + v;
                        any = true;
                        if pr {
                            psum = psum + v;
                            pany = true;
                        }
                    } else {
                        proof {
                            lemma_pair_term(fp, cp, 0, lo, hi, i as int, j as int);
                            lemma_pair_term(fp, cp, 1, lo, hi, i as int, j as int);
                            lemma_pair_term(fp, cp, 2, lo, hi, i as int, j as int);
                            lemma_pair_term(fp, cp, 3, lo, hi, i as int, j as int);
                            lemma_pair_term(fp, cp, 4, lo, hi, i as int, j as int);
                            lemma_inner_step(cp, 0, lo, hi, a, j as int);
                            lemma_inner_step(cp, 1, lo, hi, a, j as int);
                            lemma_inner_step(cp, 2, lo, hi, a, j as int);
                            lemma_inner_step(cp, 3, lo, hi, a, j as int);
                            lemma_inner_step(cp, 4, lo, hi, a, j as int);
                        }
                    }
                    j = j + 1;
                }
            } else {
                proof {
                    lemma_inner_out(cp, 0, lo, hi, a);
                    lemma_inner_out(cp, 1, lo, hi, a);
                    lemma_inner_out(cp, 2, lo, hi, a);
                    lemma_inner_out(cp, 3, lo, hi, a);
                    lemma_inner_out(cp, 4, lo, hi, a);
                }
            }
            proof {
                lemma_tot_step(fp, cp, 0, lo, hi, 0, i as int);
                lemma_tot_step(fp, cp, 1, lo, hi, 0, i as int);
                lemma_tot_step(fp, cp, 2, lo, hi, 0, i as int);
                lemma_tot_step(fp, cp, 3, lo, hi, 0, i as int);
                lemma_tot_step(fp, cp, 4, lo, hi, 0, i as int);
            }
            i = i + 1;
        }
        g = g + 1;
    }
    proof {
        assert(c.gs@[c.ng as int] == n);
        lemma_inner_ends(cp, 0, lo, hi, seq![]);
        lemma_inner_ends(cp, 1, lo, hi, seq![]);
        lemma_inner_ends(cp, 2, lo, hi, seq![]);
        lemma_inner_ends(cp, 3, lo, hi, seq![]);
        lemma_inner_ends(cp, 4, lo, hi, seq![]);
    }
    Some(Tot { psum, sum, any, pany })
}

/// A prefix of the inner loop of a non-negative accumulator is non-negative and at most the whole inner sum.
pub proof fn lemma_inner_upto_nonneg(cp: Seq<PartView>, k: int, lo: int, hi: int, a: Row, j: int)
    requires k == 0 || k == 1 || k == 4 || k == 5, 0 <= j <= n_pa(cp),
    ensures
        inner_upto(cp, k, lo, hi, a, j) >= 0,
        inner_upto(cp, k, lo, hi, a, j) <= inner(cp, k, lo, hi)(a),
{
    let bs = pa_rows(cp);
    let f = |b: Row| term(k, lo, hi)(a + b);
    assert forall|i: int| 0 <= i < bs.len() implies f(#[trigger] bs[i]) >= 0 by {
        let z = a + bs[i];
        lemma_contrib_bounds(zq(lo, hi, z), zp(z), zv(z));
    }
    let pre = bs.subrange(0, j);
    let post = bs.subrange(j, bs.len() as int);
    assert forall|i: int| 0 <= i < pre.len() implies f(#[trigger] pre[i]) >= 0 by {
        assert(pre[i] == bs[i]);
    }
    assert forall|i: int| 0 <= i < post.len() implies f(#[trigger] post[i]) >= 0 by {
        assert(post[i] == bs[i + j]);
    }
    lemma_sum_nonneg(pre, f);
    lemma_sum_nonneg(post, f);
    lemma_sum_split(bs, f, 0, j, bs.len() as int);
    assert(bs.subrange(0, bs.len() as int) =~= bs);
}

/// The mass of a joined prefix plus the next term exceeding `i128` makes the whole mass exceed it.
pub proof fn lemma_mass_exceeds(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, i: int, a: Row, j: int)
    requires
        0 <= i < n_li(fp),
        a == li_rows(fp)[i],
        0 <= j < n_pa(cp),
        tot(fp, cp, 4, w.lo as int, w.hi as int, 0, i) + inner_upto(cp, 4, w.lo as int, w.hi as int, a, j + 1) > i128::MAX,
    ensures
        tot(fp, cp, 4, w.lo as int, w.hi as int, 0, n_li(fp)) > i128::MAX,
{
    let (lo, hi) = (w.lo as int, w.hi as int);
    lemma_inner_upto_nonneg(cp, 4, lo, hi, a, j + 1);
    lemma_tot_step(fp, cp, 4, lo, hi, 0, i);
    lemma_tot_split(fp, cp, 4, lo, hi, 0, i + 1, n_li(fp));
    lemma_tot_nonneg(fp, cp, 4, lo, hi, i + 1, n_li(fp));
}

/// Within the mass bound, the sums of a joined prefix fit `i128`.
pub proof fn lemma_sum_bounds(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, i: int, a: Row, j: int)
    requires
        0 <= i < n_li(fp),
        0 <= j <= n_pa(cp),
    ensures
        ({
            let (lo, hi) = (w.lo as int, w.hi as int);
            let m = tot(fp, cp, 4, lo, hi, 0, i) + inner_upto(cp, 4, lo, hi, a, j);
            &&& -m <= tot(fp, cp, 2, lo, hi, 0, i) + inner_upto(cp, 2, lo, hi, a, j) <= m
            &&& -m <= tot(fp, cp, 3, lo, hi, 0, i) + inner_upto(cp, 3, lo, hi, a, j) <= m
        }),
{
    let (lo, hi) = (w.lo as int, w.hi as int);
    let bs = pa_rows(cp).subrange(0, j);
    lemma_terms_within(bs, a, 2, lo, hi);
    lemma_terms_within(bs, a, 3, lo, hi);
    assert forall|x: Row| -inner(cp, 4, lo, hi)(x) <= #[trigger] inner(cp, 2, lo, hi)(x) <= inner(cp, 4, lo, hi)(x) by {
        lemma_terms_within(pa_rows(cp), x, 2, lo, hi);
    }
    assert forall|x: Row| -inner(cp, 4, lo, hi)(x) <= #[trigger] inner(cp, 3, lo, hi)(x) <= inner(cp, 4, lo, hi)(x) by {
        lemma_terms_within(pa_rows(cp), x, 3, lo, hi);
    }
    lemma_sum_within(li_rows(fp).subrange(0, i), inner(cp, 2, lo, hi), inner(cp, 4, lo, hi));
    lemma_sum_within(li_rows(fp).subrange(0, i), inner(cp, 3, lo, hi), inner(cp, 4, lo, hi));
}

/// `|sum f| <= sum h` when `|f| <= h` termwise.
pub proof fn lemma_sum_within(rows: Seq<Row>, f: spec_fn(Row) -> int, h: spec_fn(Row) -> int)
    requires forall|x: Row| -h(x) <= #[trigger] f(x) <= h(x),
    ensures -sum_of(rows, h) <= sum_of(rows, f) <= sum_of(rows, h),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_sum_within(rows.drop_last(), f, h);
        assert(-h(rows.last()) <= f(rows.last()) <= h(rows.last()));
    }
}

/// The sums of a part prefix are within its mass (accumulator 2 or 3 against 4).
pub proof fn lemma_terms_within(bs: Seq<Row>, a: Row, k: int, lo: int, hi: int)
    requires k == 2 || k == 3,
    ensures
        -sum_of(bs, |b: Row| term(4, lo, hi)(a + b)) <= sum_of(bs, |b: Row| term(k, lo, hi)(a + b))
            <= sum_of(bs, |b: Row| term(4, lo, hi)(a + b)),
{
    let f = |b: Row| term(k, lo, hi)(a + b);
    let h = |b: Row| term(4, lo, hi)(a + b);
    assert forall|b: Row| -h(b) <= #[trigger] f(b) <= h(b) by {
        let z = a + b;
        lemma_contrib_bounds(zq(lo, hi, z), zp(z), zv(z));
    }
    lemma_sum_within(bs, f, h);
}

} // verus!
