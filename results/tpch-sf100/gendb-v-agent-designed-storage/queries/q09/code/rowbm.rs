//! The row bitmap and the payloads of one destination chunk (phase 2 of the directory path). A scan task works
//! through its rows chunk by chunk (`shuffle::CH` rows, chunk `h` = rows `[h * CH, min((h + 1) * CH, l_n))`); for
//! each it fills a bitmap whose bit `j - lo` is set exactly when row `j` matches (`bm_ok`, `fill_chunk`) from the
//! chunk's segment of every shuffle result (`shuffle::res_ok`: their part ranges cover every part row), then places
//! every row's payload at the row's rank among the set bits (`common::bmrank::nbelow`; `chunk_pay_ok`,
//! `scatter_chunk`), so that the `i`-th listed row of the chunk finds its payload at index `i`. `collect_bm` lists the
//! matching rows of one block in increasing order (`scan::list_ok`) from the bitmap words.
use vstd::prelude::*;
use crate::gendb_entry::work::put;
use super::model::*;
use super::qspec::*;
use super::scan::{pm, list_ok, BLOCK};
use super::shuffle::{ShufOut, PA, pay_ok, res_ok, res_one_ok, rin, placed, dt, nchunks, segs_wf, segs_order, lemma_st_mono, CH};
use super::common::bitlist::*;
use super::common::bmrank::*;

verus! {

/// Rows `[lo, hi)` are destination chunk `h`.
pub open spec fn chunk_rows(m: M, h: int, lo: int, hi: int) -> bool {
    &&& 0 <= h < nchunks(m.l_n)
    &&& lo == h * CH as int
    &&& hi == if (h + 1) * CH as int <= m.l_n { (h + 1) * CH as int } else { m.l_n }
}

/// Bit `k` is set exactly when row `lo + k` is a matching row of `[lo, hi)`.
pub open spec fn bm_ok(bm: Seq<u64>, m: M, p: QP, lo: int, hi: int) -> bool {
    &&& bm.len() * 64 >= hi - lo
    &&& forall|k: int| 0 <= k < bm.len() * 64 ==> (#[trigger] wbit(bm, k) <==> (k < hi - lo && pm(m, p, lo + k)))
}

/// The payload of matching row `j` of the chunk from `lo` sits at the row's rank among the set bits.
pub open spec fn pl_at(pl: Seq<u32>, bm: Seq<u64>, m: M, a: PA, lo: int, j: int) -> bool {
    &&& nbelow(bm, j - lo) < pl.len()
    &&& pay_ok(pl[nbelow(bm, j - lo) as int], a, lc(m, j))
}

/// Every matching row of the chunk `[lo, hi)` has its payload at its rank.
pub open spec fn chunk_pay_ok(pl: Seq<u32>, bm: Seq<u64>, m: M, a: PA, lo: int, hi: int) -> bool {
    forall|k: int| 0 <= k < hi - lo && #[trigger] wbit(bm, k) ==> pl_at(pl, bm, m, a, lo, lo + k)
}

/// A row of chunk `h` lies in the chunk's rows.
proof fn lemma_in_chunk(m: M, h: int, lo: int, hi: int, j: int)
    requires chunk_rows(m, h, lo, hi), 0 <= j < m.l_n, dt(j) == h,
    ensures lo <= j < hi,
{
    assert(h * 262144 <= j < (h + 1) * 262144) by (nonlinear_arith) requires h == j / 262144, j >= 0;
}

/// A matching row of the chunk lies in the chunk's segment of every result holding its part row.
proof fn lemma_find_res(rs: Seq<ShufOut>, m: M, c: int, s: int) -> (r: int)
    requires
        rs.len() >= 1, rs[rs.len() - 1].c_hi@ >= m.p_n,
        forall|t: int| 0 <= t < rs.len() - 1 ==> #[trigger] rs[t].c_hi@ == rs[t + 1].c_lo@,
        0 <= s < rs.len(), rs[s].c_lo@ <= c < m.p_n,
    ensures 0 <= r < rs.len(), rs[r].c_lo@ <= c < rs[r].c_hi@,
    decreases rs.len() - s,
{
    if c < rs[s].c_hi@ {
        s
    } else {
        assert(s < rs.len() - 1);
        assert(rs[s].c_hi@ == rs[s + 1].c_lo@);
        lemma_find_res(rs, m, c, s + 1)
    }
}

/// The bounds of segment `h` of a result inside its buffers.
proof fn lemma_seg_bounds(o: ShufOut, m: M, p: QP, a: PA, h: int)
    requires res_one_ok(o, m, p, a), 0 <= h < nchunks(m.l_n),
    ensures o.st@[h] <= o.cur@[h] <= o.buf@.len(), o.pay@.len() == o.buf@.len(), o.st@.len() == nchunks(m.l_n) + 1,
        o.cur@.len() == nchunks(m.l_n),
{
    let nd = nchunks(m.l_n);
    assert(segs_wf(o.buf@, o.pay@, o.st@, o.cur@, nd));
    assert(segs_order(o.st@, o.cur@, nd));
    assert(forall|u: int| 0 <= u < nd ==> #[trigger] o.st@[u] <= o.cur@[u] && o.cur@[u] <= o.st@[u + 1]);
    assert(0 <= h < nd);
    let x = o.st@[h];
    assert(x <= o.cur@[h]);
    assert(o.cur@[h] <= o.st@[h + 1]);
    lemma_st_mono(o.st@, o.cur@, nd, h + 1, nd);
}

/// Setting bit `k` sets exactly that bit.
proof fn lemma_set(b0: Seq<u64>, b1: Seq<u64>, k: int)
    requires 0 <= k < b0.len() * 64, b1 == b0.update(k / 64, b0[k / 64] | (1u64 << ((k % 64) as u64))),
    ensures forall|k2: int| 0 <= k2 < b0.len() * 64 ==> (#[trigger] wbit(b1, k2) <==> (wbit(b0, k2) || k2 == k)),
{
    assert forall|k2: int| 0 <= k2 < b0.len() * 64 implies (#[trigger] wbit(b1, k2) <==> (wbit(b0, k2) || k2 == k)) by {
        assert(0 <= k2 / 64 < b0.len()) by (nonlinear_arith) requires 0 <= k2 < b0.len() * 64;
        if k2 / 64 == k / 64 {
            let c = (k % 64) as u64;
            let b = (k2 % 64) as u64;
            let w0 = b0[k / 64];
            assert(((w0 | (1u64 << c)) >> b) & 1u64 == if b == c { 1u64 } else { (w0 >> b) & 1u64 }) by (bit_vector)
                requires c < 64, b < 64;
            assert((k2 == k) == (b == c)) by {
                assert(k == (k / 64) * 64 + k % 64 && k2 == (k2 / 64) * 64 + k2 % 64) by (nonlinear_arith) requires 0 <= k, 0 <= k2;
            }
        } else {
            assert(k2 != k);
        }
    }
}

/// The bitmap of the matching rows of chunk `h` = rows `[lo, hi)` from every result's segment (`bm` all zero on
/// entry).
pub fn fill_chunk(rs: &Vec<ShufOut>, h: usize, bm: &mut Vec<u64>, lo: usize, hi: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(a): Ghost<PA>)
    requires
        res_ok(rs@, m, p, a),
        chunk_rows(m, h as int, lo as int, hi as int),
        old(bm)@.len() * 64 >= hi - lo,
        forall|k: int| 0 <= k < old(bm)@.len() ==> #[trigger] old(bm)@[k] == 0u64,
    ensures
        final(bm)@.len() == old(bm)@.len(),
        bm_ok(final(bm)@, m, p, lo as int, hi as int),
    no_unwind
{
    let ghost nw = bm@.len();
    proof {
        assert forall|k: int| 0 <= k < nw * 64 implies !#[trigger] wbit(bm@, k) by {
            assert(0 <= k / 64 < nw) by (nonlinear_arith) requires 0 <= k < nw * 64;
            let b = (k % 64) as u64;
            assert((0u64 >> b) & 1u64 == 0u64) by (bit_vector);
        }
    }
    let ns = rs.len();
    let mut s: usize = 0;
    while s < ns
        invariant
            res_ok(rs@, m, p, a), chunk_rows(m, h as int, lo as int, hi as int), ns == rs@.len(),
            bm@.len() == nw, nw * 64 >= hi - lo,
            s <= ns,
            forall|k: int| 0 <= k < nw * 64 && #[trigger] wbit(bm@, k) ==> k < hi - lo && pm(m, p, lo + k),
            forall|t: int, x: int| 0 <= t < s && rs@[t].st@[h as int] <= x < rs@[t].cur@[h as int] ==>
                #[trigger] wbit(bm@, rs@[t].buf@[x] - lo),
        decreases ns - s,
    {
        let o = &rs[s];
        proof {
            assert(res_one_ok(rs@[s as int], m, p, a));
            lemma_seg_bounds(rs@[s as int], m, p, a, h as int);
        }
        let b_end = o.cur[h];
        let mut x = o.st[h];
        while x < b_end
            invariant
                res_ok(rs@, m, p, a), chunk_rows(m, h as int, lo as int, hi as int), ns == rs@.len(), s < ns,
                *o == rs@[s as int], res_one_ok(*o, m, p, a),
                o.st@[h as int] <= x <= b_end, b_end == o.cur@[h as int], b_end <= o.buf@.len(),
                bm@.len() == nw, nw * 64 >= hi - lo,
                forall|k: int| 0 <= k < nw * 64 && #[trigger] wbit(bm@, k) ==> k < hi - lo && pm(m, p, lo + k),
                forall|t: int, y: int| 0 <= t < s && rs@[t].st@[h as int] <= y < rs@[t].cur@[h as int] ==>
                    #[trigger] wbit(bm@, rs@[t].buf@[y] - lo),
                forall|y: int| o.st@[h as int] <= y < x ==> #[trigger] wbit(bm@, o.buf@[y] - lo),
            decreases b_end - x,
        {
            let j = o.buf[x] as usize;
            proof {
                assert(rin(m, p, a, o.buf@[x as int], o.pay@[x as int], h as int));
                reveal(rin);
                lemma_in_chunk(m, h as int, lo as int, hi as int, j as int);
            }
            let k = j - lo;
            proof {
                assert(k / 64 < nw) by (nonlinear_arith) requires k < hi - lo, hi - lo <= nw * 64;
            }
            let w = bm[k / 64] | (1u64 << ((k % 64) as u64));
            let ghost b0 = bm@;
            put(bm, k / 64, w);
            proof {
                lemma_set(b0, bm@, k as int);
                assert(wbit(bm@, k as int));
                assert forall|t: int, y: int| 0 <= t < s && rs@[t].st@[h as int] <= y < rs@[t].cur@[h as int] implies
                    #[trigger] wbit(bm@, rs@[t].buf@[y] - lo) by {
                    assert(wbit(b0, rs@[t].buf@[y] - lo));
                    assert(res_one_ok(rs@[t], m, p, a));
                    assert(rin(m, p, a, rs@[t].buf@[y], rs@[t].pay@[y], h as int));
                    reveal(rin);
                    lemma_in_chunk(m, h as int, lo as int, hi as int, rs@[t].buf@[y] as int);
                }
                assert forall|y: int| o.st@[h as int] <= y < x + 1 implies #[trigger] wbit(bm@, o.buf@[y] - lo) by {
                    if y < x {
                        assert(wbit(b0, o.buf@[y] - lo));
                        assert(rin(m, p, a, o.buf@[y], o.pay@[y], h as int));
                        reveal(rin);
                        lemma_in_chunk(m, h as int, lo as int, hi as int, o.buf@[y] as int);
                    }
                }
            }
            x = x + 1;
        }
        s = s + 1;
    }
    proof {
        assert forall|k: int| 0 <= k < nw * 64 implies (#[trigger] wbit(bm@, k) <==> (k < hi - lo && pm(m, p, lo + k))) by {
            if k < hi - lo && pm(m, p, lo + k) {
                let j = lo + k;
                assert(lc(m, j) < m.p_n);
                let s0 = lemma_find_res(rs@, m, lc(m, j), 0);
                assert(res_one_ok(rs@[s0], m, p, a));
                assert(placed(rs@[s0].buf@, rs@[s0].st@, rs@[s0].cur@, j));
                assert(dt(j) == h) by (nonlinear_arith) requires j == lo + k, lo == h * 262144, 0 <= k < 262144;
                let x = choose|x: int| rs@[s0].st@[dt(j)] <= x < rs@[s0].cur@[dt(j)] && rs@[s0].buf@[x] as int == j;
                assert(wbit(bm@, rs@[s0].buf@[x] - lo));
            }
        }
    }
}

/// Every matching row's payload of chunk `h` = rows `[lo, hi)`, at the row's rank among the set bits of `bm`.
pub fn scatter_chunk(rs: &Vec<ShufOut>, h: usize, bm: &Vec<u64>, wp: &Vec<u32>, nw: usize, pl: &mut Vec<u32>, lo: usize, hi: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(a): Ghost<PA>)
    requires
        res_ok(rs@, m, p, a),
        chunk_rows(m, h as int, lo as int, hi as int),
        bm_ok(bm@, m, p, lo as int, hi as int),
        prefix_ok(bm@, wp@, nw as int), nw * 64 >= hi - lo,
        old(pl)@.len() >= wp@[nw as int],
    ensures
        final(pl)@.len() == old(pl)@.len(),
        chunk_pay_ok(final(pl)@, bm@, m, a, lo as int, hi as int),
    no_unwind
{
    let ns = rs.len();
    let mut s: usize = 0;
    while s < ns
        invariant
            res_ok(rs@, m, p, a), chunk_rows(m, h as int, lo as int, hi as int), ns == rs@.len(),
            bm_ok(bm@, m, p, lo as int, hi as int), prefix_ok(bm@, wp@, nw as int), nw * 64 >= hi - lo,
            pl@.len() == old(pl)@.len(), pl@.len() >= wp@[nw as int],
            s <= ns,
            forall|t: int, x: int| 0 <= t < s && rs@[t].st@[h as int] <= x < rs@[t].cur@[h as int] ==>
                #[trigger] pl_at(pl@, bm@, m, a, lo as int, rs@[t].buf@[x] as int),
        decreases ns - s,
    {
        let o = &rs[s];
        proof {
            assert(res_one_ok(rs@[s as int], m, p, a));
            lemma_seg_bounds(rs@[s as int], m, p, a, h as int);
        }
        let b_end = o.cur[h];
        let mut x = o.st[h];
        while x < b_end
            invariant
                res_ok(rs@, m, p, a), chunk_rows(m, h as int, lo as int, hi as int), ns == rs@.len(), s < ns,
                bm_ok(bm@, m, p, lo as int, hi as int), prefix_ok(bm@, wp@, nw as int), nw * 64 >= hi - lo,
                *o == rs@[s as int], res_one_ok(*o, m, p, a),
                o.st@[h as int] <= x <= b_end, b_end == o.cur@[h as int], b_end <= o.buf@.len(),
                pl@.len() == old(pl)@.len(), pl@.len() >= wp@[nw as int],
                forall|t: int, y: int| 0 <= t < s && rs@[t].st@[h as int] <= y < rs@[t].cur@[h as int] ==>
                    #[trigger] pl_at(pl@, bm@, m, a, lo as int, rs@[t].buf@[y] as int),
                forall|y: int| o.st@[h as int] <= y < x ==> #[trigger] pl_at(pl@, bm@, m, a, lo as int, o.buf@[y] as int),
            decreases b_end - x,
        {
            let j = o.buf[x] as usize;
            let e = o.pay[x];
            proof {
                assert(rin(m, p, a, o.buf@[x as int], o.pay@[x as int], h as int));
                reveal(rin);
                lemma_in_chunk(m, h as int, lo as int, hi as int, j as int);
            }
            let k = j - lo;
            let pos = rank_at(bm, wp, k, Ghost(nw as int));
            proof {
                assert(wbit(bm@, k as int));
                lemma_nbelow_lt(bm@, k as int, nw * 64);
            }
            let ghost l0 = pl@;
            put(pl, pos, e);
            proof {
                // an earlier entry keeps its payload: another row has another rank
                assert forall|j2: int| lo <= j2 < hi && #[trigger] pl_at(l0, bm@, m, a, lo as int, j2) && pm(m, p, j2) implies
                    pl_at(pl@, bm@, m, a, lo as int, j2) by {
                    if j2 != j {
                        let k2 = j2 - lo;
                        assert(wbit(bm@, k2));
                        if k2 < k { lemma_nbelow_lt(bm@, k2, k as int); } else { lemma_nbelow_lt(bm@, k as int, k2); }
                    }
                }
                assert(pl_at(pl@, bm@, m, a, lo as int, j as int));
                assert forall|t: int, y: int| 0 <= t < s && rs@[t].st@[h as int] <= y < rs@[t].cur@[h as int] implies
                    #[trigger] pl_at(pl@, bm@, m, a, lo as int, rs@[t].buf@[y] as int) by {
                    assert(res_one_ok(rs@[t], m, p, a));
                    assert(rin(m, p, a, rs@[t].buf@[y], rs@[t].pay@[y], h as int));
                    reveal(rin);
                    lemma_in_chunk(m, h as int, lo as int, hi as int, rs@[t].buf@[y] as int);
                    assert(pl_at(l0, bm@, m, a, lo as int, rs@[t].buf@[y] as int));
                }
                assert forall|y: int| o.st@[h as int] <= y < x + 1 implies #[trigger] pl_at(pl@, bm@, m, a, lo as int, o.buf@[y] as int) by {
                    if y < x {
                        assert(rin(m, p, a, o.buf@[y], o.pay@[y], h as int));
                        reveal(rin);
                        lemma_in_chunk(m, h as int, lo as int, hi as int, o.buf@[y] as int);
                        assert(pl_at(l0, bm@, m, a, lo as int, o.buf@[y] as int));
                    }
                }
            }
            x = x + 1;
        }
        s = s + 1;
    }
    proof {
        assert forall|k: int| 0 <= k < hi - lo && #[trigger] wbit(bm@, k) implies pl_at(pl@, bm@, m, a, lo as int, lo + k) by {
            let j = lo + k;
            assert(k < bm@.len() * 64);
            assert(pm(m, p, j));
            assert(lc(m, j) < m.p_n);
            let s0 = lemma_find_res(rs@, m, lc(m, j), 0);
            assert(res_one_ok(rs@[s0], m, p, a));
            assert(0 <= j < m.l_n);
            assert(placed(rs@[s0].buf@, rs@[s0].st@, rs@[s0].cur@, j));
            assert(dt(j) == h) by (nonlinear_arith) requires j == lo + k, lo == h * 262144, 0 <= k < 262144;
            let x = choose|x: int| rs@[s0].st@[dt(j)] <= x < rs@[s0].cur@[dt(j)] && rs@[s0].buf@[x] as int == j;
            assert(pl_at(pl@, bm@, m, a, lo as int, rs@[s0].buf@[x] as int));
        }
    }
}

/// The matching rows of block `[blo, bhi)` of the task's rows `[lo, hi)`, from the bitmap, in increasing order.
pub fn collect_bm(bm: &Vec<u64>, lo: usize, hi: usize, blo: usize, bhi: usize, qj: &mut Vec<usize>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (nq: usize)
    requires
        bm_ok(bm@, m, p, lo as int, hi as int),
        lo <= blo < bhi <= hi, hi + 64 <= usize::MAX,
        (blo - lo) % 64 == 0,
        bhi == hi || (bhi - lo) % 64 == 0,
        bhi - blo <= BLOCK,
        old(qj)@.len() == BLOCK + 1,
    ensures
        final(qj)@.len() == BLOCK + 1,
        nq <= BLOCK,
        list_ok(m, p, final(qj)@, nq as int, blo as int, bhi as int),
    no_unwind
{
    let k_lo = blo - lo;
    let k_hi = bhi - lo;
    proof {
        if k_hi % 64 != 0 {
            assert(bhi == hi);
            assert forall|k: int| k_hi <= k < (k_hi / 64 + 1) * 64 implies !#[trigger] wbit(bm@, k) by {
                if k < bm@.len() * 64 {
                    assert(!(k < hi - lo));
                } else {
                    assert(false) by (nonlinear_arith) requires k_hi <= bm@.len() * 64, k_hi % 64 != 0, k < (k_hi / 64 + 1) * 64, k >= bm@.len() * 64;
                }
            }
        }
    }
    let nq = set_bits(bm, k_lo, k_hi, lo, qj);
    proof {
        let q = qj@;
        assert forall|i: int| 0 <= i < nq implies blo <= #[trigger] q[i] < bhi && pm(m, p, q[i] as int) by {
            assert(k_lo <= q[i] - lo < k_hi && wbit(bm@, q[i] - lo));
        }
        assert forall|j: int| blo <= j < bhi && #[trigger] pm(m, p, j) implies exists|i: int| 0 <= i < nq && q[i] == j by {
            assert(wbit(bm@, j - lo));
            let i = choose|i: int| 0 <= i < nq && q[i] == lo + (j - lo);
        }
        assert forall|i: int, k: int| 0 <= i < k < nq implies #[trigger] q[i] < #[trigger] q[k] by {}
    }
    nq
}

} // verus!
