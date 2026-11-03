//! The lineitem-driven scan of one chunk on the co-clustered layout. The chunk's lineitem rows `[l_lo, l_hi)` are
//! exactly the rows of its orders `[o_lo, o_hi)` (`kernel::lb_ok` at both ends), and the rows of one order are one
//! run of equal l_orderkey. The scan walks the rows once, block by block (bases hoisted), keeping the current run's
//! start `s`, key `ck` and quantity sum; a row of another key ends the run (branch-free: the reset is a select).
//! Only a finished run whose sum is above `$1` takes a branch (`take_run`): its order is found by key (the orders
//! key index), its customer checked, and its row inserted into the top 100.
//!
//! Proof: the current run's order position `lpos(s)` is ghost; the buffer is the top 100 of the groups of the
//! orders before it (`gseq(o_lo, lpos(s))`). A finished run `[s, j)` holds every row of its key (`lemma_run_end`),
//! so its sum is the key's sum, and the orders between it and the next run have no lineitem (not groups).
//!
//! With the run directory of storage `liruns` (`scan_runs`), the chunk walks its runs instead of its rows: a run of
//! `len` rows whose `len * qm` (`qm` bounds every l_quantity, from the zone map) is not above `$1` cannot be a group
//! (`lemma_run_bound`) and is skipped without reading its rows; only the other runs are summed (`run_sum`). The
//! runs are maximal (`runs_ok`: one key per run, different keys across run starts), so each is a finished run of
//! `lemma_run_end`.
//!
//! With the run permutation by length (`scan_long`, when no run shorter than the longest length `lg_max` can be above
//! `$1`), the chunk visits only the runs of length `lg_max` it contains, in run order: their run indices and start
//! rows are a range of the permutation's first class (found by `lower_bound`). The runs between two visited runs are
//! shorter (`lemma_gap`: a run of length `lg_max` is listed, and the list is increasing), so they are skipped as in
//! `scan_runs` (`lemma_skip_range`) without reading even their lengths.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::pow10;
use super::common::isum::*;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::cand::*;
use super::kernel::*;
use super::plan::find_order_guess;
use super::answer::lemma_gseq_wf;
use crate::stores::liruns::interface as fi;

verus! {

/// The chunk: orders `[o_lo, o_hi)` with lineitem rows `[l_lo, l_hi)` on the co-clustered layout.
pub open spec fn chunk_ok(m: M, o_lo: int, o_hi: int, l_lo: int, l_hi: int) -> bool {
    &&& model_ok(m)
    &&& m.cluster == 1
    &&& 0 <= o_lo <= o_hi <= m.o_n
    &&& 0 <= l_lo <= l_hi <= m.l_n
    &&& lb_ok(m, o_lo, l_lo)
    &&& lb_ok(m, o_hi, l_hi)
}

/// `[s, j)` is a run of key `ck` inside the chunk, maximal on the left.
pub open spec fn run_ok(m: M, l_lo: int, s: int, j: int, ck: int) -> bool {
    &&& l_lo <= s < j
    &&& forall|t: int| s <= t < j ==> #[trigger] lkey(m, t) == ck
    &&& (s == l_lo || lkey(m, s - 1) != ck)
}

/// A row inside the chunk belongs to an order of the chunk.
proof fn lemma_row_pos(m: M, o_lo: int, o_hi: int, l_lo: int, l_hi: int, t: int)
    requires chunk_ok(m, o_lo, o_hi, l_lo, l_hi), l_lo <= t < l_hi,
    ensures o_lo <= lpos(m, t) < o_hi, okey(m, lpos(m, t)) == lkey(m, t),
{
    crate::agent::facts::lemma_opos(m, lkey(m, t));
}

/// An order with no lineitem row is not a group.
proof fn lemma_no_rows(m: M, p: QP, q: int)
    requires model_ok(m), 0 <= q < m.o_n, forall|t: int| 0 <= t < m.l_n ==> #[trigger] lpos(m, t) != q,
    ensures !good(m, p, q),
{
    assert forall|t: int| 0 <= t < m.l_n implies #[trigger] kcnt_f(m, okey(m, q))(t) == 0 by {
        lemma_lpos_key(m, q, t);
    }
    lemma_isum_zero(m.l_n, kcnt_f(m, okey(m, q)));
}

/// The groups of the orders before the chunk's first run: none (those orders have no lineitem).
pub proof fn lemma_scan_start(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int)
    requires chunk_ok(m, o_lo, o_hi, l_lo, l_hi), l_lo < l_hi,
    ensures gseq(m, p, o_lo, lpos(m, l_lo)) == Seq::<Row>::empty(), o_lo <= lpos(m, l_lo) < o_hi,
{
    lemma_row_pos(m, o_lo, o_hi, l_lo, l_hi, l_lo);
    assert forall|q: int| o_lo <= q < lpos(m, l_lo) implies !#[trigger] good(m, p, q) by {
        assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lpos(m, t) != q by {
            if t >= l_lo {
                lemma_lpos_mono(m, l_lo, t);
            }
        }
        lemma_no_rows(m, p, q);
    }
    lemma_gseq_none(m, p, o_lo, lpos(m, l_lo));
}

/// An empty chunk has no groups.
pub proof fn lemma_scan_empty(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int)
    requires chunk_ok(m, o_lo, o_hi, l_lo, l_hi), l_lo == l_hi,
    ensures gseq(m, p, o_lo, o_hi) == Seq::<Row>::empty(),
{
    assert forall|q: int| o_lo <= q < o_hi implies !#[trigger] good(m, p, q) by {
        assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lpos(m, t) != q by {}
        lemma_no_rows(m, p, q);
    }
    lemma_gseq_none(m, p, o_lo, o_hi);
}

/// The next order position after a run ending at `j`: the next run's order, or `o_hi` at the chunk's end.
pub open spec fn next_pos(m: M, o_hi: int, l_hi: int, j: int) -> int {
    if j < l_hi { lpos(m, j) } else { o_hi }
}

/// A finished run `[s, j)` (row `j` has another key, or `j` ends the chunk) holds every row of its key: its count
/// and sum are the key's; its order is `lpos(s)`; the orders up to the next run have no lineitem, so the groups up
/// to the next run are those before the run and possibly the run's order.
pub proof fn lemma_run_end(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, s: int, j: int, ck: int)
    requires
        chunk_ok(m, o_lo, o_hi, l_lo, l_hi),
        run_ok(m, l_lo, s, j, ck),
        j <= l_hi,
        j < l_hi ==> lkey(m, j) != ck,
    ensures
        o_lo <= lpos(m, s) < o_hi,
        okey(m, lpos(m, s)) == ck,
        lpos(m, s) < next_pos(m, o_hi, l_hi, j) <= o_hi,
        kcnt(m, ck) == j - s,
        dsum(ksum_f(m, ck), s, j) == ksum(m, ck),
        gseq(m, p, o_lo, next_pos(m, o_hi, l_hi, j)) == if good(m, p, lpos(m, s)) {
            gseq(m, p, o_lo, lpos(m, s)).push(grow(m, p, lpos(m, s)))
        } else {
            gseq(m, p, o_lo, lpos(m, s))
        },
{
    let gq = lpos(m, s);
    let nq = next_pos(m, o_hi, l_hi, j);
    lemma_row_pos(m, o_lo, o_hi, l_lo, l_hi, s);
    // the rows of key ck are exactly [s, j)
    assert forall|t: int| 0 <= t < m.l_n && (t < s || t >= j) implies lkey(m, t) != ck by {
        lemma_lpos_key(m, gq, t);
        if t < s {
            if s > l_lo {
                lemma_lpos_key(m, gq, s - 1);
                lemma_lpos_mono(m, t, s - 1);
                lemma_lpos_mono(m, s - 1, s);
            } else {
                assert(lpos(m, t) < o_lo);
            }
        } else {
            if j < l_hi {
                lemma_lpos_key(m, gq, j);
                lemma_lpos_mono(m, s, j);
                lemma_lpos_mono(m, j, t);
            } else {
                assert(lpos(m, t) >= o_hi);
            }
        }
    }
    assert forall|t: int| s <= t < j implies #[trigger] lpos(m, t) == gq by {
        lemma_lpos_key(m, gq, t);
    }
    lemma_run_totals(m, ck, s, j);
    lemma_count_prefix(m, ck, s, j);
    // the next run's order is after this one
    if j < l_hi {
        lemma_row_pos(m, o_lo, o_hi, l_lo, l_hi, j);
        lemma_lpos_mono(m, s, j);
        lemma_lpos_key(m, gq, j);
    }
    // the orders strictly between have no lineitem
    assert forall|q: int| gq < q < nq implies !#[trigger] good(m, p, q) by {
        assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lpos(m, t) != q by {
            if t < j {
                if t >= s {
                } else if t >= l_lo {
                    lemma_lpos_mono(m, t, s);
                } else {
                    assert(lpos(m, t) < o_lo);
                }
            } else {
                if j < l_hi {
                    lemma_lpos_mono(m, j, t);
                } else {
                    assert(lpos(m, t) >= o_hi);
                }
            }
        }
        lemma_no_rows(m, p, q);
    }
    lemma_gseq_step(m, p, o_lo, gq);
    lemma_gseq_none(m, p, gq + 1, nq);
    lemma_gseq_split(m, p, o_lo, gq + 1, nq);
    assert(gseq(m, p, o_lo, gq + 1) + Seq::<Row>::empty() =~= gseq(m, p, o_lo, gq + 1));
}

/// The count of `[s, j)` rows of one key, as a prefix sum.
proof fn lemma_count_prefix(m: M, ck: int, s: int, j: int)
    requires
        0 <= s <= j <= m.l_n,
        forall|t: int| s <= t < j ==> #[trigger] lkey(m, t) == ck,
        forall|t: int| 0 <= t < m.l_n && (t < s || t >= j) ==> lkey(m, t) != ck,
    ensures kcnt(m, ck) == j - s,
{
    let f = kcnt_f(m, ck);
    assert forall|t: int| 0 <= t < s implies #[trigger] f(t) == 0 by {}
    lemma_isum_prefix_zero(s, f);
    lemma_count_range(m, ck, s, j);
    assert forall|t: int| j <= t < m.l_n implies #[trigger] f(t) == 0 by {}
    lemma_isum_suffix_zero(j, m.l_n, f);
}

/// Rows `[s, i)` of key `ck` count `i - s` on top of the prefix.
proof fn lemma_count_range(m: M, ck: int, s: int, i: int)
    requires 0 <= s <= i, forall|t: int| s <= t < i ==> #[trigger] lkey(m, t) == ck,
    ensures isum(i, kcnt_f(m, ck)) == isum(s, kcnt_f(m, ck)) + (i - s),
    decreases i - s,
{
    if i > s {
        lemma_count_range(m, ck, s, i - 1);
        lemma_isum_step(i - 1, kcnt_f(m, ck));
    }
}

/// The candidate of a finished run above `$1`: its order (by key), customer and row, inserted into the top 100
/// when the order is a group.
fn take_run(c: &Cols, ck: i64, sum: i128, guess: usize, buf: &mut Vec<Cand>, len: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(gq): Ghost<int>, Ghost(all): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>)
    -> (r: usize)
    requires
        cols_ok(*c, m, p), model_ok(m), c.idx_ok,
        lo <= gq < m.o_n, 0 <= lo,
        okey(m, gq) == ck as int,
        kcnt(m, ck as int) > 0,
        ksum(m, ck as int) == sum as int,
        sum > c.thr,
        all == gseq(m, p, lo, gq),
        old(buf)@.len() == K,
        len <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, old(buf)@, len as int), all),
        forall|i: int| 0 <= i < len ==> (#[trigger] old(buf)@[i]).cpos < m.c_n,
    ensures
        final(buf)@.len() == K,
        r <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, final(buf)@, r as int),
            if good(m, p, gq) { all.push(grow(m, p, gq)) } else { all }),
        forall|i: int| 0 <= i < r ==> (#[trigger] final(buf)@[i]).cpos < m.c_n,
    no_unwind
{
    let q = match find_order_guess(c, ck, guess, Ghost(m), Ghost(p)) {
        Some(q) => q,
        None => {
            proof {
                crate::agent::facts::lemma_opos(m, ck as int);
            }
            return len;
        },
    };
    proof {
        crate::agent::facts::lemma_opos(m, ck as int);
        assert(q as int == gq);
    }
    let og = ((q as u64) / c.o_bs) as usize;
    proof {
        lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb);
    }
    let cnt: u64 = 1;
    match cand_of(c, q, og, ck, sum, Ghost(m), Ghost(p)) {
        Some(cd) => {
            let ghost lb = buf@;
            proof {
                lemma_gseq_step(m, p, lo, gq);
                lemma_gseq_wf(m, p, lo, gq + 1);
            }
            let r = topk_insert(buf, len, cd, Ghost(m), Ghost(all));
            proof {
                assert forall|i: int| 0 <= i < r implies (#[trigger] buf@[i]).cpos < m.c_n by {
                    if buf@[i] != cd {
                        let u = choose|u: int| 0 <= u < len && buf@[i] == lb[u];
                    }
                }
            }
            r
        },
        None => len,
    }
}

/// The scan state after rows `[l_lo, j)`: the current run `[s, j)` of key `ck` with sum `sum`, and the top 100 of
/// the groups of the orders before the run's order.
pub open spec fn scan_inv(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, s: int, j: int, ck: int,
    sum: i128, buf: Seq<Cand>, len: int) -> bool
{
    &&& chunk_ok(m, o_lo, o_hi, l_lo, l_hi)
    &&& run_ok(m, l_lo, s, j, ck)
    &&& j <= l_hi
    &&& acc_ok(m, ck, s, j, (j - s) as u64, sum)
    &&& buf.len() == K
    &&& 0 <= len <= K
    &&& o_lo <= lpos(m, s)
    &&& topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, buf, len), gseq(m, p, o_lo, lpos(m, s)))
    &&& forall|i: int| 0 <= i < len ==> (#[trigger] buf[i]).cpos < m.c_n
}

/// The chunk's top 100: one pass over its lineitem rows.
pub fn scan_chunk(c: &Cols, o_lo: usize, o_hi: usize, l_lo: usize, l_hi: usize, buf: &mut Vec<Cand>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (len: usize)
    requires
        cols_ok(*c, m, p), c.idx_ok,
        chunk_ok(m, o_lo as int, o_hi as int, l_lo as int, l_hi as int),
        old(buf)@.len() == K,
    ensures
        final(buf)@.len() == K,
        len <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, final(buf)@, len as int), gseq(m, p, o_lo as int, o_hi as int)),
        forall|i: int| 0 <= i < len ==> (#[trigger] final(buf)@[i]).cpos < m.c_n,
    no_unwind
{
    if l_lo >= l_hi {
        proof {
            lemma_scan_empty(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int);
            lemma_topk_empty(q18_keys(), q18_fams(), K as nat);
            assert(cands_view(m, buf@, 0) =~= Seq::<Row>::empty());
        }
        return 0;
    }
    let thr = c.thr;
    let bs = c.l_bs;
    // the first row starts the first run
    let g0 = ((l_lo as u64) / bs) as usize;
    proof {
        lemma_block_bound(l_lo as int, m.l_bs, m.l_n, m.l_nb);
        assert(in_i64(lkey(m, l_lo as int)));
        assert(qmax() == pow10(15)) by {
            assert(pow10(15) == 1000000000000000) by (compute);
        }
    }
    let mut ck: i64 = c.l_key_b[g0] + c.l_key_c[l_lo] as i64;
    let mut sum: i128 = (c.l_qty_b[g0] + c.l_qty_c[l_lo] as i64) as i128;
    let mut s: usize = l_lo;
    let mut j: usize = l_lo + 1;
    let mut len: usize = 0;
    proof {
        lemma_scan_start(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int);
        lemma_topk_empty(q18_keys(), q18_fams(), K as nat);
        assert(cands_view(m, buf@, 0) =~= Seq::<Row>::empty());
        assert(acc_ok(m, ck as int, l_lo as int, l_lo as int, 0, 0));
        lemma_acc_step(m, ck as int, l_lo as int, l_lo as int, 0, 0, (c.l_qty_b[g0 as int] + c.l_qty_c[l_lo as int]) as i64);
    }
    // block by block (bases hoisted)
    while j < l_hi
        invariant
            cols_ok(*c, m, p), c.idx_ok, thr == c.thr, bs as int == m.l_bs,
            l_lo < j <= l_hi,
            scan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, s as int, j as int, ck as int, sum, buf@, len as int),
            qmax() == pow10(15),
        decreases l_hi - j,
    {
        // the block of row j and its end inside the chunk
        let gj64 = (j as u64) / bs;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j as int, m.l_bs);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(j as int, m.l_bs);
            assert(m.l_bs * gj64 == gj64 * m.l_bs) by (nonlinear_arith);
            assert((gj64 + 1) * m.l_bs == gj64 * m.l_bs + m.l_bs) by (nonlinear_arith);
            assert(gj64 <= j) by (nonlinear_arith) requires gj64 * m.l_bs <= j, m.l_bs >= 1, gj64 >= 0;
            lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
        }
        let gj = gj64 as usize;
        let ge64 = (gj64 + 1) * bs;
        let je: usize = if ge64 < l_hi as u64 { ge64 as usize } else { l_hi };
        let kb = c.l_key_b[gj];
        let qb = c.l_qty_b[gj];
        while j < je
            invariant
                cols_ok(*c, m, p), c.idx_ok, thr == c.thr, bs as int == m.l_bs,
                l_lo < j <= je <= l_hi,
                gj * m.l_bs <= j, je <= (gj + 1) * m.l_bs, gj < m.l_nb,
                scan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, s as int, j as int, ck as int, sum, buf@, len as int),
                kb == m.l_key_b[gj as int], qb == m.l_qty_b[gj as int],
                qmax() == pow10(15),
            decreases je - j,
        {
            proof {
                lemma_div_in(j as int, m.l_bs, gj as int);
                assert(in_i64(lkey(m, j as int)));
            }
            let key = kb + c.l_key_c[j] as i64;
            let qv = qb + c.l_qty_c[j] as i64;
            let nr: u64 = if key != ck { 1 } else { 0 };
            let over: u64 = if sum > thr { 1 } else { 0 };
            let ghost gq = lpos(m, s as int);
            let ghost s0 = s as int;
            let ghost ck0 = ck as int;
            proof {
                assert(nr * over == 1 <==> (nr == 1 && over == 1)) by (nonlinear_arith)
                    requires nr == 0 || nr == 1, over == 0 || over == 1;
                if nr == 1 {
                    lemma_run_end(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, s as int, j as int, ck as int);
                }
            }
            if nr * over == 1 {
                // a finished run above `$1`
                len = take_run(c, ck, sum, c.o_n, buf, len, Ghost(m), Ghost(p), Ghost(gq), Ghost(gseq(m, p, o_lo as int, gq)), Ghost(o_lo as int));
            }
            proof {
                if nr == 1 {
                    // the run's order is a group only above `$1`; the groups up to the next run are settled
                    if over == 0 {
                        assert(!good(m, p, gq));
                    }
                    lemma_row_pos(m, o_lo as int, o_hi as int, l_lo as int, l_hi as int, j as int);
                    assert(acc_ok(m, key as int, j as int, j as int, 0, 0));
                    lemma_acc_step(m, key as int, j as int, j as int, 0, 0, qv);
                    assert(lkey(m, j - 1) == ck0);
                } else {
                    lemma_acc_step(m, ck as int, s as int, j as int, (j - s) as u64, sum, qv);
                }
            }
            let keep: i128 = if nr == 1 { 0 } else { sum };
            sum = keep + qv as i128;
            s = if nr == 1 { j } else { s };
            ck = key;
            j = j + 1;
            proof {
                assert(run_ok(m, l_lo as int, s as int, j as int, ck as int));
            }
        }
    }
    // the last run ends with the chunk
    let ghost gq = lpos(m, s as int);
    proof {
        lemma_run_end(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, s as int, j as int, ck as int);
    }
    if sum > thr {
        len = take_run(c, ck, sum, c.o_n, buf, len, Ghost(m), Ghost(p), Ghost(gq), Ghost(gseq(m, p, o_lo as int, gq)), Ghost(o_lo as int));
    } else {
        proof {
            assert(!good(m, p, gq));
        }
    }
    len
}

// ------------------------------------------------------------------------------------------------ the run directory

/// The chunk's runs `[r_lo, r_hi)` (mode 1), whose rows are `[l_lo, l_hi)`; `qm` bounds every l_quantity.
pub open spec fn rchunk_ok(m: M, r_lo: int, r_hi: int, l_lo: int, l_hi: int, qm: int) -> bool {
    &&& runs_ok(m)
    &&& m.r_mode == 1
    &&& 0 <= r_lo <= r_hi <= nruns(m)
    &&& rs(m, r_lo) == l_lo
    &&& rs(m, r_hi) == l_hi
    &&& i64::MIN <= qm <= i64::MAX
    &&& forall|j: int| 0 <= j < m.l_n ==> #[trigger] lqty(m, j) <= qm
}

/// A run of `len` rows cannot be above `thr` when every quantity is at most `qm`.
pub open spec fn below_kmin(qm: int, thr: int, len: int) -> bool {
    len * qm <= thr
}

/// Every run shorter than `kmin` rows cannot be above `thr`.
pub open spec fn kmin_ok(qm: int, thr: int, kmin: int) -> bool {
    &&& 0 <= kmin <= 256
    &&& forall|len: int| 0 <= len < kmin ==> #[trigger] below_kmin(qm, thr, len)
}

/// The shortest run length that may be above `thr` (256 when none up to 255 rows may be).
pub fn kmin_of(qm: i128, thr: i128) -> (k: u16)
    requires i64::MIN <= qm <= i64::MAX,
    ensures kmin_ok(qm as int, thr as int, k as int),
{
    let mut k: u16 = 0;
    let mut done = false;
    while k < 256 && !done
        invariant
            i64::MIN <= qm <= i64::MAX,
            0 <= k <= 256,
            forall|len: int| 0 <= len < k ==> #[trigger] below_kmin(qm as int, thr as int, len),
        decreases 256 - k + if done { 0int } else { 1int },
    {
        proof {
            assert(-256 * 9223372036854775808 <= (k as int) * (qm as int) <= 256 * 9223372036854775808) by (nonlinear_arith)
                requires 0 <= k <= 256, -9223372036854775808 <= qm <= 9223372036854775807;
        }
        if (k as i128) * qm > thr {
            done = true;
        } else {
            k = k + 1;
        }
    }
    k
}

/// Run starts never decrease.
pub proof fn lemma_rs_mono(m: M, a: int, b: int)
    requires 0 <= a <= b <= nruns(m),
    ensures rs(m, a) <= rs(m, b),
    decreases b - a,
{
    if a < b {
        lemma_rs_mono(m, a, b - 1);
        assert(rs(m, b) == rs(m, b - 1) + m.r_lens[b - 1]);
    }
}

/// The quantity sum of rows `[s, e)` of key `ck` is at most `(e - s) * qm` when every quantity is at most `qm`.
proof fn lemma_run_bound(m: M, ck: int, s: int, e: int, qm: int)
    requires
        0 <= s <= e,
        forall|t: int| s <= t < e ==> #[trigger] lkey(m, t) == ck,
        forall|t: int| s <= t < e ==> #[trigger] lqty(m, t) <= qm,
    ensures dsum(ksum_f(m, ck), s, e) <= (e - s) * qm,
    decreases e - s,
{
    if e == s {
        assert((e - s) * qm == 0) by (nonlinear_arith) requires e == s;
    } else {
        lemma_run_bound(m, ck, s, e - 1, qm);
        lemma_isum_step(e - 1, ksum_f(m, ck));
        assert(lkey(m, e - 1) == ck);
        assert(lqty(m, e - 1) <= qm);
        assert(ksum_f(m, ck)(e - 1) == lqty(m, e - 1));
        assert(dsum(ksum_f(m, ck), s, e) == dsum(ksum_f(m, ck), s, e - 1) + lqty(m, e - 1));
        assert((e - s) * qm == (e - 1 - s) * qm + qm) by (nonlinear_arith);
    }
}

/// The l_quantity sum of the rows `[s, e)` of key `ck`, all inside block `g` (`e <= ge`, the block's end) or,
/// crossing a block end, row by row.
fn run_sum(c: &Cols, s: usize, e: usize, g: usize, ge: u64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(ck): Ghost<int>)
    -> (r: i128)
    requires
        cols_ok(*c, m, p), model_ok(m),
        s < e <= m.l_n,
        e - s <= 255,
        g * m.l_bs <= s < ge,
        ge == (g + 1) * m.l_bs,
        g < m.l_nb,
        forall|t: int| s <= t < e ==> #[trigger] lkey(m, t) == ck,
    ensures
        r as int == dsum(ksum_f(m, ck), s as int, e as int),
    no_unwind
{
    proof {
        assert(qmax() == pow10(15)) by {
            assert(pow10(15) == 1000000000000000) by (compute);
        }
        lemma_block_bound(s as int, m.l_bs, m.l_n, m.l_nb);
        lemma_div_in(s as int, m.l_bs, g as int);
    }
    if (e as u64) <= ge {
        // one block: the base once, then the codes
        let qb = c.l_qty_b[g];
        let mut t: usize = s;
        let mut acc: u64 = 0;
        while t < e
            invariant
                cols_ok(*c, m, p), model_ok(m),
                s <= t <= e <= m.l_n, e - s <= 255, e <= ge,
                g * m.l_bs <= s, ge == (g + 1) * m.l_bs, g < m.l_nb,
                qb == m.l_qty_b[g as int],
                forall|u: int| s <= u < e ==> #[trigger] lkey(m, u) == ck,
                acc <= (t - s) * 65535,
                acc as int + (t - s) * (qb as int) == dsum(ksum_f(m, ck), s as int, t as int),
            decreases e - t,
        {
            proof {
                lemma_div_in(t as int, m.l_bs, g as int);
                lemma_isum_step(t as int, ksum_f(m, ck));
                assert(lkey(m, t as int) == ck);
                assert(lqty(m, t as int) == qb as int + m.l_qty_c[t as int] as int);
                assert((t + 1 - s) * (qb as int) == (t - s) * (qb as int) + qb as int) by (nonlinear_arith);
                assert((t + 1 - s) * 65535 == (t - s) * 65535 + 65535) by (nonlinear_arith);
                assert((t - s) * 65535 <= 255 * 65535) by (nonlinear_arith) requires t - s <= 255;
            }
            acc = acc + c.l_qty_c[t] as u64;
            t = t + 1;
        }
        proof {
            assert((qb as int) * ((e - s) as int) <= 255 * 9223372036854775807) by (nonlinear_arith)
                requires e - s <= 255, e - s >= 0, qb <= 9223372036854775807, qb >= -9223372036854775808;
            assert((qb as int) * ((e - s) as int) >= 255 * (-9223372036854775808)) by (nonlinear_arith)
                requires e - s <= 255, e - s >= 0, qb >= -9223372036854775808, qb <= 9223372036854775807;
            assert((qb as int) * ((e - s) as int) == (e - s) * (qb as int)) by (nonlinear_arith);
            assert(acc <= 255 * 65535) by (nonlinear_arith) requires acc <= (e - s) * 65535, e - s <= 255;
        }
        (qb as i128) * ((e - s) as i128) + acc as i128
    } else {
        // across a block end: row by row
        let mut t: usize = s;
        let mut sum: i128 = 0;
        while t < e
            invariant
                cols_ok(*c, m, p), model_ok(m),
                s <= t <= e <= m.l_n, e - s <= 255,
                forall|u: int| s <= u < e ==> #[trigger] lkey(m, u) == ck,
                qmax() == pow10(15),
                -(t - s) * qmax() <= sum <= (t - s) * qmax(),
                sum as int == dsum(ksum_f(m, ck), s as int, t as int),
            decreases e - t,
        {
            proof {
                lemma_block_bound(t as int, m.l_bs, m.l_n, m.l_nb);
                lemma_isum_step(t as int, ksum_f(m, ck));
                assert(lkey(m, t as int) == ck);
                assert(-(t + 1 - s) * qmax() == -(t - s) * qmax() - qmax());
                assert((t + 1 - s) * qmax() == (t - s) * qmax() + qmax());
                assert((t - s) * qmax() <= 255 * qmax()) by (nonlinear_arith) requires t - s <= 255, qmax() > 0;
            }
            let gt = ((t as u64) / c.l_bs) as usize;
            let qv = c.l_qty_b[gt] + c.l_qty_c[t] as i64;
            sum = sum + qv as i128;
            t = t + 1;
        }
        sum
    }
}

/// The block cursor `(g, ge)` (block `g` ends at row `ge`) moved forward to row `pos`.
fn cursor_to(pos: usize, g: usize, ge: u64, bs: u64, Ghost(n): Ghost<int>) -> (r: (usize, u64))
    requires
        bs >= 1, pos < n, n + bs <= u64::MAX,
        g * bs <= pos, ge == (g + 1) * bs, ge <= pos + bs,
    ensures
        r.0 * bs <= pos < r.1, r.1 == (r.0 + 1) * bs, r.1 <= pos + bs,
    no_unwind
{
    let mut g = g;
    let mut ge = ge;
    while (pos as u64) >= ge
        invariant
            bs >= 1, pos < n, n + bs <= u64::MAX,
            g * bs <= pos, ge == (g + 1) * bs, ge <= pos + bs,
        decreases pos + bs - ge,
    {
        proof {
            assert((g + 2) * bs == (g + 1) * bs + bs) by (nonlinear_arith);
            assert(g + 1 <= pos) by (nonlinear_arith) requires (g + 1) * bs <= pos, bs >= 1, g >= 0;
        }
        g = g + 1;
        ge = ge + bs;
    }
    (g, ge)
}

/// The scan state after the runs `[r_lo, r)`: the next run starts at row `pos`, the lineitem block cursor is
/// `g` (ending at row `ge`), and the buffer is the top 100 of the groups of the orders before the next run's order.
#[verifier::opaque]
pub open spec fn rscan_inv(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, r_lo: int, r_hi: int, qm: int,
    r: int, pos: int, g: int, ge: int, buf: Seq<Cand>, len: int) -> bool
{
    &&& chunk_ok(m, o_lo, o_hi, l_lo, l_hi)
    &&& rchunk_ok(m, r_lo, r_hi, l_lo, l_hi, qm)
    &&& r_lo <= r <= r_hi
    &&& pos == rs(m, r)
    &&& l_lo <= pos <= l_hi
    &&& 0 <= g && g * m.l_bs <= pos && ge == (g + 1) * m.l_bs && ge <= pos + m.l_bs
    &&& buf.len() == K
    &&& 0 <= len <= K
    &&& topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, buf, len), gseq(m, p, o_lo, next_pos(m, o_hi, l_hi, pos)))
    &&& forall|i: int| 0 <= i < len ==> (#[trigger] buf[i]).cpos < m.c_n
}

/// Run `r` of the chunk is a finished run of `lemma_run_end`: `[rs(r), rs(r + 1))`, maximal on both sides.
proof fn lemma_run_at(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, r_lo: int, r_hi: int, qm: int, r: int)
    requires
        chunk_ok(m, o_lo, o_hi, l_lo, l_hi),
        rchunk_ok(m, r_lo, r_hi, l_lo, l_hi, qm),
        r_lo <= r < r_hi,
    ensures ({
        let (s, j, ck) = (rs(m, r), rs(m, r + 1), lkey(m, rs(m, r)));
        &&& l_lo <= s < j <= l_hi
        &&& j == s + m.r_lens[r]
        &&& run_ok(m, l_lo, s, j, ck)
        &&& (j < l_hi ==> lkey(m, j) != ck)
        &&& forall|t: int| s <= t < j ==> #[trigger] lqty(m, t) <= qm
    }),
{
    reveal(runs_ok);
    let (s, j, ck) = (rs(m, r), rs(m, r + 1), lkey(m, rs(m, r)));
    lemma_rs_mono(m, r_lo, r);
    lemma_rs_mono(m, r + 1, r_hi);
    assert(m.r_lens[r] >= 1 && run_same_m(m, r));
    assert(j == s + m.r_lens[r]);
    assert forall|t: int| s <= t < j implies #[trigger] lkey(m, t) == ck by {}
    if s != l_lo {
        assert(r != r_lo);
        assert(run_cut_m(m, r));
    }
    if j < l_hi {
        assert(r + 1 != r_hi);
        assert(run_cut_m(m, r + 1));
        assert(lkey(m, j - 1) == ck);
    }
    assert forall|t: int| s <= t < j implies #[trigger] lqty(m, t) <= qm by {
        assert(0 <= t < m.l_n);
    }
}

/// A run below `kmin` rows is not a group: the state moves past it unchanged.
proof fn lemma_step_skip(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, r_lo: int, r_hi: int, qm: int,
    tv: int, kmin: int, r: int, pos: int, g: int, ge: int, buf: Seq<Cand>, len: int)
    requires
        tv == thr(p),
        kmin_ok(qm, tv, kmin),
        r < r_hi,
        rscan_inv(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r, pos, g, ge, buf, len),
        (m.r_lens[r] as int) < kmin,
    ensures
        rscan_inv(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r + 1, rs(m, r + 1), g, ge, buf, len),
{
    reveal(rscan_inv);
    let ln = m.r_lens[r] as int;
    let ck = lkey(m, pos);
    let gq = lpos(m, pos);
    lemma_run_at(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r);
    lemma_run_end(m, p, o_lo, o_hi, l_lo, l_hi, pos, pos + ln, ck);
    // every quantity is at most `qm`, so the run's sum is at most `ln * qm <= $1`
    assert(below_kmin(qm, tv, ln));
    lemma_run_bound(m, ck, pos, pos + ln, qm);
    assert(!big(m, p, ck));
    assert(!good(m, p, gq));
    assert(m.l_bs >= 1);
}

/// The facts of run `r` that a summed run needs (after `lemma_run_end`).
pub open spec fn cand_facts(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, pos: int, e: int) -> bool {
    let ck = lkey(m, pos);
    let gq = lpos(m, pos);
    &&& o_lo <= gq < o_hi
    &&& okey(m, gq) == ck
    &&& kcnt(m, ck) == e - pos
    &&& dsum(ksum_f(m, ck), pos, e) == ksum(m, ck)
    &&& gseq(m, p, o_lo, next_pos(m, o_hi, l_hi, e)) == if good(m, p, gq) {
            gseq(m, p, o_lo, gq).push(grow(m, p, gq))
        } else {
            gseq(m, p, o_lo, gq)
        }
}

/// Run `r` of the state: its rows, key and order (`lemma_run_end`), and the state's other facts.
proof fn lemma_cand_facts(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, r_lo: int, r_hi: int, qm: int,
    r: int, pos: int, g: int, ge: int, buf: Seq<Cand>, len: int)
    requires
        r < r_hi,
        rscan_inv(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r, pos, g, ge, buf, len),
    ensures
        cand_facts(m, p, o_lo, o_hi, l_lo, l_hi, pos, rs(m, r + 1)),
        rs(m, r + 1) == pos + m.r_lens[r],
        pos < rs(m, r + 1) <= l_hi <= m.l_n,
        forall|t: int| pos <= t < rs(m, r + 1) ==> #[trigger] lkey(m, t) == lkey(m, pos),
        model_ok(m),
        m.l_bs >= 1, m.l_n + m.l_bs <= u64::MAX,
        0 <= g && g * m.l_bs <= pos && ge == (g + 1) * m.l_bs && ge <= pos + m.l_bs,
        buf.len() == K, 0 <= len <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, buf, len), gseq(m, p, o_lo, lpos(m, pos))),
        forall|i: int| 0 <= i < len ==> (#[trigger] buf[i]).cpos < m.c_n,
        0 <= o_lo, o_hi <= m.o_n,
        r_hi <= nruns(m),
        pos == rs(m, r),
{
    reveal(rscan_inv);
    lemma_run_at(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r);
    lemma_run_end(m, p, o_lo, o_hi, l_lo, l_hi, pos, rs(m, r + 1), lkey(m, pos));
}

/// The state after a summed run `r` whose buffer now covers the groups up to the next run's order.
proof fn lemma_step_done(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, r_lo: int, r_hi: int, qm: int,
    r: int, pos: int, g: int, ge: int, buf: Seq<Cand>, len: int, g2: int, ge2: int, buf2: Seq<Cand>, len2: int)
    requires
        r < r_hi,
        rscan_inv(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r, pos, g, ge, buf, len),
        0 <= g2 && g2 * m.l_bs <= pos && ge2 == (g2 + 1) * m.l_bs && ge2 <= pos + m.l_bs,
        buf2.len() == K, 0 <= len2 <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, buf2, len2),
            gseq(m, p, o_lo, next_pos(m, o_hi, l_hi, rs(m, r + 1)))),
        forall|i: int| 0 <= i < len2 ==> (#[trigger] buf2[i]).cpos < m.c_n,
    ensures
        rscan_inv(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r + 1, rs(m, r + 1), g2, ge2, buf2, len2),
{
    reveal(rscan_inv);
    lemma_run_at(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r);
    let e = rs(m, r + 1);
    assert(g2 * m.l_bs <= e && ge2 <= e + m.l_bs);
}

/// A run of at least `kmin` rows: its sum, and (above `$1`) its order into the top 100.
fn cand_step(c: &Cols, o_lo: usize, o_hi: usize, l_lo: usize, l_hi: usize, r_lo: usize, r_hi: usize, qm: i128,
    r: usize, pos: usize, e: usize, g: usize, ge: u64, buf: &mut Vec<Cand>, len: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (out: (usize, u64, usize))
    requires
        cols_ok(*c, m, p), c.idx_ok,
        r < r_hi,
        e as int == rs(m, r + 1),
        rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r as int, pos as int, g as int, ge as int, old(buf)@, len as int),
    ensures
        rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r + 1, e as int, out.0 as int, out.1 as int, final(buf)@, out.2 as int),
    no_unwind
{
    let ghost ck = lkey(m, pos as int);
    let ghost gq = lpos(m, pos as int);
    proof {
        lemma_cand_facts(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r as int, pos as int, g as int, ge as int, buf@, len as int);
    }
    let ghost b0 = buf@;
    // move the block cursor to the run, then sum its rows
    let (g2, ge2) = cursor_to(pos, g, ge, c.l_bs, Ghost(m.l_n));
    proof {
        lemma_div_in(pos as int, m.l_bs, g2 as int);
        lemma_block_bound(pos as int, m.l_bs, m.l_n, m.l_nb);
    }
    let sum = run_sum(c, pos, e, g2, ge2, Ghost(m), Ghost(p), Ghost(ck));
    let mut len2 = len;
    if sum > c.thr {
        // a group candidate (rare): its key
        proof {
            lemma_div_in(pos as int, m.l_bs, g2 as int);
            lemma_block_bound(pos as int, m.l_bs, m.l_n, m.l_nb);
            assert(in_i64(lkey(m, pos as int)));
        }
        let ckv = c.l_key_b[g2] + c.l_key_c[pos] as i64;
        len2 = take_run(c, ckv, sum, r, buf, len, Ghost(m), Ghost(p), Ghost(gq), Ghost(gseq(m, p, o_lo as int, gq)), Ghost(o_lo as int));
    } else {
        proof {
            assert(!good(m, p, gq));
        }
    }
    proof {
        lemma_step_done(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r as int, pos as int, g as int, ge as int, b0, len as int, g2 as int, ge2 as int, buf@, len2 as int);
    }
    (g2, ge2, len2)
}

/// One run of the chunk (run `r`, starting at row `pos`): skipped unread below `kmin` rows, else summed and, above
/// `$1`, its order taken into the top 100. Returns the next run's start, the block cursor and the buffer length.
fn step_run(c: &Cols, o_lo: usize, o_hi: usize, l_lo: usize, l_hi: usize, r_lo: usize, r_hi: usize, qm: i128,
    kmin: u16, r: usize, pos: usize, g: usize, ge: u64, buf: &mut Vec<Cand>, len: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (out: (usize, usize, u64, usize))
    requires
        cols_ok(*c, m, p), c.idx_ok, rcols_ok(*c, m),
        kmin_ok(qm as int, c.thr as int, kmin as int),
        r < r_hi,
        rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r as int, pos as int, g as int, ge as int, old(buf)@, len as int),
    ensures
        rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r + 1, out.0 as int, out.1 as int, out.2 as int, final(buf)@, out.3 as int),
    no_unwind
{
    proof {
        lemma_cand_facts(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r as int, pos as int, g as int, ge as int, buf@, len as int);
    }
    let ln = c.r_lens[r];
    let e = pos + ln as usize;
    if ln as u16 >= kmin {
        let (g2, ge2, len2) = cand_step(c, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r, pos, e, g, ge, buf, len, Ghost(m), Ghost(p));
        (e, g2, ge2, len2)
    } else {
        proof {
            lemma_step_skip(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
                c.thr as int, kmin as int, r as int, pos as int, g as int, ge as int, buf@, len as int);
        }
        (e, g, ge, len)
    }
}

/// The chunk's top 100 by its runs: runs that cannot be above `$1` are skipped unread.
pub fn scan_runs(c: &Cols, o_lo: usize, o_hi: usize, l_lo: usize, l_hi: usize, r_lo: usize, r_hi: usize, qm: i128,
    kmin: u16, buf: &mut Vec<Cand>, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (len: usize)
    requires
        cols_ok(*c, m, p), c.idx_ok, rcols_ok(*c, m),
        chunk_ok(m, o_lo as int, o_hi as int, l_lo as int, l_hi as int),
        rchunk_ok(m, r_lo as int, r_hi as int, l_lo as int, l_hi as int, qm as int),
        kmin_ok(qm as int, c.thr as int, kmin as int),
        old(buf)@.len() == K,
    ensures
        final(buf)@.len() == K,
        len <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, final(buf)@, len as int), gseq(m, p, o_lo as int, o_hi as int)),
        forall|i: int| 0 <= i < len ==> (#[trigger] final(buf)@[i]).cpos < m.c_n,
    no_unwind
{
    if l_lo >= l_hi {
        proof {
            lemma_scan_empty(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int);
            lemma_topk_empty(q18_keys(), q18_fams(), K as nat);
            assert(cands_view(m, buf@, 0) =~= Seq::<Row>::empty());
        }
        return 0;
    }
    let thr = c.thr;
    let bs = c.l_bs;
    // the lineitem block cursor (one division per chunk)
    let g64 = (l_lo as u64) / bs;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(l_lo as int, m.l_bs);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(l_lo as int, m.l_bs);
        assert(m.l_bs * g64 == g64 * m.l_bs) by (nonlinear_arith);
        assert((g64 + 1) * m.l_bs == g64 * m.l_bs + m.l_bs) by (nonlinear_arith);
        assert(g64 <= l_lo) by (nonlinear_arith) requires g64 * m.l_bs <= l_lo, m.l_bs >= 1, g64 >= 0;
    }
    let mut g: usize = g64 as usize;
    let mut ge: u64 = (g64 + 1) * bs;
    let mut pos: usize = l_lo;
    let mut r: usize = r_lo;
    let mut len: usize = 0;
    proof {
        lemma_scan_start(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int);
        lemma_topk_empty(q18_keys(), q18_fams(), K as nat);
        assert(cands_view(m, buf@, 0) =~= Seq::<Row>::empty());
        reveal(rscan_inv);
        assert(rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r as int, pos as int, g as int, ge as int, buf@, len as int));
    }
    while r < r_hi
        invariant
            cols_ok(*c, m, p), c.idx_ok, rcols_ok(*c, m),
            kmin_ok(qm as int, c.thr as int, kmin as int),
            rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
                r as int, pos as int, g as int, ge as int, buf@, len as int),
        decreases r_hi - r,
    {
        let st = step_run(c, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, kmin, r, pos, g, ge, buf, len, Ghost(m), Ghost(p));
        pos = st.0;
        g = st.1;
        ge = st.2;
        len = st.3;
        r = r + 1;
    }
    proof {
        reveal(rscan_inv);
        assert(pos == l_hi);
    }
    len
}

// ------------------------------------------------------------------------------------------------ the run permutation

/// The run permutation by length serves a chunk: present, and its longest length is at most `kmin`.
pub open spec fn long_use_ok(m: M, kmin: int) -> bool {
    &&& long_ok(m)
    &&& m.lg_mode == 1
    &&& m.lg_max <= kmin
}

/// The first `n` entries of `s` strictly increase.
pub open spec fn incr(s: Seq<u32>, n: int) -> bool {
    forall|a: int, b: int| 0 <= a < b < n ==> #[trigger] s[a] < #[trigger] s[b]
}

/// The shape of the permutation's first class.
proof fn lemma_long_facts(m: M)
    requires long_ok(m), m.lg_mode == 1,
    ensures
        m.r_mode == 1,
        m.lg_n <= m.lg_runs.len(), m.lg_n <= m.lg_starts.len(),
        incr(m.lg_runs, m.lg_n),
{
    reveal(long_ok);
}

/// Entry `i` of the first class: a run of length `lg_max`, with its start row.
proof fn lemma_long_entry(m: M, i: int)
    requires long_ok(m), m.lg_mode == 1, 0 <= i < m.lg_n,
    ensures
        m.lg_runs[i] < nruns(m),
        m.r_lens[m.lg_runs[i] as int] == m.lg_max,
        m.lg_starts[i] == rs(m, m.lg_runs[i] as int),
{
    reveal(long_ok);
    assert(fi::long_at(m.r_lens, m.lg_runs, m.lg_starts, m.lg_max, i));
}

/// When the entries before `i` are below run `ra` and the entries from `i` on are at least run `rb`, every run in
/// `[ra, rb)` is shorter than `lg_max` (a run of length `lg_max` is listed).
proof fn lemma_gap(m: M, i: int, ra: int, rb: int)
    requires
        long_ok(m), m.lg_mode == 1, 0 <= i <= m.lg_n,
        forall|j: int| 0 <= j < i ==> #[trigger] m.lg_runs[j] < ra,
        forall|j: int| i <= j < m.lg_n ==> rb <= #[trigger] m.lg_runs[j],
    ensures
        forall|t: int| ra <= t < rb && 0 <= t < nruns(m) ==> #[trigger] m.r_lens[t] < m.lg_max,
{
    reveal(long_ok);
    assert forall|t: int| ra <= t < rb && 0 <= t < nruns(m) implies #[trigger] m.r_lens[t] < m.lg_max by {
        assert(m.r_lens[t] <= m.lg_max);
        if m.r_lens[t] == m.lg_max {
            assert(fi::long_listed(m.lg_runs, m.lg_n, t));
            let j = choose|j: int| 0 <= j < m.lg_n && m.lg_runs[j] as int == t;
            if j < i {
                assert(m.lg_runs[j] < ra);
            } else {
                assert(rb <= m.lg_runs[j]);
            }
        }
    }
}

/// The runs `[ra, rb)`, all shorter than `kmin`, are skipped: the state moves past them unchanged.
proof fn lemma_skip_range(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, r_lo: int, r_hi: int, qm: int,
    tv: int, kmin: int, ra: int, rb: int, pos: int, g: int, ge: int, buf: Seq<Cand>, len: int)
    requires
        tv == thr(p),
        kmin_ok(qm, tv, kmin),
        ra <= rb <= r_hi,
        rscan_inv(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, ra, pos, g, ge, buf, len),
        forall|t: int| ra <= t < rb ==> (#[trigger] m.r_lens[t] as int) < kmin,
    ensures
        rscan_inv(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, rb, rs(m, rb), g, ge, buf, len),
    decreases rb - ra,
{
    reveal(rscan_inv);
    if ra < rb {
        assert((m.r_lens[ra] as int) < kmin);
        lemma_step_skip(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, tv, kmin, ra, pos, g, ge, buf, len);
        lemma_skip_range(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, tv, kmin, ra + 1, rb, rs(m, ra + 1), g, ge, buf, len);
    }
}

/// The first of the `n` increasing entries of `s` that is at least `x` (`n` when none).
fn lower_bound(s: &[u32], n: usize, x: usize) -> (i: usize)
    requires n <= s@.len(), incr(s@, n as int),
    ensures
        i <= n,
        forall|j: int| 0 <= j < i ==> #[trigger] s@[j] < x,
        forall|j: int| i <= j < n ==> x <= #[trigger] s@[j],
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant
            lo <= hi <= n, n <= s@.len(), incr(s@, n as int),
            forall|j: int| 0 <= j < lo ==> #[trigger] s@[j] < x,
            forall|j: int| hi <= j < n ==> x <= #[trigger] s@[j],
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if (s[mid] as usize) < x {
            proof {
                assert forall|j: int| 0 <= j < mid + 1 implies #[trigger] s@[j] < x by {
                    if j < mid {
                        assert(s@[j] < s@[mid as int]);
                    }
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|j: int| mid <= j < n implies x <= #[trigger] s@[j] by {
                    if j > mid {
                        assert(s@[mid as int] < s@[j]);
                    }
                }
            }
            hi = mid;
        }
    }
    lo
}

/// `acc + (t - s) * base` is the l_quantity sum of the rows `[s, t)` of key `ck` inside lineitem block `g`.
pub open spec fn codes_at(m: M, ck: int, s: int, t: int, g: int, acc: int) -> bool {
    acc + (t - s) * m.l_qty_b[g] == dsum(ksum_f(m, ck), s, t)
}

/// One more row `t` of key `ck` inside block `g` adds its code.
proof fn lemma_code_step(m: M, ck: int, s: int, t: int, g: int, acc: int)
    requires
        model_ok(m),
        0 <= s, g * m.l_bs <= s <= t, t < (g + 1) * m.l_bs, t < m.l_n,
        lkey(m, t) == ck,
        codes_at(m, ck, s, t, g, acc),
    ensures
        codes_at(m, ck, s, t + 1, g, acc + m.l_qty_c[t]),
{
    lemma_div_in(t, m.l_bs, g);
    lemma_isum_step(t, ksum_f(m, ck));
    assert(lqty(m, t) == m.l_qty_b[g] as int + m.l_qty_c[t] as int);
    assert((t + 1 - s) * m.l_qty_b[g] == (t - s) * m.l_qty_b[g] + m.l_qty_b[g]) by (nonlinear_arith);
}

/// The l_quantity codes of the rows `[s, e)` of key `ck`, all inside block `g`, summed (7 rows unrolled).
#[inline(always)]
fn block_codes(c: &Cols, s: usize, e: usize, g: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(ck): Ghost<int>)
    -> (acc: u64)
    requires
        cols_ok(*c, m, p), model_ok(m),
        s < e <= m.l_n,
        e - s <= 255,
        g * m.l_bs <= s, e <= (g + 1) * m.l_bs,
        forall|t: int| s <= t < e ==> #[trigger] lkey(m, t) == ck,
    ensures
        acc <= (e - s) * 65535,
        codes_at(m, ck, s as int, e as int, g as int, acc as int),
    no_unwind
{
    let q = c.l_qty_c;
    proof {
        assert((s - s) * m.l_qty_b[g as int] == 0) by (nonlinear_arith);
        assert(codes_at(m, ck, s as int, s as int, g as int, 0));
    }
    if e - s == 7 {
        let a0 = q[s] as u64;
        let a1 = q[s + 1] as u64;
        let a2 = q[s + 2] as u64;
        let a3 = q[s + 3] as u64;
        let a4 = q[s + 4] as u64;
        let a5 = q[s + 5] as u64;
        let a6 = q[s + 6] as u64;
        proof {
            let (si, gi) = (s as int, g as int);
            lemma_code_step(m, ck, si, si, gi, 0);
            lemma_code_step(m, ck, si, si + 1, gi, a0 as int);
            lemma_code_step(m, ck, si, si + 2, gi, (a0 + a1) as int);
            lemma_code_step(m, ck, si, si + 3, gi, (a0 + a1 + a2) as int);
            lemma_code_step(m, ck, si, si + 4, gi, (a0 + a1 + a2 + a3) as int);
            lemma_code_step(m, ck, si, si + 5, gi, (a0 + a1 + a2 + a3 + a4) as int);
            lemma_code_step(m, ck, si, si + 6, gi, (a0 + a1 + a2 + a3 + a4 + a5) as int);
        }
        a0 + a1 + a2 + a3 + a4 + a5 + a6
    } else {
        let mut t: usize = s;
        let mut acc: u64 = 0;
        while t < e
            invariant
                cols_ok(*c, m, p), model_ok(m), q@ == m.l_qty_c,
                s <= t <= e <= m.l_n, e - s <= 255,
                g * m.l_bs <= s, e <= (g + 1) * m.l_bs,
                forall|u: int| s <= u < e ==> #[trigger] lkey(m, u) == ck,
                acc <= (t - s) * 65535,
                codes_at(m, ck, s as int, t as int, g as int, acc as int),
            decreases e - t,
        {
            proof {
                lemma_code_step(m, ck, s as int, t as int, g as int, acc as int);
                assert((t + 1 - s) * 65535 == (t - s) * 65535 + 65535) by (nonlinear_arith);
                assert((t - s) * 65535 <= 255 * 65535) by (nonlinear_arith) requires t - s <= 255;
            }
            acc = acc + q[t] as u64;
            t = t + 1;
        }
        acc
    }
}

/// Every run has at least one row.
proof fn lemma_run_len_pos(m: M, r: int)
    requires runs_ok(m), m.r_mode == 1, 0 <= r < nruns(m),
    ensures m.r_lens[r] >= 1,
{
    reveal(runs_ok);
    assert(m.r_lens[r] >= 1 && run_same_m(m, r));
}

/// The state with the lineitem block cursor moved to `(g2, ge2)` (still at or before the next run's start).
proof fn lemma_rscan_cursor(m: M, p: QP, o_lo: int, o_hi: int, l_lo: int, l_hi: int, r_lo: int, r_hi: int, qm: int,
    r: int, pos: int, g: int, ge: int, buf: Seq<Cand>, len: int, g2: int, ge2: int)
    requires
        rscan_inv(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r, pos, g, ge, buf, len),
        0 <= g2, g2 * m.l_bs <= pos, ge2 == (g2 + 1) * m.l_bs, ge2 <= pos + m.l_bs,
    ensures
        rscan_inv(m, p, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, r, pos, g2, ge2, buf, len),
{
    reveal(rscan_inv);
}

/// A run `r` at `pos` whose rows end inside the cursor's block `g` (`lim` is `$1` minus the run's rows times the
/// block's base): its codes are summed, and only above `lim` is its exact sum formed and its order taken.
#[inline(always)]
fn long_step(c: &Cols, o_lo: usize, o_hi: usize, l_lo: usize, l_hi: usize, r_lo: usize, r_hi: usize, qm: i128,
    pos: usize, e: usize, g: usize, ge: u64, qb: i64, lim: i128, gi: usize, buf: &mut Vec<Cand>, len: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(r): Ghost<int>) -> (len2: usize)
    requires
        cols_ok(*c, m, p), c.idx_ok, gi < c.lg_runs@.len(),
        r < r_hi,
        e as int == rs(m, r + 1),
        rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r, pos as int, g as int, ge as int, old(buf)@, len as int),
        e <= ge,
        g < m.l_nb,
        qb == m.l_qty_b[g as int],
        lim == c.thr - (e - pos) * qb,
    ensures
        rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r + 1, e as int, g as int, ge as int, final(buf)@, len2 as int),
    no_unwind
{
    let ghost ck = lkey(m, pos as int);
    let ghost gq = lpos(m, pos as int);
    proof {
        lemma_cand_facts(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r, pos as int, g as int, ge as int, buf@, len as int);
        assert(m.r_lens[r] <= 255);
    }
    let ghost b0 = buf@;
    let acc = block_codes(c, pos, e, g, Ghost(m), Ghost(p), Ghost(ck));
    let mut len2 = len;
    if (acc as i128) > lim {
        // a group candidate (rare): its exact sum and key
        proof {
            assert(-9223372036854775808 * 255 <= (qb as int) * ((e - pos) as int) <= 9223372036854775807 * 255)
                by (nonlinear_arith) requires 0 <= e - pos <= 255, -9223372036854775808 <= qb <= 9223372036854775807;
            assert((qb as int) * ((e - pos) as int) == (e - pos) * qb) by (nonlinear_arith);
            assert(qmax() == pow10(15)) by {
                assert(pow10(15) == 1000000000000000) by (compute);
            }
            lemma_block_bound(pos as int, m.l_bs, m.l_n, m.l_nb);
            lemma_div_in(pos as int, m.l_bs, g as int);
            assert(in_i64(lkey(m, pos as int)));
        }
        let sum = (qb as i128) * ((e - pos) as i128) + acc as i128;
        let ckv = c.l_key_b[g] + c.l_key_c[pos] as i64;
        let guess = c.lg_runs[gi] as usize;
        len2 = take_run(c, ckv, sum, guess, buf, len, Ghost(m), Ghost(p), Ghost(gq), Ghost(gseq(m, p, o_lo as int, gq)), Ghost(o_lo as int));
    } else {
        proof {
            assert(ksum(m, ck) <= thr(p));
            assert(!good(m, p, gq));
        }
    }
    proof {
        lemma_step_done(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r, pos as int, g as int, ge as int, b0, len as int, g as int, ge as int, buf@, len2 as int);
    }
    len2
}

/// The chunk's top 100 by the run permutation: only its runs of the longest length are read and summed.
pub fn scan_long(c: &Cols, o_lo: usize, o_hi: usize, l_lo: usize, l_hi: usize, r_lo: usize, r_hi: usize, qm: i128,
    kmin: u16, buf: &mut Vec<Cand>, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (len: usize)
    requires
        cols_ok(*c, m, p), c.idx_ok, rcols_ok(*c, m), lcols_ok(*c, m),
        chunk_ok(m, o_lo as int, o_hi as int, l_lo as int, l_hi as int),
        rchunk_ok(m, r_lo as int, r_hi as int, l_lo as int, l_hi as int, qm as int),
        kmin_ok(qm as int, c.thr as int, kmin as int),
        long_use_ok(m, kmin as int),
        old(buf)@.len() == K,
    ensures
        final(buf)@.len() == K,
        len <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, final(buf)@, len as int), gseq(m, p, o_lo as int, o_hi as int)),
        forall|i: int| 0 <= i < len ==> (#[trigger] final(buf)@[i]).cpos < m.c_n,
    no_unwind
{
    if l_lo >= l_hi {
        proof {
            lemma_scan_empty(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int);
            lemma_topk_empty(q18_keys(), q18_fams(), K as nat);
            assert(cands_view(m, buf@, 0) =~= Seq::<Row>::empty());
        }
        return 0;
    }
    proof {
        lemma_long_facts(m);
    }
    // the class size fits `usize`: it is at most the permutation's length
    let n: usize = if c.lg_n <= c.lg_rn as u64 { c.lg_n as usize } else { c.lg_rn };
    let lmax = c.lg_max as usize;
    let i_lo = lower_bound(c.lg_runs, n, r_lo);
    let i_hi = lower_bound(c.lg_runs, n, r_hi);
    proof {
        if i_hi < i_lo {
            assert(c.lg_runs@[i_hi as int] < r_lo);
            assert(r_hi <= c.lg_runs@[i_hi as int]);
        }
    }
    let bs = c.l_bs;
    // the lineitem block cursor (one division per chunk) and its block's limit
    let g64 = (l_lo as u64) / bs;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(l_lo as int, m.l_bs);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(l_lo as int, m.l_bs);
        assert(m.l_bs * g64 == g64 * m.l_bs) by (nonlinear_arith);
        assert((g64 + 1) * m.l_bs == g64 * m.l_bs + m.l_bs) by (nonlinear_arith);
        assert(g64 <= l_lo) by (nonlinear_arith) requires g64 * m.l_bs <= l_lo, m.l_bs >= 1, g64 >= 0;
        lemma_div_in(l_lo as int, m.l_bs, g64 as int);
        lemma_block_bound(l_lo as int, m.l_bs, m.l_n, m.l_nb);
    }
    let mut g: usize = g64 as usize;
    let mut ge: u64 = (g64 + 1) * bs;
    let mut qb: i64 = c.l_qty_b[g];
    proof {
        assert(-9223372036854775808 * 256 <= (lmax as int) * (qb as int) <= 9223372036854775807 * 256)
            by (nonlinear_arith) requires 0 <= lmax <= 256, -9223372036854775808 <= qb <= 9223372036854775807;
    }
    let mut lim: i128 = c.thr - (lmax as i128) * (qb as i128);
    let ghost mut pos: int = l_lo as int;
    let ghost mut r: int = r_lo as int;
    let mut len: usize = 0;
    proof {
        lemma_scan_start(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int);
        lemma_topk_empty(q18_keys(), q18_fams(), K as nat);
        assert(cands_view(m, buf@, 0) =~= Seq::<Row>::empty());
        reveal(rscan_inv);
        assert(rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
            r, pos, g as int, ge as int, buf@, len as int));
    }
    let mut i: usize = i_lo;
    while i < i_hi
        invariant
            cols_ok(*c, m, p), c.idx_ok, rcols_ok(*c, m), lcols_ok(*c, m), model_ok(m),
            kmin_ok(qm as int, c.thr as int, kmin as int),
            long_use_ok(m, kmin as int),
            m.lg_n == n as int, n <= m.lg_runs.len(), n <= m.lg_starts.len(), incr(m.lg_runs, n as int),
            lmax as int == m.lg_max, lmax <= 256, bs as int == m.l_bs,
            rchunk_ok(m, r_lo as int, r_hi as int, l_lo as int, l_hi as int, qm as int),
            i_lo <= i <= i_hi <= n,
            r_lo <= r <= r_hi,
            forall|j: int| 0 <= j < i ==> #[trigger] m.lg_runs[j] < r,
            forall|j: int| i <= j < n ==> r <= #[trigger] m.lg_runs[j],
            forall|j: int| 0 <= j < i_hi ==> #[trigger] m.lg_runs[j] < r_hi,
            forall|j: int| i_hi <= j < n ==> r_hi <= #[trigger] m.lg_runs[j],
            rscan_inv(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int, qm as int,
                r, pos, g as int, ge as int, buf@, len as int),
            g < m.l_nb ==> qb == m.l_qty_b[g as int] && lim == c.thr - lmax * qb,
        decreases i_hi - i,
    {
        let ghost rr = m.lg_runs[i as int] as int;
        proof {
            lemma_long_entry(m, i as int);
            assert forall|j: int| i <= j < n implies rr <= #[trigger] m.lg_runs[j] by {
                if j > i {
                    assert(m.lg_runs[i as int] < m.lg_runs[j]);
                }
            }
            lemma_gap(m, i as int, r, rr);
            assert forall|t: int| r <= t < rr implies (#[trigger] m.r_lens[t] as int) < kmin by {
                assert(m.r_lens[t] < m.lg_max);
            }
            lemma_skip_range(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int,
                qm as int, c.thr as int, kmin as int, r, rr, pos, g as int, ge as int, buf@, len as int);
            // the run's rows end inside the chunk
            assert(rs(m, rr + 1) == rs(m, rr) + m.r_lens[rr]);
            lemma_rs_mono(m, rr + 1, r_hi as int);
            lemma_run_len_pos(m, rr);
            reveal(rscan_inv);
        }
        let start = c.lg_starts[i] as usize;
        let e = start + lmax;
        if (start as u64) >= ge {
            // the run starts in a later block: move the cursor and take that block's limit
            let (g2, ge2) = cursor_to(start, g, ge, bs, Ghost(m.l_n));
            proof {
                lemma_div_in(start as int, m.l_bs, g2 as int);
                lemma_block_bound(start as int, m.l_bs, m.l_n, m.l_nb);
                lemma_rscan_cursor(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int,
                    qm as int, rr, start as int, g as int, ge as int, buf@, len as int, g2 as int, ge2 as int);
            }
            g = g2;
            ge = ge2;
            qb = c.l_qty_b[g];
            proof {
                assert(-9223372036854775808 * 256 <= (lmax as int) * (qb as int) <= 9223372036854775807 * 256)
                    by (nonlinear_arith) requires 0 <= lmax <= 256, -9223372036854775808 <= qb <= 9223372036854775807;
            }
            lim = c.thr - (lmax as i128) * (qb as i128);
        }
        proof {
            // the cursor's block holds the run's start
            reveal(rscan_inv);
            assert(g * m.l_bs <= start);
            if g >= m.l_nb {
                assert(g * m.l_bs >= m.l_nb * m.l_bs) by (nonlinear_arith) requires g >= m.l_nb, m.l_bs >= 1;
            }
        }
        proof {
            assert((e - start) * qb == lmax * qb) by (nonlinear_arith) requires e - start == lmax;
        }
        if (e as u64) <= ge {
            len = long_step(c, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, start, e, g, ge, qb, lim, i, buf, len,
                Ghost(m), Ghost(p), Ghost(rr));
        } else {
            // the run crosses a block end (rare): the general step
            let rx = c.lg_runs[i] as usize;
            let st = cand_step(c, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, rx, start, e, g, ge, buf, len, Ghost(m), Ghost(p));
            g = st.0;
            ge = st.1;
            len = st.2;
            if g < c.l_nb {
                qb = c.l_qty_b[g];
                proof {
                    assert(-9223372036854775808 * 256 <= (lmax as int) * (qb as int) <= 9223372036854775807 * 256)
                        by (nonlinear_arith) requires 0 <= lmax <= 256, -9223372036854775808 <= qb <= 9223372036854775807;
                }
                lim = c.thr - (lmax as i128) * (qb as i128);
            }
        }
        proof {
            pos = e as int;
        }
        let ghost r0 = r;
        proof {
            r = rr + 1;
        }
        i = i + 1;
        proof {
            assert forall|j: int| 0 <= j < i implies #[trigger] m.lg_runs[j] < r by {
                if j < i - 1 {
                    assert(m.lg_runs[j] < r0);
                }
            }
            assert forall|j: int| i <= j < n implies r <= #[trigger] m.lg_runs[j] by {
                assert(m.lg_runs[i - 1] < m.lg_runs[j]);
            }
        }
    }
    proof {
        // the runs after the chunk's last listed run are shorter too
        lemma_gap(m, i_hi as int, r, r_hi as int);
        assert forall|t: int| r <= t < r_hi implies (#[trigger] m.r_lens[t] as int) < kmin by {
            reveal(runs_ok);
            assert(m.r_lens[t] < m.lg_max);
        }
        lemma_skip_range(m, p, o_lo as int, o_hi as int, l_lo as int, l_hi as int, r_lo as int, r_hi as int,
            qm as int, c.thr as int, kmin as int, r, r_hi as int, pos, g as int, ge as int, buf@, len as int);
        reveal(rscan_inv);
    }
    len
}

} // verus!
