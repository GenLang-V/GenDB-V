//! Key runs of a lineitem chunk, built without data-dependent branches. A chunk is at most `CH` consecutive rows
//! `[j0, e)` of one fast lineitem block (`kernel::fast_block`). `build_runs` splits it into runs of equal
//! `l_orderkey`: run `i` covers the rows `[st[i], st[i + 1])` (a ghost list of starts). One buffer `gt` of slots
//! `(key, revenue, |revenue|, count)` holds, in slot `i + 1`, the key of run `i` and the running totals of the
//! returned rows of the chunk up to the run's end; slot `i` holds the totals of the rows `[j0, st[i])` (`run_ok`), so
//! run `i` sums to the difference of slots `i + 1` and `i`. Every row adds to the totals and writes the slot of its
//! run (one store); a new key only advances the slot index by one (an add of the comparison), so the loop has no
//! branch on the data.
//! Runs need not be maximal (a key may continue in the next chunk); the consumer merges runs of one order.
use vstd::prelude::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::work::put;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;
use super::recs::*;

verus! {

/// Most rows of one chunk.
pub const CH: usize = 4096;

/// Slots of the run buffers (`CH` runs and the total before the first).
pub const CH_SLOTS: usize = 4097;

/// A run slot: key, revenue, absolute revenue and count (totals from the chunk start).
pub type Slot = (i64, i64, u64, u64);

/// Bound of one row's revenue coefficient in a fast block (`row_arg64`).
pub const ARG64: u64 = 0x1000_0000_0000;

/// Per-row terms of the returned rows: count, revenue and absolute revenue (any key).
pub open spec fn fcnt_f(m: M) -> spec_fn(int) -> int {
    |j: int| if lflag(m, j) == r_text() { 1int } else { 0int }
}

pub open spec fn fsum_f(m: M) -> spec_fn(int) -> int {
    |j: int| if lflag(m, j) == r_text() { larg(m, j) } else { 0int }
}

pub open spec fn fabs_f(m: M) -> spec_fn(int) -> int {
    |j: int| if lflag(m, j) == r_text() { abs(larg(m, j)) } else { 0int }
}

/// The running totals of the rows `[j0, b)`, inside `i64` (at most `CH` rows of fast blocks).
pub open spec fn tot_ok(m: M, j0: int, b: int, n: u64, s: i64, ab: u64) -> bool {
    &&& n as int == dsum(fcnt_f(m), j0, b)
    &&& s as int == dsum(fsum_f(m), j0, b)
    &&& ab as int == dsum(fabs_f(m), j0, b)
    &&& n as int <= b - j0
    &&& -(ab as int) <= s as int <= ab as int
    &&& ab as int <= (b - j0) * ARG64
}

/// Run `i` is nonempty (a named step, so the ordering of the starts gives no matching loop).
pub open spec fn lt_next(st: Seq<int>, i: int) -> bool {
    st[i] < st[i + 1]
}

/// Every row of `[a, b)` has key `k`.
#[verifier::opaque]
pub open spec fn keys_in(m: M, k: int, a: int, b: int) -> bool {
    forall|t: int| a <= t < b ==> #[trigger] lkey(m, t) == k
}

/// A row of a key range has the range's key.
pub proof fn lemma_keys_at(m: M, k: int, a: int, b: int, t: int)
    requires keys_in(m, k, a, b), a <= t < b,
    ensures lkey(m, t) == k,
{
    reveal(keys_in);
}

/// The runs of the chunk `[j0, e)`: `ng` runs with starts `st` (`st[ng] == e`), each of one key, and the running
/// totals at every start.
pub open spec fn run_ok(m: M, gt: Seq<Slot>, st: Seq<int>, ng: int, j0: int, e: int) -> bool {
    &&& 1 <= ng && ng < gt.len()
    &&& st.len() == ng + 1
    &&& st[0] == j0 && st[ng] == e
    &&& forall|i: int| 0 <= i <= ng ==> j0 <= #[trigger] st[i] <= e
    &&& forall|i: int| 0 <= i < ng ==> #[trigger] lt_next(st, i)
    &&& forall|i: int| 0 <= i < ng ==> #[trigger] keys_in(m, gt[i + 1].0 as int, st[i], st[i + 1])
    &&& forall|i: int| 0 <= i <= ng ==> #[trigger] tot_ok(m, j0, st[i], gt[i].3, gt[i].1, gt[i].2)
}

/// On rows of the order's key the order's terms are the returned-row terms.
pub proof fn lemma_flag_terms(m: M, q: int, a: int, b: int)
    requires
        0 <= a <= b,
        forall|t: int| a <= t < b ==> #[trigger] lkey(m, t) == okey(m, q),
    ensures
        dsum(lcnt_f(m, q), a, b) == dsum(fcnt_f(m), a, b),
        dsum(lsum_f(m, q), a, b) == dsum(fsum_f(m), a, b),
        dsum(labs_f(m, q), a, b) == dsum(fabs_f(m), a, b),
    decreases b - a,
{
    if a < b {
        lemma_flag_terms(m, q, a, b - 1);
        assert(lkey(m, b - 1) == okey(m, q));
        lemma_dsum_step(lcnt_f(m, q), a, b - 1);
        lemma_dsum_step(lsum_f(m, q), a, b - 1);
        lemma_dsum_step(labs_f(m, q), a, b - 1);
        lemma_dsum_step(fcnt_f(m), a, b - 1);
        lemma_dsum_step(fsum_f(m), a, b - 1);
        lemma_dsum_step(fabs_f(m), a, b - 1);
    }
}

/// One row `j` added to the running totals of `[j0, j)`.
proof fn lemma_tot_step(m: M, j0: int, j: int, n: u64, s: i64, ab: u64, hit: bool, t: int, tm: int)
    requires
        tot_ok(m, j0, j, n, s, ab),
        0 <= j0 <= j,
        j - j0 < CH,
        hit == (lflag(m, j) == r_text()),
        t == larg(m, j),
        -(ARG64 as int) < t < ARG64,
        tm == if hit { t } else { 0 },
    ensures
        tot_ok(m, j0, j + 1, (n + if hit { 1u64 } else { 0u64 }) as u64, (s + tm) as i64, (ab + abs(tm)) as u64),
{
    lemma_dsum_step(fcnt_f(m), j0, j);
    lemma_dsum_step(fsum_f(m), j0, j);
    lemma_dsum_step(fabs_f(m), j0, j);
    assert((j + 1 - j0) * ARG64 == (j - j0) * ARG64 + ARG64);
    assert((j - j0) * ARG64 <= CH * ARG64) by (nonlinear_arith) requires j - j0 < CH;
}

/// The runs before slot `cur` are closed: increasing starts, one key per run, and the running totals at every start
/// up to `st[cur]`.
#[verifier::opaque]
pub open spec fn closed_ok(m: M, gt: Seq<Slot>, st: Seq<int>, cur: int, j0: int) -> bool {
    &&& forall|i: int| 0 <= i < cur ==> #[trigger] lt_next(st, i)
    &&& forall|i: int| 0 <= i < cur ==> #[trigger] keys_in(m, gt[i + 1].0 as int, st[i], st[i + 1])
    &&& forall|i: int| 0 <= i <= cur ==> #[trigger] tot_ok(m, j0, st[i], gt[i].3, gt[i].1, gt[i].2)
}

/// One row `j` of key `k` written to the slots: with `step == 1` the open run (key `prev`, rows `[st[cur], j)`, its
/// end total already in slot `cur + 1`) closes and row `j` opens run `cur + 1`.
proof fn lemma_build_step(m: M, gt0: Seq<Slot>, st0: Seq<int>, gt: Seq<Slot>, st: Seq<int>, cur: int, step: int,
    j0: int, j: int, prev: i64, k: i64, n: u64, s: i64, a: u64, n2: u64, s2: i64, a2: u64)
    requires
        closed_ok(m, gt0, st0, cur, j0),
        st0.len() == cur + 1, 0 <= cur, st0[cur] <= j,
        step == 0 || step == 1,
        step == 1 ==> j > j0 && st0[cur] < j && prev != k,
        step == 0 ==> prev == k,
        j > j0 ==> gt0[cur + 1] == (prev, s, a, n),
        keys_in(m, prev as int, st0[cur], j),
        tot_ok(m, j0, j, n, s, a),
        gt0.len() > cur + 2,
        st == if step == 1 { st0.push(j) } else { st0 },
        gt == gt0.update(cur + step + 1, (k, s2, a2, n2)),
    ensures
        closed_ok(m, gt, st, cur + step, j0),
{
    reveal(closed_ok);
    let nxt = cur + step;
    assert forall|i: int| 0 <= i < nxt implies #[trigger] lt_next(st, i) by {
        if i < cur {
            assert(lt_next(st0, i));
        } else {
            assert(st[i] == st0[cur] && st[i + 1] == j);
        }
    }
    assert forall|i: int| 0 <= i < nxt implies #[trigger] keys_in(m, gt[i + 1].0 as int, st[i], st[i + 1]) by {
        if i < cur {
            assert(keys_in(m, gt0[i + 1].0 as int, st0[i], st0[i + 1]));
            assert(gt[i + 1] == gt0[i + 1]);
        } else {
            assert(st[i] == st0[cur] && st[i + 1] == j);
            assert(gt[cur + 1] == gt0[cur + 1]);
        }
    }
    assert forall|i: int| 0 <= i <= nxt implies #[trigger] tot_ok(m, j0, st[i], gt[i].3, gt[i].1, gt[i].2) by {
        if i <= cur {
            assert(tot_ok(m, j0, st0[i], gt0[i].3, gt0[i].1, gt0[i].2));
            assert(st[i] == st0[i] && gt[i] == gt0[i]);
        } else {
            assert(st[i] == j);
            assert(gt[i] == gt0[cur + 1]);
        }
    }
}

/// The runs of the rows `[j0, e)` of fast block `g` (`e - j0 <= CH`, key base `kb`, returned-flag target `tgt`, price
/// and discount bases `pb`, `db`) into the slots `0..=ng` of `gt`; returns `ng` and the ghost starts.
pub fn build_runs(c: &Cols, j0: usize, e: usize, kb: i64, tgt: u16, pb: i64, db: i64,
    gt: &mut Vec<Slot>, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(g): Ghost<int>) -> (r: (usize, Ghost<Seq<int>>))
    requires
        cols_ok(*c, m, p), model_ok(m),
        0 <= g < m.l_nb,
        g * m.l_bs <= j0 < e <= (g + 1) * m.l_bs,
        e <= m.l_n,
        e - j0 <= CH,
        fast_block(m, g), kb == m.l_key_b[g], pb == m.l_price_b[g], db == m.l_disc_b[g],
        forall|t: int| 0 <= t < m.l_n && t / m.l_bs == g ==> (#[trigger] lflag(m, t) == r_text()) == (m.l_rf_c[t] as int == tgt as int),
        old(gt)@.len() >= CH_SLOTS,
    ensures
        final(gt)@.len() == old(gt)@.len(),
        run_ok(m, final(gt)@, r.1@, r.0 as int, j0 as int, e as int),
    no_unwind
{
    proof {
        lemma_div_in(j0 as int, m.l_bs, g);
        assert(in_i64(lkey(m, j0 as int)));
    }
    let mut prev: i64 = kb + c.l_key_c[j0] as i64;
    let mut cur: usize = 0;
    let mut s: i64 = 0;
    let mut a: u64 = 0;
    let mut n: u64 = 0;
    let mut j = j0;
    let ghost mut st: Seq<int> = seq![j0 as int];
    put(gt, 0, (0, 0, 0, 0));
    proof {
        reveal(closed_ok);
        reveal(keys_in);
        assert(tot_ok(m, j0 as int, st[0], gt@[0].3, gt@[0].1, gt@[0].2));
    }
    while j < e
        invariant
            cols_ok(*c, m, p), model_ok(m),
            0 <= g < m.l_nb,
            g * m.l_bs <= j0 <= j <= e <= (g + 1) * m.l_bs,
            e <= m.l_n,
            e - j0 <= CH,
            fast_block(m, g), kb == m.l_key_b[g], pb == m.l_price_b[g], db == m.l_disc_b[g],
            forall|t: int| 0 <= t < m.l_n && t / m.l_bs == g ==> (#[trigger] lflag(m, t) == r_text()) == (m.l_rf_c[t] as int == tgt as int),
            gt@.len() == old(gt)@.len(),
            gt@.len() >= CH_SLOTS,
            st.len() == cur + 1,
            st[0] == j0,
            forall|i: int| 0 <= i <= cur ==> j0 <= #[trigger] st[i] <= j,
            cur <= j - j0,
            j > j0 ==> cur < j - j0,
            st[cur as int] <= j,
            j > j0 ==> st[cur as int] < j,
            prev as int == lkey(m, st[cur as int]),
            closed_ok(m, gt@, st, cur as int, j0 as int),
            keys_in(m, prev as int, st[cur as int], j as int),
            tot_ok(m, j0 as int, j as int, n, s, a),
            j > j0 ==> gt@[cur + 1] == (prev, s, a, n),
        decreases e - j,
    {
        proof {
            lemma_div_in(j as int, m.l_bs, g);
            assert(in_i64(lkey(m, j as int)));
        }
        let k = kb + c.l_key_c[j] as i64;
        let step: usize = if k != prev { 1 } else { 0 };
        let hit = c.l_rf_c[j] as u16 == tgt;
        let t = row_arg64(c, j, pb, db, Ghost(m), Ghost(p), Ghost(g));
        let tm: i64 = if hit { t } else { 0 };
        let ta: u64 = if tm < 0 { (0 - tm) as u64 } else { tm as u64 };
        let hn: u64 = if hit { 1 } else { 0 };
        let ghost st0 = st;
        let ghost gt0 = gt@;
        let ghost (n0, s0, a0) = (n, s, a);
        proof {
            lemma_tot_step(m, j0 as int, j as int, n, s, a, hit, t as int, tm as int);
            if step == 1 {
                assert(j > j0);
                st = st.push(j as int);
            }
        }
        let nxt: usize = cur + step;
        s = s + tm;
        a = a + ta;
        n = n + hn;
        put(gt, nxt + 1, (k, s, a, n));
        proof {
            lemma_build_step(m, gt0, st0, gt@, st, cur as int, step as int, j0 as int, j as int, prev, k, n0, s0, a0,
                n, s, a);
            reveal(keys_in);
            assert forall|t2: int| st[nxt as int] <= t2 < j + 1 implies #[trigger] lkey(m, t2) == k as int by {
                if step == 0 {
                    if t2 < j {
                        assert(lkey(m, t2) == prev as int);
                    }
                }
            }
        }
        proof {
            assert forall|i: int| 0 <= i <= nxt implies j0 <= #[trigger] st[i] <= j + 1 by {
                if i <= cur {
                    assert(j0 <= st0[i] <= j);
                }
            }
        }
        cur = nxt;
        prev = k;
        j = j + 1;
    }
    let ghost stf = st.push(e as int);
    proof {
        reveal(closed_ok);
        assert forall|i: int| 0 <= i <= cur + 1 implies j0 <= #[trigger] stf[i] <= e by {
            if i <= cur {
                assert(j0 <= st[i] <= j);
            }
        }
        assert forall|i: int| 0 <= i < cur + 1 implies #[trigger] lt_next(stf, i) by {
            if i < cur {
                assert(lt_next(st, i));
            }
        }
        assert forall|i: int| 0 <= i < cur + 1 implies #[trigger] keys_in(m, gt@[i + 1].0 as int, stf[i], stf[i + 1]) by {
            if i < cur {
                assert(keys_in(m, gt@[i + 1].0 as int, st[i], st[i + 1]));
            }
        }
        assert forall|i: int| 0 <= i <= cur + 1 implies #[trigger] tot_ok(m, j0 as int, stf[i], gt@[i].3, gt@[i].1, gt@[i].2) by {
            if i <= cur {
                assert(tot_ok(m, j0 as int, st[i], gt@[i].3, gt@[i].1, gt@[i].2));
            }
        }
    }
    (cur + 1, Ghost(stf))
}

/// Run `i` of the chunk (rows `[st[i], st[i + 1])`, all of the order at `q`) added to the order's sums over
/// `[j0, st[i])`.
#[inline(always)]
pub fn acc_run(cnt: u64, sum: i128, ab: u128, ovf: bool, gt: &Vec<Slot>, i: usize,
    Ghost(m): Ghost<M>, Ghost(q): Ghost<int>, Ghost(j0): Ghost<int>, Ghost(c0): Ghost<int>, Ghost(j1): Ghost<int>,
    Ghost(j2): Ghost<int>) -> (r: (u64, i128, u128, bool))
    requires
        acc_ok(m, q, j0, j1, cnt, sum, ab, ovf),
        i < CH, i + 1 < gt@.len(),
        tot_ok(m, c0, j1, gt@[i as int].3, gt@[i as int].1, gt@[i as int].2),
        tot_ok(m, c0, j2, gt@[i + 1].3, gt@[i + 1].1, gt@[i + 1].2),
        0 <= j0 <= j1, 0 <= c0 <= j1 <= j2,
        j2 - c0 <= CH,
        j2 <= u64::MAX,
        forall|t: int| j1 <= t < j2 ==> #[trigger] lkey(m, t) == okey(m, q),
    ensures
        acc_ok(m, q, j0, j2, r.0, r.1, r.2, r.3),
    no_unwind
{
    proof {
        lemma_flag_terms(m, q, j1, j2);
        lemma_dsum_join(fcnt_f(m), c0, j1, j2);
        lemma_dsum_join(fsum_f(m), c0, j1, j2);
        lemma_dsum_join(fabs_f(m), c0, j1, j2);
        lemma_dsum_join(lcnt_f(m, q), j0, j1, j2);
        lemma_dsum_join(lsum_f(m, q), j0, j1, j2);
        lemma_dsum_join(labs_f(m, q), j0, j1, j2);
        assert forall|t: int| j1 <= t < j2 implies abs(#[trigger] fsum_f(m)(t)) <= fabs_f(m)(t) by {}
        lemma_dsum_abs(fsum_f(m), fabs_f(m), j1, j2);
        assert forall|t: int| j1 <= t < j2 implies #[trigger] fcnt_f(m)(t) <= 1 by {}
        assert forall|t: int| j1 <= t < j2 implies #[trigger] fcnt_f(m)(t) >= 0 by {}
        lemma_dsum_nonneg(fcnt_f(m), j1, j2);
        lemma_cnt_le(m, j1, j2);
        assert((j2 - c0) * ARG64 <= CH * ARG64) by (nonlinear_arith) requires j2 - c0 <= CH;
        assert((j1 - c0) * ARG64 <= CH * ARG64) by (nonlinear_arith) requires j1 - c0 <= CH;
    }
    let x1 = gt[i + 1];
    let x0 = gt[i];
    let n = x1.3 - x0.3;
    let s = x1.1 - x0.1;
    let a = x1.2 - x0.2;
    let cnt1 = cnt + n;
    if ovf {
        return (cnt1, sum, ab, true);
    }
    let na: u128 = ab + a as u128;
    if na > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
        (cnt1, sum, ab, true)
    } else {
        (cnt1, sum + s as i128, na, false)
    }
}

/// At most one returned row per row.
proof fn lemma_cnt_le(m: M, a: int, b: int)
    requires 0 <= a <= b,
    ensures dsum(fcnt_f(m), a, b) <= b - a,
    decreases b - a,
{
    if a < b {
        lemma_cnt_le(m, a, b - 1);
        lemma_dsum_step(fcnt_f(m), a, b - 1);
    }
}

} // verus!
