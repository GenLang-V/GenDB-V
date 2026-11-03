//! The chunk kernel over the l_orderkey run starts of storage `li_okruns` (`m.l_st`), used when customer keys are
//! dense and the segment is one U8 code (`Cols::seg_fast`). Orders are taken in batches inside one orders block:
//! - phase 1 is `select::select` (the batch's orders dated before the day whose customer has the segment);
//! - the batch's runs are its orders' (run `t` = lineitem rows `[l_st[t], l_st[t + 1])` of the order at stored
//!   position `t`) when the first and the last run of the batch start with their order's key: under co-clustering
//!   the order positions of consecutive runs strictly increase, so every run between is its order's
//!   (`lemma_aligned_range`, `lemma_run_rows`). Otherwise the kernel gives up (`aligned` false) and the caller runs
//!   `select::run_sel`;
//! - phase 2 reads each listed order's run directly. A run inside one lineitem block, of at most `DIR_RUN_CAP` rows,
//!   with small price and discount bases is summed branch-free in `i64` (`dir_sums`); any other run by
//!   `kernel::fast_sums`. An order whose revenue is below the 10th of a full top 10 is skipped before its
//!   candidate row is read.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::expr::i128_max;
use super::common::isum::*;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;
use super::select::*;

verus! {

/// Most rows of a run summed in `i64` by `dir_sums`.
pub const DIR_RUN_CAP: usize = 256;

/// Bound of one row's SUM argument on the `i64` path (`2^54`).
pub open spec fn arg_cap() -> int { 0x40_0000_0000_0000 }

/// The lineitem rows of the order at `t` are exactly `[a, b)`.
pub open spec fn rows_exact(m: M, t: int, a: int, b: int) -> bool {
    &&& 0 <= a <= b <= m.l_n
    &&& forall|x: int| a <= x < b ==> #[trigger] lkey(m, x) == okey(m, t)
    &&& forall|x: int| 0 <= x < m.l_n && (x < a || x >= b) ==> #[trigger] lkey(m, x) != okey(m, t)
}

/// A row after run `t` (whose first row has the key of the order at `t`) has another key.
proof fn lemma_after_run(m: M, t: int, x: int)
    requires
        model_ok(m), m.cluster == 1,
        0 <= t < m.o_n, t + 1 < m.l_st.len(),
        lkey(m, m.l_st[t] as int) == okey(m, t),
        m.l_st[t + 1] <= x < m.l_n,
    ensures
        lkey(m, x) != okey(m, t),
{
    let a = m.l_st[t] as int;
    let b = m.l_st[t + 1] as int;
    assert(run_ok(m, t));
    assert(lkey(m, b - 1) == lkey(m, a));
    if lkey(m, x) == okey(m, t) {
        // the order position is t at b - 1 and at x, so also at b, whose key differs from b - 1's
        lemma_lpos_key(m, t, x);
        lemma_lpos_key(m, t, b - 1);
        lemma_lpos_mono(m, b - 1, b);
        lemma_lpos_mono(m, b, x);
        lemma_lpos_key(m, t, b);
    }
}

/// A row before run `t` (whose first row has the key of the order at `t`) has another key.
proof fn lemma_before_run(m: M, t: int, x: int)
    requires
        model_ok(m), m.cluster == 1,
        0 <= t < m.o_n, t + 1 < m.l_st.len(),
        lkey(m, m.l_st[t] as int) == okey(m, t),
        0 <= x < m.l_st[t],
    ensures
        lkey(m, x) != okey(m, t),
{
    let a = m.l_st[t] as int;
    // a > 0, so run t - 1 ends at a and the key changes there
    assert(t >= 1) by {
        if t == 0 {
            assert(m.l_st[0] == 0);
        }
    }
    assert(run_ok(m, t));
    assert(run_ok(m, t - 1));
    if lkey(m, x) == okey(m, t) {
        lemma_lpos_key(m, t, x);
        lemma_lpos_key(m, t, a);
        lemma_lpos_mono(m, x, a - 1);
        lemma_lpos_mono(m, a - 1, a);
        lemma_lpos_key(m, t, a - 1);
    }
}

/// Run `t` whose first row has the key of the order at `t` holds exactly that order's rows (co-clustering).
pub proof fn lemma_run_rows(m: M, t: int)
    requires
        model_ok(m), m.cluster == 1,
        0 <= t < m.o_n,
        t + 1 < m.l_st.len(),
        lkey(m, m.l_st[t] as int) == okey(m, t),
    ensures
        rows_exact(m, t, m.l_st[t] as int, m.l_st[t + 1] as int),
{
    let a = m.l_st[t] as int;
    let b = m.l_st[t + 1] as int;
    assert(run_ok(m, t));
    assert forall|x: int| 0 <= x < m.l_n && (x < a || x >= b) implies #[trigger] lkey(m, x) != okey(m, t) by {
        if x < a {
            lemma_before_run(m, t, x);
        } else {
            lemma_after_run(m, t, x);
        }
    }
}

/// Run starts increase.
proof fn lemma_st_mono(m: M, i: int, j: int)
    requires model_ok(m), 0 <= i <= j < m.l_st.len(),
    ensures m.l_st[i] <= m.l_st[j],
    decreases j - i,
{
    if i < j {
        lemma_st_mono(m, i, j - 1);
        assert(run_ok(m, j - 1));
    }
}

/// The order position of the first row of run `k`.
pub open spec fn run_pos(m: M, k: int) -> int {
    lpos(m, m.l_st[k] as int)
}

/// Consecutive runs (both inside the table) belong to strictly increasing order positions while those are orders.
proof fn lemma_pos_step(m: M, k: int)
    requires
        model_ok(m), m.cluster == 1,
        0 <= k, k + 2 < m.l_st.len(),
        run_pos(m, k + 1) < m.o_n,
    ensures
        run_pos(m, k + 1) > run_pos(m, k),
{
    let a = m.l_st[k] as int;
    let b = m.l_st[k + 1] as int;
    assert(run_ok(m, k));
    assert(run_ok(m, k + 1));
    assert(lkey(m, b - 1) == lkey(m, a));
    lemma_lpos_mono(m, a, b - 1);
    lemma_lpos_mono(m, b - 1, b);
    crate::agent::facts::lemma_opos(m, lkey(m, b));
    crate::agent::facts::lemma_opos(m, lkey(m, b - 1));
}

/// Order positions of runs `[i, j]` grow by at least one per run (run `r` is the order at `r`, `j <= r`).
proof fn lemma_pos_gap(m: M, i: int, j: int, r: int)
    requires
        model_ok(m), m.cluster == 1,
        0 <= i <= j <= r, r + 1 < m.l_st.len(),
        r < m.o_n, run_pos(m, r) == r,
    ensures
        run_pos(m, j) >= run_pos(m, i) + (j - i),
    decreases j - i,
{
    if i < j {
        lemma_pos_gap(m, i, j - 1, r);
        lemma_pos_gap_step(m, j, r);
    }
}

/// One step of `lemma_pos_gap`: runs up to `r` belong to orders, so the position grows from run `j - 1` to `j`.
proof fn lemma_pos_gap_step(m: M, j: int, r: int)
    requires
        model_ok(m), m.cluster == 1,
        1 <= j <= r, r + 1 < m.l_st.len(),
        r < m.o_n, run_pos(m, r) == r,
    ensures
        run_pos(m, j) > run_pos(m, j - 1),
{
    lemma_st_mono(m, j, r);
    assert(run_ok(m, r));
    lemma_lpos_mono(m, m.l_st[j] as int, m.l_st[r] as int);
    lemma_pos_step(m, j - 1);
}

/// When the first and the last run of `[q, r]` are the orders at `q` and `r`, every run between is its order's.
pub proof fn lemma_aligned_range(m: M, q: int, r: int)
    requires
        model_ok(m), m.cluster == 1,
        0 <= q <= r < m.o_n, r + 1 < m.l_st.len(),
        lkey(m, m.l_st[q] as int) == okey(m, q),
        lkey(m, m.l_st[r] as int) == okey(m, r),
    ensures
        forall|k: int| q <= k <= r ==> #[trigger] lkey(m, m.l_st[k] as int) == okey(m, k),
{
    assert(run_ok(m, q));
    assert(run_ok(m, r));
    lemma_lpos_key(m, q, m.l_st[q] as int);
    lemma_lpos_key(m, r, m.l_st[r] as int);
    assert forall|k: int| q <= k <= r implies #[trigger] lkey(m, m.l_st[k] as int) == okey(m, k) by {
        lemma_pos_gap(m, q, k, r);
        lemma_pos_gap(m, k, r, r);
        assert(run_ok(m, k));
        lemma_lpos_key(m, k, m.l_st[k] as int);
    }
}

/// Exact rows give the run's lower bound and the rows after it.
proof fn lemma_rows_lb(m: M, t: int, a: int, b: int)
    requires
        model_ok(m), m.cluster == 1,
        0 <= t < m.o_n,
        rows_exact(m, t, a, b),
        a < b,
    ensures
        lb_ok(m, t, a),
        forall|x: int| b <= x < m.l_n ==> #[trigger] lpos(m, x) > t,
{
    lemma_lpos_key(m, t, a);
    assert forall|x: int| 0 <= x < a implies #[trigger] lpos(m, x) < t by {
        lemma_lpos_key(m, t, x);
        lemma_lpos_mono(m, x, a);
    }
    assert forall|x: int| a <= x < m.l_n implies #[trigger] lpos(m, x) >= t by {
        lemma_lpos_mono(m, a, x);
    }
    assert forall|x: int| b <= x < m.l_n implies #[trigger] lpos(m, x) > t by {
        lemma_lpos_key(m, t, x);
        lemma_lpos_mono(m, a, x);
    }
}

/// A shift by 16 bits is a division by the block size 65536.
proof fn lemma_shr16(x: u64)
    ensures x >> 16u64 == x / 0x10000u64,
{
    assert(x >> 16u64 == x / 0x10000u64) by (bit_vector);
}

/// The block of row `x` and the end of that block: `lcur_ok`, with `x` inside the block.
fn block_of(c: &Cols, x: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (usize, u64))
    requires cols_ok(*c, m, p), model_ok(m), x < m.l_n,
    ensures
        lcur_ok(m, x as int, r.0 as int, r.1 as int),
        x < r.1,
        r.0 < m.l_nb,
    no_unwind
{
    let x64 = x as u64;
    let g64 = if c.l_bs == 0x10000 {
        proof { lemma_shr16(x64); }
        x64 >> 16u64
    } else {
        x64 / c.l_bs
    };
    proof {
        assert(g64 == x64 / c.l_bs);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, m.l_bs);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, m.l_bs);
        assert(m.l_bs * g64 == g64 * m.l_bs) by (nonlinear_arith);
        assert((g64 + 1) * m.l_bs == g64 * m.l_bs + m.l_bs) by (nonlinear_arith);
        assert(g64 <= x) by (nonlinear_arith) requires g64 * m.l_bs <= x, m.l_bs >= 1, g64 >= 0;
        lemma_block_bound(x as int, m.l_bs, m.l_n, m.l_nb);
    }
    (g64 as usize, (g64 + 1) * c.l_bs)
}

/// Partial sums of the order at `t` over rows `[a, x)` on the `i64` path.
pub open spec fn dacc_ok(m: M, p: QP, t: int, a: int, x: int, cnt: u32, sum: i64) -> bool {
    &&& cnt as int == dsum(lcnt_f(m, p, t), a, x)
    &&& cnt as int <= x - a
    &&& sum as int == dsum(lsum_f(m, p, t), a, x)
    &&& 0 <= dsum(labs_f(m, p, t), a, x) <= (x - a) * arg_cap()
    &&& -dsum(labs_f(m, p, t), a, x) <= sum as int <= dsum(labs_f(m, p, t), a, x)
}

/// One more row: a hit with argument `v` (`|v| < 2^54`), or not a hit.
proof fn lemma_dacc_step(m: M, p: QP, t: int, a: int, x: int, cnt: u32, sum: i64, hit: bool, v: int)
    requires
        dacc_ok(m, p, t, a, x, cnt, sum),
        0 <= a <= x,
        hit == lhit(m, p, t, x),
        hit ==> v == larg(m, x),
        abs(v) < arg_cap(),
    ensures
        dsum(lcnt_f(m, p, t), a, x + 1) == cnt + if hit { 1int } else { 0int },
        dsum(lsum_f(m, p, t), a, x + 1) == sum + if hit { v } else { 0int },
        0 <= dsum(labs_f(m, p, t), a, x + 1) <= (x + 1 - a) * arg_cap(),
        -dsum(labs_f(m, p, t), a, x + 1) <= sum + (if hit { v } else { 0int }) <= dsum(labs_f(m, p, t), a, x + 1),
{
    lemma_terms_at(m, p, t, x);
    lemma_isum_step(x, lcnt_f(m, p, t));
    lemma_isum_step(x, lsum_f(m, p, t));
    lemma_isum_step(x, labs_f(m, p, t));
    assert((x + 1 - a) * arg_cap() == (x - a) * arg_cap() + arg_cap()) by (nonlinear_arith);
}

/// The SUM argument of one row from its price and discount: `(pb + pc) * (dm - dc)` stays under `2^54`.
proof fn lemma_small_arg(pb: int, pc: int, dm: int, dc: int)
    requires
        -0x8000_0000 <= pb <= 0x8000_0000, 0 <= pc < 0x1_0000_0000,
        -0x10_0000 + 100 <= dm <= 0x10_0000 + 100, 0 <= dc < 256,
    ensures
        abs((pb + pc) * (dm - dc)) < arg_cap(),
{
    let x = abs(pb + pc);
    let y = abs(dm - dc);
    assert(abs((pb + pc) * (dm - dc)) == x * y) by (nonlinear_arith) requires x == abs(pb + pc), y == abs(dm - dc);
    assert(x * y < 0x40_0000_0000_0000) by (nonlinear_arith)
        requires 0 <= x < 0x2_0000_0000, 0 <= y < 0x20_0000;
}

/// The run `[a, b)` of the order at `t`, inside lineitem block `g`, summed branch-free in `i64` when the run has at
/// most `DIR_RUN_CAP` rows and the block's price and discount bases are small (`Some((count, revenue))`).
pub fn dir_sums(c: &Cols, a: usize, b: usize, g: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(t): Ghost<int>)
    -> (r: Option<(u32, i64)>)
    requires
        cols_ok(*c, m, p), model_ok(m),
        0 <= t < m.o_n,
        rows_exact(m, t, a as int, b as int),
        a < b,
        g < m.l_nb,
        g * m.l_bs <= a,
        b <= (g + 1) * m.l_bs,
    ensures
        r matches Some(s) ==> {
            &&& s.0 as int == lcnt(m, p, t)
            &&& s.1 as int == lsum(m, p, t)
            &&& labs(m, p, t) <= i128_max()
        },
    no_unwind
{
    if b - a > DIR_RUN_CAP {
        return None;
    }
    let pb = c.l_price_b[g];
    let db = c.l_disc_b[g];
    if pb < -0x8000_0000 || pb > 0x8000_0000 || db < -0x10_0000 || db > 0x10_0000 {
        return None;
    }
    let sb = c.l_ship_b[g];
    // a row ships after the day exactly when its U16 code exceeds `thr` (the day minus the base, clamped)
    let sday: i128 = c.day as i128 - sb as i128;
    let thr: i64 = if sday < -1 { -1 } else if sday > 0xffff { 0xffff } else { sday as i64 };
    let dm: i64 = 100 - db;
    let mut cnt: u32 = 0;
    let mut sum: i64 = 0;
    let mut x = a;
    proof {
        assert(dsum(lcnt_f(m, p, t), a as int, a as int) == 0);
        assert(dsum(lsum_f(m, p, t), a as int, a as int) == 0);
        assert(dsum(labs_f(m, p, t), a as int, a as int) == 0);
    }
    while x < b
        invariant
            cols_ok(*c, m, p), model_ok(m),
            0 <= t < m.o_n,
            rows_exact(m, t, a as int, b as int),
            a <= x <= b, b - a <= DIR_RUN_CAP,
            g < m.l_nb, g * m.l_bs <= a, b <= (g + 1) * m.l_bs,
            pb == m.l_price_b[g as int], db == m.l_disc_b[g as int], sb == m.l_ship_b[g as int],
            -0x8000_0000 <= pb <= 0x8000_0000, -0x10_0000 <= db <= 0x10_0000,
            dm == 100 - db,
            sday as int == p.day - sb,
            thr as int == if sday < -1 { -1int } else if sday > 0xffff { 0xffffint } else { sday as int },
            dacc_ok(m, p, t, a as int, x as int, cnt, sum),
        decreases b - x,
    {
        proof {
            lemma_div_in(x as int, m.l_bs, g as int);
            assert(lkey(m, x as int) == okey(m, t));
        }
        let sc = c.l_ship_c[x];
        let pc = c.l_price_c[x];
        let dc = c.l_disc_c[x];
        let hit = (sc as i64) > thr;
        proof {
            assert(lship(m, x as int) == sb + sc);
            assert(hit == (lship(m, x as int) > p.day));
            assert(hit == lhit(m, p, t, x as int));
            assert(lprice(m, x as int) == pb + pc);
            assert(ldisc(m, x as int) == db + dc);
            lemma_small_arg(pb as int, pc as int, dm as int, dc as int);
            assert(larg(m, x as int) == (pb + pc) * (dm - dc)) by (nonlinear_arith)
                requires larg(m, x as int) == lprice(m, x as int) * (100 - ldisc(m, x as int)),
                    lprice(m, x as int) == pb + pc, ldisc(m, x as int) == db + dc, dm == 100 - db;
        }
        let v: i64 = (pb + pc as i64) * (dm - dc as i64);
        proof {
            lemma_dacc_step(m, p, t, a as int, x as int, cnt, sum, hit, v as int);
            assert((x + 1 - a) * arg_cap() <= 256 * arg_cap()) by (nonlinear_arith) requires x + 1 - a <= 256;
        }
        sum = sum + if hit { v } else { 0i64 };
        cnt = cnt + if hit { 1u32 } else { 0u32 };
        x = x + 1;
    }
    proof {
        lemma_run_totals(m, p, t, a as int, b as int);
        assert(b - a <= 256);
        assert((b - a) * arg_cap() <= 256 * arg_cap()) by (nonlinear_arith) requires b - a <= 256;
        assert(i128_max() == 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
    }
    Some((cnt, sum))
}

/// Whether run `t` starts with the key of the order at `t` (orders block `og`, key base `kb`).
fn run_matches(c: &Cols, t: usize, og: usize, kb: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: bool)
    requires
        cols_ok(*c, m, p), model_ok(m),
        t < m.o_n, t + 1 < m.l_st.len(),
        og * m.o_bs <= t < (og + 1) * m.o_bs, og < m.o_nb, kb == m.o_key_b[og as int],
    ensures r == (lkey(m, m.l_st[t as int] as int) == okey(m, t as int)),
    no_unwind
{
    let a = c.l_st[t] as usize;
    proof {
        assert(run_ok(m, t as int));
        lemma_div_in(t as int, m.o_bs, og as int);
        assert(in_i64(okey(m, t as int)));
    }
    let (g, ge) = block_of(c, a, Ghost(m), Ghost(p));
    proof {
        lemma_div_in(a as int, m.l_bs, g as int);
        assert(in_i64(lkey(m, a as int)));
    }
    c.l_key_b[g] + c.l_key_c[a] as i64 == kb + c.o_key_c[t] as i64
}

/// The run of the order at `t` (its own: the key at its first row is the order's): count, revenue, and whether the
/// absolute mass leaves `i128`.
fn order_sums(c: &Cols, t: usize, og: usize, kb: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: (u64, i128, bool))
    requires
        cols_ok(*c, m, p), model_ok(m), m.cluster == 1,
        t < m.o_n, t + 1 < m.l_st.len(),
        og * m.o_bs <= t < (og + 1) * m.o_bs, og < m.o_nb, kb == m.o_key_b[og as int],
        lkey(m, m.l_st[t as int] as int) == okey(m, t as int),
    ensures
        r.0 as int == lcnt(m, p, t as int),
        !r.2 ==> r.1 as int == lsum(m, p, t as int) && labs(m, p, t as int) <= i128_max(),
        r.2 ==> labs(m, p, t as int) > i128_max(),
    no_unwind
{
    let a = c.l_st[t] as usize;
    let b = c.l_st[t + 1] as usize;
    proof {
        assert(run_ok(m, t as int));
        lemma_run_rows(m, t as int);
    }
    let (g, ge) = block_of(c, a, Ghost(m), Ghost(p));
    if (b as u64) <= ge {
        if let Some(s) = dir_sums(c, a, b, g, Ghost(m), Ghost(p), Ghost(t as int)) {
            return (s.0 as u64, s.1 as i128, false);
        }
    }
    proof {
        lemma_rows_lb(m, t as int, a as int, b as int);
        lemma_div_in(t as int, m.o_bs, og as int);
        assert(in_i64(okey(m, t as int)));
    }
    let okv = kb + c.o_key_c[t] as i64;
    let r = fast_sums(c, okv, a, b, g, ge, Ghost(m), Ghost(p), Ghost(t as int));
    (r.0, r.1, r.3)
}

/// The chunk `[o_lo, o_hi)` by batches over the run starts: `aligned` false when some listed order's run is not its
/// own (then nothing is claimed); otherwise its top 10 (`len`), or an order whose mass leaves `i128`.
pub fn run_dir(c: &Cols, bm: &Vec<u64>, use_bm: bool, o_lo: usize, o_hi: usize,
    buf: &mut Vec<Cand>, sel: &mut Vec<usize>, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (bool, usize, bool, usize))
    requires
        cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.seg_fast,
        use_bm ==> bm_ok(bm@, m, *c),
        o_lo <= o_hi <= m.o_n,
        o_hi < m.l_st.len(),
        old(buf)@.len() == 10,
        old(sel)@.len() == BATCH,
    ensures ({
        let (aligned, len, ovf, ovf_q) = r;
        &&& final(buf)@.len() == 10
        &&& final(sel)@.len() == BATCH
        &&& aligned ==> {
            &&& len <= 10
            &&& ovf ==> o_lo <= ovf_q < o_hi && good(m, p, ovf_q as int) && labs(m, p, ovf_q as int) > i128_max()
            &&& !ovf ==> {
                &&& topk_ok(q3_keys(), q3_fams(), 10, cands_view(final(buf)@, len as int), gseq(m, p, o_lo as int, o_hi as int))
                &&& forall|q: int| o_lo <= q < o_hi && #[trigger] good(m, p, q) ==> labs(m, p, q) <= i128_max()
            }
        }
    }),
    no_unwind
{
    let mut len: usize = 0;
    let mut q = o_lo;
    proof {
        lemma_topk_empty(q3_keys(), q3_fams(), 10);
        lemma_gseq_empty(m, p, o_lo as int);
        assert(cands_view(buf@, 0) =~= Seq::<Row>::empty());
    }
    let mut found = false;
    let mut found_q: usize = 0;
    let mut aligned = true;
    while q < o_hi && !found && aligned
        invariant
            cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.seg_fast,
            use_bm ==> bm_ok(bm@, m, *c),
            o_lo <= q <= o_hi <= m.o_n,
            o_hi < m.l_st.len(),
            buf@.len() == 10,
            sel@.len() == BATCH,
            len <= 10,
            found ==> o_lo <= found_q < o_hi && good(m, p, found_q as int) && labs(m, p, found_q as int) > i128_max(),
            !found && aligned ==> {
                &&& topk_ok(q3_keys(), q3_fams(), 10, cands_view(buf@, len as int), gseq(m, p, o_lo as int, q as int))
                &&& forall|q2: int| o_lo <= q2 < q && #[trigger] good(m, p, q2) ==> labs(m, p, q2) <= i128_max()
            },
        decreases o_hi - q + if found || !aligned { 0int } else { 1int },
    {
        // the batch [q, bend): inside one orders block, at most BATCH orders
        let og64 = (q as u64) / c.o_bs;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q as int, m.o_bs);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(q as int, m.o_bs);
            assert(m.o_bs * og64 == og64 * m.o_bs) by (nonlinear_arith);
            assert((og64 + 1) * m.o_bs == og64 * m.o_bs + m.o_bs) by (nonlinear_arith);
            assert(og64 <= q) by (nonlinear_arith) requires og64 * m.o_bs <= q, m.o_bs >= 1, og64 >= 0;
        }
        let og = og64 as usize;
        let be64 = (og64 + 1) * c.o_bs;
        let mut bend: usize = if be64 < o_hi as u64 { be64 as usize } else { o_hi };
        if bend - q > BATCH {
            bend = q + BATCH;
        }
        let n = select(c, bm, use_bm, q, bend, og, sel, Ghost(m), Ghost(p));
        proof {
            lemma_div_in(q as int, m.o_bs, og as int);
            lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb);
        }
        let kb = c.o_key_b[og];
        let db = c.o_date_b[og];
        let sb = c.o_sp_b[og];
        // the batch's runs are its orders' when its first and last run are (`lemma_aligned_range`)
        if !run_matches(c, q, og, kb, Ghost(m), Ghost(p)) || !run_matches(c, bend - 1, og, kb, Ghost(m), Ghost(p)) {
            aligned = false;
        } else {
        proof {
            lemma_aligned_range(m, q as int, bend - 1);
        }
        // phase 2: the listed orders, in position order
        let mut i: usize = 0;
        let ghost mut q2: int = q as int;
        while i < n && !found && aligned
            invariant
                cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.seg_fast,
                o_lo <= q < bend <= o_hi <= m.o_n,
                o_hi < m.l_st.len(),
                og * m.o_bs <= q, bend <= (og + 1) * m.o_bs, og < m.o_nb,
                kb == m.o_key_b[og as int], db == m.o_date_b[og as int], sb == m.o_sp_b[og as int],
                buf@.len() == 10,
                sel@.len() == BATCH,
                sel_ok(m, p, sel@, n as int, q as int, bend as int),
                forall|k: int| q <= k <= bend - 1 ==> #[trigger] lkey(m, m.l_st[k] as int) == okey(m, k),
                i <= n,
                len <= 10,
                found ==> o_lo <= found_q < o_hi && good(m, p, found_q as int) && labs(m, p, found_q as int) > i128_max(),
                !found && aligned ==> {
                    &&& q2 == if i == 0 { q as int } else { sel@[i - 1] + 1 }
                    &&& q <= q2 <= bend
                    &&& topk_ok(q3_keys(), q3_fams(), 10, cands_view(buf@, len as int), gseq(m, p, o_lo as int, q2))
                    &&& forall|u: int| o_lo <= u < q2 && #[trigger] good(m, p, u) ==> labs(m, p, u) <= i128_max()
                },
            decreases n - i + if found || !aligned { 0int } else { 1int },
        {
            let t = sel[i];
            proof {
                // orders [q2, t) are not flagged, so no groups
                lemma_sel_gap(m, p, sel@, n as int, q as int, bend as int, i as int, q2, t as int);
                assert forall|u: int| q2 <= u < t implies !#[trigger] good(m, p, u) by {
                    assert(!flag(m, p, u));
                }
                lemma_gseq_skip(m, p, o_lo as int, q2, t as int);
                lemma_div_in(t as int, m.o_bs, og as int);
                assert(in_i64(okey(m, t as int)));
                assert(flag(m, p, t as int));
            }
            let ghost g0 = gseq(m, p, o_lo as int, t as int);
            proof {
                lemma_gseq_step(m, p, o_lo as int, t as int);
                assert(lkey(m, m.l_st[t as int] as int) == okey(m, t as int));
            }
            let r = order_sums(c, t, og, kb, Ghost(m), Ghost(p));
            {
                {
                    if r.0 > 0 {
                        assert(good(m, p, t as int));
                        if r.2 {
                            found = true;
                            found_q = t;
                        } else if len == 10 && r.1 < buf[9].rev {
                            // below the 10th revenue: the order cannot enter the top 10
                            proof {
                                assert(in_i64(okey(m, t as int)) && in_i64(odate(m, t as int)) && in_i64(osp(m, t as int)));
                                let gc = Cand { okey: okey(m, t as int) as i64, rev: r.1, date: odate(m, t as int) as i64,
                                    sp: osp(m, t as int) as i64 };
                                assert(cand_row(gc) =~= grow(m, p, t as int));
                                lemma_gseq_wf_range(m, p, o_lo as int, t as int + 1);
                                lemma_view_last(buf@, 10);
                                lemma_cand_cmp(buf@[9], gc);
                                lemma_topk_skip(q3_keys(), q3_fams(), 10, cands_view(buf@, 10), g0, cand_row(gc));
                            }
                        } else {
                            let okv = kb + c.o_key_c[t] as i64;
                            let date = db + c.o_date_c[t] as i64;
                            let sp = sb + c.o_sp_c[t] as i64;
                            let cand = Cand { okey: okv, rev: r.1, date, sp };
                            proof {
                                assert(in_i64(odate(m, t as int)) && in_i64(osp(m, t as int)));
                                assert(cand_row(cand) =~= grow(m, p, t as int));
                                lemma_gseq_wf_range(m, p, o_lo as int, t as int + 1);
                            }
                            len = topk_insert(buf, len, cand, Ghost(g0));
                        }
                    } else {
                        assert(!good(m, p, t as int));
                    }
                    proof {
                        if !found {
                            q2 = t as int + 1;
                        }
                    }
                }
            }
            i = i + 1;
        }
        if !found {
            proof {
                lemma_sel_gap(m, p, sel@, n as int, q as int, bend as int, n as int, q2, bend as int);
                assert forall|u: int| q2 <= u < bend implies !#[trigger] good(m, p, u) by {
                    assert(!flag(m, p, u));
                }
                lemma_gseq_skip(m, p, o_lo as int, q2, bend as int);
            }
            q = bend;
        }
        }
    }
    (aligned, len, found, found_q)
}

} // verus!
