//! The chunk kernel when customer keys are dense and the market segment is one U8 code (`Cols::seg_fast`).
//! Orders are taken in batches of at most `BATCH` positions inside one orders block:
//! - phase 1 (`select`, branch-free) lists the batch's orders that are `flag`ged: dated before the day, with a
//!   customer of the segment, tested by key position in the bit set of the segment's customers (`bm`, built by the
//!   calling thread when few workers run) or in the segment code column;
//! - phase 2 finds each listed order's lineitem run by scanning the lineitem key codes forward from the cursor
//!   (`find_run`; the runs of unlisted orders are passed over without reading other columns) and sums the run with
//!   `kernel::fast_sums`.
//! Invariant of the cursor `j` (`before`): every lineitem row before `j` belongs to an order before the next one.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::expr::i128_max;
use crate::gendb_entry::work::put;
use super::common::isum::*;
use super::common::topk::*;
use super::common::bitset::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;

verus! {

/// Orders per batch (the length of a task's selection buffer).
pub const BATCH: usize = 2048;

/// The order at `q` is dated before the day and its customer has the segment (a group iff a lineitem ships later).
pub open spec fn flag(m: M, p: QP, q: int) -> bool {
    odate(m, q) < p.day && ccnt(m, p, ocust(m, q)) > 0
}

/// `s` is the bit set of the customer rows whose segment code is the parameter's.
pub open spec fn bm_ok(s: Seq<u64>, m: M, c: Cols) -> bool {
    &&& s.len() == m.c_n / 64 + 1
    &&& forall|i: int| 0 <= i < m.c_n ==> #[trigger] bit(s, i) == (m.c_seg_c[i] == c.segc)
}

/// Every lineitem row before `j` belongs to an order before position `q`.
pub open spec fn before(m: M, q: int, j: int) -> bool {
    forall|t: int| 0 <= t < j ==> #[trigger] lpos(m, t) < q
}

/// `s[0..n)` lists exactly the flagged orders of `[lo, hi)`, increasing.
pub open spec fn sel_ok(m: M, p: QP, s: Seq<usize>, n: int, lo: int, hi: int) -> bool {
    &&& 0 <= n <= s.len()
    &&& forall|i: int| 0 <= i < n ==> lo <= #[trigger] s[i] < hi && flag(m, p, s[i] as int)
    &&& forall|a: int, b: int| 0 <= a < b < n ==> #[trigger] s[a] < #[trigger] s[b]
    &&& forall|u: int| lo <= u < hi && #[trigger] flag(m, p, u) ==> exists|i: int| 0 <= i < n && s[i] == u
}

// ------------------------------------------------------------------------------------------------ customers

/// The customer of key `ck` has the segment (dense keys: the customer of key `ck` is row `ck - 1`).
pub fn cust_flag(c: &Cols, bm: &Vec<u64>, use_bm: bool, ck: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: bool)
    requires
        cols_ok(*c, m, p), model_ok(m), c.seg_fast,
        use_bm ==> bm_ok(bm@, m, *c),
    ensures r == (ccnt(m, p, ck as int) > 0),
    no_unwind
{
    let ghost f = cmatch_f(m, p, ck as int);
    if ck >= 1 && (ck as u64) <= (c.c_n as u64) {
        let row = (ck - 1) as usize;
        let hit = if use_bm {
            proof {
                assert(row / 64 <= m.c_n / 64) by (nonlinear_arith) requires row < m.c_n;
            }
            bit_at(bm, row)
        } else {
            c.c_seg_c[row] == c.segc
        };
        proof {
            assert(hit == (m.c_seg_c[row as int] == c.segc));
            lemma_seg_match(*c, m, p, row as int);
            assert(ckey(m, row as int) == row + 1);
            assert forall|i: int| 0 <= i < m.c_n && i != row as int implies #[trigger] f(i) == 0 by {
                assert(ckey(m, i) == i + 1);
            }
            lemma_isum_single(m.c_n, f, row as int);
        }
        hit
    } else {
        proof {
            assert forall|i: int| 0 <= i < m.c_n implies #[trigger] f(i) == 0 by {
                assert(ckey(m, i) == i + 1);
            }
            lemma_isum_zero(m.c_n, f);
        }
        false
    }
}

// ------------------------------------------------------------------------------------------------ phase 1

/// One more position of the selection: `t` is appended when flagged.
proof fn lemma_sel_step(m: M, p: QP, s0: Seq<usize>, n: int, lo: int, t: int, f: int)
    requires
        sel_ok(m, p, s0, n, lo, t),
        lo <= t,
        n < s0.len(),
        0 <= t <= usize::MAX,
        f == if flag(m, p, t) { 1int } else { 0int },
    ensures
        sel_ok(m, p, s0.update(n, t as usize), n + f, lo, t + 1),
{
    let s1 = s0.update(n, t as usize);
    assert forall|i: int| 0 <= i < n + f implies lo <= #[trigger] s1[i] < t + 1 && flag(m, p, s1[i] as int) by {
        if i < n {
            assert(s1[i] == s0[i]);
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < n + f implies #[trigger] s1[a] < #[trigger] s1[b] by {
        assert(s1[a] == s0[a]);
        if b < n {
            assert(s1[b] == s0[b]);
        }
    }
    assert forall|u: int| lo <= u < t + 1 && #[trigger] flag(m, p, u) implies exists|i: int| 0 <= i < n + f && s1[i] == u by {
        if u < t {
            let i = choose|i: int| 0 <= i < n && s0[i] == u;
            assert(s1[i] == s0[i]);
        } else {
            assert(s1[n] == u);
        }
    }
}

/// Phase 1: the flagged orders of the batch `[q, bend)` (inside orders block `og`), listed in `sel`.
pub fn select(c: &Cols, bm: &Vec<u64>, use_bm: bool, q: usize, bend: usize, og: usize, sel: &mut Vec<usize>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (n: usize)
    requires
        cols_ok(*c, m, p), model_ok(m), c.seg_fast,
        use_bm ==> bm_ok(bm@, m, *c),
        q < bend <= m.o_n,
        og * m.o_bs <= q,
        bend <= (og + 1) * m.o_bs,
        bend - q <= old(sel)@.len(),
    ensures
        final(sel)@.len() == old(sel)@.len(),
        n <= bend - q,
        sel_ok(m, p, final(sel)@, n as int, q as int, bend as int),
    no_unwind
{
    proof {
        lemma_div_in(q as int, m.o_bs, og as int);
        lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb);
    }
    let cb = c.o_cust_b[og];
    let db = c.o_date_b[og];
    let ghost len0 = sel@.len();
    let mut n: usize = 0;
    let mut t = q;
    while t < bend
        invariant
            cols_ok(*c, m, p), model_ok(m), c.seg_fast,
            use_bm ==> bm_ok(bm@, m, *c),
            q <= t <= bend <= m.o_n,
            og * m.o_bs <= q,
            bend <= (og + 1) * m.o_bs,
            bend - q <= len0,
            sel@.len() == len0,
            cb == m.o_cust_b[og as int], db == m.o_date_b[og as int],
            n <= t - q,
            sel_ok(m, p, sel@, n as int, q as int, t as int),
        decreases bend - t,
    {
        proof {
            lemma_div_in(t as int, m.o_bs, og as int);
            assert(in_i64(okey(m, t as int)));
            assert(in_i64(ocust(m, t as int)) && in_i64(odate(m, t as int)));
        }
        let date = db + c.o_date_c[t] as i64;
        let ck = cb + c.o_cust_c[t] as i64;
        let okc = cust_flag(c, bm, use_bm, ck, Ghost(m), Ghost(p));
        let f: usize = if date < c.day && okc { 1 } else { 0 };
        let ghost s0 = sel@;
        put(sel, n, t);
        proof {
            assert(f as int == if flag(m, p, t as int) { 1int } else { 0int });
            lemma_sel_step(m, p, s0, n as int, q as int, t as int, f as int);
        }
        n = n + f;
        t = t + 1;
    }
    n
}

/// Between consecutive listed orders (and around them) no order is flagged.
pub proof fn lemma_sel_gap(m: M, p: QP, s: Seq<usize>, n: int, lo: int, hi: int, i: int, a: int, b: int)
    requires
        sel_ok(m, p, s, n, lo, hi),
        0 <= i <= n,
        a == if i == 0 { lo } else { s[i - 1] + 1 },
        b == if i == n { hi } else { s[i] as int },
    ensures
        forall|u: int| a <= u < b ==> !#[trigger] flag(m, p, u),
{
    assert forall|u: int| a <= u < b implies !#[trigger] flag(m, p, u) by {
        if flag(m, p, u) {
            assert(lo <= u < hi) by {
                if i > 0 {
                    assert(lo <= s[i - 1]);
                }
                if i < n {
                    assert(s[i] < hi);
                }
            }
            let k = choose|k: int| 0 <= k < n && s[k] == u;
            if k < i - 1 {
                assert(s[k] < s[i - 1]);
            } else if k > i {
                assert(s[i] < s[k]);
            }
        }
    }
}

/// Positions without groups leave the group rows unchanged.
pub proof fn lemma_gseq_skip(m: M, p: QP, lo: int, a: int, b: int)
    requires
        lo <= a <= b,
        forall|u: int| a <= u < b ==> !#[trigger] good(m, p, u),
    ensures
        gseq(m, p, lo, b) == gseq(m, p, lo, a),
{
    lemma_gseq_split(m, p, lo, a, b);
    lemma_gseq_none(m, p, a, b);
    assert(gseq(m, p, lo, a) + Seq::<Row>::empty() =~= gseq(m, p, lo, a));
}

// ------------------------------------------------------------------------------------------------ phase 2

/// The first lineitem row at or after `j` (below `l_hi`) whose key is `okv`: its position and block cursor, or
/// none (`x == l_hi`). Rows passed over have other keys.
pub fn find_run(c: &Cols, okv: i64, j: usize, l_hi: usize, lg: usize, lge: u64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: (bool, usize, usize, u64))
    requires
        cols_ok(*c, m, p), model_ok(m),
        j <= l_hi <= m.l_n,
        lcur_ok(m, j as int, lg as int, lge as int),
    ensures ({
        let (found, x, g, ge) = r;
        &&& j <= x <= l_hi
        &&& forall|t: int| j <= t < x ==> lkey(m, t) != okv
        &&& found ==> x < l_hi && lkey(m, x as int) == okv && lcur_ok(m, x as int, g as int, ge as int)
        &&& !found ==> x == l_hi
    }),
    no_unwind
{
    let mut x = j;
    let mut g = lg;
    let mut ge = lge;
    let mut found = false;
    while x < l_hi && !found
        invariant
            cols_ok(*c, m, p), model_ok(m),
            j <= x <= l_hi <= m.l_n,
            lcur_ok(m, x as int, g as int, ge as int),
            forall|t: int| j <= t < x ==> lkey(m, t) != okv,
            found ==> x < l_hi && lkey(m, x as int) == okv,
        decreases l_hi - x + if found { 0int } else { 1int },
    {
        if x as u64 == ge {
            proof {
                assert((g + 2) * m.l_bs == (g + 1) * m.l_bs + m.l_bs) by (nonlinear_arith);
                lemma_div_in(x as int, m.l_bs, g as int + 1);
                lemma_block_bound(x as int, m.l_bs, m.l_n, m.l_nb);
            }
            g = g + 1;
            ge = ge + c.l_bs;
        }
        proof {
            lemma_div_in(x as int, m.l_bs, g as int);
            lemma_block_bound(x as int, m.l_bs, m.l_n, m.l_nb);
        }
        let end: usize = if ge < l_hi as u64 { ge as usize } else { l_hi };
        assert(x < end);
        let ghost x0 = x;
        let base = c.l_key_b[g];
        let d: i128 = okv as i128 - base as i128;
        if 0 <= d && d < 0x1_0000_0000i128 {
            let tc = d as u32;
            while x < end && c.l_key_c[x] != tc
                invariant
                    cols_ok(*c, m, p), model_ok(m),
                    j <= x <= end, end <= l_hi, end <= ge, l_hi <= m.l_n,
                    x0 <= x, x0 < end,
                    lcur_ok(m, x as int, g as int, ge as int),
                    g < m.l_nb,
                    base == m.l_key_b[g as int],
                    tc as int == okv - base,
                    forall|t: int| j <= t < x ==> lkey(m, t) != okv,
                decreases end - x,
            {
                proof {
                    lemma_div_in(x as int, m.l_bs, g as int);
                }
                x = x + 1;
            }
            if x < end {
                proof {
                    lemma_div_in(x as int, m.l_bs, g as int);
                }
                found = true;
            } else {
                assert(x > x0);
            }
        } else {
            proof {
                assert forall|t: int| j <= t < end implies lkey(m, t) != okv by {
                    if t >= x {
                        lemma_div_in(t, m.l_bs, g as int);
                    }
                }
            }
            x = end;
        }
        assert(found || x > x0);
    }
    (found, x, g, ge)
}

/// A found run start `a` of the order at `t` (cursor invariant `before(t, j)`, `j <= a`) is its lineitem bound.
proof fn lemma_found_lb(m: M, t: int, j: int, a: int)
    requires
        model_ok(m), m.cluster == 1,
        0 <= t < m.o_n,
        before(m, t, j),
        0 <= j <= a < m.l_n,
        forall|u: int| j <= u < a ==> lkey(m, u) != okey(m, t),
        lkey(m, a) == okey(m, t),
    ensures
        lb_ok(m, t, a),
{
    lemma_lpos_key(m, t, a);
    assert forall|u: int| 0 <= u < a implies #[trigger] lpos(m, u) < t by {
        if u >= j {
            lemma_lpos_key(m, t, u);
            lemma_lpos_mono(m, u, a);
        }
    }
    assert forall|u: int| a <= u < m.l_n implies #[trigger] lpos(m, u) >= t by {
        lemma_lpos_mono(m, a, u);
    }
}

/// An order whose key is on no row from `j` to `l_hi` (and none before `j` or from `l_hi`) has no lineitem.
proof fn lemma_not_found(m: M, p: QP, t: int, j: int, l_hi: int, o_hi: int)
    requires
        model_ok(m),
        0 <= t < o_hi <= m.o_n,
        before(m, t, j),
        0 <= j <= l_hi <= m.l_n,
        forall|u: int| j <= u < l_hi ==> lkey(m, u) != okey(m, t),
        forall|u: int| l_hi <= u < m.l_n ==> #[trigger] lpos(m, u) >= o_hi,
    ensures
        lcnt(m, p, t) == 0,
        !good(m, p, t),
{
    assert forall|u: int| 0 <= u < m.l_n implies #[trigger] lcnt_f(m, p, t)(u) == 0 by {
        if u < j || u >= l_hi {
            lemma_lpos_key(m, t, u);
        }
    }
    lemma_isum_zero(m.l_n, lcnt_f(m, p, t));
}

/// Most rows of one run summed by `run_sums`: below it the absolute revenue mass (each row under 10^31) stays
/// inside `i128`, so neither the mass nor an overflow needs tracking.
pub const RUN_CAP: usize = 0x80_0000;

/// Partial sums of one order's rows `[a0, j)`: count and revenue; the absolute mass is at most `10^31` per row.
pub open spec fn racc_ok(m: M, p: QP, q: int, a0: int, j: int, cnt: u64, sum: i128) -> bool {
    &&& cnt as int == dsum(lcnt_f(m, p, q), a0, j)
    &&& cnt as int <= j - a0
    &&& sum as int == dsum(lsum_f(m, p, q), a0, j)
    &&& 0 <= dsum(labs_f(m, p, q), a0, j) <= (j - a0) * 10000000000000000000000000000000
    &&& -dsum(labs_f(m, p, q), a0, j) <= sum as int <= dsum(labs_f(m, p, q), a0, j)
}

/// One more row of the run (a hit with argument `a`, or not a hit).
proof fn lemma_racc_step(m: M, p: QP, q: int, a0: int, j: int, cnt: u64, sum: i128, hit: bool, a: int)
    requires
        racc_ok(m, p, q, a0, j, cnt, sum),
        0 <= a0 <= j,
        hit == lhit(m, p, q, j),
        hit ==> a == larg(m, j),
        abs(a) < 10000000000000000000000000000000,
    ensures
        dsum(lcnt_f(m, p, q), a0, j + 1) == cnt + if hit { 1int } else { 0int },
        dsum(lsum_f(m, p, q), a0, j + 1) == sum + if hit { a } else { 0int },
        0 <= dsum(labs_f(m, p, q), a0, j + 1) <= (j + 1 - a0) * 10000000000000000000000000000000,
        -dsum(labs_f(m, p, q), a0, j + 1) <= sum + (if hit { a } else { 0int }) <= dsum(labs_f(m, p, q), a0, j + 1),
{
    lemma_terms_at(m, p, q, j);
    lemma_isum_step(j, lcnt_f(m, p, q));
    lemma_isum_step(j, lsum_f(m, p, q));
    lemma_isum_step(j, labs_f(m, p, q));
}

/// The lineitem run of the order at `q` (key `okv`) from its first row `a0`, summed branch-free: `complete` with
/// the count, the revenue and the cursor after the run, or not complete when the run reaches `RUN_CAP` rows (the
/// caller then sums it with `kernel::fast_sums`, which tracks the mass).
pub fn run_sums(c: &Cols, okv: i64, a0: usize, l_hi: usize, lg0: usize, lge0: u64,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(q): Ghost<int>) -> (r: (bool, u64, i128, usize, usize, u64))
    requires
        cols_ok(*c, m, p), model_ok(m), m.cluster == 1,
        0 <= q < m.o_n, okv == okey(m, q),
        lb_ok(m, q, a0 as int),
        a0 <= l_hi <= m.l_n,
        forall|t: int| l_hi <= t < m.l_n ==> #[trigger] lpos(m, t) > q,
        lcur_ok(m, a0 as int, lg0 as int, lge0 as int),
    ensures ({
        let (complete, cnt, sum, j1, lg1, lge1) = r;
        complete ==> {
            &&& a0 <= j1 <= l_hi
            &&& lb_ok(m, q + 1, j1 as int)
            &&& lcur_ok(m, j1 as int, lg1 as int, lge1 as int)
            &&& cnt as int == lcnt(m, p, q)
            &&& sum as int == lsum(m, p, q)
            &&& labs(m, p, q) <= i128_max()
        }
    }),
    no_unwind
{
    let mut j = a0;
    let mut lg = lg0;
    let mut lge = lge0;
    let mut cnt: u64 = 0;
    let mut sum: i128 = 0;
    let mut stop = false;
    proof {
        assert(dsum(lcnt_f(m, p, q), a0 as int, a0 as int) == 0);
    }
    while j < l_hi && !stop && j - a0 < RUN_CAP
        invariant
            cols_ok(*c, m, p), model_ok(m), m.cluster == 1,
            0 <= q < m.o_n, okv == okey(m, q),
            lb_ok(m, q, a0 as int),
            a0 <= j <= l_hi <= m.l_n,
            j - a0 <= RUN_CAP,
            lcur_ok(m, j as int, lg as int, lge as int),
            forall|t: int| a0 <= t < j ==> #[trigger] lkey(m, t) == okey(m, q),
            stop ==> j < l_hi && lkey(m, j as int) != okey(m, q),
            racc_ok(m, p, q, a0 as int, j as int, cnt, sum),
        decreases l_hi - j + if stop { 0int } else { 1int },
    {
        if j as u64 == lge {
            proof {
                assert((lg + 2) * m.l_bs == (lg + 1) * m.l_bs + m.l_bs) by (nonlinear_arith);
                lemma_div_in(j as int, m.l_bs, lg as int + 1);
                lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            }
            lg = lg + 1;
            lge = lge + c.l_bs;
        }
        proof {
            lemma_div_in(j as int, m.l_bs, lg as int);
            lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            assert(in_i64(lkey(m, j as int)));
        }
        let lk = c.l_key_b[lg] + c.l_key_c[j] as i64;
        if lk != okv {
            stop = true;
        } else {
            let sh = c.l_ship_b[lg] + c.l_ship_c[j] as i64;
            let hit = sh > c.day;
            let a = row_arg(c, j, lg, Ghost(m), Ghost(p));
            proof {
                lemma_racc_step(m, p, q, a0 as int, j as int, cnt, sum, hit, a as int);
                assert((j - a0 + 1) * 10000000000000000000000000000000 <= 0x80_0000 * 10000000000000000000000000000000int)
                    by (nonlinear_arith) requires j - a0 + 1 <= 0x80_0000;
            }
            cnt = cnt + if hit { 1u64 } else { 0u64 };
            sum = sum + if hit { a } else { 0i128 };
            j = j + 1;
        }
    }
    let complete = stop || j >= l_hi;
    if complete {
        proof {
            // the order's rows are exactly [a0, j)
            assert forall|t: int| 0 <= t < m.l_n && (t < a0 || t >= j) implies lkey(m, t) != okey(m, q) by {
                lemma_lpos_key(m, q, t);
                if t >= j {
                    if j < l_hi {
                        lemma_lpos_key(m, q, j as int);
                        lemma_lpos_mono(m, j as int, t);
                    }
                }
            }
            lemma_run_totals(m, p, q, a0 as int, j as int);
            assert forall|t: int| 0 <= t < j implies #[trigger] lpos(m, t) < q + 1 by {
                if t >= a0 {
                    lemma_lpos_key(m, q, t);
                }
            }
            assert forall|t: int| j <= t < m.l_n implies #[trigger] lpos(m, t) >= q + 1 by {
                if j < l_hi {
                    lemma_lpos_key(m, q, j as int);
                    lemma_lpos_mono(m, j as int, t);
                }
            }
            assert(i128_max() == 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
        }
    }
    (complete, cnt, sum, j, lg, lge)
}

/// The chunk `[o_lo, o_hi)` x `[l_lo, l_hi)` by batches: its top 10 (`len`), or an order whose mass leaves `i128`.
pub fn run_sel(c: &Cols, bm: &Vec<u64>, use_bm: bool, o_lo: usize, o_hi: usize, l_lo: usize, l_hi: usize,
    buf: &mut Vec<Cand>, sel: &mut Vec<usize>, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (usize, bool, usize))
    requires
        cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.seg_fast,
        use_bm ==> bm_ok(bm@, m, *c),
        o_lo <= o_hi <= m.o_n,
        l_lo <= l_hi <= m.l_n,
        lb_ok(m, o_lo as int, l_lo as int),
        lb_ok(m, o_hi as int, l_hi as int),
        old(buf)@.len() == 10,
        old(sel)@.len() == BATCH,
    ensures ({
        let (len, ovf, ovf_q) = r;
        &&& final(buf)@.len() == 10
        &&& len <= 10
        &&& ovf ==> o_lo <= ovf_q < o_hi && good(m, p, ovf_q as int) && labs(m, p, ovf_q as int) > i128_max()
        &&& !ovf ==> {
            &&& topk_ok(q3_keys(), q3_fams(), 10, cands_view(final(buf)@, len as int), gseq(m, p, o_lo as int, o_hi as int))
            &&& forall|q: int| o_lo <= q < o_hi && #[trigger] good(m, p, q) ==> labs(m, p, q) <= i128_max()
        }
    }),
    no_unwind
{
    let mut len: usize = 0;
    let mut q = o_lo;
    let mut j = l_lo;
    let lg64 = (j as u64) / c.l_bs;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j as int, m.l_bs);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(j as int, m.l_bs);
        assert(m.l_bs * lg64 == lg64 * m.l_bs) by (nonlinear_arith);
        assert((lg64 + 1) * m.l_bs == lg64 * m.l_bs + m.l_bs) by (nonlinear_arith);
        assert(lg64 <= j) by (nonlinear_arith) requires lg64 * m.l_bs <= j, m.l_bs >= 1, lg64 >= 0;
    }
    let mut lg: usize = lg64 as usize;
    let mut lge: u64 = (lg64 + 1) * c.l_bs;
    proof {
        lemma_topk_empty(q3_keys(), q3_fams(), 10);
        lemma_gseq_empty(m, p, o_lo as int);
        assert(cands_view(buf@, 0) =~= Seq::<Row>::empty());
    }
    let mut found = false;
    let mut found_q: usize = 0;
    while q < o_hi && !found
        invariant
            cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.seg_fast,
            use_bm ==> bm_ok(bm@, m, *c),
            o_lo <= q <= o_hi <= m.o_n,
            l_hi <= m.l_n,
            lb_ok(m, o_hi as int, l_hi as int),
            buf@.len() == 10,
            sel@.len() == BATCH,
            len <= 10,
            found ==> o_lo <= found_q < o_hi && good(m, p, found_q as int) && labs(m, p, found_q as int) > i128_max(),
            !found ==> {
                &&& j <= l_hi
                &&& before(m, q as int, j as int)
                &&& lcur_ok(m, j as int, lg as int, lge as int)
                &&& topk_ok(q3_keys(), q3_fams(), 10, cands_view(buf@, len as int), gseq(m, p, o_lo as int, q as int))
                &&& forall|q2: int| o_lo <= q2 < q && #[trigger] good(m, p, q2) ==> labs(m, p, q2) <= i128_max()
            },
        decreases o_hi - q + if found { 0int } else { 1int },
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
        // phase 2: the listed orders, in position order
        let mut i: usize = 0;
        let ghost mut q2: int = q as int;
        while i < n && !found
            invariant
                cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.seg_fast,
                o_lo <= q < bend <= o_hi <= m.o_n,
                og * m.o_bs <= q, bend <= (og + 1) * m.o_bs, og < m.o_nb,
                kb == m.o_key_b[og as int], db == m.o_date_b[og as int], sb == m.o_sp_b[og as int],
                l_hi <= m.l_n,
                lb_ok(m, o_hi as int, l_hi as int),
                buf@.len() == 10,
                sel@.len() == BATCH,
                sel_ok(m, p, sel@, n as int, q as int, bend as int),
                i <= n,
                len <= 10,
                found ==> o_lo <= found_q < o_hi && good(m, p, found_q as int) && labs(m, p, found_q as int) > i128_max(),
                !found ==> {
                    &&& q2 == if i == 0 { q as int } else { sel@[i - 1] + 1 }
                    &&& q <= q2 <= bend
                    &&& j <= l_hi
                    &&& before(m, q2, j as int)
                    &&& lcur_ok(m, j as int, lg as int, lge as int)
                    &&& topk_ok(q3_keys(), q3_fams(), 10, cands_view(buf@, len as int), gseq(m, p, o_lo as int, q2))
                    &&& forall|u: int| o_lo <= u < q2 && #[trigger] good(m, p, u) ==> labs(m, p, u) <= i128_max()
                },
            decreases n - i + if found { 0int } else { 1int },
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
                assert(forall|u: int| 0 <= u < j ==> #[trigger] lpos(m, u) < t);
            }
            let okv = kb + c.o_key_c[t] as i64;
            let (fnd, a, g, ge) = find_run(c, okv, j, l_hi, lg, lge, Ghost(m), Ghost(p));
            let ghost g0 = gseq(m, p, o_lo as int, t as int);
            proof {
                lemma_gseq_step(m, p, o_lo as int, t as int);
            }
            if fnd {
                proof {
                    lemma_found_lb(m, t as int, j as int, a as int);
                    assert forall|u: int| l_hi <= u < m.l_n implies #[trigger] lpos(m, u) > t by {}
                }
                let rs = run_sums(c, okv, a, l_hi, g, ge, Ghost(m), Ghost(p), Ghost(t as int));
                let r = if rs.0 {
                    (rs.1, rs.2, 0u128, false, rs.3, rs.4, rs.5)
                } else {
                    fast_sums(c, okv, a, l_hi, g, ge, Ghost(m), Ghost(p), Ghost(t as int))
                };
                j = r.4;
                lg = r.5;
                lge = r.6;
                if r.0 > 0 {
                    assert(good(m, p, t as int));
                    if r.3 {
                        found = true;
                        found_q = t;
                    } else {
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
            } else {
                proof {
                    lemma_not_found(m, p, t as int, j as int, l_hi as int, o_hi as int);
                }
            }
            proof {
                if !found {
                    q2 = t as int + 1;
                    assert(before(m, q2, j as int)) by {
                        if !fnd {
                            assert forall|u: int| 0 <= u < j implies #[trigger] lpos(m, u) < q2 by {}
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
                assert forall|u: int| 0 <= u < j implies #[trigger] lpos(m, u) < bend by {}
            }
            q = bend;
        }
    }
    (len, found, found_q)
}

} // verus!
