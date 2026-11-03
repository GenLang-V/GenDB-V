//! Run-rank join of the Q12 scan (storages `li_okruns`: the start row of every maximal run of equal l_orderkey
//! along the stored lineitem rows; `li_okmode`: the same run starts as a bitmap, and l_shipmode equality bitmaps).
//! When the runs match the stored orders rows one to one (`runs_match`: run `k`, stored lineitem rows
//! `[st[k], st[k + 1])`, holds exactly the lines of stored orders row `k`), the order of line `j` is its run's index
//! `run_of(j) = nst(j + 1) - 1`, the number of run starts up to `j` less one (`rank_ok`). A block scan
//! (`scan_block_bits`) keeps `base = nst(word start)` and finds the run index of each qualifying line as
//! `base + popcount(run bits & low_mask(lane)) - 1`, so neither l_orderkey nor o_orderkey is read, and the ship-mode
//! test of a row is one bit of the two selected l_shipmode bitmaps.
//! `runs_match` follows from the storage's run facts, the co-clustering of lineitem with orders, the orders primary
//! key and two run-time checks (as many runs as orders, and the last line's key is the last order's key):
//! `lemma_runs_match`; `rank_ok` from it and the run facts (`lemma_rank_runs`).
use vstd::prelude::*;
use super::model::*;
use super::kernel::*;
use super::common::bits::*;
use super::common::popcount::*;

verus! {

/// Row `j` lies in run `k` of the run starts `st`.
pub open spec fn in_run(st: Seq<u32>, k: int, j: int) -> bool {
    st[k] <= j < st[k + 1]
}

/// The run starts `st` match the stored orders rows one to one: every stored lineitem row of run `k` belongs to
/// stored orders row `k` (`rpos`), with the shape facts the cursor needs.
pub open spec fn runs_match(c: Cols, st: Seq<u32>) -> bool {
    &&& st.len() == c.n_o + 1
    &&& 1 <= c.n_o <= u32::MAX
    &&& c.n_l <= u32::MAX
    &&& c.bs_o <= c.n_o
    &&& st[0] == 0
    &&& st[c.n_o as int] == c.n_l
    &&& forall|k: int, j: int| 0 <= k < c.n_o && 0 <= j < c.n_l && #[trigger] in_run(st, k, j)
        ==> rpos(c, lkey(c, j)) == k
}

// ------------------------------------------------------------------------------------------------ runs = orders

/// Run `k` of `st` over the model: nonempty inside the table, one l_orderkey, another key right after it.
pub open spec fn run_wf(c: Cols, st: Seq<u32>, k: int) -> bool {
    let a = st[k] as int;
    let b = st[k + 1] as int;
    &&& a < b <= c.n_l
    &&& forall|j: int| a <= j < b ==> #[trigger] lkey(c, j) == lkey(c, a)
    &&& b < c.n_l ==> lkey(c, b) != lkey(c, b - 1)
}

/// The run facts of storage `li_okruns` over the model: the first start 0, every run well formed.
pub open spec fn starts_ok(c: Cols, st: Seq<u32>) -> bool {
    &&& st.len() >= 1
    &&& st[0] == 0
    &&& forall|k: int| 0 <= k < st.len() - 1 ==> #[trigger] run_wf(c, st, k)
}

/// The stored orders row of run `k`'s key.
pub open spec fn frun(c: Cols, st: Seq<u32>, k: int) -> int {
    rpos(c, lkey(c, st[k] as int))
}

/// Consecutive runs belong to strictly increasing orders rows, when the later one has an order: the rows follow
/// the orders (`lines_clustered`), and equal orders rows would give the two runs one key.
proof fn lemma_frun_step(c: Cols, st: Seq<u32>, k: int)
    requires
        starts_ok(c, st),
        lines_clustered(c),
        keys_distinct(c),
        0 <= k,
        k + 2 < st.len(),
        frun(c, st, k + 1) < c.n_o,
    ensures frun(c, st, k) < frun(c, st, k + 1),
{
    let a = st[k] as int;
    let b = st[k + 1] as int;
    assert(run_wf(c, st, k));
    assert(run_wf(c, st, k + 1));
    assert(lkey(c, b - 1) == lkey(c, a));
    lemma_lines_le(c, a, b);
    lemma_rpos_bound(c, lkey(c, a));
    lemma_rpos_bound(c, lkey(c, b));
}

/// Every run up to the last belongs to an orders row at most its index.
proof fn lemma_frun_upper(c: Cols, st: Seq<u32>, k: int)
    requires
        starts_ok(c, st),
        lines_clustered(c),
        keys_distinct(c),
        st.len() == c.n_o + 1,
        0 <= k < c.n_o,
        frun(c, st, c.n_o - 1) == c.n_o - 1,
    ensures frun(c, st, k) <= k,
    decreases c.n_o - k,
{
    if k < c.n_o - 1 {
        lemma_frun_upper(c, st, k + 1);
        lemma_frun_step(c, st, k);
    }
}

/// Every run belongs to an orders row at least its index.
proof fn lemma_frun_lower(c: Cols, st: Seq<u32>, k: int)
    requires
        starts_ok(c, st),
        lines_clustered(c),
        keys_distinct(c),
        st.len() == c.n_o + 1,
        0 <= k < c.n_o,
        frun(c, st, c.n_o - 1) == c.n_o - 1,
    ensures frun(c, st, k) >= k,
    decreases k,
{
    if k == 0 {
        lemma_rpos_bound(c, lkey(c, st[0] as int));
    } else {
        lemma_frun_lower(c, st, k - 1);
        lemma_frun_upper(c, st, k);
        lemma_frun_step(c, st, k - 1);
    }
}

/// As many runs as orders rows, the runs covering the table, and the last line's key the last order's key: run `k`
/// belongs to orders row `k` (a strictly increasing map of `[0, n_o)` into itself is the identity).
pub proof fn lemma_runs_match(c: Cols, st: Seq<u32>)
    requires
        c.bs_o >= 1,
        starts_ok(c, st),
        lines_clustered(c),
        keys_distinct(c),
        st.len() == c.n_o + 1,
        1 <= c.n_o <= u32::MAX,
        1 <= c.n_l <= u32::MAX,
        c.bs_o <= c.n_o,
        st[c.n_o as int] == c.n_l,
        okey(c, c.n_o - 1) == lkey(c, c.n_l - 1),
    ensures runs_match(c, st),
{
    let last = c.n_o - 1;
    assert(run_wf(c, st, last));
    assert(lkey(c, c.n_l - 1) == lkey(c, st[last] as int));
    lemma_rpos_of(c, last);
    assert forall|k: int, j: int| 0 <= k < c.n_o && 0 <= j < c.n_l && #[trigger] in_run(st, k, j)
        implies rpos(c, lkey(c, j)) == k by {
        lemma_frun_upper(c, st, k);
        lemma_frun_lower(c, st, k);
        assert(run_wf(c, st, k));
    }
}

/// The run-time checks of `lemma_runs_match`: true only when the runs match the orders rows.
pub fn check_runs(c: &Cols, st: &[u32], clustered: bool, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>) -> (ok: bool)
    requires
        cols_ok(*c, kp, km),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
        starts_ok(*c, st@),
    ensures ok ==> runs_match(*c, st@) && rank_ok(*c),
{
    let n_o = c.n_o;
    let n_l = c.n_l;
    if !clustered || n_o == 0 || n_l == 0 || n_o >= u32::MAX as usize || n_l >= u32::MAX as usize || c.bs_o > n_o {
        return false;
    }
    if st.len() != n_o + 1 {
        return false;
    }
    if st[n_o] as usize != n_l {
        return false;
    }
    proof {
        lemma_div_below(n_o - 1, c.bs_o as int, c.ok_bases@.len() as int);
        lemma_div_below(n_l - 1, c.bs_l as int, c.lk_bases@.len() as int);
    }
    let ko = c.ok_bases[(n_o - 1) / c.bs_o] as i128 + c.ok_codes[n_o - 1] as i128;
    let kl = c.lk_bases[(n_l - 1) / c.bs_l] as i128 + c.lk_codes[n_l - 1] as i128;
    if ko != kl {
        return false;
    }
    proof {
        lemma_runs_match(*c, st@);
        lemma_rank_runs(*c, st@);
    }
    true
}

// ------------------------------------------------------------------------------------------------ run ranks

/// Row `j` starts a run of equal l_orderkey.
pub open spec fn lstart(c: Cols, j: int) -> bool {
    j == 0 || lkey(c, j) != lkey(c, j - 1)
}

/// Number of run starts among rows `[0, e)`.
pub open spec fn nst(c: Cols, e: int) -> int
    decreases e,
{
    if e <= 0 { 0 } else { nst(c, e - 1) + if lstart(c, e - 1) { 1int } else { 0int } }
}

/// The run index of row `j`: run starts up to `j`, less one.
pub open spec fn run_of(c: Cols, j: int) -> int {
    nst(c, j + 1) - 1
}

/// Every stored lineitem row belongs to the stored orders row of its run index.
pub open spec fn rank_ok(c: Cols) -> bool {
    forall|j: int| 0 <= j < c.n_l ==> 0 <= #[trigger] run_of(c, j) < c.n_o && rpos(c, lkey(c, j)) == run_of(c, j)
}

/// The run starts increase strictly.
proof fn lemma_st_mono(c: Cols, st: Seq<u32>, a: int, b: int)
    requires starts_ok(c, st), 0 <= a < b < st.len(),
    ensures st[a] < st[b],
    decreases b - a,
{
    assert(run_wf(c, st, b - 1));
    if a < b - 1 {
        lemma_st_mono(c, st, a, b - 1);
    }
}

/// Row `j` lies in exactly one run.
proof fn lemma_run_unique(c: Cols, st: Seq<u32>, r: int, q: int, j: int)
    requires
        starts_ok(c, st),
        0 <= r < st.len() - 1,
        0 <= q < st.len() - 1,
        in_run(st, r, j),
        in_run(st, q, j),
    ensures r == q,
{
    if r < q {
        if r + 1 < q {
            lemma_st_mono(c, st, r + 1, q);
        }
    } else if q < r {
        if q + 1 < r {
            lemma_st_mono(c, st, q + 1, r);
        }
    }
}

/// Row `j` lies in run `run_of(j)` (by induction over the rows: a row starts a new run exactly when it is the next
/// run start).
proof fn lemma_rank_at(c: Cols, st: Seq<u32>, j: int)
    requires
        starts_ok(c, st),
        st.len() == c.n_o + 1,
        c.n_o >= 1,
        st[c.n_o as int] == c.n_l,
        0 <= j < c.n_l,
    ensures
        0 <= run_of(c, j) < c.n_o,
        in_run(st, run_of(c, j), j),
    decreases j,
{
    if j == 0 {
        assert(run_wf(c, st, 0));
        assert(nst(c, 1) == 1);
    } else {
        lemma_rank_at(c, st, j - 1);
        let r = run_of(c, j - 1);
        assert(run_wf(c, st, r));
        assert(nst(c, j + 1) == nst(c, j) + if lstart(c, j) { 1int } else { 0int });
        if lstart(c, j) {
            // j - 1 is the last row of run r: j is the next start
            if j < st[r + 1] {
                assert(lkey(c, j) == lkey(c, st[r] as int));
                assert(lkey(c, j - 1) == lkey(c, st[r] as int));
            }
            assert(j == st[r + 1]);
            if r + 1 == c.n_o {
                assert(false);
            }
            assert(run_wf(c, st, r + 1));
        } else {
            if j == st[r + 1] {
                assert(st[r + 1] < c.n_l);
            }
        }
    }
}

/// The runs matching the orders give every row's order by its run index.
pub proof fn lemma_rank_runs(c: Cols, st: Seq<u32>)
    requires
        starts_ok(c, st),
        runs_match(c, st),
    ensures rank_ok(c),
{
    assert forall|j: int| 0 <= j < c.n_l implies 0 <= #[trigger] run_of(c, j) < c.n_o
        && rpos(c, lkey(c, j)) == run_of(c, j) by {
        lemma_rank_at(c, st, j);
    }
}

/// `nst` grows by at most one per row.
pub proof fn lemma_nst_bound(c: Cols, e: int)
    requires 0 <= e,
    ensures 0 <= nst(c, e) <= e,
    decreases e,
{
    if e > 0 {
        lemma_nst_bound(c, e - 1);
    }
}

// ------------------------------------------------------------------------------------------------ bitmaps

/// The bitmaps of storage li_okmode: the run-start bitmap and `nm` l_shipmode bitmaps of `nw` words.
pub struct Bits {
    pub run: &'static [u64],
    pub mode: &'static [u64],
    pub nw: usize,
    pub nm: usize,
}

impl Copy for Bits {}

impl Clone for Bits {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// The run-start bit of row `j`.
pub open spec fn run_bit(b: Bits, j: int) -> bool {
    lane(b.run@[j / 64], j % 64)
}

/// The bit of row `j` in l_shipmode bitmap `k`.
pub open spec fn mode_bit(b: Bits, k: int, j: int) -> bool {
    lane(b.mode@[k * b.nw + j / 64], j % 64)
}

/// What the bitmaps mean over the model's rows.
pub open spec fn bits_ok(c: Cols, b: Bits) -> bool {
    &&& b.run@.len() == b.nw
    &&& b.mode@.len() == b.nm * b.nw
    &&& c.n_l <= b.nw * 64
    &&& forall|j: int| 0 <= j < c.n_l ==> #[trigger] run_bit(b, j) == lstart(c, j)
    &&& forall|k: int, j: int| 0 <= k < b.nm && 0 <= j < c.n_l ==> #[trigger] mode_bit(b, k, j) == (lmode(c, j) == k)
}

/// The selected l_shipmode bitmaps: words `o0 + w` masked by `k0` (all ones when `$1`'s entry has a bitmap, 0 when
/// no entry holds `$1`), and the same for `$2`.
pub struct Sel {
    pub o0: usize,
    pub k0: u64,
    pub o1: usize,
    pub k1: u64,
}

impl Copy for Sel {}

impl Clone for Sel {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// The selection matches the window's ship-mode entries.
pub open spec fn sel_ok(c: Cols, w: Win, b: Bits, s: Sel) -> bool {
    &&& b.mode@.len() <= usize::MAX
    &&& s.o0 + b.nw <= b.mode@.len()
    &&& s.o1 + b.nw <= b.mode@.len()
    &&& s.k0 == 0 || s.k0 == u64::MAX
    &&& s.k1 == 0 || s.k1 == u64::MAX
    &&& s.k0 == u64::MAX ==> w.s0 < b.nm && s.o0 == w.s0 * b.nw
    &&& s.k0 == 0 ==> w.s0 == u64::MAX
    &&& s.k1 == u64::MAX ==> w.s1 < b.nm && s.o1 == w.s1 * b.nw
    &&& s.k1 == 0 ==> w.s1 == u64::MAX
}

/// Every o_orderpriority group base is 0: the priority entry of orders row `p` is its code.
pub open spec fn prio_flat(c: Cols) -> bool {
    forall|g: int| 0 <= g < c.op_bases@.len() ==> #[trigger] c.op_bases@[g] == 0
}

/// Everything the bitmap path relies on.
pub open spec fn fast_ok(c: Cols, w: Win, st: Seq<u32>, b: Bits, s: Sel) -> bool {
    &&& starts_ok(c, st)
    &&& runs_match(c, st)
    &&& rank_ok(c)
    &&& bits_ok(c, b)
    &&& sel_ok(c, w, b, s)
    &&& prio_flat(c)
    &&& c.bs_l % 64 == 0
}

/// Row `64 w + i` of word `w`: `/ 64` is `w`, `% 64` is `i`.
pub proof fn lemma_word_row(w: int, i: int)
    requires 0 <= w, 0 <= i < 64,
    ensures (64 * w + i) / 64 == w, (64 * w + i) % 64 == i,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(64 * w + i, 64, w, i);
}

/// Over the word of rows `[64 wg, 64 wg + 64)`: the run starts before row `64 wg + k` are those before the word
/// plus the set lanes of the word's run bits below `k`.
proof fn lemma_nst_word(c: Cols, b: Bits, wg: int, k: int)
    requires
        bits_ok(c, b),
        0 <= wg,
        64 * wg + 64 <= c.n_l,
        0 <= k <= 64,
    ensures nst(c, 64 * wg + k) == nst(c, 64 * wg) + cnt_lanes(b.run@[wg], k),
    decreases k,
{
    if k > 0 {
        lemma_nst_word(c, b, wg, k - 1);
        lemma_word_row(wg, k - 1);
        assert(run_bit(b, 64 * wg + k - 1) == lstart(c, 64 * wg + k - 1));
    }
}

// ------------------------------------------------------------------------------------------------ the rank at a row

/// `nst(j0)` at row `j0 < n_l`: the run `r` containing `j0` (binary search over the run starts, keeping
/// `st[lo] <= j0 < st[hi]`) is `run_of(j0)`, so `nst(j0) = r + 1` less one when `j0` starts its run.
pub fn rank_at(c: &Cols, st: &[u32], b: &Bits, Ghost(w): Ghost<Win>, Ghost(s): Ghost<Sel>, j0: usize) -> (base: usize)
    requires
        fast_ok(*c, w, st@, *b, s),
        j0 < c.n_l,
    ensures base as int == nst(*c, j0 as int),
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = c.n_o;
    while hi - lo > 1
        invariant
            fast_ok(*c, w, st@, *b, s),
            j0 < c.n_l,
            lo < hi <= c.n_o,
            st@[lo as int] <= j0 < st@[hi as int],
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if st[mid] as usize <= j0 {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    proof {
        lemma_rank_at(*c, st@, j0 as int);
        lemma_run_unique(*c, st@, lo as int, run_of(*c, j0 as int), j0 as int);
        lemma_word_row((j0 / 64) as int, (j0 % 64) as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j0 as int, 64);
        assert(run_bit(*b, j0 as int) == lstart(*c, j0 as int));
        assert(j0 / 64 < b.nw);
    }
    let x = b.run[j0 / 64];
    let sb = (x >> (j0 % 64) as u64) & 1u64;
    proof {
        assert(sb <= 1) by (bit_vector)
            requires sb == (x >> ((j0 % 64) as u64)) & 1u64;
        assert(nst(*c, j0 + 1) == nst(*c, j0 as int) + if lstart(*c, j0 as int) { 1int } else { 0int });
    }
    lo + 1 - sb as usize
}

// ------------------------------------------------------------------------------------------------ the block scan

/// The `u32` lane mask of the date tests of the 32 rows from `j0 + off` (`off` 0 or 32) of a 64-row word in a
/// small group `g`: lane `k` is set exactly when row `j0 + off + k` passes the receipt window and the two date
/// comparisons. Branch-free over exact-length code slices.
#[inline(always)]
fn date_half(c: &Cols, w: &Win, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>, Ghost(g): Ghost<int>, t: &Thr16,
    Ghost(j0): Ghost<int>, rw: &[u16], cw: &[u16], sw: &[u16], off: usize) -> (x: u32)
    requires
        cols_ok(*c, kp, km),
        0 <= j0,
        j0 + 64 <= c.n_l,
        g * c.bs_l <= j0,
        j0 + 64 <= g * c.bs_l + c.bs_l,
        thr16_ok(*c, *w, g, *t),
        t.fast,
        rw@ == c.lr_codes@.subrange(j0, j0 + 64),
        cw@ == c.lc_codes@.subrange(j0, j0 + 64),
        sw@ == c.ls_codes@.subrange(j0, j0 + 64),
        off == 0 || off == 32,
    ensures forall|k: int| 0 <= k < 32 ==> #[trigger] lane32(x, k) == ldates(*c, *w, j0 + off + k),
    no_unwind
{
    let ra = t.ra;
    let rb = t.rb;
    let ecr = t.ecr;
    let esc = t.esc;
    let mut x: u32 = 0;
    let mut b: u32 = 0;
    proof {
        lemma_zero_lanes32();
    }
    while b < 32
        invariant
            cols_ok(*c, kp, km),
            0 <= j0,
            j0 + 64 <= c.n_l,
            g * c.bs_l <= j0,
            j0 + 64 <= g * c.bs_l + c.bs_l,
            thr16_ok(*c, *w, g, *t),
            t.fast,
            ra == t.ra && rb == t.rb && ecr == t.ecr && esc == t.esc,
            rw@ == c.lr_codes@.subrange(j0, j0 + 64),
            cw@ == c.lc_codes@.subrange(j0, j0 + 64),
            sw@ == c.ls_codes@.subrange(j0, j0 + 64),
            off == 0 || off == 32,
            b <= 32,
            clear_from32(x, b as int),
            forall|k: int| 0 <= k < b ==> #[trigger] lane32(x, k) == ldates(*c, *w, j0 + off + k),
        decreases 32 - b,
    {
        let i = off + b as usize;
        proof {
            lemma_div_group(j0 + i, c.bs_l as int, g);
            lemma_dates16(*c, *w, kp, km, g, *t, j0 + i);
        }
        let r = rw[i] as i16;
        let cv = cw[i] as i16;
        let s = sw[i] as i16;
        let q1: u32 = if r > ra { 1 } else { 0 };
        let q2: u32 = if r <= rb { 1 } else { 0 };
        let q3: u32 = if cv - r <= ecr { 1 } else { 0 };
        let q4: u32 = if s - cv <= esc { 1 } else { 0 };
        let q: u32 = q1 & q2 & q3 & q4;
        proof {
            assert(q <= 1u32 && (q == 1u32 <==> (q1 == 1u32 && q2 == 1u32 && q3 == 1u32 && q4 == 1u32))) by (bit_vector)
                requires q1 <= 1 && q2 <= 1 && q3 <= 1 && q4 <= 1, q == q1 & q2 & q3 & q4;
        }
        x = put_lane32(x, b, q);
        b = b + 1;
    }
    x
}

/// `date_half` for a group whose receipt dates all lie in the window (`inner_ok`): only the two date comparisons.
#[inline(always)]
fn date_half_in(c: &Cols, w: &Win, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>, Ghost(g): Ghost<int>, t: &Thr16,
    Ghost(j0): Ghost<int>, rw: &[u16], cw: &[u16], sw: &[u16], off: usize) -> (x: u32)
    requires
        cols_ok(*c, kp, km),
        0 <= j0,
        j0 + 64 <= c.n_l,
        g * c.bs_l <= j0,
        j0 + 64 <= g * c.bs_l + c.bs_l,
        thr16_ok(*c, *w, g, *t),
        t.fast,
        inner_ok(*c, *w, g),
        rw@ == c.lr_codes@.subrange(j0, j0 + 64),
        cw@ == c.lc_codes@.subrange(j0, j0 + 64),
        sw@ == c.ls_codes@.subrange(j0, j0 + 64),
        off == 0 || off == 32,
    ensures forall|k: int| 0 <= k < 32 ==> #[trigger] lane32(x, k) == ldates(*c, *w, j0 + off + k),
    no_unwind
{
    let ecr = t.ecr;
    let esc = t.esc;
    let mut x: u32 = 0;
    let mut b: u32 = 0;
    proof {
        lemma_zero_lanes32();
    }
    while b < 32
        invariant
            cols_ok(*c, kp, km),
            0 <= j0,
            j0 + 64 <= c.n_l,
            g * c.bs_l <= j0,
            j0 + 64 <= g * c.bs_l + c.bs_l,
            thr16_ok(*c, *w, g, *t),
            t.fast,
            inner_ok(*c, *w, g),
            ecr == t.ecr && esc == t.esc,
            rw@ == c.lr_codes@.subrange(j0, j0 + 64),
            cw@ == c.lc_codes@.subrange(j0, j0 + 64),
            sw@ == c.ls_codes@.subrange(j0, j0 + 64),
            off == 0 || off == 32,
            b <= 32,
            clear_from32(x, b as int),
            forall|k: int| 0 <= k < b ==> #[trigger] lane32(x, k) == ldates(*c, *w, j0 + off + k),
        decreases 32 - b,
    {
        let i = off + b as usize;
        proof {
            lemma_div_group(j0 + i, c.bs_l as int, g);
            lemma_dates16_in(*c, *w, kp, km, g, *t, j0 + i);
        }
        let r = rw[i] as i16;
        let cv = cw[i] as i16;
        let s = sw[i] as i16;
        let q3: u32 = if cv - r <= ecr { 1 } else { 0 };
        let q4: u32 = if s - cv <= esc { 1 } else { 0 };
        let q: u32 = q3 & q4;
        proof {
            assert(q <= 1u32 && (q == 1u32 <==> (q3 == 1u32 && q4 == 1u32))) by (bit_vector)
                requires q3 <= 1 && q4 <= 1, q == q3 & q4;
        }
        x = put_lane32(x, b, q);
        b = b + 1;
    }
    x
}

/// Row `j` passes the receipt window and the two date comparisons (`lqual` without the ship mode).
pub open spec fn ldates(c: Cols, w: Win, j: int) -> bool {
    &&& w.lo <= lrcp(c, j) <= w.hi
    &&& lcmt(c, j) < lrcp(c, j)
    &&& lship(c, j) < lcmt(c, j)
}

/// Every receipt date of lineitem group `g` lies in the window (by its zone): the receipt test always holds there.
pub open spec fn inner_ok(c: Cols, w: Win, g: int) -> bool {
    w.lo <= c.lr_bases@[g] && c.lr_zmax@[g] <= w.hi
}

/// In a group inside the receipt window, the 16-bit date tests of row `j` reduce to the two comparisons.
proof fn lemma_dates16_in(c: Cols, w: Win, kp: int, km: int, g: int, t: Thr16, j: int)
    requires
        cols_ok(c, kp, km),
        0 <= j < c.n_l,
        j / c.bs_l as int == g,
        thr16_ok(c, w, g, t),
        t.fast,
        inner_ok(c, w, g),
    ensures ({
        let r = c.lr_codes@[j] as int;
        let cc = c.lc_codes@[j] as int;
        let s = c.ls_codes@[j] as int;
        &&& r <= 32767 && cc <= 32767 && s <= 32767
        &&& ldates(c, w, j) == (cc - r <= t.ecr && s - cc <= t.esc)
    }),
{
    lemma_dates16(c, w, kp, km, g, t, j);
    assert(lrcp(c, j) <= c.lr_zmax@[g]);
}

/// The 16-bit date tests on the raw codes of row `j` (in a small group `g`) are `ldates`.
proof fn lemma_dates16(c: Cols, w: Win, kp: int, km: int, g: int, t: Thr16, j: int)
    requires
        cols_ok(c, kp, km),
        0 <= j < c.n_l,
        j / c.bs_l as int == g,
        thr16_ok(c, w, g, t),
        t.fast,
    ensures ({
        let r = c.lr_codes@[j] as int;
        let cc = c.lc_codes@[j] as int;
        let s = c.ls_codes@[j] as int;
        &&& r <= 32767 && cc <= 32767 && s <= 32767
        &&& ldates(c, w, j) == (r > t.ra && r <= t.rb && cc - r <= t.ecr && s - cc <= t.esc)
    }),
{
    assert(lrcp(c, j) <= c.lr_zmax@[g]);
    assert(lcmt(c, j) <= c.lc_zmax@[g]);
    assert(lship(c, j) <= c.ls_zmax@[g]);
}

/// The lane mask of the 64 rows of global word `wg` (rows from `64 wg`, in a small group `g`): lane `k` is set
/// exactly when row `64 wg + k` qualifies; `m0` holds the rows of `$1`'s ship mode.
#[inline(always)]
fn word_bits(c: &Cols, w: &Win, b: &Bits, s: &Sel, Ghost(st): Ghost<Seq<u32>>, Ghost(kp): Ghost<int>,
    Ghost(km): Ghost<int>, Ghost(g): Ghost<int>, t: &Thr16, inner: bool, wg: usize) -> (r: (u64, u64))
    requires
        inner ==> inner_ok(*c, *w, g),
        cols_ok(*c, kp, km),
        fast_ok(*c, *w, st, *b, *s),
        64 * wg + 64 <= c.n_l,
        g * c.bs_l <= 64 * wg,
        64 * wg + 64 <= g * c.bs_l + c.bs_l,
        thr16_ok(*c, *w, g, *t),
        t.fast,
    ensures
        forall|k: int| 0 <= k < 64 ==> #[trigger] lane(r.0, k) == lqual(*c, *w, 64 * wg + k),
        forall|k: int| 0 <= k < 64 ==> #[trigger] lane(r.1, k) == (lmode(*c, 64 * wg + k) == w.s0),
    no_unwind
{
    let wb = 64 * wg;
    let rw = sub16(c.lr_codes, wb, WL);
    let cw = sub16(c.lc_codes, wb, WL);
    let sw = sub16(c.ls_codes, wb, WL);
    let (lo, hi) = if inner {
        (date_half_in(c, w, Ghost(kp), Ghost(km), Ghost(g), t, Ghost(wb as int), rw, cw, sw, 0),
        date_half_in(c, w, Ghost(kp), Ghost(km), Ghost(g), t, Ghost(wb as int), rw, cw, sw, 32))
    } else {
        (date_half(c, w, Ghost(kp), Ghost(km), Ghost(g), t, Ghost(wb as int), rw, cw, sw, 0),
        date_half(c, w, Ghost(kp), Ghost(km), Ghost(g), t, Ghost(wb as int), rw, cw, sw, 32))
    };
    let d = (lo as u64) | ((hi as u64) << 32u64);
    proof {
        assert(bits_ok(*c, *b));
        assert(sel_ok(*c, *w, *b, *s));
        assert(64 * wg < 64 * b.nw);
        assert(wg < b.nw);
        assert(s.o0 + wg < b.mode@.len());
        assert(s.o1 + wg < b.mode@.len());
    }
    let m0 = b.mode[s.o0 + wg] & s.k0;
    let m1 = b.mode[s.o1 + wg] & s.k1;
    let x = d & (m0 | m1);
    proof {
        lemma_join32(lo, hi, d);
        assert forall|k: int| 0 <= k < 64 implies #[trigger] lane(d, k) == ldates(*c, *w, wb + k) by {
            if k < 32 {
                assert(lane32(lo, k) == ldates(*c, *w, wb + 0 + k));
            } else {
                assert(lane32(hi, k - 32) == ldates(*c, *w, wb + 32 + (k - 32)));
            }
        }
        assert forall|k: int| 0 <= k < 64 implies #[trigger] lane(m0, k) == (lmode(*c, wb + k) == w.s0) by {
            lemma_word_row(wg as int, k);
            lemma_and_lane(b.mode@[s.o0 + wg], s.k0, k);
            let kk = k as u64;
            assert(((u64::MAX >> kk) & 1u64 == 1u64) && ((0u64 >> kk) & 1u64 != 1u64)) by (bit_vector)
                requires kk < 64;
            if s.k0 == u64::MAX {
                assert(s.o0 + wg == w.s0 * b.nw + (wb + k) / 64);
                assert(mode_bit(*b, w.s0 as int, wb + k) == (lmode(*c, wb + k) == w.s0));
            } else {
                assert(0 <= lmode(*c, wb + k) < km);
            }
        }
        assert forall|k: int| 0 <= k < 64 implies #[trigger] lane(m1, k) == (lmode(*c, wb + k) == w.s1) by {
            lemma_word_row(wg as int, k);
            lemma_and_lane(b.mode@[s.o1 + wg], s.k1, k);
            let kk = k as u64;
            assert(((u64::MAX >> kk) & 1u64 == 1u64) && ((0u64 >> kk) & 1u64 != 1u64)) by (bit_vector)
                requires kk < 64;
            if s.k1 == u64::MAX {
                assert(s.o1 + wg == w.s1 * b.nw + (wb + k) / 64);
                assert(mode_bit(*b, w.s1 as int, wb + k) == (lmode(*c, wb + k) == w.s1));
            } else {
                assert(0 <= lmode(*c, wb + k) < km);
            }
        }
        assert forall|k: int| 0 <= k < 64 implies #[trigger] lane(x, k) == lqual(*c, *w, wb + k) by {
            assert(lane(d, k) == ldates(*c, *w, wb + k));
            assert(lane(m0, k) == (lmode(*c, wb + k) == w.s0));
            assert(lane(m1, k) == (lmode(*c, wb + k) == w.s1));
            let kk = k as u64;
            assert(((x >> kk) & 1u64 == 1u64) == (((d >> kk) & 1u64 == 1u64)
                && (((m0 >> kk) & 1u64 == 1u64) || ((m1 >> kk) & 1u64 == 1u64)))) by (bit_vector)
                requires x == d & (m0 | m1), kk < 64;
        }
    }
    (x, m0)
}

/// Counts the qualifying lines of global word `wg` (the set lanes of `x0`; `m0` marks `$1`'s mode) in row order:
/// line `64 wg + t` belongs to orders row `base + popcount(run bits & low_mask(t)) - 1`.
#[inline(always)]
fn count_word_bits(c: &Cols, w: &Win, b: &Bits, s: &Sel, tab: &[u8; 64], Ghost(st): Ghost<Seq<u32>>,
    Ghost(kp): Ghost<int>, km: usize, wg: usize, x0: u64, m0: u64, base: usize, hi_cnt: &mut Vec<usize>,
    lo_cnt: &mut Vec<usize>, Ghost(j0): Ghost<int>)
    requires
        tz_table_ok(*tab),
        cols_ok(*c, kp, km as int),
        fast_ok(*c, *w, st, *b, *s),
        win_ok(*w),
        0 <= j0 <= 64 * wg,
        64 * wg + 64 <= c.n_l,
        base as int == nst(*c, 64 * wg),
        forall|k: int| 0 <= k < 64 ==> #[trigger] lane(x0, k) == lqual(*c, *w, 64 * wg + k),
        forall|k: int| 0 <= k < 64 ==> #[trigger] lane(m0, k) == (lmode(*c, 64 * wg + k) == w.s0),
        counts_at(*c, *w, km as int, old(hi_cnt)@, old(lo_cnt)@, j0, 64 * wg),
    ensures
        counts_at(*c, *w, km as int, final(hi_cnt)@, final(lo_cnt)@, j0, 64 * wg + 64),
    no_unwind
{
    let wb = 64 * wg;
    proof {
        assert(wg < b.nw);
    }
    let rb = b.run[wg];
    let mut x = x0;
    let ghost mut pos: int = 0;
    while x != 0
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km as int),
            fast_ok(*c, *w, st, *b, *s),
            win_ok(*w),
            0 <= j0 <= wb,
            wb == 64 * wg,
            wb + 64 <= c.n_l,
            wg < b.nw,
            rb == b.run@[wg as int],
            base as int == nst(*c, wb as int),
            forall|k: int| 0 <= k < 64 ==> #[trigger] lane(x0, k) == lqual(*c, *w, wb + k),
            forall|k: int| 0 <= k < 64 ==> #[trigger] lane(m0, k) == (lmode(*c, wb + k) == w.s0),
            0 <= pos <= 64,
            forall|k: int| 0 <= k < 64 ==> #[trigger] lane(x, k) == (k >= pos && lane(x0, k)),
            counts_at(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, wb + pos),
        decreases 64 - pos,
    {
        let t = lowest_lane(tab, x);
        let ghost j = wb + t;
        proof {
            assert(t >= pos);
            assert forall|k: int| wb + pos <= k < j implies !#[trigger] lqual(*c, *w, k) by {
                assert(!lane(x, k - wb));
            }
            lemma_counts_skip(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, wb + pos, j);
            assert(lqual(*c, *w, j)) by {
                assert(lane(x0, t as int));
            }
        }
        let lm = low_mask(t);
        let pc = popcount(rb & lm);
        proof {
            lemma_rank(rb, lm, t as int);
            lemma_nst_word(*c, *b, wg as int, t + 1);
            assert(run_of(*c, j) == nst(*c, j + 1) - 1);
            assert(0 <= run_of(*c, j) < c.n_o && rpos(*c, lkey(*c, j)) == run_of(*c, j));
            lemma_nst_bound(*c, wb as int);
        }
        let p = base + pc as usize - 1;
        proof {
            lemma_div_below(p as int, c.bs_o as int, c.ok_bases@.len() as int);
            assert(c.op_bases@[(p as int) / (c.bs_o as int)] == 0);
            assert(oprio(*c, p as int) == c.op_codes@[p as int]);
            assert(0 <= oprio(*c, p as int) < kp);
        }
        let e = c.op_codes[p] as u64;
        // Branch-free: the priority of a line's order is unpredictable.
        let h0b: usize = if e == w.u0 { 1 } else { 0 };
        let h1b: usize = if e == w.u1 { 1 } else { 0 };
        let h: usize = h0b | h1b;
        let is0 = (m0 >> t) & 1u64;
        proof {
            assert(h == 1usize <==> (h0b == 1usize || h1b == 1usize)) by (bit_vector)
                requires h0b <= 1, h1b <= 1, h == h0b | h1b;
            assert(h <= 1usize) by (bit_vector)
                requires h0b <= 1, h1b <= 1, h == h0b | h1b;
            assert(is0 <= 1) by (bit_vector)
                requires is0 == (m0 >> t) & 1u64;
            assert((is0 == 1) == (lmode(*c, j) == w.s0)) by {
                assert(lane(m0, t as int) == (lmode(*c, wb + t) == w.s0));
            }
            assert(0 <= lmode(*c, j) < km);
        }
        let md = if is0 == 1 { w.s0 } else { w.s1 };
        proof {
            assert(md as int == lmode(*c, j));
            lemma_cnt_bound(*c, *w, 0, md as int, j0, j);
            lemma_cnt_bound(*c, *w, 1, md as int, j0, j);
        }
        let m = md as usize;
        let ghost h0 = hi_cnt@;
        let ghost l0 = lo_cnt@;
        hi_cnt[m] = hi_cnt[m] + h;
        lo_cnt[m] = lo_cnt[m] + (1 - h);
        proof {
            assert(rpos(*c, lkey(*c, j)) == p);
            assert forall|d: int| 0 <= d < km implies #[trigger] hi_cnt@[d] as int == h0[d] + lval(*c, *w, 0, d, j) by {
                if d != m as int {
                    assert(lval(*c, *w, 0, d, j) == 0);
                }
            }
            assert forall|d: int| 0 <= d < km implies #[trigger] lo_cnt@[d] as int == l0[d] + lval(*c, *w, 1, d, j) by {
                if d != m as int {
                    assert(lval(*c, *w, 1, d, j) == 0);
                }
            }
            lemma_counts_step(*c, *w, km as int, h0, l0, hi_cnt@, lo_cnt@, j0, j);
        }
        let ghost xo = x;
        x = clear_lowest(x, Ghost(t));
        proof {
            assert forall|k: int| 0 <= k < 64 implies #[trigger] lane(x, k) == (k >= t + 1 && lane(x0, k)) by {
                if k < t {
                    assert(!lane(xo, k));
                }
            }
            pos = t + 1;
        }
    }
    proof {
        assert forall|k: int| wb + pos <= k < wb + 64 implies !#[trigger] lqual(*c, *w, k) by {
            lemma_zero_lanes();
            assert(!lane(x, k - wb));
        }
        lemma_counts_skip(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, wb + pos, wb + 64);
    }
}

/// Scans the `FB` rows of global words `[wg0, wg0 + 64)` of a small lineitem group `g` word by word: the lane mask
/// of the word (dates and ship-mode bitmaps), then its qualifying lines, counted by their orders' priorities through
/// the run ranks. `base` is `nst` at the block's first row; returns it at the next.
pub fn scan_block_bits(c: &Cols, w: &Win, b: &Bits, s: &Sel, tab: &[u8; 64], Ghost(st): Ghost<Seq<u32>>,
    Ghost(kp): Ghost<int>, km: usize, g: usize, t: &Thr16, wg0: usize, base: usize, hi_cnt: &mut Vec<usize>,
    lo_cnt: &mut Vec<usize>, Ghost(j0): Ghost<int>) -> (base2: usize)
    requires
        tz_table_ok(*tab),
        cols_ok(*c, kp, km as int),
        fast_ok(*c, *w, st, *b, *s),
        win_ok(*w),
        0 <= j0 <= 64 * wg0,
        64 * wg0 + FB <= c.n_l,
        g * c.bs_l <= 64 * wg0,
        64 * wg0 + FB <= g * c.bs_l + c.bs_l,
        g < c.lk_bases@.len(),
        thr16_ok(*c, *w, g as int, *t),
        t.fast,
        base as int == nst(*c, 64 * wg0),
        counts_at(*c, *w, km as int, old(hi_cnt)@, old(lo_cnt)@, j0, 64 * wg0),
    ensures
        base2 as int == nst(*c, 64 * wg0 + FB),
        counts_at(*c, *w, km as int, final(hi_cnt)@, final(lo_cnt)@, j0, 64 * wg0 + FB),
    no_unwind
{
    let inner = w.lo <= c.lr_bases[g] && c.lr_zmax[g] <= w.hi;
    // Word by word: the lane masks, the qualifying lines, and the word's run starts into `base`. One pass keeps
    // the streaming loads of the date codes going while the lines are counted.
    let mut bs = base;
    let mut wi: usize = 0;
    while wi < 64
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km as int),
            fast_ok(*c, *w, st, *b, *s),
            win_ok(*w),
            0 <= j0 <= 64 * wg0,
            64 * wg0 + FB <= c.n_l,
            g * c.bs_l <= 64 * wg0,
            64 * wg0 + FB <= g * c.bs_l + c.bs_l,
            g < c.lk_bases@.len(),
            thr16_ok(*c, *w, g as int, *t),
            t.fast,
            inner ==> inner_ok(*c, *w, g as int),
            wi <= 64,
            bs as int == nst(*c, 64 * (wg0 + wi)),
            counts_at(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, 64 * (wg0 + wi)),
        decreases 64 - wi,
    {
        let wg = wg0 + wi;
        let (x, m0) = word_bits(c, w, b, s, Ghost(st), Ghost(kp), Ghost(km as int), Ghost(g as int), t, inner, wg);
        if x != 0 {
            count_word_bits(c, w, b, s, tab, Ghost(st), Ghost(kp), km, wg, x, m0, bs, hi_cnt, lo_cnt, Ghost(j0));
        } else {
            proof {
                assert forall|k: int| 64 * wg <= k < 64 * wg + 64 implies !#[trigger] lqual(*c, *w, k) by {
                    lemma_zero_lanes();
                    assert(!lane(x, k - 64 * wg));
                }
                lemma_counts_skip(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, 64 * wg, 64 * wg + 64);
            }
        }
        proof {
            assert(wg < b.nw);
            lemma_nst_word(*c, *b, wg as int, 64);
            lemma_nst_bound(*c, 64 * wg + 64);
        }
        let pc = popcount(b.run[wg]);
        bs = bs + pc as usize;
        wi = wi + 1;
    }
    bs
}

} // verus!
