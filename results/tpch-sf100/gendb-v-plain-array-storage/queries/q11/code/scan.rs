//! The partsupp scan of one row range `[lo, hi)` (`ScanTask`, one worker task per range).
//!
//! Per block of `BLK` rows: (1) a branch-free selection of the qualifying rows (`select_block`: the supplier of
//! `ps_suppkey` found by its dense key, `base + b` is row `b`, then its bit in the supplier bitmap), (2) a gather of
//! the selected rows' part key and value `ps_supplycost * ps_availqty` into small buffers (`gather_block`;
//! independent loads, so many cache misses are in flight at once), (3) run aggregation (`push_row`): consecutive
//! qualifying rows with the same part key form one run `(sum, key)`, closed when the key changes. A closed run is
//! stored only when its sum exceeds the task's lower bound `lb` of the HAVING threshold (the caller checks
//! `lb <= threshold` afterwards, so no passing group is lost). At the end the stored runs are sorted by sum,
//! descending, in place (`msort::sort_range`, scratch buffers of the same capacity).
//!
//! State (`RunState::inv` at row position `pos`): the ghost list `all` of every closed run plus the open run
//! describe `[lo, pos)` (for every key, their sums add up to the range sum and the key occurs exactly when some row
//! has it); the stored runs are `above(all, lb)`; `sorted` records that the keys have only increased (then `all`
//! has strictly increasing keys, all below the open key); `first_key` is the key of the range's first run; `total`
//! and `mass` are the range's value sum and absolute mass, the mass at most `i128::MAX` (a row that would exceed it
//! stops the scan with `OVER`: the statement is then outside the capacity domain).
//!
//! Buffers: the run and scratch buffers are allocated by the calling thread with `vec![0; cap]`; the caller makes
//! them at least 32 MiB so that the allocator maps fresh zero pages for them (no memset on the calling thread) and
//! only the slots a task writes are ever touched.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::numeric::abs;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::normal::*;
use crate::agent::groups::*;
use crate::agent::sem::lemma_product_bound;
use crate::agent::common::msort::{pairs, desc, sort_range, lemma_pairs_push, lemma_pairs_frame};
use crate::agent::common::bitmap::bit_at;
use crate::agent::filter::Sorted;

verus! {

/// Rows per block.
pub const BLK: usize = 1024;

/// Scan status: done, the absolute mass leaves `i128`, the run buffer is full.
pub const GO: u8 = 0;
pub const OVER: u8 = 1;
pub const FULL: u8 = 2;

/// `i128::MAX` as an integer.
pub open spec fn imax() -> int { i128::MAX as int }

/// `2^113`: a bound of every row value (`sem::lemma_val_bound`).
pub open spec fn vbound() -> int { 0x2_0000_0000_0000_0000_0000_0000_0000 }

// ------------------------------------------------------------------------------------------ supplier lookup facts

/// Bit `b` of the supplier bitmap is the supplier flag of row `b`.
pub open spec fn bits_ok(words: Seq<u64>, nbits: int, sv: StoresView, p: Seq<u8>) -> bool {
    &&& nbits == supp_n(sv)
    &&& 64 * words.len() >= nbits
    &&& forall|b: int| 0 <= b < nbits ==> #[trigger] bit_at(words, b) == supp_ok(sv, p, b)
}

/// The supplier keys are `base, base + 1, ..` up to `last` (at least one supplier).
pub open spec fn dense_ok(sv: StoresView, base: int, last: int) -> bool {
    &&& supp_n(sv) >= 1
    &&& last == base + supp_n(sv) - 1
    &&& forall|b: int| 0 <= b < supp_n(sv) ==> #[trigger] s_keys(sv)[b] == base + b
}

/// With dense supplier keys, a partsupp row qualifies exactly when its supplier key is in range and the bit of
/// supplier `ps_suppkey - base` is set.
pub proof fn lemma_qrow_dense(words: Seq<u64>, sv: StoresView, p: Seq<u8>, base: int, last: int, c: int)
    requires stores_wf(sv), bits_ok(words, supp_n(sv) as int, sv, p), dense_ok(sv, base, last), 0 <= c < ps_n(sv),
    ensures ({
        let s = ps_skeys(sv)[c] as int;
        qrow(sv, p, c) == (base <= s <= last && bit_at(words, s - base))
    }),
{
    let s = ps_skeys(sv)[c] as int;
    if qrow(sv, p, c) {
        let b = choose|b: int| 0 <= b < supp_n(sv) && #[trigger] s_keys(sv)[b] == s && supp_ok(sv, p, b);
        assert(s_keys(sv)[b] == base + b);
    }
    if base <= s <= last && bit_at(words, s - base) {
        let b = s - base;
        assert(s_keys(sv)[b] == base + b);
        assert(key_ok(sv, p, s));
    }
}

/// `2^62`: the bound of the supplier key base and of the supplier count on the fast path.
pub open spec fn off_bound() -> int { 0x4000_0000_0000_0000 }

/// The wrapping offset `s - base` of supplier key `s` lies in `[0, nbits)` exactly when `s` is one of the keys
/// `base .. base + nbits`, and then it is the exact difference (keys far below `base` wrap to at least `2^62`).
pub proof fn lemma_offset(s: i64, base: i64, nbits: i64)
    requires 0 <= base <= off_bound(), 0 <= nbits <= off_bound(),
    ensures
        (0 <= s.wrapping_sub(base) && s.wrapping_sub(base) < nbits) == (base <= s && s < base + nbits),
        0 <= s.wrapping_sub(base) ==> s.wrapping_sub(base) < nbits ==> s.wrapping_sub(base) == s - base,
{
}

// ------------------------------------------------------------------------------------------ run state

/// The run aggregation state of one task.
pub struct RunState {
    pub keys: Vec<i64>,
    pub sums: Vec<i128>,
    pub cap: usize,
    pub used: usize,
    /// Closed runs with a sum above `lb` are stored.
    pub lb: i128,
    pub have: bool,
    pub cur_key: i64,
    pub cur_sum: i128,
    pub first_key: i64,
    pub sorted: bool,
    pub total: i128,
    pub mass: i128,
    /// Every closed run, in row order.
    pub all: Ghost<Seq<(int, int)>>,
}

impl RunState {
    /// The stored runs as (sum, key) pairs.
    pub open spec fn rs(&self) -> Seq<(int, int)> {
        pairs(self.sums@, self.keys@, 0, self.used as int)
    }

    /// The open run's contribution to key `k`.
    pub open spec fn open_sum(&self, k: int) -> int {
        if self.have && self.cur_key as int == k { self.cur_sum as int } else { 0 }
    }

    /// Key `k` has a closed run or is the open run's key.
    pub open spec fn key_in(&self, k: int) -> bool {
        rs_has(self.all@, k) || (self.have && self.cur_key as int == k)
    }

    /// The buffers, and the stored runs are the closed runs above `lb`.
    pub open spec fn wf(&self) -> bool {
        &&& self.keys@.len() == self.cap && self.sums@.len() == self.cap
        &&& self.used <= self.cap
        &&& self.rs() == above(self.all@, self.lb as int)
    }

    /// `first_key` is the key of the first run (closed, or the open one).
    pub open spec fn first_ok(&self) -> bool {
        self.have ==> self.first_key as int == (if self.all@.len() > 0 { self.all@[0].1 } else { self.cur_key as int })
    }

    /// The state describes the rows `[lo, pos)`.
    pub open spec fn inv(&self, sv: StoresView, p: Seq<u8>, lo: int, pos: int) -> bool {
        &&& self.wf()
        &&& 0 <= lo <= pos
        &&& forall|k: int| #[trigger] rs_sum(self.all@, k) + self.open_sum(k) == rsum(sv, p, t_sum(sv, k), lo, pos)
        &&& forall|k: int| #[trigger] self.key_in(k) == (rsum(sv, p, t_cnt(sv, k), lo, pos) > 0)
        &&& !self.have ==> self.all@.len() == 0
        &&& self.sorted ==> strict(self.all@) && (self.have ==> forall|i: int| 0 <= i < self.all@.len() ==> (#[trigger] self.all@[i]).1 < self.cur_key)
        &&& self.first_ok()
        &&& self.total == rsum(sv, p, t_val(sv), lo, pos)
        &&& self.mass == rsum(sv, p, t_absv(sv), lo, pos)
        &&& self.have ==> abs(self.cur_sum as int) <= self.mass
    }

    /// The finished state describes `[lo, hi)`: `have` tells whether there is a run, `first_key` and `cur_key` are
    /// the keys of the first and the last one.
    pub open spec fn done(&self, sv: StoresView, p: Seq<u8>, lo: int, hi: int) -> bool {
        &&& self.wf()
        &&& runs_ok(sv, p, lo, hi, self.all@)
        &&& self.sorted ==> strict(self.all@)
        &&& self.have == (self.all@.len() > 0)
        &&& self.have ==> self.first_key as int == self.all@[0].1 && self.cur_key as int == self.all@.last().1
        &&& self.total == rsum(sv, p, t_val(sv), lo, hi)
        &&& self.mass == rsum(sv, p, t_absv(sv), lo, hi)
    }
}

/// An empty state of `cap` run slots storing runs above `lb` (calling thread; see the module header on buffers).
pub fn new_state(cap: usize, lb: i128) -> (st: RunState)
    ensures st.wf(), st.cap == cap, st.lb == lb, st.used == 0, !st.have, st.sorted, st.total == 0, st.mass == 0,
        st.all@ == Seq::<(int, int)>::empty(),
{
    let st = RunState { keys: vec![0i64; cap], sums: vec![0i128; cap], cap, used: 0, lb, have: false, cur_key: 0,
        cur_sum: 0, first_key: 0, sorted: true, total: 0, mass: 0, all: Ghost(Seq::empty()) };
    proof {
        assert(st.rs() =~= Seq::<(int, int)>::empty());
        assert(above(st.all@, lb as int) =~= Seq::<(int, int)>::empty());
    }
    st
}

/// A fresh state describes the empty range `[lo, lo)`.
pub proof fn lemma_new_inv(st: RunState, sv: StoresView, p: Seq<u8>, lo: int)
    requires st.wf(), !st.have, st.sorted, st.total == 0, st.mass == 0, st.all@ == Seq::<(int, int)>::empty(), 0 <= lo,
    ensures st.inv(sv, p, lo, lo),
{
    assert forall|k: int| #[trigger] st.key_in(k) == (rsum(sv, p, t_cnt(sv, k), lo, lo) > 0) by {}
}

/// Rows `[a, b)` without a qualifying row leave the state's meaning unchanged.
pub proof fn lemma_inv_skip(st: RunState, sv: StoresView, p: Seq<u8>, lo: int, a: int, b: int)
    requires st.inv(sv, p, lo, a), a <= b, forall|x: int| a <= x < b ==> !#[trigger] qrow(sv, p, x),
    ensures st.inv(sv, p, lo, b),
{
    assert forall|k: int| #[trigger] rs_sum(st.all@, k) + st.open_sum(k) == rsum(sv, p, t_sum(sv, k), lo, b) by {
        lemma_rsum_skip(sv, p, t_sum(sv, k), lo, a, b);
    }
    assert forall|k: int| #[trigger] st.key_in(k) == (rsum(sv, p, t_cnt(sv, k), lo, b) > 0) by {
        lemma_rsum_skip(sv, p, t_cnt(sv, k), lo, a, b);
    }
    lemma_rsum_skip(sv, p, t_val(sv), lo, a, b);
    lemma_rsum_skip(sv, p, t_absv(sv), lo, a, b);
}

/// The open run continues with row `c` (same key): the state describes `[lo, c + 1)`.
proof fn lemma_push_same(st0: RunState, st1: RunState, sv: StoresView, p: Seq<u8>, lo: int, c: int)
    requires
        st0.inv(sv, p, lo, c), qrow(sv, p, c), 0 <= c < ps_n(sv),
        st0.have, st0.cur_key as int == ps_pkeys(sv)[c] as int,
        st1.keys == st0.keys, st1.sums == st0.sums, st1.cap == st0.cap, st1.used == st0.used, st1.lb == st0.lb,
        st1.all == st0.all, st1.first_key == st0.first_key,
        st1.have, st1.cur_key == st0.cur_key, st1.cur_sum as int == st0.cur_sum as int + val(sv, c),
        st1.sorted == st0.sorted,
        st1.total as int == st0.total as int + val(sv, c),
        st1.mass as int == st0.mass as int + abs(val(sv, c)),
    ensures st1.inv(sv, p, lo, c + 1),
{
    lemma_rsum_step(sv, p, t_val(sv), lo, c);
    lemma_rsum_step(sv, p, t_absv(sv), lo, c);
    assert forall|kk: int| #[trigger] rs_sum(st1.all@, kk) + st1.open_sum(kk) == rsum(sv, p, t_sum(sv, kk), lo, c + 1) by {
        lemma_rsum_step(sv, p, t_sum(sv, kk), lo, c);
        assert(rs_sum(st0.all@, kk) + st0.open_sum(kk) == rsum(sv, p, t_sum(sv, kk), lo, c));
    }
    assert forall|kk: int| #[trigger] st1.key_in(kk) == (rsum(sv, p, t_cnt(sv, kk), lo, c + 1) > 0) by {
        lemma_rsum_step(sv, p, t_cnt(sv, kk), lo, c);
        lemma_rsum_bounds(sv, p, kk, lo, c);
        assert(st0.key_in(kk) == (rsum(sv, p, t_cnt(sv, kk), lo, c) > 0));
    }
}

/// Row `c` opens a new run after the open run was closed (or after no row): the state describes `[lo, c + 1)`.
proof fn lemma_push_new(st0: RunState, st1: RunState, sv: StoresView, p: Seq<u8>, lo: int, c: int)
    requires
        st0.inv(sv, p, lo, c), qrow(sv, p, c), 0 <= c < ps_n(sv),
        !(st0.have && st0.cur_key as int == ps_pkeys(sv)[c] as int),
        st1.wf(), st1.cap == st0.cap, st1.lb == st0.lb,
        st0.have ==> st1.all@ == st0.all@.push((st0.cur_sum as int, st0.cur_key as int)) && st1.first_key == st0.first_key,
        !st0.have ==> st1.all@ == st0.all@ && st1.first_key == ps_pkeys(sv)[c],
        st1.have, st1.cur_key as int == ps_pkeys(sv)[c] as int, st1.cur_sum as int == val(sv, c),
        st1.sorted == (st0.sorted && !(st0.have && (ps_pkeys(sv)[c] as int) < st0.cur_key as int)),
        st1.total as int == st0.total as int + val(sv, c),
        st1.mass as int == st0.mass as int + abs(val(sv, c)),
    ensures st1.inv(sv, p, lo, c + 1),
{
    let e = (st0.cur_sum as int, st0.cur_key as int);
    lemma_rsum_step(sv, p, t_val(sv), lo, c);
    lemma_rsum_step(sv, p, t_absv(sv), lo, c);
    lemma_rsum_nonneg(sv, p, t_absv(sv), lo, c);
    assert forall|kk: int| #[trigger] rs_sum(st1.all@, kk) + st1.open_sum(kk) == rsum(sv, p, t_sum(sv, kk), lo, c + 1) by {
        lemma_rsum_step(sv, p, t_sum(sv, kk), lo, c);
        assert(rs_sum(st0.all@, kk) + st0.open_sum(kk) == rsum(sv, p, t_sum(sv, kk), lo, c));
        if st0.have {
            lemma_rs_push(st0.all@, e, kk);
        }
    }
    assert forall|kk: int| #[trigger] st1.key_in(kk) == (rsum(sv, p, t_cnt(sv, kk), lo, c + 1) > 0) by {
        lemma_rsum_step(sv, p, t_cnt(sv, kk), lo, c);
        lemma_rsum_bounds(sv, p, kk, lo, c);
        assert(st0.key_in(kk) == (rsum(sv, p, t_cnt(sv, kk), lo, c) > 0));
        if st0.have {
            lemma_rs_push(st0.all@, e, kk);
        }
    }
    if st1.sorted && st0.have {
        let rs = st1.all@;
        assert forall|i: int, j: int| 0 <= i < j < rs.len() implies (#[trigger] rs[i]).1 < (#[trigger] rs[j]).1 by {
            if j < st0.all@.len() {
                assert(rs[i] == st0.all@[i] && rs[j] == st0.all@[j]);
            } else {
                assert(rs[i] == st0.all@[i]);
            }
        }
        assert forall|i: int| 0 <= i < st1.all@.len() implies (#[trigger] st1.all@[i]).1 < st1.cur_key by {
            if i < st0.all@.len() {
                assert(st1.all@[i] == st0.all@[i]);
            }
        }
    }
    if st0.have && st0.all@.len() > 0 {
        assert(st1.all@[0] == st0.all@[0]);
    }
}

/// Close the open run: it joins the closed runs and is stored when its sum exceeds `lb` (`false`: no free slot).
#[inline(always)]
fn close_run(st: &mut RunState) -> (ok: bool)
    requires old(st).wf(), old(st).have,
    ensures
        ok ==> final(st).wf(),
        ok ==> final(st).all@ == old(st).all@.push((old(st).cur_sum as int, old(st).cur_key as int)),
        final(st).cap == old(st).cap, final(st).lb == old(st).lb, final(st).have == old(st).have,
        final(st).cur_key == old(st).cur_key, final(st).cur_sum == old(st).cur_sum,
        final(st).first_key == old(st).first_key, final(st).sorted == old(st).sorted,
        final(st).total == old(st).total, final(st).mass == old(st).mass,
    no_unwind
{
    let ghost st0 = *st;
    let ghost e = (st.cur_sum as int, st.cur_key as int);
    proof {
        lemma_above_push(st0.all@, e, st0.lb as int);
    }
    if st.cur_sum > st.lb {
        if st.used >= st.cap {
            return false;
        }
        let u = st.used;
        let ghost kv0 = st.keys@;
        let ghost sv0 = st.sums@;
        st.keys[u] = st.cur_key;
        st.sums[u] = st.cur_sum;
        st.used = u + 1;
        proof {
            lemma_pairs_frame(sv0, kv0, st.sums@, st.keys@, 0, u as int);
            lemma_pairs_push(st.sums@, st.keys@, 0, u as int);
        }
    }
    st.all = Ghost(st0.all@.push(e));
    true
}

/// Add qualifying row `c` (key `k`, value `v`) after rows `[pos, c)` without a qualifying row.
#[inline(always)]
fn push_row(st: &mut RunState, k: i64, v: i128, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>,
    Ghost(lo): Ghost<int>, Ghost(pos): Ghost<int>, Ghost(c): Ghost<int>) -> (r: u8)
    requires
        old(st).inv(sv, p, lo, pos),
        pos <= c < ps_n(sv), forall|x: int| pos <= x < c ==> !#[trigger] qrow(sv, p, x),
        qrow(sv, p, c), k == ps_pkeys(sv)[c], v == val(sv, c),
        -vbound() < v < vbound(),
    ensures
        r == GO ==> final(st).inv(sv, p, lo, c + 1) && final(st).cap == old(st).cap && final(st).lb == old(st).lb,
        r == OVER ==> rsum(sv, p, t_absv(sv), lo, c + 1) > imax(),
        r <= FULL,
    no_unwind
{
    let ghost st0 = *st;
    proof {
        lemma_inv_skip(st0, sv, p, lo, pos, c);
        lemma_rsum_nonneg(sv, p, t_absv(sv), lo, c);
        lemma_rsum_bounds(sv, p, 0, lo, c);
    }
    let av: i128 = if v < 0 { -v } else { v };
    if av > i128::MAX - st.mass {
        proof {
            lemma_rsum_step(sv, p, t_absv(sv), lo, c);
        }
        return OVER;
    }
    let mass2 = st.mass + av;
    let total2 = st.total + v;
    if st.have && st.cur_key == k {
        st.cur_sum = st.cur_sum + v;
        st.mass = mass2;
        st.total = total2;
        proof {
            lemma_push_same(st0, *st, sv, p, lo, c);
        }
    } else {
        if st.have {
            if k < st.cur_key {
                st.sorted = false;
            }
            if !close_run(st) {
                return FULL;
            }
        } else {
            st.first_key = k;
        }
        st.have = true;
        st.cur_key = k;
        st.cur_sum = v;
        st.mass = mass2;
        st.total = total2;
        proof {
            lemma_push_new(st0, *st, sv, p, lo, c);
        }
    }
    GO
}

/// Close the open run at the end of the range.
fn flush(st: &mut RunState, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>) -> (ok: bool)
    requires old(st).inv(sv, p, lo, hi),
    ensures ok ==> final(st).done(sv, p, lo, hi) && final(st).cap == old(st).cap && final(st).lb == old(st).lb,
    no_unwind
{
    let ghost st0 = *st;
    if st.have {
        if !close_run(st) {
            return false;
        }
        proof {
            let st1 = *st;
            let e = (st0.cur_sum as int, st0.cur_key as int);
            assert forall|k: int| #[trigger] rs_sum(st1.all@, k) == rsum(sv, p, t_sum(sv, k), lo, hi) by {
                lemma_rs_push(st0.all@, e, k);
            }
            assert forall|k: int| #[trigger] rs_has(st1.all@, k) <==> rsum(sv, p, t_cnt(sv, k), lo, hi) > 0 by {
                lemma_rs_push(st0.all@, e, k);
                assert(st0.key_in(k) == (rsum(sv, p, t_cnt(sv, k), lo, hi) > 0));
            }
            if st1.sorted {
                let rs = st1.all@;
                assert forall|i: int, j: int| 0 <= i < j < rs.len() implies (#[trigger] rs[i]).1 < (#[trigger] rs[j]).1 by {
                    if j < st0.all@.len() {
                        assert(rs[i] == st0.all@[i] && rs[j] == st0.all@[j]);
                    } else {
                        assert(rs[i] == st0.all@[i]);
                    }
                }
            }
            if st0.all@.len() > 0 {
                assert(st1.all@[0] == st0.all@[0]);
            }
        }
    } else {
        proof {
            assert(st0.all@ =~= Seq::<(int, int)>::empty());
            assert forall|k: int| #[trigger] rs_sum(st0.all@, k) == rsum(sv, p, t_sum(sv, k), lo, hi) by {
                assert(st0.open_sum(k) == 0);
            }
            assert forall|k: int| #[trigger] rs_has(st0.all@, k) <==> rsum(sv, p, t_cnt(sv, k), lo, hi) > 0 by {
                assert(st0.key_in(k) == (rsum(sv, p, t_cnt(sv, k), lo, hi) > 0));
            }
        }
    }
    true
}

// ------------------------------------------------------------------------------------------ one block

/// `sel[0..m)` lists, as offsets from `b0` and increasing, exactly the qualifying rows of `[b0, b1)`.
pub open spec fn sel_ok(sel: Seq<u32>, m: int, b0: int, b1: int, sv: StoresView, p: Seq<u8>) -> bool {
    &&& 0 <= m <= sel.len()
    &&& forall|j: int| 0 <= j < m ==> b0 <= b0 + #[trigger] sel[j] < b1 && qrow(sv, p, b0 + sel[j])
    &&& forall|i: int, j: int| 0 <= i < j < m ==> #[trigger] sel[i] < #[trigger] sel[j]
    &&& forall|c: int| b0 <= c < b1 && #[trigger] qrow(sv, p, c) ==> exists|j: int| 0 <= j < m && b0 + sel[j] == c
}

/// The qualifying rows of `[b0, b1)`, branch-free: every row's offset is written, the count advances by its flag.
/// The supplier of key `s` is row `s - base` when that wrapping offset lies in `[0, nbits)` (`lemma_offset`; one
/// unsigned compare). Its own function so that the loop's values stay in registers.
#[inline(never)]
fn select_block(sk: &[i64], bw: &Vec<u64>, nbits: usize, base: i64, b0: usize, b1: usize,
    sel: &mut Vec<u32>, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>) -> (m: usize)
    requires
        stores_wf(sv), sk@ == ps_skeys(sv),
        b0 <= b1 <= ps_n(sv), b1 - b0 <= BLK, old(sel)@.len() == BLK,
        bits_ok(bw@, nbits as int, sv, p), dense_ok(sv, base as int, base + nbits - 1),
        0 <= base <= off_bound(), nbits <= off_bound(),
    ensures final(sel)@.len() == BLK, m <= b1 - b0, sel_ok(final(sel)@, m as int, b0 as int, b1 as int, sv, p),
    no_unwind
{
    let nb = nbits as i64;
    let mut m: usize = 0;
    let mut c = b0;
    while c < b1
        invariant
            stores_wf(sv), sk@ == ps_skeys(sv),
            b0 <= c <= b1 <= ps_n(sv), b1 - b0 <= BLK, sel@.len() == BLK,
            bits_ok(bw@, nbits as int, sv, p), dense_ok(sv, base as int, base + nbits - 1),
            0 <= base <= off_bound(), nbits <= off_bound(), nb == nbits,
            m <= c - b0,
            sel_ok(sel@, m as int, b0 as int, c as int, sv, p),
        decreases b1 - c,
    {
        let s = sk[c];
        let d = s.wrapping_sub(base);
        let inr = 0 <= d && d < nb;
        let o2: usize = if inr { d as usize } else { 0 };
        proof {
            lemma_offset(s, base, nb);
            assert(nbits >= 1);
            assert(o2 < nbits);
            assert(o2 / 64 < bw@.len()) by (nonlinear_arith) requires o2 < nbits, 64 * bw@.len() >= nbits;
            lemma_qrow_dense(bw@, sv, p, base as int, base + nbits - 1, c as int);
        }
        let w = bw[o2 / 64];
        let sh: u64 = (o2 % 64) as u64;
        let bitv: u64 = (w >> sh) & 1u64;
        let flag: u64 = if inr { 1u64 } else { 0u64 };
        let keep: usize = (bitv & flag) as usize;
        let ghost sel0 = sel@;
        sel[m] = (c - b0) as u32;
        proof {
            assert(bitv <= 1u64) by (bit_vector) requires bitv == (w >> sh) & 1u64;
            assert(bitv & flag == if flag == 1u64 { bitv } else { 0u64 }) by (bit_vector)
                requires bitv <= 1u64, flag == 0u64 || flag == 1u64;
            assert(inr <==> (base <= s && s <= base + nbits - 1));
            assert(keep == 1 <==> qrow(sv, p, c as int)) by {
                if inr {
                    assert(o2 as int == s - base);
                    assert(bit_at(bw@, o2 as int) == (bitv == 1u64));
                }
            }
            assert(keep <= 1);
            let m2 = m + keep;
            assert forall|j: int| 0 <= j < m2 implies b0 <= b0 + #[trigger] sel@[j] < c + 1 && qrow(sv, p, b0 + sel@[j]) by {
                if j < m { assert(sel@[j] == sel0[j]); }
            }
            assert forall|i: int, j: int| 0 <= i < j < m2 implies #[trigger] sel@[i] < #[trigger] sel@[j] by {
                if j < m { assert(sel@[i] == sel0[i] && sel@[j] == sel0[j]); } else { assert(sel@[i] == sel0[i]); }
            }
            assert forall|x: int| b0 <= x < c + 1 && #[trigger] qrow(sv, p, x) implies exists|j: int| 0 <= j < m2 && b0 + sel@[j] == x by {
                if x < c {
                    let j = choose|j: int| 0 <= j < m && b0 + sel0[j] == x;
                    assert(sel@[j] == sel0[j]);
                } else {
                    assert(b0 + sel@[m as int] == x);
                }
            }
        }
        m = m + keep;
        c = c + 1;
    }
    m
}

/// `gk[j]`, `gv[j]` are the part key and value of selected row `j`.
pub open spec fn gathered(gk: Seq<i64>, gv: Seq<i128>, sel: Seq<u32>, m: int, b0: int, sv: StoresView) -> bool {
    forall|j: int| 0 <= j < m ==> #[trigger] gk[j] == ps_pkeys(sv)[b0 + sel[j]] && gv[j] == val(sv, b0 + sel[j])
}

/// Selected row `j`'s gathered key and value.
proof fn lemma_gathered_at(gk: Seq<i64>, gv: Seq<i128>, sel: Seq<u32>, m: int, b0: int, sv: StoresView, j: int)
    requires gathered(gk, gv, sel, m, b0, sv), 0 <= j < m,
    ensures gk[j] == ps_pkeys(sv)[b0 + sel[j]], gv[j] == val(sv, b0 + sel[j]),
{
    let c = b0 + sel[j];
    assert(gk[j] == ps_pkeys(sv)[c] && gv[j] == val(sv, c));
}

/// The part key and value of the selected rows.
fn gather_block(pk: &'static [i64], aq: &'static [i64], cost: &'static [i128], sel: &Vec<u32>, m: usize, b0: usize,
    b1: usize, gk: &mut Vec<i64>, gv: &mut Vec<i128>, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>)
    requires
        stores_wf(sv), bounds_ok(sv),
        pk@ == ps_pkeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv),
        b0 <= b1 <= ps_n(sv), m <= BLK, sel@.len() == BLK,
        sel_ok(sel@, m as int, b0 as int, b1 as int, sv, p),
        old(gk)@.len() == BLK, old(gv)@.len() == BLK,
    ensures
        final(gk)@.len() == BLK, final(gv)@.len() == BLK,
        gathered(final(gk)@, final(gv)@, sel@, m as int, b0 as int, sv),
    no_unwind
{
    let mut j: usize = 0;
    while j < m
        invariant
            stores_wf(sv), bounds_ok(sv),
            pk@ == ps_pkeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv),
            b0 <= b1 <= ps_n(sv), m <= BLK, sel@.len() == BLK, j <= m,
            sel_ok(sel@, m as int, b0 as int, b1 as int, sv, p),
            gk@.len() == BLK, gv@.len() == BLK,
            forall|i: int| 0 <= i < j ==> #[trigger] gk@[i] == ps_pkeys(sv)[b0 + sel@[i]] && gv@[i] == val(sv, b0 + sel@[i]),
        decreases m - j,
    {
        let c = b0 + sel[j] as usize;
        proof {
            assert(b0 <= b0 + sel@[j as int] < b1);
            assert(-cost_bound() < ps_costs(sv)[c as int] < cost_bound());
            lemma_product_bound(ps_costs(sv)[c as int] as int, ps_aqs(sv)[c as int] as int);
        }
        gk[j] = pk[c];
        gv[j] = cost[c] * (aq[c] as i128);
        j = j + 1;
    }
}

// ------------------------------------------------------------------------------------------ the task

/// The scan of rows `[lo, hi)`.
pub struct ScanTask {
    pub pk: &'static [i64],
    pub sk: &'static [i64],
    pub aq: &'static [i64],
    pub cost: &'static [i128],
    pub lo: usize,
    pub hi: usize,
    pub bits: Arc<Vec<u64>>,
    pub nbits: usize,
    pub base: i64,
    pub st: RunState,
    pub bv: Vec<i128>,
    pub bk: Vec<i64>,
    pub sel: Vec<u32>,
    pub gk: Vec<i64>,
    pub gv: Vec<i128>,
    pub sv: Ghost<StoresView>,
    pub p: Ghost<Seq<u8>>,
}

/// The finished scan: the stored runs sorted by sum, descending, and what the combination needs.
pub struct ScanOut {
    pub list: Sorted,
    pub status: u8,
    pub sorted: bool,
    /// The range has a run; then `first_key` and `last_key` are the keys of its first and last run.
    pub any: bool,
    pub first_key: i64,
    pub last_key: i64,
    pub total: i128,
    pub mass: i128,
    /// Every run of the range, in row order.
    pub all: Ghost<Seq<(int, int)>>,
}

/// What a done scan of `[lo, hi)` with lower bound `lb` establishes.
pub open spec fn out_done(sv: StoresView, p: Seq<u8>, lo: int, hi: int, lb: int, out: ScanOut) -> bool {
    let all = out.all@;
    &&& runs_ok(sv, p, lo, hi, all)
    &&& out.sorted ==> strict(all)
    &&& out.list.wf() && desc(out.list.view())
    &&& out.list.view().to_multiset() == above(all, lb).to_multiset()
    &&& out.total == rsum(sv, p, t_val(sv), lo, hi)
    &&& out.mass == rsum(sv, p, t_absv(sv), lo, hi)
    &&& out.any == (all.len() > 0)
    &&& out.any ==> out.first_key as int == all[0].1 && out.last_key as int == all.last().1
}

/// What the scan of `[lo, hi)` establishes.
#[verifier::opaque]
pub open spec fn scan_post(sv: StoresView, p: Seq<u8>, lo: int, hi: int, lb: int, out: ScanOut) -> bool {
    &&& out.status <= FULL
    &&& out.status == GO ==> out_done(sv, p, lo, hi, lb, out)
    &&& out.status == OVER ==> rsum(sv, p, t_absv(sv), lo, hi) > imax()
}

impl ScanTask {
    pub open spec fn ready(&self) -> bool {
        let sv = self.sv@;
        let p = self.p@;
        &&& stores_wf(sv) && bounds_ok(sv)
        &&& self.pk@ == ps_pkeys(sv) && self.sk@ == ps_skeys(sv) && self.aq@ == ps_aqs(sv) && self.cost@ == ps_costs(sv)
        &&& self.lo <= self.hi <= ps_n(sv)
        &&& bits_ok((*self.bits)@, self.nbits as int, sv, p)
        &&& dense_ok(sv, self.base as int, self.base + self.nbits - 1)
        &&& 0 <= self.base <= off_bound() && self.nbits <= off_bound()
        &&& self.st.wf() && !self.st.have && self.st.sorted && self.st.total == 0 && self.st.mass == 0
        &&& self.st.all@ == Seq::<(int, int)>::empty()
        &&& self.bv@.len() == self.st.cap && self.bk@.len() == self.st.cap
        &&& self.sel@.len() == BLK && self.gk@.len() == BLK && self.gv@.len() == BLK
    }
}

/// The output of a stopped scan (no list).
fn stopped(st: RunState, status: u8) -> (out: ScanOut)
    ensures out.status == status,
    no_unwind
{
    let RunState { keys, sums, cap: _, used: _, lb: _, have: _, cur_key: _, cur_sum: _, first_key: _, sorted, total, mass, all } = st;
    ScanOut { list: Sorted { v: sums, k: keys, n: 0 }, status, sorted, any: false, first_key: 0, last_key: 0, total, mass, all }
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        self.ready()
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        scan_post(self.sv@, self.p@, self.lo as int, self.hi as int, self.st.lb as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let ghost task = self;
        let ScanTask { pk, sk, aq, cost, lo, hi, bits, nbits, base, st, bv, bk, sel, gk, gv, sv, p } = self;
        let ghost sv = sv@;
        let ghost p = p@;
        let ghost lb = st.lb as int;
        let mut st = st;
        let mut bv = bv;
        let mut bk = bk;
        let mut sel = sel;
        let mut gk = gk;
        let mut gv = gv;
        let bw: &Vec<u64> = &*bits;
        proof {
            lemma_new_inv(st, sv, p, lo as int);
        }
        let mut b0 = lo;
        while b0 < hi
            invariant
                stores_wf(sv), bounds_ok(sv),
                pk@ == ps_pkeys(sv), sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv),
                lo <= b0 <= hi <= ps_n(sv),
                bits_ok(bw@, nbits as int, sv, p), dense_ok(sv, base as int, base + nbits - 1),
                0 <= base <= off_bound(), nbits <= off_bound(),
                sel@.len() == BLK, gk@.len() == BLK, gv@.len() == BLK,
                st.inv(sv, p, lo as int, b0 as int), st.lb == lb,
                bv@.len() == st.cap && bk@.len() == st.cap,
                task.sv@ == sv && task.p@ == p && task.lo == lo && task.hi == hi && task.st.lb == lb && task == self,
            decreases hi - b0,
        {
            let b1 = if hi - b0 > BLK { b0 + BLK } else { hi };
            let m = select_block(sk, bw, nbits, base, b0, b1, &mut sel, Ghost(sv), Ghost(p));
            gather_block(pk, aq, cost, &sel, m, b0, b1, &mut gk, &mut gv, Ghost(sv), Ghost(p));
            let mut j: usize = 0;
            let ghost mut pos: int = b0 as int;
            while j < m
                invariant
                    stores_wf(sv), bounds_ok(sv),
                    lo <= b0 <= b1 <= hi <= ps_n(sv), m <= BLK, j <= m,
                    sel@.len() == BLK, gk@.len() == BLK, gv@.len() == BLK,
                    sel_ok(sel@, m as int, b0 as int, b1 as int, sv, p),
                    gathered(gk@, gv@, sel@, m as int, b0 as int, sv),
                    pos == if j == 0 { b0 as int } else { b0 + sel@[j - 1] + 1 },
                    b0 <= pos <= b1,
                    st.inv(sv, p, lo as int, pos), st.lb == lb,
                    bv@.len() == st.cap && bk@.len() == st.cap,
                    task.sv@ == sv && task.p@ == p && task.lo == lo && task.hi == hi && task.st.lb == lb && task == self,
                decreases m - j,
            {
                let ghost c = b0 + sel@[j as int];
                proof {
                    assert forall|x: int| pos <= x < c implies !#[trigger] qrow(sv, p, x) by {
                        if qrow(sv, p, x) {
                            let i = choose|i: int| 0 <= i < m && b0 + sel@[i] == x;
                            if i < j {
                                if i < j - 1 { assert(sel@[i] < sel@[j - 1]); }
                            } else if i > j {
                                assert(sel@[j as int] < sel@[i]);
                            }
                        }
                    }
                    if j > 0 { assert(sel@[j - 1] < sel@[j as int]); }
                    lemma_val_bound_pub(sv, c);
                    lemma_gathered_at(gk@, gv@, sel@, m as int, b0 as int, sv, j as int);
                }
                let r = push_row(&mut st, gk[j], gv[j], Ghost(sv), Ghost(p), Ghost(lo as int), Ghost(pos), Ghost(c));
                if r != GO {
                    proof {
                        if r == OVER {
                            assert forall|x: int| c + 1 <= x < hi implies #[trigger] (t_absv(sv))(x) >= 0 by {}
                            lemma_rsum_mono(sv, p, t_absv(sv), lo as int, c + 1, hi as int);
                        }
                    }
                    let out = stopped(st, r);
                    proof {
                        reveal(scan_post);
                    }
                    return out;
                }
                proof { pos = c + 1; }
                j = j + 1;
            }
            proof {
                assert forall|x: int| pos <= x < b1 implies !#[trigger] qrow(sv, p, x) by {
                    if qrow(sv, p, x) {
                        let i = choose|i: int| 0 <= i < m && b0 + sel@[i] == x;
                        if i < m - 1 { assert(sel@[i] < sel@[m - 1]); }
                    }
                }
                lemma_inv_skip(st, sv, p, lo as int, pos, b1 as int);
            }
            b0 = b1;
        }
        let ok = flush(&mut st, Ghost(sv), Ghost(p), Ghost(lo as int), Ghost(hi as int));
        if !ok {
            let out = stopped(st, FULL);
            proof {
                reveal(scan_post);
            }
            return out;
        }
        // sort the stored runs by sum, descending
        let ghost before = st.rs();
        let RunState { keys, sums, cap: _, used, lb: _, have, cur_key, cur_sum: _, first_key, sorted, total, mass, all } = st;
        let mut keys = keys;
        let mut sums = sums;
        sort_range(&mut sums, &mut keys, &mut bv, &mut bk, 0, used);
        let out = ScanOut { list: Sorted { v: sums, k: keys, n: used }, status: GO, sorted, any: have, first_key,
            last_key: cur_key, total, mass, all };
        proof {
            assert(out.list.view() == pairs(sums@, keys@, 0, used as int));
            assert(before == above(all@, lb));
            reveal(scan_post);
        }
        out
    }
}

/// The facts of `scan_post`.
pub proof fn lemma_scan_post(sv: StoresView, p: Seq<u8>, lo: int, hi: int, lb: int, out: ScanOut)
    requires scan_post(sv, p, lo, hi, lb, out),
    ensures
        out.status <= FULL,
        out.status == GO ==> out_done(sv, p, lo, hi, lb, out),
        out.status == OVER ==> rsum(sv, p, t_absv(sv), lo, hi) > imax(),
{
    reveal(scan_post);
}

/// `|val| < 2^113` (re-exported for the scan's row step).
pub proof fn lemma_val_bound_pub(sv: StoresView, c: int)
    requires stores_wf(sv), bounds_ok(sv), 0 <= c < ps_n(sv),
    ensures -vbound() < val(sv, c) < vbound(),
{
    crate::agent::sem::lemma_val_bound(sv, c);
}

} // verus!
