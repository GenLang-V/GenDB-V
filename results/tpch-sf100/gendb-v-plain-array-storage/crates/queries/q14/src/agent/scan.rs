//! The lineitem scan of one row range (`scan_range`, run by `ScanTask`), in blocks of `BLOCK` rows:
//! 1. `select`: per 64-row word a branch-free window mask of the ship dates (`mask64`, vectorized over the 64
//!    stored days), then its set bits in order (`common::tz`); the rows of the block inside the window are listed in
//!    `sel` (offsets from the block start), which is `range_filter(b, e, pwin)` (`common::selection`);
//! 2. `gather`: for every listed row, its part row (`find_part`: `l_partkey - 1` when every part row is positional,
//!    checked by the part pass, else a linear search of the part keys), its volume, and its part's promotion bit;
//!    the row's contribution `tot1` is added to the accumulator (`acc_add`).
//! Rows outside the window contribute nothing, so the listed rows' contributions are the block's totals
//! (`lemma_tlist_window`).
//!
//! The accumulator (`Acc`) holds the exact counts and, while the absolute volume mass stays below `2^127`
//! (`MASS_CAP`), the exact sums; beyond it the mass sticks at `MASS_CAP` (the SUM leaves `i128`: the statement is
//! outside its capacity domain). `acc_ok(a, t)` relates it to the totals `t` it stands for.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::bounds::*;
use crate::agent::parts::{pbits_ok, pos_all};
use crate::agent::common::bits::*;
use crate::agent::common::tz::{tz64, tz_table_array};
use crate::agent::common::selection::*;

verus! {

/// Rows per block of `scan_range` (offsets in a block fit `u32`); also the length of a task's `sel` buffer.
pub const BLOCK: usize = 2048;

/// `2^127 = i128::MAX + 1`: the saturation value of the absolute mass.
pub const MASS_CAP: u128 = 0x8000_0000_0000_0000_0000_0000_0000_0000;

// ------------------------------------------------------------------------------------------------ columns

/// The columns the scan reads.
#[derive(Clone, Copy)]
pub struct ScanCols {
    pub ship: &'static [i32],
    pub pkey: &'static [i64],
    pub price: &'static [i128],
    pub disc: &'static [i128],
    pub nl: usize,
    pub part_key: &'static [i64],
    pub np: usize,
}

/// The slices are the stored columns; the model's facts the scan relies on hold.
pub open spec fn scan_cols_ok(c: ScanCols, sv: StoresView) -> bool {
    &&& c.ship@ == l_ship(sv) && c.pkey@ == l_pkey(sv) && c.price@ == l_price(sv) && c.disc@ == l_disc(sv)
    &&& c.nl == n_l(sv)
    &&& l_ship(sv).len() == n_l(sv) && l_pkey(sv).len() == n_l(sv) && l_price(sv).len() == n_l(sv)
    &&& l_disc(sv).len() == n_l(sv)
    &&& c.part_key@ == p_key(sv) && c.np == n_p(sv)
    &&& domains_ok(sv)
    &&& keys_unique(p_key(sv))
}

/// The window test of row `l`.
pub open spec fn pwin(sv: StoresView, w: Win) -> spec_fn(int) -> bool { |l: int| in_win(sv, w, l) }

// ------------------------------------------------------------------------------------------------ totals of row lists

/// The contribution of row `l` to the totals.
pub open spec fn tot1(sv: StoresView, w: Win, l: int) -> Tot {
    Tot {
        cnt: (f_cnt(sv, w))(l),
        s_all: (f_all(sv, w))(l),
        a_all: (f_abs(sv, w))(l),
        n_pr: (f_npr(sv, w))(l),
        s_pr: (f_pr(sv, w))(l),
        a_pr: (f_apr(sv, w))(l),
    }
}

pub open spec fn tot_zero() -> Tot { Tot { cnt: 0, s_all: 0, a_all: 0, n_pr: 0, s_pr: 0, a_pr: 0 } }

/// The totals of the rows listed in `s`.
pub open spec fn tlist(sv: StoresView, w: Win, s: Seq<int>) -> Tot
    decreases s.len(),
{
    if s.len() == 0 { tot_zero() } else { tot_plus(tlist(sv, w, s.drop_last()), tot1(sv, w, s.last())) }
}

/// One more listed row.
pub proof fn lemma_tlist_push(sv: StoresView, w: Win, s: Seq<int>, x: int)
    ensures tlist(sv, w, s.push(x)) == tot_plus(tlist(sv, w, s), tot1(sv, w, x)),
{
    assert(s.push(x).drop_last() =~= s);
}

/// One more row of a range.
proof fn lemma_tot_step(sv: StoresView, w: Win, lo: int, hi: int)
    requires lo <= hi,
    ensures tot(sv, w, lo, hi + 1) == tot_plus(tot(sv, w, lo, hi), tot1(sv, w, hi)),
{
}

/// The totals of the window rows of a range listed in order are the range's totals.
pub proof fn lemma_tlist_window(sv: StoresView, w: Win, b: int, e: int)
    requires b <= e,
    ensures tlist(sv, w, range_filter(b, e, pwin(sv, w))) == tot(sv, w, b, e),
    decreases e - b,
{
    let p = pwin(sv, w);
    if e > b {
        lemma_tlist_window(sv, w, b, e - 1);
        lemma_tot_step(sv, w, b, e - 1);
        let s = range_filter(b, e - 1, p);
        if p(e - 1) {
            lemma_tlist_push(sv, w, s, e - 1);
        } else {
            assert(tot1(sv, w, e - 1) == tot_zero());
        }
    } else {
        assert(range_filter(b, e, p) =~= Seq::<int>::empty());
    }
}

/// Totals with the bounds of real ones: non-negative counts and masses bounding the sums.
pub open spec fn tot_sane(t: Tot) -> bool {
    &&& 0 <= t.n_pr <= t.cnt
    &&& 0 <= t.a_pr <= t.a_all
    &&& -t.a_all <= t.s_all <= t.a_all
    &&& -t.a_pr <= t.s_pr <= t.a_pr
}

// ------------------------------------------------------------------------------------------------ the accumulator

/// Running totals (see the module header).
#[derive(Clone, Copy)]
pub struct Acc {
    pub cnt: u64,
    pub n_pr: u64,
    pub s_all: i128,
    pub s_pr: i128,
    pub mass: u128,
}

/// `a` stands for the totals `t`.
pub open spec fn acc_ok(a: Acc, t: Tot) -> bool {
    &&& tot_sane(t)
    &&& a.cnt as int == t.cnt
    &&& a.n_pr as int == t.n_pr
    &&& a.mass as int == if t.a_all < MASS_CAP as int { t.a_all } else { MASS_CAP as int }
    &&& t.a_all < MASS_CAP as int ==> a.s_all as int == t.s_all && a.s_pr as int == t.s_pr
}

/// The accumulator of no rows.
pub fn acc_new() -> (a: Acc)
    ensures acc_ok(a, tot_zero()),
    no_unwind
{
    Acc { cnt: 0, n_pr: 0, s_all: 0, s_pr: 0, mass: 0 }
}

/// Adds one qualifying row of volume `v`, promotional or not.
fn acc_add(acc: &mut Acc, v: i128, promo: bool, Ghost(t): Ghost<Tot>)
    requires
        acc_ok(*old(acc), t),
        v > i128::MIN,
        t.cnt < 0xffff_ffff_ffff_ffff,
    ensures
        acc_ok(*final(acc), tot_plus(t, Tot {
            cnt: 1, s_all: v as int, a_all: abs(v as int),
            n_pr: if promo { 1 } else { 0 }, s_pr: if promo { v as int } else { 0 }, a_pr: if promo { abs(v as int) } else { 0 },
        })),
    no_unwind
{
    let a: u128 = if v < 0 { (-v) as u128 } else { v as u128 };
    if acc.mass >= MASS_CAP - a {
        acc.mass = MASS_CAP;
    } else {
        // Unsaturated: `|s + v| <= mass + |v| < 2^127`.
        acc.mass = acc.mass + a;
        acc.s_all = acc.s_all + v;
        if promo {
            acc.s_pr = acc.s_pr + v;
        }
    }
    acc.cnt = acc.cnt + 1;
    if promo {
        acc.n_pr = acc.n_pr + 1;
    }
}

/// Merges the accumulators of two disjoint row sets.
pub fn acc_merge(x: Acc, y: Acc, Ghost(t1): Ghost<Tot>, Ghost(t2): Ghost<Tot>) -> (r: Acc)
    requires acc_ok(x, t1), acc_ok(y, t2), t1.cnt + t2.cnt <= 0xffff_ffff_ffff_ffff,
    ensures acc_ok(r, tot_plus(t1, t2)),
    no_unwind
{
    let cnt = x.cnt + y.cnt;
    let n_pr = x.n_pr + y.n_pr;
    if x.mass >= MASS_CAP - y.mass {
        Acc { cnt, n_pr, s_all: 0, s_pr: 0, mass: MASS_CAP }
    } else {
        Acc { cnt, n_pr, s_all: x.s_all + y.s_all, s_pr: x.s_pr + y.s_pr, mass: x.mass + y.mass }
    }
}

// ------------------------------------------------------------------------------------------------ one row

/// The part row holding key `pk`: `pk - 1` when every part row is positional, else a linear search.
fn find_part(c: &ScanCols, pos: bool, pk: i64, Ghost(sv): Ghost<StoresView>) -> (r: Option<usize>)
    requires scan_cols_ok(*c, sv), pos ==> pos_all(sv),
    ensures
        r matches Some(a) ==> a < n_p(sv) && p_key(sv)[a as int] == pk,
        r is None ==> forall|a: int| 0 <= a < n_p(sv) ==> #[trigger] p_key(sv)[a] != pk,
    no_unwind
{
    if pos {
        let d = pk as i128 - 1;
        if 0 <= d && d < c.np as i128 {
            proof { assert(p_key(sv)[d as int] as int == d + 1); }
            Some(d as usize)
        } else {
            proof {
                assert forall|a: int| 0 <= a < n_p(sv) implies #[trigger] p_key(sv)[a] != pk by {
                    assert(p_key(sv)[a] as int == a + 1);
                }
            }
            None
        }
    } else {
        let mut a: usize = 0;
        while a < c.np
            invariant
                scan_cols_ok(*c, sv), a <= c.np,
                forall|q: int| 0 <= q < a ==> #[trigger] p_key(sv)[q] != pk,
            decreases c.np - a,
        {
            if c.part_key[a] == pk {
                return Some(a);
            }
            a = a + 1;
        }
        None
    }
}

/// Adds row `r` (inside the window) to the accumulator.
#[inline(always)]
fn add_row(c: &ScanCols, bits: &Vec<u64>, pos: bool, r: usize, acc: &mut Acc,
    Ghost(sv): Ghost<StoresView>, Ghost(w): Ghost<Win>, Ghost(t): Ghost<Tot>)
    requires
        scan_cols_ok(*c, sv), pbits_ok(bits@, sv), pos ==> pos_all(sv),
        r < c.nl, in_win(sv, w, r as int),
        acc_ok(*old(acc), t),
        t.cnt < 0xffff_ffff_ffff_ffff,
    ensures acc_ok(*final(acc), tot_plus(t, tot1(sv, w, r as int))),
    no_unwind
{
    let ghost l = r as int;
    let pk = c.pkey[r];
    match find_part(c, pos, pk, Ghost(sv)) {
        None => {
            proof {
                lemma_no_part(sv, l);
                assert(tot1(sv, w, l) == tot_zero());
                assert(tot_plus(t, tot_zero()) == t);
            }
        },
        Some(a) => {
            proof {
                lemma_part_is(sv, l, a as int);
                assert(num15(l_price(sv)[l]) && num15(l_disc(sv)[l]));
            }
            let pr = c.price[r];
            let dc = c.disc[r];
            proof {
                // both factors are numeric(15,2) coefficients: the product is below 10^31 in absolute value
                assert(-10_000_000_000_000_000_000_000_000_000_000 < (pr as int) * (100 - dc as int)
                    < 10_000_000_000_000_000_000_000_000_000_000) by (nonlinear_arith)
                    requires -1_000_000_000_000_000 < (pr as int) < 1_000_000_000_000_000,
                        -1_000_000_000_000_000 < (dc as int) < 1_000_000_000_000_000;
            }
            let v = pr * (100 - dc);
            let word = bits[a / 64];
            let is_promo = (word >> ((a % 64) as u64)) & 1u64 == 1u64;
            proof {
                assert(word_bit(bits@, a as int) == is_promo);
                assert(is_promo == promo(sv, a as int));
                assert(v as int == vol(sv, l));
            }
            acc_add(acc, v, is_promo, Ghost(t));
        },
    }
}

// ------------------------------------------------------------------------------------------------ selection

/// The window test of 64 consecutive stored days as a mask: bit `u` is day `ch[u]` (branch-free; the compiler
/// vectorizes it since the slice length is known).
fn mask64(ch: &[i32], x: &Window) -> (m: u64)
    requires ch@.len() == 64, window_wf(*x),
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == in_window(*x, ch@[u as int]),
    no_unwind
{
    let mut m: u64 = 0;
    let mut u: usize = 0;
    proof {
        assert forall|v: u64| v < 64 implies !#[trigger] bit(0u64, v) by { lemma_bit_zero(v); }
    }
    while u < 64
        invariant
            ch@.len() == 64, u <= 64, window_wf(*x),
            forall|v: u64| v < 64 ==> #[trigger] bit(m, v) == (v < u && in_window(*x, ch@[v as int])),
        decreases 64 - u,
    {
        let keep = day_in(x, ch[u]);
        let b: u64 = if keep { 1 } else { 0 };
        let ghost m0 = m;
        m = m | (b << (u as u64));
        proof {
            assert forall|v: u64| v < 64 implies #[trigger] bit(m, v) == (v < u + 1 && in_window(*x, ch@[v as int])) by {
                lemma_bit_set(m0, b, u as u64, v);
            }
        }
        u = u + 1;
    }
    m
}

/// The window mask of the rows `w..we` (at most 64): bit `u` is row `w + u`.
fn word_mask(c: &ScanCols, x: &Window, w: usize, we: usize, Ghost(sv): Ghost<StoresView>) -> (m: u64)
    requires scan_cols_ok(*c, sv), window_wf(*x), w < we <= c.nl, we - w <= 64,
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (u < we - w && in_win(sv, win_of(*x), w + u)),
    no_unwind
{
    if we - w == 64 {
        let (_, tail) = c.ship.split_at(w);
        let (ch, _) = tail.split_at(64);
        let m = mask64(ch, x);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (u < we - w && in_win(sv, win_of(*x), w + u)) by {
                assert(ch@[u as int] == tail@[u as int]);
                assert(tail@[u as int] == l_ship(sv)[w + u]);
            }
        }
        m
    } else {
        let mut m: u64 = 0;
        let mut j = w;
        proof {
            assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
        }
        while j < we
            invariant
                scan_cols_ok(*c, sv), window_wf(*x), w <= j <= we <= c.nl, we - w <= 64,
                forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (u < j - w && in_win(sv, win_of(*x), w + u)),
            decreases we - j,
        {
            let keep = day_in(x, c.ship[j]);
            let b: u64 = if keep { 1 } else { 0 };
            let t = (j - w) as u64;
            let ghost m0 = m;
            m = m | (b << t);
            proof {
                assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (u < j + 1 - w && in_win(sv, win_of(*x), w + u)) by {
                    lemma_bit_set(m0, b, t, u);
                }
            }
            j = j + 1;
        }
        m
    }
}

/// A range filter does not grow over rows that fail the condition.
proof fn lemma_rf_skip(b: int, x: int, y: int, p: spec_fn(int) -> bool)
    requires b <= x <= y, forall|l: int| x <= l < y ==> !#[trigger] p(l),
    ensures range_filter(b, y, p) == range_filter(b, x, p),
    decreases y - x,
{
    if y > x {
        lemma_rf_skip(b, x, y - 1, p);
    }
}

/// A range filter lists at most the rows of its range.
proof fn lemma_rf_len(b: int, e: int, p: spec_fn(int) -> bool)
    requires b <= e,
    ensures range_filter(b, e, p).len() <= e - b,
    decreases e - b,
{
    if e > b {
        lemma_rf_len(b, e - 1, p);
    }
}

/// The rows of `[b, e)` inside the window, as offsets from `b` in `sel`.
fn select(c: &ScanCols, x: &Window, table: &[u8; 64], b: usize, e: usize, sel: &mut Vec<u32>, Ghost(sv): Ghost<StoresView>)
    -> (k: usize)
    requires
        scan_cols_ok(*c, sv), window_wf(*x), table@.len() == 64,
        b <= e <= c.nl, e - b <= BLOCK, old(sel)@.len() == BLOCK,
    ensures
        final(sel)@.len() == BLOCK,
        sel_matches(final(sel)@, k as int, b as int, range_filter(b as int, e as int, pwin(sv, win_of(*x)))),
    no_unwind
{
    let ghost p = pwin(sv, win_of(*x));
    let mut k: usize = 0;
    let mut w = b;
    while w < e
        invariant
            scan_cols_ok(*c, sv), window_wf(*x), table@.len() == 64,
            b <= w <= e <= c.nl, e - b <= BLOCK, sel@.len() == BLOCK,
            p == pwin(sv, win_of(*x)),
            sel_matches(sel@, k as int, b as int, range_filter(b as int, w as int, p)),
        decreases e - w,
    {
        let we = if e - w > 64 { w + 64 } else { e };
        let mut m = word_mask(c, x, w, we, Ghost(sv));
        let ghost mut q: int = 0;
        while m != 0
            invariant
                scan_cols_ok(*c, sv), window_wf(*x), table@.len() == 64,
                b <= w < we <= e <= c.nl, we - w <= 64, e - b <= BLOCK, sel@.len() == BLOCK,
                p == pwin(sv, win_of(*x)),
                0 <= q <= we - w,
                forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (q <= u < we - w && in_win(sv, win_of(*x), w + u)),
                sel_matches(sel@, k as int, b as int, range_filter(b as int, w + q, p)),
            decreases we - w - q,
        {
            proof { lemma_first_bit(m); }
            let t = tz64(m, table) as u64;
            proof {
                assert(bit(m, t));
                assert forall|l: int| w + q <= l < w + t implies !#[trigger] p(l) by {
                    let u = (l - w) as u64;
                    assert(!bit(m, u));
                }
                lemma_rf_skip(b as int, w + q, w + t, p);
                lemma_rf_len(b as int, w + t, p);
            }
            let ghost m1 = m;
            m = m & (m - 1);
            proof {
                assert(m1 - 1 == sub(m1, 1));
                assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (t + 1 <= u < we - w && in_win(sv, win_of(*x), w + u)) by {
                    lemma_clear_lowest(m1, t, u);
                }
            }
            let off = (w + t as usize - b) as u32;
            proof {
                lemma_sel_write(sel@, k as int, b as int, range_filter(b as int, w + t, p), off, true);
                assert(range_filter(b as int, w + t + 1, p) == range_filter(b as int, w + t, p).push(w + t));
            }
            sel[k] = off;
            k = k + 1;
            proof { q = t + 1; }
        }
        proof {
            assert forall|l: int| w + q <= l < we implies !#[trigger] p(l) by {
                let u = (l - w) as u64;
                lemma_bit_zero(u);
                assert(!bit(m, u));
            }
            lemma_rf_skip(b as int, w + q, we as int, p);
        }
        w = we;
    }
    k
}

// ------------------------------------------------------------------------------------------------ one range

/// Adds the listed rows (`sel`, offsets from `b`) to the accumulator.
fn gather(c: &ScanCols, bits: &Vec<u64>, pos: bool, b: usize, k: usize, sel: &Vec<u32>, acc: &mut Acc,
    Ghost(sv): Ghost<StoresView>, Ghost(w): Ghost<Win>, Ghost(s): Ghost<Seq<int>>, Ghost(t0): Ghost<Tot>)
    requires
        scan_cols_ok(*c, sv), pbits_ok(bits@, sv), pos ==> pos_all(sv),
        sel_matches(sel@, k as int, b as int, s),
        forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < c.nl && in_win(sv, w, s[i]),
        acc_ok(*old(acc), t0),
        t0.cnt + k <= 0xffff_ffff_ffff_ffff,
    ensures acc_ok(*final(acc), tot_plus(t0, tlist(sv, w, s))),
    no_unwind
{
    let mut t: usize = 0;
    while t < k
        invariant
            scan_cols_ok(*c, sv), pbits_ok(bits@, sv), pos ==> pos_all(sv),
            sel_matches(sel@, k as int, b as int, s),
            forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < c.nl && in_win(sv, w, s[i]),
            t <= k, t0.cnt + k <= 0xffff_ffff_ffff_ffff,
            acc_ok(*acc, tot_plus(t0, tlist(sv, w, s.take(t as int)))),
            tot_plus(t0, tlist(sv, w, s.take(t as int))).cnt <= t0.cnt + t,
        decreases k - t,
    {
        let off = sel[t];
        proof {
            assert(b + off as int == s[t as int]);
            lemma_take_step(s, t as int);
            lemma_tlist_push(sv, w, s.take(t as int), s[t as int]);
        }
        let r = b + off as usize;
        let ghost tt = tot_plus(t0, tlist(sv, w, s.take(t as int)));
        add_row(c, bits, pos, r, acc, Ghost(sv), Ghost(w), Ghost(tt));
        proof {
            assert(tot_plus(tt, tot1(sv, w, r as int)) == tot_plus(t0, tlist(sv, w, s.take(t + 1))));
        }
        t = t + 1;
    }
    proof { assert(s.take(k as int) =~= s); }
}

/// `|vol| < 10^31` for every lineitem row (numeric(15,2) factors).
pub open spec fn vol_bound() -> int { 10_000_000_000_000_000_000_000_000_000_000 }

proof fn lemma_vol_bound(sv: StoresView, l: int)
    requires domains_ok(sv), 0 <= l < n_l(sv),
    ensures -vol_bound() < vol(sv, l) < vol_bound(),
{
    let pr = l_price(sv)[l] as int;
    let dc = l_disc(sv)[l] as int;
    assert(num15(l_price(sv)[l]) && num15(l_disc(sv)[l]));
    assert(-10_000_000_000_000_000_000_000_000_000_000 < pr * (100 - dc) < 10_000_000_000_000_000_000_000_000_000_000)
        by (nonlinear_arith)
        requires -1_000_000_000_000_000 < pr < 1_000_000_000_000_000, -1_000_000_000_000_000 < dc < 1_000_000_000_000_000;
}

/// The totals of the listed rows (inside the window, at most `BLOCK` of them) when every part row is positional,
/// exactly (their absolute mass stays far below `2^127`), in three branch-light passes over the list: the part
/// keys, the volumes, then the sums (the part row of key `k` is `k - 1`, `0 <= k - 1 < np`).
fn gather_fast(c: &ScanCols, bits: &Vec<u64>, b: usize, k: usize, sel: &Vec<u32>, pkb: &mut Vec<i64>, vb: &mut Vec<i128>,
    Ghost(sv): Ghost<StoresView>, Ghost(w): Ghost<Win>, Ghost(s): Ghost<Seq<int>>) -> (r: Acc)
    requires
        scan_cols_ok(*c, sv), pbits_ok(bits@, sv), pos_all(sv),
        sel_matches(sel@, k as int, b as int, s),
        forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < c.nl && in_win(sv, w, s[i]),
        k <= BLOCK, old(pkb)@.len() == BLOCK, old(vb)@.len() == BLOCK,
    ensures
        acc_ok(r, tlist(sv, w, s)),
        final(pkb)@.len() == BLOCK, final(vb)@.len() == BLOCK,
    no_unwind
{
    // pass 1: the part keys of the listed rows
    let mut t: usize = 0;
    while t < k
        invariant
            scan_cols_ok(*c, sv), sel_matches(sel@, k as int, b as int, s), k <= BLOCK, pkb@.len() == BLOCK, t <= k,
            forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < c.nl,
            forall|i: int| 0 <= i < t ==> #[trigger] pkb@[i] == l_pkey(sv)[s[i]],
        decreases k - t,
    {
        let off = sel[t];
        proof { assert(b + off as int == s[t as int]); }
        let r = b + off as usize;
        pkb[t] = c.pkey[r];
        t = t + 1;
    }
    // pass 2: their volumes
    let mut t: usize = 0;
    while t < k
        invariant
            scan_cols_ok(*c, sv), sel_matches(sel@, k as int, b as int, s), k <= BLOCK, vb@.len() == BLOCK, t <= k,
            forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < c.nl,
            forall|i: int| 0 <= i < t ==> #[trigger] vb@[i] as int == vol(sv, s[i]),
        decreases k - t,
    {
        let off = sel[t];
        proof { assert(b + off as int == s[t as int]); }
        let r = b + off as usize;
        let pr = c.price[r];
        let dc = c.disc[r];
        proof {
            assert(num15(l_price(sv)[r as int]) && num15(l_disc(sv)[r as int]));
            assert(-10_000_000_000_000_000_000_000_000_000_000 < (pr as int) * (100 - dc as int)
                < 10_000_000_000_000_000_000_000_000_000_000) by (nonlinear_arith)
                requires -1_000_000_000_000_000 < (pr as int) < 1_000_000_000_000_000,
                    -1_000_000_000_000_000 < (dc as int) < 1_000_000_000_000_000;
        }
        vb[t] = pr * (100 - dc);
        t = t + 1;
    }
    // pass 3: the sums
    let np = c.np;
    let mut cnt: u64 = 0;
    let mut npr: u64 = 0;
    let mut sa: i128 = 0;
    let mut sp: i128 = 0;
    let mut ma: u128 = 0;
    let mut t: usize = 0;
    proof { assert(s.take(0) =~= Seq::<int>::empty()); }
    while t < k
        invariant
            scan_cols_ok(*c, sv), pbits_ok(bits@, sv), pos_all(sv), np == c.np,
            sel_matches(sel@, k as int, b as int, s), k <= BLOCK, t <= k,
            pkb@.len() == BLOCK, vb@.len() == BLOCK,
            forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < c.nl && in_win(sv, w, s[i]),
            forall|i: int| 0 <= i < k ==> #[trigger] pkb@[i] == l_pkey(sv)[s[i]],
            forall|i: int| 0 <= i < k ==> #[trigger] vb@[i] as int == vol(sv, s[i]),
            acc_ok(Acc { cnt, n_pr: npr, s_all: sa, s_pr: sp, mass: ma }, tlist(sv, w, s.take(t as int))),
            tlist(sv, w, s.take(t as int)).a_all <= t * vol_bound(),
            tlist(sv, w, s.take(t as int)).cnt <= t,
        decreases k - t,
    {
        let ghost l = s[t as int];
        let ghost t0 = tlist(sv, w, s.take(t as int));
        proof {
            lemma_take_step(s, t as int);
            lemma_tlist_push(sv, w, s.take(t as int), l);
            lemma_vol_bound(sv, l);
            assert(t * vol_bound() + vol_bound() <= BLOCK * vol_bound()) by (nonlinear_arith)
                requires t < k, k <= BLOCK;
        }
        let d = pkb[t] as i128 - 1;
        let found = 0 <= d && d < np as i128;
        let a: usize = if found { d as usize } else { 0 };
        let word: u64 = if found { bits[a / 64] } else { 0 };
        let promo = found && (word >> ((a % 64) as u64)) & 1u64 == 1u64;
        let v: i128 = if found { vb[t] } else { 0 };
        let pv: i128 = if promo { v } else { 0 };
        let av: u128 = if v < 0 { (-v) as u128 } else { v as u128 };
        proof {
            if found {
                assert(p_key(sv)[a as int] as int == a + 1);
                lemma_part_is(sv, l, a as int);
                assert(word_bit(bits@, a as int) == promo);
            } else {
                assert forall|q: int| 0 <= q < n_p(sv) implies #[trigger] p_key(sv)[q] != l_pkey(sv)[l] by {
                    assert(p_key(sv)[q] as int == q + 1);
                }
                lemma_no_part(sv, l);
            }
            assert(tot1(sv, w, l).cnt == if found { 1int } else { 0int });
            assert(tot1(sv, w, l).s_all == v as int);
            assert(tot1(sv, w, l).a_all == av as int);
            assert(tot1(sv, w, l).s_pr == pv as int);
        }
        cnt = cnt + if found { 1u64 } else { 0u64 };
        npr = npr + if promo { 1u64 } else { 0u64 };
        sa = sa + v;
        sp = sp + pv;
        ma = ma + av;
        t = t + 1;
    }
    proof { assert(s.take(k as int) =~= s); }
    Acc { cnt, n_pr: npr, s_all: sa, s_pr: sp, mass: ma }
}

/// The scan inputs of a task.
pub open spec fn scan_inputs_ok(c: ScanCols, x: Window, bits: Seq<u64>, pos: bool, sv: StoresView) -> bool {
    &&& scan_cols_ok(c, sv)
    &&& window_wf(x)
    &&& pbits_ok(bits, sv)
    &&& pos ==> pos_all(sv)
}

/// The totals of the rows `[lo, hi)`.
pub fn scan_range(c: &ScanCols, x: &Window, bits: &Vec<u64>, pos: bool, lo: usize, hi: usize, sel: &mut Vec<u32>,
    pkb: &mut Vec<i64>, vb: &mut Vec<i128>, Ghost(sv): Ghost<StoresView>) -> (acc: Acc)
    requires
        scan_inputs_ok(*c, *x, bits@, pos, sv),
        lo <= hi <= c.nl, old(sel)@.len() == BLOCK, old(pkb)@.len() == BLOCK, old(vb)@.len() == BLOCK,
    ensures
        final(sel)@.len() == BLOCK, final(pkb)@.len() == BLOCK, final(vb)@.len() == BLOCK,
        acc_ok(acc, tot(sv, win_of(*x), lo as int, hi as int)),
    no_unwind
{
    let ghost w = win_of(*x);
    let ghost p = pwin(sv, w);
    let table = tz_table_array();
    let mut acc = acc_new();
    let mut b = lo;
    proof { lemma_tot_empty(sv, w, lo as int); }
    while b < hi
        invariant
            scan_inputs_ok(*c, *x, bits@, pos, sv), table@.len() == 64,
            lo <= b <= hi <= c.nl, sel@.len() == BLOCK, pkb@.len() == BLOCK, vb@.len() == BLOCK,
            w == win_of(*x), p == pwin(sv, w),
            acc_ok(acc, tot(sv, w, lo as int, b as int)),
        decreases hi - b,
    {
        let e = if hi - b > BLOCK { b + BLOCK } else { hi };
        let k = select(c, x, &table, b, e, sel, Ghost(sv));
        let ghost s = range_filter(b as int, e as int, p);
        proof {
            lemma_range_filter_bounds(b as int, e as int, p);
            assert forall|i: int| 0 <= i < s.len() implies 0 <= #[trigger] s[i] < c.nl && in_win(sv, w, s[i]) by {
                lemma_range_filter_members(b as int, e as int, p, i);
            }
            lemma_tot_bounds(sv, w, lo as int, b as int);
            lemma_rf_len(b as int, e as int, p);
        }
        proof {
            lemma_tlist_window(sv, w, b as int, e as int);
            lemma_tot_split(sv, w, lo as int, b as int, e as int);
            lemma_tot_bounds(sv, w, b as int, e as int);
        }
        if pos {
            let ba = gather_fast(c, bits, b, k, sel, pkb, vb, Ghost(sv), Ghost(w), Ghost(s));
            acc = acc_merge(acc, ba, Ghost(tot(sv, w, lo as int, b as int)), Ghost(tlist(sv, w, s)));
        } else {
            gather(c, bits, pos, b, k, sel, &mut acc, Ghost(sv), Ghost(w), Ghost(s), Ghost(tot(sv, w, lo as int, b as int)));
        }
        b = e;
    }
    acc
}

/// The elements of a range filter satisfy the condition.
proof fn lemma_range_filter_members(lo: int, hi: int, p: spec_fn(int) -> bool, i: int)
    requires 0 <= i < range_filter(lo, hi, p).len(),
    ensures p(range_filter(lo, hi, p)[i]),
    decreases hi - lo,
{
    if hi > lo {
        let s = range_filter(lo, hi - 1, p);
        if i < s.len() {
            lemma_range_filter_members(lo, hi - 1, p, i);
            if p(hi - 1) {
                assert(range_filter(lo, hi, p)[i] == s[i]);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ the task

/// One scan task: the rows `lo..hi`.
pub struct ScanTask {
    pub cols: ScanCols,
    pub win: Window,
    pub bits: Arc<Vec<u64>>,
    pub pos: bool,
    pub lo: usize,
    pub hi: usize,
    pub sel: Vec<u32>,
    pub pkb: Vec<i64>,
    pub vb: Vec<i128>,
    pub sv: Ghost<StoresView>,
}

impl WorkerTask for ScanTask {
    type Output = Acc;

    open spec fn pre(&self) -> bool {
        &&& scan_inputs_ok(self.cols, self.win, (*self.bits)@, self.pos, self.sv@)
        &&& self.lo <= self.hi <= self.cols.nl
        &&& self.sel@.len() == BLOCK
        &&& self.pkb@.len() == BLOCK
        &&& self.vb@.len() == BLOCK
    }

    open spec fn post(&self, out: Acc) -> bool {
        acc_ok(out, tot(self.sv@, win_of(self.win), self.lo as int, self.hi as int))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Acc) {
        let ScanTask { cols, win, bits, pos, lo, hi, sel, pkb, vb, sv } = self;
        let mut sel = sel;
        let mut pkb = pkb;
        let mut vb = vb;
        scan_range(&cols, &win, &*bits, pos, lo, hi, &mut sel, &mut pkb, &mut vb, sv)
    }
}

} // verus!
