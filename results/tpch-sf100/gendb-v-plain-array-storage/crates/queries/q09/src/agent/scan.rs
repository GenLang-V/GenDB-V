//! The lineitem scan of one task (`LineTask`): rows `lo..hi`, accumulating per nation group and year (`answer::tsum`)
//! the count and the amount into a table of `NG x YW` slots, and the absolute amount of all qualifying rows
//! (`answer::msum`).
//!
//! Fast-path facts (`scan_ok`): `p_partkey` and `s_suppkey` are positional (a key finds its row by subtraction), the
//! part bitmap (`partmatch::bits_ok`), the word locations and records (`records`), the year table and at most `NG`
//! nations with small keys (`nations`). Rows are processed in blocks of `BLK` rows, each through short loops over
//! small buffers so that the memory loads of different rows overlap:
//! 1. filter (`stage_filter`): the rows whose part key is in range and whose part's bit is set (`hit`), in row order;
//!    every other row does not qualify (`lemma_nonhit`);
//! 2. ranks (`stage_rank`): each candidate's chunk and record index (`records::wl_ok`);
//! 3. warming loops (`touch_*`): read the records and the lineitem and orders values the later loops need (no
//!    meaning; their checksum reaches the task's result);
//! 4. match (`stage_match`): the record entry of the row's supplier gives its partsupp row, supply cost and nation
//!    group (`pre_qual`);
//! 5. accumulate (`stage_acc`): the order at the key's dbgen position (checked against `o_orderkey`), its year (year
//!    table), the amount, and the table update (`table_ok`).
//! Any row the fast path cannot place (no record entry, a missing nation, an order not at its dbgen position, a year
//! outside the table, an absolute amount beyond `i128::MAX`) stops the task with `bail`; the query then uses the
//! general path.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::link::expr::i128_max;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::lines::*;
use crate::agent::answer::*;
use crate::agent::columns::*;
use crate::agent::partmatch::*;
use crate::agent::nations::*;
use crate::agent::records::*;
use crate::agent::common::bits::*;
use crate::agent::common::popc::*;
use crate::agent::common::split::*;

verus! {

/// Rows per block (at most; the buffers' length).
pub const BLK: usize = 4096;

/// Rows per block when several workers scan.
pub const BLK_PAR: usize = 512;

/// Table slots: `NG` groups times `YW` years.
pub const NT: usize = 8160;

/// Scalar parameters of the scan.
#[derive(Clone, Copy)]
pub struct ScanPar {
    pub pbase: i64,
    pub sbase: i64,
    pub k: usize,
}

/// Everything the scan reads, and the fast-path facts.
pub open spec fn scan_ok(c: Cols, bits: Seq<u64>, wl: Seq<u64>, recs: Seq<Vec<i64>>, ytab: Seq<u8>, pc: Seq<u8>,
    par: ScanPar, sv: StoresView, ps: Seq<Literal>) -> bool
{
    &&& cols_ok(c, sv)
    &&& bits_ok(bits, sv, ps)
    &&& 1 <= par.k <= 64 && wl_ok(wl, bits, par.k as int) && recs_ok(recs, bits, par.k as int, sv, par.sbase as int)
    &&& ytab_ok(ytab) && pc_ok(pc)
    &&& nations_small(sv)
    &&& positional(pk(sv), par.pbase as int) && positional(sk(sv), par.sbase as int)
    &&& 0 <= par.pbase && par.pbase + n_p(sv) < i64::MAX && n_p(sv) < 0x1_0000_0000
    &&& 0 <= par.sbase && par.sbase + n_s(sv) < i64::MAX
}

// ------------------------------------------------------------------------------------------------ rows

/// The part row of lineitem row `l` by subtraction.
pub open spec fn prow(sv: StoresView, par: ScanPar, l: int) -> int { lpk(sv)[l] as int - par.pbase }

/// Lineitem row `l`'s part key is a part's, and that part's name matches.
pub open spec fn hit(sv: StoresView, ps: Seq<Literal>, par: ScanPar, l: int) -> bool {
    0 <= prow(sv, par, l) < n_p(sv) && match_bit(sv, ps, prow(sv, par, l))
}

/// A positional key column holds `k` exactly in `base .. base + len`, at row `k - base`.
pub proof fn lemma_positional(keys: Seq<i64>, base: int, k: i64)
    requires positional(keys, base), keys_unique(keys),
    ensures
        has_key(keys, k) == (base <= k < base + keys.len()),
        has_key(keys, k) ==> key_row(keys, k) == k - base,
{
    if base <= k < base + keys.len() {
        let r = k - base;
        assert(keys[r] as int == base + r);
        assert(has_key(keys, k));
    }
    lemma_key_row(keys, k);
    if has_key(keys, k) {
        let j = key_row(keys, k);
        assert(keys[j] as int == base + j);
    }
}

/// A row that is not a hit does not qualify.
pub proof fn lemma_nonhit(c: Cols, bits: Seq<u64>, wl: Seq<u64>, recs: Seq<Vec<i64>>, ytab: Seq<u8>, pc: Seq<u8>,
    par: ScanPar, sv: StoresView, ps: Seq<Literal>, l: int)
    requires scan_ok(c, bits, wl, recs, ytab, pc, par, sv, ps), 0 <= l < n_l(sv), !hit(sv, ps, par, l),
    ensures !line_qual(sv, ps, l),
{
    lemma_positional(pk(sv), par.pbase as int, lpk(sv)[l]);
}

// ------------------------------------------------------------------------------------------------ the table

/// The table's slot `ix` is group `ix / YW`, year `Y0 + ix % YW`.
pub open spec fn tgrp(ix: int) -> int { ix / (YW as int) }
pub open spec fn tyr(ix: int) -> int { Y0 + ix % (YW as int) }

/// The table holds the counts and amounts of the rows `lo..x`, every qualifying row of them falls inside the table,
/// and `mass` is their absolute amount (within `i128`).
pub open spec fn table_ok(acc: Seq<i128>, cnt: Seq<u64>, mass: u128, sv: StoresView, ps: Seq<Literal>, lo: int, x: int) -> bool {
    &&& acc.len() == NT && cnt.len() == NT
    &&& forall|ix: int| 0 <= ix < NT ==> #[trigger] acc[ix] as int == tsum(sv, ps, tgrp(ix), tyr(ix), 1, lo, x)
        && cnt[ix] as int == tsum(sv, ps, tgrp(ix), tyr(ix), 0, lo, x)
    &&& forall|a: int, y: int| #[trigger] tsum(sv, ps, a, y, 0, lo, x) > 0 ==> 0 <= a < NG && Y0 <= y < Y0 + YW
    &&& mass as int == msum(sv, ps, lo, x) && mass as int <= i128_max()
}

/// The slot of group `a`, year slot `yi`.
pub proof fn lemma_slot(a: int, yi: int)
    requires 0 <= a < NG, 0 <= yi < YW,
    ensures 0 <= a * 255 + yi < NT, tgrp(a * 255 + yi) == a, tyr(a * 255 + yi) == Y0 + yi,
{
    assert(0 <= a * 255 + yi < NT) by (nonlinear_arith) requires 0 <= a < 32, 0 <= yi < 255;
    assert((a * 255 + yi) / 255 == a) by (nonlinear_arith) requires 0 <= a, 0 <= yi < 255;
    assert((a * 255 + yi) % 255 == yi) by (nonlinear_arith) requires 0 <= a, 0 <= yi < 255;
}

/// Zero table over the empty range.
pub proof fn lemma_table_empty(acc: Seq<i128>, cnt: Seq<u64>, sv: StoresView, ps: Seq<Literal>, lo: int)
    requires acc == Seq::new(NT as nat, |_i: int| 0i128), cnt == Seq::new(NT as nat, |_i: int| 0u64),
    ensures table_ok(acc, cnt, 0, sv, ps, lo, lo),
{
    assert forall|a: int, y: int| #[trigger] tsum(sv, ps, a, y, 0, lo, lo) > 0 implies 0 <= a < NG && Y0 <= y < Y0 + YW by {}
}

/// Counts are bounded by the number of rows.
pub proof fn lemma_count_le(sv: StoresView, ps: Seq<Literal>, a: int, y: int, lo: int, x: int)
    requires lo <= x,
    ensures tsum(sv, ps, a, y, 0, lo, x) <= x - lo,
    decreases x - lo,
{
    if x > lo {
        lemma_count_le(sv, ps, a, y, lo, x - 1);
    }
}

/// Rows `x..y` that are not hits leave the table as it is.
pub proof fn lemma_skip(c: Cols, bits: Seq<u64>, wl: Seq<u64>, recs: Seq<Vec<i64>>, ytab: Seq<u8>, pc: Seq<u8>,
    par: ScanPar, sv: StoresView, ps: Seq<Literal>, acc: Seq<i128>, cnt: Seq<u64>, mass: u128, lo: int, x: int, y: int)
    requires
        scan_ok(c, bits, wl, recs, ytab, pc, par, sv, ps), 0 <= lo <= x <= y <= n_l(sv),
        forall|l: int| x <= l < y ==> !#[trigger] hit(sv, ps, par, l),
        table_ok(acc, cnt, mass, sv, ps, lo, x),
    ensures table_ok(acc, cnt, mass, sv, ps, lo, y),
    decreases y - x,
{
    if y > x {
        lemma_skip(c, bits, wl, recs, ytab, pc, par, sv, ps, acc, cnt, mass, lo, x, y - 1);
        lemma_nonhit(c, bits, wl, recs, ytab, pc, par, sv, ps, y - 1);
        assert forall|ix: int| 0 <= ix < NT implies #[trigger] acc[ix] as int == tsum(sv, ps, tgrp(ix), tyr(ix), 1, lo, y)
            && cnt[ix] as int == tsum(sv, ps, tgrp(ix), tyr(ix), 0, lo, y) by {}
        assert forall|a: int, yy: int| #[trigger] tsum(sv, ps, a, yy, 0, lo, y) > 0 implies 0 <= a < NG && Y0 <= yy < Y0 + YW by {
            assert(tsum(sv, ps, a, yy, 0, lo, y) == tsum(sv, ps, a, yy, 0, lo, y - 1));
        }
    }
}

/// One qualifying row `x` of group `a`, year slot `yi` and amount `v`: the table with the row added.
pub proof fn lemma_add_row(acc: Seq<i128>, cnt: Seq<u64>, mass: u128, sv: StoresView, ps: Seq<Literal>, lo: int, x: int,
    a: int, yi: int, v: int, acc2: Seq<i128>, cnt2: Seq<u64>, mass2: u128)
    requires
        table_ok(acc, cnt, mass, sv, ps, lo, x), lo <= x,
        line_qual(sv, ps, x), grp(sv, x) == a, yr(sv, x) == Y0 + yi, line_val(sv, x) == v,
        0 <= a < NG, 0 <= yi < YW,
        acc2 == acc.update(a * 255 + yi, (acc[a * 255 + yi] + v) as i128),
        cnt2 == cnt.update(a * 255 + yi, (cnt[a * 255 + yi] + 1) as u64),
        acc[a * 255 + yi] + v <= i128::MAX, acc[a * 255 + yi] + v >= i128::MIN, cnt[a * 255 + yi] + 1 <= u64::MAX,
        mass2 as int == mass + abs(v), mass2 as int <= i128_max(),
    ensures table_ok(acc2, cnt2, mass2, sv, ps, lo, x + 1),
{
    let ix0 = a * 255 + yi;
    lemma_slot(a, yi);
    assert forall|ix: int| 0 <= ix < NT implies #[trigger] acc2[ix] as int == tsum(sv, ps, tgrp(ix), tyr(ix), 1, lo, x + 1)
        && cnt2[ix] as int == tsum(sv, ps, tgrp(ix), tyr(ix), 0, lo, x + 1) by {
        if ix == ix0 {
        } else {
            if tgrp(ix) == a && tyr(ix) == Y0 + yi {
                assert(ix == tgrp(ix) * 255 + ix % 255) by (nonlinear_arith) requires 0 <= ix, tgrp(ix) == ix / 255;
                assert(ix % 255 == yi);
            }
        }
    }
    assert forall|aa: int, y: int| #[trigger] tsum(sv, ps, aa, y, 0, lo, x + 1) > 0 implies 0 <= aa < NG && Y0 <= y < Y0 + YW by {
        if !(aa == a && y == Y0 + yi) {
            assert(tsum(sv, ps, aa, y, 0, lo, x + 1) == tsum(sv, ps, aa, y, 0, lo, x));
        }
    }
}


// ------------------------------------------------------------------------------------------------ 1. filter

/// `cand[..n]` lists, in increasing order, the offsets from `b0` of exactly the hit rows of `b0..b1`.
pub open spec fn cands_ok(sv: StoresView, ps: Seq<Literal>, par: ScanPar, cand: Seq<u32>, n: int, b0: int, b1: int) -> bool {
    &&& 0 <= n <= b1 - b0 && n <= cand.len()
    &&& forall|i: int| 0 <= i < n ==> (#[trigger] cand[i]) < b1 - b0 && hit(sv, ps, par, b0 + cand[i])
    &&& forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] cand[i] < #[trigger] cand[j]
    &&& forall|l: int| b0 <= l < b1 && #[trigger] hit(sv, ps, par, l) ==> exists|i: int| 0 <= i < n && b0 + cand[i] == l
}

/// Row `x`'s bit in a bitmap word, by shift and mask.
proof fn lemma_word_probe(word: u64, x: usize)
    ensures ((word >> ((x % 64) as u64)) & 1u64 == 1u64) == bit(word, (x % 64) as u64),
{
}

/// The candidates of rows `b0..b1`.
pub fn stage_filter(c: &Cols, bits: &Vec<u64>, par: ScanPar, b0: usize, b1: usize, cand: &mut Vec<u32>,
    Ghost(wl): Ghost<Seq<u64>>, Ghost(recs): Ghost<Seq<Vec<i64>>>, Ghost(ytab): Ghost<Seq<u8>>, Ghost(pc): Ghost<Seq<u8>>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (n: usize)
    requires
        scan_ok(*c, bits@, wl, recs, ytab, pc, par, sv, ps), b0 <= b1 <= c.nl, b1 - b0 <= BLK, old(cand)@.len() == BLK,
    ensures final(cand)@.len() == BLK, cands_ok(sv, ps, par, final(cand)@, n as int, b0 as int, b1 as int),
    no_unwind
{
    let np = c.np as i128;
    let pb = par.pbase as i128;
    let mut n: usize = 0;
    let mut l = b0;
    while l < b1
        invariant
            scan_ok(*c, bits@, wl, recs, ytab, pc, par, sv, ps), b0 <= l <= b1 <= c.nl, b1 - b0 <= BLK,
            cand@.len() == BLK, np == c.np, pb == par.pbase,
            cands_ok(sv, ps, par, cand@, n as int, b0 as int, l as int),
        decreases b1 - l,
    {
        let x = c.lpart[l] as i128 - pb;
        let inr = 0 <= x && x < np;
        let ri: usize = if inr { x as usize } else { 0 };
        proof {
            if inr {
                assert(ri < 64 * bits@.len());
                lemma_word_probe(bits@[(ri / 64) as int], ri);
                assert(word_bit(bits@, ri as int) == bit(bits@[(ri / 64) as int], (ri % 64) as u64));
            }
        }
        let h = inr && (bits[ri / 64] >> ((ri % 64) as u64)) & 1u64 == 1u64;
        proof {
            assert(x as int == prow(sv, par, l as int));
            assert(h == hit(sv, ps, par, l as int));
        }
        let ghost before = cand@;
        cand[n] = (l - b0) as u32;
        proof {
            let n1 = if h { n + 1 } else { n as int };
            assert forall|i: int| 0 <= i < n implies #[trigger] cand@[i] == before[i] by {}
            assert(cands_ok(sv, ps, par, cand@, n1, b0 as int, l + 1)) by {
                assert forall|i: int| 0 <= i < n1 implies (#[trigger] cand@[i]) < l + 1 - b0 && hit(sv, ps, par, b0 + cand@[i]) by {
                    if i < n { assert(cand@[i] == before[i]); }
                }
                assert forall|i: int, j: int| 0 <= i < j < n1 implies #[trigger] cand@[i] < #[trigger] cand@[j] by {
                    if j == n { assert(cand@[i] == before[i]); }
                }
                assert forall|ll: int| b0 <= ll < l + 1 && #[trigger] hit(sv, ps, par, ll) implies exists|i: int| 0 <= i < n1 && b0 + cand@[i] == ll by {
                    if ll < l {
                        let i = choose|i: int| 0 <= i < n && b0 + before[i] == ll;
                        assert(cand@[i] == before[i]);
                    } else {
                        assert(b0 + cand@[n as int] == ll);
                    }
                }
            }
        }
        if h {
            n = n + 1;
        }
        l = l + 1;
    }
    n
}

// ------------------------------------------------------------------------------------------------ 2. ranks

/// Candidate `i`'s record: chunk `chk[i]`, index `rix[i]` (`records::rec_ok`).
pub open spec fn ranks_ok(sv: StoresView, ps: Seq<Literal>, par: ScanPar, recs: Seq<Vec<i64>>, cand: Seq<u32>, n: int,
    b0: int, chk: Seq<u32>, rix: Seq<usize>) -> bool
{
    forall|i: int| 0 <= i < n ==> (#[trigger] chk[i]) < par.k
        && rec_ok(recs[chk[i] as int]@, rix[i] as int, prow(sv, par, b0 + cand[i]), sv, par.sbase as int)
}

/// The record of hit row `l`.
fn rank_of(c: &Cols, wl: &Vec<u64>, recs_v: &Vec<Vec<i64>>, pc: &[u8; 256], par: ScanPar, l: usize,
    Ghost(bits): Ghost<Seq<u64>>, Ghost(recs): Ghost<Seq<Vec<i64>>>, Ghost(ytab): Ghost<Seq<u8>>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (ce: (u32, usize))
    requires scan_ok(*c, bits, wl@, recs, ytab, pc@, par, sv, ps), l < c.nl, hit(sv, ps, par, l as int), recs_v@ == recs,
    ensures ce.0 < par.k, rec_ok(recs[ce.0 as int]@, ce.1 as int, prow(sv, par, l as int), sv, par.sbase as int),
    no_unwind
{
    let r = (c.lpart[l] - par.pbase) as usize;
    let w = r / 64;
    let t = r % 64;
    proof {
        assert(r as int == prow(sv, par, l as int));
        assert(w < bits.len());
        assert(word_bit(bits, r as int));
    }
    let bw = wl[2 * w];
    let loc = wl[2 * w + 1];
    let ch = loc >> 32u64;
    let cnt = loc & 0xffff_ffffu64;
    let pcnt = popc_below(bw, t as u64, pc);
    proof {
        assert((loc >> 32u64) == loc / 0x1_0000_0000) by (bit_vector);
        assert((loc & 0xffff_ffffu64) == loc % 0x1_0000_0000) by (bit_vector);
        assert(cnt < 0x1_0000_0000);
        assert(pcnt >= 1 && pcnt <= 64) by {
            lemma_count_bounds(bw, t as int, t + 1);
        }
        let cc = ch as int;
        assert(wloc_ok(loc, bits, par.k as int, w as int));
        let w0 = split(bits.len() as int, par.k as int, cc);
        assert(chunk_recs_ok(recs[cc]@, bits, w0, split(bits.len() as int, par.k as int, cc + 1), sv, par.sbase as int));
        assert(64 * w0 <= r < 64 * split(bits.len() as int, par.k as int, cc + 1));
        lemma_count_step(bw, t as int);
        assert(bit(bw, t as u64));
        assert(r / 64 == w && r % 64 == t);
        assert(cnt as int + pcnt as int - 1 == crank(bits, w0, r as int));
        lemma_cnt_nonneg(bits, w0, w as int);
        lemma_count_nonneg(bw, t as int);
        assert(rec_ok(recs[cc]@, crank(bits, w0, r as int), r as int, sv, par.sbase as int));
    }
    let e: u64 = cnt + pcnt - 1;
    let rl = recs_v[ch as usize].len();
    proof { assert(4 * e + 4 <= rl); }
    (ch as u32, e as usize)
}

/// The records of the candidates.
pub fn stage_rank(c: &Cols, wl: &Vec<u64>, recs_v: &Vec<Vec<i64>>, pc: &[u8; 256], par: ScanPar, b0: usize, cand: &Vec<u32>, n: usize,
    chk: &mut Vec<u32>, rix: &mut Vec<usize>,
    Ghost(bits): Ghost<Seq<u64>>, Ghost(recs): Ghost<Seq<Vec<i64>>>, Ghost(ytab): Ghost<Seq<u8>>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(b1): Ghost<int>)
    requires
        scan_ok(*c, bits, wl@, recs, ytab, pc@, par, sv, ps), b0 <= b1 <= c.nl, recs_v@ == recs,
        cands_ok(sv, ps, par, cand@, n as int, b0 as int, b1), old(chk)@.len() == BLK, old(rix)@.len() == BLK, cand@.len() == BLK,
    ensures
        final(chk)@.len() == BLK, final(rix)@.len() == BLK,
        ranks_ok(sv, ps, par, recs, cand@, n as int, b0 as int, final(chk)@, final(rix)@),
    no_unwind
{
    let mut i: usize = 0;
    while i < n
        invariant
            scan_ok(*c, bits, wl@, recs, ytab, pc@, par, sv, ps), b0 <= b1 <= c.nl, i <= n, recs_v@ == recs,
            cands_ok(sv, ps, par, cand@, n as int, b0 as int, b1), chk@.len() == BLK, rix@.len() == BLK, cand@.len() == BLK,
            ranks_ok(sv, ps, par, recs, cand@, i as int, b0 as int, chk@, rix@),
        decreases n - i,
    {
        let l = b0 + cand[i] as usize;
        let (ch, e) = rank_of(c, wl, recs_v, pc, par, l, Ghost(bits), Ghost(recs), Ghost(ytab), Ghost(sv), Ghost(ps));
        chk[i] = ch;
        rix[i] = e;
        i = i + 1;
    }
}

// ------------------------------------------------------------------------------------------------ 3. warming

/// Reads the first value of every candidate's record (no meaning; a checksum).
pub fn touch_recs(recs: &Vec<Vec<i64>>, chk: &Vec<u32>, rix: &Vec<usize>, n: usize,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(par): Ghost<ScanPar>, Ghost(cand): Ghost<Seq<u32>>,
    Ghost(b0): Ghost<int>) -> (t: u64)
    requires n <= chk@.len(), n <= rix@.len(), ranks_ok(sv, ps, par, recs@, cand, n as int, b0, chk@, rix@), par.k <= recs@.len(),
    no_unwind
{
    let mut t: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant i <= n, n <= chk@.len(), n <= rix@.len(), ranks_ok(sv, ps, par, recs@, cand, n as int, b0, chk@, rix@), par.k <= recs@.len(),
        decreases n - i,
    {
        let rec = &recs[chk[i] as usize];
        let rl = rec.len();
        proof { assert(4 * rix@[i as int] + 4 <= rl); }
        t = t.wrapping_add(rec[rix[i] * 4] as u64);
        i = i + 1;
    }
    t
}

/// Reads the lineitem values of every candidate (no meaning; a checksum).
pub fn touch_cols(c: &Cols, b0: usize, cand: &Vec<u32>, n: usize, Ghost(b1): Ghost<int>) -> (t: u64)
    requires n <= cand@.len(), b0 <= b1 <= c.nl, forall|i: int| 0 <= i < n ==> b0 + (#[trigger] cand@[i]) < b1,
        c.lsupp@.len() == c.nl, c.lokey@.len() == c.nl, c.lqty@.len() == c.nl, c.lprice@.len() == c.nl, c.ldisc@.len() == c.nl,
    no_unwind
{
    let mut t: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant i <= n, n <= cand@.len(), b0 <= b1 <= c.nl, forall|i: int| 0 <= i < n ==> b0 + (#[trigger] cand@[i]) < b1,
            c.lsupp@.len() == c.nl, c.lokey@.len() == c.nl, c.lqty@.len() == c.nl, c.lprice@.len() == c.nl, c.ldisc@.len() == c.nl,
        decreases n - i,
    {
        let l = b0 + cand[i] as usize;
        t = t.wrapping_add(c.lsupp[l] as u64).wrapping_add(c.lokey[l] as u64).wrapping_add(c.lqty[l] as u64)
            .wrapping_add(c.lprice[l] as u64).wrapping_add(c.ldisc[l] as u64);
        i = i + 1;
    }
    t
}

/// Reads the orders values at every candidate's order row (no meaning; a checksum).
pub fn touch_orders(c: &Cols, orw: &Vec<u64>, n: usize) -> (t: u64)
    requires n <= orw@.len(), c.okey@.len() == c.no, c.odate@.len() == c.no,
    no_unwind
{
    let mut t: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant i <= n, n <= orw@.len(), c.okey@.len() == c.no, c.odate@.len() == c.no,
        decreases n - i,
    {
        let o = orw[i];
        if o < c.no as u64 {
            let ou = o as usize;
            t = t.wrapping_add(c.okey[ou] as u64).wrapping_add(c.odate[ou] as u64);
        }
        i = i + 1;
    }
    t
}


// ------------------------------------------------------------------------------------------------ 4. match

/// Lineitem row `l` has its part (whose name matches), supplier, partsupp row and supplier nation, with supply
/// cost `cost` and group `slot` (inside the table).
pub open spec fn pre_qual(sv: StoresView, ps: Seq<Literal>, l: int, cost: int, slot: int) -> bool {
    &&& has_key(pk(sv), lpk(sv)[l]) && like_true(pname(sv, l_part(sv, l)), pat_of(ps))
    &&& has_key(sk(sv), lsk(sv)[l]) && has_key2(pspk(sv), pssk(sv), lpk(sv)[l], lsk(sv)[l])
    &&& has_key(nk(sv), sn(sv)[l_supp(sv, l)])
    &&& psc(sv)[l_ps(sv, l)] as int == cost && grp(sv, l) == slot && 0 <= slot < NG
}

/// Every candidate's facts after the match stage.
pub open spec fn matched_ok(sv: StoresView, ps: Seq<Literal>, cand: Seq<u32>, n: int, b0: int, costb: Seq<i64>, slotb: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] pre_qual(sv, ps, b0 + cand[i], costb[i] as int, slotb[i] as int)
}

/// Unpacking an entry: its supplier row, supply cost and slot.
proof fn lemma_unpack(x: int, s: int, cost: int, slot: int)
    requires x == pack(s, cost, slot), 0 <= s, 0 <= cost < 0x80_0000, 0 <= slot < 256,
    ensures x / 0x1_0000_0000 == s, (x / 256) % 0x100_0000 == cost, x % 256 == slot, x >= 0,
{
    assert(x / 0x1_0000_0000 == s && (x / 256) % 0x100_0000 == cost && x % 256 == slot) by (nonlinear_arith)
        requires x == s * 0x1_0000_0000 + cost * 256 + slot, 0 <= s, 0 <= cost < 0x80_0000, 0 <= slot < 256;
}

/// The fields of an entry by shifts and masks.
proof fn lemma_fields(xu: u64)
    ensures
        xu >> 32u64 == xu / 0x1_0000_0000,
        (xu >> 8u64) & 0xff_ffffu64 == (xu / 256) % 0x100_0000,
        xu & 0xffu64 == xu % 256,
{
    assert(xu >> 32u64 == xu / 0x1_0000_0000) by (bit_vector);
    assert((xu >> 8u64) & 0xff_ffffu64 == (xu / 256) % 0x100_0000) by (bit_vector);
    assert(xu & 0xffu64 == xu % 256) by (bit_vector);
}

/// The supply cost and group of hit row `l` from its part's record, if its supplier has an entry and a nation.
fn match_row(c: &Cols, recs_v: &Vec<Vec<i64>>, par: ScanPar, l: usize, ch: u32, e: usize,
    Ghost(bits): Ghost<Seq<u64>>, Ghost(wl): Ghost<Seq<u64>>, Ghost(ytab): Ghost<Seq<u8>>, Ghost(pc): Ghost<Seq<u8>>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<(i64, u32)>)
    requires
        scan_ok(*c, bits, wl, recs_v@, ytab, pc, par, sv, ps), l < c.nl, hit(sv, ps, par, l as int),
        ch < par.k, rec_ok(recs_v@[ch as int]@, e as int, prow(sv, par, l as int), sv, par.sbase as int),
    ensures r matches Some((cost, slot)) ==> pre_qual(sv, ps, l as int, cost as int, slot as int),
    no_unwind
{
    let rec = &recs_v[ch as usize];
    let rl = rec.len();
    let base = e * 4;
    let skl = c.lsupp[l];
    let ghost r = prow(sv, par, l as int);
    // the line's supplier row (positional supplier keys); a key outside the table matches no entry
    if skl < par.sbase || skl - par.sbase >= c.ns as i64 {
        return None;
    }
    let srow = (skl - par.sbase) as u64;
    let mut j: usize = 0;
    while j < 4
        invariant
            j <= 4, base == 4 * e, base + 4 <= rl, rl == rec@.len(), rec@ == recs_v@[ch as int]@,
            scan_ok(*c, bits, wl, recs_v@, ytab, pc, par, sv, ps), l < c.nl, hit(sv, ps, par, l as int),
            ch < par.k, rec_ok(recs_v@[ch as int]@, e as int, r, sv, par.sbase as int),
            r == prow(sv, par, l as int), skl == lsk(sv)[l as int], srow as int == skl - par.sbase,
        decreases 4 - j,
    {
        let x = rec[base + j];
        if x >= 0 && (x as u64) >> 32u64 == srow {
            let xu = x as u64;
            proof {
                let q = 4 * r + j;
                assert(rec_entry_ok(rec@[4 * e + j], 4 * r + j, r, sv, par.sbase as int));
                let s = x as int / 0x1_0000_0000;
                lemma_fields(xu);
                assert(s == srow as int);
                assert(pk(sv)[r] as int == par.pbase + r);
                lemma_positional(pk(sv), par.pbase as int, lpk(sv)[l as int]);
                lemma_positional(sk(sv), par.sbase as int, lsk(sv)[l as int]);
                assert(pssk(sv)[q] == lsk(sv)[l as int]);
                assert(at2(pspk(sv), pssk(sv), lpk(sv)[l as int], lsk(sv)[l as int], q));
                lemma_key_row2(pspk(sv), pssk(sv), lpk(sv)[l as int], lsk(sv)[l as int]);
                let k = sn(sv)[s];
                lemma_key_row(nk(sv), k);
                if has_key(nk(sv), k) {
                    lemma_nrep(sv, key_row(nk(sv), k));
                }
                assert(0 <= slot_of(sv, k) < 256);
                lemma_unpack(x as int, s, psc(sv)[q] as int, slot_of(sv, k));
            }
            let slot = xu & 0xffu64;
            if slot >= NG as u64 {
                return None;
            }
            let cost = ((xu >> 8u64) & 0xff_ffffu64) as i64;
            proof {
                let s = lsk(sv)[l as int] - par.sbase;
                assert(has_key(nk(sv), sn(sv)[s]));
            }
            return Some((cost, slot as u32));
        }
        j = j + 1;
    }
    None
}

/// The dbgen row of order key `k` (`k = 32 * (i / 8) + i % 8` for the `i`-th order, from 1), a guess checked later.
fn order_guess(k: i64) -> (o: u64)
    no_unwind
{
    if k > 0 {
        let ku = (k - 1) as u64;
        ((ku >> 5u64) << 3u64) | (ku & 7u64)
    } else {
        u64::MAX
    }
}

/// The supply cost, group and order-row guess of every candidate; `false` when a candidate cannot be placed.
pub fn stage_match(c: &Cols, recs_v: &Vec<Vec<i64>>, par: ScanPar, b0: usize, cand: &Vec<u32>, n: usize,
    chk: &Vec<u32>, rix: &Vec<usize>, costb: &mut Vec<i64>, slotb: &mut Vec<u32>, orw: &mut Vec<u64>,
    Ghost(bits): Ghost<Seq<u64>>, Ghost(wl): Ghost<Seq<u64>>, Ghost(ytab): Ghost<Seq<u8>>, Ghost(pc): Ghost<Seq<u8>>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(b1): Ghost<int>) -> (ok: bool)
    requires
        scan_ok(*c, bits, wl, recs_v@, ytab, pc, par, sv, ps), b0 <= b1 <= c.nl,
        cands_ok(sv, ps, par, cand@, n as int, b0 as int, b1), cand@.len() == BLK, chk@.len() == BLK, rix@.len() == BLK,
        ranks_ok(sv, ps, par, recs_v@, cand@, n as int, b0 as int, chk@, rix@),
        old(costb)@.len() == BLK, old(slotb)@.len() == BLK, old(orw)@.len() == BLK,
    ensures
        final(costb)@.len() == BLK, final(slotb)@.len() == BLK, final(orw)@.len() == BLK,
        ok ==> matched_ok(sv, ps, cand@, n as int, b0 as int, final(costb)@, final(slotb)@),
    no_unwind
{
    let mut i: usize = 0;
    while i < n
        invariant
            scan_ok(*c, bits, wl, recs_v@, ytab, pc, par, sv, ps), b0 <= b1 <= c.nl, i <= n,
            cands_ok(sv, ps, par, cand@, n as int, b0 as int, b1), cand@.len() == BLK, chk@.len() == BLK, rix@.len() == BLK,
            ranks_ok(sv, ps, par, recs_v@, cand@, n as int, b0 as int, chk@, rix@),
            costb@.len() == BLK, slotb@.len() == BLK, orw@.len() == BLK,
            matched_ok(sv, ps, cand@, i as int, b0 as int, costb@, slotb@),
        decreases n - i,
    {
        let l = b0 + cand[i] as usize;
        match match_row(c, recs_v, par, l, chk[i], rix[i], Ghost(bits), Ghost(wl), Ghost(ytab), Ghost(pc), Ghost(sv), Ghost(ps)) {
            Some((cost, slot)) => {
                costb[i] = cost;
                slotb[i] = slot;
            },
            None => { return false; },
        }
        orw[i] = order_guess(c.lokey[l]);
        proof {
            assert forall|i2: int| 0 <= i2 < i + 1 implies #[trigger] pre_qual(sv, ps, b0 + cand@[i2], costb@[i2] as int, slotb@[i2] as int) by {}
        }
        i = i + 1;
    }
    true
}

// ------------------------------------------------------------------------------------------------ 5. accumulate

/// The row after candidate `i - 1` (the block start for `i == 0`), and the row of candidate `i` (the block end for
/// `i == n`): no row in between is a hit.
pub open spec fn gap_lo(cand: Seq<u32>, b0: int, i: int) -> int { if i == 0 { b0 } else { b0 + cand[i - 1] + 1 } }
pub open spec fn gap_hi(cand: Seq<u32>, n: int, b0: int, b1: int, i: int) -> int { if i < n { b0 + cand[i] } else { b1 } }

proof fn lemma_gap(sv: StoresView, ps: Seq<Literal>, par: ScanPar, cand: Seq<u32>, n: int, b0: int, b1: int, i: int)
    requires cands_ok(sv, ps, par, cand, n, b0, b1), 0 <= i <= n,
    ensures
        b0 <= gap_lo(cand, b0, i) <= gap_hi(cand, n, b0, b1, i) <= b1,
        forall|l: int| gap_lo(cand, b0, i) <= l < gap_hi(cand, n, b0, b1, i) ==> !#[trigger] hit(sv, ps, par, l),
{
    if i > 0 && i < n {
        assert(cand[i - 1] < cand[i]);
    }
    assert forall|l: int| gap_lo(cand, b0, i) <= l < gap_hi(cand, n, b0, b1, i) implies !#[trigger] hit(sv, ps, par, l) by {
        if hit(sv, ps, par, l) {
            let j = choose|j: int| 0 <= j < n && b0 + cand[j] == l;
            if j < i {
                if j < i - 1 { assert(cand[j] < cand[i - 1]); }
            } else {
                if j > i { assert(cand[i] < cand[j]); }
            }
        }
    }
}

/// Candidate row `l` with its match facts: its order (checked at the guess `o`), its year slot (year table), and its
/// amount; `None` when the order is not at the guess or the year is outside the table.
fn acc_row(c: &Cols, ytab: &Vec<u8>, l: usize, o: u64, cost: i64, slot: u32,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<(usize, i128)>)
    requires cols_ok(*c, sv), ytab_ok(ytab@), l < c.nl, pre_qual(sv, ps, l as int, cost as int, slot as int),
    ensures r matches Some((yi, v)) ==> yi < YW && line_qual(sv, ps, l as int) && grp(sv, l as int) == slot
        && yr(sv, l as int) == Y0 + yi && line_val(sv, l as int) == v && abs(v as int) < 0x20_0000_0000_0000_0000_0000_0000,
    no_unwind
{
    if o >= c.no as u64 {
        return None;
    }
    let ou = o as usize;
    let k = c.lokey[l];
    if c.okey[ou] != k {
        return None;
    }
    proof {
        assert(has_key(ok(sv), k));
        lemma_key_row(ok(sv), k);
        assert(l_ord(sv, l as int) == ou);
    }
    let d = c.odate[ou];
    if d < D0 || d >= D0 + ND as i32 {
        return None;
    }
    let yi = ytab[(d - D0) as usize];
    if yi == 255 {
        return None;
    }
    proof {
        assert(ytab@[(d - D0) as int] as int == yslot((D0 + (d - D0)) as i32));
        assert((D0 + (d - D0)) as i32 == d);
    }
    let price = c.lprice[l];
    let disc = c.ldisc[l];
    let qty = c.lqty[l];
    proof {
        assert(num15(lpr(sv)[l as int]) && num15(ldc(sv)[l as int]) && num15(lqt(sv)[l as int]));
        assert(num15(psc(sv)[l_ps(sv, l as int)]));
        lemma_key_row2(pspk(sv), pssk(sv), lpk(sv)[l as int], lsk(sv)[l as int]);
        assert(-1_000_000_000_000_000 < cost < 1_000_000_000_000_000);
        assert(-1_000_000_000_000_000 * 1_000_000_000_000_100 < price * (100 - disc) < 1_000_000_000_000_000 * 1_000_000_000_000_100)
            by (nonlinear_arith) requires -1_000_000_000_000_000 < price < 1_000_000_000_000_000,
                -1_000_000_000_000_000 < disc < 1_000_000_000_000_000;
        assert(-1_000_000_000_000_000 * 1_000_000_000_000_000 < cost * qty < 1_000_000_000_000_000 * 1_000_000_000_000_000)
            by (nonlinear_arith) requires -1_000_000_000_000_000 < cost < 1_000_000_000_000_000,
                -1_000_000_000_000_000 < qty < 1_000_000_000_000_000;
    }
    let v: i128 = price * (100 - disc) - (cost as i128) * qty;
    Some((yi as usize, v))
}

/// The table after the candidates of block `b0..b1`: `false` when a candidate cannot be placed or the absolute
/// amount leaves `i128`.
pub fn stage_acc(c: &Cols, ytab: &Vec<u8>, b0: usize, cand: &Vec<u32>, n: usize, costb: &Vec<i64>, slotb: &Vec<u32>,
    orw: &Vec<u64>, acc: &mut Vec<i128>, cnt: &mut Vec<u64>, mass: &mut u128,
    Ghost(bits): Ghost<Seq<u64>>, Ghost(wl): Ghost<Seq<u64>>, Ghost(recs): Ghost<Seq<Vec<i64>>>, Ghost(pc): Ghost<Seq<u8>>,
    Ghost(par): Ghost<ScanPar>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>, Ghost(b1): Ghost<int>)
    -> (ok: bool)
    requires
        scan_ok(*c, bits, wl, recs, ytab@, pc, par, sv, ps), 0 <= lo <= b0 <= b1 <= c.nl,
        cands_ok(sv, ps, par, cand@, n as int, b0 as int, b1), cand@.len() == BLK,
        costb@.len() == BLK, slotb@.len() == BLK, orw@.len() == BLK,
        matched_ok(sv, ps, cand@, n as int, b0 as int, costb@, slotb@),
        table_ok(old(acc)@, old(cnt)@, *old(mass), sv, ps, lo, b0 as int),
    ensures ok ==> table_ok(final(acc)@, final(cnt)@, *final(mass), sv, ps, lo, b1),
    no_unwind
{
    let mut i: usize = 0;
    while i < n
        invariant
            scan_ok(*c, bits, wl, recs, ytab@, pc, par, sv, ps), 0 <= lo <= b0 <= b1 <= c.nl, i <= n,
            cands_ok(sv, ps, par, cand@, n as int, b0 as int, b1), cand@.len() == BLK,
            costb@.len() == BLK, slotb@.len() == BLK, orw@.len() == BLK,
            matched_ok(sv, ps, cand@, n as int, b0 as int, costb@, slotb@),
            table_ok(acc@, cnt@, *mass, sv, ps, lo, gap_lo(cand@, b0 as int, i as int)),
        decreases n - i,
    {
        let l = b0 + cand[i] as usize;
        proof {
            lemma_gap(sv, ps, par, cand@, n as int, b0 as int, b1, i as int);
            lemma_skip(*c, bits, wl, recs, ytab@, pc, par, sv, ps, acc@, cnt@, *mass, lo, gap_lo(cand@, b0 as int, i as int), l as int);
            assert(pre_qual(sv, ps, b0 + cand@[i as int], costb@[i as int] as int, slotb@[i as int] as int));
        }
        let slot = slotb[i];
        match acc_row(c, ytab, l, orw[i], costb[i], slot, Ghost(sv), Ghost(ps)) {
            None => { return false; },
            Some((yi, v)) => {
                let av: u128 = if v < 0 { (0 - v) as u128 } else { v as u128 };
                let m2 = *mass + av;
                if m2 > i128::MAX as u128 {
                    return false;
                }
                let ix = slot as usize * 255 + yi;
                proof {
                    lemma_slot(slot as int, yi as int);
                    let (a, y) = (slot as int, Y0 + yi);
                    assert(acc@[ix as int] as int == tsum(sv, ps, a, y, 1, lo, l as int));
                    lemma_tsum_bounds(sv, ps, a, y, lo, l as int);
                    lemma_count_le(sv, ps, a, y, lo, l as int);
                }
                let ghost acc0 = acc@;
                let ghost cnt0 = cnt@;
                let ghost mass0 = *mass;
                acc[ix] = acc[ix] + v;
                cnt[ix] = cnt[ix] + 1;
                *mass = m2;
                proof {
                    lemma_add_row(acc0, cnt0, mass0, sv, ps, lo, l as int, slot as int, yi as int, v as int, acc@, cnt@, *mass);
                    assert(gap_lo(cand@, b0 as int, i + 1) == l + 1);
                }
            },
        }
        i = i + 1;
    }
    proof {
        lemma_gap(sv, ps, par, cand@, n as int, b0 as int, b1, n as int);
        lemma_skip(*c, bits, wl, recs, ytab@, pc, par, sv, ps, acc@, cnt@, *mass, lo, gap_lo(cand@, b0 as int, n as int), b1);
    }
    true
}

} // verus!
