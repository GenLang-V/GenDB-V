//! The lineitem scan of one row range (`scan_range`, run by `ScanTask`), in blocks of as many rows as its candidate
//! buffers hold (at most `BLOCK`):
//! 1. `select`: per 64-row word a branch-free probe mask (`probe64`): `l_partkey` with both of its Bloom filter bits
//!    set (`chit`); its set bits in order (`common::tz`) list the block's candidates in `sel` (offsets from the block
//!    start): `range_filter(b, e, chit)` (`common::selection`);
//! 2. `gather::gather_staged`: over the candidate list, stage by stage, the branch code of each candidate's key from
//!    the key map (0 for a key without a qualifying part), the quantity windows, then the ship instruction and mode;
//!    the survivors' volumes are added to the accumulator.
//! A row whose part satisfies some branch (`lhit`) is a candidate, so the rows not listed contribute nothing
//! (`lemma_tlist_cands`).
//!
//! The accumulator (`Acc`) holds the exact count and, while the absolute volume mass stays below `2^127`
//! (`MASS_CAP`), the exact sum; beyond it the mass sticks at `MASS_CAP` (the SUM leaves `i128`: the statement is
//! outside its capacity domain). `acc_ok(a, t)` relates it to the totals `t` it stands for.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::numeric::abs;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::bind::*;
use crate::agent::keymap::*;
use crate::agent::common::key_tags::*;
use crate::agent::common::bits::*;
use crate::agent::common::tz::{tz64, tz_table_array};
use crate::agent::common::selection::*;
use crate::agent::common::text_eq::*;

verus! {

/// The most rows per block of `scan_range` (offsets in a block fit `u32`): the length of the calling thread's
/// candidate buffers. Large blocks keep many candidates in flight in each gather stage.
pub const BLOCK: usize = 65536;

/// The length of a parallel scan task's candidate buffers (rows per block): the calling thread allocates (and zeroes)
/// the buffers of every task before the tasks start, so they are kept small.
pub const TASK_BLOCK: usize = 8192;

/// `2^127 = i128::MAX + 1`: the saturation value of the absolute mass.
pub const MASS_CAP: u128 = 0x8000_0000_0000_0000_0000_0000_0000_0000;

// ------------------------------------------------------------------------------------------------ inputs

/// Everything a scan task reads.
#[derive(Clone, Copy)]
pub struct ScanCols {
    pub line: LineCols,
}

/// The scan's inputs: the stored columns, the model's facts, the bound parameters and the key map.
pub open spec fn scan_inputs_ok(c: ScanCols, x: Bind, km: KeyMap, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& line_cols_ok(c.line, sv)
    &&& model_ok(sv)
    &&& bind_ok(x, ps)
    &&& keymap_ok(km, sv, ps)
}

// ------------------------------------------------------------------------------------------------ row facts

/// Lineitem row `l`'s part satisfies branch `k`.
pub open spec fn lb(sv: StoresView, ps: Seq<Literal>, k: int, l: int) -> bool {
    has_part(sv, l) && pcond(sv, ps, k, part_of(sv, l))
}

/// Lineitem row `l`'s part satisfies some branch.
pub open spec fn lhit(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> bool {
    |l: int| lb(sv, ps, 0, l) || lb(sv, ps, 1, l) || lb(sv, ps, 2, l)
}

/// Qualification from the branch bits of the row's part.
pub proof fn lemma_qual_lb(sv: StoresView, ps: Seq<Literal>, l: int)
    ensures qual(sv, ps, l) == (((lb(sv, ps, 0, l) && qcond(sv, ps, 0, l)) || (lb(sv, ps, 1, l) && qcond(sv, ps, 1, l))
        || (lb(sv, ps, 2, l) && qcond(sv, ps, 2, l))) && ship_ok(sv, l)),
{
}

/// The key bit of a lineitem row's part key is the branch bit of its part (the part key is a primary key).
pub proof fn lemma_kbit_part(sv: StoresView, ps: Seq<Literal>, k: int, l: int)
    requires keys_unique(p_key(sv)), 0 <= l < n_l(sv),
    ensures kbit(sv, ps, k, l_pkey(sv)[l] as int) == lb(sv, ps, k, l),
{
    if kbit(sv, ps, k, l_pkey(sv)[l] as int) {
        let a = choose|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] as int == l_pkey(sv)[l] as int && pcond(sv, ps, k, a);
        lemma_part_is(sv, l, a);
    }
    if lb(sv, ps, k, l) {
        lemma_part_of(sv, l);
        let a = part_of(sv, l);
        assert(p_key(sv)[a] as int == l_pkey(sv)[l] as int);
    }
}

/// Row `l` is a candidate: both filter bits of its part key are set.
pub open spec fn chit(sv: StoresView, km: KeyMap) -> spec_fn(int) -> bool {
    |l: int| hhit(km.cb@, l_pkey(sv)[l])
}

/// A row whose part satisfies some branch is a candidate; its key has a branch bit exactly when its part does.
pub proof fn lemma_probe(sv: StoresView, ps: Seq<Literal>, km: KeyMap, l: int)
    requires keymap_ok(km, sv, ps), model_ok(sv), 0 <= l < n_l(sv),
    ensures
        qkey(sv, ps, l_pkey(sv)[l]) == (lhit(sv, ps))(l),
        forall|k: int| 0 <= k < 3 ==> #[trigger] kbit(sv, ps, k, l_pkey(sv)[l] as int) == lb(sv, ps, k, l),
        (lhit(sv, ps))(l) ==> (chit(sv, km))(l),
{
    lemma_kbit_part(sv, ps, 0, l);
    lemma_kbit_part(sv, ps, 1, l);
    lemma_kbit_part(sv, ps, 2, l);
    assert forall|k: int| 0 <= k < 3 implies #[trigger] kbit(sv, ps, k, l_pkey(sv)[l] as int) == lb(sv, ps, k, l) by {
        lemma_kbit_part(sv, ps, k, l);
    }
    if qkey(sv, ps, l_pkey(sv)[l]) {
        assert(hhit(km.cb@, l_pkey(sv)[l]));
    }
}

// ------------------------------------------------------------------------------------------------ totals of row lists

/// The totals of the rows listed in `s`.
pub open spec fn tlist(sv: StoresView, ps: Seq<Literal>, s: Seq<int>) -> Tot
    decreases s.len(),
{
    if s.len() == 0 { tot_zero() } else { tot_plus(tlist(sv, ps, s.drop_last()), tot1(sv, ps, s.last())) }
}

/// One more listed row.
pub proof fn lemma_tlist_push(sv: StoresView, ps: Seq<Literal>, s: Seq<int>, x: int)
    ensures tlist(sv, ps, s.push(x)) == tot_plus(tlist(sv, ps, s), tot1(sv, ps, x)),
{
    assert(s.push(x).drop_last() =~= s);
}

/// The totals of the candidates of a range listed in order are the range's totals, for any candidate test `p` that
/// holds on every row whose part satisfies some branch.
pub proof fn lemma_tlist_cands(sv: StoresView, ps: Seq<Literal>, p: spec_fn(int) -> bool, b: int, e: int)
    requires b <= e, forall|l: int| b <= l < e && (#[trigger] (lhit(sv, ps))(l)) ==> p(l),
    ensures tlist(sv, ps, range_filter(b, e, p)) == tot(sv, ps, b, e),
    decreases e - b,
{
    if e > b {
        lemma_tlist_cands(sv, ps, p, b, e - 1);
        lemma_tot_step(sv, ps, b, e - 1);
        let s = range_filter(b, e - 1, p);
        lemma_qual_lb(sv, ps, e - 1);
        if p(e - 1) {
            lemma_tlist_push(sv, ps, s, e - 1);
        } else {
            assert(!(lhit(sv, ps))(e - 1));
            assert(tot1(sv, ps, e - 1) == tot_zero());
        }
    } else {
        assert(range_filter(b, e, p) =~= Seq::<int>::empty());
    }
}

/// One row's contribution: at most one row, its mass bounding its sum.
pub proof fn lemma_tot1_bounds(sv: StoresView, ps: Seq<Literal>, l: int)
    ensures tot_sane(tot1(sv, ps, l)), 0 <= tot1(sv, ps, l).cnt <= 1,
{
}

/// A range without qualifying rows has zero totals.
pub proof fn lemma_tot_none(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int)
    requires lo <= hi, forall|l: int| lo <= l < hi ==> !#[trigger] qual(sv, ps, l),
    ensures tot(sv, ps, lo, hi) == tot_zero(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_tot_none(sv, ps, lo, hi - 1);
        lemma_tot_step(sv, ps, lo, hi - 1);
        assert(!qual(sv, ps, hi - 1));
    }
}

// ------------------------------------------------------------------------------------------------ the accumulator

/// Running totals (see the module header).
#[derive(Clone, Copy)]
pub struct Acc {
    pub cnt: u64,
    pub s_all: i128,
    pub mass: u128,
}

/// `a` stands for the totals `t`.
pub open spec fn acc_ok(a: Acc, t: Tot) -> bool {
    &&& tot_sane(t)
    &&& a.cnt as int == t.cnt
    &&& a.mass as int == if t.a_all < MASS_CAP as int { t.a_all } else { MASS_CAP as int }
    &&& t.a_all < MASS_CAP as int ==> a.s_all as int == t.s_all
}

/// The accumulator of no rows.
pub fn acc_new() -> (a: Acc)
    ensures acc_ok(a, tot_zero()),
    no_unwind
{
    Acc { cnt: 0, s_all: 0, mass: 0 }
}

/// Adds one qualifying row of volume `v`.
pub fn acc_add(acc: &mut Acc, v: i128, Ghost(t): Ghost<Tot>)
    requires acc_ok(*old(acc), t), v > i128::MIN, t.cnt < 0xffff_ffff_ffff_ffff,
    ensures acc_ok(*final(acc), tot_plus(t, Tot { cnt: 1, s_all: v as int, a_all: abs(v as int) })),
    no_unwind
{
    let a: u128 = if v < 0 { (-v) as u128 } else { v as u128 };
    if acc.mass >= MASS_CAP - a {
        acc.mass = MASS_CAP;
    } else {
        // Unsaturated: `|s + v| <= mass + |v| < 2^127`.
        acc.mass = acc.mass + a;
        acc.s_all = acc.s_all + v;
    }
    acc.cnt = acc.cnt + 1;
}

/// Merges the accumulators of two disjoint row sets.
pub fn acc_merge(x: Acc, y: Acc, Ghost(t1): Ghost<Tot>, Ghost(t2): Ghost<Tot>) -> (r: Acc)
    requires acc_ok(x, t1), acc_ok(y, t2), t1.cnt + t2.cnt <= 0xffff_ffff_ffff_ffff,
    ensures acc_ok(r, tot_plus(t1, t2)),
    no_unwind
{
    let cnt = x.cnt + y.cnt;
    if x.mass >= MASS_CAP - y.mass {
        Acc { cnt, s_all: 0, mass: MASS_CAP }
    } else {
        Acc { cnt, s_all: x.s_all + y.s_all, mass: x.mass + y.mass }
    }
}

/// `|vol| < 10^31` for every lineitem row (numeric(15,2) factors).
pub open spec fn vol_bound() -> int { 10_000_000_000_000_000_000_000_000_000_000 }

pub proof fn lemma_vol_bound(sv: StoresView, l: int)
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

// ------------------------------------------------------------------------------------------------ one row

/// The ship instruction and mode of row `l`.
pub fn ship_at(c: &LineCols, l: usize, Ghost(sv): Ghost<StoresView>) -> (b: bool)
    requires line_cols_ok(*c, sv), l < c.nl,
    ensures b == ship_ok(sv, l as int),
    no_unwind
{
    let ghost n = c.nl as int;
    let dip: [u8; 24] = [68, 69, 76, 73, 86, 69, 82, 32, 73, 78, 32, 80, 69, 82, 83, 79, 78, 0, 0, 0, 0, 0, 0, 0];
    let air: [u8; 24] = [65, 73, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let air_reg: [u8; 24] = [65, 73, 82, 32, 82, 69, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    proof {
        assert(lit_of(dip, 17) =~= dip_lit() && lit_of(air, 3) =~= air_lit() && lit_of(air_reg, 7) =~= air_reg_lit());
    }
    if !text_is_lit(c.instr.offs, c.instr.bytes, l, &dip, 17, Ghost(n)) {
        return false;
    }
    text_is_lit(c.mode.offs, c.mode.bytes, l, &air, 3, Ghost(n)) || text_is_lit(c.mode.offs, c.mode.bytes, l, &air_reg, 7, Ghost(n))
}

// ------------------------------------------------------------------------------------------------ selection

/// The filter probe of one key: 1 when both of its filter bits are set (branch-free; the word index has 16 bits,
/// so it is inside the filter).
#[inline(always)]
fn probe1(key: i64, cb: &Vec<u64>) -> (b: u64)
    requires cb@.len() == CB_WORDS,
    ensures b == (if hhit(cb@, key) { 1u64 } else { 0u64 }),
    no_unwind
{
    let x = kbits_exec(key);
    proof {
        lemma_hword(key);
        assert((x >> 6u64) & 65535u64 < 65536u64) by (bit_vector);
    }
    let w = cb[((x >> 6u64) & 65535u64) as usize];
    let b2 = hb2_exec(x, Ghost(key));
    let b = (w >> (x & 63u64)) & (w >> b2) & 1u64;
    proof {
        lemma_and_bits(w, x & 63u64, b2);
    }
    b
}

/// The two-bit test of the filter: `(w >> s1) & (w >> s2) & 1` is 1 exactly when both bits are set.
proof fn lemma_and_bits(w: u64, s1: u64, s2: u64)
    requires s1 < 64, s2 < 64,
    ensures ((w >> s1) & (w >> s2) & 1u64) == (if bit(w, s1) && bit(w, s2) { 1u64 } else { 0u64 }),
{
    assert((s1 < 64 && s2 < 64) ==> ((w >> s1) & (w >> s2) & 1u64)
        == (if (w >> s1) & 1u64 == 1u64 && (w >> s2) & 1u64 == 1u64 { 1u64 } else { 0u64 })) by (bit_vector);
}

/// The filter probes of 64 consecutive part keys: bit `u` is the probe of key `ch[u]` (branch-free; the slice
/// length is known, so the loop compiles to straight-line code).
fn probe64(ch: &[i64], cb: &Vec<u64>) -> (m: u64)
    requires ch@.len() == 64, cb@.len() == CB_WORDS,
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == hhit(cb@, ch@[u as int]),
    no_unwind
{
    // never taken: it tells the compiler the filter's length, so the loads below need no bounds branch
    if cb.len() != CB_WORDS {
        return 0;
    }
    let mut m: u64 = 0;
    let mut u: usize = 0;
    proof {
        assert forall|v: u64| v < 64 implies !#[trigger] bit(0u64, v) by { lemma_bit_zero(v); }
    }
    while u < 64
        invariant
            ch@.len() == 64, u <= 64, cb@.len() == CB_WORDS,
            forall|v: u64| v < 64 ==> #[trigger] bit(m, v) == (v < u && hhit(cb@, ch@[v as int])),
        decreases 64 - u,
    {
        let b = probe1(ch[u], cb);
        let ghost m0 = m;
        m = m | (b << (u as u64));
        proof {
            assert forall|v: u64| v < 64 implies #[trigger] bit(m, v) == (v < u + 1 && hhit(cb@, ch@[v as int])) by {
                lemma_bit_set(m0, b, u as u64, v);
            }
        }
        u = u + 1;
    }
    m
}

/// The candidate mask of the rows `w..we` (at most 64): bit `u` is `chit(w + u)`.
fn word_mask(c: &ScanCols, km: &KeyMap, w: usize, we: usize, Ghost(sv): Ghost<StoresView>) -> (m: u64)
    requires line_cols_ok(c.line, sv), km.cb@.len() == CB_WORDS, w < we <= c.line.nl, we - w <= 64,
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (u < we - w && (chit(sv, *km))(w + u)),
    no_unwind
{
    if we - w == 64 {
        let (_, tail) = c.line.pkey.split_at(w);
        let (ch, _) = tail.split_at(64);
        let m = probe64(ch, &km.cb);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (u < we - w && (chit(sv, *km))(w + u)) by {
                assert(ch@[u as int] == tail@[u as int]);
                assert(tail@[u as int] == l_pkey(sv)[w + u]);
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
                line_cols_ok(c.line, sv), km.cb@.len() == CB_WORDS, w <= j <= we <= c.line.nl, we - w <= 64,
                forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (u < j - w && (chit(sv, *km))(w + u)),
            decreases we - j,
        {
            let b = probe1(c.line.pkey[j], &km.cb);
            let t = (j - w) as u64;
            let ghost m0 = m;
            m = m | (b << t);
            proof {
                assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (u < j + 1 - w && (chit(sv, *km))(w + u)) by {
                    lemma_bit_set(m0, b, t, u);
                }
            }
            j = j + 1;
        }
        m
    }
}

/// The candidates of `[b, e)`, as offsets from `b` in `sel`.
fn select(c: &ScanCols, km: &KeyMap, table: &[u8; 64], b: usize, e: usize, sel: &mut Vec<u32>,
    Ghost(sv): Ghost<StoresView>) -> (k: usize)
    requires
        line_cols_ok(c.line, sv), km.cb@.len() == CB_WORDS, table@.len() == 64,
        b <= e <= c.line.nl, e - b <= old(sel)@.len(), old(sel)@.len() <= BLOCK,
    ensures
        final(sel)@.len() == old(sel)@.len(),
        sel_matches(final(sel)@, k as int, b as int, range_filter(b as int, e as int, chit(sv, *km))),
    no_unwind
{
    let ghost nb = sel@.len();
    let ghost p = chit(sv, *km);
    let mut k: usize = 0;
    let mut w = b;
    while w < e
        invariant
            line_cols_ok(c.line, sv), km.cb@.len() == CB_WORDS, table@.len() == 64,
            b <= w <= e <= c.line.nl, e - b <= nb, sel@.len() == nb, nb <= BLOCK,
            p == chit(sv, *km),
            sel_matches(sel@, k as int, b as int, range_filter(b as int, w as int, p)),
        decreases e - w,
    {
        let we = if e - w > 64 { w + 64 } else { e };
        let mut m = word_mask(c, km, w, we, Ghost(sv));
        let ghost mut q: int = 0;
        while m != 0
            invariant
                line_cols_ok(c.line, sv), km.cb@.len() == CB_WORDS, table@.len() == 64,
                b <= w < we <= e <= c.line.nl, we - w <= 64, e - b <= nb, sel@.len() == nb, nb <= BLOCK,
                p == chit(sv, *km),
                0 <= q <= we - w,
                forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (q <= u < we - w && p(w + u)),
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
                assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (t + 1 <= u < we - w && p(w + u)) by {
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

// ------------------------------------------------------------------------------------------------ gather

/// The branch code of `key` (0 for a key without a qualifying part): from the table, or (for more than `2^31`
/// keys) from the key list.
#[inline(always)]
pub fn key_code(km: &KeyMap, key: i64, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (tag: u8)
    requires keymap_ok(*km, sv, ps),
    ensures
        tag != 0u8 ==> tag == code(sv, ps, key),
        tag == 0u8 ==> !qkey(sv, ps, key),
    no_unwind
{
    if km.small {
        let h = hx_exec(key);
        let mm = km.mm;
        proof {
            lemma_thome(mm);
            assert((h >> 20u64) & mm <= mm) by (bit_vector);
        }
        let hm = ((h >> 20u64) & mm) as usize;
        proof { assert(hm as int == (thome(mm))(key)); }
        let tag = tags_get(&km.slots, km.n, key, hm, Ghost(km.m as int), Ghost(km.cap as int), Ghost(thome(km.mm)));
        proof {
            if tag != 0u8 {
                let i = choose|i: int| 0 <= i < km.slots@.len() && occ(km.slots@, i) && #[trigger] km.slots@[i] == (key, tag);
                assert(km.slots@[i].1 == code(sv, ps, km.slots@[i].0));
            }
        }
        tag
    } else {
        list_get(&km.keys, &km.codes, km.nk, key, Ghost(sv), Ghost(ps))
    }
}

// ------------------------------------------------------------------------------------------------ one range

/// The totals of the rows `[lo, hi)`.
pub fn scan_range(c: &ScanCols, x: &Bind, km: &KeyMap, lo: usize, hi: usize, sel: &mut Vec<u32>, sel2: &mut Vec<u32>,
    tags: &mut Vec<u8>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (acc: Acc)
    requires
        scan_inputs_ok(*c, *x, *km, sv, ps),
        lo <= hi <= c.line.nl, 1 <= old(sel)@.len() <= BLOCK, old(sel2)@.len() == old(sel)@.len(),
        old(tags)@.len() == old(sel)@.len(),
    ensures
        final(sel)@.len() == old(sel)@.len(), final(sel2)@.len() == old(sel)@.len(), final(tags)@.len() == old(sel)@.len(),
        acc_ok(acc, tot(sv, ps, lo as int, hi as int)),
    no_unwind
{
    let ghost p = chit(sv, *km);
    let nb = sel.len();
    let table = tz_table_array();
    let mut acc = acc_new();
    let mut b = lo;
    proof { lemma_tot_empty(sv, ps, lo as int); }
    while b < hi
        invariant
            scan_inputs_ok(*c, *x, *km, sv, ps), table@.len() == 64,
            lo <= b <= hi <= c.line.nl, sel@.len() == nb, sel2@.len() == nb, tags@.len() == nb, 1 <= nb <= BLOCK,
            p == chit(sv, *km),
            acc_ok(acc, tot(sv, ps, lo as int, b as int)),
        decreases hi - b,
    {
        let e = if hi - b > nb { b + nb } else { hi };
        let k = select(c, km, &table, b, e, sel, Ghost(sv));
        let ghost s = range_filter(b as int, e as int, p);
        proof {
            lemma_range_filter_bounds(b as int, e as int, p);
            assert forall|i: int| 0 <= i < s.len() implies 0 <= #[trigger] s[i] < c.line.nl by {}
            assert(crate::agent::gather::rows_in(s, c.line.nl as int));
            lemma_tot_bounds(sv, ps, lo as int, b as int);
            lemma_rf_len(b as int, e as int, p);
            assert forall|l: int| b <= l < e && (#[trigger] (lhit(sv, ps))(l)) implies p(l) by {
                lemma_probe(sv, ps, *km, l);
            }
            lemma_tlist_cands(sv, ps, p, b as int, e as int);
            lemma_tot_split(sv, ps, lo as int, b as int, e as int);
        }
        crate::agent::gather::gather_staged(c, x, km, b, k, sel, sel2, tags, &mut acc, Ghost(sv), Ghost(ps), Ghost(s),
            Ghost(tot(sv, ps, lo as int, b as int)));
        b = e;
    }
    acc
}

// ------------------------------------------------------------------------------------------------ the task

/// One scan task: the rows `lo..hi`.
pub struct ScanTask {
    pub cols: ScanCols,
    pub bind: Bind,
    pub km: Arc<KeyMap>,
    pub lo: usize,
    pub hi: usize,
    pub sel: Vec<u32>,
    pub sel2: Vec<u32>,
    pub tags: Vec<u8>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

impl WorkerTask for ScanTask {
    type Output = Acc;

    open spec fn pre(&self) -> bool {
        &&& scan_inputs_ok(self.cols, self.bind, *self.km, self.sv@, self.ps@)
        &&& self.lo <= self.hi <= self.cols.line.nl
        &&& 1 <= self.sel@.len() <= BLOCK && self.sel2@.len() == self.sel@.len() && self.tags@.len() == self.sel@.len()
    }

    open spec fn post(&self, out: Acc) -> bool {
        acc_ok(out, tot(self.sv@, self.ps@, self.lo as int, self.hi as int))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Acc) {
        let ScanTask { cols, bind, km, lo, hi, sel, sel2, tags, sv, ps } = self;
        let mut sel = sel;
        let mut sel2 = sel2;
        let mut tags = tags;
        scan_range(&cols, &bind, &*km, lo, hi, &mut sel, &mut sel2, &mut tags, sv, ps)
    }
}

} // verus!
