//! The lineitem kernel: one task per range of stored lineitem rows (`ScanTask`), in blocks of `BLOCK` rows. For a
//! block it (1) lists the rows whose part matches: from the row bitmap of the current destination chunk (`rowbm`,
//! filled from the directory shuffle, with every row's payload at its rank) when it has one, else branch-free by the
//! filter bit of each row's part; then (2) finds for each listed row its partsupp cost (the per-range compact tables
//! of `build`, through the row's payload or its part's rank, or partsupp itself) and its supplier's nation row, then
//! (3) its order year: one year for the whole stretch of the block's lineitem group when the orders of the stretch's
//! end rows (`range_year`) lie in orders groups of one known year, else a cursor along the co-clustered orders; and
//! adds `l_extendedprice * (100 - l_discount) - ps_supplycost * l_quantity` (scale 4) to the cell (year slot, nation
//! row) (`cells`). A task stops early at a row that needs a year slot beyond `ycap` (the caller runs the rest as
//! another task) or that takes a cell's absolute sum beyond `i128::MAX` (`aovf`, Capacity).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::numeric::{abs, pow10};
use crate::link::expr::i128_max;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use super::model::*;
use super::cols::*;
use super::qspec::*;
use super::year::*;
use super::lookups::*;
use super::cells::*;
use super::common::popcnt::{cnt_below, count_below};
use super::common::grp::grp;
use super::rowbm::{bm_ok, chunk_rows, chunk_pay_ok, pl_at, fill_chunk, scatter_chunk, collect_bm};
use super::shuffle::{ShufOut, PA, pay_ok, res_ok, CH};
use super::common::bmrank::*;
use super::common::bitlist::wbit;
use super::build::BuildOut;
use super::common::grp::{Div, div_ok};

verus! {

/// Year slots per task (when the cells fit).
pub const YEARS: usize = 8;
/// Rows per block.
pub const BLOCK: usize = 2048;
/// No partsupp cost.
pub const NO_COST: i64 = -0x8000_0000_0000_0000i64;
/// Entries per matching part in the compact partsupp table.
pub const SLOTS: usize = 4;
/// An unused entry.
pub const EMPTY: u64 = 0xffff_ffff_ffff_ffffu64;
/// No known year of an orders group.
pub const NO_YEAR: i64 = -0x8000_0000_0000_0000i64;

/// `gyear[g]` is the order year of every order of orders group `g` (`NO_YEAR`: unknown).
pub open spec fn gyear_ok(gyear: Seq<i64>, m: M) -> bool {
    &&& gyear.len() == m.o_nb
    &&& forall|q: int| 0 <= q < m.o_n && #[trigger] gyear[q / m.o_bs] != NO_YEAR ==> year_of(odate(m, q)) == gyear[q / m.o_bs]
}

// ------------------------------------------------------------------------------------------------ prepared tables

/// Bit `c % 64` of word `c / 64`.
pub open spec fn bit_of(words: Seq<u64>, c: int) -> bool {
    (words[c / 64] >> ((c % 64) as u64)) & 1u64 == 1u64
}

/// The part filter bits: bit `c` is set exactly when part row `c` matches.
pub open spec fn bits_ok(bits: Seq<u64>, m: M, p: QP) -> bool {
    &&& bits.len() * 64 >= m.p_n
    &&& forall|c: int| 0 <= c < m.p_n ==> #[trigger] bit_of(bits, c) == pmatch(m, p, c)
}

/// The rank of matching part row `c`: matching parts before its word, then before it in its word.
pub open spec fn rank_of(bits: Seq<u64>, wpre: Seq<u32>, c: int) -> int {
    wpre[c / 64] as int + cnt_below(bits[c / 64], c % 64)
}

/// The nation tag of an entry: no supplier of key `sk` or no nation of its supplier.
pub const NO_TAG: u64 = 255;

/// The nation tag of supplier key `sk`: the nation row of its supplier, or `NO_TAG` when there is no such supplier
/// or nation.
pub open spec fn ntag(m: M, sk: int) -> int {
    let s = spos(m, sk);
    if s < m.s_n && sn(m, s) < m.n_n { sn(m, s) } else { NO_TAG as int }
}

/// A packed `(ps_suppkey, nation tag of ps_suppkey, ps_supplycost)` entry: bits 40.., 32..40 and ..32.
pub open spec fn pack(m: M, skv: int, cost: int) -> int {
    skv * 0x100_0000_0000 + ntag(m, skv) * 0x1_0000_0000 + cost
}

/// Partsupp row `t` packs: its supplier key, nation tag and cost fit the entry fields (fewer than `NO_TAG` nation
/// rows, so a nation row is never the tag `NO_TAG`).
pub open spec fn packable(m: M, t: int) -> bool {
    0 <= tsk(m, t) < 0xff_ffff && 0 <= tcost(m, t) <= 0xffff_ffff && m.n_n < NO_TAG
}

/// Entry `e` is unused or packs a partsupp row of part key `pk`.
pub open spec fn slot_ok(m: M, pk: int, e: u64) -> bool {
    e == EMPTY || exists|t: int| 0 <= t < m.t_n && tpk(m, t) == pk && packable(m, t) && #[trigger] pack(m, tsk(m, t), tcost(m, t)) == e as int
}

/// The entries of rank `r` list every partsupp row of part key `pk`.
pub open spec fn slots_cover(m: M, ents: Seq<u64>, r: int, pk: int) -> bool {
    &&& forall|i: int| 0 <= i < SLOTS ==> #[trigger] slot_ok(m, pk, ents[r * SLOTS as int + i])
    &&& forall|t: int| 0 <= t < m.t_n && #[trigger] tpk(m, t) == pk ==>
            packable(m, t) && exists|i: int| 0 <= i < SLOTS && #[trigger] ents[r * SLOTS as int + i] as int == pack(m, tsk(m, t), tcost(m, t))
}

/// Matching part row `c`'s entries: in the table of its range `c / per`, at its rank minus the range's first rank.
pub open spec fn ents_at(bits: Seq<u64>, wpre: Seq<u32>, tabs: Seq<BuildOut>, k0s: Seq<u64>, per: int, m: M, c: int) -> bool {
    let tb = c / per;
    let r = rank_of(bits, wpre, c) - k0s[tb] as int;
    &&& 0 <= tb < tabs.len()
    &&& 0 <= r
    &&& (r + 1) * SLOTS as int <= tabs[tb].ents@.len()
    &&& tabs[tb].ents@.len() <= usize::MAX
    &&& slots_cover(m, tabs[tb].ents@, r, pkey(m, c))
}

/// The compact partsupp table: every matching part's entries in its range's table.
pub open spec fn ents_ok(bits: Seq<u64>, wpre: Seq<u32>, tabs: Seq<BuildOut>, k0s: Seq<u64>, per: int, m: M) -> bool {
    &&& wpre.len() * 64 >= m.p_n
    &&& per >= 1
    &&& k0s.len() == tabs.len()
    &&& forall|c: int| 0 <= c < m.p_n && #[trigger] bit_of(bits, c) ==> ents_at(bits, wpre, tabs, k0s, per, m, c)
}

/// The fields of a packed entry.
pub proof fn lemma_unpack(skv: u64, nt: u64, cost: u64)
    requires skv < 0xff_ffff, nt < 256, cost <= 0xffff_ffff,
    ensures
        ((skv << 40u64) | (nt << 32u64) | cost) as int == skv * 0x100_0000_0000 + nt * 0x1_0000_0000 + cost,
        ((skv << 40u64) | (nt << 32u64) | cost) >> 40u64 == skv,
        (((skv << 40u64) | (nt << 32u64) | cost) >> 32u64) & 0xffu64 == nt,
        ((skv << 40u64) | (nt << 32u64) | cost) & 0xffff_ffffu64 == cost,
        ((skv << 40u64) | (nt << 32u64) | cost) != EMPTY,
{
    assert(((skv << 40u64) | (nt << 32u64) | cost) == skv * 0x100_0000_0000u64 + nt * 0x1_0000_0000u64 + cost) by (bit_vector)
        requires skv < 0xff_ffffu64, nt < 256u64, cost <= 0xffff_ffffu64;
    assert(((skv << 40u64) | (nt << 32u64) | cost) >> 40u64 == skv) by (bit_vector)
        requires skv < 0xff_ffffu64, nt < 256u64, cost <= 0xffff_ffffu64;
    assert((((skv << 40u64) | (nt << 32u64) | cost) >> 32u64) & 0xffu64 == nt) by (bit_vector)
        requires skv < 0xff_ffffu64, nt < 256u64, cost <= 0xffff_ffffu64;
    assert(((skv << 40u64) | (nt << 32u64) | cost) & 0xffff_ffffu64 == cost) by (bit_vector)
        requires skv < 0xff_ffffu64, nt < 256u64, cost <= 0xffff_ffffu64;
    assert(((skv << 40u64) | (nt << 32u64) | cost) != 0xffff_ffff_ffff_ffffu64) by (bit_vector)
        requires skv < 0xff_ffffu64, nt < 256u64, cost <= 0xffff_ffffu64;
}

/// A packed entry's fields are its supplier key, nation tag and cost.
proof fn lemma_pack_fields(e: u64, skv: int, nt: int, cost: int)
    requires 0 <= skv < 0xff_ffff, 0 <= nt < 256, 0 <= cost <= 0xffff_ffff,
        e as int == skv * 0x100_0000_0000 + nt * 0x1_0000_0000 + cost,
    ensures (e >> 40u64) as int == skv, ((e >> 32u64) & 0xffu64) as int == nt, (e & 0xffff_ffffu64) as int == cost, e != EMPTY,
{
    lemma_unpack(skv as u64, nt as u64, cost as u64);
}

/// The nation tag of a packable partsupp row is below 256; a tag other than `NO_TAG` is its supplier's nation row.
pub proof fn lemma_ntag(m: M, sk: int)
    requires model_ok(m), m.n_n < NO_TAG,
    ensures
        0 <= ntag(m, sk) < 256,
        ntag(m, sk) == NO_TAG ==> !(spos(m, sk) < m.s_n && sn(m, spos(m, sk)) < m.n_n),
        ntag(m, sk) != NO_TAG ==> spos(m, sk) < m.s_n && sn(m, spos(m, sk)) == ntag(m, sk) && ntag(m, sk) < m.n_n,
{
    lemma_npos(m, snk(m, spos(m, sk)), 0);
}

/// The partsupp cost of `(pkey(c), skv)` from the compact table (`NO_COST`: no such partsupp row), with the nation
/// tag of `skv` when it has one. The slot scan only selects the matching entry (no branch on the loaded entries, so
/// the table misses of consecutive rows overlap); the entry is unpacked once.
fn ps_cost_fast(ents: &Vec<u64>, r: usize, skv: i64, Ghost(m): Ghost<M>, Ghost(pk): Ghost<int>) -> (res: (i64, u64))
    requires
        model_ok(m),
        (r + 1) * SLOTS <= ents@.len() <= usize::MAX,
        slots_cover(m, ents@, r as int, pk),
    ensures
        res.0 == NO_COST ==> tpos(m, pk, skv as int) == m.t_n,
        res.0 != NO_COST ==> tpos(m, pk, skv as int) < m.t_n && res.0 as int == tcost(m, tpos(m, pk, skv as int)),
        res.0 != NO_COST ==> m.n_n < NO_TAG && res.1 as int == ntag(m, skv as int),
    no_unwind
{
    assert(SLOTS == 4);
    let base = r * SLOTS;
    let mut found: u64 = EMPTY;
    let mut i: usize = 0;
    while i < SLOTS
        invariant
            model_ok(m),
            (r + 1) * SLOTS <= ents@.len() <= usize::MAX,
            base == r * SLOTS,
            slots_cover(m, ents@, r as int, pk),
            i <= SLOTS,
            found == EMPTY ==> forall|k: int| 0 <= k < i ==> !(#[trigger] ents@[base + k] != EMPTY && (ents@[base + k] >> 40u64) as int == skv as int),
            found != EMPTY ==> slot_ok(m, pk, found) && (found >> 40u64) as int == skv as int,
        decreases SLOTS - i,
    {
        let e = ents[base + i];
        proof {
            assert((e >> 40u64) <= 0xff_ffffu64) by (bit_vector);
            assert(slot_ok(m, pk, ents@[r * SLOTS as int + i]));
        }
        let hit = e != EMPTY && (e >> 40u64) as i64 == skv;
        found = if hit { e } else { found };
        i = i + 1;
    }
    if found == EMPTY {
        proof {
            assert forall|t: int| 0 <= t < m.t_n implies !(#[trigger] tpk(m, t) == pk && tsk(m, t) == skv as int) by {
                if tpk(m, t) == pk && tsk(m, t) == skv as int {
                    let k = choose|k: int| 0 <= k < SLOTS && #[trigger] ents@[r * SLOTS as int + k] as int == pack(m, tsk(m, t), tcost(m, t));
                    lemma_ntag(m, tsk(m, t));
                    lemma_pack_fields(ents@[base + k], tsk(m, t), ntag(m, tsk(m, t)), tcost(m, t));
                }
            }
            lemma_tpos(m, pk, skv as int, 0);
        }
        (NO_COST, NO_TAG)
    } else {
        proof {
            let t = choose|t: int| 0 <= t < m.t_n && tpk(m, t) == pk && packable(m, t) && #[trigger] pack(m, tsk(m, t), tcost(m, t)) == found as int;
            lemma_ntag(m, tsk(m, t));
            lemma_pack_fields(found, tsk(m, t), ntag(m, tsk(m, t)), tcost(m, t));
            lemma_tpos(m, pk, skv as int, t);
        }
        ((found & 0xffff_ffffu64) as i64, (found >> 32u64) & 0xffu64)
    }
}

/// The partsupp cost of `(pkey(cc), skv)` for matching part row `cc` of rank `r`, from its range's table, with the
/// nation tag of `skv` when it has one.
fn tab_cost(tabs: &Vec<BuildOut>, k0s: &Vec<u64>, edv: Div, cc: usize, r: u64, skv: i64,
    Ghost(bits): Ghost<Seq<u64>>, Ghost(wpre): Ghost<Seq<u32>>, Ghost(m): Ghost<M>) -> (res: (i64, u64))
    requires
        model_ok(m),
        ents_ok(bits, wpre, tabs@, k0s@, edv.bs as int, m), div_ok(edv, edv.bs as int),
        cc < m.p_n, bit_of(bits, cc as int), r as int == rank_of(bits, wpre, cc as int),
    ensures
        res.0 == NO_COST ==> tpos(m, pkey(m, cc as int), skv as int) == m.t_n,
        res.0 != NO_COST ==> tpos(m, pkey(m, cc as int), skv as int) < m.t_n
            && res.0 as int == tcost(m, tpos(m, pkey(m, cc as int), skv as int)),
        res.0 != NO_COST ==> m.n_n < NO_TAG && res.1 as int == ntag(m, skv as int),
    no_unwind
{
    proof { assert(ents_at(bits, wpre, tabs@, k0s@, edv.bs as int, m, cc as int)); }
    let tb = grp(cc, edv);
    let k0 = k0s[tb];
    let local = (r - k0) as usize;
    let t = &tabs[tb];
    ps_cost_fast(&t.ents, local, skv, Ghost(m), Ghost(pkey(m, cc as int)))
}

// ------------------------------------------------------------------------------------------------ the task

/// The lineitem rows `[j_lo, j_hi)` of one task, with its preallocated cells, year slots and block buffers.
pub struct ScanTask {
    pub cols: Cols,
    pub divs: Divs,
    pub bits: Arc<Vec<u64>>,
    pub wpre: Arc<Vec<u32>>,
    pub ents: Arc<Vec<BuildOut>>,
    pub k0s: Arc<Vec<u64>>,
    pub edv: Div,
    pub ntab: Arc<Vec<u64>>,
    pub gyear: Arc<Vec<i64>>,
    pub ofast: bool,
    pub fast_ps: bool,
    pub n_small: bool,
    pub p_dense: bool,
    pub s_dense: bool,
    pub j_lo: usize,
    pub j_hi: usize,
    pub nn: usize,
    pub ycap: usize,
    pub cells: Vec<Cell>,
    pub years: Vec<i64>,
    pub qj: Vec<usize>,
    pub qc: Vec<i64>,
    pub qn: Vec<u64>,
    pub qs: Vec<i64>,
    pub qr: Vec<u64>,
    pub qa: Vec<i128>,
    pub use_bm: bool,
    pub res: Arc<Vec<ShufOut>>,
    pub bm: Vec<u64>,
    pub wp: Vec<u32>,
    pub pl: Vec<u32>,
    pub m: Ghost<M>,
    pub p: Ghost<QP>,
}

/// A task's result: the cells of the rows `[j_lo, stop)`; `stop < j_hi` when a row needed a year slot beyond
/// `ycap`, or (`aovf`) when row `stop` took the cell `(ovf_k, ovf_n)` beyond `i128::MAX`.
pub struct ScanOut {
    pub cells: Vec<Cell>,
    pub years: Vec<i64>,
    pub ny: usize,
    pub stop: usize,
    pub aovf: bool,
    pub ovf_k: usize,
    pub ovf_n: usize,
}

pub open spec fn scan_pre(t: ScanTask) -> bool {
    let m = t.m@;
    let p = t.p@;
    &&& look_ok(t.cols, t.divs, m)
    &&& m.p_n > 0
    &&& bits_ok((*t.bits)@, m, p)
    &&& t.fast_ps ==> ents_ok((*t.bits)@, (*t.wpre)@, (*t.ents)@, (*t.k0s)@, t.edv.bs as int, m) && div_ok(t.edv, t.edv.bs as int)
    &&& ntab_ok((*t.ntab)@, t.n_small, m)
    &&& t.ofast ==> m.cluster == 1 && ofacts_ok(m) && gyear_ok((*t.gyear)@, m)
    &&& t.p_dense ==> p_dense_ok(m)
    &&& t.s_dense ==> s_dense_ok(m)
    &&& t.j_lo <= t.j_hi <= m.l_n
    &&& t.nn == m.n_n
    &&& t.ycap >= 1
    &&& t.cells@ == Seq::new((t.ycap * t.nn) as nat, |i: int| zero_cell())
    &&& t.years@.len() == t.ycap
    &&& t.qj@.len() == BLOCK + 1
    &&& t.qc@.len() == BLOCK + 1
    &&& t.qn@.len() == BLOCK + 1
    &&& t.qs@.len() == BLOCK + 1
    &&& t.qr@.len() == BLOCK + 1
    &&& t.qa@.len() == BLOCK + 1
    &&& t.ycap * t.nn <= usize::MAX
    &&& t.use_bm ==> {
        &&& res_ok((*t.res)@, m, p, pa_task(t))
        &&& t.j_lo as int % CH as int == 0
        &&& (t.j_hi == m.l_n || t.j_hi as int % CH as int == 0)
        &&& m.l_n + CH <= usize::MAX
        &&& t.bm@.len() == CHW + 1 && t.wp@.len() == CHW + 2
    }
}

/// Words of a chunk's bitmap.
pub const CHW: usize = 4096;

/// The payload context of a task's tables.
pub open spec fn pa_task(t: ScanTask) -> PA {
    PA { bits: (*t.bits)@, wpre: (*t.wpre)@, k0s: (*t.k0s)@, per: t.edv.bs as int }
}

pub open spec fn scan_post(t: ScanTask, out: ScanOut) -> bool {
    let m = t.m@;
    let p = t.p@;
    &&& t.j_lo <= out.stop <= t.j_hi
    &&& out.years@.len() == t.ycap
    &&& out.cells@.len() == t.ycap * t.nn
    &&& out.ny <= t.ycap
    &&& !out.aovf ==> cells_inv(m, p, out.cells@, out.years@, out.ny as int, t.ycap as int, t.nn as int, t.j_lo as int, out.stop as int)
    &&& !out.aovf && out.stop < t.j_hi ==> out.stop > t.j_lo
    &&& out.aovf ==> {
        &&& out.stop < t.j_hi
        &&& out.ovf_k < out.ny && out.ovf_n < t.nn
        &&& dsum(abs_f(m, p, out.ovf_n as int, out.years@[out.ovf_k as int] as int), t.j_lo as int, out.stop + 1) > i128_max()
    }
}

/// A row below `n <= len * 64` has its word below `len`.
proof fn lemma_word(c: int, n: int, len: int)
    requires 0 <= c < n, n <= len * 64,
    ensures 0 <= c / 64 < len,
{
    assert(c / 64 < len) by (nonlinear_arith) requires 0 <= c < len * 64;
}

/// Part row `c`'s bit, read from its word.
proof fn lemma_bit(bits: Seq<u64>, c: int, w: u64)
    requires 0 <= c, c / 64 < bits.len(), w == bits[c / 64],
    ensures bit_of(bits, c) == ((w >> ((c % 64) as u64)) & 1u64 == 1u64),
{
}

/// The part of lineitem row `j` matches (a necessary condition of `jok`).
pub open spec fn pm(m: M, p: QP, j: int) -> bool {
    lc(m, j) < m.p_n && pmatch(m, p, lc(m, j))
}

/// `qj[0 .. nq]` are, in increasing order, the rows of `[blo, pos)` whose part matches.
pub open spec fn list_ok(m: M, p: QP, qj: Seq<usize>, nq: int, blo: int, pos: int) -> bool {
    &&& 0 <= nq <= pos - blo
    &&& forall|i: int| 0 <= i < nq ==> blo <= #[trigger] qj[i] < pos && pm(m, p, qj[i] as int)
    &&& forall|i: int, k: int| 0 <= i < k < nq ==> #[trigger] qj[i] < #[trigger] qj[k]
    &&& forall|j: int| blo <= j < pos && #[trigger] pm(m, p, j) ==> exists|i: int| 0 <= i < nq && qj[i] == j
}

/// What the gather step found for listed row `i`: its partsupp cost and, when it has one, its supplier's nation row.
pub open spec fn gather_ok(m: M, qj: Seq<usize>, qc: Seq<i64>, qn: Seq<u64>, nq: int) -> bool {
    forall|i: int| 0 <= i < nq ==> {
        let j = #[trigger] qj[i] as int;
        &&& (qc[i] != NO_COST && qn[i] == NO_NATION ==> !(ls(m, j) < m.s_n && jn(m, j) < m.n_n))
        &&& (qc[i] != NO_COST && qn[i] != NO_NATION ==> ls(m, j) < m.s_n && jn(m, j) == qn[i] as int && (qn[i] as int) < m.n_n)
        &&& (qc[i] == NO_COST ==> lt(m, j) == m.t_n)
        &&& (qc[i] != NO_COST ==> lt(m, j) < m.t_n && qc[i] as int == tcost(m, lt(m, j)))
    }
}

/// Rows between consecutive listed rows do not match.
proof fn lemma_gap(m: M, p: QP, qj: Seq<usize>, nq: int, blo: int, bhi: int, i: int, j: int)
    requires
        list_ok(m, p, qj, nq, blo, bhi),
        0 <= i <= nq,
        (if i == 0 { blo } else { qj[i - 1] + 1 }) <= j,
        j < (if i == nq { bhi } else { qj[i] as int }),
    ensures !pm(m, p, j),
{
    if pm(m, p, j) {
        let k = choose|k: int| 0 <= k < nq && qj[k] == j;
        if k < i {
            if k < i - 1 {
                assert(qj[k] < qj[i - 1]);
            }
        } else {
            if k > i {
                assert(qj[i] < qj[k]);
            }
        }
    }
}

/// The amount of a joining row from its decoded values.
proof fn lemma_amount(m: M, j: int, cost: int)
    requires
        model_ok(m), 0 <= j < m.l_n,
        lt(m, j) < m.t_n, cost == tcost(m, lt(m, j)),
    ensures
        jamt(m, j) == lprice(m, j) * (100 - ldisc(m, j)) - cost * lqty(m, j),
        abs(jamt(m, j)) < 0x10_0000_0000_0000_0000_0000_0000_0000,
        abs(lprice(m, j) * (100 - ldisc(m, j))) < 0x1_0000_0000_0000_0000_0000_0000_0000,
        abs(cost * lqty(m, j)) < 0x1_0000_0000_0000_0000_0000_0000_0000,
        -0x1_0000_0000_0000_0000 < 100 - ldisc(m, j) < 0x1_0000_0000_0000_0000,
{
    lemma_lvals(m, j);
    lemma_tvals(m, lt(m, j));
    assert(pow10(15) == 1000000000000000) by (compute);
    let (pr, ds, c, q) = (lprice(m, j), ldisc(m, j), cost, lqty(m, j));
    assert(abs(pr * (100 - ds) - c * q) < 0x10_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
        requires -1000000000000000 < pr < 1000000000000000, -1000000000000000 < ds < 1000000000000000,
            -1000000000000000 < c < 1000000000000000, -1000000000000000 < q < 1000000000000000;
    assert(abs(pr * (100 - ds)) < 0x1_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
        requires -1000000000000000 < pr < 1000000000000000, -1000000000000000 < ds < 1000000000000000;
    assert(abs(c * q) < 0x1_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
        requires -1000000000000000 < c < 1000000000000000, -1000000000000000 < q < 1000000000000000;
}

/// The accumulation state of a task: the cells and year slots, the order cursor (the key `ckey` of the last
/// looked-up order, its position `cq` and year slot `cslot`, `ycap` when it has no order) and the date cache (the
/// year slot `lslot` of the last date `ldate`).
pub struct Acc {
    pub cells: Vec<Cell>,
    pub years: Vec<i64>,
    pub ny: usize,
    pub ycap: usize,
    pub have: bool,
    pub ckey: i64,
    pub cq: usize,
    pub cslot: usize,
    pub have_date: bool,
    pub ldate: i64,
    pub lslot: usize,
    pub done: bool,
}

pub open spec fn cursor_ok(m: M, a: Acc) -> bool {
    a.have ==> {
        &&& (a.cslot < a.ycap ==> a.cslot < a.ny && opos(m, a.ckey as int) < m.o_n
                && a.years@[a.cslot as int] as int == year_of(odate(m, opos(m, a.ckey as int))))
        &&& (a.cslot >= a.ycap ==> opos(m, a.ckey as int) == m.o_n)
    }
}

pub open spec fn dcache_ok(a: Acc) -> bool {
    a.have_date ==> a.lslot < a.ny && a.years@[a.lslot as int] as int == year_of(a.ldate as int)
}

/// The state holds the cells of the rows `[lo, pos)`.
pub open spec fn acc_core(m: M, p: QP, a: Acc, nn: int, lo: int, pos: int) -> bool {
    &&& cells_inv(m, p, a.cells@, a.years@, a.ny as int, a.ycap as int, nn, lo, pos)
    &&& cursor_ok(m, a)
    &&& dcache_ok(a)
    &&& a.ycap * nn <= usize::MAX
    &&& a.ycap >= 1
}

pub open spec fn acc_ok(m: M, p: QP, a: Acc, nn: int, lo: int, pos: int) -> bool {
    &&& acc_core(m, p, a, nn, lo, pos)
    &&& a.ny > 0 ==> a.done
    &&& a.done ==> pos > lo
}

/// The year slot of a valid date: its slot in the list, a new slot, or `ycap` when the list is full and the year is
/// new (then nothing changed).
fn year_slot(a: &mut Acc, date: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(nn): Ghost<int>, Ghost(lo): Ghost<int>,
    Ghost(pos): Ghost<int>) -> (k: usize)
    requires acc_ok(m, p, *old(a), nn, lo, pos), crate::spec::datetime::date_valid(date as int),
    ensures
        k < final(a).ycap ==> acc_core(m, p, *final(a), nn, lo, pos) && k < final(a).ny
            && final(a).years@[k as int] as int == year_of(date as int) && final(a).done == old(a).done,
        k < final(a).ycap && final(a).ny > old(a).ny ==> k == old(a).ny,
        k < final(a).ycap && final(a).ny == old(a).ny ==> final(a).years@ == old(a).years@,
        k < final(a).ycap ==> final(a).cells@ == old(a).cells@ && final(a).have == old(a).have && final(a).ckey == old(a).ckey
            && final(a).cslot == old(a).cslot && final(a).cq == old(a).cq,
        k < final(a).ycap && final(a).ny > old(a).ny ==> final(a).ny == old(a).ny + 1,
        k >= final(a).ycap ==> *final(a) == *old(a) && old(a).ny == old(a).ycap,
        final(a).ycap == old(a).ycap,
    no_unwind
{
    if a.have_date && date == a.ldate {
        return a.lslot;
    }
    let y = year_exec(date);
    let ghost a0 = *a;
    let mut k: usize = 0;
    while k < a.ny && a.years[k] != y
        invariant
            acc_ok(m, p, *a, nn, lo, pos), *a == a0,
            k <= a.ny,
            forall|x: int| 0 <= x < k ==> a.years@[x] != y,
        decreases a.ny - k,
    {
        k = k + 1;
    }
    if k == a.ny {
        if a.ny == a.ycap {
            return a.ycap;
        }
        proof {
            lemma_cells_new_year(m, p, a.cells@, a.years@, a.ny as int, a.ycap as int, nn, lo, pos, y);
        }
        put(&mut a.years, a.ny, y);
        a.ny = a.ny + 1;
    }
    a.ldate = date;
    a.lslot = k;
    a.have_date = true;
    k
}

/// The year slot of the order of key `okv` (through the cursor): `Some(k)` with the order's year in slot `k`,
/// `Some(ycap)` when there is no such order, `None` when the list is full and the year is new.
fn order_slot(a: &mut Acc, c: &Cols, d: &Divs, okv: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(nn): Ghost<int>,
    Ghost(lo): Ghost<int>, Ghost(pos): Ghost<int>) -> (r: Option<usize>)
    requires acc_ok(m, p, *old(a), nn, lo, pos), look_ok(*c, *d, m),
    ensures
        r matches Some(k) ==> acc_core(m, p, *final(a), nn, lo, pos) && final(a).cells@ == old(a).cells@
            && final(a).done == old(a).done && (
            k < final(a).ycap && k < final(a).ny && opos(m, okv as int) < m.o_n
                && final(a).years@[k as int] as int == year_of(odate(m, opos(m, okv as int)))
            || k >= final(a).ycap && opos(m, okv as int) == m.o_n && final(a).years@ == old(a).years@ && final(a).ny == old(a).ny),
        r matches Some(k) ==> (final(a).ny > old(a).ny ==> final(a).ny == old(a).ny + 1 && k == old(a).ny),
        r matches Some(k) ==> (final(a).ny == old(a).ny ==> final(a).years@ == old(a).years@),
        r is None ==> old(a).ny == old(a).ycap && *final(a) == *old(a),
        final(a).ycap == old(a).ycap,
    no_unwind
{
    if a.have && okv == a.ckey {
        return Some(a.cslot);
    }
    match order_row(c, d, a.cq, okv, Ghost(m)) {
        Some(q) => {
            let date = get_odate(c, d, q, Ghost(m));
            proof { lemma_ovals(m, q as int); }
            let k = year_slot(a, date, Ghost(m), Ghost(p), Ghost(nn), Ghost(lo), Ghost(pos));
            if k >= a.ycap {
                return None;
            }
            a.have = true;
            a.ckey = okv;
            a.cq = q;
            a.cslot = k;
            Some(k)
        },
        None => {
            a.have = true;
            a.ckey = okv;
            a.cslot = a.ycap;
            Some(a.ycap)
        },
    }
}

/// Add joining row `j` (cost `cost`, nation row `n`, year slot `k`) to its cell; `false` when its absolute sum would
/// leave `i128` (then nothing changed).
fn add_row(a: &mut Acc, c: &Cols, d: &Divs, j: usize, cost: i64, n: u64, k: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>,
    nn: usize, Ghost(lo): Ghost<int>, pre: Option<i128>)
    -> (ok: bool)
    requires
        pre matches Some(x) ==> x as int == jamt(m, j as int),
        acc_core(m, p, *old(a), nn as int, lo, j as int),
        lo <= j,
        look_ok(*c, *d, m),
        j < m.l_n,
        jok(m, p, j as int),
        lt(m, j as int) < m.t_n, cost as int == tcost(m, lt(m, j as int)),
        n as int == jn(m, j as int), (n as int) < nn,
        k < old(a).ny, old(a).years@[k as int] as int == jyear(m, j as int),
    ensures
        ok ==> acc_ok(m, p, *final(a), nn as int, lo, j + 1) && final(a).ny == old(a).ny,
        ok ==> final(a).years@ == old(a).years@,
        !ok ==> *final(a) == *old(a)
            && dsum(abs_f(m, p, n as int, old(a).years@[k as int] as int), lo, j + 1) > i128_max(),
        final(a).ycap == old(a).ycap,
    no_unwind
{
    proof { lemma_amount(m, j as int, cost as int); }
    // the amount: precomputed by the gather step (`amounts`) or decoded here
    let amt: i128 = match pre {
        Some(x) => x,
        None => {
            let (qty, price, disc) = get_lnums(c, d, j, Ghost(m));
            (price as i128) * (100 - disc as i128) - (cost as i128) * (qty as i128)
        },
    };
    proof {
        lemma_cell_bound(nn as int, a.ycap as int, k as int, n as int);
        assert(k * nn <= k * nn + n);
    }
    let idx = k * nn + n as usize;
    let old_cell = a.cells[idx];
    let aa: u128 = if amt < 0 { (0 - amt) as u128 } else { amt as u128 };
    proof {
        assert(aa as int == abs(jamt(m, j as int)));
        assert(cell_is(m, p, a.cells@[k * nn + n as int], n as int, a.years@[k as int] as int, lo, j as int));
    }
    if old_cell.ab > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 - aa {
        proof {
            lemma_cells_overflow(m, p, a.cells@, a.years@, a.ny as int, a.ycap as int, nn as int, lo, j as int, k as int, n as int);
        }
        return false;
    }
    proof {
        lemma_dsum_bounds(m, p, a.cells@, a.years@, a.ny as int, nn as int, lo, j as int, k as int, n as int);
    }
    let x = Cell { cnt: old_cell.cnt + 1, sum: old_cell.sum + amt, ab: old_cell.ab + aa };
    proof {
        lemma_cells_add(m, p, a.cells@, a.years@, a.ny as int, a.ycap as int, nn as int, lo, j as int, k as int, n as int, x);
    }
    put(&mut a.cells, idx, x);
    a.done = true;
    true
}

/// What happened to a listed row.
pub enum Step {
    Done,
    Full,
    Overflow(usize, usize),
}

/// Process listed row `j` with its gathered cost and nation row: skip it (it does not join), add it, or stop
/// (`Full`: a new year needs a slot beyond `ycap`; `Overflow(k, n)`: its cell's absolute sum would leave `i128`).
fn step_row(a: &mut Acc, c: &Cols, d: &Divs, j: usize, cost: i64, n: u64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>,
    nn: usize, Ghost(lo): Ghost<int>, pre: Option<i128>) -> (r: Step)
    requires
        pre matches Some(x) ==> (cost != NO_COST ==> x as int == jamt(m, j as int)),
        acc_ok(m, p, *old(a), nn as int, lo, j as int),
        look_ok(*c, *d, m),
        lo <= j < m.l_n,
        nn == m.n_n,
        pm(m, p, j as int),
        cost != NO_COST && n == NO_NATION ==> !(ls(m, j as int) < m.s_n && jn(m, j as int) < m.n_n),
        cost != NO_COST && n != NO_NATION ==> ls(m, j as int) < m.s_n && jn(m, j as int) == n as int && (n as int) < m.n_n,
        cost == NO_COST ==> lt(m, j as int) == m.t_n,
        cost != NO_COST ==> lt(m, j as int) < m.t_n && cost as int == tcost(m, lt(m, j as int)),
    ensures
        r is Done ==> acc_ok(m, p, *final(a), nn as int, lo, j + 1),
        r is Full ==> acc_ok(m, p, *final(a), nn as int, lo, j as int) && j > lo,
        r matches Step::Overflow(k, n2) ==> k < final(a).ny && n2 < nn
            && dsum(abs_f(m, p, n2 as int, final(a).years@[k as int] as int), lo, j + 1) > i128_max(),
        final(a).years@.len() == final(a).ycap, final(a).cells@.len() == final(a).ycap * nn, final(a).ny <= final(a).ycap,
        final(a).ycap == old(a).ycap,
    no_unwind
{
    if cost == NO_COST || n == NO_NATION {
        proof {
            lemma_cells_skip(m, p, a.cells@, a.years@, a.ny as int, a.ycap as int, nn as int, lo, j as int);
        }
        return Step::Done;
    }
    let okv = get_lok(c, d, j, Ghost(m));
    match order_slot(a, c, d, okv, Ghost(m), Ghost(p), Ghost(nn as int), Ghost(lo), Ghost(j as int)) {
        None => Step::Full,
        Some(k) => {
            if k >= a.ycap {
                proof {
                    lemma_cells_skip(m, p, a.cells@, a.years@, a.ny as int, a.ycap as int, nn as int, lo, j as int);
                }
                return Step::Done;
            }
            proof { assert(jok(m, p, j as int)); }
            let ghost a1 = *a;
            if add_row(a, c, d, j, cost, n, k, Ghost(m), Ghost(p), nn, Ghost(lo), pre) {
                Step::Done
            } else {
                Step::Overflow(k, n as usize)
            }
        },
    }
}

/// Process listed row `j` whose order exists and has the year of slot `k`: skip it (it does not join), add it, or
/// stop on an absolute sum leaving `i128` (`Overflow`).
fn step_fixed(a: &mut Acc, c: &Cols, d: &Divs, j: usize, cost: i64, n: u64, k: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>,
    nn: usize, Ghost(lo): Ghost<int>, pre: Option<i128>) -> (r: Step)
    requires
        pre matches Some(x) ==> (cost != NO_COST ==> x as int == jamt(m, j as int)),
        acc_ok(m, p, *old(a), nn as int, lo, j as int),
        look_ok(*c, *d, m),
        lo <= j < m.l_n,
        nn == m.n_n,
        pm(m, p, j as int),
        cost != NO_COST && n == NO_NATION ==> !(ls(m, j as int) < m.s_n && jn(m, j as int) < m.n_n),
        cost != NO_COST && n != NO_NATION ==> ls(m, j as int) < m.s_n && jn(m, j as int) == n as int && (n as int) < m.n_n,
        cost == NO_COST ==> lt(m, j as int) == m.t_n,
        cost != NO_COST ==> lt(m, j as int) < m.t_n && cost as int == tcost(m, lt(m, j as int)),
        k < old(a).ny,
        lq(m, j as int) < m.o_n,
        old(a).years@[k as int] as int == jyear(m, j as int),
    ensures
        r is Done ==> acc_ok(m, p, *final(a), nn as int, lo, j + 1),
        !(r is Full),
        r matches Step::Overflow(k2, n2) ==> k2 < final(a).ny && n2 < nn
            && dsum(abs_f(m, p, n2 as int, final(a).years@[k2 as int] as int), lo, j + 1) > i128_max(),
        final(a).years@ == old(a).years@, final(a).ny == old(a).ny,
        final(a).years@.len() == final(a).ycap, final(a).cells@.len() == final(a).ycap * nn, final(a).ny <= final(a).ycap,
        final(a).ycap == old(a).ycap,
    no_unwind
{
    if cost == NO_COST || n == NO_NATION {
        proof {
            lemma_cells_skip(m, p, a.cells@, a.years@, a.ny as int, a.ycap as int, nn as int, lo, j as int);
        }
        return Step::Done;
    }
    proof { assert(jok(m, p, j as int)); }
    if add_row(a, c, d, j, cost, n, k, Ghost(m), Ghost(p), nn, Ghost(lo), pre) {
        Step::Done
    } else {
        Step::Overflow(k, n as usize)
    }
}

/// The year slot of year `y`, when the list has it.
fn slot_find(a: &Acc, y: i64) -> (r: Option<usize>)
    requires a.ny <= a.years@.len(),
    ensures r matches Some(k) ==> k < a.ny && a.years@[k as int] == y,
    no_unwind
{
    let mut k: usize = 0;
    while k < a.ny
        invariant k <= a.ny <= a.years@.len(),
        decreases a.ny - k,
    {
        if a.years[k] == y {
            return Some(k);
        }
        k = k + 1;
    }
    None
}



/// Every lineitem row of `[ja, jb]` has its order, of year `y`, when `cy` is `Some(y)`.
pub open spec fn year_cover(m: M, cy: Option<i64>, ja: int, jb: int) -> bool {
    match cy {
        Some(y) => forall|j: int| ja <= j <= jb ==> lq(m, j) < m.o_n && #[trigger] jyear(m, j) == y as int,
        None => true,
    }
}

/// The order year of every lineitem row of `[ja, jb]` when known: the orders of the end rows (`order_row`, from the
/// position `hint`), and one known year (`gyear`) for every orders group between them (with the co-clustering, the
/// order of every row between them lies between); the order position of `jb` as the next hint.
fn range_year(c: &Cols, d: &Divs, gyear: &Vec<i64>, ja: usize, jb: usize, hint: usize, Ghost(m): Ghost<M>)
    -> (r: (Option<i64>, usize))
    requires
        look_ok(*c, *d, m), m.cluster == 1, ofacts_ok(m), gyear_ok(gyear@, m),
        ja <= jb < m.l_n,
    ensures
        year_cover(m, r.0, ja as int, jb as int),
    no_unwind
{
    let k0 = get_lok(c, d, ja, Ghost(m));
    let k1 = get_lok(c, d, jb, Ghost(m));
    let q0 = match order_row(c, d, hint, k0, Ghost(m)) {
        Some(q) => q,
        None => { return (None, hint); },
    };
    let q1 = match order_row(c, d, q0, k1, Ghost(m)) {
        Some(q) => q,
        None => { return (None, q0); },
    };
    proof {
        lemma_block(q0 as int, m.o_bs, m.o_n, m.o_nb);
        lemma_block(q1 as int, m.o_bs, m.o_n, m.o_nb);
        assert(opos(m, lok(m, ja as int)) <= opos(m, lok(m, jb as int)));
        vstd::arithmetic::div_mod::lemma_div_is_ordered(q0 as int, q1 as int, m.o_bs);
    }
    let g0 = grp(q0, d.o);
    let g1 = grp(q1, d.o);
    let y = gyear[g0];
    if y == NO_YEAR {
        return (None, q1);
    }
    let mut g = g0;
    while g < g1
        invariant
            gyear_ok(gyear@, m), g0 <= g <= g1, (g1 as int) < m.o_nb,
            forall|h: int| g0 <= h <= g ==> #[trigger] gyear@[h] == y,
        decreases g1 - g,
    {
        if gyear[g + 1] != y {
            return (None, q1);
        }
        g = g + 1;
    }
    proof {
        assert forall|j: int| ja <= j <= jb implies lq(m, j) < m.o_n && #[trigger] jyear(m, j) == y as int by {
            assert(opos(m, lok(m, ja as int)) <= opos(m, lok(m, j)));
            assert(opos(m, lok(m, j)) <= opos(m, lok(m, jb as int)));
            let q = lq(m, j);
            assert(q0 <= q <= q1);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(q0 as int, q, m.o_bs);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(q, q1 as int, m.o_bs);
            assert(gyear@[q / m.o_bs] == y);
        }
    }
    (Some(y), q1)
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        scan_pre(*self)
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        scan_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.j_lo as u64, self.j_hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let ghost task = self;
        let ghost pa = pa_task(task);
        let ScanTask { cols, divs, bits, wpre, ents, k0s, edv, ntab, gyear, ofast, fast_ps, n_small, p_dense, s_dense, j_lo, j_hi, nn, ycap, cells, years,
            qj, qc, qn, qs, qr, qa, use_bm, res, bm, wp, pl, m: gm, p: gp } = self;
        let ghost m = gm@;
        let ghost p = gp@;
        let c = cols;
        let d = divs;
        let mut qj = qj;
        let mut qc = qc;
        let mut qn = qn;
        let mut qs = qs;
        let mut qr = qr;
        let mut qa = qa;
        let mut bm = bm;
        let mut wp = wp;
        let mut pl = pl;
        let mut a = Acc { cells, years, ny: 0, have: false, ckey: 0, cq: 0, ycap, cslot: ycap, have_date: false, ldate: 0, lslot: 0, done: false };
        proof {
            lemma_cells_start(m, p, a.years@, ycap as int, nn as int, j_lo as int);
            assert(a.cells@ =~= Seq::new((ycap * nn) as nat, |i: int| zero_cell()));
        }
        // stop: the row before which the task stopped (`j_hi` when it did not), with the overflow witness
        let mut stopped = false;
        let mut stop: usize = j_hi;
        let mut aovf = false;
        let mut ovf_k: usize = 0;
        let mut ovf_n: usize = 0;
        let mut hint: usize = 0;
        let mut have_c = false;
        let mut ca: usize = 0;
        let mut cb: usize = 0;
        let mut cy: Option<i64> = None;
        // the directory path's destination chunk state
        let mut cs = ChunkSt { bm, wp, pl, lo: j_lo, hi: j_lo, rpos: 0, pay: false };
        proof {
            if use_bm {
                reveal(chunk_inv);
                assert(chunk_inv(cs, m, p, pa, j_lo as int, j_hi as int, j_lo as int));
            }
        }
        let mut blo = j_lo;
        while blo < j_hi && !stopped
            invariant
                task.pre(),
                m == task.m@, p == task.p@, pa == pa_task(task), c == task.cols, d == task.divs,
                bits == task.bits, wpre == task.wpre, ents == task.ents, k0s == task.k0s, edv == task.edv, ntab == task.ntab,
                gyear == task.gyear, ofast == task.ofast,
                fast_ps == task.fast_ps, n_small == task.n_small, p_dense == task.p_dense, s_dense == task.s_dense,
                j_lo == task.j_lo, j_hi == task.j_hi, nn == task.nn, ycap == task.ycap, a.ycap == ycap,
                use_bm == task.use_bm, res == task.res,
                use_bm ==> res_ok((*res)@, m, p, pa),
                use_bm && !stopped ==> chunk_inv(cs, m, p, pa, j_lo as int, j_hi as int, blo as int),
                j_lo <= blo <= j_hi,
                have_c ==> year_cover(m, cy, ca as int, cb as int),
                qj@.len() == BLOCK + 1, qc@.len() == BLOCK + 1, qn@.len() == BLOCK + 1,
                qs@.len() == BLOCK + 1, qr@.len() == BLOCK + 1, qa@.len() == BLOCK + 1,
                a.years@.len() == ycap, a.cells@.len() == ycap * nn, a.ny <= ycap,
                !stopped ==> acc_ok(m, p, a, nn as int, j_lo as int, blo as int) && stop == j_hi,
                stopped && !aovf ==> acc_ok(m, p, a, nn as int, j_lo as int, stop as int) && j_lo < stop < j_hi,
                stopped && aovf ==> j_lo <= stop < j_hi && ovf_k < a.ny && ovf_n < nn
                    && dsum(abs_f(m, p, ovf_n as int, a.years@[ovf_k as int] as int), j_lo as int, stop + 1) > i128_max(),
                !stopped ==> !aovf,
            decreases j_hi - blo + if stopped { 0int } else { 1int },
        {
            let bhi = if j_hi - blo > BLOCK { blo + BLOCK } else { j_hi };
            let nq = block_rows(&c, &d, &bits, &wpre, &ents, &k0s, edv, &ntab, fast_ps, n_small, p_dense, s_dense, use_bm, &res, &mut cs,
                blo, bhi, j_hi, &mut qj, &mut qc, &mut qn, &mut qs, &mut qr, &mut qa, Ghost(m), Ghost(p), Ghost(pa), Ghost(j_lo as int));
            // one order year for the block's listed rows, when known: its slot
            let mut fixed: Option<usize> = None;
            if ofast && nq > 0 {
                if !(have_c && ca <= blo && bhi - 1 <= cb) {
                    // a new stretch: from this block to the end of its lineitem group (or of the task)
                    proof { lemma_block(blo as int, m.l_bs, m.l_n, m.l_nb); }
                    let g = grp(blo, d.l);
                    proof {
                        assert(g as int * (d.l.bs as int) <= blo) by (nonlinear_arith)
                            requires g == blo as int / d.l.bs as int, d.l.bs >= 1;
                        assert((g as int + 1) * (d.l.bs as int) <= blo + d.l.bs) by (nonlinear_arith)
                            requires g as int * (d.l.bs as int) <= blo;
                    }
                    let ge: u128 = (g as u128 + 1) * (d.l.bs as u128);
                    let end: usize = if ge < j_hi as u128 && ge > blo as u128 { ge as usize } else { j_hi };
                    let (yo, h2) = range_year(&c, &d, &gyear, blo, end - 1, hint, Ghost(m));
                    hint = h2;
                    have_c = true;
                    ca = blo;
                    cb = end - 1;
                    cy = yo;
                }
                if have_c && ca <= blo && bhi - 1 <= cb {
                    match cy {
                        Some(y) => {
                            fixed = slot_find(&a, y);
                            proof {
                                assert(year_cover(m, cy, ca as int, cb as int));
                                assert forall|x: int| 0 <= x < nq implies lq(m, #[trigger] qj@[x] as int) < m.o_n
                                    && jyear(m, qj@[x] as int) == y as int by {
                                    assert(blo <= qj@[x] < bhi);
                                    assert(jyear(m, qj@[x] as int) == y as int);
                                }
                            }
                        },
                        None => {},
                    }
                }
            }
            // order, year and accumulation of each listed row
            let mut i: usize = 0;
            let ghost mut pos: int = blo as int;
            while i < nq && !stopped
                invariant
                    have_c ==> year_cover(m, cy, ca as int, cb as int),
                    task.pre(),
                    m == task.m@, p == task.p@, c == task.cols, d == task.divs,
                    j_lo == task.j_lo, j_hi == task.j_hi, nn == task.nn, ycap == task.ycap, a.ycap == ycap,
                    pa == pa_task(task), use_bm == task.use_bm, res == task.res,
                    use_bm ==> res_ok((*res)@, m, p, pa) && chunk_inv(cs, m, p, pa, j_lo as int, j_hi as int, bhi as int),
                    j_lo <= blo <= bhi <= j_hi, bhi - blo <= BLOCK,
                    i <= nq <= BLOCK,
                    qj@.len() == BLOCK + 1, qc@.len() == BLOCK + 1, qn@.len() == BLOCK + 1,
                    list_ok(m, p, qj@, nq as int, blo as int, bhi as int),
                    gather_ok(m, qj@, qc@, qn@, nq as int),
                    qa@.len() == BLOCK + 1,
                    amts_ok(m, qj@, qc@, qa@, nq as int),
                    fixed matches Some(k) ==> k < a.ny && forall|x: int| 0 <= x < nq ==>
                        lq(m, #[trigger] qj@[x] as int) < m.o_n && jyear(m, qj@[x] as int) == a.years@[k as int] as int,
                    pos == if i == 0 { blo as int } else { qj@[i - 1] + 1 },
                    a.years@.len() == ycap, a.cells@.len() == ycap * nn, a.ny <= ycap,
                    !stopped ==> acc_ok(m, p, a, nn as int, j_lo as int, pos) && stop == j_hi,
                    stopped && !aovf ==> acc_ok(m, p, a, nn as int, j_lo as int, stop as int) && j_lo < stop < j_hi,
                    stopped && aovf ==> j_lo <= stop < j_hi && ovf_k < a.ny && ovf_n < nn
                        && dsum(abs_f(m, p, ovf_n as int, a.years@[ovf_k as int] as int), j_lo as int, stop + 1) > i128_max(),
                    !stopped ==> !aovf,
                decreases nq - i + if stopped { 0int } else { 1int },
            {
                let j = qj[i];
                proof {
                    assert forall|x: int| pos <= x < j implies !#[trigger] jok(m, p, x) by {
                        lemma_gap(m, p, qj@, nq as int, blo as int, bhi as int, i as int, x);
                    }
                    lemma_cells_skip_range(m, p, a.cells@, a.years@, a.ny as int, ycap as int, nn as int, j_lo as int, pos, j as int);
                    assert(pm(m, p, j as int));
                }
                let st = match fixed {
                    Some(k) => step_fixed(&mut a, &c, &d, j, qc[i], qn[i], k, Ghost(m), Ghost(p), nn, Ghost(j_lo as int), Some(qa[i])),
                    None => step_row(&mut a, &c, &d, j, qc[i], qn[i], Ghost(m), Ghost(p), nn, Ghost(j_lo as int), Some(qa[i])),
                };
                match st {
                    Step::Done => {
                        proof { pos = j + 1; }
                        i = i + 1;
                    },
                    Step::Full => {
                        stopped = true;
                        stop = j;
                    },
                    Step::Overflow(k, n) => {
                        stopped = true;
                        stop = j;
                        aovf = true;
                        ovf_k = k;
                        ovf_n = n;
                    },
                }
            }
            if !stopped {
                proof {
                    assert forall|x: int| pos <= x < bhi implies !#[trigger] jok(m, p, x) by {
                        lemma_gap(m, p, qj@, nq as int, blo as int, bhi as int, nq as int, x);
                    }
                    lemma_cells_skip_range(m, p, a.cells@, a.years@, a.ny as int, ycap as int, nn as int, j_lo as int, pos, bhi as int);
                }
                blo = bhi;
            }
        }
        let out = ScanOut { cells: a.cells, years: a.years, ny: a.ny, stop, aovf, ovf_k, ovf_n };
        out
    }
}

/// A row of a block whose first and last rows share a group shares it.
proof fn lemma_same_group(blo: int, bhi: int, j: int, bs: int)
    requires 1 <= bs, 0 <= blo <= j < bhi, blo / bs == (bhi - 1) / bs,
    ensures j / bs == blo / bs,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(blo, j, bs);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(j, bhi - 1, bs);
}

/// (1) fast: part keys dense and the block inside one group of lineitem rows (one `l_partkey` base).
fn collect_fast(c: &Cols, d: &Divs, bits: &Vec<u64>, blo: usize, bhi: usize, qj: &mut Vec<usize>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (nq: usize)
    requires
        look_ok(*c, *d, m), m.p_n > 0,
        bits_ok(bits@, m, p),
        p_dense_ok(m),
        blo < bhi <= m.l_n, bhi - blo <= BLOCK,
        blo as int / m.l_bs == (bhi - 1) as int / m.l_bs,
        old(qj)@.len() == BLOCK + 1,
    ensures
        final(qj)@.len() == BLOCK + 1,
        nq <= BLOCK,
        list_ok(m, p, final(qj)@, nq as int, blo as int, bhi as int),
    no_unwind
{
    proof { lemma_block(blo as int, m.l_bs, m.l_n, m.l_nb); }
    let g = grp(blo, d.l);
    let base = c.l_pk_b[g];
    let codes = c.l_pk_c;
    let pn: i64 = if (c.p_n as u64) <= 0x7fff_ffff_ffff_ffffu64 { c.p_n as i64 } else { 0x7fff_ffff_ffff_ffffi64 };
    let mut nq: usize = 0;
    let mut jj = blo;
    while jj < bhi
        invariant
            look_ok(*c, *d, m), m.p_n > 0,
            bits_ok(bits@, m, p),
            p_dense_ok(m),
            blo <= jj <= bhi <= m.l_n, bhi - blo <= BLOCK,
            blo as int / m.l_bs == (bhi - 1) as int / m.l_bs,
            g as int == blo as int / m.l_bs, base == m.l_pk_b[g as int], codes@ == m.l_pk_c,
            pn as int == if m.p_n <= 0x7fff_ffff_ffff_ffff { m.p_n } else { 0x7fff_ffff_ffff_ffff },
            qj@.len() == BLOCK + 1,
            list_ok(m, p, qj@, nq as int, blo as int, jj as int),
        decreases bhi - jj,
    {
        proof {
            lemma_same_group(blo as int, bhi as int, jj as int, m.l_bs);
            lemma_lvals(m, jj as int);
        }
        let pk = base + codes[jj] as i64;
        let inr = 1 <= pk && pk <= pn;
        let cc: usize = if inr { (pk - 1) as usize } else { 0 };
        proof {
            assert(pk as int == lpk(m, jj as int));
            if inr {
                assert(pkey(m, cc as int) == cc + 1);
                lemma_ppos(m, pk as int, cc as int);
            } else {
                assert forall|r: int| 0 <= r < m.p_n implies #[trigger] pkey(m, r) != pk as int by {
                    assert(pkey(m, r) == r + 1);
                }
                lemma_ppos(m, pk as int, 0);
            }
            lemma_word(cc as int, m.p_n, bits@.len() as int);
        }
        let w = bits[cc / 64];
        let bit: usize = if inr { ((w >> ((cc % 64) as u64)) & 1u64) as usize } else { 0 };
        proof {
            lemma_bit(bits@, cc as int, w);
            if inr {
                assert(bit_of(bits@, cc as int) == pmatch(m, p, cc as int));
                assert(((w >> ((cc % 64) as u64)) & 1u64) <= 1u64) by (bit_vector);
            }
            assert(pm(m, p, jj as int) == (bit == 1));
        }
        let ghost q0 = qj@;
        put(qj, nq, jj);
        proof {
            assert forall|j: int| blo <= j < jj + 1 && #[trigger] pm(m, p, j) implies
                exists|i: int| 0 <= i < nq + bit && qj@[i] == j by {
                if j < jj {
                    let i = choose|i: int| 0 <= i < nq && q0[i] == j;
                    assert(qj@[i] == j);
                } else {
                    assert(qj@[nq as int] == j);
                }
            }
        }
        nq = nq + bit;
        jj = jj + 1;
    }
    nq
}

/// (2) fast, in three tight passes: the supplier key and the part's rank (`qs`, `qr`), the cost from the compact
/// table (`qc`), the nation row (`qn`); dense part and supplier keys, nation keys in `[0, 256)`, one group.
fn gather_fast(c: &Cols, d: &Divs, bits: &Vec<u64>, wpre: &Vec<u32>, ents: &Vec<BuildOut>, k0s: &Vec<u64>, edv: Div,
    ntab: &Vec<u64>, blo: usize, bhi: usize,
    nq: usize, qj: &Vec<usize>, qc: &mut Vec<i64>, qn: &mut Vec<u64>, qs: &mut Vec<i64>, qr: &mut Vec<u64>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    requires
        look_ok(*c, *d, m), m.p_n > 0,
        bits_ok(bits@, m, p),
        ents_ok(bits@, wpre@, ents@, k0s@, edv.bs as int, m), div_ok(edv, edv.bs as int),
        ntab_ok(ntab@, true, m),
        p_dense_ok(m), s_dense_ok(m),
        blo < bhi <= m.l_n,
        blo as int / m.l_bs == (bhi - 1) as int / m.l_bs,
        nq <= BLOCK,
        qj@.len() == BLOCK + 1, old(qc)@.len() == BLOCK + 1, old(qn)@.len() == BLOCK + 1,
        old(qs)@.len() == BLOCK + 1, old(qr)@.len() == BLOCK + 1,
        list_ok(m, p, qj@, nq as int, blo as int, bhi as int),
    ensures
        final(qc)@.len() == BLOCK + 1, final(qn)@.len() == BLOCK + 1,
        final(qs)@.len() == BLOCK + 1, final(qr)@.len() == BLOCK + 1,
        gather_ok(m, qj@, final(qc)@, final(qn)@, nq as int),
    no_unwind
{
    proof { lemma_block(blo as int, m.l_bs, m.l_n, m.l_nb); }
    let g = grp(blo, d.l);
    let skb = c.l_sk_b[g];
    let pkb = c.l_pk_b[g];
    // pass 1: supplier key and part rank
    let mut i: usize = 0;
    while i < nq
        invariant
            look_ok(*c, *d, m), m.p_n > 0,
            bits_ok(bits@, m, p), ents_ok(bits@, wpre@, ents@, k0s@, edv.bs as int, m), div_ok(edv, edv.bs as int), p_dense_ok(m),
            blo < bhi <= m.l_n, blo as int / m.l_bs == (bhi - 1) as int / m.l_bs,
            g as int == blo as int / m.l_bs, skb == m.l_sk_b[g as int], pkb == m.l_pk_b[g as int],
            i <= nq <= BLOCK,
            qj@.len() == BLOCK + 1, qs@.len() == BLOCK + 1, qr@.len() == BLOCK + 1, qn@.len() == BLOCK + 1,
            list_ok(m, p, qj@, nq as int, blo as int, bhi as int),
            forall|k: int| 0 <= k < i ==> {
                let j = #[trigger] qj@[k] as int;
                &&& qs@[k] as int == lsk(m, j)
                &&& lc(m, j) < m.p_n
                &&& qr@[k] as int == rank_of(bits@, wpre@, lc(m, j))
                &&& qn@[k] as int == lc(m, j)
            },
        decreases nq - i,
    {
        let j = qj[i];
        proof {
            assert(blo <= qj@[i as int] < bhi && pm(m, p, j as int));
            lemma_same_group(blo as int, bhi as int, j as int, m.l_bs);
            lemma_lvals(m, j as int);
        }
        let sk = skb + c.l_sk_c[j] as i64;
        let pk = pkb + c.l_pk_c[j] as i64;
        proof {
            assert(pk as int == lpk(m, j as int) && sk as int == lsk(m, j as int));
            lemma_ppos(m, pk as int, 0);
            assert(pkey(m, lc(m, j as int)) == lc(m, j as int) + 1);
        }
        let cc = (pk - 1) as usize;
        proof {
            assert(cc as int == lc(m, j as int));
            lemma_word(cc as int, m.p_n, bits@.len() as int);
            lemma_word(cc as int, m.p_n, wpre@.len() as int);
        }
        let word = bits[cc / 64];
        let r = wpre[cc / 64] as u64 + count_below(word, (cc % 64) as u64);
        let ghost s0 = qs@;
        let ghost r0 = qr@;
        let ghost n0 = qn@;
        put(qs, i, sk);
        put(qr, i, r);
        put(qn, i, cc as u64);
        proof {
            assert forall|k: int| 0 <= k < i + 1 implies {
                let jk = #[trigger] qj@[k] as int;
                &&& qs@[k] as int == lsk(m, jk)
                &&& lc(m, jk) < m.p_n
                &&& qr@[k] as int == rank_of(bits@, wpre@, lc(m, jk))
                &&& qn@[k] as int == lc(m, jk)
            } by {
                if k < i { assert(qs@[k] == s0[k] && qr@[k] == r0[k] && qn@[k] == n0[k]); }
            }
        }
        i = i + 1;
    }
    // pass 2: the cost from the compact table
    let mut i: usize = 0;
    while i < nq
        invariant
            look_ok(*c, *d, m), m.p_n > 0,
            bits_ok(bits@, m, p), ents_ok(bits@, wpre@, ents@, k0s@, edv.bs as int, m), div_ok(edv, edv.bs as int), p_dense_ok(m),
            i <= nq <= BLOCK,
            qj@.len() == BLOCK + 1, qs@.len() == BLOCK + 1, qr@.len() == BLOCK + 1, qc@.len() == BLOCK + 1, qn@.len() == BLOCK + 1,
            forall|k: int| 0 <= k < nq ==> {
                let j = #[trigger] qj@[k] as int;
                &&& qs@[k] as int == lsk(m, j)
                &&& lc(m, j) < m.p_n
                &&& qr@[k] as int == rank_of(bits@, wpre@, lc(m, j))
                &&& qn@[k] as int == lc(m, j)
                &&& pm(m, p, j)
            },
            forall|k: int| 0 <= k < i ==> {
                let j = #[trigger] qj@[k] as int;
                &&& (qc@[k] == NO_COST ==> lt(m, j) == m.t_n)
                &&& (qc@[k] != NO_COST ==> lt(m, j) < m.t_n && qc@[k] as int == tcost(m, lt(m, j)))
            },
        decreases nq - i,
    {
        let r = qr[i];
        let sk = qs[i];
        let cc = qn[i] as usize;
        let ghost j = qj@[i as int] as int;
        proof {
            assert(cc as int == lc(m, j));
            assert(bit_of(bits@, cc as int));
            lemma_ppos(m, lpk(m, j), 0);
            assert(pkey(m, cc as int) == lpk(m, j));
        }
        let cost = tab_cost(ents, k0s, edv, cc, r, sk, Ghost(bits@), Ghost(wpre@), Ghost(m)).0;
        let ghost c0 = qc@;
        put(qc, i, cost);
        proof {
            assert forall|k: int| 0 <= k < i + 1 implies {
                let jk = #[trigger] qj@[k] as int;
                &&& (qc@[k] == NO_COST ==> lt(m, jk) == m.t_n)
                &&& (qc@[k] != NO_COST ==> lt(m, jk) < m.t_n && qc@[k] as int == tcost(m, lt(m, jk)))
            } by {
                if k < i { assert(qc@[k] == c0[k]); }
            }
        }
        i = i + 1;
    }
    // pass 3: the nation row of the supplier
    let sn = c.s_n;
    let mut i: usize = 0;
    while i < nq
        invariant
            look_ok(*c, *d, m), s_dense_ok(m), ntab_ok(ntab@, true, m), sn == m.s_n,
            i <= nq <= BLOCK,
            qj@.len() == BLOCK + 1, qs@.len() == BLOCK + 1, qn@.len() == BLOCK + 1,
            forall|k: int| 0 <= k < nq ==> (#[trigger] qs@[k]) as int == lsk(m, qj@[k] as int),
            forall|k: int| 0 <= k < i ==> {
                let j = #[trigger] qj@[k] as int;
                &&& (qn@[k] == NO_NATION ==> !(ls(m, j) < m.s_n && jn(m, j) < m.n_n))
                &&& (qn@[k] != NO_NATION ==> ls(m, j) < m.s_n && jn(m, j) == qn@[k] as int && (qn@[k] as int) < m.n_n)
            },
        decreases nq - i,
    {
        let sk = qs[i];
        let ghost j = qj@[i as int] as int;
        let n: u64 = if 1 <= sk && (sk as u64) <= (sn as u64) {
            let s = (sk - 1) as usize;
            proof {
                assert(skey(m, s as int) == s + 1);
                lemma_spos(m, sk as int, s as int);
            }
            nation_of(c, d, ntab, true, s, Ghost(m))
        } else {
            proof {
                assert forall|x: int| 0 <= x < m.s_n implies #[trigger] skey(m, x) != sk as int by {
                    assert(skey(m, x) == x + 1);
                }
                lemma_spos(m, sk as int, 0);
            }
            NO_NATION
        };
        proof { assert(qs@[i as int] as int == lsk(m, j)); }
        let ghost n0 = qn@;
        put(qn, i, n);
        proof {
            assert forall|k: int| 0 <= k < i + 1 implies {
                let jk = #[trigger] qj@[k] as int;
                &&& (qn@[k] == NO_NATION ==> !(ls(m, jk) < m.s_n && jn(m, jk) < m.n_n))
                &&& (qn@[k] != NO_NATION ==> ls(m, jk) < m.s_n && jn(m, jk) == qn@[k] as int && (qn@[k] as int) < m.n_n)
            } by {
                if k < i { assert(qn@[k] == n0[k]); }
            }
        }
        i = i + 1;
    }
}

/// Block `[blo, bhi)` of a task's rows `[j_lo, j_hi)`: (1) its matching rows (from the destination chunk's bitmap on
/// the directory path, else from the rows' parts), (2) their partsupp costs and nation rows (through the rows'
/// payloads when the chunk has them).
fn block_rows(c: &Cols, d: &Divs, bits: &Vec<u64>, wpre: &Vec<u32>, ents: &Vec<BuildOut>, k0s: &Vec<u64>, edv: Div, ntab: &Vec<u64>,
    fast_ps: bool, n_small: bool, p_dense: bool, s_dense: bool, use_bm: bool, res: &Vec<ShufOut>, cs: &mut ChunkSt,
    blo: usize, bhi: usize, j_hi: usize, qj: &mut Vec<usize>, qc: &mut Vec<i64>, qn: &mut Vec<u64>, qs: &mut Vec<i64>, qr: &mut Vec<u64>,
    qa: &mut Vec<i128>, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(pa): Ghost<PA>, Ghost(j_lo): Ghost<int>) -> (nq: usize)
    requires
        look_ok(*c, *d, m), m.p_n > 0,
        bits_ok(bits@, m, p),
        fast_ps ==> ents_ok(bits@, wpre@, ents@, k0s@, edv.bs as int, m) && div_ok(edv, edv.bs as int),
        ntab_ok(ntab@, n_small, m),
        p_dense ==> p_dense_ok(m),
        s_dense ==> s_dense_ok(m),
        pa == (PA { bits: bits@, wpre: wpre@, k0s: k0s@, per: edv.bs as int }),
        use_bm ==> res_ok(res@, m, p, pa) && chunk_inv(*old(cs), m, p, pa, j_lo, j_hi as int, blo as int),
        j_lo <= blo < j_hi <= m.l_n,
        bhi == (if j_hi - blo > BLOCK { (blo + BLOCK) as usize } else { j_hi }),
        old(qj)@.len() == BLOCK + 1, old(qc)@.len() == BLOCK + 1, old(qn)@.len() == BLOCK + 1,
        old(qs)@.len() == BLOCK + 1, old(qr)@.len() == BLOCK + 1, old(qa)@.len() == BLOCK + 1,
    ensures
        final(qj)@.len() == BLOCK + 1, final(qc)@.len() == BLOCK + 1, final(qn)@.len() == BLOCK + 1,
        final(qs)@.len() == BLOCK + 1, final(qr)@.len() == BLOCK + 1, final(qa)@.len() == BLOCK + 1,
        nq <= BLOCK,
        list_ok(m, p, final(qj)@, nq as int, blo as int, bhi as int),
        gather_ok(m, final(qj)@, final(qc)@, final(qn)@, nq as int),
        amts_ok(m, final(qj)@, final(qc)@, final(qa)@, nq as int),
        use_bm ==> chunk_inv(*final(cs), m, p, pa, j_lo, j_hi as int, bhi as int),
    no_unwind
{
    let one = grp(blo, d.l) == grp(bhi - 1, d.l);
    let mut r0: usize = 0;
    let nq = if use_bm {
        let (n1, r1) = bm_block(res, cs, blo, bhi, j_hi, c.l_n, qj, Ghost(m), Ghost(p), Ghost(pa), Ghost(j_lo));
        r0 = r1;
        n1
    } else if p_dense && one {
        collect_fast(c, d, bits, blo, bhi, qj, Ghost(m), Ghost(p))
    } else {
        collect(c, d, bits, p_dense, blo, bhi, qj, Ghost(m), Ghost(p))
    };
    if use_bm && cs.pay && fast_ps && n_small && s_dense && one {
        gather_pay(c, d, ents, blo, bhi, nq, qj, &cs.pl, r0, qc, qn, qs, qr, Ghost(m), Ghost(p), Ghost(pa));
    } else if fast_ps && n_small && p_dense && s_dense && one {
        gather_fast(c, d, bits, wpre, ents, k0s, edv, ntab, blo, bhi, nq, qj, qc, qn, qs, qr, Ghost(m), Ghost(p));
    } else {
        gather(c, d, bits, wpre, ents, k0s, edv, ntab, fast_ps, n_small, p_dense, s_dense, nq, qj, qc, qn,
            Ghost(m), Ghost(p), Ghost(blo as int), Ghost(bhi as int));
    }
    amounts(c, d, nq, qj, qc, qa, Ghost(m), Ghost(p), Ghost(qn@), Ghost(blo as int), Ghost(bhi as int));
    nq
}

/// Every listed row with a partsupp cost has its amount (scale 4) in `qa`.
pub open spec fn amts_ok(m: M, qj: Seq<usize>, qc: Seq<i64>, qa: Seq<i128>, nq: int) -> bool {
    forall|i: int| 0 <= i < nq && qc[i] != NO_COST ==> #[trigger] qa[i] as int == jamt(m, qj[i] as int)
}

/// (2d) The amount `l_extendedprice * (100 - l_discount) - ps_supplycost * l_quantity` (scale 4) of every listed
/// row with a partsupp cost (`0` for the others), in one tight pass whose column reads overlap; the accumulation
/// step then only adds.
fn amounts(c: &Cols, d: &Divs, nq: usize, qj: &Vec<usize>, qc: &Vec<i64>, qa: &mut Vec<i128>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(qn): Ghost<Seq<u64>>, Ghost(blo): Ghost<int>, Ghost(bhi): Ghost<int>)
    requires
        look_ok(*c, *d, m),
        bhi <= m.l_n,
        nq <= BLOCK,
        qj@.len() == BLOCK + 1, qc@.len() == BLOCK + 1, old(qa)@.len() == BLOCK + 1,
        list_ok(m, p, qj@, nq as int, blo, bhi),
        gather_ok(m, qj@, qc@, qn, nq as int),
    ensures
        final(qa)@.len() == BLOCK + 1,
        amts_ok(m, qj@, qc@, final(qa)@, nq as int),
    no_unwind
{
    let mut i: usize = 0;
    while i < nq
        invariant
            look_ok(*c, *d, m),
            bhi <= m.l_n,
            i <= nq <= BLOCK,
            qj@.len() == BLOCK + 1, qc@.len() == BLOCK + 1, qa@.len() == BLOCK + 1,
            list_ok(m, p, qj@, nq as int, blo, bhi),
            gather_ok(m, qj@, qc@, qn, nq as int),
            forall|k: int| 0 <= k < i && qc@[k] != NO_COST ==> #[trigger] qa@[k] as int == jamt(m, qj@[k] as int),
        decreases nq - i,
    {
        let j = qj[i];
        let cost = qc[i];
        let x: i128 = if cost != NO_COST {
            proof {
                assert(blo <= qj@[i as int] < bhi);
                lemma_amount(m, j as int, cost as int);
            }
            let (qty, price, disc) = get_lnums(c, d, j, Ghost(m));
            (price as i128) * (100 - disc as i128) - (cost as i128) * (qty as i128)
        } else {
            0
        };
        let ghost a0 = qa@;
        put(qa, i, x);
        proof {
            assert forall|k: int| 0 <= k < i + 1 && qc@[k] != NO_COST implies #[trigger] qa@[k] as int == jamt(m, qj@[k] as int) by {
                if k < i { assert(qa@[k] == a0[k]); }
            }
        }
        i = i + 1;
    }
}

/// The directory path's state of a task: the current destination chunk `[lo, hi)` with its bitmap, word prefixes
/// and (when `pay`) the payloads of its rows at their ranks, and the set bits `rpos` before the next block.
pub struct ChunkSt {
    pub bm: Vec<u64>,
    pub wp: Vec<u32>,
    pub pl: Vec<u32>,
    pub lo: usize,
    pub hi: usize,
    pub rpos: usize,
    pub pay: bool,
}

/// The chunk state before block row `blo` of the task rows `[j_lo, j_hi)`: `blo` is the chunk's end (the next block
/// opens the next chunk) or a block start inside it.
#[verifier::opaque]
pub open spec fn chunk_inv(s: ChunkSt, m: M, p: QP, pa: PA, j_lo: int, j_hi: int, blo: int) -> bool {
    &&& s.bm@.len() == CHW + 1 && s.wp@.len() == CHW + 2
    &&& j_lo <= s.lo <= blo <= s.hi <= j_hi <= m.l_n
    &&& s.lo as int % CH as int == 0
    &&& (s.hi as int % CH as int == 0 || s.hi == m.l_n)
    &&& (j_hi % CH as int == 0 || j_hi == m.l_n)
    &&& m.l_n + CH <= usize::MAX
    &&& blo < s.hi ==> {
        &&& chunk_rows(m, s.lo as int / CH as int, s.lo as int, s.hi as int)
        &&& bm_ok(s.bm@, m, p, s.lo as int, s.hi as int)
        &&& (s.pay ==> chunk_pay_ok(s.pl@, s.bm@, m, pa, s.lo as int, s.hi as int))
        &&& s.rpos == nbelow(s.bm@, blo - s.lo)
        &&& (blo - s.lo) % BLOCK as int == 0
    }
}

/// The next chunk from its start `blo` (a chunk boundary before the task end).
proof fn lemma_open_chunk(m: M, j_hi: int, blo: int, h: int, chi: int)
    requires
        blo % CH as int == 0, 0 <= blo < j_hi <= m.l_n, (j_hi % CH as int == 0 || j_hi == m.l_n),
        h == blo / CH as int,
        chi == (if m.l_n - blo >= CH { blo + CH } else { m.l_n }),
    ensures
        chunk_rows(m, h, blo, chi), chi <= j_hi, (chi % CH as int == 0 || chi == m.l_n), blo < chi,
{
    assert(h * 262144 == blo) by (nonlinear_arith) requires h == blo / 262144, blo % 262144 == 0;
    assert(h < m.l_n / 262144 + 1) by (nonlinear_arith) requires h == blo / 262144, 0 <= blo < m.l_n;
    if j_hi != m.l_n {
        assert(j_hi >= blo + 262144) by (nonlinear_arith) requires j_hi % 262144 == 0, blo % 262144 == 0, blo < j_hi;
    }
    if m.l_n - blo >= CH {
        assert((blo + 262144) % 262144 == 0) by (nonlinear_arith) requires blo % 262144 == 0;
    }
}

/// A block from `blo` (a block start inside the chunk `[lo, hi)`) ends inside the chunk, at a word boundary or at the
/// chunk's end.
proof fn lemma_block_in_chunk(lo: int, hi: int, blo: int, bhi: int, j_hi: int, n: int)
    requires
        lo % CH as int == 0, 0 <= lo <= blo < hi <= j_hi <= n, hi <= lo + CH,
        (hi % CH as int == 0 || hi == n), (j_hi % CH as int == 0 || j_hi == n),
        (blo - lo) % BLOCK as int == 0,
        bhi == (if j_hi - blo > BLOCK { blo + BLOCK } else { j_hi }),
    ensures
        bhi <= hi, (blo - lo) % 64 == 0, bhi == hi || (bhi - lo) % BLOCK as int == 0, (bhi - lo) % 64 == 0 || bhi == hi,
{
    assert((blo - lo) % 64 == 0) by (nonlinear_arith) requires (blo - lo) % 2048 == 0, blo >= lo;
    if hi != n {
        assert(hi == lo + 262144) by (nonlinear_arith) requires hi % 262144 == 0, lo % 262144 == 0, lo < hi <= lo + 262144;
        assert(blo + 2048 <= hi) by (nonlinear_arith) requires (blo - lo) % 2048 == 0, lo <= blo < hi, hi == lo + 262144;
    }
    if bhi == blo + BLOCK {
        assert((bhi - lo) % 2048 == 0 && (bhi - lo) % 64 == 0) by (nonlinear_arith) requires (blo - lo) % 2048 == 0, bhi == blo + 2048, blo >= lo;
    }
}

/// The directory path's block `[blo, bhi)`: opens the next destination chunk when `blo` is the current one's end,
/// then lists the block's matching rows from the chunk's bitmap; returns them with the set bits `r0` before the
/// block (the payload of listed row `i` is `pl[r0 + i]` when the chunk has payloads).
fn bm_block(res: &Vec<ShufOut>, cs: &mut ChunkSt, blo: usize, bhi: usize, j_hi: usize, n: usize, qj: &mut Vec<usize>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(pa): Ghost<PA>, Ghost(j_lo): Ghost<int>) -> (r: (usize, usize))
    requires
        res_ok(res@, m, p, pa),
        chunk_inv(*old(cs), m, p, pa, j_lo, j_hi as int, blo as int),
        blo < j_hi, n == m.l_n,
        bhi == (if j_hi - blo > BLOCK { (blo + BLOCK) as usize } else { j_hi }),
        old(qj)@.len() == BLOCK + 1,
    ensures
        final(qj)@.len() == BLOCK + 1,
        r.0 <= BLOCK,
        list_ok(m, p, final(qj)@, r.0 as int, blo as int, bhi as int),
        chunk_inv(*final(cs), m, p, pa, j_lo, j_hi as int, bhi as int),
        final(cs).pay ==> forall|i: int| 0 <= i < r.0 ==> #[trigger] pay_row(final(cs).pl@, r.1 as int, pa, m, final(qj)@, i),
    no_unwind
{
    proof { reveal(chunk_inv); }
    if blo == cs.hi {
        // the next destination chunk
        let h = blo / CH;
        let chi = if n - blo >= CH { blo + CH } else { n };
        proof {
            assert(blo as int % CH as int == 0);
            lemma_open_chunk(m, j_hi as int, blo as int, h as int, chi as int);
        }
        let ok = start_chunk(res, h, blo, chi, &mut cs.bm, &mut cs.wp, &mut cs.pl, Ghost(m), Ghost(p), Ghost(pa));
        cs.lo = blo;
        cs.hi = chi;
        cs.rpos = 0;
        cs.pay = ok;
        proof {
            assert(blo as int / CH as int == h as int);
            assert(nbelow(cs.bm@, 0) == 0);
        }
    }
    proof {
        lemma_block_in_chunk(cs.lo as int, cs.hi as int, blo as int, bhi as int, j_hi as int, n as int);
    }
    let nq = collect_bm(&cs.bm, cs.lo, cs.hi, blo, bhi, qj, Ghost(m), Ghost(p));
    let r0 = cs.rpos;
    proof {
        if cs.pay {
            lemma_block_pay(m, p, pa, cs.bm@, cs.pl@, qj@, nq as int, cs.lo as int, cs.hi as int, blo as int, bhi as int, r0 as int);
        } else {
            lemma_block_count(m, p, cs.bm@, qj@, nq as int, cs.lo as int, cs.hi as int, blo as int, bhi as int);
        }
        lemma_nbelow_le(cs.bm@, bhi - cs.lo);
    }
    cs.rpos = r0 + nq;
    (nq, r0)
}

/// Destination chunk `h` = rows `[lo, hi)`: its bitmap (cleared first), the word prefixes and the rows' payloads at
/// their ranks.
fn start_chunk(res: &Vec<ShufOut>, h: usize, lo: usize, hi: usize, bm: &mut Vec<u64>, wp: &mut Vec<u32>, pl: &mut Vec<u32>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(a): Ghost<PA>) -> (ok: bool)
    requires
        res_ok(res@, m, p, a),
        chunk_rows(m, h as int, lo as int, hi as int),
        old(bm)@.len() == CHW + 1, old(wp)@.len() == CHW + 2,
    ensures
        final(bm)@.len() == CHW + 1, final(wp)@.len() == CHW + 2, final(pl)@.len() == old(pl)@.len(),
        bm_ok(final(bm)@, m, p, lo as int, hi as int),
        ok ==> chunk_pay_ok(final(pl)@, final(bm)@, m, a, lo as int, hi as int),
    no_unwind
{
    let mut w: usize = 0;
    while w < CHW + 1
        invariant
            bm@.len() == CHW + 1, w <= CHW + 1,
            forall|v: int| 0 <= v < w ==> #[trigger] bm@[v] == 0u64,
        decreases CHW + 1 - w,
    {
        let ghost b0 = bm@;
        put(bm, w, 0u64);
        proof {
            assert forall|v: int| 0 <= v < w + 1 implies #[trigger] bm@[v] == 0u64 by {
                if v < w { assert(bm@[v] == b0[v]); }
            }
        }
        w = w + 1;
    }
    proof {
        assert(hi - lo <= CH);
    }
    fill_chunk(res, h, bm, lo, hi, Ghost(m), Ghost(p), Ghost(a));
    let nw = (hi - lo + 63) / 64;
    proof {
        assert(nw <= CHW && nw * 64 >= hi - lo) by (nonlinear_arith) requires nw == (hi - lo + 63) / 64, hi - lo <= 262144, lo <= hi;
    }
    prefix_counts(bm, nw, wp);
    if (wp[nw] as usize) <= pl.len() {
        scatter_chunk(res, h, bm, wp, nw, pl, lo, hi, Ghost(m), Ghost(p), Ghost(a));
        true
    } else {
        false
    }
}

/// Listed row `i` finds its part's payload at `pl[r + i]`.
pub open spec fn pay_row(pl: Seq<u32>, r: int, a: PA, m: M, qj: Seq<usize>, i: int) -> bool {
    &&& r + i < pl.len()
    &&& pay_ok(pl[r + i], a, lc(m, qj[i] as int))
}

/// The listed rows of block `[blo, bhi)` of chunk `[lo, hi)` find their payloads at `rpos + i` (`rpos`: the set bits
/// before the block), and the block holds `nq` set bits.
proof fn lemma_block_pay(m: M, p: QP, a: PA, bm: Seq<u64>, pl: Seq<u32>, qj: Seq<usize>, nq: int, lo: int, hi: int,
    blo: int, bhi: int, rpos: int)
    requires
        bm_ok(bm, m, p, lo, hi), chunk_pay_ok(pl, bm, m, a, lo, hi),
        list_ok(m, p, qj, nq, blo, bhi), nq <= qj.len(),
        0 <= lo <= blo <= bhi <= hi, rpos == nbelow(bm, blo - lo),
    ensures
        forall|i: int| 0 <= i < nq ==> #[trigger] pay_row(pl, rpos, a, m, qj, i),
        nbelow(bm, bhi - lo) == rpos + nq,
{
    assert forall|i: int| 0 <= i < nq implies blo - lo <= #[trigger] qj[i] - lo < bhi - lo && wbit(bm, qj[i] - lo) by {
        assert(blo <= qj[i] < bhi && pm(m, p, qj[i] as int));
    }
    assert forall|k: int| blo - lo <= k < bhi - lo && #[trigger] wbit(bm, k) implies exists|i: int| 0 <= i < nq && qj[i] == lo + k by {
        assert(pm(m, p, lo + k));
    }
    assert(listed(qj, nq, bm, blo - lo, bhi - lo, lo));
    lemma_list_rank(qj, nq, bm, blo - lo, bhi - lo, lo);
    assert forall|i: int| 0 <= i < nq implies #[trigger] pay_row(pl, rpos, a, m, qj, i) by {
        let k = qj[i] - lo;
        assert(nbelow(bm, qj[i] - lo) == rpos + i);
        assert(wbit(bm, k));
        assert(pl_at(pl, bm, m, a, lo, lo + k));
    }
}

/// A block of chunk `[lo, hi)` holds the `nq` listed set bits.
proof fn lemma_block_count(m: M, p: QP, bm: Seq<u64>, qj: Seq<usize>, nq: int, lo: int, hi: int, blo: int, bhi: int)
    requires
        bm_ok(bm, m, p, lo, hi), list_ok(m, p, qj, nq, blo, bhi), nq <= qj.len(),
        0 <= lo <= blo <= bhi <= hi,
    ensures nbelow(bm, bhi - lo) == nbelow(bm, blo - lo) + nq,
{
    assert forall|i: int| 0 <= i < nq implies blo - lo <= #[trigger] qj[i] - lo < bhi - lo && wbit(bm, qj[i] - lo) by {
        assert(blo <= qj[i] < bhi && pm(m, p, qj[i] as int));
    }
    assert forall|k: int| blo - lo <= k < bhi - lo && #[trigger] wbit(bm, k) implies exists|i: int| 0 <= i < nq && qj[i] == lo + k by {
        assert(pm(m, p, lo + k));
    }
    assert(listed(qj, nq, bm, blo - lo, bhi - lo, lo));
    lemma_list_rank(qj, nq, bm, blo - lo, bhi - lo, lo);
}

/// (2) through the payloads (`pl[rpos ..]`: each row's compact table and entries' index), in two tight passes: the
/// supplier key and the payload (`qs`, `qr`), then the cost and the supplier's nation row from the entry of the
/// compact table (`qc`, `qn`; the entry packs the nation tag of its supplier key); one group.
fn gather_pay(c: &Cols, d: &Divs, ents: &Vec<BuildOut>, blo: usize, bhi: usize,
    nq: usize, qj: &Vec<usize>, pl: &Vec<u32>, rpos: usize, qc: &mut Vec<i64>, qn: &mut Vec<u64>, qs: &mut Vec<i64>, qr: &mut Vec<u64>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(a): Ghost<PA>)
    requires
        look_ok(*c, *d, m), m.p_n > 0,
        bits_ok(a.bits, m, p),
        ents_ok(a.bits, a.wpre, ents@, a.k0s, a.per, m),
        blo < bhi <= m.l_n,
        blo as int / m.l_bs == (bhi - 1) as int / m.l_bs,
        nq <= BLOCK,
        qj@.len() == BLOCK + 1, old(qc)@.len() == BLOCK + 1, old(qn)@.len() == BLOCK + 1,
        old(qs)@.len() == BLOCK + 1, old(qr)@.len() == BLOCK + 1,
        list_ok(m, p, qj@, nq as int, blo as int, bhi as int),
        forall|i: int| 0 <= i < nq ==> #[trigger] pay_row(pl@, rpos as int, a, m, qj@, i),
    ensures
        final(qc)@.len() == BLOCK + 1, final(qn)@.len() == BLOCK + 1,
        final(qs)@.len() == BLOCK + 1, final(qr)@.len() == BLOCK + 1,
        gather_ok(m, qj@, final(qc)@, final(qn)@, nq as int),
    no_unwind
{
    proof {
        lemma_block(blo as int, m.l_bs, m.l_n, m.l_nb);
    }
    let pn = pl.len();
    let g = grp(blo, d.l);
    let skb = c.l_sk_b[g];
    // pass 1: supplier key and payload
    let mut i: usize = 0;
    while i < nq
        invariant
            look_ok(*c, *d, m),
            blo < bhi <= m.l_n, blo as int / m.l_bs == (bhi - 1) as int / m.l_bs,
            g as int == blo as int / m.l_bs, skb == m.l_sk_b[g as int],
            i <= nq <= BLOCK, pn == pl@.len(),
            forall|k: int| 0 <= k < nq ==> #[trigger] pay_row(pl@, rpos as int, a, m, qj@, k),
            qj@.len() == BLOCK + 1, qs@.len() == BLOCK + 1, qr@.len() == BLOCK + 1,
            list_ok(m, p, qj@, nq as int, blo as int, bhi as int),
            forall|k: int| 0 <= k < i ==> {
                let j = #[trigger] qj@[k] as int;
                &&& qs@[k] as int == lsk(m, j)
                &&& qr@[k] == pl@[rpos + k] as u64
            },
        decreases nq - i,
    {
        let j = qj[i];
        proof {
            assert(blo <= qj@[i as int] < bhi);
            lemma_same_group(blo as int, bhi as int, j as int, m.l_bs);
            lemma_lvals(m, j as int);
        }
        let sk = skb + c.l_sk_c[j] as i64;
        proof { assert(pay_row(pl@, rpos as int, a, m, qj@, i as int)); }
        let e = pl[rpos + i];
        let ghost s0 = qs@;
        let ghost r0 = qr@;
        put(qs, i, sk);
        put(qr, i, e as u64);
        proof {
            assert forall|k: int| 0 <= k < i + 1 implies {
                let jk = #[trigger] qj@[k] as int;
                &&& qs@[k] as int == lsk(m, jk)
                &&& qr@[k] == pl@[rpos + k] as u64
            } by {
                if k < i { assert(qs@[k] == s0[k] && qr@[k] == r0[k]); }
            }
        }
        i = i + 1;
    }
    // pass 2: the cost and the supplier's nation row from the compact table of the payload
    let ntabs = ents.len();
    let mut i: usize = 0;
    while i < nq
        invariant
            look_ok(*c, *d, m), m.p_n > 0,
            bits_ok(a.bits, m, p), ents_ok(a.bits, a.wpre, ents@, a.k0s, a.per, m), ntabs == ents@.len(),
            i <= nq <= BLOCK,
            qj@.len() == BLOCK + 1, qs@.len() == BLOCK + 1, qr@.len() == BLOCK + 1, qc@.len() == BLOCK + 1, qn@.len() == BLOCK + 1,
            list_ok(m, p, qj@, nq as int, blo as int, bhi as int),
            forall|k: int| 0 <= k < nq ==> #[trigger] pay_row(pl@, rpos as int, a, m, qj@, k),
            forall|k: int| 0 <= k < nq ==> {
                let j = #[trigger] qj@[k] as int;
                &&& qs@[k] as int == lsk(m, j)
                &&& qr@[k] == pl@[rpos + k] as u64
            },
            forall|k: int| 0 <= k < i ==> {
                let j = #[trigger] qj@[k] as int;
                &&& (qc@[k] != NO_COST && qn@[k] == NO_NATION ==> !(ls(m, j) < m.s_n && jn(m, j) < m.n_n))
                &&& (qc@[k] != NO_COST && qn@[k] != NO_NATION ==> ls(m, j) < m.s_n && jn(m, j) == qn@[k] as int && (qn@[k] as int) < m.n_n)
                &&& (qc@[k] == NO_COST ==> lt(m, j) == m.t_n)
                &&& (qc@[k] != NO_COST ==> lt(m, j) < m.t_n && qc@[k] as int == tcost(m, lt(m, j)))
            },
        decreases nq - i,
    {
        let e = qr[i] as u32;
        let sk = qs[i];
        let ghost j = qj@[i as int] as int;
        let ghost cc = lc(m, j);
        proof {
            assert(pm(m, p, j));
            assert(pay_row(pl@, rpos as int, a, m, qj@, i as int));
            assert(pay_ok(pl@[rpos + i], a, cc));
            assert(bit_of(a.bits, cc));
            assert(ents_at(a.bits, a.wpre, ents@, a.k0s, a.per, m, cc));
            lemma_ppos(m, lpk(m, j), 0);
            assert(pkey(m, cc) == lpk(m, j));
        }
        let tb = (e >> 26u32) as usize;
        let local = (e & 0x3ff_ffffu32) as usize;
        let t = &ents[tb];
        let (cost, nt) = ps_cost_fast(&t.ents, local, sk, Ghost(m), Ghost(pkey(m, cc)));
        let n: u64 = if nt == NO_TAG { NO_NATION } else { nt };
        proof {
            if cost != NO_COST {
                // the tag of the row's supplier key is its supplier's nation row (`ls`, `jn`)
                lemma_ntag(m, sk as int);
                assert(sk as int == lsk(m, j));
            }
        }
        let ghost c0 = qc@;
        let ghost n0 = qn@;
        put(qc, i, cost);
        put(qn, i, n);
        proof {
            assert forall|k: int| 0 <= k < i + 1 implies {
                let jk = #[trigger] qj@[k] as int;
                &&& (qc@[k] != NO_COST && qn@[k] == NO_NATION ==> !(ls(m, jk) < m.s_n && jn(m, jk) < m.n_n))
                &&& (qc@[k] != NO_COST && qn@[k] != NO_NATION ==> ls(m, jk) < m.s_n && jn(m, jk) == qn@[k] as int && (qn@[k] as int) < m.n_n)
                &&& (qc@[k] == NO_COST ==> lt(m, jk) == m.t_n)
                &&& (qc@[k] != NO_COST ==> lt(m, jk) < m.t_n && qc@[k] as int == tcost(m, lt(m, jk)))
            } by {
                if k < i { assert(qc@[k] == c0[k] && qn@[k] == n0[k]); }
            }
        }
        i = i + 1;
    }
}

/// (1) The rows of `[blo, bhi)` whose part matches, branch-free, into `qj[0 .. nq]`.
fn collect(c: &Cols, d: &Divs, bits: &Vec<u64>, p_dense: bool, blo: usize, bhi: usize, qj: &mut Vec<usize>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (nq: usize)
    requires
        look_ok(*c, *d, m), m.p_n > 0,
        bits_ok(bits@, m, p),
        p_dense ==> p_dense_ok(m),
        blo <= bhi <= m.l_n, bhi - blo <= BLOCK,
        old(qj)@.len() == BLOCK + 1,
    ensures
        final(qj)@.len() == BLOCK + 1,
        nq <= BLOCK,
        list_ok(m, p, final(qj)@, nq as int, blo as int, bhi as int),
    no_unwind
{
    let mut nq: usize = 0;
    let mut jj = blo;
    while jj < bhi
        invariant
            look_ok(*c, *d, m), m.p_n > 0,
            bits_ok(bits@, m, p),
            p_dense ==> p_dense_ok(m),
            blo <= jj <= bhi <= m.l_n, bhi - blo <= BLOCK,
            qj@.len() == BLOCK + 1,
            list_ok(m, p, qj@, nq as int, blo as int, jj as int),
        decreases bhi - jj,
    {
        let pk = get_lpk(c, d, jj, Ghost(m));
        let pr = part_row(c, d, p_dense, pk, Ghost(m));
        let (cc, inr) = match pr { Some(x) => (x, true), None => (0usize, false) };
        proof { lemma_word(cc as int, m.p_n, bits@.len() as int); }
        let w = bits[cc / 64];
        let bit: usize = if inr { ((w >> ((cc % 64) as u64)) & 1u64) as usize } else { 0 };
        proof {
            lemma_bit(bits@, cc as int, w);
            if inr {
                assert(bit_of(bits@, cc as int) == pmatch(m, p, cc as int));
                assert(((w >> ((cc % 64) as u64)) & 1u64) <= 1u64) by (bit_vector);
            }
            assert(pm(m, p, jj as int) == (bit == 1));
        }
        let ghost q0 = qj@;
        put(qj, nq, jj);
        proof {
            assert forall|j: int| blo <= j < jj + 1 && #[trigger] pm(m, p, j) implies
                exists|i: int| 0 <= i < nq + bit && qj@[i] == j by {
                if j < jj {
                    let i = choose|i: int| 0 <= i < nq && q0[i] == j;
                    assert(qj@[i] == j);
                } else {
                    assert(qj@[nq as int] == j);
                }
            }
        }
        nq = nq + bit;
        jj = jj + 1;
    }
    nq
}

/// (2) The partsupp cost and nation row of each listed row.
fn gather(c: &Cols, d: &Divs, bits: &Vec<u64>, wpre: &Vec<u32>, ents: &Vec<BuildOut>, k0s: &Vec<u64>, edv: Div, ntab: &Vec<u64>, fast_ps: bool, n_small: bool,
    p_dense: bool, s_dense: bool, nq: usize, qj: &Vec<usize>, qc: &mut Vec<i64>, qn: &mut Vec<u64>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(blo): Ghost<int>, Ghost(bhi): Ghost<int>)
    requires
        look_ok(*c, *d, m), m.p_n > 0,
        bits_ok(bits@, m, p),
        fast_ps ==> ents_ok(bits@, wpre@, ents@, k0s@, edv.bs as int, m) && div_ok(edv, edv.bs as int),
        ntab_ok(ntab@, n_small, m),
        p_dense ==> p_dense_ok(m),
        s_dense ==> s_dense_ok(m),
        0 <= blo <= bhi <= m.l_n,
        nq <= BLOCK,
        qj@.len() == BLOCK + 1, old(qc)@.len() == BLOCK + 1, old(qn)@.len() == BLOCK + 1,
        list_ok(m, p, qj@, nq as int, blo, bhi),
    ensures
        final(qc)@.len() == BLOCK + 1, final(qn)@.len() == BLOCK + 1,
        gather_ok(m, qj@, final(qc)@, final(qn)@, nq as int),
    no_unwind
{
    let mut i: usize = 0;
    while i < nq
        invariant
            look_ok(*c, *d, m), m.p_n > 0,
            bits_ok(bits@, m, p),
            fast_ps ==> ents_ok(bits@, wpre@, ents@, k0s@, edv.bs as int, m) && div_ok(edv, edv.bs as int),
            ntab_ok(ntab@, n_small, m),
            p_dense ==> p_dense_ok(m),
            s_dense ==> s_dense_ok(m),
            0 <= blo <= bhi <= m.l_n,
            i <= nq <= BLOCK,
            qj@.len() == BLOCK + 1, qc@.len() == BLOCK + 1, qn@.len() == BLOCK + 1,
            list_ok(m, p, qj@, nq as int, blo, bhi),
            gather_ok(m, qj@, qc@, qn@, i as int),
        decreases nq - i,
    {
        let j = qj[i];
        let (cost, n) = gather_row(c, d, bits, wpre, ents, k0s, edv, ntab, fast_ps, n_small, p_dense, s_dense, j, Ghost(m), Ghost(p));
        let ghost qc0 = qc@;
        let ghost qn0 = qn@;
        put(qc, i, cost);
        put(qn, i, n);
        proof {
            assert forall|k: int| 0 <= k < i + 1 implies {
                let jk = #[trigger] qj@[k] as int;
                &&& (qc@[k] != NO_COST && qn@[k] == NO_NATION ==> !(ls(m, jk) < m.s_n && jn(m, jk) < m.n_n))
                &&& (qc@[k] != NO_COST && qn@[k] != NO_NATION ==> ls(m, jk) < m.s_n && jn(m, jk) == qn@[k] as int && (qn@[k] as int) < m.n_n)
                &&& (qc@[k] == NO_COST ==> lt(m, jk) == m.t_n)
                &&& (qc@[k] != NO_COST ==> lt(m, jk) < m.t_n && qc@[k] as int == tcost(m, lt(m, jk)))
            } by {
                if k < i {
                    assert(qc@[k] == qc0[k] && qn@[k] == qn0[k]);
                }
            }
        }
        i = i + 1;
    }
}

/// The partsupp cost and nation row of lineitem row `j`, whose part matches.
fn gather_row(c: &Cols, d: &Divs, bits: &Vec<u64>, wpre: &Vec<u32>, ents: &Vec<BuildOut>, k0s: &Vec<u64>, edv: Div, ntab: &Vec<u64>, fast_ps: bool,
    n_small: bool, p_dense: bool, s_dense: bool, j: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (i64, u64))
    requires
        look_ok(*c, *d, m), m.p_n > 0,
        bits_ok(bits@, m, p),
        fast_ps ==> ents_ok(bits@, wpre@, ents@, k0s@, edv.bs as int, m) && div_ok(edv, edv.bs as int),
        ntab_ok(ntab@, n_small, m),
        p_dense ==> p_dense_ok(m),
        s_dense ==> s_dense_ok(m),
        j < m.l_n,
        pm(m, p, j as int),
    ensures
        r.1 == NO_NATION ==> !(ls(m, j as int) < m.s_n && jn(m, j as int) < m.n_n),
        r.1 != NO_NATION ==> ls(m, j as int) < m.s_n && jn(m, j as int) == r.1 as int && (r.1 as int) < m.n_n,
        r.0 == NO_COST ==> lt(m, j as int) == m.t_n,
        r.0 != NO_COST ==> lt(m, j as int) < m.t_n && r.0 as int == tcost(m, lt(m, j as int)),
    no_unwind
{
    let pk = get_lpk(c, d, j, Ghost(m));
    let skv = get_lsk(c, d, j, Ghost(m));
    let n: u64 = match supp_row(c, d, s_dense, skv, Ghost(m)) {
        Some(s) => nation_of(c, d, ntab, n_small, s, Ghost(m)),
        None => NO_NATION,
    };
    let cost: i64 = if fast_ps {
        let cc = match part_row(c, d, p_dense, pk, Ghost(m)) { Some(x) => x, None => 0 };
        proof {
            assert(bit_of(bits@, cc as int));
            lemma_word(cc as int, m.p_n, bits@.len() as int);
            lemma_word(cc as int, m.p_n, wpre@.len() as int);
        }
        let word = bits[cc / 64];
        let r = wpre[cc / 64] as u64 + count_below(word, (cc % 64) as u64);
        proof {
            assert(r as int == rank_of(bits@, wpre@, cc as int));
            lemma_ppos(m, pk as int, cc as int);
        }
        tab_cost(ents, k0s, edv, cc, r, skv, Ghost(bits@), Ghost(wpre@), Ghost(m)).0
    } else {
        match ps_row(c, d, pk, skv, Ghost(m)) {
            Some(t) => {
                let (_, _, cost) = get_t(c, d, t, Ghost(m));
                proof {
                    lemma_tvals(m, t as int);
                    assert(pow10(15) == 1000000000000000) by (compute);
                }
                cost
            },
            None => NO_COST,
        }
    };
    (cost, n)
}

/// Bounds of a cell's partial sums: the count is at most the rows, the sum at most the absolute sum.
proof fn lemma_dsum_bounds(m: M, p: QP, cells: Seq<Cell>, years: Seq<i64>, ny: int, nn: int, lo: int, pos: int, k: int, n: int)
    requires
        0 <= lo <= pos,
        0 <= k < ny, 0 <= n < nn,
        cell_is(m, p, cells[k * nn + n], n, years[k] as int, lo, pos),
    ensures
        cells[k * nn + n].cnt <= pos - lo,
        -(cells[k * nn + n].ab as int) <= cells[k * nn + n].sum <= cells[k * nn + n].ab,
{
    lemma_dsum_le(m, p, n, years[k] as int, lo, pos);
}

/// `dsum` of the count is at most the rows; `|dsum(sum)| <= dsum(abs)`.
pub proof fn lemma_dsum_le(m: M, p: QP, n: int, y: int, lo: int, pos: int)
    requires 0 <= lo <= pos,
    ensures
        0 <= dsum(cnt_f(m, p, n, y), lo, pos) <= pos - lo,
        -dsum(abs_f(m, p, n, y), lo, pos) <= dsum(sum_f(m, p, n, y), lo, pos) <= dsum(abs_f(m, p, n, y), lo, pos),
    decreases pos - lo,
{
    if pos > lo {
        lemma_dsum_le(m, p, n, y, lo, pos - 1);
        lemma_dsum_step(cnt_f(m, p, n, y), lo, pos - 1);
        lemma_dsum_step(sum_f(m, p, n, y), lo, pos - 1);
        lemma_dsum_step(abs_f(m, p, n, y), lo, pos - 1);
        lemma_terms_at(m, p, n, y, pos - 1);
    }
}

} // verus!
