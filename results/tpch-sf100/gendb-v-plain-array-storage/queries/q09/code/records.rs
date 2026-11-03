//! Compact partsupp records of the matching parts, read by the lineitem scan.
//!
//! The bitmap's words are split into `k` chunks of consecutive words (`common::split`); chunk `c` holds a record of
//! 4 `i64` entries (32 bytes) for each matching part row `r` of its words, at the part's rank among the chunk's set
//! bits (`crank`): for `j < 4`, entry `j` is partsupp row `4r + j` (dbgen writes the four suppliers of a part there)
//! when that row belongs to `r`'s part key, names a supplier row `s` inside the supplier table and has a supply cost
//! in `0 .. 2^23` (`rec_entry_ok`): the value `pack(s, cost, slot) = s * 2^32 + cost * 256 + slot`, `slot` being the
//! supplier nation's slot; otherwise the entry is negative and never matches. A lineitem row finds its part's
//! record through the word locations `wl` (`wl_ok`): word `w`'s bits, and its chunk and the chunk's set bits
//! before it.
use vstd::prelude::*;
use crate::agent::common::zeroed::{zeros_i64, zeros_u64};
use std::sync::Arc;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::agent::tables::*;
use crate::agent::lines::*;
use crate::agent::columns::*;
use crate::agent::partmatch::*;
use crate::agent::nations::*;
use crate::agent::common::bits::*;
use crate::agent::common::popc::*;
use crate::agent::common::split::*;

verus! {

/// Supply costs fitting an entry: `0 <= cost < COST_LIMIT` (`2^23`).
pub const COST_LIMIT: i64 = 0x80_0000;

/// The entry of supplier row `s`, supply cost `cost` and slot `slot` (`0 <= slot < 256`).
pub open spec fn pack(s: int, cost: int, slot: int) -> int { s * 0x1_0000_0000 + cost * 256 + slot }

/// Set bits of words `a..b`.
pub open spec fn cnt_words(bits: Seq<u64>, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a { 0 } else { cnt_words(bits, a, b - 1) + count_below(bits[b - 1], 64) }
}

/// Set bits of rows `64 * w0 .. x` (the rank of row `x` among the set bits from word `w0`).
pub open spec fn crank(bits: Seq<u64>, w0: int, x: int) -> int {
    cnt_words(bits, w0, x / 64) + count_below(bits[x / 64], x % 64)
}

/// Entry `x` of the record of part row `r` for partsupp row `q`: a non-negative entry packs the row's supplier row
/// `s`, supply cost and supplier slot.
pub open spec fn rec_entry_ok(x: i64, q: int, r: int, sv: StoresView, sbase: int) -> bool {
    x >= 0 ==> {
        let s = x as int / 0x1_0000_0000;
        &&& 0 <= q < n_ps(sv) && pspk(sv)[q] == pk(sv)[r]
        &&& 0 <= s < n_s(sv) && pssk(sv)[q] as int == sbase + s
        &&& 0 <= psc(sv)[q] < COST_LIMIT
        &&& x as int == pack(s, psc(sv)[q] as int, slot_of(sv, sn(sv)[s]))
    }
}

/// The record of part row `r` is the 4 entries at `4 * e` of `out`.
pub open spec fn rec_ok(out: Seq<i64>, e: int, r: int, sv: StoresView, sbase: int) -> bool {
    &&& 0 <= e && 4 * e + 4 <= out.len()
    &&& forall|j: int| 0 <= j < 4 ==> #[trigger] rec_entry_ok(out[4 * e + j], 4 * r + j, r, sv, sbase)
}

/// The records of chunk `c` (words `w0..w1`): every matching part row of the chunk has its record at its rank.
pub open spec fn chunk_recs_ok(out: Seq<i64>, bits: Seq<u64>, w0: int, w1: int, sv: StoresView, sbase: int) -> bool {
    &&& out.len() == 4 * cnt_words(bits, w0, w1)
    &&& forall|r: int| 64 * w0 <= r < 64 * w1 && #[trigger] word_bit(bits, r) ==> rec_ok(out, crank(bits, w0, r), r, sv, sbase)
}

/// The records of all `k` chunks.
pub open spec fn recs_ok(recs: Seq<Vec<i64>>, bits: Seq<u64>, k: int, sv: StoresView, sbase: int) -> bool {
    &&& recs.len() == k
    &&& forall|c: int| 0 <= c < k ==> #[trigger] chunk_recs_ok(recs[c]@, bits, split(bits.len() as int, k, c),
            split(bits.len() as int, k, c + 1), sv, sbase)
}

/// The location word of word `w`: its chunk `c` (`x / 2^32`) and the chunk's set bits before it (`x % 2^32`).
pub open spec fn wloc_ok(x: u64, bits: Seq<u64>, k: int, w: int) -> bool {
    let c = x as int / 0x1_0000_0000;
    &&& 0 <= c < k
    &&& split(bits.len() as int, k, c) <= w < split(bits.len() as int, k, c + 1)
    &&& x as int % 0x1_0000_0000 == cnt_words(bits, split(bits.len() as int, k, c), w)
}

/// Word locations: for word `w`, its bits at `2w` and its location at `2w + 1`.
pub open spec fn wl_ok(wl: Seq<u64>, bits: Seq<u64>, k: int) -> bool {
    &&& wl.len() == 2 * bits.len()
    &&& forall|w: int| 0 <= w < bits.len() ==> #[trigger] wl[2 * w] == bits[w] && wloc_ok(wl[2 * w + 1], bits, k, w)
}

// ------------------------------------------------------------------------------------------------ counting lemmas

/// Words split: counts add.
pub proof fn lemma_cnt_split(bits: Seq<u64>, a: int, m: int, b: int)
    requires a <= m <= b,
    ensures cnt_words(bits, a, b) == cnt_words(bits, a, m) + cnt_words(bits, m, b),
    decreases b - m,
{
    if b > m {
        lemma_cnt_split(bits, a, m, b - 1);
    }
}

/// Counts are non-negative.
pub proof fn lemma_cnt_nonneg(bits: Seq<u64>, a: int, b: int)
    ensures cnt_words(bits, a, b) >= 0,
    decreases b - a,
{
    if b > a {
        lemma_cnt_nonneg(bits, a, b - 1);
        lemma_count_nonneg(bits[b - 1], 64);
    }
}

/// One row further: the rank grows by the row's bit.
pub proof fn lemma_crank_step(bits: Seq<u64>, w0: int, x: int)
    requires 64 * w0 <= x,
    ensures crank(bits, w0, x + 1) == crank(bits, w0, x) + if bit(bits[x / 64], (x % 64) as u64) { 1int } else { 0int },
{
    let w = x / 64;
    let b = x % 64;
    lemma_count_step(bits[w], b);
    if b == 63 {
        assert((x + 1) / 64 == w + 1 && (x + 1) % 64 == 0);
        assert(count_below(bits[w + 1], 0) == 0);
    } else {
        assert((x + 1) / 64 == w && (x + 1) % 64 == b + 1);
    }
}

/// Ranks do not decrease.
pub proof fn lemma_crank_mono(bits: Seq<u64>, w0: int, x: int, y: int)
    requires 64 * w0 <= x <= y,
    ensures crank(bits, w0, x) <= crank(bits, w0, y),
    decreases y - x,
{
    if y > x {
        lemma_crank_mono(bits, w0, x, y - 1);
        lemma_crank_step(bits, w0, y - 1);
    }
}

/// At a word boundary the rank is the words' count.
pub proof fn lemma_crank_word(bits: Seq<u64>, w0: int, w: int)
    ensures crank(bits, w0, 64 * w) == cnt_words(bits, w0, w),
{
    assert((64 * w) / 64 == w && (64 * w) % 64 == 0);
}

// ------------------------------------------------------------------------------------------------ word locations

/// The word locations, and each chunk's number of set bits (`None` when a chunk has `2^32` or more).
pub fn word_locs(bits: &Vec<u64>, k: usize) -> (r: Option<(Vec<u64>, Vec<usize>)>)
    requires 1 <= k <= 64,
    ensures
        r matches Some((wl, counts)) ==> wl_ok(wl@, bits@, k as int) && counts@.len() == k
            && forall|c: int| 0 <= c < k ==> #[trigger] counts@[c] as int
                == cnt_words(bits@, split(bits@.len() as int, k as int, c), split(bits@.len() as int, k as int, c + 1)),
{
    let pc = match pc_table() { Some(t) => t, None => { return None; } };
    let nw = bits.len();
    if nw >= 0x1000_0000 {
        return None;
    }
    // one zeroed allocation, filled by index: word `w` at `2w`, its location at `2w + 1`
    let mut wl: Vec<u64> = zeros_u64(2 * nw);
    let mut counts: Vec<usize> = Vec::new();
    let mut c: usize = 0;
    while c < k
        invariant
            c <= k, 1 <= k <= 64, nw == bits@.len(), pc_ok(pc@),
            wl@.len() == 2 * nw, nw < 0x1000_0000, counts@.len() == c,
            forall|w: int| 0 <= w < split(nw as int, k as int, c as int) ==> #[trigger] wl@[2 * w] == bits@[w]
                && wloc_ok(wl@[2 * w + 1], bits@, k as int, w),
            forall|cc: int| 0 <= cc < c ==> #[trigger] counts@[cc] as int
                == cnt_words(bits@, split(nw as int, k as int, cc), split(nw as int, k as int, cc + 1)),
        decreases k - c,
    {
        proof { lemma_split(nw as int, k as int, c as int, c + 1); lemma_split(nw as int, k as int, c + 1, k as int); }
        let w0 = split_exec(nw, k, c);
        let w1 = split_exec(nw, k, c + 1);
        let mut cnt: u64 = 0;
        let mut w = w0;
        while w < w1
            invariant
                w0 <= w <= w1 <= nw, nw == bits@.len(), c < k, 1 <= k <= 64, pc_ok(pc@),
                w0 == split(nw as int, k as int, c as int), w1 == split(nw as int, k as int, c + 1),
                wl@.len() == 2 * nw, nw < 0x1000_0000, cnt as int == cnt_words(bits@, w0 as int, w as int), cnt < 0x1_0000_0000,
                forall|x: int| 0 <= x < w ==> #[trigger] wl@[2 * x] == bits@[x] && wloc_ok(wl@[2 * x + 1], bits@, k as int, x),
            decreases w1 - w,
        {
            let word = bits[w];
            let loc: u64 = ((c as u64) << 32u64) | cnt;
            proof {
                let cu = c as u64;
                assert(((cu << 32u64) | cnt) == cu * 0x1_0000_0000 + cnt) by (bit_vector)
                    requires cu < 64, cnt < 0x1_0000_0000;
                assert((c as int * 0x1_0000_0000 + cnt as int) / 0x1_0000_0000 == c as int) by (nonlinear_arith)
                    requires 0 <= cnt < 0x1_0000_0000, 0 <= c;
                assert((c as int * 0x1_0000_0000 + cnt as int) % 0x1_0000_0000 == cnt as int) by (nonlinear_arith)
                    requires 0 <= cnt < 0x1_0000_0000, 0 <= c;
                assert(wloc_ok(loc, bits@, k as int, w as int));
            }
            let ghost wl0 = wl@;
            wl[2 * w] = word;
            wl[2 * w + 1] = loc;
            proof {
                assert(wl@[2 * w as int] == word);
                assert(wl@[2 * w as int + 1] == loc);
                assert forall|x: int| 0 <= x < w implies #[trigger] wl@[2 * x] == wl0[2 * x] && wl@[2 * x + 1] == wl0[2 * x + 1] by {}
            }
            let pcnt = popc_below(word, 63, &pc);
            proof {
                assert(pcnt as int == count_below(word, 64));
                lemma_count_nonneg(word, 64);
            }
            if cnt + pcnt >= 0x1_0000_0000 {
                return None;
            }
            cnt = cnt + pcnt;
            proof {
                assert forall|x: int| 0 <= x < w + 1 implies #[trigger] wl@[2 * x] == bits@[x] && wloc_ok(wl@[2 * x + 1], bits@, k as int, x) by {
                    if x == w {
                        assert(wl@[2 * x] == word && wl@[2 * x + 1] == loc);
                    } else {
                        assert(wl@[2 * x] == wl0[2 * x] && wl@[2 * x + 1] == wl0[2 * x + 1]);
                    }
                }
            }
            w = w + 1;
        }
        counts.push(cnt as usize);
        c = c + 1;
    }
    proof { lemma_split(nw as int, k as int, k as int, k as int); }
    Some((wl, counts))
}

// ------------------------------------------------------------------------------------------------ records

/// One task building the records of chunk words `w0..w1`.
pub struct RecTask {
    pub c: Cols,
    pub bits: Arc<Vec<u64>>,
    pub sslot: Arc<Vec<u8>>,
    pub sbase: i64,
    pub pbase: i64,
    pub w0: usize,
    pub w1: usize,
    pub out: Vec<i64>,
    pub sv: Ghost<StoresView>,
}

/// The inputs of a record task.
pub open spec fn rec_inputs_ok(c: Cols, bits: Seq<u64>, sslot: Seq<u8>, sbase: i64, pbase: i64, sv: StoresView) -> bool {
    &&& cols_ok(c, sv)
    &&& positional(pk(sv), pbase as int) && 0 <= pbase && pbase + n_p(sv) < i64::MAX
    &&& bits.len() == nwords(n_p(sv))
    &&& forall|u: int| 0 <= u < 64 * bits.len() && #[trigger] word_bit(bits, u) ==> u < n_p(sv)
    &&& sslot.len() == n_s(sv) && forall|s: int| 0 <= s < n_s(sv) ==> #[trigger] sslot[s] as int == slot_of(sv, sn(sv)[s])
    &&& 0 <= sbase && sbase + n_s(sv) < i64::MAX && n_s(sv) < 0x8000_0000
    &&& 4 * n_p(sv) + 8 < usize::MAX
}

/// The entry of partsupp row `q` whose supplier row is `s` (`-1` when its supply cost does not fit).
fn pack_entry(c: &Cols, sslot: &Vec<u8>, q: usize, s: usize, Ghost(sv): Ghost<StoresView>, Ghost(r): Ghost<int>,
    Ghost(sbase): Ghost<int>) -> (x: i64)
    requires cols_ok(*c, sv), q < c.nps, s < c.ns, c.ns < 0x8000_0000, sslot@.len() == c.ns,
        forall|t: int| 0 <= t < n_s(sv) ==> #[trigger] sslot@[t] as int == slot_of(sv, sn(sv)[t]),
        pspk(sv)[q as int] == pk(sv)[r], pssk(sv)[q as int] as int == sbase + s,
    ensures rec_entry_ok(x, q as int, r, sv, sbase),
    no_unwind
{
    let cost = c.pscost[q];
    if cost < 0 || cost >= COST_LIMIT as i128 {
        return -1;
    }
    let slot = sslot[s];
    proof {
        if has_key(nk(sv), sn(sv)[s as int]) {
            lemma_key_row(nk(sv), sn(sv)[s as int]);
            crate::agent::answer::lemma_nrep(sv, key_row(nk(sv), sn(sv)[s as int]));
        }
    }
    let x: i64 = ((s as i64) << 32u64) | ((cost as i64) << 8u64) | (slot as i64);
    proof {
        let su = s as i64;
        let cu = cost as i64;
        let tu = slot as i64;
        assert(((su << 32u64) | (cu << 8u64) | tu) == su * 0x1_0000_0000 + cu * 256 + tu) by (bit_vector)
            requires 0 <= su < 0x8000_0000, 0 <= cu < 0x80_0000, 0 <= tu < 256;
        assert(x as int / 0x1_0000_0000 == s as int) by (nonlinear_arith)
            requires x as int == s * 0x1_0000_0000 + cost * 256 + slot, 0 <= cost < 0x80_0000, 0 <= slot < 256, 0 <= s;
    }
    x
}

impl WorkerTask for RecTask {
    type Output = Vec<i64>;

    open spec fn pre(&self) -> bool {
        &&& rec_inputs_ok(self.c, self.bits@, self.sslot@, self.sbase, self.pbase, self.sv@)
        &&& self.w0 <= self.w1 <= self.bits@.len()
        &&& self.out@.len() == 4 * cnt_words(self.bits@, self.w0 as int, self.w1 as int)
    }

    open spec fn post(&self, out: Vec<i64>) -> bool {
        chunk_recs_ok(out@, self.bits@, self.w0 as int, self.w1 as int, self.sv@, self.sbase as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.w0 as u64, self.w1 as u64)
    }

    fn run(self) -> (out: Vec<i64>) {
        let RecTask { c, bits, sslot, sbase, pbase, w0, w1, out, sv } = self;
        let ghost sv = sv@;
        let bits: &Vec<u64> = &*bits;
        let sslot: &Vec<u8> = &*sslot;
        let mut out = out;
        let olen = out.len();
        let ghost bv = bits@;
        let mut e: usize = 0;
        let mut x = w0 * 64;
        let xe = w1 * 64;
        proof {
            lemma_crank_word(bv, w0 as int, w0 as int);
            lemma_crank_word(bv, w0 as int, w1 as int);
        }
        while x < xe
            invariant
                rec_inputs_ok(c, bv, sslot@, sbase, pbase, sv), bits@ == bv, w0 <= w1 <= bv.len(), xe == w1 * 64,
                w0 * 64 <= x <= xe, out@.len() == 4 * cnt_words(bv, w0 as int, w1 as int), olen == out@.len(),
                e as int == crank(bv, w0 as int, x as int), crank(bv, w0 as int, xe as int) == cnt_words(bv, w0 as int, w1 as int),
                forall|r: int| 64 * w0 <= r < x && #[trigger] word_bit(bv, r) ==> crank(bv, w0 as int, r) < e
                    && rec_ok(out@, crank(bv, w0 as int, r), r, sv, sbase as int),
            decreases xe - x,
        {
            let word = bits[x / 64];
            proof {
                lemma_crank_step(bv, w0 as int, x as int);
                lemma_crank_mono(bv, w0 as int, x + 1, xe as int);
            }
            if (word >> ((x % 64) as u64)) & 1 == 1 {
                let r = x;
                proof {
                    assert(word_bit(bv, r as int));
                    assert(r < n_p(sv));
                }
                // positional part keys: row `r` holds key `pbase + r` (no read of the key column)
                let pkr = pbase + r as i64;
                proof { assert(pk(sv)[r as int] as int == pbase + r); }
                let ghost before = out@;
                let mut j: usize = 0;
                while j < 4
                    invariant
                        j <= 4, rec_inputs_ok(c, bv, sslot@, sbase, pbase, sv), r < n_p(sv), pkr == pk(sv)[r as int],
                        4 * e + 4 <= out@.len(), out@.len() == before.len(), olen == out@.len(),
                        forall|i: int| 0 <= i < out@.len() && !(4 * e <= i < 4 * e + 4) ==> #[trigger] out@[i] == before[i],
                        forall|jj: int| 0 <= jj < j ==> #[trigger] rec_entry_ok(out@[4 * e + jj], 4 * r + jj, r as int, sv, sbase as int),
                    decreases 4 - j,
                {
                    let q = 4 * r + j;
                    let mut val: i64 = -1;
                    if q < c.nps {
                        let sk2 = c.pssupp[q];
                        if c.pspart[q] == pkr && sk2 >= sbase && sk2 - sbase < c.ns as i64 {
                            let s = (sk2 - sbase) as usize;
                            val = pack_entry(&c, sslot, q, s, Ghost(sv), Ghost(r as int), Ghost(sbase as int));
                        }
                    }
                    out[4 * e + j] = val;
                    proof {
                        assert forall|jj: int| 0 <= jj < j + 1 implies #[trigger] rec_entry_ok(out@[4 * e + jj],
                            4 * r + jj, r as int, sv, sbase as int) by {
                            if jj == j {
                                assert(out@[4 * e + jj] == val);
                            }
                        }
                    }
                    j = j + 1;
                }
                proof {
                    assert forall|r2: int| 64 * w0 <= r2 < x + 1 && #[trigger] word_bit(bv, r2) implies crank(bv, w0 as int, r2) < e + 1
                        && rec_ok(out@, crank(bv, w0 as int, r2), r2, sv, sbase as int) by {
                        if r2 < x {
                            let e2 = crank(bv, w0 as int, r2);
                            assert(rec_ok(before, e2, r2, sv, sbase as int));
                            assert forall|jj: int| 0 <= jj < 4 implies #[trigger] rec_entry_ok(out@[4 * e2 + jj], 4 * r2 + jj, r2, sv, sbase as int) by {
                                assert(out@[4 * e2 + jj] == before[4 * e2 + jj]);
                            }
                        }
                    }
                }
                e = e + 1;
            }
            x = x + 1;
        }
        out
    }
}


/// A chunk has at most 64 set bits per word.
pub proof fn lemma_cnt_le(bits: Seq<u64>, a: int, b: int)
    requires a <= b,
    ensures cnt_words(bits, a, b) <= 64 * (b - a),
    decreases b - a,
{
    if b > a {
        lemma_cnt_le(bits, a, b - 1);
        lemma_count_nonneg(bits[b - 1], 64);
    }
}

/// The records of the `k` chunks, one task per chunk (the calling thread runs a single task).
pub fn build_records(c: &Cols, bits: Arc<Vec<u64>>, sslot: Arc<Vec<u8>>, sbase: i64, pbase: i64, counts: &Vec<usize>, k: usize,
    dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>) -> (r: Result<Vec<Vec<i64>>, WorkerFailure>)
    requires
        rec_inputs_ok(*c, bits@, sslot@, sbase, pbase, sv), 1 <= k <= MAX_WORKERS, n_p(sv) < 0x800_0000,
        counts@.len() == k,
        forall|j: int| 0 <= j < k ==> #[trigger] counts@[j] as int
            == cnt_words(bits@, split(bits@.len() as int, k as int, j), split(bits@.len() as int, k as int, j + 1)),
    ensures r matches Ok(recs) ==> recs_ok(recs@, bits@, k as int, sv, sbase as int),
{
    let nw = bits.len();
    let mut tasks: Vec<RecTask> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            t <= k, 1 <= k <= MAX_WORKERS, tasks@.len() == t, nw == bits@.len(), n_p(sv) < 0x800_0000,
            rec_inputs_ok(*c, bits@, sslot@, sbase, pbase, sv), counts@.len() == k,
            forall|j: int| 0 <= j < k ==> #[trigger] counts@[j] as int
                == cnt_words(bits@, split(nw as int, k as int, j), split(nw as int, k as int, j + 1)),
            forall|j: int| 0 <= j < t ==> (#[trigger] tasks@[j]).pre() && tasks@[j].sv@ == sv && tasks@[j].bits@ == bits@
                && tasks@[j].sbase == sbase && tasks@[j].pbase == pbase
                && tasks@[j].w0 == split(nw as int, k as int, j) && tasks@[j].w1 == split(nw as int, k as int, j + 1),
        decreases k - t,
    {
        proof { lemma_split(nw as int, k as int, t as int, t + 1); lemma_split(nw as int, k as int, t + 1, k as int); }
        let w0 = split_exec(nw, k, t);
        let w1 = split_exec(nw, k, t + 1);
        proof {
            lemma_cnt_le(bits@, w0 as int, w1 as int);
            assert(nw as int == nwords(n_p(sv)));
        }
        let cnt = counts[t];
        let task = RecTask { c: *c, bits: bits.clone(), sslot: sslot.clone(), sbase, pbase, w0, w1, out: zeros_i64(4 * cnt), sv: Ghost(sv) };
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = if k == 1 {
        let task = tasks.pop().unwrap();
        assert(task == tv[0]);
        let o = task.run();
        let mut v: Vec<Vec<i64>> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => { return Err(e); },
        }
    };
    proof {
        assert(outs@.len() == k);
        assert forall|j: int| 0 <= j < k implies #[trigger] chunk_recs_ok(outs@[j]@, bits@, split(bits@.len() as int, k as int, j),
            split(bits@.len() as int, k as int, j + 1), sv, sbase as int) by {
            assert(tv[j].post(outs@[j]));
        }
    }
    Ok(outs)
}

} // verus!
