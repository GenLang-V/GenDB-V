//! The part pass (adapted from an admitted query's part pass): one bit per part row for "`p_type` starts with the
//! characters `PROMO`" (`PartTask`, one task per range of 64-row words), and whether every part row is positional
//! (`p_partkey == row + 1`), which lets a lineitem row find its part row by subtraction.
//!
//! - `pbits_ok`: bit `r` of the words (bit `r % 64` of word `r / 64`) is `line::promo(sv, r)`;
//! - `pos_all`: every part row `r` has the key `r + 1`.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::link::query::{text_at, text_wf};
use crate::spec::chars::is_cont;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::common::bits::*;
use crate::agent::common::like_prefix::starts_with_chars;

verus! {

/// The promotion bits of every part row.
pub open spec fn pbits_ok(bits: Seq<u64>, sv: StoresView) -> bool {
    &&& 64 * bits.len() >= n_p(sv)
    &&& forall|r: int| 0 <= r < n_p(sv) ==> #[trigger] word_bit(bits, r) == promo(sv, r)
}

/// Every part row is positional.
pub open spec fn pos_all(sv: StoresView) -> bool {
    forall|r: int| 0 <= r < n_p(sv) ==> #[trigger] p_key(sv)[r] as int == r + 1
}

// ------------------------------------------------------------------------------------------------ one task

/// The part columns a task reads.
#[derive(Clone, Copy)]
pub struct PartCols {
    pub key: &'static [i64],
    pub offs: &'static [i64],
    pub bytes: &'static [u8],
    pub nb: usize,
    pub np: usize,
}

pub open spec fn part_cols_ok(c: PartCols, sv: StoresView) -> bool {
    &&& c.key@ == p_key(sv)
    &&& tview(c.offs@, c.bytes@) == ptype_col(sv)
    &&& text_wf(ptype_col(sv), n_p(sv) as int)
    &&& c.nb == c.bytes@.len()
    &&& c.np == n_p(sv)
}

/// Whether part row `r`'s type starts with the characters `PROMO`: its first five bytes are `PROMO`, followed by
/// its end or a byte that is not a continuation byte.
fn promo_at(c: &PartCols, r: usize, Ghost(sv): Ghost<StoresView>) -> (b: bool)
    requires part_cols_ok(*c, sv), r < c.np,
    ensures b == promo(sv, r as int),
    no_unwind
{
    let ghost t = tview(c.offs@, c.bytes@);
    proof { assert(0 <= t.offsets[r as int] <= t.offsets[r + 1] <= t.bytes.len()); }
    let s = c.offs[r] as usize;
    let e = c.offs[r + 1] as usize;
    let ghost v = c.bytes@.subrange(s as int, e as int);
    let ghost lit = promo_lit();
    assert(v == p_type(sv, r as int));
    if e - s < 5 {
        return false;
    }
    let b = c.bytes;
    let head = b[s] == 80u8 && b[s + 1] == 82u8 && b[s + 2] == 79u8 && b[s + 3] == 77u8 && b[s + 4] == 79u8;
    proof {
        assert(v[0] == b@[s as int] && v[1] == b@[s + 1] && v[2] == b@[s + 2] && v[3] == b@[s + 3] && v[4] == b@[s + 4]);
        if head {
            assert(v.subrange(0, 5) =~= lit);
        } else if v.subrange(0, 5) == lit {
            assert(v.subrange(0, 5)[0] == 80u8 && v.subrange(0, 5)[1] == 82u8 && v.subrange(0, 5)[2] == 79u8);
            assert(v.subrange(0, 5)[3] == 77u8 && v.subrange(0, 5)[4] == 79u8);
        }
    }
    if !head {
        return false;
    }
    if e - s == 5 {
        return true;
    }
    let x = b[s + 5];
    assert(v[5] == x);
    !(0x80u8 <= x && x < 0xC0u8)
}

/// One word: the rows `64 w .. min(64 w + 64, np)`.
fn part_word(c: &PartCols, w: usize, Ghost(sv): Ghost<StoresView>) -> (r: (u64, bool))
    requires part_cols_ok(*c, sv), 64 * w < c.np,
    ensures
        forall|u: u64| u < 64 && 64 * w + u < n_p(sv) ==> #[trigger] bit(r.0, u) == promo(sv, 64 * w + u),
        r.1 ==> forall|u: u64| u < 64 && 64 * w + u < n_p(sv) ==> #[trigger] p_key(sv)[64 * w + u] as int == 64 * w + u + 1,
    no_unwind
{
    let lo = 64 * w;
    let hi = if c.np - lo > 64 { lo + 64 } else { c.np };
    let mut word: u64 = 0;
    let mut positional = true;
    let mut k = lo;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while k < hi
        invariant
            part_cols_ok(*c, sv), lo == 64 * w, lo <= k <= hi <= c.np, hi <= lo + 64,
            forall|u: u64| u < 64 ==> #[trigger] bit(word, u) == (lo + u < k && promo(sv, lo + u)),
            positional ==> forall|u: u64| u < 64 && lo + u < k ==> #[trigger] p_key(sv)[lo + u] as int == lo + u + 1,
        decreases hi - k,
    {
        let p = promo_at(c, k, Ghost(sv));
        let x: u64 = if p { 1 } else { 0 };
        let t = (k - lo) as u64;
        let ghost w0 = word;
        word = word | (x << t);
        let pos_k = (c.key[k] as i128) == (k as i128) + 1;
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(word, u) == (lo + u < k + 1 && promo(sv, lo + u)) by {
                lemma_bit_set(w0, x, t, u);
            }
            if positional && pos_k {
                assert forall|u: u64| u < 64 && lo + u < k + 1 implies #[trigger] p_key(sv)[lo + u] as int == lo + u + 1 by {
                    if lo + u == k {
                        assert(c.key@[k as int] == p_key(sv)[k as int]);
                    }
                }
            }
        }
        positional = positional && pos_k;
        k = k + 1;
    }
    (word, positional)
}

/// One task: the words `w_lo..w_hi`.
pub struct PartTask {
    pub cols: PartCols,
    pub w_lo: usize,
    pub w_hi: usize,
    pub out: Vec<u64>,
    pub sv: Ghost<StoresView>,
}

/// The task's words and positional flag.
pub open spec fn part_words_ok(words: Seq<u64>, positional: bool, sv: StoresView, w_lo: int, w_hi: int) -> bool {
    &&& words.len() == w_hi - w_lo
    &&& forall|r: int| 64 * w_lo <= r < 64 * w_hi && r < n_p(sv) ==>
            #[trigger] bit(words[r / 64 - w_lo], (r % 64) as u64) == promo(sv, r)
    &&& positional ==> forall|r: int| 64 * w_lo <= r < 64 * w_hi && r < n_p(sv) ==> #[trigger] p_key(sv)[r] as int == r + 1
}

impl WorkerTask for PartTask {
    type Output = (Vec<u64>, bool);

    open spec fn pre(&self) -> bool {
        &&& part_cols_ok(self.cols, self.sv@)
        &&& self.w_lo <= self.w_hi
        &&& 64 * self.w_hi <= self.cols.np + 63
        &&& self.out@.len() == self.w_hi - self.w_lo
    }

    open spec fn post(&self, out: (Vec<u64>, bool)) -> bool {
        part_words_ok(out.0@, out.1, self.sv@, self.w_lo as int, self.w_hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.w_lo as u64, self.w_hi as u64)
    }

    fn run(self) -> (out: (Vec<u64>, bool)) {
        let c = self.cols;
        let ghost sv = self.sv@;
        let mut out = self.out;
        let mut positional = true;
        let mut w = self.w_lo;
        while w < self.w_hi
            invariant
                part_cols_ok(c, sv), self.w_lo <= w <= self.w_hi, 64 * self.w_hi <= c.np + 63,
                out@.len() == self.w_hi - self.w_lo,
                forall|r: int| 64 * self.w_lo <= r < 64 * w && r < n_p(sv) ==>
                    #[trigger] bit(out@[r / 64 - self.w_lo], (r % 64) as u64) == promo(sv, r),
                positional ==> forall|r: int| 64 * self.w_lo <= r < 64 * w && r < n_p(sv) ==> #[trigger] p_key(sv)[r] as int == r + 1,
            decreases self.w_hi - w,
        {
            let (word, pos) = part_word(&c, w, Ghost(sv));
            let ghost out0 = out@;
            out[w - self.w_lo] = word;
            proof {
                assert forall|r: int| 64 * self.w_lo <= r < 64 * (w + 1) && r < n_p(sv) implies
                    #[trigger] bit(out@[r / 64 - self.w_lo], (r % 64) as u64) == promo(sv, r) by {
                    if r < 64 * w {
                        assert(out@[r / 64 - self.w_lo] == out0[r / 64 - self.w_lo]);
                    } else {
                        assert(r / 64 == w);
                        let u = (r - 64 * w) as u64;
                        assert(r % 64 == u);
                        assert(bit(word, u) == promo(sv, 64 * w + u));
                    }
                }
                if positional && pos {
                    assert forall|r: int| 64 * self.w_lo <= r < 64 * (w + 1) && r < n_p(sv) implies #[trigger] p_key(sv)[r] as int == r + 1 by {
                        if r >= 64 * w {
                            let u = (r - 64 * w) as u64;
                            assert(p_key(sv)[64 * w + u] as int == 64 * w + u + 1);
                        }
                    }
                }
            }
            positional = positional && pos;
            w = w + 1;
        }
        (out, positional)
    }
}

// ------------------------------------------------------------------------------------------------ the pass

/// Start of part `k` when `n` items are split into `w` parts: `k * (n / w) + min(k, n % w)`.
pub open spec fn split_at(n: int, w: int, k: int) -> int {
    k * (n / w) + if k < n % w { k } else { n % w }
}

/// The part boundaries are non-decreasing and end at `n`.
pub proof fn lemma_split(n: int, w: int, k: int)
    requires 0 <= n, 1 <= w, 0 <= k < w,
    ensures
        split_at(n, w, k + 1) == split_at(n, w, k) + n / w + if k < n % w { 1int } else { 0int },
        0 <= split_at(n, w, k) <= split_at(n, w, k + 1) <= n,
        split_at(n, w, 0) == 0,
        split_at(n, w, w) == n,
{
    let (q, r) = (n / w, n % w);
    assert(n == w * q + r && 0 <= r < w && 0 <= q) by (nonlinear_arith) requires q == n / w, r == n % w, 0 <= n, 1 <= w;
    assert((k + 1) * q == k * q + q) by (nonlinear_arith);
    assert(w * q == q * w) by (nonlinear_arith);
    assert(0 <= k * q) by (nonlinear_arith) requires 0 <= k, 0 <= q;
    assert((k + 1) * q <= w * q) by (nonlinear_arith) requires k + 1 <= w, 0 <= q;
    assert(0 * q == 0);
}

/// The part pass: the promotion bits of all part rows, and whether every part row is positional.
pub fn part_pass(pc: PartCols, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>)
    -> (r: Result<(Vec<u64>, bool), WorkerFailure>)
    requires part_cols_ok(pc, sv), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok((bits, pos)) ==> pbits_ok(bits@, sv) && (pos ==> pos_all(sv)),
{
    let nw = pc.np / 64 + if pc.np % 64 != 0 { 1 } else { 0 };
    let q = nw / workers;
    let rm = nw % workers;
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut w_lo: usize = 0;
    let mut k: usize = 0;
    while k < workers
        invariant
            part_cols_ok(pc, sv), 1 <= workers <= MAX_WORKERS, k <= workers,
            nw == pc.np / 64 + if pc.np % 64 != 0 { 1int } else { 0int }, q == nw / workers, rm == nw % workers,
            tasks@.len() == k,
            w_lo == split_at(nw as int, workers as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].sv@ == sv
                && tasks@[t].w_lo == split_at(nw as int, workers as int, t)
                && tasks@[t].w_hi == split_at(nw as int, workers as int, t + 1),
        decreases workers - k,
    {
        proof { lemma_split(nw as int, workers as int, k as int); }
        let w_hi = w_lo + q + if k < rm { 1 } else { 0 };
        assert(64 * w_hi <= pc.np + 63);
        let task = PartTask { cols: pc, w_lo, w_hi, out: vec![0u64; w_hi - w_lo], sv: Ghost(sv) };
        tasks.push(task);
        w_lo = w_hi;
        k = k + 1;
    }
    let ghost tasks0 = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let ghost outs0 = outs@;
    proof {
        assert forall|u: int| 0 <= u < workers implies part_words_ok(#[trigger] outs0[u].0@, outs0[u].1, sv,
            split_at(nw as int, workers as int, u), split_at(nw as int, workers as int, u + 1)) by {
            assert(tasks0[u].post(outs0[u]));
        }
    }
    let mut outs = outs;
    let mut bits: Vec<u64> = Vec::with_capacity(nw);
    let mut pos = true;
    let mut t: usize = 0;
    proof { lemma_split(nw as int, workers as int, 0); }
    while t < workers
        invariant
            part_cols_ok(pc, sv), 1 <= workers, t <= workers, outs0.len() == workers,
            nw == pc.np / 64 + if pc.np % 64 != 0 { 1int } else { 0int },
            outs@ == outs0.subrange(t as int, workers as int),
            bits@.len() == split_at(nw as int, workers as int, t as int),
            forall|u: int| 0 <= u < workers ==> part_words_ok(#[trigger] outs0[u].0@, outs0[u].1, sv,
                split_at(nw as int, workers as int, u), split_at(nw as int, workers as int, u + 1)),
            forall|r: int| 0 <= r < 64 * split_at(nw as int, workers as int, t as int) && r < n_p(sv) ==>
                #[trigger] word_bit(bits@, r) == promo(sv, r),
            pos ==> forall|r: int| 0 <= r < 64 * split_at(nw as int, workers as int, t as int) && r < n_p(sv)
                ==> #[trigger] p_key(sv)[r] as int == r + 1,
        decreases workers - t,
    {
        proof { lemma_split(nw as int, workers as int, t as int); }
        let ghost (wl, wh) = (split_at(nw as int, workers as int, t as int), split_at(nw as int, workers as int, t + 1));
        let (mut w, p) = outs.remove(0);
        assert((w@, p) == (outs0[t as int].0@, outs0[t as int].1));
        let ghost bits0 = bits@;
        let ghost w0 = w@;
        assert(part_words_ok(w0, p, sv, wl, wh));
        bits.append(&mut w);
        proof {
            assert(bits@ == bits0 + w0);
            assert forall|r: int| 0 <= r < 64 * wh && r < n_p(sv) implies #[trigger] word_bit(bits@, r) == promo(sv, r) by {
                if r < 64 * wl {
                    assert(word_bit(bits0, r) == promo(sv, r));
                    assert(r / 64 < wl);
                    assert(bits@[r / 64] == bits0[r / 64]);
                } else {
                    assert(r / 64 >= wl);
                    assert(bits@[r / 64] == w0[r / 64 - wl]);
                    assert(bit(w0[r / 64 - wl], (r % 64) as u64) == promo(sv, r));
                }
            }
            if pos && p {
                assert forall|r: int| 0 <= r < 64 * wh && r < n_p(sv) implies #[trigger] p_key(sv)[r] as int == r + 1 by {
                    if r >= 64 * wl {
                        assert(p_key(sv)[r] as int == r + 1);
                    }
                }
            }
            assert(outs@ == outs0.subrange(t + 1, workers as int));
        }
        pos = pos && p;
        t = t + 1;
    }
    proof {
        lemma_split(nw as int, workers as int, (workers - 1) as int);
        assert(pc.np <= 64 * nw);
        assert forall|r: int| 0 <= r < n_p(sv) implies #[trigger] word_bit(bits@, r) == promo(sv, r) by {
            assert(r < 64 * nw);
        }
        if pos {
            assert forall|r: int| 0 <= r < n_p(sv) implies #[trigger] p_key(sv)[r] as int == r + 1 by {
                assert(r < 64 * nw);
            }
        }
    }
    Ok((bits, pos))
}

} // verus!
