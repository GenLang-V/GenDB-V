//! The part pass: one bit per part row for "`p_brand = $1 AND p_container = $2`" (`joined::sel`), computed by
//! `PartTask`s over ranges of 64-row words (bit `r % 64` of word `r / 64` is row `r`; bits past the last row are 0).
//!
//! A text value equals a parameter when the lengths agree and every byte agrees; the bytes are compared without
//! early exit (an OR of XORs), so the loop has no data-dependent branch. The container is compared only for rows
//! whose brand matches.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::link::query::{text_at, text_wf};
use crate::spec::ast::Literal;
use crate::agent::tables::*;
use crate::agent::joined::{sel, pb, pc};
use crate::agent::cols::*;
use crate::agent::common::bits::*;

verus! {

/// Bit `r` of the words is `sel(r)` for every row `r < np`, and clear for the rows past the last.
pub open spec fn pbits_ok(bits: Seq<u64>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& 64 * bits.len() >= n_p(sv)
    &&& 64 * bits.len() < n_p(sv) + 64
    &&& forall|r: int| 0 <= r < 64 * bits.len() ==> #[trigger] word_bit(bits, r) == (r < n_p(sv) && sel(sv, ps, r))
}

// ------------------------------------------------------------------------------------------------ one row

/// The part columns a task reads, and the parameters' bytes (`pbn`, `pcn`: their lengths).
#[derive(Clone, Copy)]
pub struct PartCols {
    pub b_offs: &'static [i64],
    pub b_bytes: &'static [u8],
    pub c_offs: &'static [i64],
    pub c_bytes: &'static [u8],
    pub np: usize,
    pub b_nb: usize,
    pub c_nb: usize,
    pub pb: &'static [u8],
    pub pbn: usize,
    pub pc: &'static [u8],
    pub pcn: usize,
}

pub open spec fn part_cols_ok(c: PartCols, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& tview(c.b_offs@, c.b_bytes@) == brand_col(sv) && text_wf(brand_col(sv), n_p(sv) as int)
    &&& tview(c.c_offs@, c.c_bytes@) == cont_col(sv) && text_wf(cont_col(sv), n_p(sv) as int)
    &&& c.np == n_p(sv)
    &&& c.b_nb == c.b_bytes@.len() && c.c_nb == c.c_bytes@.len()
    &&& c.pb@ == pb(ps) && c.pbn == c.pb@.len()
    &&& c.pc@ == pc(ps) && c.pcn == c.pc@.len()
}

/// An OR of byte differences is zero exactly when the accumulator was zero and the bytes agree.
proof fn lemma_xor_or(acc: u8, x: u8, y: u8)
    ensures ((acc | (x ^ y)) == 0) == (acc == 0 && x == y),
{
    assert(((acc | (x ^ y)) == 0u8) == (acc == 0u8 && x == y)) by (bit_vector);
}

/// Whether value `r` of the text column (`offs`, `bytes`) is exactly the `n` bytes `lit`.
fn text_is(offs: &'static [i64], bytes: &'static [u8], nb: usize, r: usize, lit: &'static [u8], n: usize, Ghost(np): Ghost<int>) -> (b: bool)
    requires text_wf(tview(offs@, bytes@), np), r < np, n == lit@.len(), nb == bytes@.len(),
    ensures b == (text_at(tview(offs@, bytes@), r as int) == lit@),
    no_unwind
{
    let ghost t = tview(offs@, bytes@);
    proof { assert(0 <= t.offsets[r as int] <= t.offsets[r + 1] <= t.bytes.len()); }
    let s0 = offs[r];
    let e0 = offs[r + 1];
    assert(0 <= s0 <= e0 <= nb);
    let s = s0 as usize;
    let e = e0 as usize;
    assert(s as int == s0 as int && e as int == e0 as int);
    let ghost v = bytes@.subrange(s as int, e as int);
    assert(v == text_at(t, r as int));
    if e - s != n {
        assert(v.len() != lit@.len());
        return false;
    }
    // quick reject on the last byte (values of one length usually differ there first)
    if n > 0 && bytes[e - 1] != lit[n - 1] {
        assert(v[n - 1] != lit@[n - 1]);
        return false;
    }
    let mut acc: u8 = 0;
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n, e - s == n, s <= e, e <= bytes@.len(), n == lit@.len(),
            v == bytes@.subrange(s as int, e as int),
            (acc == 0) == (forall|q: int| 0 <= q < j ==> #[trigger] v[q] == lit@[q]),
        decreases n - j,
    {
        let x = bytes[s + j];
        let y = lit[j];
        proof {
            lemma_xor_or(acc, x, y);
            assert(v[j as int] == x);
            if acc == 0 && x == y {
                assert forall|q: int| 0 <= q < j + 1 implies #[trigger] v[q] == lit@[q] by {}
            }
        }
        acc = acc | (x ^ y);
        j = j + 1;
    }
    proof {
        if acc == 0 {
            assert(v =~= lit@);
        } else {
            let q = choose|q: int| 0 <= q < n && #[trigger] v[q] != lit@[q];
            assert(v[q] != lit@[q]);
        }
    }
    acc == 0
}

/// Whether part row `r` is selected: the brand, then (only when it matches) the container.
fn sel_at(c: &PartCols, r: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (b: bool)
    requires part_cols_ok(*c, sv, ps), r < c.np,
    ensures b == sel(sv, ps, r as int),
    no_unwind
{
    let bm = text_is(c.b_offs, c.b_bytes, c.b_nb, r, c.pb, c.pbn, Ghost(n_p(sv) as int));
    if !bm {
        return false;
    }
    text_is(c.c_offs, c.c_bytes, c.c_nb, r, c.pc, c.pcn, Ghost(n_p(sv) as int))
}

// ------------------------------------------------------------------------------------------------ one task

/// One word: the rows `64 w .. min(64 w + 64, np)`.
fn part_word(c: &PartCols, w: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (word: u64)
    requires part_cols_ok(*c, sv, ps), 64 * w < c.np,
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(word, u) == (64 * w + u < n_p(sv) && sel(sv, ps, 64 * w + u)),
    no_unwind
{
    let lo = 64 * w;
    let hi = if c.np - lo > 64 { lo + 64 } else { c.np };
    let mut word: u64 = 0;
    let mut k = lo;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while k < hi
        invariant
            part_cols_ok(*c, sv, ps), lo == 64 * w, lo <= k <= hi <= c.np, hi <= lo + 64,
            hi == c.np || hi == lo + 64,
            forall|u: u64| u < 64 ==> #[trigger] bit(word, u) == (lo + u < k && sel(sv, ps, lo + u)),
        decreases hi - k,
    {
        let p = sel_at(c, k, Ghost(sv), Ghost(ps));
        let x: u64 = if p { 1 } else { 0 };
        let t = (k - lo) as u64;
        let ghost w0 = word;
        word = word | (x << t);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(word, u) == (lo + u < k + 1 && sel(sv, ps, lo + u)) by {
                lemma_bit_set(w0, x, t, u);
            }
        }
        k = k + 1;
    }
    word
}

/// One task: the words `w_lo..w_hi`, written into `out` (one slot per word).
pub struct PartTask {
    pub cols: PartCols,
    pub w_lo: usize,
    pub w_hi: usize,
    pub out: Vec<u64>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

/// The task's words.
pub open spec fn part_words_ok(words: Seq<u64>, sv: StoresView, ps: Seq<Literal>, w_lo: int, w_hi: int) -> bool {
    &&& words.len() == w_hi - w_lo
    &&& forall|r: int| 64 * w_lo <= r < 64 * w_hi ==>
            #[trigger] bit(words[r / 64 - w_lo], (r % 64) as u64) == (r < n_p(sv) && sel(sv, ps, r))
}

/// The words `w_lo..w_hi` (each at least partly inside the table).
fn part_words(c: &PartCols, w_lo: usize, w_hi: usize, out: &mut Vec<u64>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    requires part_cols_ok(*c, sv, ps), w_lo <= w_hi, 64 * w_hi <= c.np + 63, old(out)@.len() == w_hi - w_lo,
    ensures part_words_ok(final(out)@, sv, ps, w_lo as int, w_hi as int),
    no_unwind
{
    let mut w = w_lo;
    while w < w_hi
        invariant
            part_cols_ok(*c, sv, ps), w_lo <= w <= w_hi, 64 * w_hi <= c.np + 63,
            out@.len() == w_hi - w_lo,
            forall|r: int| 64 * w_lo <= r < 64 * w ==>
                #[trigger] bit(out@[r / 64 - w_lo], (r % 64) as u64) == (r < n_p(sv) && sel(sv, ps, r)),
        decreases w_hi - w,
    {
        let word = part_word(c, w, Ghost(sv), Ghost(ps));
        let ghost out0 = out@;
        out[w - w_lo] = word;
        proof {
            assert forall|r: int| 64 * w_lo <= r < 64 * (w + 1) implies
                #[trigger] bit(out@[r / 64 - w_lo], (r % 64) as u64) == (r < n_p(sv) && sel(sv, ps, r)) by {
                if r < 64 * w {
                    assert(out@[r / 64 - w_lo] == out0[r / 64 - w_lo]);
                } else {
                    assert(r / 64 == w);
                    let u = (r - 64 * w) as u64;
                    assert(r % 64 == u);
                    assert(bit(word, u) == (64 * w + u < n_p(sv) && sel(sv, ps, 64 * w + u)));
                }
            }
        }
        w = w + 1;
    }
}

impl WorkerTask for PartTask {
    type Output = Vec<u64>;

    open spec fn pre(&self) -> bool {
        &&& part_cols_ok(self.cols, self.sv@, self.ps@)
        &&& self.w_lo <= self.w_hi
        &&& 64 * self.w_hi <= self.cols.np + 63
        &&& self.out@.len() == self.w_hi - self.w_lo
    }

    open spec fn post(&self, out: Vec<u64>) -> bool {
        part_words_ok(out@, self.sv@, self.ps@, self.w_lo as int, self.w_hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.w_lo as u64, self.w_hi as u64)
    }

    fn run(self) -> (out: Vec<u64>) {
        let c = self.cols;
        let mut out = self.out;
        part_words(&c, self.w_lo, self.w_hi, &mut out, self.sv, self.ps);
        out
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

/// The words of the rows `0..np`, on the calling thread or split into `nt` tasks.
pub fn part_pass(pc: PartCols, nt: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<Vec<u64>, WorkerFailure>)
    requires part_cols_ok(pc, sv, ps), 1 <= nt <= MAX_WORKERS,
    ensures r matches Ok(bits) ==> pbits_ok(bits@, sv, ps),
{
    let nw = pc.np / 64 + if pc.np % 64 != 0 { 1 } else { 0 };
    if nt == 1 {
        let mut bits: Vec<u64> = vec![0u64; nw];
        proof {
            assert(bits@.len() == nw);
        }
        part_words(&pc, 0, nw, &mut bits, Ghost(sv), Ghost(ps));
        proof {
            assert forall|r: int| 0 <= r < 64 * bits@.len() implies #[trigger] word_bit(bits@, r) == (r < n_p(sv) && sel(sv, ps, r)) by {
                assert(bit(bits@[r / 64 - 0], (r % 64) as u64) == (r < n_p(sv) && sel(sv, ps, r)));
            }
        }
        return Ok(bits);
    }
    let q = nw / nt;
    let rm = nw % nt;
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut w_lo: usize = 0;
    let mut k: usize = 0;
    while k < nt
        invariant
            part_cols_ok(pc, sv, ps), 1 <= nt <= MAX_WORKERS, k <= nt,
            nw == pc.np / 64 + if pc.np % 64 != 0 { 1int } else { 0int }, q == nw / nt, rm == nw % nt,
            tasks@.len() == k,
            w_lo == split_at(nw as int, nt as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].sv@ == sv && tasks@[t].ps@ == ps
                && tasks@[t].w_lo == split_at(nw as int, nt as int, t)
                && tasks@[t].w_hi == split_at(nw as int, nt as int, t + 1),
        decreases nt - k,
    {
        proof { lemma_split(nw as int, nt as int, k as int); }
        let w_hi = w_lo + q + if k < rm { 1 } else { 0 };
        assert(64 * w_hi <= pc.np + 63);
        let task = PartTask { cols: pc, w_lo, w_hi, out: vec![0u64; w_hi - w_lo], sv: Ghost(sv), ps: Ghost(ps) };
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
        assert forall|u: int| 0 <= u < nt implies part_words_ok(#[trigger] outs0[u]@, sv, ps,
            split_at(nw as int, nt as int, u), split_at(nw as int, nt as int, u + 1)) by {
            assert(tasks0[u].post(outs0[u]));
        }
    }
    let mut outs = outs;
    let mut bits: Vec<u64> = Vec::with_capacity(nw);
    let mut t: usize = 0;
    proof { lemma_split(nw as int, nt as int, 0); }
    while t < nt
        invariant
            part_cols_ok(pc, sv, ps), 1 <= nt, t <= nt, outs0.len() == nt,
            nw == pc.np / 64 + if pc.np % 64 != 0 { 1int } else { 0int },
            outs@ == outs0.subrange(t as int, nt as int),
            bits@.len() == split_at(nw as int, nt as int, t as int),
            forall|u: int| 0 <= u < nt ==> part_words_ok(#[trigger] outs0[u]@, sv, ps,
                split_at(nw as int, nt as int, u), split_at(nw as int, nt as int, u + 1)),
            forall|r: int| 0 <= r < 64 * split_at(nw as int, nt as int, t as int) ==>
                #[trigger] word_bit(bits@, r) == (r < n_p(sv) && sel(sv, ps, r)),
        decreases nt - t,
    {
        proof { lemma_split(nw as int, nt as int, t as int); }
        let ghost (wl, wh) = (split_at(nw as int, nt as int, t as int), split_at(nw as int, nt as int, t + 1));
        let mut w = outs.remove(0);
        assert(w@ == outs0[t as int]@);
        let ghost bits0 = bits@;
        let ghost w0 = w@;
        assert(part_words_ok(w0, sv, ps, wl, wh));
        bits.append(&mut w);
        proof {
            assert(bits@ == bits0 + w0);
            assert forall|r: int| 0 <= r < 64 * wh implies #[trigger] word_bit(bits@, r) == (r < n_p(sv) && sel(sv, ps, r)) by {
                if r < 64 * wl {
                    assert(word_bit(bits0, r) == (r < n_p(sv) && sel(sv, ps, r)));
                    assert(r / 64 < wl);
                    assert(bits@[r / 64] == bits0[r / 64]);
                } else {
                    assert(r / 64 >= wl);
                    assert(bits@[r / 64] == w0[r / 64 - wl]);
                    assert(bit(w0[r / 64 - wl], (r % 64) as u64) == (r < n_p(sv) && sel(sv, ps, r)));
                }
            }
            assert(outs@ == outs0.subrange(t + 1, nt as int));
        }
        t = t + 1;
    }
    proof {
        lemma_split(nw as int, nt as int, (nt - 1) as int);
    }
    Ok(bits)
}

} // verus!
