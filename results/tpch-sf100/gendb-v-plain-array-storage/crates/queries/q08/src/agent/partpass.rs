//! The part pass: one bit per part row for `p_type = $3` (`PartTask`, one task per range of 64-row words; per word a
//! branch-free length test, then the bytes of the rows of the right length only), and
//! whether every matching row is positional (`p_partkey == row + 1`), which lets a lineitem find its part row
//! by subtraction. From the bits, a small hashed filter of part keys (`coarse`, one bit per group of 8
//! consecutive keys, groups folded modulo 2^21, 256 KiB) answers "certainly not" for most lineitem rows from the L2
//! cache.
//!
//! - `pbits_ok`: bit `r` of the words is the type test of part row `r`;
//! - `pos_ok`: every matching row `r` has key `r + 1`;
//! - `coarse_ok`: the coarse bit of the key `r + 1` of every matching row `r` (`khash(k) = (k / 8) mod 2^21`) is set.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::link::query::{text_at, text_wf};
use crate::agent::tables::*;
use crate::agent::cols::*;
use crate::agent::common::bits::*;
use crate::agent::common::text::{text_eq_at, tview};

verus! {

/// Words of the coarse filter (2^21 bits).
pub const CW: usize = 32768;

/// Mask of a coarse bit index (2^21 - 1).
pub const GMASK: u64 = 0x1f_ffff;

/// The coarse bit of part key `k`.
pub open spec fn khash(k: int) -> int { (k / 8) % 0x20_0000 }

/// The type test of every part row.
pub open spec fn pbits_ok(bits: Seq<u64>, sv: StoresView, typ: Seq<u8>) -> bool {
    &&& 64 * bits.len() >= n_p(sv)
    &&& forall|r: int| 0 <= r < n_p(sv) ==> #[trigger] word_bit(bits, r) == (p_type(sv, r) == typ)
}

/// Every matching part row is positional.
pub open spec fn pos_ok(sv: StoresView, typ: Seq<u8>) -> bool {
    forall|r: int| 0 <= r < n_p(sv) && #[trigger] p_type(sv, r) == typ ==> p_key(sv)[r] as int == r + 1
}

/// The coarse bit of every matching row's positional key is set.
pub open spec fn coarse_ok(coarse: Seq<u64>, bits: Seq<u64>, np: int) -> bool {
    &&& coarse.len() == CW
    &&& forall|r: int| 0 <= r < np && #[trigger] word_bit(bits, r) ==> word_bit(coarse, khash(r + 1))
}

// ------------------------------------------------------------------------------------------------ one task

/// The part columns a task reads and the type parameter.
#[derive(Clone, Copy)]
pub struct PartCols {
    pub key: &'static [i64],
    pub offs: &'static [i64],
    pub bytes: &'static [u8],
    pub nb: usize,
    pub pat: &'static [u8],
    pub plen: usize,
    pub np: usize,
}

pub open spec fn part_cols_ok(c: PartCols, sv: StoresView, typ: Seq<u8>) -> bool {
    &&& c.key@ == p_key(sv)
    &&& tview(c.offs@, c.bytes@) == ptype_col(sv)
    &&& text_wf(ptype_col(sv), n_p(sv) as int)
    &&& c.nb == c.bytes@.len()
    &&& c.pat@ == typ
    &&& c.plen == typ.len()
    &&& c.np == n_p(sv)
}

/// The length test of one word's rows (`64 w .. min(64 w + 64, np)`), without branches: bit `u` is set when row
/// `64 w + u` exists and its type has as many bytes as the parameter (only these rows can match).
fn part_lens(c: PartCols, w: usize, Ghost(sv): Ghost<StoresView>, Ghost(typ): Ghost<Seq<u8>>) -> (m: u64)
    requires part_cols_ok(c, sv, typ), 64 * w < c.np,
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (64 * w + u < n_p(sv) && p_type(sv, 64 * w + u).len() == typ.len()),
    no_unwind
{
    let lo = 64 * w;
    let hi = if c.np - lo > 64 { lo + 64 } else { c.np };
    let ghost tv = tview(c.offs@, c.bytes@);
    let mut m: u64 = 0;
    let mut r = lo;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while r < hi
        invariant
            part_cols_ok(c, sv, typ), lo == 64 * w, lo <= r <= hi <= c.np, hi <= lo + 64, tv == tview(c.offs@, c.bytes@),
            forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (lo + u < r && p_type(sv, lo + u).len() == typ.len()),
        decreases hi - r,
    {
        proof { assert(0 <= tv.offsets[r as int] <= tv.offsets[r + 1] <= tv.bytes.len()); }
        let a = c.offs[r];
        let e = c.offs[r + 1];
        let x: u64 = if ((e - a) as u64) == (c.plen as u64) { 1 } else { 0 };
        proof { assert(p_type(sv, r as int).len() == e - a); }
        let t = (r - lo) as u64;
        let ghost m0 = m;
        m = m | (x << t);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (lo + u < r + 1 && p_type(sv, lo + u).len() == typ.len()) by {
                lemma_bit_set(m0, x, t, u);
            }
        }
        r = r + 1;
    }
    m
}

/// One word: the rows `64 w .. min(64 w + 64, np)`. The bytes are compared only for the rows of the length test.
fn part_word(c: PartCols, w: usize, Ghost(sv): Ghost<StoresView>, Ghost(typ): Ghost<Seq<u8>>) -> (r: (u64, bool))
    requires part_cols_ok(c, sv, typ), 64 * w < c.np,
    ensures
        forall|u: u64| u < 64 && 64 * w + u < n_p(sv) ==> #[trigger] bit(r.0, u) == (p_type(sv, 64 * w + u) == typ),
        r.1 ==> forall|u: u64| u < 64 && 64 * w + u < n_p(sv) && #[trigger] p_type(sv, 64 * w + u) == typ
            ==> p_key(sv)[64 * w + u] as int == 64 * w + u + 1,
    no_unwind
{
    let lo = 64 * w;
    let m = part_lens(c, w, Ghost(sv), Ghost(typ));
    let mut word: u64 = 0;
    let mut positional = true;
    let mut mm = m;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    // the rows of the length test still to compare are the bits of `mm`
    while mm != 0
        invariant
            part_cols_ok(c, sv, typ), lo == 64 * w, 64 * w < c.np,
            forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (lo + u < n_p(sv) && p_type(sv, lo + u).len() == typ.len()),
            forall|u: u64| u < 64 && #[trigger] bit(mm, u) ==> bit(m, u),
            forall|u: u64| u < 64 ==> #[trigger] bit(word, u) == (bit(m, u) && !bit(mm, u) && p_type(sv, lo + u) == typ),
            positional ==> forall|u: u64| u < 64 && lo + u < n_p(sv) && !bit(mm, u) && #[trigger] p_type(sv, lo + u) == typ
                ==> p_key(sv)[lo + u] as int == lo + u + 1,
        decreases mm,
    {
        let t = low_index(mm);
        proof { assert(bit(m, t)); }
        let r = lo + t as usize;
        let eq = text_eq_at(c.offs, c.bytes, c.nb, r, c.pat, c.plen, Ghost(n_p(sv) as int));
        assert(eq == (p_type(sv, r as int) == typ));
        let x: u64 = if eq { 1 } else { 0 };
        let ghost w0 = word;
        word = word | (x << t);
        let pos_r = !eq || (c.key[r] as i128) == (r as i128) + 1;
        let ghost p0 = positional;
        positional = positional && pos_r;
        let ghost mm0 = mm;
        proof { lemma_clear_shrinks(mm); }
        mm = mm & (mm - 1);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(mm, u) == (bit(mm0, u) && u != t) by {
                lemma_clear_lowest(mm0, t, u);
            }
            assert forall|u: u64| u < 64 implies #[trigger] bit(word, u) == if u == t { x == 1 } else { bit(w0, u) } by {
                lemma_bit_set(w0, x, t, u);
            }
            assert forall|u: u64| u < 64 implies #[trigger] bit(word, u) == (bit(m, u) && !bit(mm, u) && p_type(sv, lo + u) == typ) by {
                if u == t {
                    assert(lo + u == r as int);
                } else {
                    assert(bit(mm, u) == bit(mm0, u));
                }
            }
            if positional {
                assert forall|u: u64| u < 64 && lo + u < n_p(sv) && !bit(mm, u) && #[trigger] p_type(sv, lo + u) == typ
                    implies p_key(sv)[lo + u] as int == lo + u + 1 by {
                    if u == t {
                        assert(lo + u == r as int);
                    } else {
                        assert(bit(mm, u) == bit(mm0, u));
                    }
                }
            }
        }
    }
    proof {
        assert forall|u: u64| u < 64 && 64 * w + u < n_p(sv) implies #[trigger] bit(word, u) == (p_type(sv, 64 * w + u) == typ) by {
            lemma_bit_zero(u);
            if p_type(sv, lo + u) == typ {
                assert(bit(m, u));
            }
        }
        if positional {
            assert forall|u: u64| u < 64 && 64 * w + u < n_p(sv) && #[trigger] p_type(sv, 64 * w + u) == typ
                implies p_key(sv)[64 * w + u] as int == 64 * w + u + 1 by {
                lemma_bit_zero(u);
            }
        }
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
    pub typ: Ghost<Seq<u8>>,
}

/// The task's words and positional flag.
pub open spec fn part_words_ok(words: Seq<u64>, positional: bool, sv: StoresView, typ: Seq<u8>, w_lo: int, w_hi: int) -> bool {
    &&& words.len() == w_hi - w_lo
    &&& forall|r: int| 64 * w_lo <= r < 64 * w_hi && r < n_p(sv) ==>
            #[trigger] bit(words[r / 64 - w_lo], (r % 64) as u64) == (p_type(sv, r) == typ)
    &&& positional ==> forall|r: int| 64 * w_lo <= r < 64 * w_hi && r < n_p(sv) && #[trigger] p_type(sv, r) == typ
            ==> p_key(sv)[r] as int == r + 1
}

impl WorkerTask for PartTask {
    type Output = (Vec<u64>, bool);

    open spec fn pre(&self) -> bool {
        &&& part_cols_ok(self.cols, self.sv@, self.typ@)
        &&& self.w_lo <= self.w_hi
        &&& 64 * self.w_hi <= self.cols.np + 63
        &&& self.out@.len() == self.w_hi - self.w_lo
    }

    open spec fn post(&self, out: (Vec<u64>, bool)) -> bool {
        part_words_ok(out.0@, out.1, self.sv@, self.typ@, self.w_lo as int, self.w_hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.w_lo as u64, self.w_hi as u64)
    }

    fn run(self) -> (out: (Vec<u64>, bool)) {
        let c = self.cols;
        let ghost (sv, typ) = (self.sv@, self.typ@);
        let mut out = self.out;
        let mut positional = true;
        let mut w = self.w_lo;
        while w < self.w_hi
            invariant
                part_cols_ok(c, sv, typ), self.w_lo <= w <= self.w_hi, 64 * self.w_hi <= c.np + 63,
                out@.len() == self.w_hi - self.w_lo,
                forall|r: int| 64 * self.w_lo <= r < 64 * w && r < n_p(sv) ==>
                    #[trigger] bit(out@[r / 64 - self.w_lo], (r % 64) as u64) == (p_type(sv, r) == typ),
                positional ==> forall|r: int| 64 * self.w_lo <= r < 64 * w && r < n_p(sv) && #[trigger] p_type(sv, r) == typ
                    ==> p_key(sv)[r] as int == r + 1,
            decreases self.w_hi - w,
        {
            let (word, pos) = part_word(c, w, Ghost(sv), Ghost(typ));
            let ghost out0 = out@;
            out[w - self.w_lo] = word;
            proof {
                assert forall|r: int| 64 * self.w_lo <= r < 64 * (w + 1) && r < n_p(sv) implies
                    #[trigger] bit(out@[r / 64 - self.w_lo], (r % 64) as u64) == (p_type(sv, r) == typ) by {
                    if r < 64 * w {
                        assert(out@[r / 64 - self.w_lo] == out0[r / 64 - self.w_lo]);
                    } else {
                        assert(r / 64 == w);
                        let u = (r - 64 * w) as u64;
                        assert(r % 64 == u);
                        assert(bit(word, u) == (p_type(sv, 64 * w + u) == typ));
                    }
                }
                if positional && pos {
                    assert forall|r: int| 64 * self.w_lo <= r < 64 * (w + 1) && r < n_p(sv) && #[trigger] p_type(sv, r) == typ
                        implies p_key(sv)[r] as int == r + 1 by {
                        if r >= 64 * w {
                            let u = (r - 64 * w) as u64;
                            assert(p_type(sv, 64 * w + u) == typ);
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

/// The part pass: the type bits of all part rows, and whether the matching rows are positional.
pub fn part_pass(pc: PartCols, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>, Ghost(typ): Ghost<Seq<u8>>)
    -> (r: Result<(Vec<u64>, bool), WorkerFailure>)
    requires part_cols_ok(pc, sv, typ), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok((bits, pos)) ==> pbits_ok(bits@, sv, typ) && (pos ==> pos_ok(sv, typ)),
{
    let nw = pc.np / 64 + if pc.np % 64 != 0 { 1 } else { 0 };
    let q = nw / workers;
    let rm = nw % workers;
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut w_lo: usize = 0;
    let mut k: usize = 0;
    while k < workers
        invariant
            part_cols_ok(pc, sv, typ), 1 <= workers <= MAX_WORKERS, k <= workers,
            nw == pc.np / 64 + if pc.np % 64 != 0 { 1int } else { 0int }, q == nw / workers, rm == nw % workers,
            tasks@.len() == k,
            w_lo == split_at(nw as int, workers as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].sv@ == sv && tasks@[t].typ@ == typ
                && tasks@[t].w_lo == split_at(nw as int, workers as int, t)
                && tasks@[t].w_hi == split_at(nw as int, workers as int, t + 1),
        decreases workers - k,
    {
        proof { lemma_split(nw as int, workers as int, k as int); }
        let w_hi = w_lo + q + if k < rm { 1 } else { 0 };
        assert(64 * w_hi <= pc.np + 63);
        let task = PartTask { cols: pc, w_lo, w_hi, out: vec![0u64; w_hi - w_lo], sv: Ghost(sv), typ: Ghost(typ) };
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
        assert forall|u: int| 0 <= u < workers implies part_words_ok(#[trigger] outs0[u].0@, outs0[u].1, sv, typ,
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
            part_cols_ok(pc, sv, typ), 1 <= workers, t <= workers, outs0.len() == workers,
            nw == pc.np / 64 + if pc.np % 64 != 0 { 1int } else { 0int },
            outs@ == outs0.subrange(t as int, workers as int),
            bits@.len() == split_at(nw as int, workers as int, t as int),
            forall|u: int| 0 <= u < workers ==> part_words_ok(#[trigger] outs0[u].0@, outs0[u].1, sv, typ,
                split_at(nw as int, workers as int, u), split_at(nw as int, workers as int, u + 1)),
            forall|r: int| 0 <= r < 64 * split_at(nw as int, workers as int, t as int) && r < n_p(sv) ==>
                #[trigger] word_bit(bits@, r) == (p_type(sv, r) == typ),
            pos ==> forall|r: int| 0 <= r < 64 * split_at(nw as int, workers as int, t as int) && r < n_p(sv)
                && #[trigger] p_type(sv, r) == typ ==> p_key(sv)[r] as int == r + 1,
        decreases workers - t,
    {
        proof { lemma_split(nw as int, workers as int, t as int); }
        let ghost (wl, wh) = (split_at(nw as int, workers as int, t as int), split_at(nw as int, workers as int, t + 1));
        let (mut w, p) = outs.remove(0);
        assert((w@, p) == (outs0[t as int].0@, outs0[t as int].1));
        let ghost bits0 = bits@;
        let ghost w0 = w@;
        assert(part_words_ok(w0, p, sv, typ, wl, wh));
        bits.append(&mut w);
        proof {
            assert(bits@ == bits0 + w0);
            assert forall|r: int| 0 <= r < 64 * wh && r < n_p(sv) implies #[trigger] word_bit(bits@, r) == (p_type(sv, r) == typ) by {
                if r < 64 * wl {
                    assert(word_bit(bits0, r) == (p_type(sv, r) == typ));
                    assert(r / 64 < wl);
                    assert(bits@[r / 64] == bits0[r / 64]);
                } else {
                    assert(r / 64 >= wl);
                    assert(bits@[r / 64] == w0[r / 64 - wl]);
                    assert(bit(w0[r / 64 - wl], (r % 64) as u64) == (p_type(sv, r) == typ));
                }
            }
            if pos && p {
                assert forall|r: int| 0 <= r < 64 * wh && r < n_p(sv) && #[trigger] p_type(sv, r) == typ
                    implies p_key(sv)[r] as int == r + 1 by {
                    if r >= 64 * wl {
                        assert(p_type(sv, r) == typ);
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
        assert forall|r: int| 0 <= r < n_p(sv) implies #[trigger] word_bit(bits@, r) == (p_type(sv, r) == typ) by {
            assert(r < 64 * nw);
        }
        if pos {
            assert forall|r: int| 0 <= r < n_p(sv) && #[trigger] p_type(sv, r) == typ implies p_key(sv)[r] as int == r + 1 by {
                assert(r < 64 * nw);
            }
        }
    }
    Ok((bits, pos))
}

// ------------------------------------------------------------------------------------------------ the coarse filter

/// Setting bit `t` keeps the others and sets `t`.
proof fn lemma_or_bit(m: u64, t: u64, u: u64)
    requires t < 64, u < 64,
    ensures bit(m | (1u64 << t), u) == (u == t || bit(m, u)),
{
    assert(t < 64 && u < 64 ==> ((((m | (1u64 << t)) >> u) & 1u64 == 1u64) == (u == t || (m >> u) & 1u64 == 1u64))) by (bit_vector);
}

/// The coarse bit index of a key `x`, and its word and position.
pub proof fn lemma_key_group(x: u64)
    ensures
        ((x >> 3) & GMASK) as int == khash(x as int),
        (((x >> 3) & GMASK) >> 6) < CW,
        (((x >> 3) & GMASK) >> 6) as int == khash(x as int) / 64,
        (((x >> 3) & GMASK) & 63) as int == khash(x as int) % 64,
        (((x >> 3) & GMASK) & 63) < 64,
{
    assert(((x >> 3) & 0x1f_ffff) == (x / 8) % 0x20_0000) by (bit_vector);
    let g = (x >> 3) & 0x1f_ffff;
    assert(g <= 0x1f_ffff) by (bit_vector) requires g == (x >> 3) & 0x1f_ffff;
    assert(g <= 0x1f_ffff ==> (g >> 6) == g / 64 && (g >> 6) < 32768 && (g & 63) == g % 64 && (g & 63) < 64) by (bit_vector);
}

/// A lowest-bit step shrinks a non-zero mask.
proof fn lemma_clear_shrinks(m: u64)
    requires m != 0,
    ensures m & sub(m, 1) < m,
{
    assert(m != 0 ==> m & sub(m, 1) < m) by (bit_vector);
}

/// Build the coarse filter from the type bits: one bit per matching row's key group.
pub fn build_coarse(bits: &Vec<u64>, np: usize) -> (coarse: Box<[u64; CW]>)
    requires 64 * bits@.len() >= np,
    ensures coarse_ok((*coarse)@, bits@, np as int),
{
    if (np as u64) >= 0x4000_0000_0000_0000 {
        // a filter that lets every key through
        let full = [0xffff_ffff_ffff_ffffu64; CW];
        proof {
            assert forall|r: int| 0 <= r < np && #[trigger] word_bit(bits@, r) implies word_bit(full@, khash(r + 1)) by {
                let h = khash(r + 1);
                assert(0 <= h < 0x20_0000);
                assert(bit(0xffff_ffff_ffff_ffffu64, (h % 64) as u64)) by {
                    let u = (h % 64) as u64;
                    assert(u < 64 ==> (0xffff_ffff_ffff_ffffu64 >> u) & 1u64 == 1u64) by (bit_vector);
                }
            }
        }
        return Box::new(full);
    }
    let mut coarse = [0u64; CW];
    let nw0 = bits.len();
    let nw = if nw0 > np / 64 + 1 { np / 64 + 1 } else { nw0 };
    let mut w: usize = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while w < nw
        invariant
            nw <= bits@.len(), nw <= np / 64 + 1, np < 0x4000_0000_0000_0000, w <= nw, coarse@.len() == CW,
            64 * bits@.len() >= np, nw == bits@.len() || 64 * nw >= np,
            forall|r: int| 0 <= r < 64 * w && r < np && #[trigger] word_bit(bits@, r) ==> word_bit(coarse@, khash(r + 1)),
        decreases nw - w,
    {
        let x = bits[w];
        let mut m = x;
        while m != 0
            invariant
                w < nw, nw <= bits@.len(), nw <= np / 64 + 1, np < 0x4000_0000_0000_0000, coarse@.len() == CW, x == bits@[w as int],
                forall|r: int| 0 <= r < 64 * w && r < np && #[trigger] word_bit(bits@, r) ==> word_bit(coarse@, khash(r + 1)),
                forall|u: u64| u < 64 && #[trigger] bit(m, u) ==> bit(x, u),
                forall|u: u64| u < 64 && bit(x, u) && !bit(m, u) && 64 * w + u < np ==> word_bit(coarse@, khash(64 * w + u + 1)),
            decreases m,
        {
            proof { lemma_first_bit(m); }
            let t = m.trailing_zeros() as u64;
            let r = (w as u64) * 64 + t;
            let ghost c0 = coarse@;
            if r < np as u64 {
                let key = r + 1;
                proof { lemma_key_group(key); }
                let g = (key >> 3) & GMASK;
                let gi = (g >> 6) as usize;
                let gb = g & 63;
                coarse[gi] = coarse[gi] | (1u64 << gb);
                proof {
                    assert forall|h: int| 0 <= h < 0x20_0000 && #[trigger] word_bit(c0, h) implies word_bit(coarse@, h) by {
                        if h / 64 == gi as int {
                            lemma_or_bit(c0[h / 64], gb, (h % 64) as u64);
                        }
                    }
                    lemma_or_bit(c0[gi as int], gb, gb);
                    assert(word_bit(coarse@, khash(key as int)));
                }
            }
            proof {
                // setting a bit keeps the bits already set
                assert(forall|h: int| 0 <= h < 0x20_0000 && #[trigger] word_bit(c0, h) ==> word_bit(coarse@, h));
                assert(r < np as u64 ==> word_bit(coarse@, khash(r as int + 1)));
            }
            let ghost m0 = m;
            proof { lemma_clear_shrinks(m); }
            m = m & (m - 1);
            proof {
                assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (bit(m0, u) && u != t) by {
                    lemma_clear_lowest(m0, t, u);
                }
                assert forall|r2: int| 0 <= r2 < 64 * w && r2 < np && #[trigger] word_bit(bits@, r2) implies word_bit(coarse@, khash(r2 + 1)) by {
                    let h = khash(r2 + 1);
                    assert(0 <= h < 0x20_0000);
                    assert(word_bit(c0, h));
                }
                assert forall|u: u64| u < 64 && bit(x, u) && !bit(m, u) && 64 * w + u < np implies word_bit(coarse@, khash(64 * w + u + 1)) by {
                    let h = khash(64 * w + u + 1);
                    assert(0 <= h < 0x20_0000);
                    if u != t {
                        assert(!bit(m0, u));
                        assert(word_bit(c0, h));
                    } else {
                        assert(r as int == 64 * w + u);
                    }
                }
            }
        }
        proof {
            assert forall|r: int| 0 <= r < 64 * (w + 1) && r < np && #[trigger] word_bit(bits@, r) implies word_bit(coarse@, khash(r + 1)) by {
                if r >= 64 * w {
                    assert(r / 64 == w);
                    let u = (r % 64) as u64;
                    assert(r == 64 * w + u);
                    lemma_bit_zero(u);
                }
            }
        }
        w = w + 1;
    }
    proof {
        assert forall|r: int| 0 <= r < np && #[trigger] word_bit(bits@, r) implies word_bit(coarse@, khash(r + 1)) by {
            assert(r < 64 * nw);
        }
    }
    Box::new(coarse)
}

} // verus!
