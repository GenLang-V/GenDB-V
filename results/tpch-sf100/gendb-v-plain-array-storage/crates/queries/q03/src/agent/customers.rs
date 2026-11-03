//! The customer pass: one bit per customer row, set when its `c_mktsegment` is `$1` (`CustTask`, one task per range
//! of 64-row words), and whether `c_custkey` is positional (`c_custkey[r] == c_custkey[0] + r`), which lets an
//! order find its customer row by subtraction (`scan_parts::cust_bit`).
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::link::query::{text_at, text_wf};
use crate::agent::tables::*;
use crate::agent::common::bits::*;

verus! {

/// The customer columns a task reads (whole parts) and the segment parameter.
#[derive(Clone, Copy)]
pub struct CustCols {
    pub ckey: &'static [i64],
    pub offs: &'static [i64],
    pub bytes: &'static [u8],
    pub seg: &'static [u8],
    pub seg_len: usize,
    pub bytes_len: usize,
    pub nc: usize,
    pub base: i64,
}

pub open spec fn cust_cols_ok(c: CustCols, sv: StoresView, seg: Seq<u8>) -> bool {
    &&& c.ckey@ == ck(sv)
    &&& c.offs@ == cseg_col(sv).offsets
    &&& c.bytes@ == cseg_col(sv).bytes
    &&& text_wf(cseg_col(sv), n_c(sv))
    &&& c.seg@ == seg
    &&& c.seg_len as int == seg.len()
    &&& c.bytes_len as int == c.bytes@.len()
    &&& c.nc as int == n_c(sv)
    &&& n_c(sv) > 0 ==> c.base == ck(sv)[0]
}

/// Customer row `r` has segment `seg` (byte equality).
pub fn seg_eq(c: CustCols, r: usize, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>) -> (b: bool)
    requires cust_cols_ok(c, sv, seg), r < c.nc,
    ensures b == (cseg(sv, r as int) == seg),
    no_unwind
{
    let a0 = c.offs[r];
    let e0 = c.offs[r + 1];
    let ghost t = cseg_col(sv);
    assert(0 <= t.offsets[r as int] <= t.offsets[r + 1] <= t.bytes.len());
    assert(a0 == t.offsets[r as int] && e0 == t.offsets[r + 1]);
    let a = a0 as usize;
    let e = e0 as usize;
    assert(a as int == a0 as int && e as int == e0 as int && a <= e);
    let n = c.seg_len;
    if e - a != n {
        assert(cseg(sv, r as int).len() != seg.len());
        return false;
    }
    let mut k: usize = 0;
    while k < n
        invariant
            cust_cols_ok(c, sv, seg), r < c.nc, t == cseg_col(sv),
            k <= n, n == seg.len(), c.seg@ == seg, a + n == e, e <= c.bytes@.len(), c.bytes@ == t.bytes,
            a == t.offsets[r as int], e == t.offsets[r + 1],
            cseg(sv, r as int) == t.bytes.subrange(a as int, e as int),
            forall|x: int| 0 <= x < k ==> c.bytes@[a + x] == seg[x],
        decreases n - k,
    {
        if c.bytes[a + k] != c.seg[k] {
            assert(cseg(sv, r as int)[k as int] == t.bytes[a + k]);
            assert(cseg(sv, r as int)[k as int] != seg[k as int]);
            return false;
        }
        k = k + 1;
    }
    assert(cseg(sv, r as int) =~= seg);
    true
}

/// One task: the words `w_lo..w_hi` (rows `64 w_lo .. min(64 w_hi, nc)`).
pub struct CustTask {
    pub cols: CustCols,
    pub w_lo: usize,
    pub w_hi: usize,
    pub out: Vec<u64>,
    pub sv: Ghost<StoresView>,
    pub seg: Ghost<Seq<u8>>,
}

/// The task's words: bit `r % 64` of word `r / 64 - w_lo` is customer row `r`'s segment test; and when
/// `positional`, every key of the range is `base + r`.
pub open spec fn cust_words_ok(words: Seq<u64>, positional: bool, c: CustCols, sv: StoresView, seg: Seq<u8>, w_lo: int, w_hi: int)
    -> bool
{
    &&& words.len() == w_hi - w_lo
    &&& forall|r: int| 64 * w_lo <= r < 64 * w_hi && r < n_c(sv) ==>
            #[trigger] bit(words[r / 64 - w_lo], (r % 64) as u64) == (cseg(sv, r) == seg)
    &&& positional ==> forall|r: int| 64 * w_lo <= r < 64 * w_hi && r < n_c(sv) ==> #[trigger] ck(sv)[r] as int == c.base + r
}

/// One word: the rows `64 w .. min(64 w + 64, nc)`.
fn cust_word(c: CustCols, w: usize, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>) -> (r: (u64, bool))
    requires cust_cols_ok(c, sv, seg), 64 * w < c.nc,
    ensures
        forall|u: u64| u < 64 && 64 * w + u < n_c(sv) ==> #[trigger] bit(r.0, u) == (cseg(sv, 64 * w + u) == seg),
        r.1 ==> forall|u: u64| u < 64 && 64 * w + u < n_c(sv) ==> #[trigger] ck(sv)[64 * w + u] as int == c.base + 64 * w + u,
    no_unwind
{
    let lo = 64 * w;
    let hi = if c.nc - lo > 64 { lo + 64 } else { c.nc };
    let mut word: u64 = 0;
    let mut positional = true;
    let mut r = lo;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while r < hi
        invariant
            cust_cols_ok(c, sv, seg), lo == 64 * w, lo <= r <= hi <= c.nc, hi <= lo + 64,
            forall|u: u64| u < 64 && lo + u < r ==> #[trigger] bit(word, u) == (cseg(sv, lo + u) == seg),
            forall|u: u64| u < 64 && lo + u >= r ==> !#[trigger] bit(word, u),
            positional ==> forall|u: u64| u < 64 && lo + u < r ==> #[trigger] ck(sv)[lo + u] as int == c.base + lo + u,
        decreases hi - r,
    {
        let eq = seg_eq(c, r, Ghost(sv), Ghost(seg));
        let x: u64 = if eq { 1 } else { 0 };
        let t = (r - lo) as u64;
        let ghost w0 = word;
        word = word | (x << t);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(word, u) == if u == t { x == 1 } else { bit(w0, u) } by {
                lemma_bit_set(w0, x, t, u);
            }
        }
        if (c.ckey[r] as i128) != (c.base as i128) + (r as i128) {
            positional = false;
        }
        r = r + 1;
    }
    (word, positional)
}

impl WorkerTask for CustTask {
    type Output = (Vec<u64>, bool);

    open spec fn pre(&self) -> bool {
        &&& cust_cols_ok(self.cols, self.sv@, self.seg@)
        &&& self.w_lo <= self.w_hi
        &&& 64 * self.w_hi <= self.cols.nc + 63
        &&& self.out@.len() == self.w_hi - self.w_lo
    }

    open spec fn post(&self, out: (Vec<u64>, bool)) -> bool {
        cust_words_ok(out.0@, out.1, self.cols, self.sv@, self.seg@, self.w_lo as int, self.w_hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.w_lo as u64, self.w_hi as u64)
    }

    fn run(self) -> (out: (Vec<u64>, bool)) {
        let c = self.cols;
        let ghost (sv, seg) = (self.sv@, self.seg@);
        let mut out = self.out;
        let mut positional = true;
        let mut w = self.w_lo;
        while w < self.w_hi
            invariant
                cust_cols_ok(c, sv, seg), self.w_lo <= w <= self.w_hi, 64 * self.w_hi <= c.nc + 63,
                out@.len() == self.w_hi - self.w_lo,
                forall|r: int| 64 * self.w_lo <= r < 64 * w && r < n_c(sv) ==>
                    #[trigger] bit(out@[r / 64 - self.w_lo], (r % 64) as u64) == (cseg(sv, r) == seg),
                positional ==> forall|r: int| 64 * self.w_lo <= r < 64 * w && r < n_c(sv) ==> #[trigger] ck(sv)[r] as int == c.base + r,
            decreases self.w_hi - w,
        {
            let (word, pos) = cust_word(c, w, Ghost(sv), Ghost(seg));
            let ghost out0 = out@;
            out[w - self.w_lo] = word;
            proof {
                assert forall|r: int| 64 * self.w_lo <= r < 64 * (w + 1) && r < n_c(sv) implies
                    #[trigger] bit(out@[r / 64 - self.w_lo], (r % 64) as u64) == (cseg(sv, r) == seg) by {
                    if r < 64 * w {
                        assert(out@[r / 64 - self.w_lo] == out0[r / 64 - self.w_lo]);
                    } else {
                        assert(r / 64 == w);
                        let u = (r - 64 * w) as u64;
                        assert(r % 64 == u);
                        assert(bit(word, u) == (cseg(sv, 64 * w + u) == seg));
                    }
                }
                if positional && pos {
                    assert forall|r: int| 64 * self.w_lo <= r < 64 * (w + 1) && r < n_c(sv) implies #[trigger] ck(sv)[r] as int == c.base + r by {
                        if r >= 64 * w {
                            let u = (r - 64 * w) as u64;
                            assert(ck(sv)[64 * w + u] as int == c.base + 64 * w + u);
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

} // verus!
