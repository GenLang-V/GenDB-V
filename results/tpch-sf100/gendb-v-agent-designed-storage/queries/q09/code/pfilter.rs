//! The part filter for a pattern `%w%` with a plain word `w` (`common::like_word`): one task per range of part rows
//! (`PartTask`, ranges start at multiples of 64) sets bit `(c - c_lo) % 64` of word `(c - c_lo) / 64` exactly when part
//! row `c`'s name contains `w` as a byte substring, and reports whether every name of its range is ASCII (then the bit
//! is the LIKE value) and whether part row `c` has key `c + 1` (dense keys). A row whose p_name signature (storage
//! `partsig`) lacks a bit of the word's trigram mask and is not all ones is skipped unread: its name is ASCII and does
//! not contain the word (`sigmask::lemma_skip`); the other names are checked for ASCII and searched.
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use super::model::*;
use super::cols::*;
use super::lookups::*;
use super::scan::bit_of;
use super::common::like_word::*;
use super::common::horspool::{shift_ok, find_horspool};
use super::sigmask::{word_mask, lemma_skip};
use crate::stores::partsig::interface as gi;
use std::sync::Arc;

verus! {

/// Bit `b` of `x | (1 << c)`.
proof fn lemma_set_bit(x: u64, c: u64, b: u64)
    requires c < 64, b < 64,
    ensures ((x | (1u64 << c)) >> b) & 1u64 == if b == c { 1u64 } else { (x >> b) & 1u64 },
{
    assert(((x | (1u64 << c)) >> b) & 1u64 == if b == c { 1u64 } else { (x >> b) & 1u64 }) by (bit_vector)
        requires c < 64, b < 64;
}

/// The bits of 0.
proof fn lemma_zero_bits(b: u64)
    requires b < 64,
    ensures (0u64 >> b) & 1u64 == 0u64,
{
    assert((0u64 >> b) & 1u64 == 0u64) by (bit_vector);
}

/// OR of ASCII bytes.
proof fn lemma_or_ascii(h: u8, b: u8)
    ensures ((h | b) < 0x80u8) == (h < 0x80u8 && b < 0x80u8),
{
    assert(((h | b) < 0x80u8) == (h < 0x80u8 && b < 0x80u8)) by (bit_vector);
}

/// Are the bytes `y[a..e]` ASCII? (one OR over the range)
fn range_ascii(y: &[u8], n: usize, a: usize, e: usize) -> (r: bool)
    requires a <= e <= y@.len(), n == y@.len(),
    ensures r ==> forall|x: int| a <= x < e ==> #[trigger] y@[x] < 0x80,
    no_unwind
{
    let e = if e <= n { e } else { n };
    let mut hi: u8 = 0;
    let mut i = a;
    while i < e
        invariant
            a <= i <= e <= y@.len(),
            (hi < 0x80u8) == forall|x: int| a <= x < i ==> #[trigger] y@[x] < 0x80,
        decreases e - i,
    {
        let b = y[i];
        proof {
            lemma_or_ascii(hi, b);
            assert((hi | b < 0x80u8) == forall|x: int| a <= x < i + 1 ==> #[trigger] y@[x] < 0x80) by {
                if (hi | b) < 0x80u8 {
                    assert forall|x: int| a <= x < i + 1 implies #[trigger] y@[x] < 0x80 by {}
                }
            }
        }
        hi = hi | b;
        i = i + 1;
    }
    hi < 0x80
}

/// Does `y[a..e]` contain `w = pat[wl .. wl + wn]`? (first byte test, then the rest; stops at the first match)
fn find_word(y: &[u8], a: usize, e: usize, pat: &[u8], wl: usize, wn: usize) -> (r: bool)
    requires
        a <= e <= y@.len(),
        wl + wn <= pat@.len() <= usize::MAX,
        wn >= 1,
    ensures r == contains(y@.subrange(a as int, e as int), pat@.subrange(wl as int, wl + wn)),
    no_unwind
{
    let ghost s = y@.subrange(a as int, e as int);
    let ghost w = pat@.subrange(wl as int, wl + wn);
    if e - a < wn {
        proof {
            assert forall|x: int| !#[trigger] occurs_at(s, w, x) by {}
        }
        return false;
    }
    let last = e - wn;
    let w0 = pat[wl];
    let mut i = a;
    while i <= last
        invariant
            a <= i <= last + 1, last + wn == e, e <= y@.len(),
            wl + wn <= pat@.len() <= usize::MAX,
            wn >= 1,
            s == y@.subrange(a as int, e as int),
            w == pat@.subrange(wl as int, wl + wn),
            w0 == pat@[wl as int],
            forall|x: int| 0 <= x < i - a ==> !#[trigger] occurs_at(s, w, x),
        decreases last + 1 - i,
    {
        if y[i] == w0 {
            let mut k: usize = 1;
            while k < wn && y[i + k] == pat[wl + k]
                invariant
                    a <= i <= last, last + wn == e, e <= y@.len(),
                    wl + wn <= pat@.len() <= usize::MAX,
                    1 <= k <= wn,
                    forall|x: int| 0 <= x < k ==> #[trigger] y@[i + x] == pat@[wl + x],
                    y@[i as int] == pat@[wl as int],
                decreases wn - k,
            {
                k = k + 1;
            }
            if k == wn {
                proof {
                    assert(s.subrange(i - a, i - a + wn) =~= w) by {
                        assert forall|x: int| 0 <= x < wn implies s.subrange(i - a, i - a + wn)[x] == w[x] by {
                            assert(y@[i + x] == pat@[wl + x]);
                        }
                    }
                    assert(occurs_at(s, w, i - a));
                }
                return true;
            } else {
                proof {
                    assert(!occurs_at(s, w, i - a)) by {
                        if occurs_at(s, w, i - a) {
                            assert(s.subrange(i - a, i - a + wn)[k as int] == w[k as int]);
                        }
                    }
                }
            }
        } else {
            proof {
                assert(!occurs_at(s, w, i - a)) by {
                    if occurs_at(s, w, i - a) {
                        assert(s.subrange(i - a, i - a + wn)[0] == w[0]);
                    }
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|x: int| !#[trigger] occurs_at(s, w, x) by {
            if occurs_at(s, w, x) {
                assert(x < i - a);
            }
        }
    }
    false
}

/// Offsets of text values never decrease.
proof fn lemma_offs_mono(o: Seq<u64>, y: Seq<u8>, n: int, a: int, b: int)
    requires crate::stores::custpart::interface::common::colfmt::text_parts_wf(o, y, n), 0 <= a <= b <= n,
    ensures o[a] <= o[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(o, y, n, a, b - 1);
        assert(crate::stores::custpart::interface::common::colfmt::text_range_ok(o, y, b - 1));
    }
}

/// The part rows `[c_lo, c_hi)` (`c_lo` a multiple of 64), with the preallocated bit words of the range; the word is
/// `pat[wl .. wl + wn]`.
pub struct PartTask {
    pub cols: Cols,
    pub divs: Divs,
    pub c_lo: usize,
    pub c_hi: usize,
    pub pat: &'static [u8],
    pub wl: usize,
    pub wn: usize,
    pub sh: Arc<Vec<u8>>,
    pub use_sh: bool,
    pub pm: u64,
    pub words: Vec<u64>,
    pub m: Ghost<M>,
}

pub struct PartOut {
    pub words: Vec<u64>,
    pub ascii: bool,
    pub dense: bool,
    pub hits: u64,
}

pub open spec fn part_pre(t: PartTask) -> bool {
    let m = t.m@;
    &&& look_ok(t.cols, t.divs, m)
    &&& t.c_lo <= t.c_hi <= m.p_n
    &&& t.c_lo % 64 == 0
    &&& t.words@.len() == (t.c_hi - t.c_lo + 63) / 64
    &&& t.wl + t.wn <= t.pat@.len() <= usize::MAX
    &&& t.wn >= 1
    &&& t.use_sh ==> shift_ok((*t.sh)@, t.pat@.subrange(t.wl as int, t.wl + t.wn))
    &&& t.pm == word_mask(t.pat@.subrange(t.wl as int, t.wl + t.wn))
    &&& psig_ok(t.cols.p_sig@, m)
}

/// The word of the task.
pub open spec fn task_word(t: PartTask) -> Seq<u8> {
    t.pat@.subrange(t.wl as int, t.wl + t.wn)
}

pub open spec fn part_post(t: PartTask, out: PartOut) -> bool {
    let m = t.m@;
    &&& out.words@.len() == t.words@.len()
    &&& forall|c: int| t.c_lo <= c < t.c_hi ==> (#[trigger] bit_of(out.words@, c - t.c_lo) == contains(pname(m, c), task_word(t)))
    &&& out.ascii ==> forall|c: int| t.c_lo <= c < t.c_hi ==> all_ascii(#[trigger] pname(m, c))
    &&& out.dense ==> forall|c: int| t.c_lo <= c < t.c_hi ==> #[trigger] pkey(m, c) == c + 1
}

impl WorkerTask for PartTask {
    type Output = PartOut;

    open spec fn pre(&self) -> bool {
        part_pre(*self)
    }

    open spec fn post(&self, out: PartOut) -> bool {
        part_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.c_lo as u64, self.c_hi as u64)
    }

    fn run(self) -> (out: PartOut) {
        let ghost task = self;
        let PartTask { cols, divs, c_lo, c_hi, pat, wl, wn, sh, use_sh, pm, words, m: gm } = self;
        let ghost m = gm@;
        let ghost w = task_word(task);
        let c = cols;
        let d = divs;
        let mut words = words;
        let mut ascii = true;
        let mut dense = true;
        let mut hits: u64 = 0;
        let mut cur: u64 = 0;
        let mut bit: u64 = 0;
        let mut wi: usize = 0;
        let mut r = c_lo;
        proof {
            assert forall|b: u64| b < 64 implies (cur >> b) & 1u64 == 0u64 by { lemma_zero_bits(b); }
        }
        while r < c_hi
            invariant
                task.pre(),
                m == task.m@, c == task.cols, d == task.divs, w == task_word(task),
                c_lo == task.c_lo, c_hi == task.c_hi, pat == task.pat, wl == task.wl, wn == task.wn,
                sh == task.sh, use_sh == task.use_sh,
                c_lo <= r <= c_hi,
                words@.len() == task.words@.len(),
                bit < 64,
                r - c_lo == wi * 64 + bit,
                hits <= r - c_lo,
                // finished words
                forall|x: int| c_lo <= x < c_lo + wi * 64 ==> (#[trigger] bit_of(words@, x - c_lo) == contains(pname(m, x), w)),
                // the current word: bits below `bit` are the rows `c_lo + wi * 64 ..`, the others are 0
                forall|b: u64| b < bit ==> (((cur >> b) & 1u64 == 1u64) == contains(pname(m, c_lo + wi * 64 + b), w)),
                forall|b: u64| bit <= b < 64 ==> (cur >> b) & 1u64 == 0u64,
                pm == task.pm, pm == word_mask(w), psig_ok(c.p_sig@, m),
                ascii ==> forall|x: int| c_lo <= x < r ==> #[trigger] all_ascii(pname(m, x)),
                dense ==> forall|x: int| c_lo <= x < r ==> #[trigger] pkey(m, x) == x + 1,
            decreases c_hi - r,
        {
            proof {
                assert(crate::stores::custpart::interface::common::colfmt::text_range_ok(m.p_name_o, m.p_name_y, r as int));
                assert(gi::sig_row_ok(pname(m, r as int), c.p_sig@[r as int]));
            }
            let sg = c.p_sig[r];
            let skip = (sg & pm) != pm && sg != 0xffff_ffff_ffff_ffffu64;
            let ghost a0 = ascii;
            let hit = if skip {
                proof {
                    if contains(pname(m, r as int), w) {
                        lemma_skip(pname(m, r as int), sg, w);
                    }
                    assert(gi::ascii_text(pname(m, r as int)));
                    assert(all_ascii(pname(m, r as int)));
                }
                false
            } else {
                let a = c.p_name_o[r] as usize;
                let e = c.p_name_o[r + 1] as usize;
                proof { assert(pname(m, r as int) == c.p_name_y@.subrange(a as int, e as int)); }
                if !range_ascii(c.p_name_y, c.py_n, a, e) {
                    ascii = false;
                } else {
                    proof {
                        assert forall|i: int| 0 <= i < pname(m, r as int).len() implies #[trigger] pname(m, r as int)[i] < 0x80 by {
                            assert(pname(m, r as int)[i] == c.p_name_y@[a + i]);
                        }
                    }
                }
                if use_sh { find_horspool(c.p_name_y, a, e, pat, wl, wn, &sh) } else { find_word(c.p_name_y, a, e, pat, wl, wn) }
            };
            proof {
                if ascii {
                    assert forall|x: int| c_lo <= x < r + 1 implies #[trigger] all_ascii(pname(m, x)) by {
                        if x < r { assert(a0); }
                    }
                }
            }
            let ghost cur0 = cur;
            if hit {
                proof {
                    assert forall|b: u64| b < 64 implies ((cur | (1u64 << bit)) >> b) & 1u64 == if b == bit { 1u64 } else { (cur >> b) & 1u64 } by {
                        lemma_set_bit(cur, bit, b);
                    }
                }
                cur = cur | (1u64 << bit);
                hits = hits + 1;
            }
            if get_pkey(&c, &d, r, Ghost(m)) as i128 != r as i128 + 1 {
                dense = false;
            }
            proof {
                assert forall|b: u64| b < 64 && b != bit implies (cur >> b) & 1u64 == (cur0 >> b) & 1u64 by {
                    if hit { lemma_set_bit(cur0, bit, b); }
                }
                assert forall|b: u64| b < bit + 1 implies (((cur >> b) & 1u64 == 1u64) == contains(pname(m, c_lo + wi * 64 + b), w)) by {
                    if b < bit {
                        assert((cur >> b) & 1u64 == (cur0 >> b) & 1u64);
                    } else {
                        if hit { lemma_set_bit(cur0, bit, b); }
                    }
                }
                assert forall|b: u64| bit + 1 <= b < 64 implies (cur >> b) & 1u64 == 0u64 by {
                    assert((cur >> b) & 1u64 == (cur0 >> b) & 1u64);
                }
            }
            bit = bit + 1;
            if bit == 64 {
                let ghost w0 = words@;
                proof {
                    assert(wi < words@.len()) by {
                        assert(wi * 64 + 64 <= c_hi - c_lo + 63);
                    }
                }
                put(&mut words, wi, cur);
                proof {
                    assert forall|x: int| c_lo <= x < c_lo + (wi + 1) * 64 implies (#[trigger] bit_of(words@, x - c_lo) == contains(pname(m, x), w)) by {
                        let k = x - c_lo;
                        if k < wi * 64 {
                            assert(k / 64 < wi) by { }
                            assert(words@[k / 64] == w0[k / 64]);
                            assert(bit_of(w0, k) == contains(pname(m, x), w));
                        } else {
                            assert(k / 64 == wi) by { }
                            assert(k % 64 == k - wi * 64) by { }
                            let b = (k % 64) as u64;
                            assert(((cur >> b) & 1u64 == 1u64) == contains(pname(m, c_lo + wi * 64 + b), w));
                        }
                    }
                }
                wi = wi + 1;
                cur = 0;
                bit = 0;
                proof {
                    assert forall|b: u64| b < 64 implies (cur >> b) & 1u64 == 0u64 by { lemma_zero_bits(b); }
                }
            }
            r = r + 1;
        }
        if bit > 0 {
            let ghost w0 = words@;
            proof {
                assert(wi < words@.len()) by {
                    assert(wi * 64 + 1 <= c_hi - c_lo);
                }
            }
            put(&mut words, wi, cur);
            proof {
                assert forall|x: int| c_lo <= x < c_hi implies (#[trigger] bit_of(words@, x - c_lo) == contains(pname(m, x), w)) by {
                    let k = x - c_lo;
                    if k < wi * 64 {
                        assert(k / 64 < wi) by { }
                        assert(words@[k / 64] == w0[k / 64]);
                        assert(bit_of(w0, k) == contains(pname(m, x), w));
                    } else {
                        assert(k / 64 == wi) by { }
                        assert(k % 64 == k - wi * 64) by { }
                        let b = (k % 64) as u64;
                        assert(((cur >> b) & 1u64 == 1u64) == contains(pname(m, c_lo + wi * 64 + b), w));
                    }
                }
            }
        }
        PartOut { words, ascii, dense, hits }
    }
}

} // verus!
