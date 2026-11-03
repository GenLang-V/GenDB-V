//! The part filter's bitmaps built in parallel over the part rows.
//!
//! When the stored part keys are dense (row `i` holds key `first + i`, checked by the workers as they scan), the
//! bitmap over the keys `[first, first + n_p)` is the bitmap over the part rows: bit `i` is "row `i` has type `$3`"
//! (`mrow`). Worker `t` scans part rows `[a_t, b_t)` (`a_t` a multiple of 512, so its fine words and its coarse words
//! start on word boundaries of the whole bitmaps) and sets bit `i - a_t` of its fine words and bit `(i - a_t) / 8` of
//! its coarse words for each matching row; the calling thread concatenates the words. Without dense keys (or
//! without a dictionary entry `$3`, or more than `2^32` parts) the serial builder (`build::pfilter_serial`) runs.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use super::sql::*;
use super::model::*;
use super::kernel::*;
use super::filters::*;
use super::build::*;
use std::sync::Arc;

verus! {

/// Part rows per alignment unit of a task (one coarse word).
pub const PALIGN: usize = 512;

// ------------------------------------------------------------------------------------------------ bits

/// Sets bit `x` (no allocation).
fn set_bit_nu(ws: &mut Vec<u64>, x: usize)
    requires x / 64 < old(ws)@.len(),
    ensures
        final(ws)@.len() == old(ws)@.len(),
        forall|y: int| 0 <= y && y / 64 < old(ws)@.len() ==> #[trigger] bit_at(final(ws)@, y) == (y == x || bit_at(old(ws)@, y)),
    no_unwind
{
    let w = x / 64;
    let s = (x % 64) as u64;
    let a = ws[w];
    ws[w] = a | (1u64 << s);
    proof {
        let o = old(ws)@;
        let nw = ws@;
        assert forall|y: int| 0 <= y && y / 64 < o.len() implies #[trigger] bit_at(nw, y) == (y == x || bit_at(o, y)) by {
            let t = (y % 64) as u64;
            if y / 64 == w as int {
                assert(nw[y / 64] == a | (1u64 << s));
                assert((((a | (1u64 << s)) >> t) & 1u64 == 1u64) == (t == s || ((a >> t) & 1u64 == 1u64))) by (bit_vector)
                    requires s < 64, t < 64;
                assert((y == x) == (t == s)) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y, 64);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 64);
                    vstd::arithmetic::div_mod::lemma_mod_bound(y, 64);
                    assert(y == 64 * (y / 64) + y % 64);
                    assert(x as int == 64 * (x as int / 64) + x as int % 64);
                }
            } else {
                assert(nw[y / 64] == o[y / 64]);
                assert(y != x as int);
            }
        }
    }
}

/// A word sequence of zeros has no bit set.
proof fn lemma_zero_word_bits(ws: Seq<u64>, x: int)
    requires 0 <= x, x / 64 < ws.len(), ws[x / 64] == 0,
    ensures !bit_at(ws, x),
{
    let t = (x % 64) as u64;
    assert((0u64 >> t) & 1u64 == 0u64) by (bit_vector);
}

/// Bits of a concatenation: the first part's below its length, the second part's (shifted) above.
proof fn lemma_concat_bit(p: Seq<u64>, s: Seq<u64>, x: int)
    requires 0 <= x < (p.len() + s.len()) * 64,
    ensures
        x < p.len() * 64 ==> bit_at(p + s, x) == bit_at(p, x),
        x >= p.len() * 64 ==> bit_at(p + s, x) == bit_at(s, x - p.len() * 64),
{
    let a = p.len() * 64;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, 64);
    vstd::arithmetic::div_mod::lemma_mod_bound(x, 64);
    if x < a {
        vstd::arithmetic::div_mod::lemma_div_is_ordered(x, a - 1, 64);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a - 1, 64, p.len() - 1, 63);
        assert(x / 64 < p.len());
    } else {
        let y = x - a;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y, 64);
        vstd::arithmetic::div_mod::lemma_mod_bound(y, 64);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, 64, y / 64 + p.len(), y % 64);
        assert(x / 64 == y / 64 + p.len() && x % 64 == y % 64);
    }
}

// ------------------------------------------------------------------------------------------------ the task

/// Part rows `[a, b)` hold the keys `first + i`.
pub open spec fn rows_dense(f: PFilter, first: int, a: int, b: int) -> bool {
    forall|i: int| a <= i < b ==> #[trigger] pkey(f, i) == first + i
}

/// The bitmaps of part rows `[a, b)`: fine bit `x` is row `a + x`'s match, a set fine bit has its coarse bit.
pub open spec fn rows_bits(f: PFilter, a: int, b: int, words: Seq<u64>, coarse: Seq<u64>) -> bool {
    &&& forall|x: int| 0 <= x < b - a ==> #[trigger] bit_at(words, x) == mrow(f, a + x)
    &&& forall|x: int| 0 <= x < b - a && #[trigger] bit_at(words, x) ==> bit_at(coarse, x / 8)
}

/// Scans part rows `[a, b)`: fine and coarse bits of the rows of type `$3`, and whether their keys are dense.
pub struct PartTask {
    pub f: Arc<PFilter>,
    pub first: i64,
    pub a: usize,
    pub b: usize,
    pub words: Vec<u64>,
    pub coarse: Vec<u64>,
}

pub struct PartOut {
    pub words: Vec<u64>,
    pub coarse: Vec<u64>,
    pub dense: bool,
}

pub open spec fn part_pre(t: PartTask) -> bool {
    &&& pf_shape(*t.f)
    &&& t.a <= t.b <= t.f.n_p
    &&& t.words@.len() * 64 >= t.b - t.a && t.coarse@.len() * 512 >= t.b - t.a
    &&& forall|i: int| 0 <= i < t.words@.len() ==> #[trigger] t.words@[i] == 0
    &&& forall|i: int| 0 <= i < t.coarse@.len() ==> #[trigger] t.coarse@[i] == 0
}

pub open spec fn part_post(t: PartTask, out: PartOut) -> bool {
    &&& out.words@.len() == t.words@.len() && out.coarse@.len() == t.coarse@.len()
    &&& rows_bits(*t.f, t.a as int, t.b as int, out.words@, out.coarse@)
    &&& out.dense ==> rows_dense(*t.f, t.first as int, t.a as int, t.b as int)
}

/// The group of part row `i` and the rows `[gs, ge)` of that group.
pub open spec fn grp_ok(f: PFilter, i: int, g: int, ge: int) -> bool {
    &&& 0 <= g < f.pk_b@.len()
    &&& g * f.bs_p <= i < ge
    &&& ge == if f.n_p - g * f.bs_p > f.bs_p { g * f.bs_p + f.bs_p } else { f.n_p as int }
}

/// The dictionary entry `$3` as a code of group `g`, if the group's base can reach it.
fn want_of(f: &PFilter, g: usize) -> (r: (bool, u8))
    requires pf_shape(*f), g < f.pk_b@.len(),
    ensures
        forall|i: int| 0 <= i < f.n_p && i / (f.bs_p as int) == g ==> #[trigger] mrow(*f, i) == (r.0 && f.pt_c@[i] == r.1),
    no_unwind
{
    let base = f.pt_b[g];
    if f.has_t && f.t >= base && f.t - base < 256 {
        let want = (f.t - base) as u8;
        proof {
            assert forall|i: int| 0 <= i < f.n_p && i / (f.bs_p as int) == g implies #[trigger] mrow(*f, i)
                == (f.pt_c@[i] == want) by {
                assert(ptype(*f, i) == base + f.pt_c@[i]);
            }
        }
        (true, want)
    } else {
        proof {
            assert forall|i: int| 0 <= i < f.n_p && i / (f.bs_p as int) == g implies !#[trigger] mrow(*f, i) by {
                assert(ptype(*f, i) == base + f.pt_c@[i]);
            }
        }
        (false, 0)
    }
}

/// The scan of part rows `[a, b)`.
fn scan_parts(f: &PFilter, first: i64, a: usize, b: usize, words: Vec<u64>, coarse: Vec<u64>) -> (out: PartOut)
    requires
        pf_shape(*f),
        a <= b <= f.n_p,
        words@.len() * 64 >= b - a && coarse@.len() * 512 >= b - a,
        forall|i: int| 0 <= i < words@.len() ==> #[trigger] words@[i] == 0,
        forall|i: int| 0 <= i < coarse@.len() ==> #[trigger] coarse@[i] == 0,
    ensures
        out.words@.len() == words@.len() && out.coarse@.len() == coarse@.len(),
        rows_bits(*f, a as int, b as int, out.words@, out.coarse@),
        out.dense ==> rows_dense(*f, first as int, a as int, b as int),
    no_unwind
{
    let ghost w0 = words@;
    let ghost c0 = coarse@;
    let mut words = words;
    let mut coarse = coarse;
    let mut dense = true;
    if a >= b {
        return PartOut { words, coarse, dense };
    }
    let n = f.n_p;
    let bs = f.bs_p;
    proof {
        crate::stores::custpart::interface::common::read::lemma_div_lt(a as int, bs as int, f.pk_b@.len() as int);
        lemma_group_of_row(a as int, bs as int);
    }
    let mut g = a / bs;
    let mut ge = if n - g * bs > bs { g * bs + bs } else { n };
    let (mut has, mut want) = want_of(f, g);
    let mut i = a;
    proof {
        assert forall|x: int| 0 <= x < words@.len() * 64 implies !#[trigger] bit_at(words@, x) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(x, words@.len() * 64 - 1, 64);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(words@.len() * 64 - 1, 64,
                words@.len() - 1, 63);
            lemma_zero_word_bits(words@, x);
        }
    }
    while i < b
        invariant
            pf_shape(*f), n == f.n_p, bs == f.bs_p,
            a <= i <= b <= n, a < b,
            i < b ==> grp_ok(*f, i as int, g as int, ge as int),
            i < b ==> forall|r: int| 0 <= r < f.n_p && r / (bs as int) == g ==> #[trigger] mrow(*f, r) == (has && f.pt_c@[r] == want),
            words@.len() == w0.len(), coarse@.len() == c0.len(),
            w0.len() * 64 >= b - a && c0.len() * 512 >= b - a,
            forall|x: int| 0 <= x < i - a ==> #[trigger] bit_at(words@, x) == mrow(*f, a + x),
            forall|x: int| i - a <= x < words@.len() * 64 ==> !#[trigger] bit_at(words@, x),
            forall|x: int| 0 <= x < i - a && #[trigger] bit_at(words@, x) ==> bit_at(coarse@, x / 8),
            dense ==> rows_dense(*f, first as int, a as int, i as int),
        decreases b - i,
    {
        proof {
            lemma_div_group(i as int, bs as int, g as int);
            assert(in_i64(pkey(*f, i as int)));
            assert(pkey(*f, i as int) == f.pk_b@[g as int] + f.pk_c@[i as int]);
        }
        let k = f.pk_b[g] + f.pk_c[i] as i64;
        if k as i128 != first as i128 + i as i128 {
            dense = false;
        }
        let x = i - a;
        let ghost wb = words@;
        let ghost cb = coarse@;
        if has && f.pt_c[i] == want {
            proof {
                vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, (b - a - 1) as int, 64);
                assert((b - a - 1) as int / 64 < w0.len()) by {
                    vstd::arithmetic::div_mod::lemma_div_is_ordered((b - a - 1) as int, w0.len() * 64 - 1, 64);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(w0.len() * 64 - 1, 64,
                        w0.len() - 1, 63);
                }
                vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, (b - a - 1) as int, 8);
                assert((x as int / 8) / 64 < c0.len()) by {
                    vstd::arithmetic::div_mod::lemma_div_denominator(x as int, 8, 64);
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, (b - a - 1) as int, 512);
                    vstd::arithmetic::div_mod::lemma_div_is_ordered((b - a - 1) as int, c0.len() * 512 - 1, 512);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(c0.len() * 512 - 1, 512,
                        c0.len() - 1, 511);
                }
            }
            set_bit_nu(&mut words, x);
            set_bit_nu(&mut coarse, x / 8);
            proof {
                assert(mrow(*f, a + x));
                assert forall|y: int| 0 <= y < i + 1 - a && #[trigger] bit_at(words@, y) implies bit_at(coarse@, y / 8) by {
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(y, (b - a - 1) as int, 8);
                    vstd::arithmetic::div_mod::lemma_div_denominator(y, 8, 64);
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(y, (b - a - 1) as int, 512);
                    vstd::arithmetic::div_mod::lemma_div_is_ordered((b - a - 1) as int, c0.len() * 512 - 1, 512);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(c0.len() * 512 - 1, 512,
                        c0.len() - 1, 511);
                    if y < x {
                        vstd::arithmetic::div_mod::lemma_div_is_ordered(y, (b - a - 1) as int, 64);
                        assert(bit_at(wb, y));
                    }
                }
                assert forall|y: int| i + 1 - a <= y < words@.len() * 64 implies !#[trigger] bit_at(words@, y) by {
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(y, words@.len() * 64 - 1, 64);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(words@.len() * 64 - 1, 64,
                        words@.len() - 1, 63);
                    assert(!bit_at(wb, y));
                }
                assert forall|y: int| 0 <= y < i + 1 - a implies #[trigger] bit_at(words@, y) == mrow(*f, a + y) by {
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(y, (b - a - 1) as int, 64);
                }
            }
        } else {
            proof {
                assert(!mrow(*f, a + x));
                assert(!bit_at(words@, x as int)) by {
                    assert(x < words@.len() * 64);
                }
            }
        }
        proof {
            if dense {
                assert(pkey(*f, i as int) == first + i);
            }
        }
        i = i + 1;
        if i < b && i == ge {
            proof {
                assert(ge == g * bs + bs);
                assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
                lemma_div_group(i as int, bs as int, (g + 1) as int);
                crate::stores::custpart::interface::common::read::lemma_div_lt(i as int, bs as int, f.pk_b@.len() as int);
            }
            g = g + 1;
            proof { assert(g * bs == i); }
            ge = if n - g * bs > bs { g * bs + bs } else { n };
            let (h2, w2) = want_of(f, g);
            has = h2;
            want = w2;
        }
    }
    PartOut { words, coarse, dense }
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
        (self.a as u64, self.b as u64)
    }

    fn run(self) -> (out: PartOut) {
        let f: &PFilter = &*self.f;
        scan_parts(f, self.first, self.a, self.b, self.words, self.coarse)
    }
}

// ------------------------------------------------------------------------------------------------ the driver

/// Task `t` of `ts` scans part rows `[bs[t], bs[t + 1])`, each boundary but the last a multiple of 512.
pub open spec fn ptasks_ok(ts: Seq<PartTask>, bs: Seq<int>, f: PFilter, first: i64, n: int) -> bool {
    &&& bs.len() == ts.len() + 1
    &&& bs[0] == 0 && bs[ts.len() as int] == n
    &&& forall|t: int| 0 <= t < ts.len() ==> #[trigger] ptask_at(ts, bs, t, f, first, ts.len() as int)
}

/// Task `k` of `ts` (of `nt`) scans part rows `[bs[k], bs[k + 1])`.
pub open spec fn ptask_at(ts: Seq<PartTask>, bs: Seq<int>, k: int, f: PFilter, first: i64, nt: int) -> bool {
    &&& *ts[k].f == f && ts[k].first == first
    &&& ts[k].a as int == bs[k] && ts[k].b as int == bs[k + 1]
    &&& part_pre(ts[k])
    &&& ts[k].words@.len() == (bs[k + 1] - bs[k] + 63) / 64
    &&& ts[k].coarse@.len() == (bs[k + 1] - bs[k] + 511) / 512
    &&& bs[k] % 512 == 0
    &&& k + 1 < nt ==> (bs[k + 1] - bs[k]) % 512 == 0
}

/// `(len + d - 1) / d` units of `d` cover `len`; exactly `len / d` when `d` divides `len`.
proof fn lemma_ceil(len: int, d: int)
    requires len >= 0, d >= 1,
    ensures
        ((len + d - 1) / d) * d >= len,
        len % d == 0 ==> (len + d - 1) / d == len / d && (len / d) * d == len,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len + d - 1, d);
    vstd::arithmetic::div_mod::lemma_mod_bound(len + d - 1, d);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len, d);
    if len % d == 0 {
        assert(len + d - 1 == (len / d) * d + (d - 1)) by (nonlinear_arith)
            requires len == d * (len / d) + len % d, len % d == 0;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(len + d - 1, d, len / d, d - 1);
        assert((len / d) * d == len) by (nonlinear_arith)
            requires len == d * (len / d) + len % d, len % d == 0;
    }
    assert(((len + d - 1) / d) * d >= len) by (nonlinear_arith)
        requires len + d - 1 == d * ((len + d - 1) / d) + (len + d - 1) % d, (len + d - 1) % d < d;
}

/// `ceil(len / d)` without overflow.
fn ceil_div(len: usize, d: usize) -> (q: usize)
    requires d >= 1,
    ensures q as int == (len as int + d as int - 1) / (d as int),
{
    let q = len / d;
    let r = len % d;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len as int, d as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(len as int, d as int);
        if r == 0 {
            assert(len + d - 1 == q * d + (d - 1)) by (nonlinear_arith) requires len as int == d * q + r, r == 0;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(len + d - 1, d as int, q as int, d - 1);
        } else {
            assert(len + d - 1 == (q + 1) * d + (r - 1)) by (nonlinear_arith) requires len as int == d * q + r;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(len + d - 1, d as int, q + 1, r - 1);
        }
        assert(q <= len) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(len as int, 1, d as int);
        }
    }
    proof {
        if r != 0 {
            assert(q + 1 <= len) by (nonlinear_arith) requires len as int == d * q + r, r >= 1, d >= 1, q >= 0;
        }
    }
    if r == 0 { q } else { q + 1 }
}

/// Tasks over part rows `[0, n)` in runs of whole 512-row units.
fn part_tasks(fa: Arc<PFilter>, first: i64, n: usize, workers: usize) -> (r: (Vec<PartTask>, Ghost<Seq<int>>))
    requires pf_shape(*fa), 1 <= n == fa.n_p, n <= 0x1_0000_0000, 1 <= workers <= MAX_WORKERS,
    ensures 1 <= r.0@.len() <= workers, ptasks_ok(r.0@, r.1@, *fa, first, n as int),
{
    let units = ceil_div(n, PALIGN);
    proof {
        lemma_ceil(n as int, 512);
        assert(units >= 1);
    }
    let nt = if workers < units { workers } else { units };
    let per = units / nt;
    proof {
        assert(per >= 1) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(nt as int, units as int, nt as int);
            vstd::arithmetic::div_mod::lemma_div_by_self(nt as int);
        }
        assert(per * nt <= units) by (nonlinear_arith) requires per == units / nt, nt >= 1;
        assert(units * 512 < n + 512) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n + 511, 512);
            vstd::arithmetic::div_mod::lemma_mod_bound(n + 511, 512);
        }
    }
    let mut tasks: Vec<PartTask> = Vec::new();
    let ghost mut bs: Seq<int> = seq![0int];
    let mut t: usize = 0;
    while t < nt
        invariant
            pf_shape(*fa), 1 <= n == fa.n_p, n <= 0x1_0000_0000,
            1 <= nt <= workers, nt <= units, per >= 1, per * nt <= units, units * 512 < n + 512,
            units == (n + 511) / 512, ((n + 511) / 512) * 512 >= n,
            t <= nt,
            tasks@.len() == t,
            bs.len() == t + 1,
            bs[0] == 0,
            t < nt ==> bs[t as int] == t * per * 512,
            t == nt ==> bs[t as int] == n,
            forall|k: int| 0 <= k < t ==> #[trigger] ptask_at(tasks@, bs, k, *fa, first, nt as int),
        decreases nt - t,
    {
        proof {
            assert((t + 1) * per <= nt * per) by (nonlinear_arith) requires t + 1 <= nt, per >= 1;
            assert(t * per * 512 + per * 512 == (t + 1) * per * 512) by (nonlinear_arith);
            assert((t + 1) * per * 512 <= units * 512 - 512 || t + 1 == nt || (t + 1) * per * 512 < n) by {
                if t + 1 < nt {
                    assert((t + 1) * per <= units - per) by (nonlinear_arith)
                        requires t + 2 <= nt, per * nt <= units, per >= 1;
                    assert((t + 1) * per * 512 <= (units - 1) * 512) by (nonlinear_arith)
                        requires (t + 1) * per <= units - per, per >= 1;
                }
            }
        }
        let a = t * per * PALIGN;
        let b = if t + 1 == nt { n } else { (t + 1) * per * PALIGN };
        proof {
            assert(a <= b);
            assert(a % 512 == 0) by {
                vstd::arithmetic::div_mod::lemma_mod_multiples_basic(t * per, 512);
            }
            if t + 1 < nt {
                assert((b - a) == per * 512) by (nonlinear_arith) requires b == (t + 1) * per * 512, a == t * per * 512;
                vstd::arithmetic::div_mod::lemma_mod_multiples_basic(per as int, 512);
            }
            lemma_ceil((b - a) as int, 64);
            lemma_ceil((b - a) as int, 512);
        }
        let words: Vec<u64> = vec![0u64; ceil_div(b - a, 64)];
        let coarse: Vec<u64> = vec![0u64; ceil_div(b - a, PALIGN)];
        let task = PartTask { f: fa.clone(), first, a, b, words, coarse };
        proof {
            assert(part_pre(task));
        }
        let ghost old_tasks = tasks@;
        let ghost old_bs = bs;
        tasks.push(task);
        proof {
            bs = bs.push(b as int);
            assert forall|k: int| 0 <= k < t + 1 implies #[trigger] ptask_at(tasks@, bs, k, *fa, first, nt as int) by {
                if k < t {
                    assert(ptask_at(old_tasks, old_bs, k, *fa, first, nt as int));
                    assert(tasks@[k] == old_tasks[k]);
                    assert(bs[k] == old_bs[k] && bs[k + 1] == old_bs[k + 1]);
                }
            }
        }
        t = t + 1;
    }
    (tasks, Ghost(bs))
}

/// The bitmaps over part rows `[0, e)` and their keys.
pub open spec fn prefix_ok(f: PFilter, first: int, e: int, bits: Seq<u64>, coarse: Seq<u64>) -> bool {
    &&& bits.len() * 64 >= e && coarse.len() * 512 >= e
    &&& forall|x: int| 0 <= x < e ==> #[trigger] bit_at(bits, x) == mrow(f, x)
    &&& forall|x: int| 0 <= x < e && #[trigger] bit_at(bits, x) ==> bit_at(coarse, x / 8)
    &&& rows_dense(f, first, 0, e)
}

/// Appends a task's words (rows `[a, b)`, `a` = 64 times the fine words so far = 512 times the coarse words).
fn append_task(bits: &mut Vec<u64>, coarse: &mut Vec<u64>, out: &PartOut, Ghost(f): Ghost<PFilter>, Ghost(first): Ghost<int>,
    Ghost(a): Ghost<int>, Ghost(b): Ghost<int>)
    requires
        old(bits)@.len() * 64 == a, old(coarse)@.len() * 512 == a, a <= b,
        out.words@.len() * 64 >= b - a, out.coarse@.len() * 512 >= b - a,
        prefix_ok(f, first, a, old(bits)@, old(coarse)@),
        rows_bits(f, a, b, out.words@, out.coarse@),
        rows_dense(f, first, a, b),
    ensures
        final(bits)@ == old(bits)@ + out.words@,
        final(coarse)@ == old(coarse)@ + out.coarse@,
        prefix_ok(f, first, b, final(bits)@, final(coarse)@),
{
    let ghost (b0, c0) = (bits@, coarse@);
    let mut k: usize = 0;
    while k < out.words.len()
        invariant k <= out.words@.len(), bits@ == b0 + out.words@.subrange(0, k as int),
        decreases out.words@.len() - k,
    {
        bits.push(out.words[k]);
        proof { assert(bits@ =~= b0 + out.words@.subrange(0, k + 1)); }
        k = k + 1;
    }
    let mut k: usize = 0;
    while k < out.coarse.len()
        invariant k <= out.coarse@.len(), coarse@ == c0 + out.coarse@.subrange(0, k as int),
        decreases out.coarse@.len() - k,
    {
        coarse.push(out.coarse[k]);
        proof { assert(coarse@ =~= c0 + out.coarse@.subrange(0, k + 1)); }
        k = k + 1;
    }
    proof {
        assert(out.words@.subrange(0, out.words@.len() as int) =~= out.words@);
        assert(out.coarse@.subrange(0, out.coarse@.len() as int) =~= out.coarse@);
        let (ws, cs) = (out.words@, out.coarse@);
        let (nb, nc) = (bits@, coarse@);
        assert forall|x: int| 0 <= x < b implies #[trigger] bit_at(nb, x) == mrow(f, x) by {
            lemma_concat_bit(b0, ws, x);
        }
        assert forall|x: int| 0 <= x < b && #[trigger] bit_at(nb, x) implies bit_at(nc, x / 8) by {
            lemma_concat_bit(b0, ws, x);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(x, b - 1, 8);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(b - 1, (c0.len() + cs.len()) * 512 - 1, 8);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((c0.len() + cs.len()) * 512 - 1, 8,
                (c0.len() + cs.len()) * 64 - 1, 7);
            lemma_concat_bit(c0, cs, x / 8);
            if x >= a {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x - a, 8);
                vstd::arithmetic::div_mod::lemma_mod_bound(x - a, 8);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, 8, c0.len() * 64 + (x - a) / 8, (x - a) % 8);
                assert(x / 8 - c0.len() * 64 == (x - a) / 8);
            } else {
                vstd::arithmetic::div_mod::lemma_div_is_ordered(x, a - 1, 8);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a - 1, 8, c0.len() * 64 - 1, 7);
            }
        }
    }
}

/// The part filter of type `$3`; its bitmaps are built by up to `workers` tasks when the part keys are dense.
pub fn build_pfilter_par(cp: &mut StoredParts, p2: &'static [u8], workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(db): Ghost<Database>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<PFilter, WorkerFailure>)
    requires
        old(cp)@ == sv.custpart, bound_db(sv, db), ps.len() == 3, txt(ps[2]) == p2@,
        1 <= workers <= MAX_WORKERS,
    ensures
        final(cp)@ == old(cp)@,
        r matches Ok(f) ==> pf_from(sv, ps, f) && pf_ok(f),
{
    let f0 = pfilter_base(cp, p2, Ghost(sv), Ghost(db), Ghost(ps));
    let n = f0.n_p;
    if !f0.has_t || n == 0 || n as u64 > 0x1_0000_0000u64 {
        let f = pfilter_serial(&f0);
        return Ok(f);
    }
    proof {
        assert(in_i64(pkey(f0, 0)));
        assert(0int / (f0.bs_p as int) == 0);
    }
    let first = f0.pk_b[0] + f0.pk_c[0] as i64;
    let fb = base_copy(&f0);
    let ghost fv = fb;
    proof {
        lemma_same_base(fv, f0);
    }
    let fa = Arc::new(fb);
    let (tasks, Ghost(tb)) = part_tasks(fa, first, n, workers);
    let ghost ts = tasks@;
    proof {
        assert forall|i: int| 0 <= i < ts.len() implies #[trigger] ts[i].pre() by {
            assert(ptask_at(ts, tb, i, fv, first, ts.len() as int));
        }
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let mut bits: Vec<u64> = Vec::new();
    let mut coarse: Vec<u64> = Vec::new();
    let nt = outs.len();
    let mut t: usize = 0;
    while t < nt
        invariant
            nt == outs@.len(), nt == ts.len(), t <= nt,
            cp@ == old(cp)@, pf_shape(f0), pf_from(sv, ps, f0), same_base(fv, f0),
            ptasks_ok(ts, tb, fv, first, n as int),
            forall|k: int| 0 <= k < nt ==> #[trigger] ts[k].post(outs@[k]),
            pf_shape(fv),
            t < nt ==> bits@.len() * 64 == tb[t as int] && coarse@.len() * 512 == tb[t as int],
            prefix_ok(fv, first as int, tb[t as int], bits@, coarse@),
        decreases nt - t,
    {
        let o = &outs[t];
        if !o.dense {
            let f = pfilter_serial(&f0);
            return Ok(f);
        }
        proof {
            assert(ts[t as int].post(outs@[t as int]));
            assert(part_post(ts[t as int], outs@[t as int]));
            assert(ptask_at(ts, tb, t as int, fv, first, nt as int));
            let (a, b) = (tb[t as int], tb[t + 1]);
            lemma_ceil(b - a, 64);
            lemma_ceil(b - a, 512);
            if t + 1 < nt {
                assert((b - a) % 512 == 0);
                assert((b - a) % 64 == 0) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b - a, 512);
                    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(8 * ((b - a) / 512), 64);
                    assert(b - a == 64 * (8 * ((b - a) / 512))) by (nonlinear_arith)
                        requires b - a == 512 * ((b - a) / 512) + (b - a) % 512, (b - a) % 512 == 0;
                }
            }
        }
        append_task(&mut bits, &mut coarse, o, Ghost(fv), Ghost(first as int), Ghost(tb[t as int]), Ghost(tb[t + 1]));
        proof {
            if t + 1 < nt {
                let (a, b) = (tb[t as int], tb[t + 1]);
                assert(bits@.len() == (a + (b - a)) / 64 || true);
            }
        }
        t = t + 1;
    }
    let f = PFilter {
        use_bits: true, bits, coarse, nbits: n as u64, clamp: 0, pk_lo: first,
        n_p: f0.n_p, bs_p: f0.bs_p, pk_c: f0.pk_c, pk_b: f0.pk_b, pt_c: f0.pt_c, pt_b: f0.pt_b, p_kind: f0.p_kind,
        t: f0.t, has_t: f0.has_t, e32: f0.e32, e64: f0.e64,
    };
    proof {
        lemma_same_base(f, f0);
        lemma_dense_filter(f, fv, first as int);
        assert(pf_from(sv, ps, f));
    }
    Ok(f)
}

/// Dense keys: the bitmap over the part rows is the bitmap over the keys `[first, first + n_p)`.
proof fn lemma_dense_filter(f: PFilter, fv: PFilter, first: int)
    requires
        pf_shape(fv), same_base(f, fv), f.has_t, f.use_bits,
        f.nbits == f.n_p, 1 <= f.n_p <= bits_cap(), f.pk_lo == first,
        f.coarse@.len() >= 1,
        prefix_ok(fv, first, f.n_p as int, f.bits@, f.coarse@),
    ensures pf_ok(f),
{
    lemma_same_base(f, fv);
    let n = f.n_p as int;
    assert forall|i: int| 0 <= i < n implies #[trigger] pkey(f, i) == first + i by {
        assert(pkey(fv, i) == first + i);
    }
    assert forall|i: int| 0 <= i < f.nbits implies #[trigger] bit_at(f.bits@, i) == pmatch(f, f.pk_lo + i) by {
        assert(bit_at(f.bits@, i) == mrow(fv, i));
        if pmatch(f, first + i) {
            let r = choose|r: int| 0 <= r < f.n_p && #[trigger] pkey(f, r) == first + i && ptype(f, r) == f.t;
            assert(pkey(f, r) == first + r);
            assert(r == i);
        }
        if mrow(fv, i) {
            assert(pkey(f, i) == first + i && ptype(f, i) == f.t);
        }
    }
    assert forall|i: int| 0 <= i < f.nbits && #[trigger] bit_at(f.bits@, i) implies bit_at(f.coarse@, i / 8) by {}
    assert forall|v: int| #[trigger] pmatch(f, v) implies f.pk_lo <= v < f.pk_lo + f.nbits by {
        let r = choose|r: int| 0 <= r < f.n_p && #[trigger] pkey(f, r) == v && ptype(f, r) == f.t;
        assert(pkey(f, r) == first + r);
    }
}

} // verus!
