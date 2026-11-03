//! Frame-of-reference encoding of one column over uniform row blocks, in parallel. The stored rows are cut into
//! blocks of `bsize` rows (the last one shorter); block `b` stores its base (the block minimum, or 0 for a
//! column whose values all fit the code width) and per row the code `value - base`, plus the block maximum (a
//! zone map). A block whose value range exceeds the code width makes the encoding fail (`None`), and the caller
//! retries with one-row blocks, which always fit. Values are read through a `ValSrc` at the canonical row a
//! `RowMap` names, so the same encoder serves stored orders that differ from the canonical one.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::builder::common::codes::Code;
use crate::builder::common::colsrc::*;

verus! {

/// First stored row of block `b`.
pub open spec fn blk_lo(bsize: int, b: int) -> int {
    b * bsize
}

/// End (exclusive) of block `b` over `n` rows.
pub open spec fn blk_hi(n: int, bsize: int, b: int) -> int {
    if (b + 1) * bsize < n { (b + 1) * bsize } else { n }
}

/// Number of blocks of `n` rows.
pub open spec fn nblocks(n: int, bsize: int) -> int {
    (n + bsize - 1) / bsize
}

/// Block `b` is encoded: its base and zone maximum lie in the base range of the source, and every row `j` of
/// the block has `base + code == value` and `value <= zmax`, its code at `codes[j - off]`.
pub open spec fn block_ok<C: Code>(src: ValSrc, rm: RowMap, n: int, bsize: int, b: int, base: i128, zmax: i128, codes: Seq<C>, off: int) -> bool {
    &&& in_base_range(src, base as int)
    &&& in_base_range(src, zmax as int)
    &&& forall|j: int| blk_lo(bsize, b) <= j < blk_hi(n, bsize, b) ==> {
        &&& base + C::val(codes[j - off]) == #[trigger] src_val(src, rm_at(rm, j))
        &&& src_val(src, rm_at(rm, j)) <= zmax
    }
}

/// A frame-of-reference column: per row a code, per block a base and a zone maximum.
pub struct ForCol<C: Code> {
    pub codes: Vec<C>,
    pub bases: Vec<i128>,
    pub zmax: Vec<i128>,
}

/// Every block of the column is encoded.
pub open spec fn for_col_ok<C: Code>(col: ForCol<C>, src: ValSrc, rm: RowMap, n: int, bsize: int) -> bool {
    &&& col.codes@.len() == n
    &&& col.bases@.len() == nblocks(n, bsize)
    &&& col.zmax@.len() == nblocks(n, bsize)
    &&& forall|b: int| 0 <= b < nblocks(n, bsize) ==> #[trigger] block_ok(src, rm, n, bsize, b, col.bases@[b], col.zmax@[b], col.codes@, 0)
}

/// Rows of the blocks `[b0, b1)`.
pub open spec fn span_rows(n: int, bsize: int, b0: int, b1: int) -> int {
    if b0 < b1 { blk_hi(n, bsize, b1 - 1) - b0 * bsize } else { 0 }
}

/// One worker task: encode the blocks `[b0, b1)` into preallocated buffers.
pub struct EncodeTask<C: Code> {
    pub src: ValSrc,
    pub rm: RowMap,
    pub n: usize,
    pub bsize: usize,
    pub b0: usize,
    pub b1: usize,
    pub zero_base: bool,
    pub codes: Vec<C>,
    pub bases: Vec<i128>,
    pub zmax: Vec<i128>,
    pub scratch: Vec<i128>,
}

/// A task's buffers, filled, and whether every block fit.
pub struct EncodeOut<C: Code> {
    pub codes: Vec<C>,
    pub bases: Vec<i128>,
    pub zmax: Vec<i128>,
    pub ok: bool,
}

/// Every value of the source is a valid code with base 0.
pub open spec fn fits_zero_base<C: Code>(src: ValSrc, n: int) -> bool {
    forall|i: int| 0 <= i < n ==> 0 <= #[trigger] src_val(src, i) <= C::cap()
}

proof fn lemma_blk_bounds(n: int, bsize: int, b: int)
    requires
        bsize >= 1,
        0 <= b,
        b * bsize < n,
    ensures
        blk_lo(bsize, b) < blk_hi(n, bsize, b) <= n,
        blk_hi(n, bsize, b) - blk_lo(bsize, b) <= bsize,
        blk_hi(n, bsize, b) == blk_lo(bsize, b + 1) || blk_hi(n, bsize, b) == n,
{
    assert((b + 1) * bsize == b * bsize + bsize) by (nonlinear_arith);
}

impl<C: Code> WorkerTask for EncodeTask<C> {
    type Output = EncodeOut<C>;

    open spec fn pre(&self) -> bool {
        &&& src_wf(self.src, self.n as int)
        &&& rm_wf(self.rm, self.n as int)
        &&& 1 <= self.bsize
        &&& self.b0 <= self.b1
        &&& self.b1 * self.bsize <= usize::MAX
        &&& (self.b0 < self.b1 ==> (self.b1 - 1) * self.bsize < self.n)
        &&& self.codes@.len() == span_rows(self.n as int, self.bsize as int, self.b0 as int, self.b1 as int)
        &&& self.bases@.len() == self.b1 - self.b0
        &&& self.zmax@.len() == self.b1 - self.b0
        &&& self.scratch@.len() == self.bsize
        &&& (self.zero_base ==> fits_zero_base::<C>(self.src, self.n as int))
    }

    open spec fn post(&self, out: EncodeOut<C>) -> bool {
        &&& out.codes@.len() == self.codes@.len()
        &&& out.bases@.len() == self.b1 - self.b0
        &&& out.zmax@.len() == self.b1 - self.b0
        &&& (self.bsize == 1 ==> out.ok)
        &&& (out.ok ==> forall|b: int| self.b0 <= b < self.b1 ==> #[trigger] block_ok(self.src, self.rm, self.n as int,
                self.bsize as int, b, out.bases@[b - self.b0], out.zmax@[b - self.b0], out.codes@, self.b0 * self.bsize))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.b0 as u64, self.b1 as u64)
    }

    fn run(self) -> (out: EncodeOut<C>) {
        let EncodeTask { src, rm, n, bsize, b0, b1, zero_base, mut codes, mut bases, mut zmax, mut scratch } = self;
        let ghost off = b0 * bsize;
        let cap = C::cap_u64();
        let clen = codes.len();
        proof {
            if b0 < b1 {
                assert(b0 * bsize <= (b1 - 1) * bsize) by (nonlinear_arith) requires b0 <= b1 - 1, bsize >= 1;
            }
        }
        let mut b = b0;
        let mut cj: usize = 0;
        while b < b1
            invariant
                self.src == src && self.rm == rm && self.n == n && self.bsize == bsize,
                self.b0 == b0 && self.b1 == b1 && self.zero_base == zero_base,
                self.codes@.len() == codes@.len(),
                src_wf(src, n as int),
                rm_wf(rm, n as int),
                1 <= bsize,
                b0 <= b <= b1,
                b1 * bsize <= usize::MAX,
                b0 < b1 ==> (b1 - 1) * bsize < n,
                off == b0 * bsize,
                cap == C::cap(),
                clen == codes@.len(),
                b < b1 ==> cj == b * bsize - off,
                codes@.len() == span_rows(n as int, bsize as int, b0 as int, b1 as int),
                bases@.len() == b1 - b0,
                zmax@.len() == b1 - b0,
                scratch@.len() == bsize,
                zero_base ==> fits_zero_base::<C>(src, n as int),
                forall|bb: int| b0 <= bb < b ==> #[trigger] block_ok(src, rm, n as int, bsize as int, bb, bases@[bb - b0], zmax@[bb - b0], codes@, off),
            decreases b1 - b,
        {
            proof {
                assert(b * bsize <= (b1 - 1) * bsize) by (nonlinear_arith) requires b <= b1 - 1, bsize >= 1;
                assert((b + 1) * bsize <= b1 * bsize) by (nonlinear_arith) requires b + 1 <= b1, bsize >= 1;
                assert((b + 1) * bsize == b * bsize + bsize) by (nonlinear_arith);
                lemma_blk_bounds(n as int, bsize as int, b as int);
                if b + 1 < b1 {
                    assert((b + 1) * bsize <= (b1 - 1) * bsize) by (nonlinear_arith) requires b + 1 <= b1 - 1, bsize >= 1;
                }
                assert((b1 - 1) * bsize + bsize == b1 * bsize) by (nonlinear_arith);
            }
            let lo = b * bsize;
            let hi = if bsize < n - lo { lo + bsize } else { n };
            assert(hi == blk_hi(n as int, bsize as int, b as int));
            assert(cj + (hi - lo) <= codes@.len()) by {
                if b + 1 < b1 {
                    assert(blk_hi(n as int, bsize as int, b1 - 1) >= hi) by {
                        lemma_blk_bounds(n as int, bsize as int, b1 - 1);
                        assert(blk_lo(bsize as int, b1 - 1) >= (b + 1) * bsize);
                    }
                }
            }
            // Pass 1: gather the block's values into the scratch buffer, with their minimum and maximum.
            let mut mn: i128 = 0;
            let mut mx: i128 = 0;
            let mut j = lo;
            while j < hi
                invariant
                    src_wf(src, n as int),
                    rm_wf(rm, n as int),
                    lo <= j <= hi <= n,
                    hi - lo <= bsize,
                    scratch@.len() == bsize,
                    forall|t: int| 0 <= t < j - lo ==> #[trigger] scratch@[t] == src_val(src, rm_at(rm, lo + t)),
                    j > lo ==> in_base_range(src, mn as int) && in_base_range(src, mx as int) && mn <= mx,
                    j == lo + 1 ==> mn == mx,
                    forall|t: int| 0 <= t < j - lo ==> mn <= #[trigger] src_val(src, rm_at(rm, lo + t)) <= mx,
                decreases hi - j,
            {
                let i = rm_get(&rm, n, j);
                let v = src_get(&src, n, i);
                proof {
                    lemma_src_range(src, n as int, i as int);
                }
                scratch[j - lo] = v;
                if j == lo {
                    mn = v;
                    mx = v;
                } else {
                    if v < mn {
                        mn = v;
                    }
                    if v > mx {
                        mx = v;
                    }
                }
                proof {
                    assert(lo + (j - lo) == j);
                }
                j = j + 1;
            }
            let base: i128 = if zero_base { 0 } else { mn };
            if !zero_base && mx - mn > cap as i128 {
                proof {
                    if bsize == 1 {
                        assert(hi == lo + 1);
                        assert(j == hi);
                        assert(mn == mx);
                        assert(false);
                    }
                }
                let out = EncodeOut { codes, bases, zmax, ok: false };
                assert(out.codes@.len() == span_rows(n as int, bsize as int, b0 as int, b1 as int));
                assert(out.bases@.len() == b1 - b0);
                assert(out.zmax@.len() == b1 - b0);
                return out;
            }
            proof {
                if zero_base {
                    assert(src_val(src, rm_at(rm, lo as int)) == scratch@[0]);
                    assert(0 <= src_val(src, rm_at(rm, lo as int)));
                }
            }
            // Pass 2: codes relative to the base.
            let ghost before = codes@;
            let mut t: usize = 0;
            while t < hi - lo
                invariant
                    src_wf(src, n as int),
                    rm_wf(rm, n as int),
                    lo < hi <= n,
                    t <= hi - lo,
                    cap == C::cap(),
                    clen == codes@.len(),
                    cj + (hi - lo) <= codes@.len(),
                    codes@.len() == before.len(),
                    scratch@.len() == bsize,
                    hi - lo <= bsize,
                    forall|u: int| 0 <= u < hi - lo ==> #[trigger] scratch@[u] == src_val(src, rm_at(rm, lo + u)),
                    forall|u: int| 0 <= u < hi - lo ==> base <= #[trigger] src_val(src, rm_at(rm, lo + u)) <= base + cap,
                    forall|k: int| 0 <= k < cj ==> #[trigger] codes@[k] == before[k],
                    forall|u: int| 0 <= u < t ==> base + C::val(#[trigger] codes@[cj + u]) == scratch@[u],
                decreases hi - lo - t,
            {
                let code = (scratch[t] - base) as u64;
                let c = C::from_u64(code);
                codes[cj + t] = c;
                t = t + 1;
            }
            bases[b - b0] = base;
            zmax[b - b0] = mx;
            proof {
                assert(in_base_range(src, base as int)) by {
                    if zero_base {
                        lemma_src_range(src, n as int, rm_at(rm, lo as int));
                        assert(scratch@[0] == src_val(src, rm_at(rm, lo + 0)));
                    }
                }
                assert forall|bb: int| b0 <= bb < b + 1 implies #[trigger] block_ok(src, rm, n as int, bsize as int, bb,
                    bases@[bb - b0], zmax@[bb - b0], codes@, off) by {
                    if bb < b {
                        assert(block_ok(src, rm, n as int, bsize as int, bb, bases@[bb - b0], zmax@[bb - b0], before, off));
                        assert(blk_hi(n as int, bsize as int, bb) <= lo) by {
                            assert(bb * bsize <= b * bsize) by (nonlinear_arith) requires bb <= b, bsize >= 1;
                            lemma_blk_bounds(n as int, bsize as int, bb);
                            assert((bb + 1) * bsize <= b * bsize) by (nonlinear_arith) requires bb + 1 <= b, bsize >= 1;
                        }
                        assert forall|j: int| blk_lo(bsize as int, bb) <= j < blk_hi(n as int, bsize as int, bb) implies {
                            &&& bases@[bb - b0] + C::val(codes@[j - off]) == #[trigger] src_val(src, rm_at(rm, j))
                            &&& src_val(src, rm_at(rm, j)) <= zmax@[bb - b0]
                        } by {
                            assert(blk_lo(bsize as int, bb) >= off) by {
                                assert(bb * bsize >= b0 * bsize) by (nonlinear_arith) requires bb >= b0, bsize >= 1;
                            }
                            assert(codes@[j - off] == before[j - off]);
                        }
                    } else {
                        assert forall|j: int| blk_lo(bsize as int, bb) <= j < blk_hi(n as int, bsize as int, bb) implies {
                            &&& bases@[bb - b0] + C::val(codes@[j - off]) == #[trigger] src_val(src, rm_at(rm, j))
                            &&& src_val(src, rm_at(rm, j)) <= zmax@[bb - b0]
                        } by {
                            let u = j - lo;
                            assert(j - off == cj + u);
                            assert(lo + u == j);
                            assert(scratch@[u] == src_val(src, rm_at(rm, lo + u)));
                        }
                    }
                }
            }
            cj = cj + (hi - lo);
            b = b + 1;
        }
        EncodeOut { codes, bases, zmax, ok: true }
    }
}

/// Rows covered by the blocks before `b`: `min(b * bsize, n)`.
pub open spec fn rows_before(n: int, bsize: int, b: int) -> int {
    if b * bsize < n { b * bsize } else { n }
}

proof fn lemma_span(n: int, bsize: int, b0: int, b1: int)
    requires
        bsize >= 1,
        0 <= b0 <= b1,
        b0 < b1 ==> (b1 - 1) * bsize < n,
    ensures
        span_rows(n, bsize, b0, b1) == rows_before(n, bsize, b1) - rows_before(n, bsize, b0),
        rows_before(n, bsize, b0) <= rows_before(n, bsize, b1),
        b0 < b1 ==> rows_before(n, bsize, b0) == b0 * bsize,
{
    if b0 < b1 {
        assert(b0 * bsize <= (b1 - 1) * bsize) by (nonlinear_arith) requires b0 <= b1 - 1, bsize >= 1;
        assert(b1 * bsize == (b1 - 1) * bsize + bsize) by (nonlinear_arith);
    }
}

/// `n == d * (n / d) + n % d` for unsigned machine division.
proof fn lemma_divmod(n: int, d: int)
    requires n >= 0, d >= 1,
    ensures
        n == (n / d) * d + n % d,
        0 <= n % d < d,
        n / d >= 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, d);
    assert(d * (n / d) == (n / d) * d) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(n, d);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(n, d);
}

/// Number of blocks of `n` rows, computed without overflow.
pub fn block_count(n: usize, bsize: usize) -> (nb: usize)
    requires bsize >= 1,
    ensures
        nb == nblocks(n as int, bsize as int),
        nb * bsize >= n,
        nb > 0 ==> (nb - 1) * bsize < n,
        nb <= n,
{
    let q = n / bsize;
    let r = n % bsize;
    proof {
        lemma_divmod(n as int, bsize as int);
        assert(q * bsize <= n);
        assert(q <= n) by (nonlinear_arith) requires q * bsize <= n, bsize >= 1, q >= 0;
        if r != 0 {
            assert(q < n) by (nonlinear_arith) requires q * bsize + r == n, bsize >= 1, q >= 0, r >= 1;
        }
    }
    let nb = if r == 0 { q } else { q + 1 };
    proof {
        let m = n as int + bsize as int - 1;
        if r == 0 {
            assert(m == q * bsize + (bsize - 1));
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(m, bsize as int, q as int, (bsize - 1) as int);
            if nb > 0 {
                assert((nb - 1) * bsize < n) by (nonlinear_arith) requires nb == q, q >= 1, n == q * bsize, bsize >= 1;
            }
        } else {
            assert(m == (q + 1) * bsize + (r - 1)) by (nonlinear_arith) requires m == n + bsize - 1, n == q * bsize + r;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(m, bsize as int, (q + 1) as int, (r - 1) as int);
            assert((nb - 1) * bsize < n) by (nonlinear_arith) requires nb == q + 1, n == q * bsize + r, r >= 1;
            assert(nb * bsize >= n) by (nonlinear_arith) requires nb == q + 1, n == q * bsize + r, r < bsize;
        }
    }
    nb
}

/// `block_ok` moves to another code sequence that agrees on the block's rows.
proof fn lemma_block_ok_transfer<C: Code>(src: ValSrc, rm: RowMap, n: int, bsize: int, b: int, base: i128, zmax: i128,
    c1: Seq<C>, off1: int, c2: Seq<C>, off2: int)
    requires
        block_ok(src, rm, n, bsize, b, base, zmax, c1, off1),
        forall|u: int| blk_lo(bsize, b) - off2 <= u < blk_hi(n, bsize, b) - off2 ==> #[trigger] c2[u] == c1[u + off2 - off1],
    ensures
        block_ok(src, rm, n, bsize, b, base, zmax, c2, off2),
{
    assert forall|j: int| blk_lo(bsize, b) <= j < blk_hi(n, bsize, b) implies {
        &&& base + C::val(c2[j - off2]) == #[trigger] src_val(src, rm_at(rm, j))
        &&& src_val(src, rm_at(rm, j)) <= zmax
    } by {
        let u = j - off2;
        assert(c2[u] == c1[u + off2 - off1]);
        assert(u + off2 - off1 == j - off1);
    }
}

/// The rows of block `b` lie before `rows_before(b + 1)`.
proof fn lemma_block_rows(n: int, bsize: int, b: int)
    requires
        bsize >= 1,
        0 <= b,
        b * bsize < n,
    ensures
        rows_before(n, bsize, b) == blk_lo(bsize, b),
        blk_hi(n, bsize, b) == rows_before(n, bsize, b + 1),
{
}

/// Frame-of-reference encoding of `src` (read at the canonical rows `rm` names) over blocks of `bsize` stored
/// rows, with at most `workers` tasks. `Ok(None)`: some block's value range exceeds the code width (never for
/// `bsize == 1`).
pub fn encode_column<C: Code>(src: &ValSrc, rm: &RowMap, n: usize, bsize: usize, zero_base: bool, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Option<ForCol<C>>, WorkerFailure>)
    requires
        src_wf(*src, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
        zero_base ==> fits_zero_base::<C>(*src, n as int),
    ensures
        r matches Ok(Some(col)) ==> for_col_ok(col, *src, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
{
    let nb = block_count(n, bsize);
    let ntasks = if nb < workers { nb } else { workers };
    let chunk = if ntasks == 0 { 1 } else if nb % ntasks == 0 { nb / ntasks } else { nb / ntasks + 1 };
    proof {
        assert(nb * bsize <= usize::MAX) by {
            if nb > 0 {
                assert(nb * bsize == (nb - 1) * bsize + bsize) by (nonlinear_arith);
            }
        }
        if ntasks > 0 {
            lemma_divmod(nb as int, ntasks as int);
            let q = nb / ntasks;
            let r = nb % ntasks;
            if r == 0 {
                assert(chunk * ntasks >= nb);
            } else {
                assert(chunk * ntasks >= nb) by (nonlinear_arith) requires chunk == q + 1, nb == q * ntasks + r, r < ntasks;
            }
            assert(chunk >= 1) by (nonlinear_arith) requires chunk * ntasks >= nb, nb >= 1, ntasks >= 1, chunk >= 0;
        }
    }
    // One task per chunk of blocks, in block order.
    let mut tasks: Vec<EncodeTask<C>> = Vec::new();
    let mut b0: usize = 0;
    while b0 < nb
        invariant
            src_wf(*src, n as int),
            rm_wf(*rm, n as int),
            1 <= bsize,
            nb == nblocks(n as int, bsize as int),
            nb * bsize >= n,
            nb > 0 ==> (nb - 1) * bsize < n,
            nb * bsize <= usize::MAX,
            chunk >= 1,
            ntasks <= MAX_WORKERS,
            nb > 0 ==> ntasks >= 1 && chunk * ntasks >= nb,
            b0 <= nb,
            tasks@.len() <= ntasks || nb == 0,
            b0 < nb ==> b0 == tasks@.len() * chunk,
            zero_base ==> fits_zero_base::<C>(*src, n as int),
            forall|t: int| 0 <= t < tasks@.len() ==> (#[trigger] tasks@[t]).pre() && tasks@[t].b0 < tasks@[t].b1,
            forall|t: int| 0 <= t < tasks@.len() ==> (#[trigger] tasks@[t]).src == *src && tasks@[t].rm == *rm
                && tasks@[t].n == n && tasks@[t].bsize == bsize && tasks@[t].zero_base == zero_base,
            tasks@.len() == 0 ==> b0 == 0,
            tasks@.len() > 0 ==> tasks@[0].b0 == 0 && tasks@[tasks@.len() - 1].b1 == b0,
            forall|t: int| 0 <= t < tasks@.len() - 1 ==> #[trigger] tasks@[t].b1 == tasks@[t + 1].b0,
        decreases nb - b0,
    {
        proof {
            assert(tasks@.len() < ntasks) by (nonlinear_arith)
                requires tasks@.len() * chunk < nb, chunk * ntasks >= nb, chunk >= 1;
        }
        let b1 = if nb - b0 > chunk { b0 + chunk } else { nb };
        proof {
            assert((b1 - 1) * bsize < n) by {
                assert((b1 - 1) * bsize <= (nb - 1) * bsize) by (nonlinear_arith) requires b1 - 1 <= nb - 1, bsize >= 1;
            }
            assert(b1 * bsize <= nb * bsize) by (nonlinear_arith) requires b1 <= nb, bsize >= 1;
            assert(b0 * bsize <= b1 * bsize) by (nonlinear_arith) requires b0 <= b1, bsize >= 1;
            lemma_span(n as int, bsize as int, b0 as int, b1 as int);
            if b1 < nb {
                assert(b1 == (tasks@.len() + 1) * chunk) by (nonlinear_arith) requires b1 == b0 + chunk, b0 == tasks@.len() * chunk;
            }
        }
        let hi_rows = if b1 * bsize < n { b1 * bsize } else { n };
        let lo_rows = if b0 * bsize < n { b0 * bsize } else { n };
        let rows = hi_rows - lo_rows;
        let codes: Vec<C> = vec![C::zero(); rows];
        let bases: Vec<i128> = vec![0i128; b1 - b0];
        let zmax: Vec<i128> = vec![0i128; b1 - b0];
        let scratch: Vec<i128> = vec![0i128; bsize];
        let task = EncodeTask { src: src_clone(src), rm: rm_clone(rm), n, bsize, b0, b1, zero_base, codes, bases, zmax, scratch };
        let ghost old_tasks = tasks@;
        tasks.push(task);
        proof {
            assert(tasks@[tasks@.len() - 1].b1 == b1);
            assert forall|t: int| 0 <= t < tasks@.len() - 1 implies #[trigger] tasks@[t].b1 == tasks@[t + 1].b0 by {
                if t < old_tasks.len() - 1 {
                    assert(tasks@[t] == old_tasks[t] && tasks@[t + 1] == old_tasks[t + 1]);
                }
            }
        }
        b0 = b1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    // Concatenate the task outputs in block order.
    let mut codes: Vec<C> = Vec::new();
    let mut bases: Vec<i128> = Vec::new();
    let mut zmax: Vec<i128> = Vec::new();
    let ghost all_outs = outs@;
    let mut outs = outs;
    let nt = outs.len();
    let mut t: usize = 0;
    while t < nt
        invariant
            nt == all_outs.len(),
            nt == tv.len(),
            t <= nt,
            outs@ == all_outs.subrange(t as int, nt as int),
            forall|u: int| 0 <= u < tv.len() ==> (#[trigger] tv[u]).pre() && tv[u].b0 < tv[u].b1,
            forall|u: int| 0 <= u < nt ==> tv[u].post(#[trigger] all_outs[u]),
            forall|u: int| 0 <= u < tv.len() ==> (#[trigger] tv[u]).src == *src && tv[u].rm == *rm
                && tv[u].n == n && tv[u].bsize == bsize && tv[u].zero_base == zero_base,
            tv.len() > 0 ==> tv[0].b0 == 0 && tv[tv.len() - 1].b1 == nb,
            tv.len() == 0 ==> nb == 0,
            forall|u: int| 0 <= u < tv.len() - 1 ==> #[trigger] tv[u].b1 == tv[u + 1].b0,
            1 <= bsize,
            nb == nblocks(n as int, bsize as int),
            nb * bsize >= n,
            bases@.len() == (if t == 0 { 0 } else { tv[t - 1].b1 as int }),
            zmax@.len() == bases@.len(),
            codes@.len() == rows_before(n as int, bsize as int, bases@.len() as int),
            forall|b: int| 0 <= b < bases@.len() ==> #[trigger] block_ok(*src, *rm, n as int, bsize as int, b, bases@[b], zmax@[b], codes@, 0),
        decreases nt - t,
    {
        let mut o = outs.remove(0);
        proof {
            assert(o == all_outs[t as int]);
            assert(tv[t as int].post(o));
            if t > 0 {
                assert(tv[t - 1].b1 == tv[(t - 1) + 1].b0);
            }
        }
        if !o.ok {
            return Ok(None);
        }
        let ghost task = tv[t as int];
        let ghost old_codes = codes@;
        let ghost old_bases = bases@;
        let ghost old_zmax = zmax@;
        let ghost oc = o.codes@;
        let ghost ob = o.bases@;
        let ghost oz = o.zmax@;
        codes.append(&mut o.codes);
        bases.append(&mut o.bases);
        zmax.append(&mut o.zmax);
        proof {
            let (tb0, tb1) = (task.b0 as int, task.b1 as int);
            assert(old_bases.len() == tb0);
            lemma_span(n as int, bsize as int, tb0, tb1);
            assert forall|b: int| 0 <= b < bases@.len() implies #[trigger] block_ok(*src, *rm, n as int, bsize as int, b, bases@[b], zmax@[b], codes@, 0) by {
                if b < tb0 {
                    assert(block_ok(*src, *rm, n as int, bsize as int, b, old_bases[b], old_zmax[b], old_codes, 0));
                    assert(bases@[b] == old_bases[b] && zmax@[b] == old_zmax[b]);
                    assert(b * bsize < n) by {
                        assert(b * bsize <= (tb1 - 1) * bsize) by (nonlinear_arith) requires b <= tb1 - 1, bsize >= 1;
                    }
                    lemma_block_rows(n as int, bsize as int, b);
                    assert(rows_before(n as int, bsize as int, b + 1) <= rows_before(n as int, bsize as int, tb0)) by {
                        assert((b + 1) * bsize <= tb0 * bsize) by (nonlinear_arith) requires b + 1 <= tb0, bsize >= 1;
                    }
                    lemma_block_ok_transfer(*src, *rm, n as int, bsize as int, b, old_bases[b], old_zmax[b], old_codes, 0, codes@, 0);
                } else {
                    assert(block_ok(*src, *rm, n as int, bsize as int, b, ob[b - tb0], oz[b - tb0], oc, tb0 * bsize));
                    assert(bases@[b] == ob[b - tb0] && zmax@[b] == oz[b - tb0]);
                    assert(b * bsize < n) by {
                        assert(b * bsize <= (tb1 - 1) * bsize) by (nonlinear_arith) requires b <= tb1 - 1, bsize >= 1;
                    }
                    lemma_block_rows(n as int, bsize as int, b);
                    assert(tb0 * bsize <= b * bsize) by (nonlinear_arith) requires tb0 <= b, bsize >= 1;
                    assert(rows_before(n as int, bsize as int, b + 1) <= rows_before(n as int, bsize as int, tb1)) by {
                        assert((b + 1) * bsize <= tb1 * bsize) by (nonlinear_arith) requires b + 1 <= tb1, bsize >= 1;
                    }
                    lemma_block_ok_transfer(*src, *rm, n as int, bsize as int, b, ob[b - tb0], oz[b - tb0], oc, tb0 * bsize, codes@, 0);
                }
            }
        }
        t = t + 1;
    }
    proof {
        if nt == 0 {
            assert(nb == 0);
        }
        assert(bases@.len() == nb);
        assert(codes@.len() == n) by {
            assert(nb * bsize >= n);
        }
    }
    Ok(Some(ForCol { codes, bases, zmax }))
}

} // verus!
