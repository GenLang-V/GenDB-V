//! The part pass: one bit per part row, set when its name matches `$1` (`bits_ok`), and whether `p_partkey` is
//! positional (`p_partkey[r] == pbase + r`, so a part key finds its row by subtraction).
//!
//! Fast path (`part_pass_fast`, `PartTask`): for a contains pattern `'%<lit>%'` (`common::like_contains`), each task
//! scans a range of 64-row words, testing each name for an occurrence of `lit` (exact when the name is ASCII, which
//! the task checks). General path (`part_pass_general`, serial): the verified `LIKE` on every name, which also finds
//! a part row whose `LIKE` raises.
use vstd::prelude::*;
use crate::agent::common::zeroed::zeros_u64;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::exec::value::{EVal, view_result};
use crate::exec::fns::like::like_value_exec;
use crate::link::query::{text_wf, text_at};
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::lemma_like_res;
use crate::agent::columns::*;
use crate::agent::common::bits::*;
use crate::agent::common::like_contains::*;
use crate::agent::common::split::*;
use crate::agent::common::text_scan::*;

verus! {

// ------------------------------------------------------------------------------------------------ specification

/// Number of 64-row words of a bitmap over `n` rows.
pub open spec fn nwords(n: int) -> int { (n + 63) / 64 }

/// Part row `r`'s name matches `$1`.
pub open spec fn match_bit(sv: StoresView, ps: Seq<Literal>, r: int) -> bool { like_true(pname(sv, r), pat_of(ps)) }

/// One bit per part row (row `u` is bit `u % 64` of word `u / 64`), set exactly for the matching rows.
pub open spec fn bits_ok(bits: Seq<u64>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& bits.len() == nwords(n_p(sv))
    &&& forall|u: int| 0 <= u < 64 * bits.len() ==> #[trigger] word_bit(bits, u) == (u < n_p(sv) && match_bit(sv, ps, u))
}

/// No part name's `LIKE` raises.
pub open spec fn likes_all_ok(sv: StoresView, ps: Seq<Literal>) -> bool {
    forall|r: int| 0 <= r < n_p(sv) ==> #[trigger] like_ok(pname(sv, r), pat_of(ps))
}

/// Key column `keys` is `base + r` at row `r`.
pub open spec fn positional(keys: Seq<i64>, base: int) -> bool {
    forall|r: int| 0 <= r < keys.len() ==> #[trigger] keys[r] as int == base + r
}

/// Part row `x`'s `LIKE` does not raise and its match bit is whether its name contains the literal.
pub open spec fn row_ok(sv: StoresView, ps: Seq<Literal>, x: int) -> bool {
    like_ok(pname(sv, x), pat_of(ps)) && match_bit(sv, ps, x) == has_sub(pname(sv, x), contains_lit(pat_of(ps)))
}

/// The part names of `sv` and their byte ranges.
pub open spec fn names_ok(poffs: Seq<i64>, pbytes: Seq<u8>, np: int, sv: StoresView) -> bool {
    &&& poffs == pname_col(sv).offsets && pbytes == pname_col(sv).bytes && pbytes.len() <= usize::MAX
    &&& np == n_p(sv) && text_wf(pname_col(sv), n_p(sv))
}

/// The bytes of part row `r`'s name are its offsets' range.
proof fn lemma_name_range(poffs: Seq<i64>, pbytes: Seq<u8>, np: int, sv: StoresView, r: int)
    requires names_ok(poffs, pbytes, np, sv), 0 <= r < np,
    ensures
        0 <= poffs[r] <= poffs[r + 1] <= pbytes.len(),
        pbytes.subrange(poffs[r] as int, poffs[r + 1] as int) == pname(sv, r),
{
}

/// For a contains pattern, an ASCII name matches exactly when the literal occurs in it, without error.
proof fn lemma_match_contains(sv: StoresView, ps: Seq<Literal>, r: int)
    requires contains_pattern(pat_of(ps)), ascii(pname(sv, r)),
    ensures
        like_ok(pname(sv, r), pat_of(ps)),
        match_bit(sv, ps, r) == has_sub(pname(sv, r), contains_lit(pat_of(ps))),
{
    lemma_like_contains(pname(sv, r), pat_of(ps));
}

/// The byte range of part row `r`'s name.
fn name_bounds(poffs: &[i64], pbytes: &[u8], np: usize, r: usize, Ghost(sv): Ghost<StoresView>) -> (se: (usize, usize))
    requires names_ok(poffs@, pbytes@, np as int, sv), r < np,
    ensures se.0 <= se.1 <= pbytes@.len(), pbytes@.subrange(se.0 as int, se.1 as int) == pname(sv, r as int),
    no_unwind
{
    proof { lemma_name_range(poffs@, pbytes@, np as int, sv, r as int); }
    let s = poffs[r];
    let e = poffs[r + 1];
    assert(0 <= s <= e <= pbytes@.len());
    let su = s as usize;
    let eu = e as usize;
    assert(su as int == s as int && eu as int == e as int);
    (su, eu)
}

// ------------------------------------------------------------------------------------------------ the fast path

/// One task of the fast part pass: words `w0..w1` of the bitmap (part rows `64 * w0 .. min(64 * w1, np)`).
pub struct PartTask {
    pub pkey: &'static [i64],
    pub poffs: &'static [i64],
    pub pbytes: &'static [u8],
    pub np: usize,
    pub lit: Arc<Vec<u8>>,
    pub m: usize,
    pub w0: usize,
    pub w1: usize,
    pub pbase: i64,
    pub out: Vec<u64>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

/// The words `w0 + i` of `out` (for `i < out.len()`) are the bitmap's: names in range are ASCII and their bits set
/// exactly for the matching rows.
pub open spec fn words_ok(out: Seq<u64>, w0: int, sv: StoresView, ps: Seq<Literal>) -> bool {
    forall|i: int, b: int| 0 <= i < out.len() && 0 <= b < 64 ==>
        #[trigger] bit(out[i], b as u64) == ((w0 + i) * 64 + b < n_p(sv) && match_bit(sv, ps, (w0 + i) * 64 + b))
}

/// The rows `lo..hi` (of the part table) have ASCII names that do not raise.
pub open spec fn rows_like_ok(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> bool {
    forall|r: int| lo <= r < hi && r < n_p(sv) ==> #[trigger] like_ok(pname(sv, r), pat_of(ps))
}

/// The part names as a text run (`common::text_scan`).
proof fn lemma_names_run(poffs: Seq<i64>, pbytes: Seq<u8>, np: int, sv: StoresView)
    requires names_ok(poffs, pbytes, np, sv),
    ensures
        offs_wf(poffs, np, pbytes.len() as int),
        forall|x: int| 0 <= x < np ==> #[trigger] val(poffs, pbytes, x) == pname(sv, x),
{
}

/// Whether `p_partkey` is `pbase + r` at every row `r` of `lo..hi`.
fn keys_positional(pkey: &[i64], lo: usize, hi: usize, pbase: i64, Ghost(np): Ghost<int>) -> (r: bool)
    requires lo <= hi <= np, pkey@.len() == np, 0 <= pbase, pbase + np < i64::MAX,
    ensures r ==> forall|x: int| lo <= x < hi ==> #[trigger] pkey@[x] as int == pbase + x,
    no_unwind
{
    let mut x = lo;
    while x < hi
        invariant lo <= x <= hi <= np, pkey@.len() == np, 0 <= pbase, pbase + np < i64::MAX,
            forall|y: int| lo <= y < x ==> #[trigger] pkey@[y] as int == pbase + y,
        decreases hi - x,
    {
        if pkey[x] != pbase + x as i64 {
            return false;
        }
        x = x + 1;
    }
    true
}

impl WorkerTask for PartTask {
    type Output = (Vec<u64>, bool, bool);

    open spec fn pre(&self) -> bool {
        &&& self.pkey@ == pk(self.sv@)
        &&& names_ok(self.poffs@, self.pbytes@, self.np as int, self.sv@)
        &&& contains_pattern(pat_of(self.ps@)) && (*self.lit)@ == contains_lit(pat_of(self.ps@)) && self.m == (*self.lit)@.len()
        &&& self.w0 <= self.w1 <= nwords(self.np as int) && self.out@.len() == self.w1 - self.w0
        &&& forall|i: int| 0 <= i < self.out@.len() ==> #[trigger] self.out@[i] == 0u64
        &&& 0 <= self.pbase && self.pbase + self.np < i64::MAX && self.np + 128 < usize::MAX
    }

    open spec fn post(&self, out: (Vec<u64>, bool, bool)) -> bool {
        &&& out.0@.len() == self.w1 - self.w0
        &&& out.1 ==> words_ok(out.0@, self.w0 as int, self.sv@, self.ps@)
            && rows_like_ok(self.sv@, self.ps@, self.w0 * 64, self.w1 * 64)
        &&& out.2 ==> forall|r: int| self.w0 * 64 <= r < self.w1 * 64 && r < self.np ==> #[trigger] pk(self.sv@)[r] as int == self.pbase + r
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.w0 as u64, self.w1 as u64)
    }

    fn run(self) -> (out: (Vec<u64>, bool, bool)) {
        let PartTask { pkey, poffs, pbytes, np, lit, m, w0, w1, pbase, out, sv, ps } = self;
        let ghost sv = sv@;
        let ghost ps = ps@;
        let litv: &Vec<u8> = &*lit;
        let mut out = out;
        if w0 == w1 {
            return (out, true, true);
        }
        proof {
            assert(m >= 1) by { assert(pat_of(ps).len() >= 3); }
            lemma_names_run(poffs@, pbytes@, np as int, sv);
            // a nonempty word range starts below np
            assert(w0 * 64 < np) by (nonlinear_arith) requires w0 < w1, w1 <= (np + 63) / 64;
        }
        let lo = w0 * 64;
        let hi = if w1 * 64 < np { w1 * 64 } else { np };
        proof {
            assert(hi - lo <= 64 * out@.len()) by (nonlinear_arith) requires hi <= w1 * 64, lo == w0 * 64, out@.len() == w1 - w0;
        }
        let asc = contains_bits(poffs, pbytes, np, lo, hi, litv, m, &mut out);
        let posok = keys_positional(pkey, lo, hi, pbase, Ghost(np as int));
        proof {
            if asc {
                assert forall|i: int, b: int| 0 <= i < out@.len() && 0 <= b < 64 implies
                    #[trigger] bit(out@[i], b as u64) == ((w0 + i) * 64 + b < n_p(sv) && match_bit(sv, ps, (w0 + i) * 64 + b)) by {
                    let x = (w0 + i) * 64 + b;
                    assert(x - lo == 64 * i + b) by (nonlinear_arith) requires x == (w0 + i) * 64 + b, lo == w0 * 64;
                    assert((x - lo) / 64 == i && (x - lo) % 64 == b) by (nonlinear_arith) requires x - lo == 64 * i + b, 0 <= b < 64, 0 <= i;
                    assert(row_bit(out@, lo as int, x) == bit(out@[i], b as u64));
                    assert(x < lo + 64 * out@.len()) by (nonlinear_arith) requires x - lo == 64 * i + b, 0 <= b < 64, i < out@.len();
                    assert(x < w1 * 64) by (nonlinear_arith) requires x == (w0 + i) * 64 + b, 0 <= b < 64, i < w1 - w0;
                    if x < hi {
                        assert(ascii(val(poffs@, pbytes@, x)));
                        assert(val(poffs@, pbytes@, x) == pname(sv, x));
                        lemma_match_contains(sv, ps, x);
                    }
                }
                assert forall|r: int| w0 * 64 <= r < w1 * 64 && r < n_p(sv) implies #[trigger] like_ok(pname(sv, r), pat_of(ps)) by {
                    assert(ascii(val(poffs@, pbytes@, r)));
                    assert(val(poffs@, pbytes@, r) == pname(sv, r));
                    lemma_match_contains(sv, ps, r);
                }
            }
        }
        (out, asc, posok)
    }
}

/// The bitmap and the positional check, by `k` tasks over word ranges (the calling thread runs a single task).
/// `Ok((bits, true, pos))`: the bitmap of a contains pattern (every name ASCII), `pos` whether `p_partkey` is
/// positional from `pbase`; `Ok((_, false, _))`: some name is not ASCII.
pub fn part_pass_fast(c: &Cols, lit: Vec<u8>, pbase: i64, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<(Vec<u64>, bool, bool), WorkerFailure>)
    requires
        cols_ok(*c, sv), 1 <= workers <= MAX_WORKERS,
        contains_pattern(pat_of(ps)), lit@ == contains_lit(pat_of(ps)),
        0 <= pbase, pbase + c.np < i64::MAX, c.np + 128 < usize::MAX,
    ensures
        r matches Ok((bits, asc, pos)) ==> {
            &&& asc ==> bits_ok(bits@, sv, ps) && likes_all_ok(sv, ps)
            &&& pos ==> positional(pk(sv), pbase as int)
        },
{
    let np = c.np;
    let nw = np / 64 + if np % 64 == 0 { 0 } else { 1 };
    assert(nw == nwords(np as int));
    let m = lit.len();
    assert(m >= 1) by { assert(pat_of(ps).len() >= 3); }
    let lit = Arc::new(lit);
    let k = workers;
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            t <= k, k == workers, 1 <= k <= MAX_WORKERS, tasks@.len() == t, nw == nwords(np as int), np == c.np,
            cols_ok(*c, sv), contains_pattern(pat_of(ps)), (*lit)@ == contains_lit(pat_of(ps)), m == (*lit)@.len(),
            0 <= pbase, pbase + np < i64::MAX, np + 128 < usize::MAX,
            forall|j: int| 0 <= j < t ==> (#[trigger] tasks@[j]).pre() && tasks@[j].sv@ == sv && tasks@[j].ps@ == ps
                && tasks@[j].w0 == split(nw as int, k as int, j) && tasks@[j].w1 == split(nw as int, k as int, j + 1)
                && tasks@[j].np == np && tasks@[j].pbase == pbase,
        decreases k - t,
    {
        let w0 = split_exec(nw, k, t);
        let w1 = split_exec(nw, k, t + 1);
        proof { lemma_split(nw as int, k as int, t as int, t + 1); lemma_split(nw as int, k as int, t + 1, k as int); }
        let task = PartTask { pkey: c.pkey, poffs: c.poffs, pbytes: c.pbytes, np, lit: lit.clone(), m, w0, w1, pbase,
            out: zeros_u64(w1 - w0), sv: Ghost(sv), ps: Ghost(ps) };
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = if k == 1 {
        let task = tasks.pop().unwrap();
        assert(task == tv[0]);
        let o = task.run();
        let mut v: Vec<(Vec<u64>, bool, bool)> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => { return Err(e); },
        }
    };
    assert(outs@.len() == k && forall|j: int| 0 <= j < k ==> #[trigger] tv[j].post(outs@[j]));
    // concatenate the words in task order
    let mut bits: Vec<u64> = Vec::new();
    let mut asc = true;
    let mut pos = true;
    let mut j: usize = 0;
    while j < k
        invariant
            j <= k, k == workers, 1 <= k, outs@.len() == k, nw == nwords(np as int), np == c.np, cols_ok(*c, sv),
            0 <= pbase,
            forall|q: int| 0 <= q < k ==> #[trigger] tv[q].post(outs@[q]) && tv[q].sv@ == sv && tv[q].ps@ == ps
                && tv[q].w0 == split(nw as int, k as int, q) && tv[q].w1 == split(nw as int, k as int, q + 1)
                && tv[q].np == np && tv[q].pbase == pbase,
            bits@.len() == split(nw as int, k as int, j as int),
            asc ==> words_ok(bits@, 0, sv, ps) && rows_like_ok(sv, ps, 0, (bits@.len() * 64) as int),
            pos ==> forall|r: int| 0 <= r < bits@.len() * 64 && r < np ==> #[trigger] pk(sv)[r] as int == pbase + r,
        decreases k - j,
    {
        proof { lemma_split(nw as int, k as int, j as int, j + 1); }
        let ghost before = bits@;
        let ghost task = tv[j as int];
        assert(task.post(outs@[j as int]));
        if !outs[j].1 { asc = false; }
        if !outs[j].2 { pos = false; }
        let n_out = outs[j].0.len();
        let mut q: usize = 0;
        while q < n_out
            invariant
                q <= n_out, n_out == outs@[j as int].0@.len(), j < k, outs@.len() == k,
                bits@.len() == before.len() + q, before.len() == task.w0,
                forall|x: int| 0 <= x < before.len() ==> bits@[x] == #[trigger] before[x],
                forall|x: int| 0 <= x < q ==> bits@[before.len() + x] == #[trigger] outs@[j as int].0@[x],
            decreases n_out - q,
        {
            bits.push(outs[j].0[q]);
            q = q + 1;
        }
        proof {
            let o = outs@[j as int];
            if asc {
                assert(words_ok(o.0@, task.w0 as int, sv, ps));
                assert forall|i: int, b: int| 0 <= i < bits@.len() && 0 <= b < 64 implies
                    #[trigger] bit(bits@[i], b as u64) == ((0 + i) * 64 + b < n_p(sv) && match_bit(sv, ps, (0 + i) * 64 + b)) by {
                    if i < before.len() {
                        assert(bits@[i] == before[i]);
                    } else {
                        let x = i - before.len();
                        assert(bits@[before.len() + x] == o.0@[x]);
                        assert(bit(o.0@[x], b as u64) == ((task.w0 + x) * 64 + b < n_p(sv) && match_bit(sv, ps, (task.w0 + x) * 64 + b)));
                    }
                }
                assert(rows_like_ok(sv, ps, task.w0 * 64, task.w1 * 64));
            }
        }
        j = j + 1;
    }
    proof {
        lemma_split(nw as int, k as int, k as int, k as int);
        assert(bits@.len() == nw);
        if asc {
            assert forall|u: int| 0 <= u < 64 * bits@.len() implies #[trigger] word_bit(bits@, u) == (u < n_p(sv) && match_bit(sv, ps, u)) by {
                let i = u / 64;
                let b = u % 64;
                assert(bit(bits@[i], b as u64) == ((0 + i) * 64 + b < n_p(sv) && match_bit(sv, ps, (0 + i) * 64 + b)));
                assert((0 + i) * 64 + b == u);
            }
            assert(bits_ok(bits@, sv, ps));
            assert forall|r: int| 0 <= r < n_p(sv) implies #[trigger] like_ok(pname(sv, r), pat_of(ps)) by {
                assert(r < bits@.len() * 64);
            }
        }
        if pos {
            assert forall|r: int| 0 <= r < pk(sv).len() implies #[trigger] pk(sv)[r] as int == pbase + r by {
                assert(r < bits@.len() * 64);
            }
        }
    }
    Ok((bits, asc, pos))
}

// ------------------------------------------------------------------------------------------------ the general path

/// A copy of bytes `lo..hi`.
pub fn copy_range(p: &[u8], lo: usize, hi: usize) -> (v: Vec<u8>)
    requires lo <= hi <= p@.len(),
    ensures v@ == p@.subrange(lo as int, hi as int),
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = lo;
    while i < hi
        invariant lo <= i <= hi, hi <= p@.len(), v@ == p@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        v.push(p[i]);
        i = i + 1;
        proof { assert(v@ =~= p@.subrange(lo as int, i as int)); }
    }
    v
}

/// The verified `LIKE` on every part name (serial). `Ok(bits)`: the bitmap, no name raises; `Err(r)`: part row `r`'s
/// `LIKE` raises.
pub fn part_pass_general(c: &Cols, pat: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<Vec<u64>, usize>)
    requires cols_ok(*c, sv), pat@ == pat_of(ps),
    ensures
        r matches Ok(bits) ==> bits_ok(bits@, sv, ps) && likes_all_ok(sv, ps),
        r matches Err(p) ==> p < n_p(sv) && !like_ok(pname(sv, p as int), pat_of(ps)),
{
    let np = c.np;
    let nw = np / 64 + if np % 64 == 0 { 0 } else { 1 };
    let pv = EVal::Text(copy_range(pat, 0, pat.len()));
    let mut eb: Vec<u8> = Vec::new();
    eb.push(92u8);
    let ev = EVal::Text(eb);
    proof {
        assert(pat@.subrange(0, pat@.len() as int) =~= pat@);
        assert(eb@ =~= esc_bytes());
    }
    let mut bits: Vec<u64> = zeros_u64(nw);
    proof {
        assert forall|u: int| 0 <= u < 64 * nw implies !#[trigger] word_bit(bits@, u) by {
            lemma_bit_zero((u % 64) as u64);
        }
    }
    let mut r: usize = 0;
    while r < np
        invariant
            r <= np, nw == nwords(np as int), np == c.np, cols_ok(*c, sv),
            pv@ == Val::Text(pat_of(ps)), ev@ == Val::Text(esc_bytes()),
            bits@.len() == nw,
            forall|u: int| 0 <= u < 64 * nw ==> #[trigger] word_bit(bits@, u) == (u < r && match_bit(sv, ps, u)),
            forall|p: int| 0 <= p < r ==> #[trigger] like_ok(pname(sv, p), pat_of(ps)),
        decreases np - r,
    {
        let (s0, e0) = name_bounds(c.poffs, c.pbytes, np, r, Ghost(sv));
        let name = EVal::Text(copy_range(c.pbytes, s0, e0));
        let res = like_value_exec(&name, &pv, &ev);
        proof {
            assert(name@ == Val::Text(pname(sv, r as int)));
            lemma_like_res(pname(sv, r as int), pat_of(ps));
        }
        let x: u64 = match res {
            Ok(EVal::Bool(true)) => 1,
            Ok(EVal::Bool(false)) => 0,
            _ => {
                proof {
                    if like_ok(pname(sv, r as int), pat_of(ps)) {
                        let t = like_true(pname(sv, r as int), pat_of(ps));
                        assert(view_result(res) == Ok::<Val, SqlError>(Val::Bool(t)));
                        assert(res is Ok);
                        assert(res->Ok_0@ == Val::Bool(t));
                        assert(res->Ok_0 is Bool);
                        assert(false);
                    }
                }
                return Err(r);
            },
        };
        let w = r / 64;
        let t = (r % 64) as u64;
        let old = bits[w];
        proof {
            assert(word_bit(bits@, r as int) == false);
            assert(!bit(old, t));
        }
        let new = old | (x << t);
        let ghost bits0 = bits@;
        bits.set(w, new);
        proof {
            assert forall|u: int| 0 <= u < 64 * nw implies #[trigger] word_bit(bits@, u) == (u < r + 1 && match_bit(sv, ps, u)) by {
                if u / 64 == w {
                    lemma_bit_set(old, x, t, (u % 64) as u64);
                    assert(word_bit(bits0, u) == bit(old, (u % 64) as u64));
                    if (u % 64) as u64 == t { assert(u == r); }
                } else {
                    assert(bits@[u / 64] == bits0[u / 64]);
                    assert(word_bit(bits@, u) == word_bit(bits0, u));
                }
            }
        }
        r = r + 1;
    }
    proof {
        assert(bits_ok(bits@, sv, ps)) by {
            assert forall|u: int| 0 <= u < 64 * bits@.len() implies #[trigger] word_bit(bits@, u) == (u < n_p(sv) && match_bit(sv, ps, u)) by {}
        }
    }
    Ok(bits)
}

/// Whether the key column `keys` (`n` rows) is positional from `base` (serial).
pub fn positional_check(keys: &[i64], n: usize, base: i64) -> (r: bool)
    requires keys@.len() == n, 0 <= base, base + n < i64::MAX,
    ensures r ==> positional(keys@, base as int),
{
    let mut i: usize = 0;
    while i < n
        invariant i <= n, keys@.len() == n, 0 <= base, base + n < i64::MAX,
            forall|r: int| 0 <= r < i ==> #[trigger] keys@[r] as int == base + r,
        decreases n - i,
    {
        if keys[i] != base + i as i64 {
            return false;
        }
        i = i + 1;
    }
    true
}

/// Whether `pat` is a contains pattern, and its literal.
pub fn contains_pattern_exec(pat: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r is Some == contains_pattern(pat@),
        r matches Some(lit) ==> lit@ == contains_lit(pat@),
{
    let n = pat.len();
    if n < 3 || pat[0] != 0x25u8 || pat[n - 1] != 0x25u8 {
        return None;
    }
    let mut i: usize = 1;
    while i < n - 1
        invariant
            1 <= i <= n - 1, n == pat@.len(), n >= 3,
            forall|j: int| 1 <= j < i ==> #[trigger] pat@[j] < 0x80u8 && pat@[j] != 0x25u8 && pat@[j] != 0x5Fu8 && pat@[j] != 0x5Cu8,
        decreases n - 1 - i,
    {
        let x = pat[i];
        if x >= 0x80u8 || x == 0x25u8 || x == 0x5Fu8 || x == 0x5Cu8 {
            return None;
        }
        i = i + 1;
    }
    Some(copy_range(pat, 1, n - 1))
}

} // verus!
