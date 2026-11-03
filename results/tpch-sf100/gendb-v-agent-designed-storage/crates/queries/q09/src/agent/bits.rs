//! The part filter bits (`scan::bits_ok`: bit `c` set exactly when part row `c` matches `p_name LIKE $1`). For a
//! pattern `%w%` with a plain word `w` the part tasks of `pfilter` test byte substrings in parallel; when every name is
//! ASCII that is the LIKE value (`common::like_word`) and LIKE never raises. Otherwise (`like_bits`) every name is
//! matched serially with the framework's LIKE, recording a name on which LIKE raises.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::fns::like::like_value;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::filled;
use crate::exec::value::{EVal, view_result};
use crate::exec::fns::like::like_value_exec;
use super::model::*;
use super::cols::*;
use super::lookups::*;
use super::qspec::*;
use super::scan::{bit_of, bits_ok};
use super::pfilter::*;
use super::common::like_word::*;
use super::common::horspool::{shift_ok, shift_table};
use super::sigmask::{word_mask, word_mask_exec};
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

/// The word of a pattern `%w%`.
pub open spec fn word_of(pat: Seq<u8>) -> Seq<u8> {
    pat.subrange(1, pat.len() - 1)
}

/// The pattern is `%w%` with a plain word `w`.
pub open spec fn word_shape(pat: Seq<u8>) -> bool {
    pat.len() >= 3 && pat == word_pattern(word_of(pat)) && plain_word(word_of(pat))
}

/// Is the pattern `%w%` with a plain word `w`?
pub fn is_word_shape(pat: &[u8]) -> (r: bool)
    ensures r == word_shape(pat@),
{
    let n = pat.len();
    if n < 3 || pat[0] != 0x25u8 || pat[n - 1] != 0x25u8 {
        proof {
            if n >= 3 && word_shape(pat@) {
                assert(pat@[0] == word_pattern(word_of(pat@))[0]);
                assert(pat@[n - 1] == word_pattern(word_of(pat@))[n - 1]);
            }
        }
        return false;
    }
    let ghost w = word_of(pat@);
    let mut i: usize = 1;
    while i < n - 1
        invariant
            n == pat@.len(), n >= 3, 1 <= i <= n - 1, w == word_of(pat@),
            forall|x: int| 0 <= x < i - 1 ==> #[trigger] w[x] < 0x80 && w[x] != 0x25 && w[x] != 0x5F && w[x] != 0x5C,
        decreases n - 1 - i,
    {
        let b = pat[i];
        if b >= 0x80u8 || b == 0x25u8 || b == 0x5Fu8 || b == 0x5Cu8 {
            proof { assert(w[i - 1] == b); }
            return false;
        }
        i = i + 1;
    }
    proof { assert(pat@ =~= word_pattern(w)); }
    true
}

/// Consecutive part tasks over `[0, n)` for the word of `pat`.
pub open spec fn ptasks_ok(ts: Seq<PartTask>, c: Cols, d: Divs, pat: &'static [u8], m: M, n: int) -> bool {
    &&& forall|t: int| 0 <= t < ts.len() ==> task_fields(#[trigger] ts[t], c, d, pat, m, n)
    &&& forall|t: int| 0 <= t < ts.len() - 1 ==> #[trigger] hi_of(ts, t) == ts[t + 1].c_lo
    &&& ts.len() > 0 ==> ts[0].c_lo == 0 && ts[ts.len() - 1].c_hi == n
    &&& ts.len() == 0 ==> n == 0
}

/// The end of task `t`.
pub open spec fn hi_of(ts: Seq<PartTask>, t: int) -> int {
    ts[t].c_hi as int
}

/// A part task over the part rows of `[0, n)` (`part_pre` with `look_ok(c, d, m)`).
pub open spec fn task_fields(t: PartTask, c: Cols, d: Divs, pat: &'static [u8], m: M, n: int) -> bool {
    &&& t.cols == c && t.divs == d && t.m@ == m && t.pat == pat && t.wl == 1 && t.wn == pat@.len() - 2
    &&& t.use_sh ==> shift_ok((*t.sh)@, pat@.subrange(1, pat@.len() - 1))
    &&& t.pm == word_mask(pat@.subrange(1, pat@.len() - 1))
    &&& psig_ok(c.p_sig@, m)
    &&& t.c_lo <= t.c_hi <= n && t.c_lo % 64 == 0
    &&& t.words@.len() == (t.c_hi - t.c_lo + 63) / 64
}

/// The part rows covered by the first `k` tasks.
pub open spec fn cov(ts: Seq<PartTask>, k: int) -> int {
    if k == 0 { 0 } else { ts[k - 1].c_hi as int }
}

/// `ceil(k / 64)` without overflow.
fn words_for(k: usize) -> (r: usize)
    ensures r == (k + 63) / 64,
{
    let q = k / 64;
    if k % 64 == 0 { q } else { q + 1 }
}

/// At most `workers` part tasks covering the part rows, starting at multiples of 64.
fn part_tasks(c: Cols, d: Divs, pat: &'static [u8], workers: usize, Ghost(m): Ghost<M>) -> (ts: Vec<PartTask>)
    requires look_ok(c, d, m), psig_ok(c.p_sig@, m), word_shape(pat@), 1 <= workers <= MAX_WORKERS,
    ensures ts.len() <= workers, ptasks_ok(ts@, c, d, pat, m, m.p_n as int),
{
    let n = c.p_n;
    let wn = pat.len() - 2;
    let q = n / workers / 64;
    let per = if q < 0x100_0000 { (q + 1) * 64 } else { 0x4000_0000 };
    let use_sh = wn <= 255;
    let sh: Arc<Vec<u8>> = Arc::new(if use_sh { shift_table(pat, 1, wn) } else { Vec::new() });
    let pm = word_mask_exec(pat, 1, wn);
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut lo: usize = 0;
    while lo < n
        invariant
            use_sh ==> shift_ok((*sh)@, pat@.subrange(1, pat@.len() - 1)),
            pm == word_mask(pat@.subrange(1, pat@.len() - 1)), psig_ok(c.p_sig@, m),
            wn == pat@.len() - 2,
            1 <= workers <= MAX_WORKERS, per % 64 == 0, per >= 64, n == m.p_n,
            lo <= n, lo % 64 == 0 || lo == n,
            tasks.len() <= workers,
            tasks.len() == workers ==> lo == n,
            pat@.len() <= usize::MAX,
            forall|t: int| 0 <= t < tasks.len() ==> task_fields(#[trigger] tasks@[t], c, d, pat, m, n as int),
            forall|t: int| 0 <= t < tasks.len() - 1 ==> #[trigger] hi_of(tasks@, t) == tasks@[t + 1].c_lo,
            tasks.len() > 0 ==> tasks@[0].c_lo == 0 && tasks@[tasks.len() - 1].c_hi == lo,
            tasks.len() == 0 ==> lo == 0,
        decreases n - lo,
    {
        let last = tasks.len() + 1 == workers || n - lo <= per;
        let hi = if last { n } else { lo + per };
        let t = PartTask { cols: c, divs: d, c_lo: lo, c_hi: hi, pat, wl: 1, wn, sh: sh.clone(), use_sh, pm,
            words: vec![0u64; words_for(hi - lo)], m: Ghost(m) };
        proof {
            assert forall|i: int| 0 <= i < t.words@.len() implies #[trigger] t.words@[i] == 0u64 by {
                assert(vstd::pervasive::cloned(0u64, t.words@[i]));
            }
        }
        proof { assert(task_fields(t, c, d, pat, m, n as int)); }
        let ghost t0 = tasks@;
        tasks.push(t);
        proof {
            assert(tasks@[tasks.len() - 1] == t);
            assert forall|x: int| 0 <= x < tasks.len() - 1 implies #[trigger] hi_of(tasks@, x) == tasks@[x + 1].c_lo by {
                assert(tasks@[x] == t0[x]);
                if x + 1 < t0.len() { assert(tasks@[x + 1] == t0[x + 1]); assert(hi_of(t0, x) == t0[x + 1].c_lo); }
            }
            assert forall|x: int| 0 <= x < tasks.len() implies task_fields(#[trigger] tasks@[x], c, d, pat, m, n as int) by {
                if x < t0.len() { assert(tasks@[x] == t0[x]); }
            }
        }
        if last {
            lo = n;
        } else {
            lo = hi;
        }
    }
    tasks
}

/// Append `w` to `v`.
fn append(v: &mut Vec<u64>, w: &Vec<u64>)
    ensures final(v)@ == old(v)@ + w@,
{
    let mut i: usize = 0;
    while i < w.len()
        invariant i <= w@.len(), v@ == old(v)@ + w@.subrange(0, i as int),
        decreases w@.len() - i,
    {
        v.push(w[i]);
        proof { assert(v@ =~= old(v)@ + w@.subrange(0, i + 1)); }
        i = i + 1;
    }
    proof { assert(w@.subrange(0, w@.len() as int) =~= w@); }
}

/// `a * 64` (hidden from loop contexts).
#[verifier::opaque]
pub open spec fn x64(a: int) -> int {
    a * 64
}

/// A task's output (`part_post`, hidden from loop contexts).
#[verifier::opaque]
pub open spec fn post_of(t: PartTask, o: PartOut) -> bool {
    part_post(t, o)
}

/// The bits of the part rows below `hi` are the substring tests of `w` (hidden from loop contexts).
#[verifier::opaque]
pub open spec fn bits_upto(bits: Seq<u64>, m: M, w: Seq<u8>, hi: int) -> bool {
    forall|x: int| 0 <= x < hi ==> #[trigger] bit_of(bits, x) == contains(pname(m, x), w)
}

/// Bits of appended words.
proof fn lemma_append_bits(b0: Seq<u64>, w: Seq<u64>, x: int)
    requires 0 <= x < (b0.len() + w.len()) * 64,
    ensures
        x < b0.len() * 64 ==> bit_of(b0 + w, x) == bit_of(b0, x),
        x >= b0.len() * 64 ==> bit_of(b0 + w, x) == bit_of(w, x - b0.len() * 64),
{
    let lo = b0.len() * 64;
    if x < lo {
        assert(x / 64 < b0.len());
    } else {
        assert((x - lo) / 64 == x / 64 - b0.len()) by {
            vstd::arithmetic::div_mod::lemma_div_plus_one(x - lo, 64);
            assert((x - lo) / 64 == x / 64 - b0.len()) by (nonlinear_arith) requires lo == b0.len() * 64, x >= lo;
        }
        assert((x - lo) % 64 == x % 64) by (nonlinear_arith) requires lo == b0.len() * 64, x >= lo;
        assert(x / 64 < b0.len() + w.len()) by (nonlinear_arith) requires x < (b0.len() + w.len()) * 64, x >= 0;
    }
}

/// One task's words appended: the bits through the task's end are the substring tests.
proof fn lemma_task_bits(m: M, w: Seq<u8>, b0: Seq<u64>, t: PartTask, o: PartOut)
    requires
        t.c_lo <= t.c_hi, t.c_lo % 64 == 0, t.words@.len() == (t.c_hi - t.c_lo + 63) / 64, post_of(t, o), task_word(t) == w,
        b0.len() * 64 == t.c_lo,
        bits_upto(b0, m, w, t.c_lo as int),
        t.m@ == m,
    ensures
        bits_upto(b0 + o.words@, m, w, t.c_hi as int),
        (b0 + o.words@).len() * 64 >= t.c_hi,
        (t.c_hi - t.c_lo) % 64 == 0 ==> (b0 + o.words@).len() * 64 == t.c_hi,
{
    reveal(post_of);
    reveal(bits_upto);
    let ws = o.words@;
    assert(ws.len() == (t.c_hi - t.c_lo + 63) / 64);
    assert((b0.len() + ws.len()) * 64 >= t.c_hi) by (nonlinear_arith)
        requires ws.len() == (t.c_hi - t.c_lo + 63) / 64, b0.len() * 64 == t.c_lo, t.c_lo <= t.c_hi;
    if (t.c_hi - t.c_lo) % 64 == 0 {
        assert((b0.len() + ws.len()) * 64 == t.c_hi) by (nonlinear_arith)
            requires ws.len() == (t.c_hi - t.c_lo + 63) / 64, b0.len() * 64 == t.c_lo, t.c_lo <= t.c_hi, (t.c_hi - t.c_lo) % 64 == 0;
    }
    assert forall|x: int| 0 <= x < t.c_hi implies #[trigger] bit_of(b0 + ws, x) == contains(pname(m, x), w) by {
        lemma_append_bits(b0, ws, x);
        if x >= t.c_lo {
            assert(bit_of(ws, x - t.c_lo) == contains(pname(m, x), w));
        }
    }
}

/// The words of a task appended: the bits through its end are the substring tests (bits through its start were).
proof fn lemma_concat_step(t: PartTask, o: PartOut, b0: Seq<u64>, m: M, w: Seq<u8>)
    requires
        t.c_lo <= t.c_hi, t.c_lo % 64 == 0, t.words@.len() == (t.c_hi - t.c_lo + 63) / 64, t.m@ == m,
        task_word(t) == w, post_of(t, o),
        x64(b0.len() as int) == t.c_lo,
        bits_upto(b0, m, w, t.c_lo as int),
    ensures
        bits_upto(b0 + o.words@, m, w, t.c_hi as int),
        (t.c_hi - t.c_lo) % 64 == 0 ==> x64((b0 + o.words@).len() as int) == t.c_hi,
        x64((b0 + o.words@).len() as int) >= t.c_hi,
{
    reveal(x64);
    lemma_task_bits(m, w, b0, t, o);
}

/// The part filter bits of a `%w%` pattern (`None` when some name is not ASCII), with whether part keys are dense.
pub fn word_bits(c: Cols, d: Divs, pat: &'static [u8], workers: usize, dispatch: &mut Dispatch, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: Result<Option<(Vec<u64>, bool)>, QueryError>)
    requires
        look_ok(c, d, m), psig_ok(c.p_sig@, m),
        word_shape(pat@), p.pat == pat@,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some((bits, dense))) ==> bits_ok(bits@, m, p) && like_total(m, p) && (dense ==> p_dense_ok(m)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let n = c.p_n;
    let _plen = pat.len();
    let tasks = part_tasks(c, d, pat, workers, Ghost(m));
    let ghost ts = tasks@;
    proof {
        assert forall|t: int| 0 <= t < tasks.len() implies #[trigger] tasks@[t].pre() by {
            assert(task_fields(tasks@[t], c, d, pat, m, n as int));
        }
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost w = word_of(pat@);
    proof {
        assert forall|t: int| 0 <= t < ts.len() implies post_of(#[trigger] ts[t], outs@[t]) by {
            assert(ts[t].post(outs@[t]));
            reveal(post_of);
        }
        reveal(bits_upto);
        reveal(x64);
    }
    let mut bits: Vec<u64> = Vec::with_capacity(n / 64 + 1);
    let mut k: usize = 0;
    while k < outs.len()
        invariant
            w == word_of(pat@), n == m.p_n,
            outs.len() == ts.len(),
            forall|t: int| 0 <= t < ts.len() ==> post_of(#[trigger] ts[t], outs@[t]),
            ptasks_ok(ts, c, d, pat, m, n as int),
            k <= ts.len(),
            word_shape(pat@),
            k < ts.len() ==> x64(bits@.len() as int) == ts[k as int].c_lo,
            k == ts.len() && k > 0 ==> x64(bits@.len() as int) >= ts[k - 1].c_hi,
            bits_upto(bits@, m, w, cov(ts, k as int)),
        decreases ts.len() - k,
    {
        let o = &outs[k];
        let ghost b0 = bits@;
        let ghost t = ts[k as int];
        append(&mut bits, &o.words);
        proof {
            assert(post_of(t, outs@[k as int]));
            assert(task_fields(t, c, d, pat, m, n as int));
            if k > 0 { assert(hi_of(ts, k - 1) == t.c_lo); }
            assert(task_word(t) =~= w);
            lemma_concat_step(t, *o, b0, m, w);
            if k + 1 < ts.len() {
                assert(hi_of(ts, k as int) == ts[k + 1].c_lo);
                assert(task_fields(ts[k + 1], c, d, pat, m, n as int));
            }
        }
        k = k + 1;
    }
    let mut ascii = true;
    let mut dense = true;
    let mut k: usize = 0;
    while k < outs.len()
        invariant
            n == m.p_n,
            outs.len() == ts.len(),
            forall|t: int| 0 <= t < ts.len() ==> post_of(#[trigger] ts[t], outs@[t]),
            ptasks_ok(ts, c, d, pat, m, n as int),
            k <= ts.len(),
            ascii ==> forall|x: int| 0 <= x < cov(ts, k as int) ==> all_ascii(#[trigger] pname(m, x)),
            dense ==> forall|x: int| 0 <= x < cov(ts, k as int) ==> #[trigger] pkey(m, x) == x + 1,
        decreases ts.len() - k,
    {
        proof {
            assert(post_of(ts[k as int], outs@[k as int]));
            reveal(post_of);
            if k > 0 { assert(hi_of(ts, k - 1) == ts[k as int].c_lo); }
        }
        ascii = ascii && outs[k].ascii;
        dense = dense && outs[k].dense;
        k = k + 1;
    }
    if !ascii {
        return Ok(None);
    }
    proof {
        reveal(bits_upto);
        reveal(x64);
        assert(esc() =~= seq![0x5Cu8]);
        if ts.len() > 0 { assert(ts[ts.len() - 1].c_hi == n); }
        assert forall|x: int| 0 <= x < m.p_n implies #[trigger] bit_of(bits@, x) == pmatch(m, p, x) by {
            lemma_like_word(pname(m, x), w);
        }
        assert forall|x: int| 0 <= x < m.p_n implies #[trigger] plike(m, p, x) is Ok by {
            lemma_like_word(pname(m, x), w);
        }
    }
    Ok(Some((bits, dense)))
}

/// The part filter bits by the framework's LIKE on every name (serial), with a part row whose LIKE raises if any.
pub fn like_bits(c: &Cols, pat: &'static [u8], Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (Vec<u64>, Option<usize>))
    requires cols_ok(*c, m), shapes_ok(m), p.pat == pat@,
    ensures
        bits_ok(r.0@, m, p),
        r.1 matches Some(x) ==> x < m.p_n && plike(m, p, x as int) is Err,
        r.1 is None ==> like_total(m, p),
{
    let n = c.p_n;
    let mut pv: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < pat.len()
        invariant i <= pat@.len(), pv@ == pat@.subrange(0, i as int),
        decreases pat@.len() - i,
    {
        pv.push(pat[i]);
        proof { assert(pv@ =~= pat@.subrange(0, i + 1)); }
        i = i + 1;
    }
    proof { assert(pv@ =~= pat@); }
    let pval = EVal::Text(pv);
    let mut ev: Vec<u8> = Vec::new();
    ev.push(0x5Cu8);
    let eval = EVal::Text(ev);
    proof { assert(eval@ == Val::Text(esc())) by { assert(ev@ =~= esc()); } }
    let nw = n / 64 + 1;
    let mut bits: Vec<u64> = filled(nw, 0u64);
    let mut err: Option<usize> = None;
    let mut x: usize = 0;
    proof {
        assert forall|y: int| x <= y < nw * 64 implies !#[trigger] bit_of(bits@, y) by {
            lemma_zero_bits((y % 64) as u64);
        }
    }
    while x < n
        invariant
            cols_ok(*c, m), shapes_ok(m), n == m.p_n, p.pat == pat@,
            pval@ == Val::Text(pat@), eval@ == Val::Text(esc()),
            x <= n, nw == n / 64 + 1,
            bits@.len() == nw,
            forall|y: int| 0 <= y < x ==> #[trigger] bit_of(bits@, y) == pmatch(m, p, y),
            forall|y: int| x <= y < nw * 64 ==> !#[trigger] bit_of(bits@, y),
            err matches Some(e) ==> e < m.p_n && plike(m, p, e as int) is Err,
            err is None ==> forall|y: int| 0 <= y < x ==> #[trigger] plike(m, p, y) is Ok,
        decreases n - x,
    {
        proof {
            assert(crate::stores::custpart::interface::common::colfmt::text_range_ok(m.p_name_o, m.p_name_y, x as int));
        }
        let a = c.p_name_o[x] as usize;
        let e = c.p_name_o[x + 1] as usize;
        let mut sv: Vec<u8> = Vec::new();
        let mut q = a;
        while q < e
            invariant a <= q <= e <= c.p_name_y@.len(), sv@ == c.p_name_y@.subrange(a as int, q as int),
            decreases e - q,
        {
            sv.push(c.p_name_y[q]);
            proof { assert(sv@ =~= c.p_name_y@.subrange(a as int, q + 1)); }
            q = q + 1;
        }
        let sval = EVal::Text(sv);
        proof { assert(sval@ == Val::Text(pname(m, x as int))); }
        let res = like_value_exec(&sval, &pval, &eval);
        proof { assert(view_result(res) == plike(m, p, x as int)); }
        let hit = match res {
            Ok(EVal::Bool(true)) => true,
            Ok(_) => false,
            Err(_) => {
                if err.is_none() {
                    err = Some(x);
                }
                false
            },
        };
        proof { assert(hit == pmatch(m, p, x as int)); }
        if hit {
            let wi = x / 64;
            let bit = (x % 64) as u64;
            let ghost b0 = bits@;
            let wv = bits[wi] | (1u64 << bit);
            bits.set(wi, wv);
            proof {
                assert forall|y: int| 0 <= y < nw * 64 && y != x implies #[trigger] bit_of(bits@, y) == bit_of(b0, y) by {
                    if y / 64 == wi as int {
                        lemma_set_bit(b0[wi as int], bit, (y % 64) as u64);
                    }
                }
                lemma_set_bit(b0[wi as int], bit, bit);
                assert(bit_of(bits@, x as int));
            }
        }
        x = x + 1;
    }
    proof {
        if err is None {
            assert forall|y: int| 0 <= y < m.p_n implies #[trigger] plike(m, p, y) is Ok by {}
        }
    }
    (bits, err)
}

} // verus!
