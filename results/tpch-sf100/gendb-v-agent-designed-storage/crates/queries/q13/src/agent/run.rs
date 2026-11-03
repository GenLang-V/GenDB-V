//! Phase 1 on the calling thread: chunk bounds, the pattern's tokens and codes, the scan tasks (`run_scan`), and
//! the match lists (`collect_lists`): per chunk the keys of its matching rows, plus one list for the deferred
//! (non-ASCII candidate) rows decided here with the general LIKE evaluator. The occurrences of a key `v` in all lists
//! are the matching orders rows with key `v` (`likes == cnt(like_r && kf == v)`), and `any_err` tells whether the
//! matcher raises on some row.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::exec::value::*;
use crate::exec::chars::*;
use crate::exec::fns::like::*;
use super::like::*;
use super::scan::*;
use super::count::*;
use super::glue::*;
use super::common::partition::*;

verus! {

/// Bounds `0 = b[0] <= b[1] <= .. <= b[k] = n` of `k` contiguous chunks.
pub open spec fn bounds_ok(b: Seq<usize>, k: int, n: int) -> bool {
    &&& b.len() == k + 1
    &&& b[0] == 0
    &&& b[k] == n
    &&& forall|t: int| 0 <= t < k ==> #[trigger] b[t] <= b[t + 1]
}

/// `k` chunk bounds over `n` rows (about equal sizes).
pub fn make_bounds(n: usize, k: usize) -> (b: Vec<usize>)
    requires k >= 1,
    ensures bounds_ok(b@, k as int, n as int),
{
    let chunk = if n / k < usize::MAX { n / k + 1 } else { n / k };
    let mut b: Vec<usize> = Vec::new();
    b.push(0);
    let mut cur: usize = 0;
    let mut t: usize = 1;
    while t < k
        invariant
            1 <= t <= k,
            b@.len() == t,
            b@[0] == 0,
            cur == b@[t - 1],
            cur <= n,
            forall|s: int| 0 <= s < t - 1 ==> #[trigger] b@[s] <= b@[s + 1],
        decreases k - t,
    {
        cur = if n - cur > chunk { cur + chunk } else { n };
        b.push(cur);
        t = t + 1;
    }
    b.push(n);
    b
}

/// Chunk bounds lie inside `[0, n]`.
pub proof fn lemma_bounds_le(b: Seq<usize>, k: int, n: int, t: int)
    requires bounds_ok(b, k, n), 0 <= t < k,
    ensures 0 <= b[t] <= b[t + 1] <= n,
    decreases k - t,
{
    if t + 1 < k {
        lemma_bounds_le(b, k, n, t + 1);
    }
}

/// A copy of the codes (one per task).
pub fn copy_codes(codes: &Vec<u16>) -> (r: Vec<u16>)
    ensures r@ == codes@,
{
    let mut r: Vec<u16> = Vec::new();
    let mut j: usize = 0;
    while j < codes.len()
        invariant
            j <= codes.len(),
            r@ == codes@.subrange(0, j as int),
        decreases codes.len() - j,
    {
        r.push(codes[j]);
        proof { assert(r@ =~= codes@.subrange(0, j + 1)); }
        j = j + 1;
    }
    proof { assert(r@ =~= codes@); }
    r
}

/// A copy of a key vector.
pub fn copy_i64s(v: &Vec<i64>) -> (r: Vec<i64>)
    ensures r@ == v@,
{
    let mut r: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < v.len()
        invariant
            j <= v.len(),
            r@ == v@.subrange(0, j as int),
        decreases v.len() - j,
    {
        r.push(v[j]);
        proof { assert(r@ =~= v@.subrange(0, j + 1)); }
        j = j + 1;
    }
    proof { assert(r@ =~= v@); }
    r
}

/// A copy of a position vector.
pub fn copy_usizes(v: &Vec<usize>) -> (r: Vec<usize>)
    ensures r@ == v@,
{
    let mut r: Vec<usize> = Vec::new();
    let mut j: usize = 0;
    while j < v.len()
        invariant
            j <= v.len(),
            r@ == v@.subrange(0, j as int),
        decreases v.len() - j,
    {
        r.push(v[j]);
        proof { assert(r@ =~= v@.subrange(0, j + 1)); }
        j = j + 1;
    }
    proof { assert(r@ =~= v@); }
    r
}

/// A copy of a byte slice range.
pub fn copy_bytes(bytes: &[u8], lo: usize, hi: usize) -> (r: Vec<u8>)
    requires lo <= hi <= bytes@.len(),
    ensures r@ == bytes@.subrange(lo as int, hi as int),
{
    let mut r: Vec<u8> = Vec::with_capacity(hi - lo);
    let mut k = lo;
    while k < hi
        invariant
            lo <= k <= hi <= bytes@.len(),
            r@ == bytes@.subrange(lo as int, k as int),
        decreases hi - k,
    {
        r.push(bytes[k]);
        proof { assert(r@ =~= bytes@.subrange(lo as int, k + 1)); }
        k = k + 1;
    }
    r
}

/// The escape string `\` as bytes.
pub fn esc_vec() -> (v: Vec<u8>)
    ensures v@ == seq![92u8],
{
    let mut v: Vec<u8> = Vec::new();
    v.push(92u8);
    proof { assert(v@ =~= seq![92u8]); }
    v
}

/// The tokens of `pat` with escape `\`.
pub open spec fn pat_toks(pat: Seq<u8>) -> Seq<LikeTok> {
    like_tokens(chars(pat), Some(seq![92u8]), 0)
}

/// The pattern tokens of `$1 LIKE .. ESCAPE '\'` and their codes.
pub fn pattern_codes(pat: &Vec<u8>) -> (r: (Vec<u16>, Ghost<Seq<LikeTok>>))
    ensures
        r.1@ == pat_toks(pat@),
        codes_ok(r.0@, r.1@),
{
    let pc = chars_exec(pat);
    let esc_bytes = esc_vec();
    let ec = chars_exec(&esc_bytes);
    proof {
        super::sql::lemma_chars_esc();
        assert(view_chars(ec@) == seq![seq![92u8]]);
    }
    assert(ec@.len() == 1);
    let esc: Option<Vec<u8>> = Some(ec[0].clone());
    proof {
        assert(view_chars(ec@)[0] == ec@[0]@);
    }
    let toks = like_tokens_exec(&pc, &esc);
    let codes = token_codes(&toks);
    (codes, Ghost(view_toks(toks@)))
}

/// The scan context of the slices.
pub open spec fn mk_ctx(sig: Seq<u64>, offs: Seq<u64>, bytes: Seq<u8>, codes: Seq<u16>, p: Seq<LikeTok>, need0: u64,
    need1: u64, ic: Seq<u32>, ib: Seq<u64>, kc: Seq<u32>, kb: Seq<i64>, bs: int) -> ScanCtx {
    ScanCtx { sig, offs, bytes, codes, p, need0, need1, ic, ib, kc, kb, bs }
}

/// The scan task of rows `a .. b` with buffers of `kcap` keys (or rows) and `dcap` deferred rows.
fn make_task(sig: &'static [u64], nsig: usize, offs: &'static [u64], bytes: &'static [u8], nbytes: usize, codes: &Vec<u16>,
    need0: u64, need1: u64, ic: &'static [u32], ib: &'static [u64], kc: &'static [u32], kb: &'static [i64], bs: usize,
    n: usize, a: usize, b: usize, gather: bool, kcap: usize, dcap: usize, Ghost(p): Ghost<Seq<LikeTok>>, blo: &Vec<i64>,
    bhi: &Vec<i64>, sl: &SliceArgs) -> (task: ScanTask)
    requires
        a <= b <= n,
        ranges_ok(blo@, bhi@),
        blo@.len() + 2 <= usize::MAX,
        nbytes == bytes@.len(),
        nsig == sig@.len(),
        ctx_ok(mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int), n as int, gather),
        slice_args_ok(sl, mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int), n as int),
    ensures
        task.pre(),
        task_ctx(task) == mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int),
        task.gather == gather, task.a == a, task.b == b, task.kcap == kcap, task.dcap == dcap,
        task.blo@ == blo@, task.bhi@ == bhi@,
{
    proof {
        reveal(slice_args_ok);
    }
    let keys: Vec<i64> = if gather { vec![0i64; kcap] } else { Vec::new() };
    let rows: Vec<usize> = vec![0usize; kcap];
    let task = ScanTask {
        sig, nsig, offs, bytes, nbytes, codes: copy_codes(codes), need0, need1, ic, ib, kc, kb, bs, n, a, b, gather,
        keys, rows, defer: vec![0usize; dcap], kcap, dcap, toks: Ghost(p),
        blo: copy_i64s(blo), bhi: copy_i64s(bhi), nb: blo.len(), boff: vec![0usize; blo.len() + 2],
        cur: vec![0usize; blo.len() + 1],
        sl0: sl.sl0, sl1: sl.sl1, nsl: sl.nsl, nw: sl.nw, pq: copy_usizes(&sl.pq), np: sl.pq.len(),
    };
    proof {
        assert forall|i: int| 0 <= i < task.nb + 2 implies #[trigger] task.boff@[i] == 0 by {}
    }
    task
}

/// One chunk scanned on the calling thread with buffers of the chunk's size (no overflow).
fn rerun_chunk(sig: &'static [u64], nsig: usize, offs: &'static [u64], bytes: &'static [u8], nbytes: usize, codes: &Vec<u16>,
    need0: u64, need1: u64, ic: &'static [u32], ib: &'static [u64], kc: &'static [u32], kb: &'static [i64], bs: usize,
    n: usize, a: usize, b: usize, gather: bool, Ghost(p): Ghost<Seq<LikeTok>>, blo: &Vec<i64>, bhi: &Vec<i64>,
    sl: &SliceArgs) -> (o: ScanOut)
    requires
        a <= b <= n,
        nbytes == bytes@.len(),
        nsig == sig@.len(),
        ctx_ok(mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int), n as int, gather),
        slice_args_ok(sl, mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int), n as int),
        ranges_ok(blo@, bhi@),
        blo@.len() + 2 <= usize::MAX,
    ensures
        chunk_post(mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int), gather,
            a as int, b as int, o),
        seg_post(o, blo@, bhi@),
{
    let task = make_task(sig, nsig, offs, bytes, nbytes, codes, need0, need1, ic, ib, kc, kb, bs, n, a, b, gather,
        b - a, b - a, Ghost(p), blo, bhi, sl);
    let ghost tk = task;
    let o = task.run();
    proof {
        assert(tk.post(o));
    }
    o
}

/// Phase 1: `k` scan tasks over the chunks `bounds` of the orders rows.
pub fn run_scan(sig: &'static [u64], offs: &'static [u64], bytes: &'static [u8], nbytes: usize, codes: &Vec<u16>,
    need0: u64, need1: u64, ic: &'static [u32], ib: &'static [u64], kc: &'static [u32], kb: &'static [i64], bs: usize,
    n: usize, gather: bool, bounds: &Vec<usize>, k: usize, Ghost(p): Ghost<Seq<LikeTok>>, dispatch: &mut Dispatch,
    blo: &Vec<i64>, bhi: &Vec<i64>, sl: &SliceArgs)
    -> (r: Result<Vec<ScanOut>, WorkerFailure>)
    requires
        slice_args_ok(sl, mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int), n as int),
        1 <= k <= MAX_WORKERS,
        ranges_ok(blo@, bhi@),
        blo@.len() + 2 <= usize::MAX,
        bounds_ok(bounds@, k as int, n as int),
        nbytes == bytes@.len(),
        ctx_ok(mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int), n as int, gather),
    ensures
        r matches Ok(outs) ==> outs@.len() == k && forall|t: int| 0 <= t < k ==> #[trigger] chunk_post(
            mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int), gather,
            bounds@[t] as int, bounds@[t + 1] as int, outs@[t]),
        r matches Ok(outs) ==> forall|t: int| 0 <= t < k ==> #[trigger] seg_post(outs@[t], blo@, bhi@),
{
    let ghost x = mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int);
    let nsig = sig.len();
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            1 <= k <= MAX_WORKERS,
            bounds_ok(bounds@, k as int, n as int),
            nbytes == bytes@.len(),
            nsig == sig@.len(),
            x == mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int),
            ctx_ok(x, n as int, gather),
            slice_args_ok(sl, x, n as int),
            ranges_ok(blo@, bhi@), blo@.len() + 2 <= usize::MAX,
            t <= k,
            tasks@.len() == t,
            forall|s: int| 0 <= s < t ==> (#[trigger] tasks@[s]).blo@ == blo@ && tasks@[s].bhi@ == bhi@,
            forall|s: int| 0 <= s < t ==> #[trigger] tasks@[s].pre(),
            forall|s: int| 0 <= s < t ==> task_ctx(#[trigger] tasks@[s]) == x && tasks@[s].gather == gather
                && tasks@[s].a == bounds@[s] && tasks@[s].b == bounds@[s + 1],
        decreases k - t,
    {
        let a = bounds[t];
        let b = bounds[t + 1];
        proof {
            lemma_bounds_le(bounds@, k as int, n as int, t as int);
        }
        // Matches are a few percent of the rows; a chunk that overflows is rerun below with full buffers.
        let len = b - a;
        let kcap = if len > 8192 { len / 32 + 4096 } else { len };
        let dcap = if 4096 < len { 4096 } else { len };
        let task = make_task(sig, nsig, offs, bytes, nbytes, codes, need0, need1, ic, ib, kc, kb, bs, n, a, b, gather,
            kcap, dcap, Ghost(p), blo, bhi, sl);
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let mut outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    proof {
        assert forall|s: int| 0 <= s < k && !(#[trigger] outs@[s]).overflow implies
            chunk_post(x, gather, bounds@[s] as int, bounds@[s + 1] as int, outs@[s]) && seg_post(outs@[s], blo@, bhi@) by {
            assert(tv[s].post(outs@[s]));
        }
    }
    let mut t: usize = 0;
    while t < k
        invariant
            bounds_ok(bounds@, k as int, n as int),
            nbytes == bytes@.len(),
            nsig == sig@.len(),
            x == mk_ctx(sig@, offs@, bytes@, codes@, p, need0, need1, ic@, ib@, kc@, kb@, bs as int),
            ctx_ok(x, n as int, gather),
            slice_args_ok(sl, x, n as int),
            ranges_ok(blo@, bhi@), blo@.len() + 2 <= usize::MAX,
            t <= k,
            outs@.len() == k,
            forall|s: int| 0 <= s < t ==> #[trigger] chunk_post(x, gather, bounds@[s] as int, bounds@[s + 1] as int, outs@[s]),
            forall|s: int| 0 <= s < t ==> #[trigger] seg_post(outs@[s], blo@, bhi@),
            forall|s: int| t <= s < k ==> !(#[trigger] outs@[s]).overflow ==>
                chunk_post(x, gather, bounds@[s] as int, bounds@[s + 1] as int, outs@[s]) && seg_post(outs@[s], blo@, bhi@),
        decreases k - t,
    {
        if outs[t].overflow {
            let a = bounds[t];
            let b = bounds[t + 1];
            proof {
                lemma_bounds_le(bounds@, k as int, n as int, t as int);
            }
            let o = rerun_chunk(sig, nsig, offs, bytes, nbytes, codes, need0, need1, ic, ib, kc, kb, bs, n, a, b, gather,
                Ghost(p), blo, bhi, sl);
            outs.set(t, o);
        }
        t = t + 1;
    }
    Ok(outs)
}

/// The deferred-row value of a LIKE on text `t` with the pattern bytes `pat` and escape `\`.
pub proof fn lemma_like_value_pat(t: Seq<u8>, pat: Seq<u8>)
    ensures
        like_value(Val::Text(t), Val::Text(pat), Val::Text(seq![92u8])) == match like_mt(chars(t), pat_toks(pat), 0, 0) {
            Err(e) => Err::<Val, SqlError>(e),
            Ok(r) => Ok::<Val, SqlError>(Val::Bool(r is Match)),
        },
{
    hide(like_mt);
    hide(chars);
    super::sql::lemma_chars_esc();
    assert(escape_of(chars(seq![92u8])) == Some(seq![92u8]));
}

/// Occurrences of `v` in lists that agree on their first `t` elements.
pub proof fn lemma_cnt_lists_prefix(a: Seq<Vec<i64>>, b: Seq<Vec<i64>>, v: int, t: int)
    requires 0 <= t, t <= a.len(), t <= b.len(), forall|i: int| 0 <= i < t ==> a[i]@ == b[i]@,
    ensures cnt_lists(a, v, t) == cnt_lists(b, v, t),
    decreases t,
{
    if t > 0 {
        lemma_cnt_lists_prefix(a, b, v, t - 1);
    }
}

/// Every reordered list (`ps[i]`) is cut into the segments of the key ranges `[lo[t], hi[t])` at the offsets `bo[i]`.
#[verifier::opaque]
pub open spec fn cuts_ok(ls: Seq<Vec<i64>>, bo: Seq<Vec<usize>>, ps: Seq<bool>, lo: Seq<i64>, hi: Seq<i64>) -> bool {
    &&& bo.len() == ls.len()
    &&& ps.len() == ls.len()
    &&& forall|i: int| 0 <= i < ls.len() && #[trigger] ps[i] ==> segs_ok(ls[i]@, bo[i]@, lo, hi)
}

/// The facts `collect_lists` needs about the phase-1 context.
pub open spec fn collect_pre(x: ScanCtx, n: int, gather: bool, kf: spec_fn(int) -> int, keyc: Seq<i64>, pat: Seq<u8>) -> bool {
    &&& x.offs.len() == n + 1
    &&& forall|r: int| 0 <= r < n ==> #[trigger] x.offs[r] <= x.offs[r + 1] && x.offs[r + 1] <= x.bytes.len()
    &&& sigs_match(x, n)
    &&& x.p == pat_toks(pat)
    &&& forall|r: int| 0 <= r < n ==> i64::MIN <= #[trigger] kf(r) <= i64::MAX
    &&& gather ==> keys_ok(x, n) && forall|r: int| 0 <= r < n ==> #[trigger] okey(x, r) == kf(r)
    &&& !gather ==> keyc.len() == n && forall|r: int| 0 <= r < n ==> #[trigger] keyc[r] == kf(r)
}

/// The key `kf(r)` of a row, from the facts key index (gather) or the canonical keys (row mode).
fn row_key(r: usize, gather: bool, ic: &[u32], ib: &[u64], kc: &[u32], kb: &[i64], bs: usize, keyc: &Vec<i64>, n: usize,
    Ghost(x): Ghost<ScanCtx>, Ghost(kf): Ghost<spec_fn(int) -> int>) -> (key: i64)
    requires
        r < n,
        gather ==> keys_ok(x, n as int) && forall|q: int| 0 <= q < n ==> #[trigger] okey(x, q) == kf(q),
        gather ==> x.ic == ic@ && x.ib == ib@ && x.kc == kc@ && x.kb == kb@ && x.bs == bs as int,
        !gather ==> keyc@.len() == n && forall|q: int| 0 <= q < n ==> #[trigger] keyc@[q] == kf(q),
        forall|q: int| 0 <= q < n ==> i64::MIN <= #[trigger] kf(q) <= i64::MAX,
    ensures key as int == kf(r as int),
{
    if gather {
        assert(key_readable(x, n as int, r as int));
        assert(okey(x, r as int) == kf(r as int));
        let s = (ib[r / bs] + ic[r] as u64) as usize;
        kb[s / bs] + kc[s] as i64
    } else {
        keyc[r]
    }
}

/// The `FLAG_LIKE` rows of `a .. b` lie in `a .. b`.
pub proof fn lemma_lrows_range(x: ScanCtx, a: int, b: int)
    requires 0 <= a <= b <= usize::MAX,
    ensures forall|q: int| 0 <= q < lrows(x, a, b).len() ==> a <= #[trigger] lrows(x, a, b)[q] < b,
    decreases b - a,
{
    if b > a {
        lemma_lrows_range(x, a, b - 1);
        let s = lrows(x, a, b - 1);
        if rflag(x, b - 1) == FLAG_LIKE {
            let t = s.push((b - 1) as usize);
            assert forall|q: int| 0 <= q < t.len() implies a <= #[trigger] t[q] < b by {
                if q < s.len() { assert(t[q] == s[q]); }
            }
        }
    }
}

/// The key list of one chunk in row mode: `keyc` of its matching rows.
fn chunk_row_keys(rows: &Vec<usize>, nk: usize, keyc: &Vec<i64>, Ghost(x): Ghost<ScanCtx>, Ghost(a): Ghost<int>,
    Ghost(b): Ghost<int>, Ghost(n): Ghost<int>) -> (l: Vec<i64>)
    requires
        nk <= rows@.len(),
        rows@.subrange(0, nk as int) == lrows(x, a, b),
        0 <= a <= b <= n,
        b <= usize::MAX,
        keyc@.len() == n,
    ensures l@ == map_keys(lrows(x, a, b), keyc@),
{
    proof { lemma_lrows_range(x, a, b); }
    let mut l: Vec<i64> = Vec::new();
    let mut q: usize = 0;
    while q < nk
        invariant
            nk <= rows@.len(),
            rows@.subrange(0, nk as int) == lrows(x, a, b),
            forall|q2: int| 0 <= q2 < lrows(x, a, b).len() ==> a <= #[trigger] lrows(x, a, b)[q2] < b,
            0 <= a <= b <= n,
            keyc@.len() == n,
            q <= nk,
            l@ == map_keys(lrows(x, a, b), keyc@).subrange(0, q as int),
        decreases nk - q,
    {
        let rr = rows[q];
        assert(rr == lrows(x, a, b)[q as int]);
        l.push(keyc[rr]);
        proof { assert(l@ =~= map_keys(lrows(x, a, b), keyc@).subrange(0, q + 1)); }
        q = q + 1;
    }
    proof { assert(l@ =~= map_keys(lrows(x, a, b), keyc@)); }
    l
}

/// The general LIKE evaluator on one text: `FLAG_LIKE`, `FLAG_NO` or `FLAG_ERR` as the matcher answers on its
/// characters.
fn decide_text(text: Vec<u8>, pat: &Vec<u8>) -> (f: u8)
    ensures
        (f == FLAG_LIKE) == (like_mt(chars(text@), pat_toks(pat@), 0, 0) == Ok::<LikeRes, SqlError>(LikeRes::Match)),
        (f == FLAG_ERR) == (like_mt(chars(text@), pat_toks(pat@), 0, 0) is Err),
{
    let ghost t = text@;
    let pv = copy_bytes(pat.as_slice(), 0, pat.len());
    let esc = esc_vec();
    let res = like_value_exec(&EVal::Text(text), &EVal::Text(pv), &EVal::Text(esc));
    proof {
        assert(pat@.subrange(0, pat@.len() as int) =~= pat@);
        lemma_like_value_pat(t, pat@);
    }
    match res {
        Ok(EVal::Bool(true)) => FLAG_LIKE,
        Ok(_) => FLAG_NO,
        Err(_) => FLAG_ERR,
    }
}

/// Decide the deferred rows `defer[0 .. nd]` (= `drows(a, b)`) with the general LIKE evaluator: push the key of each
/// matching one onto `extra`; return the number of rows on which the matcher raises.
fn resolve_deferred(defer: &Vec<usize>, nd: usize, extra: &mut Vec<i64>, offs: &[u64], bytes: &[u8], pat: &Vec<u8>,
    gather: bool, ic: &[u32], ib: &[u64], kc: &[u32], kb: &[i64], bs: usize, keyc: &Vec<i64>, n: usize,
    Ghost(x): Ghost<ScanCtx>, Ghost(kf): Ghost<spec_fn(int) -> int>, Ghost(a): Ghost<int>, Ghost(b): Ghost<int>) -> (de: usize)
    requires
        nd <= defer@.len(),
        defer@.subrange(0, nd as int) == drows(x, a, b),
        0 <= a <= b <= n,
        x.offs == offs@, x.bytes == bytes@,
        gather ==> x.ic == ic@ && x.ib == ib@ && x.kc == kc@ && x.kb == kb@ && x.bs == bs as int,
        collect_pre(x, n as int, gather, kf, keyc@, pat@),
    ensures
        forall|v: int| #[trigger] cnt_seq(final(extra)@, v, final(extra)@.len() as int)
            == cnt_seq(old(extra)@, v, old(extra)@.len() as int) + cnt_list(drows(x, a, b), pr_like(x, kf, v), nd as int),
        de as int == cnt_list(drows(x, a, b), pr_e(x), nd as int),
{
    let ghost dr = drows(x, a, b);
    let ghost extra0 = extra@;
    proof {
        lemma_drows_cnt(x, pr_e(x), a, b);
        lemma_cnt_list_le(dr, pr_e(x), dr.len() as int);
    }
    let blen = bytes.len();
    let mut de: usize = 0;
    let mut q: usize = 0;
    while q < nd
        invariant
            blen == bytes@.len(),
            nd <= defer@.len(),
            defer@.subrange(0, nd as int) == dr,
            dr == drows(x, a, b),
            forall|q2: int| 0 <= q2 < dr.len() ==> a <= #[trigger] dr[q2] < b,
            x.offs == offs@, x.bytes == bytes@,
            gather ==> x.ic == ic@ && x.ib == ib@ && x.kc == kc@ && x.kb == kb@ && x.bs == bs as int,
            collect_pre(x, n as int, gather, kf, keyc@, pat@),
            0 <= a <= b <= n,
            q <= nd,
            forall|v: int| #[trigger] cnt_seq(extra@, v, extra@.len() as int)
                == cnt_seq(extra0, v, extra0.len() as int) + cnt_list(dr, pr_like(x, kf, v), q as int),
            de as int == cnt_list(dr, pr_e(x), q as int),
            cnt_list(dr, pr_e(x), dr.len() as int) <= nd,
        decreases nd - q,
    {
        let rr = defer[q];
        assert(rr == dr[q as int]);
        assert(a <= rr < b);
        assert(x.offs[rr as int] <= x.offs[rr + 1] && x.offs[rr + 1] <= blen);
        let text = copy_bytes(bytes, offs[rr] as usize, offs[rr + 1] as usize);
        assert(text@ == rtext(x, rr as int));
        let fl = decide_text(text, pat);
        proof {
            lemma_cnt_list_mono(dr, pr_e(x), q + 1, dr.len() as int);
        }
        let ghost e0 = extra@;
        if fl == FLAG_LIKE {
            assert(like_r(x, rr as int));
            let key = row_key(rr, gather, ic, ib, kc, kb, bs, keyc, n, Ghost(x), Ghost(kf));
            extra.push(key);
            proof {
                assert forall|v: int| #[trigger] cnt_seq(extra@, v, extra@.len() as int)
                    == cnt_seq(extra0, v, extra0.len() as int) + cnt_list(dr, pr_like(x, kf, v), q + 1) by {
                    lemma_cnt_seq_push(e0, key, v);
                }
            }
        } else if fl == FLAG_ERR {
            assert(err_r(x, rr as int) && !like_r(x, rr as int));
            de = de + 1;
        } else {
            assert(!like_r(x, rr as int) && !err_r(x, rr as int));
        }
        q = q + 1;
    }
    proof {
        assert(drows(x, a, b).len() == nd);
    }
    de
}

/// The match lists and whether the matcher raises on some row.
pub fn collect_lists(outs: Vec<ScanOut>, k: usize, bounds: &Vec<usize>, offs: &[u64], bytes: &[u8], pat: &Vec<u8>,
    gather: bool, ic: &[u32], ib: &[u64], kc: &[u32], kb: &[i64], bs: usize, keyc: &Vec<i64>, n: usize,
    Ghost(x): Ghost<ScanCtx>, Ghost(kf): Ghost<spec_fn(int) -> int>, Ghost(lo): Ghost<Seq<i64>>, Ghost(hi): Ghost<Seq<i64>>)
    -> (r: (Vec<Vec<i64>>, bool, Vec<Vec<usize>>, Vec<bool>))
    requires
        outs@.len() == k,
        bounds_ok(bounds@, k as int, n as int),
        forall|t: int| 0 <= t < k ==> #[trigger] chunk_post(x, gather, bounds@[t] as int, bounds@[t + 1] as int, outs@[t]),
        forall|t: int| 0 <= t < k ==> #[trigger] seg_post(outs@[t], lo, hi),
        x.offs == offs@, x.bytes == bytes@,
        gather ==> x.ic == ic@ && x.ib == ib@ && x.kc == kc@ && x.kb == kb@ && x.bs == bs as int,
        collect_pre(x, n as int, gather, kf, keyc@, pat@),
    ensures
        forall|v: int| #[trigger] likes(r.0@, v) == cnt(pr_like(x, kf, v), 0, n as int),
        r.1 == (cnt(pr_e(x), 0, n as int) > 0),
        cuts_ok(r.0@, r.2@, r.3@, lo, hi),
{
    let ghost orig = outs@;
    let mut outs = outs;
    let mut lists: Vec<Vec<i64>> = Vec::new();
    let mut boffs: Vec<Vec<usize>> = Vec::new();
    let mut parts: Vec<bool> = Vec::new();
    let mut extra: Vec<i64> = Vec::new();
    let mut nerrs: usize = 0;
    let mut derrs: usize = 0;
    let mut t: usize = 0;
    proof { assert(outs@ =~= orig.subrange(0, k as int)); }
    while t < k
        invariant
            bounds_ok(bounds@, k as int, n as int),
            t <= k,
            orig.len() == k,
            forall|s: int| 0 <= s < k ==> #[trigger] chunk_post(x, gather, bounds@[s] as int, bounds@[s + 1] as int, orig[s]),
            forall|s: int| 0 <= s < k ==> #[trigger] seg_post(orig[s], lo, hi),
            boffs@.len() == t, parts@.len() == t,
            forall|i: int| 0 <= i < t && #[trigger] parts@[i] ==> segs_ok(lists@[i]@, boffs@[i]@, lo, hi),
            outs@ == orig.subrange(t as int, k as int),
            x.offs == offs@, x.bytes == bytes@,
            gather ==> x.ic == ic@ && x.ib == ib@ && x.kc == kc@ && x.kb == kb@ && x.bs == bs as int,
            collect_pre(x, n as int, gather, kf, keyc@, pat@),
            lists@.len() == t,
            forall|v: int| #[trigger] cnt_lists(lists@, v, t as int) == cnt(pr_lk(x, kf, v), 0, bounds@[t as int] as int),
            forall|v: int| #[trigger] cnt_seq(extra@, v, extra@.len() as int) == cnt(pr_dlk(x, kf, v), 0, bounds@[t as int] as int),
            nerrs as int == cnt(pr_err(x), 0, bounds@[t as int] as int),
            derrs as int == cnt(pr_derr(x), 0, bounds@[t as int] as int),
            bounds@[t as int] <= n,
        decreases k - t,
    {
        proof {
            lemma_bounds_le(bounds@, k as int, n as int, t as int);
        }
        let ghost (a, b) = (bounds@[t as int] as int, bounds@[t + 1] as int);
        let o = outs.remove(0);
        proof {
            assert(o == orig[t as int]);
            assert(outs@ =~= orig.subrange(t + 1, k as int));
        }
        assert(chunk_post(x, gather, a, b, o));
        assert(seg_post(o, lo, hi));
        let ScanOut { keys, rows, nk, defer, nd, n_err, boff, parted, .. } = o;
        let seg = gather && parted;
        let ghost kv = keys@;
        proof {
            lemma_nerr_cnt(x, a, b);
            lemma_cnt_split(pr_err(x), 0, a, b);
            lemma_cnt_le(pr_err(x), 0, b);
        }
        nerrs = nerrs + n_err;
        // The chunk's key list.
        let list: Vec<i64> = if gather {
            let mut keys = keys;
            keys.truncate(nk);
            proof {
                assert(keys@ == kv.subrange(0, nk as int));
            }
            keys
        } else {
            chunk_row_keys(&rows, nk, keyc, Ghost(x), Ghost(a), Ghost(b), Ghost(n as int))
        };
        proof {
            assert forall|v: int| #[trigger] cnt_seq(list@, v, list@.len() as int) == cnt(pr_lk(x, kf, v), a, b) by {
                if gather {
                    assert forall|r: int| a <= r < b implies i64::MIN <= #[trigger] okey(x, r) <= i64::MAX by {
                        assert(key_readable(x, n as int, r));
                    }
                    lemma_lkeys_cnt(x, a, b, v);
                    // The list holds the matching keys, possibly reordered: equal counts.
                    let lk = lkeys(x, a, b);
                    lemma_cnt_seq_rng(lk, v, lk.len() as int);
                    lemma_cnt_seq_rng(list@, v, list@.len() as int);
                    lemma_rng_sub(kv, nk as int, v, 0, nk as int);
                    assert forall|r: int| a <= r < b implies #[trigger] pr_lk(x, okf(x), v)(r) == pr_lk(x, kf, v)(r) by {
                        assert(okey(x, r) == kf(r));
                    }
                    lemma_cnt_ext(pr_lk(x, okf(x), v), pr_lk(x, kf, v), a, b);
                } else {
                    lemma_lrows_cnt(x, keyc@, a, b, v);
                    assert forall|r: int| a <= r < b implies #[trigger] pr_lk(x, kcf(keyc@), v)(r) == pr_lk(x, kf, v)(r) by {
                        assert(keyc@[r] as int == kf(r));
                    }
                    lemma_cnt_ext(pr_lk(x, kcf(keyc@), v), pr_lk(x, kf, v), a, b);
                }
            }
        }
        let ghost old_lists = lists@;
        let ghost lv0 = lists@;
        let ghost bv0 = boffs@;
        let ghost pv0 = parts@;
        proof {
            if seg {
                assert(list@ == kv.subrange(0, nk as int));
            }
        }
        lists.push(list);
        boffs.push(boff);
        parts.push(seg);
        proof {
            assert forall|i: int| 0 <= i < t + 1 && #[trigger] parts@[i] implies segs_ok(lists@[i]@, boffs@[i]@, lo, hi) by {
                if i < t {
                    assert(parts@[i] == pv0[i] && lists@[i] == lv0[i] && boffs@[i] == bv0[i]);
                }
            }
        }
        proof {
            assert forall|v: int| #[trigger] cnt_lists(lists@, v, t + 1) == cnt(pr_lk(x, kf, v), 0, b) by {
                lemma_cnt_lists_prefix(lists@, old_lists, v, t as int);
                lemma_cnt_split(pr_lk(x, kf, v), 0, a, b);
            }
        }
        // The chunk's deferred rows.
        let ghost extra0 = extra@;
        let ghost derrs0 = derrs as int;
        proof {
            lemma_drows_cnt(x, pr_e(x), a, b);
            lemma_def_derr(x, a, b);
            lemma_cnt_le(pr_derr(x), a, b);
            lemma_cnt_le(pr_derr(x), 0, a);
        }
        let de = resolve_deferred(&defer, nd, &mut extra, offs, bytes, pat, gather, ic, ib, kc, kb, bs, keyc, n,
            Ghost(x), Ghost(kf), Ghost(a), Ghost(b));
        derrs = derrs + de;
        proof {
            assert forall|v: int| #[trigger] cnt_seq(extra@, v, extra@.len() as int) == cnt(pr_dlk(x, kf, v), 0, b) by {
                lemma_drows_cnt(x, pr_like(x, kf, v), a, b);
                lemma_def_dlk(x, kf, v, a, b);
                lemma_cnt_split(pr_dlk(x, kf, v), 0, a, b);
            }
            lemma_cnt_split(pr_derr(x), 0, a, b);
        }
        t = t + 1;
    }
    let ghost lists0 = lists@;
    let ghost extra_v = extra@;
    let ghost bv1 = boffs@;
    let ghost pv1 = parts@;
    lists.push(extra);
    boffs.push(Vec::new());
    parts.push(false);
    proof {
        assert forall|i: int| 0 <= i < lists@.len() && #[trigger] parts@[i] implies segs_ok(lists@[i]@, boffs@[i]@, lo, hi) by {
            assert(i < k);
            assert(parts@[i] == pv1[i] && lists@[i] == lists0[i] && boffs@[i] == bv1[i]);
        }
        reveal(cuts_ok);
    }
    proof {
        let nn = n as int;
        assert(bounds@[k as int] == n);
        assert forall|v: int| #[trigger] likes(lists@, v) == cnt(pr_like(x, kf, v), 0, nn) by {
            lemma_cnt_lists_prefix(lists@, lists0, v, k as int);
            assert(lists@[k as int]@ == extra_v);
            assert forall|q: int| 0 <= q < nn implies #[trigger] pr_like(x, kf, v)(q)
                == (pr_lk(x, kf, v)(q) || pr_dlk(x, kf, v)(q)) && !(pr_lk(x, kf, v)(q) && pr_dlk(x, kf, v)(q)) by {
                lemma_rflag(x, nn, q);
            }
            lemma_cnt_or(pr_lk(x, kf, v), pr_dlk(x, kf, v), pr_like(x, kf, v), 0, nn);
        }
        assert forall|q: int| 0 <= q < nn implies #[trigger] pr_e(x)(q)
            == (pr_err(x)(q) || pr_derr(x)(q)) && !(pr_err(x)(q) && pr_derr(x)(q)) by {
            lemma_rflag(x, nn, q);
        }
        lemma_cnt_or(pr_err(x), pr_derr(x), pr_e(x), 0, nn);
    }
    (lists, nerrs > 0 || derrs > 0, boffs, parts)
}

/// The deferred rows that raise, as a count over the rows.
pub proof fn lemma_def_derr(x: ScanCtx, a: int, b: int)
    ensures cnt(pr_def(x, pr_e(x)), a, b) == cnt(pr_derr(x), a, b),
{
    assert forall|r: int| a <= r < b implies #[trigger] pr_def(x, pr_e(x))(r) == pr_derr(x)(r) by {}
    lemma_cnt_ext(pr_def(x, pr_e(x)), pr_derr(x), a, b);
}

/// The deferred matching rows with key `v`, as a count over the rows.
pub proof fn lemma_def_dlk(x: ScanCtx, kf: spec_fn(int) -> int, v: int, a: int, b: int)
    ensures cnt(pr_def(x, pr_like(x, kf, v)), a, b) == cnt(pr_dlk(x, kf, v), a, b),
{
    assert forall|r: int| a <= r < b implies #[trigger] pr_def(x, pr_like(x, kf, v))(r) == pr_dlk(x, kf, v)(r) by {}
    lemma_cnt_ext(pr_def(x, pr_like(x, kf, v)), pr_dlk(x, kf, v), a, b);
}

/// A list count never exceeds the prefix length.
pub proof fn lemma_cnt_list_le(s: Seq<usize>, p: spec_fn(int) -> bool, m: int)
    requires 0 <= m,
    ensures cnt_list(s, p, m) <= m,
    decreases m,
{
    if m > 0 {
        lemma_cnt_list_le(s, p, m - 1);
    }
}

/// List counts grow with the prefix.
pub proof fn lemma_cnt_list_mono(s: Seq<usize>, p: spec_fn(int) -> bool, m1: int, m2: int)
    requires 0 <= m1 <= m2,
    ensures cnt_list(s, p, m1) <= cnt_list(s, p, m2),
    decreases m2,
{
    if m1 < m2 {
        lemma_cnt_list_mono(s, p, m1, m2 - 1);
    }
}

} // verus!
