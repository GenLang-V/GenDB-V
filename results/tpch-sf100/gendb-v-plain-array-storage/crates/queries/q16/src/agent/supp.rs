//! The NOT IN subquery's key set from the supplier table (`excluded`), and the range of the supplier keys.
//!
//! Parallel tasks (`SuppTask`, one per range of supplier rows) test each comment: an ASCII comment by the byte test
//! of `'%Customer%Complaints%'` (`common::like_two`), a non-ASCII one is set aside; the calling thread then runs the
//! verified `LIKE` on the set-aside comments and collects the keys (`supp_pass`). Each task also reports the least
//! and greatest supplier key of its rows.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::exec::value::EVal;
use crate::exec::fns::like::like_value_exec;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::model::*;
use crate::agent::cols::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_sub::*;
use crate::agent::common::like_two::*;
use crate::agent::common::byte_scan::{scan_ascii_byte, lemma_has_two_byte};
use crate::agent::common::slot_buffer::SlotBuffer;
use crate::agent::common::split::*;
use crate::agent::prep::big;

verus! {

/// The two literals of `'%Customer%Complaints%'`.
pub open spec fn cust_lit() -> Seq<u8> { two_lit1(comment_pat(), 8) }
pub open spec fn compl_lit() -> Seq<u8> { two_lit2(comment_pat(), 8, 10) }

/// `'%Customer%Complaints%'` is a two-segment pattern of 8 and 10 literal bytes.
pub proof fn lemma_comment_two()
    ensures two_pattern(comment_pat(), 8, 10),
{
    reveal(comment_pat);
    let p = comment_pat();
    assert forall|i: int| 1 <= i <= 8 implies #[trigger] lit_byte(p[i]) by {}
    assert forall|i: int| 10 <= i <= 19 implies #[trigger] lit_byte(p[i]) by {}
}

/// An ASCII comment matches exactly when it passes the byte test.
pub proof fn lemma_comment_ascii(s: Seq<u8>)
    requires ascii(s),
    ensures comment_hit(s) == has_two(s, cust_lit(), compl_lit()),
{
    lemma_comment_two();
    lemma_like_two(s, comment_pat(), 8, 10);
}

/// "Customer" starts with 'C'.
pub proof fn lemma_cust_first()
    ensures cust_lit().len() == 8, cust_lit()[0] == 67u8,
{
    reveal(comment_pat);
}

/// The literal vectors of the byte test.
pub fn comment_lits() -> (r: (Vec<u8>, Vec<u8>))
    ensures r.0@ == cust_lit(), r.1@ == compl_lit(), r.0@.len() == 8, r.1@.len() == 10,
{
    let a = vec![67u8, 117u8, 115u8, 116u8, 111u8, 109u8, 101u8, 114u8];
    let b = vec![67u8, 111u8, 109u8, 112u8, 108u8, 97u8, 105u8, 110u8, 116u8, 115u8];
    proof {
        reveal(comment_pat);
        assert(a@ =~= cust_lit());
        assert(b@ =~= compl_lit());
    }
    (a, b)
}

/// One range of supplier rows.
pub struct SuppTask {
    pub lo: usize,
    pub hi: usize,
    pub ns: usize,
    pub keys: &'static [i64],
    pub comment: TextCol,
    pub cust: Vec<u8>,
    pub compl: Vec<u8>,
    pub hits: SlotBuffer<usize>,
    pub others: SlotBuffer<usize>,
    pub sv: Ghost<StoresView>,
}

/// A task's result: the matching rows with an ASCII comment, the rows with a non-ASCII comment, the key bounds.
pub struct SuppOut {
    pub lo: usize,
    pub hi: usize,
    pub hits: SlotBuffer<usize>,
    pub others: SlotBuffer<usize>,
    pub kmin: i64,
    pub kmax: i64,
}

/// What a task needs.
pub open spec fn supp_pre(t: SuppTask) -> bool {
    let sv = t.sv@;
    &&& t.lo < t.hi <= t.ns
    &&& t.ns == supp_n(sv)
    &&& t.keys@ == s_keys(sv)
    &&& tcol_is(t.comment, comment_view(sv), t.ns as int)
    &&& t.cust@ == cust_lit() && t.cust@.len() == 8
    &&& t.compl@ == compl_lit() && t.compl@.len() == 10
    &&& t.hits.wf() && t.hits.view() == Seq::<usize>::empty() && t.hits.capacity() >= t.hi - t.lo
    &&& t.others.wf() && t.others.view() == Seq::<usize>::empty() && t.others.capacity() >= t.hi - t.lo
}

/// Row `b` has an ASCII comment that matches.
pub open spec fn ascii_hit(sv: StoresView, b: int) -> bool {
    ascii(s_comment(sv, b)) && supp_hit(sv, b)
}

/// The rows of `v` are exactly the rows `b` of `[lo, hi)` with `cond(b)`.
pub open spec fn rows_are(v: Seq<usize>, lo: int, hi: int, cond: spec_fn(int) -> bool) -> bool {
    &&& forall|i: int| 0 <= i < v.len() ==> lo <= #[trigger] v[i] < hi && cond(v[i] as int)
    &&& forall|b: int| lo <= b < hi && cond(b) ==> #[trigger] v.contains(b as usize)
}

/// What a task guarantees.
pub open spec fn supp_post(lo: int, hi: int, sv: StoresView, out: SuppOut) -> bool {
    &&& out.lo == lo && out.hi == hi
    &&& out.hits.wf() && out.others.wf()
    &&& rows_are(out.hits.view(), lo, hi, |b: int| ascii_hit(sv, b))
    &&& rows_are(out.others.view(), lo, hi, |b: int| !ascii(s_comment(sv, b)))
    &&& forall|b: int| lo <= b < hi ==> out.kmin <= #[trigger] s_keys(sv)[b] <= out.kmax
}

impl WorkerTask for SuppTask {
    type Output = SuppOut;

    open spec fn pre(&self) -> bool {
        supp_pre(*self)
    }

    open spec fn post(&self, out: SuppOut) -> bool {
        supp_post(self.lo as int, self.hi as int, self.sv@, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: SuppOut) {
        let SuppTask { lo, hi, ns, keys, comment, cust, compl, mut hits, mut others, sv } = self;
        let ghost sv = sv@;
        let mut kmin = keys[lo];
        let mut kmax = keys[lo];
        let mut b = lo;
        while b < hi
            invariant
                lo < hi <= ns, ns == supp_n(sv), keys@ == s_keys(sv), lo <= b <= hi,
                tcol_is(comment, comment_view(sv), ns as int),
                cust@ == cust_lit(), cust@.len() == 8, compl@ == compl_lit(), compl@.len() == 10,
                hits.wf(), others.wf(), hits.capacity() >= hi - lo, others.capacity() >= hi - lo,
                hits.view().len() <= b - lo, others.view().len() <= b - lo,
                rows_are(hits.view(), lo as int, b as int, |x: int| ascii_hit(sv, x)),
                rows_are(others.view(), lo as int, b as int, |x: int| !ascii(s_comment(sv, x))),
                forall|x: int| lo <= x < b ==> kmin <= #[trigger] s_keys(sv)[x] <= kmax,
                kmin <= s_keys(sv)[lo as int] <= kmax,
            decreases hi - b,
        {
            let (x, y) = trange(&comment, b, Ghost(ns as int));
            let ghost s = s_comment(sv, b as int);
            proof { assert(comment.bytes@.subrange(x as int, y as int) == s); }
            let ghost h0 = hits.view();
            let ghost o0 = others.view();
            // One word-at-a-time pass: ASCII, and whether the 'C' that starts "Customer" occurs at all.
            let (asc, has_c) = scan_ascii_byte(comment.bytes, x, y, 67u8);
            if asc {
                proof {
                    lemma_comment_ascii(s);
                    lemma_cust_first();
                    if !has_c && has_two(s, cust_lit(), compl_lit()) {
                        lemma_has_two_byte(s, cust_lit(), compl_lit());
                    }
                }
                if has_c && has_two_exec(comment.bytes, x, y, &cust, 8, &compl, 10) {
                    hits.push(b);
                    proof { assert(hits.view() == h0.push(b)); }
                }
            } else {
                others.push(b);
                proof { assert(others.view() == o0.push(b)); }
            }
            proof {
                let hv = hits.view();
                let ov = others.view();
                assert forall|i: int| 0 <= i < hv.len() implies lo <= #[trigger] hv[i] < b + 1 && ascii_hit(sv, hv[i] as int) by {
                    if i < h0.len() { assert(hv[i] == h0[i]); }
                }
                assert forall|z: int| lo <= z < b + 1 && ascii_hit(sv, z) implies #[trigger] hv.contains(z as usize) by {
                    if z < b {
                        assert(h0.contains(z as usize));
                        let i = choose|i: int| 0 <= i < h0.len() && h0[i] == z as usize;
                        assert(hv[i] == z as usize);
                    } else {
                        assert(hv[hv.len() - 1] == z as usize);
                    }
                }
                assert forall|i: int| 0 <= i < ov.len() implies lo <= #[trigger] ov[i] < b + 1 && !ascii(s_comment(sv, ov[i] as int)) by {
                    if i < o0.len() { assert(ov[i] == o0[i]); }
                }
                assert forall|z: int| lo <= z < b + 1 && !ascii(s_comment(sv, z)) implies #[trigger] ov.contains(z as usize) by {
                    if z < b {
                        assert(o0.contains(z as usize));
                        let i = choose|i: int| 0 <= i < o0.len() && o0[i] == z as usize;
                        assert(ov[i] == z as usize);
                    } else {
                        assert(ov[ov.len() - 1] == z as usize);
                    }
                }
            }
            let k = keys[b];
            if k < kmin { kmin = k; }
            if k > kmax { kmax = k; }
            b = b + 1;
        }
        SuppOut { lo, hi, hits, others, kmin, kmax }
    }
}

/// A copy of `b[lo..hi]`.
pub fn copy_bytes(b: &[u8], lo: usize, hi: usize) -> (v: Vec<u8>)
    requires lo <= hi <= b@.len(),
    ensures v@ == b@.subrange(lo as int, hi as int),
{
    let mut v: Vec<u8> = Vec::new();
    let mut i = lo;
    while i < hi
        invariant lo <= i <= hi <= b@.len(), v@ == b@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        v.push(b[i]);
        proof { assert(b@.subrange(lo as int, i + 1) =~= b@.subrange(lo as int, i as int).push(b@[i as int])); }
        i = i + 1;
    }
    v
}

/// The verified `LIKE` of the comment of supplier row `b` against `'%Customer%Complaints%'` (calling thread).
fn comment_hit_general(c: &Cols, b: usize, pat: &EVal, esc: &EVal, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), b < c.ns, pat@ == Val::Text(comment_pat()), esc@ == Val::Text(backslash()),
    ensures r == supp_hit(sv, b as int),
{
    let (x, y) = trange(&c.comment, b, Ghost(c.ns as int));
    let v = copy_bytes(c.comment.bytes, x, y);
    let s = EVal::Text(v);
    let ghost sb = s_comment(sv, b as int);
    proof {
        assert(s@ == Val::Text(sb));
        lemma_comment_bool(sb);
    }
    match like_value_exec(&s, pat, esc) {
        Ok(EVal::Bool(t)) => t,
        _ => false,
    }
}

/// The supplier pass's result: the excluded keys and bounds of all supplier keys.
pub struct SuppResult {
    pub ekeys: Vec<i64>,
    pub smin: i64,
    pub smax: i64,
}

/// `v` holds `k`.
pub open spec fn has_key(v: Seq<i64>, k: int) -> bool {
    exists|x: int| 0 <= x < v.len() && v[x] == k
}

/// Some matching supplier row below `n` has key `k`.
pub open spec fn hit_below(sv: StoresView, n: int, k: int) -> bool {
    exists|b: int| 0 <= b < n && supp_hit(sv, b) && s_keys(sv)[b] == k
}

/// Some row among the first `i` of `rows` that matches has key `k`.
pub open spec fn rows_key(sv: StoresView, rows: Seq<usize>, i: int, k: int) -> bool {
    exists|j: int| 0 <= j < i && supp_hit(sv, rows[j] as int) && s_keys(sv)[rows[j] as int] == k
}

/// `r` holds exactly the excluded keys, and bounds every supplier key.
pub open spec fn supp_result_ok(r: SuppResult, sv: StoresView) -> bool {
    &&& forall|k: int| #[trigger] has_key(r.ekeys@, k) <==> excluded(sv, k)
    &&& forall|i: int| 0 <= i < r.ekeys@.len() ==> r.smin <= #[trigger] r.ekeys@[i] <= r.smax
    &&& forall|b: int| 0 <= b < supp_n(sv) ==> r.smin <= #[trigger] s_keys(sv)[b] <= r.smax
}

/// The tasks over the ranges `rs` of supplier rows.
fn supp_tasks(c: &Cols, rs: &Vec<(usize, usize)>, Ghost(sv): Ghost<StoresView>) -> (tasks: Vec<SuppTask>)
    requires cols_ok(*c, sv), covers(rs@, c.ns as int),
    ensures
        tasks@.len() == rs@.len(),
        forall|t: int| 0 <= t < tasks@.len() ==> #[trigger] tasks@[t].pre(),
        forall|t: int| 0 <= t < tasks@.len() ==> (#[trigger] tasks@[t]).lo == rs@[t].0 && tasks@[t].hi == rs@[t].1
            && tasks@[t].sv@ == sv,
{
    let mut tasks: Vec<SuppTask> = Vec::new();
    let mut t: usize = 0;
    while t < rs.len()
        invariant
            cols_ok(*c, sv), covers(rs@, c.ns as int), t <= rs@.len(), tasks@.len() == t,
            forall|j: int| 0 <= j < t ==> #[trigger] tasks@[j].pre(),
            forall|j: int| 0 <= j < t ==> (#[trigger] tasks@[j]).lo == rs@[j].0 && tasks@[j].hi == rs@[j].1 && tasks@[j].sv@ == sv,
        decreases rs@.len() - t,
    {
        let (lo, hi) = rs[t];
        proof { lemma_in_bounds(rs@, c.ns as int, t as int); }
        let (cust, compl) = comment_lits();
        let task = SuppTask {
            lo, hi, ns: c.ns, keys: c.s_key, comment: c.comment, cust, compl,
            hits: SlotBuffer::new(big(hi - lo), 0usize), others: SlotBuffer::new(big(hi - lo), 0usize), sv: Ghost(sv),
        };
        tasks.push(task);
        t = t + 1;
    }
    tasks
}

/// Append the keys of the rows of `rows` that match (`check`: by the verified `LIKE`; otherwise every row
/// matches, as the task's ASCII hits do).
fn append_keys(c: &Cols, rows: &SlotBuffer<usize>, check: bool, pat: &EVal, esc: &EVal, ekeys: &mut Vec<i64>,
    Ghost(sv): Ghost<StoresView>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>)
    requires
        cols_ok(*c, sv), rows.wf(), 0 <= lo < hi <= c.ns,
        pat@ == Val::Text(comment_pat()), esc@ == Val::Text(backslash()),
        forall|i: int| 0 <= i < rows.view().len() ==> lo <= #[trigger] rows.view()[i] < hi,
        !check ==> forall|i: int| 0 <= i < rows.view().len() ==> supp_hit(sv, #[trigger] rows.view()[i] as int),
        forall|x: int| 0 <= x < old(ekeys)@.len() ==> #[trigger] is_supplier(sv, old(ekeys)@[x] as int),
    ensures
        forall|k: int| #[trigger] has_key(final(ekeys)@, k) <==> (has_key(old(ekeys)@, k) || rows_key(sv, rows.view(), rows.view().len() as int, k)),
        forall|x: int| 0 <= x < final(ekeys)@.len() ==> #[trigger] is_supplier(sv, final(ekeys)@[x] as int),
{
    let ghost e0 = ekeys@;
    let ghost rv = rows.view();
    let n = rows.len();
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c, sv), rows.wf(), rv == rows.view(), n == rv.len(), i <= n, 0 <= lo < hi <= c.ns,
            pat@ == Val::Text(comment_pat()), esc@ == Val::Text(backslash()),
            forall|j: int| 0 <= j < rv.len() ==> lo <= #[trigger] rv[j] < hi,
            !check ==> forall|j: int| 0 <= j < rv.len() ==> supp_hit(sv, #[trigger] rv[j] as int),
            forall|k: int| #[trigger] has_key(ekeys@, k) <==> (has_key(e0, k) || rows_key(sv, rv, i as int, k)),
            forall|x: int| 0 <= x < ekeys@.len() ==> #[trigger] is_supplier(sv, ekeys@[x] as int),
        decreases n - i,
    {
        let b = rows.get(i);
        proof { assert(lo <= rv[i as int] < hi); }
        let hit = if check { comment_hit_general(c, b, pat, esc, Ghost(sv)) } else { true };
        proof { assert(hit == supp_hit(sv, b as int)); }
        let ghost eb = ekeys@;
        if hit {
            ekeys.push(c.s_key[b]);
        }
        proof {
            assert forall|k: int| #[trigger] has_key(ekeys@, k) <==> (has_key(e0, k) || rows_key(sv, rv, i + 1, k)) by {
                if has_key(ekeys@, k) {
                    let x = choose|x: int| 0 <= x < ekeys@.len() && ekeys@[x] == k;
                    if x < eb.len() {
                        assert(has_key(eb, k));
                        if rows_key(sv, rv, i as int, k) {
                            let j = choose|j: int| 0 <= j < i && supp_hit(sv, rv[j] as int) && s_keys(sv)[rv[j] as int] == k;
                        }
                    } else {
                        assert(supp_hit(sv, rv[i as int] as int) && s_keys(sv)[rv[i as int] as int] == k);
                    }
                }
                if rows_key(sv, rv, i + 1, k) {
                    let j = choose|j: int| 0 <= j < i + 1 && supp_hit(sv, rv[j] as int) && s_keys(sv)[rv[j] as int] == k;
                    if j == i {
                        assert(ekeys@[eb.len() as int] == k);
                    } else {
                        assert(rows_key(sv, rv, i as int, k));
                        assert(has_key(eb, k));
                        let x = choose|x: int| 0 <= x < eb.len() && eb[x] == k;
                        assert(ekeys@[x] == k);
                    }
                }
                if has_key(e0, k) {
                    assert(has_key(eb, k));
                    let x = choose|x: int| 0 <= x < eb.len() && eb[x] == k;
                    assert(ekeys@[x] == k);
                }
            }
            assert forall|x: int| 0 <= x < ekeys@.len() implies #[trigger] is_supplier(sv, ekeys@[x] as int) by {
                if x < eb.len() { assert(ekeys@[x] == eb[x]); assert(is_supplier(sv, eb[x] as int)); } else { assert(s_keys(sv)[b as int] == ekeys@[x]); }
            }
        }
        i = i + 1;
    }
}

/// The supplier pass: the excluded keys and the bounds of the supplier keys (at least one supplier row).
/// One supplier task over rows `lo..hi`.
pub fn make_supp_task(c: &Cols, lo: usize, hi: usize, Ghost(sv): Ghost<StoresView>) -> (t: SuppTask)
    requires cols_ok(*c, sv), lo < hi <= c.ns,
    ensures t.pre(), t.lo == lo, t.hi == hi, t.sv@ == sv,
{
    let (cust, compl) = comment_lits();
    SuppTask {
        lo, hi, ns: c.ns, keys: c.s_key, comment: c.comment, cust, compl,
        hits: SlotBuffer::new(big(hi - lo), 0usize), others: SlotBuffer::new(big(hi - lo), 0usize), sv: Ghost(sv),
    }
}

/// The supplier pass: the excluded keys and the bounds of the supplier keys (at least one supplier row).
pub fn supp_pass(c: &Cols, Ghost(sv): Ghost<StoresView>, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<SuppResult, WorkerFailure>)
    requires cols_ok(*c, sv), c.ns >= 1, 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(res) ==> supp_result_ok(res, sv),
{
    let rs = split_ranges(c.ns, workers);
    let tasks = supp_tasks(c, &rs, Ghost(sv));
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let mut souts: Vec<&SuppOut> = Vec::new();
    let mut t: usize = 0;
    while t < outs.len()
        invariant
            t <= outs@.len(), souts@.len() == t, outs@.len() == rs@.len(), tv.len() == rs@.len(),
            forall|j: int| 0 <= j < t ==> *souts@[j] == outs@[j],
        decreases outs@.len() - t,
    {
        souts.push(&outs[t]);
        t = t + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < rs@.len() implies #[trigger] supp_post(rs@[j].0 as int, rs@[j].1 as int, sv, *souts@[j]) by {
            assert(tv[j].post(outs@[j]));
            assert(tv[j].lo == rs@[j].0 && tv[j].hi == rs@[j].1 && tv[j].sv@ == sv);
        }
    }
    Ok(supp_merge(c, &souts, &rs, Ghost(sv)))
}

/// The supplier pass's result from its tasks' outputs over the ranges `rs`.
pub fn supp_merge(c: &Cols, souts: &Vec<&SuppOut>, rs: &Vec<(usize, usize)>, Ghost(sv): Ghost<StoresView>) -> (r: SuppResult)
    requires
        cols_ok(*c, sv), covers(rs@, c.ns as int), souts@.len() == rs@.len(),
        forall|j: int| 0 <= j < rs@.len() ==> #[trigger] supp_post(rs@[j].0 as int, rs@[j].1 as int, sv, *souts@[j]),
    ensures supp_result_ok(r, sv),
{
    let pat = EVal::Text(comment_pat_vec());
    let escv = vec![92u8];
    proof { assert(escv@ =~= backslash()); }
    let esc = EVal::Text(escv);
    let mut ekeys: Vec<i64> = Vec::new();
    let mut smin = souts[0].kmin;
    let mut smax = souts[0].kmax;
    let nt = souts.len();
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, sv), covers(rs@, c.ns as int), nt == souts@.len(), nt == rs@.len(), t <= nt,
            forall|j: int| 0 <= j < nt ==> #[trigger] supp_post(rs@[j].0 as int, rs@[j].1 as int, sv, *souts@[j]),
            pat@ == Val::Text(comment_pat()), esc@ == Val::Text(backslash()),
            smin <= souts@[0].kmin, souts@[0].kmax <= smax,
            forall|j: int| 0 <= j < t ==> smin <= (#[trigger] souts@[j]).kmin && souts@[j].kmax <= smax,
            forall|k: int| #[trigger] has_key(ekeys@, k) <==> hit_below(sv, if t == 0 { 0 } else { rs@[t - 1].1 as int }, k),
            forall|i: int| 0 <= i < ekeys@.len() ==> #[trigger] is_supplier(sv, ekeys@[i] as int),
        decreases nt - t,
    {
        let o: &SuppOut = souts[t];
        proof {
            assert(supp_post(rs@[t as int].0 as int, rs@[t as int].1 as int, sv, *souts@[t as int]));
            lemma_in_bounds(rs@, c.ns as int, t as int);
        }
        if o.kmin < smin { smin = o.kmin; }
        if o.kmax > smax { smax = o.kmax; }
        let ghost e0 = ekeys@;
        let ghost lo_t = rs@[t as int].0 as int;
        let ghost hi_t = rs@[t as int].1 as int;
        let ghost prev = if t == 0 { 0int } else { rs@[t - 1].1 as int };
        proof {
            if t > 0 { assert(rs@[t - 1].1 == rs@[t as int].0); }
            assert(prev == lo_t);
            assert forall|i: int| 0 <= i < o.hits.view().len() implies supp_hit(sv, #[trigger] o.hits.view()[i] as int) by {
                assert(ascii_hit(sv, o.hits.view()[i] as int));
            }
        }
        append_keys(c, &o.hits, false, &pat, &esc, &mut ekeys, Ghost(sv), Ghost(lo_t), Ghost(hi_t));
        let ghost e1 = ekeys@;
        append_keys(c, &o.others, true, &pat, &esc, &mut ekeys, Ghost(sv), Ghost(lo_t), Ghost(hi_t));
        // Rows `lo_t..hi_t` are covered: the hits are the ASCII matches, the others every non-ASCII row.
        proof {
            let ov = o.others.view();
            let hv = o.hits.view();
            assert forall|k: int| #[trigger] has_key(ekeys@, k) <==> hit_below(sv, hi_t, k) by {
                assert(has_key(e1, k) <==> (has_key(e0, k) || rows_key(sv, hv, hv.len() as int, k)));
                if has_key(ekeys@, k) {
                    if rows_key(sv, hv, hv.len() as int, k) {
                        let j = choose|j: int| 0 <= j < hv.len() && supp_hit(sv, hv[j] as int) && s_keys(sv)[hv[j] as int] == k;
                        assert(lo_t <= hv[j] < hi_t);
                    } else if rows_key(sv, ov, ov.len() as int, k) {
                        let j = choose|j: int| 0 <= j < ov.len() && supp_hit(sv, ov[j] as int) && s_keys(sv)[ov[j] as int] == k;
                        assert(lo_t <= ov[j] < hi_t);
                    } else {
                        assert(has_key(e0, k));
                        let b = choose|b: int| 0 <= b < prev && supp_hit(sv, b) && s_keys(sv)[b] == k;
                    }
                }
                if hit_below(sv, hi_t, k) {
                    let b = choose|b: int| 0 <= b < hi_t && supp_hit(sv, b) && s_keys(sv)[b] == k;
                    if b < prev {
                        assert(hit_below(sv, prev, k));
                        assert(has_key(e0, k));
                    } else if ascii(s_comment(sv, b)) {
                        assert(ascii_hit(sv, b));
                        assert(hv.contains(b as usize));
                        let j = choose|j: int| 0 <= j < hv.len() && hv[j] == b as usize;
                        assert(rows_key(sv, hv, hv.len() as int, k));
                    } else {
                        assert(ov.contains(b as usize));
                        let j = choose|j: int| 0 <= j < ov.len() && ov[j] == b as usize;
                        assert(rows_key(sv, ov, ov.len() as int, k));
                    }
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert(rs@[nt - 1].1 == c.ns);
        assert forall|k: int| #[trigger] has_key(ekeys@, k) <==> excluded(sv, k) by {
            if has_key(ekeys@, k) {
                let b = choose|b: int| 0 <= b < c.ns && supp_hit(sv, b) && s_keys(sv)[b] == k;
                assert(supp_hit(sv, b));
            }
            if excluded(sv, k) {
                let b = choose|b: int| 0 <= b < supp_n(sv) && #[trigger] supp_hit(sv, b) && s_keys(sv)[b] == k;
                assert(hit_below(sv, c.ns as int, k));
            }
        }
        assert forall|b: int| 0 <= b < supp_n(sv) implies smin <= #[trigger] s_keys(sv)[b] <= smax by {
            lemma_covered(rs@, c.ns as int, b);
            let j = choose|j: int| 0 <= j < rs@.len() && rs@[j].0 <= b < #[trigger] rs@[j].1;
            assert(supp_post(rs@[j].0 as int, rs@[j].1 as int, sv, *souts@[j]));
            assert(smin <= souts@[j].kmin && souts@[j].kmax <= smax);
        }
        assert forall|i: int| 0 <= i < ekeys@.len() implies smin <= #[trigger] ekeys@[i] <= smax by {
            assert(is_supplier(sv, ekeys@[i] as int));
            let b = choose|b: int| 0 <= b < supp_n(sv) && s_keys(sv)[b] == ekeys@[i];
            assert(smin <= s_keys(sv)[b] <= smax);
        }
    }
    SuppResult { ekeys, smin, smax }
}


/// `'%Customer%Complaints%'` as a vector.
fn comment_pat_vec() -> (v: Vec<u8>)
    ensures v@ == comment_pat(),
{
    let v = vec![37u8, 67u8, 117u8, 115u8, 116u8, 111u8, 109u8, 101u8, 114u8, 37u8, 67u8, 111u8, 109u8, 112u8, 108u8,
        97u8, 105u8, 110u8, 116u8, 115u8, 37u8];
    proof {
        reveal(comment_pat);
        assert(v@ =~= comment_pat());
    }
    v
}

} // verus!
