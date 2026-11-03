//! The part pass: the keys of the part rows whose name matches `$1`, in row order (`pkeys`).
//!
//! Fast path (`part_keys_fast`): for a pattern `'lit%'` (`common::like_prefix`), each task tests the names of a
//! range of part rows with the byte test `prefix_match` (exactly `LIKE` there, and never an error) and writes the
//! keys of the matching rows into its preallocated output; the outputs are joined in task order. General path
//! (`part_keys_general`, serial): the verified `LIKE` on every name, which also finds a name whose `LIKE` raises.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::exec::value::{EVal, view_result};
use crate::exec::fns::like::like_value_exec;
use crate::link::query::text_at;
use crate::agent::tables::*;
use crate::agent::params::pat_of;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::common::selection::*;
use crate::agent::common::like_prefix::*;
use crate::agent::common::split::*;
use crate::agent::common::bigzero::zeroed_i64;

verus! {

// ------------------------------------------------------------------------------------------------ specification

/// Part row `p` matches `$1`.
pub open spec fn pm(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> bool { |p: int| pmatch(sv, ps, p) }

/// The keys of the matching part rows of `[lo, hi)`, in row order.
pub open spec fn pkeys(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> Seq<int> {
    range_filter(lo, hi, pm(sv, ps)).map_values(|p: int| pk(sv)[p] as int)
}

/// `out[0..n]` holds the keys `keys`.
pub open spec fn keys_out(out: Seq<i64>, n: int, keys: Seq<int>) -> bool {
    &&& n == keys.len() && n <= out.len()
    &&& forall|t: int| 0 <= t < n ==> #[trigger] out[t] as int == keys[t]
}

/// The keys of one more row.
proof fn lemma_pkeys_step(sv: StoresView, ps: Seq<Literal>, lo: int, r: int)
    requires lo <= r,
    ensures pkeys(sv, ps, lo, r + 1) == if pmatch(sv, ps, r) { pkeys(sv, ps, lo, r).push(pk(sv)[r] as int) } else { pkeys(sv, ps, lo, r) },
{
    let f = pm(sv, ps);
    assert(range_filter(lo, r + 1, f) == if f(r) { range_filter(lo, r, f).push(r) } else { range_filter(lo, r, f) });
    if f(r) {
        assert(pkeys(sv, ps, lo, r + 1) =~= pkeys(sv, ps, lo, r).push(pk(sv)[r] as int));
    }
}

/// Adjacent ranges' keys concatenate.
proof fn lemma_pkeys_concat(sv: StoresView, ps: Seq<Literal>, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures pkeys(sv, ps, lo, mid) + pkeys(sv, ps, mid, hi) == pkeys(sv, ps, lo, hi),
{
    lemma_range_filter_concat(lo, mid, hi, pm(sv, ps));
    assert(pkeys(sv, ps, lo, mid) + pkeys(sv, ps, mid, hi) =~= pkeys(sv, ps, lo, hi));
}

/// For a prefix pattern, part row `p` matches exactly when its name passes the byte test, and its `LIKE` never
/// raises.
pub proof fn lemma_pmatch_prefix(sv: StoresView, ps: Seq<Literal>, p: int)
    requires prefix_pattern(pat_of(ps)),
    ensures
        pmatch(sv, ps, p) == prefix_match(pname(sv, p), prefix_lit(pat_of(ps))),
        like_ok(pname(sv, p), pat_of(ps)),
{
    assert(esc() =~= backslash());
    lemma_like_prefix(pname(sv, p), pat_of(ps));
}

/// The part keys of all rows are the keys of the matching rows: `in_part`.
pub proof fn lemma_pkeys_in_part(sv: StoresView, ps: Seq<Literal>, v: int)
    ensures pkeys(sv, ps, 0, n_p(sv) as int).contains(v) == in_part(sv, ps, v),
{
    let f = pm(sv, ps);
    let rf = range_filter(0, n_p(sv) as int, f);
    let ks = pkeys(sv, ps, 0, n_p(sv) as int);
    lemma_range_filter_members(0, n_p(sv) as int, f);
    if ks.contains(v) {
        let t = choose|t: int| 0 <= t < ks.len() && ks[t] == v;
        let p = rf[t];
        assert(0 <= p < n_p(sv) && f(p));
        assert(pk(sv)[p] as int == v);
    }
    if in_part(sv, ps, v) {
        let p = choose|p: int| 0 <= p < n_p(sv) && #[trigger] pk(sv)[p] as int == v && pmatch(sv, ps, p);
        assert(f(p));
        let t = choose|t: int| 0 <= t < rf.len() && #[trigger] rf[t] == p;
        assert(ks[t] == v);
    }
}

// ------------------------------------------------------------------------------------------------ the fast path

/// One task of the fast part pass: the part rows `lo..hi`.
pub struct PartTask {
    pub pkey: &'static [i64],
    pub pname: Text,
    pub np: usize,
    pub lit: Arc<Vec<u8>>,
    pub k: usize,
    pub lo: usize,
    pub hi: usize,
    pub out: Vec<i64>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

impl WorkerTask for PartTask {
    type Output = (Vec<i64>, usize);

    open spec fn pre(&self) -> bool {
        &&& self.pkey@ == pk(self.sv@) && self.np as int == n_p(self.sv@) && self.pkey@.len() == n_p(self.sv@)
        &&& text_ok(self.pname, pname_col(self.sv@), n_p(self.sv@) as int)
        &&& prefix_pattern(pat_of(self.ps@)) && (*self.lit)@ == prefix_lit(pat_of(self.ps@)) && self.k == (*self.lit)@.len()
        &&& self.lo <= self.hi <= self.np && self.out@.len() >= self.hi - self.lo
    }

    open spec fn post(&self, out: (Vec<i64>, usize)) -> bool {
        keys_out(out.0@, out.1 as int, pkeys(self.sv@, self.ps@, self.lo as int, self.hi as int))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: (Vec<i64>, usize)) {
        let PartTask { pkey, pname, np, lit, k, lo, hi, out, sv, ps } = self;
        let ghost sv = sv@;
        let ghost ps = ps@;
        let litv: &Vec<u8> = &*lit;
        let mut out = out;
        let mut n: usize = 0;
        let mut r = lo;
        while r < hi
            invariant
                pkey@ == pk(sv), np as int == n_p(sv), pkey@.len() == n_p(sv),
                text_ok(pname, pname_col(sv), n_p(sv) as int),
                prefix_pattern(pat_of(ps)), litv@ == prefix_lit(pat_of(ps)), k == litv@.len(),
                lo <= r <= hi <= np, out@.len() >= hi - lo, n <= r - lo,
                keys_out(out@, n as int, pkeys(sv, ps, lo as int, r as int)),
            decreases hi - r,
        {
            let (s, e) = text_range(pname, r, Ghost(pname_col(sv)), Ghost(n_p(sv) as int));
            let m = prefix_match_at(pname.bytes, pname.blen, s, e, litv, k);
            proof {
                lemma_pmatch_prefix(sv, ps, r as int);
                lemma_pkeys_step(sv, ps, lo as int, r as int);
            }
            if m {
                out[n] = pkey[r];
                n = n + 1;
            }
            r = r + 1;
        }
        (out, n)
    }
}

/// The keys of all matching part rows for a prefix pattern, by `ntasks` parallel tasks.
pub fn part_keys_fast(c: &Cols, lit: Vec<u8>, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Vec<i64>, WorkerFailure>)
    requires
        cols_ok(*c, sv), 1 <= workers <= MAX_WORKERS,
        prefix_pattern(pat_of(ps)), lit@ == prefix_lit(pat_of(ps)),
    ensures r matches Ok(keys) ==> keys_out(keys@, keys@.len() as int, pkeys(sv, ps, 0, n_p(sv) as int)),
{
    let np = c.np;
    let ntasks = workers;
    let k = lit.len();
    let lit_a = Arc::new(lit);
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut t: usize = 0;
    while t < ntasks
        invariant
            cols_ok(*c, sv), np == c.np, 1 <= ntasks <= MAX_WORKERS, t <= ntasks, tasks@.len() == t,
            prefix_pattern(pat_of(ps)), (*lit_a)@ == prefix_lit(pat_of(ps)), k == (*lit_a)@.len(),
            forall|i: int| 0 <= i < t ==> (#[trigger] tasks@[i]).pre()
                && tasks@[i].lo as int == split(np as int, ntasks as int, i) && tasks@[i].hi as int == split(np as int, ntasks as int, i + 1)
                && tasks@[i].sv@ == sv && tasks@[i].ps@ == ps,
        decreases ntasks - t,
    {
        let lo = split_exec(np, ntasks, t);
        let hi = split_exec(np, ntasks, t + 1);
        proof { lemma_split(np as int, ntasks as int, t as int, t as int + 1); }
        let task = PartTask {
            pkey: c.pkey, pname: c.pname, np, lit: lit_a.clone(), k, lo, hi, out: zeroed_i64(hi - lo),
            sv: Ghost(sv), ps: Ghost(ps),
        };
        tasks.push(task);
        t = t + 1;
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    // join the outputs in task order
    let ghost tasks_v = tasks@;
    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    proof { lemma_split(np as int, ntasks as int, 0, 0); }
    while i < ntasks
        invariant
            outs@.len() == ntasks, tasks_v.len() == ntasks, i <= ntasks, np == c.np, ntasks >= 1,
            forall|j: int| 0 <= j < ntasks ==> (#[trigger] tasks_v[j]).post(outs@[j])
                && tasks_v[j].lo as int == split(np as int, ntasks as int, j) && tasks_v[j].hi as int == split(np as int, ntasks as int, j + 1)
                && tasks_v[j].sv@ == sv && tasks_v[j].ps@ == ps,
            keys_out(keys@, keys@.len() as int, pkeys(sv, ps, 0, split(np as int, ntasks as int, i as int))),
        decreases ntasks - i,
    {
        let ghost lo = split(np as int, ntasks as int, i as int);
        let ghost hi = split(np as int, ntasks as int, i as int + 1);
        proof {
            lemma_split(np as int, ntasks as int, 0, i as int);
            lemma_split(np as int, ntasks as int, i as int, i as int + 1);
            assert(tasks_v[i as int].post(outs@[i as int]));
        }
        let out = &outs[i].0;
        let n = outs[i].1;
        let ghost base = keys@;
        let mut x: usize = 0;
        while x < n
            invariant
                x <= n, n == outs@[i as int].1, out@ == outs@[i as int].0@,
                keys_out(out@, n as int, pkeys(sv, ps, lo, hi)),
                keys_out(base, base.len() as int, pkeys(sv, ps, 0, lo)),
                keys@ == base + out@.subrange(0, x as int),
            decreases n - x,
        {
            keys.push(out[x]);
            x = x + 1;
            proof { assert(keys@ =~= base + out@.subrange(0, x as int)); }
        }
        proof {
            lemma_pkeys_concat(sv, ps, 0, lo, hi);
            let all = pkeys(sv, ps, 0, hi);
            assert forall|t: int| 0 <= t < keys@.len() implies #[trigger] keys@[t] as int == all[t] by {
                if t < base.len() {
                    assert(keys@[t] == base[t]);
                } else {
                    assert(keys@[t] == out@[t - base.len()]);
                }
            }
        }
        i = i + 1;
    }
    proof { lemma_split(np as int, ntasks as int, ntasks as int, ntasks as int); }
    Ok(keys)
}

// ------------------------------------------------------------------------------------------------ the general path

/// A copy of the bytes `[s, e)` of `b`.
pub fn copy_bytes(b: &[u8], s: usize, e: usize) -> (v: Vec<u8>)
    requires s <= e <= b@.len(),
    ensures v@ == b@.subrange(s as int, e as int),
{
    let mut v: Vec<u8> = Vec::with_capacity(e - s);
    let mut i = s;
    while i < e
        invariant s <= i <= e, e <= b@.len(), v@ == b@.subrange(s as int, i as int),
        decreases e - i,
    {
        v.push(b[i]);
        i = i + 1;
        proof { assert(v@ =~= b@.subrange(s as int, i as int)); }
    }
    v
}

/// The keys of all matching part rows by the verified `LIKE` on every name (serial); `Err(())` when some name's
/// `LIKE` raises.
pub fn part_keys_general(c: &Cols, pat: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<Vec<i64>, ()>)
    requires cols_ok(*c, sv), pat@ == pat_of(ps),
    ensures
        r is Err ==> !likes_ok(sv, ps),
        r matches Ok(keys) ==> likes_ok(sv, ps) && keys_out(keys@, keys@.len() as int, pkeys(sv, ps, 0, n_p(sv) as int)),
{
    let np = c.np;
    let pat_v = EVal::Text(copy_bytes(pat, 0, pat.len()));
    let mut esc_bytes: Vec<u8> = Vec::new();
    esc_bytes.push(92u8);
    let esc_v = EVal::Text(esc_bytes);
    proof {
        assert(pat@.subrange(0, pat@.len() as int) =~= pat@);
        assert(esc_bytes@ =~= esc());
    }
    let mut keys: Vec<i64> = Vec::new();
    let mut r: usize = 0;
    while r < np
        invariant
            cols_ok(*c, sv), np == c.np, r <= np,
            pat_v@ == Val::Text(pat_of(ps)), esc_v@ == Val::Text(esc()),
            forall|p: int| 0 <= p < r ==> like_ok(#[trigger] pname(sv, p), pat_of(ps)),
            keys_out(keys@, keys@.len() as int, pkeys(sv, ps, 0, r as int)),
        decreases np - r,
    {
        let (s, e) = text_range(c.pname, r, Ghost(pname_col(sv)), Ghost(n_p(sv) as int));
        let name = EVal::Text(copy_bytes(c.pname.bytes, s, e));
        let res = like_value_exec(&name, &pat_v, &esc_v);
        proof {
            assert(name@ == Val::Text(pname(sv, r as int)));
            assert(view_result(res) == like_res(pname(sv, r as int), pat_of(ps)));
            crate::agent::den_part::lemma_like_res(pname(sv, r as int), pat_of(ps));
            lemma_pkeys_step(sv, ps, 0, r as int);
        }
        match res {
            Ok(EVal::Bool(b)) => {
                if b {
                    keys.push(c.pkey[r]);
                    proof {
                        assert(keys@.len() as int == pkeys(sv, ps, 0, r as int + 1).len());
                    }
                }
            },
            Ok(_) => {
                proof { assert(false); }
            },
            Err(_) => {
                return Err(());
            },
        }
        r = r + 1;
    }
    Ok(keys)
}

} // verus!
