//! The passes of a call, each split into tasks over consecutive row ranges (`split_at`), and their merges.
//!
//! - `tag_pass`: the nation tags (2 bits each) of the suppliers or of the customers, and whether their keys are
//!   positional;
//! - `scan_pass`: the lineitem scan (`scan::ScanTask`), whose per-range accumulators add up in range order
//!   (`merge_acc`); an absolute sum beyond `i128::MAX`, in a task or in the merge, gives `Totals::Over`;
//! - `general_pass`: the serial scan for data whose supplier or customer keys are not positional (every key is
//!   looked up by a linear search; correct for any data, used only when the fast path's checks fail).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::link::expr::i128_max;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::lines::*;
use crate::agent::scan::*;
use crate::agent::tags::*;
use crate::agent::common::bits::*;

verus! {

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

// ------------------------------------------------------------------------------------------------ supplier and customer tags

/// The nation tags of a keyed table's rows (2 bits each; one task per range of 32-row words; used for the suppliers
/// and the customers) and whether its keys are `base + r`.
pub fn tag_pass(cols: KeyCols, nation: NationCols, ntag: Arc<Vec<u8>>, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<(Vec<u64>, bool), WorkerFailure>)
    requires
        key_cols_ok(cols), nation_cols_ok(nation, sv), ntags_ok(ntag@, sv, ps), 1 <= workers <= MAX_WORKERS,
        cols.n < usize::MAX / 2,
    ensures r matches Ok((words, pos)) ==> tags_ok(words@, cols.nats@, sv, ps, cols.n as int) && (pos ==> positional(cols.keys@, cols.base as int)),
{
    let nw = cols.n / 32 + 1;
    let cap: usize = if workers > 32 { 32 } else { workers };
    let nt: usize = if nw / 4096 + 1 < cap { nw / 4096 + 1 } else { cap };
    let mut tasks: Vec<TagTask> = Vec::new();
    let mut k: usize = 0;
    while k < nt
        invariant
            key_cols_ok(cols), nation_cols_ok(nation, sv), ntags_ok(ntag@, sv, ps), cols.n < usize::MAX / 2,
            nw == cols.n / 32 + 1, 1 <= nt <= MAX_WORKERS, k <= nt, tasks@.len() == k,
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre() && tasks@[t].cols == cols
                && tasks@[t].sv@ == sv && tasks@[t].ps@ == ps
                && tasks@[t].wl == split_at(nw as int, nt as int, t) && tasks@[t].wh == split_at(nw as int, nt as int, t + 1),
        decreases nt - k,
    {
        proof { lemma_split(nw as int, nt as int, k as int); }
        let wl = k * (nw / nt) + if k < nw % nt { k } else { nw % nt };
        let wh = wl + nw / nt + if k < nw % nt { 1usize } else { 0usize };
        let task = TagTask { cols, nation, ntag: ntag.clone(), wl, wh, out: filled(wh - wl, 0u64), sv: Ghost(sv), ps: Ghost(ps) };
        tasks.push(task);
        k = k + 1;
    }
    let ghost tasks0 = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let ghost outs0 = outs@;
    proof {
        assert forall|u: int| 0 <= u < nt implies tags_range_ok(#[trigger] outs0[u].0@, outs0[u].1, cols.keys@, cols.nats@, sv, ps, cols.base as int,
            split_at(nw as int, nt as int, u), split_at(nw as int, nt as int, u + 1)) by {
            assert(tasks0[u].post(outs0[u]));
        }
    }
    let mut outs = outs;
    let mut words: Vec<u64> = Vec::new();
    let mut pos = true;
    let mut t: usize = 0;
    proof { lemma_split(nw as int, nt as int, 0); }
    while t < nt
        invariant
            1 <= nt, t <= nt, outs0.len() == nt, nw == cols.n / 32 + 1, key_cols_ok(cols),
            outs@ == outs0.subrange(t as int, nt as int),
            words@.len() == split_at(nw as int, nt as int, t as int),
            forall|u: int| 0 <= u < nt ==> tags_range_ok(#[trigger] outs0[u].0@, outs0[u].1, cols.keys@, cols.nats@, sv, ps, cols.base as int,
                split_at(nw as int, nt as int, u), split_at(nw as int, nt as int, u + 1)),
            forall|r: int| 0 <= r < 32 * split_at(nw as int, nt as int, t as int) && r < cols.n ==>
                #[trigger] field2(words@[r / 32], (r % 32) as u64) as int == nat_tag(sv, ps, cols.nats@[r]),
            pos ==> forall|r: int| 0 <= r < 32 * split_at(nw as int, nt as int, t as int) && r < cols.n ==>
                #[trigger] cols.keys@[r] as int == cols.base + r,
        decreases nt - t,
    {
        proof { lemma_split(nw as int, nt as int, t as int); }
        let ghost (wl, wh) = (split_at(nw as int, nt as int, t as int), split_at(nw as int, nt as int, t + 1));
        let (mut v, p) = outs.remove(0);
        assert((v@, p) == (outs0[t as int].0@, outs0[t as int].1));
        let ghost words0 = words@;
        let ghost v0 = v@;
        words.append(&mut v);
        proof {
            assert(words@ == words0 + v0);
            assert forall|r: int| 0 <= r < 32 * wh && r < cols.n implies #[trigger] field2(words@[r / 32], (r % 32) as u64) as int == nat_tag(sv, ps, cols.nats@[r]) by {
                if r < 32 * wl {
                    assert(words@[r / 32] == words0[r / 32]);
                } else {
                    assert(words@[r / 32] == v0[r / 32 - wl]);
                }
            }
            if pos && p {
                assert forall|r: int| 0 <= r < 32 * wh && r < cols.n implies #[trigger] cols.keys@[r] as int == cols.base + r by {
                    if r >= 32 * wl {
                        assert(cols.keys@[r] as int == cols.base + r);
                    }
                }
            }
        }
        pos = pos && p;
        t = t + 1;
        proof {
            assert(outs@ =~= outs0.subrange(t as int, nt as int));
        }
    }
    proof {
        assert forall|r: int| 0 <= r < cols.n implies #[trigger] field2(words@[r / 32], (r % 32) as u64) as int == nat_tag(sv, ps, cols.nats@[r]) by {
            assert(r < 32 * nw);
        }
        if pos {
            assert forall|r: int| 0 <= r < cols.keys@.len() implies #[trigger] cols.keys@[r] as int == cols.base + r by {
                assert(r < 32 * nw);
            }
        }
    }
    Ok((words, pos))
}

// ------------------------------------------------------------------------------------------------ the scan

/// The scan's totals: the accumulators of all lineitem rows, or a group whose absolute sum exceeds `i128::MAX`.
pub enum Totals {
    Sums(Acc),
    Over(usize),
}

pub open spec fn totals_ok(r: Totals, sv: StoresView, ps: Seq<Literal>) -> bool {
    match r {
        Totals::Sums(a) => acc_ok(a, sv, ps, 0, n_l(sv)),
        Totals::Over(g) => g < 4 && lsum(sv, ps, g as int, 2, 0, n_l(sv)) > i128_max(),
    }
}

/// An absolute sum over part of `lo..hi` bounds the one over `0..n`.
pub proof fn lemma_abs_part(sv: StoresView, ps: Seq<Literal>, g: int, lo: int, x: int, n: int)
    requires 0 <= lo <= x <= n,
    ensures lsum(sv, ps, g, 2, 0, n) >= lsum(sv, ps, g, 2, lo, x),
{
    lemma_lsum_split(sv, ps, g, 2, 0, lo, n);
    lemma_lsum_split(sv, ps, g, 2, lo, x, n);
    lemma_lsum_bounds(sv, ps, g, 0, lo);
    lemma_lsum_bounds(sv, ps, g, x, n);
}

/// Add the accumulators of rows `mid..hi` to those of `0..mid`; `Some(g)` when group `g`'s absolute sum over `0..hi`
/// exceeds `i128::MAX`.
pub fn merge_acc(total: &mut Acc, part: &Acc, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(mid): Ghost<int>,
    Ghost(hi): Ghost<int>) -> (over: Option<usize>)
    requires
        0 <= mid <= hi <= usize::MAX,
        acc_ok(*old(total), sv, ps, 0, mid),
        acc_ok(*part, sv, ps, mid, hi),
    ensures
        over is None ==> acc_ok(*final(total), sv, ps, 0, hi),
        over matches Some(g) ==> g < 4 && lsum(sv, ps, g as int, 2, 0, hi) > i128_max(),
{
    let mut g: usize = 0;
    while g < 4
        invariant
            0 <= mid <= hi <= usize::MAX, g <= 4,
            acc_ok(*part, sv, ps, mid, hi),
            total.cnt@.len() == 4 && total.sum@.len() == 4 && total.abs@.len() == 4,
            forall|h: int| #![trigger total.cnt@[h]] #![trigger total.sum@[h]] #![trigger total.abs@[h]] 0 <= h < 4 ==> {
                &&& total.cnt@[h] as int == lsum(sv, ps, h, 0, 0, if h < g { hi } else { mid })
                &&& total.sum@[h] as int == lsum(sv, ps, h, 1, 0, if h < g { hi } else { mid })
                &&& total.abs@[h] as int == lsum(sv, ps, h, 2, 0, if h < g { hi } else { mid })
            },
        decreases 4 - g,
    {
        proof {
            lemma_lsum_split(sv, ps, g as int, 0, 0, mid, hi);
            lemma_lsum_split(sv, ps, g as int, 1, 0, mid, hi);
            lemma_lsum_split(sv, ps, g as int, 2, 0, mid, hi);
            lemma_lsum_bounds(sv, ps, g as int, 0, mid);
            lemma_lsum_bounds(sv, ps, g as int, mid, hi);
            lemma_lsum_bounds(sv, ps, g as int, 0, hi);
            lemma_lsum_count(sv, ps, g as int, 0, hi);
        }
        let a = total.abs[g];
        let b = part.abs[g];
        assert(a as int == lsum(sv, ps, g as int, 2, 0, mid) && b as int == lsum(sv, ps, g as int, 2, mid, hi));
        assert(part.sum@[g as int] as int == lsum(sv, ps, g as int, 1, mid, hi));
        assert(part.cnt@[g as int] as int == lsum(sv, ps, g as int, 0, mid, hi));
        assert(total.sum@[g as int] as int == lsum(sv, ps, g as int, 1, 0, mid));
        assert(total.cnt@[g as int] as int == lsum(sv, ps, g as int, 0, 0, mid));
        if a > i128::MAX - b {
            return Some(g);
        }
        let ghost t0 = *total;
        let s = total.sum[g] + part.sum[g];
        let n = total.cnt[g] + part.cnt[g];
        total.abs[g] = a + b;
        total.sum[g] = s;
        total.cnt[g] = n;
        proof {
            assert forall|h: int| #![trigger total.cnt@[h]] #![trigger total.sum@[h]] #![trigger total.abs@[h]] 0 <= h < 4 implies {
                &&& total.cnt@[h] as int == lsum(sv, ps, h, 0, 0, if h < g + 1 { hi } else { mid })
                &&& total.sum@[h] as int == lsum(sv, ps, h, 1, 0, if h < g + 1 { hi } else { mid })
                &&& total.abs@[h] as int == lsum(sv, ps, h, 2, 0, if h < g + 1 { hi } else { mid })
            } by {
                if h != g {
                    assert(total.cnt@[h] == t0.cnt@[h] && total.sum@[h] == t0.sum@[h] && total.abs@[h] == t0.abs@[h]);
                }
            }
        }
        g = g + 1;
    }
    None
}

/// The lineitem scan, one task per range (`workers` tasks), and the merge of their accumulators.
pub fn scan_pass(c: ScanCols, swords: Arc<Vec<u64>>, cwords: Arc<Vec<u64>>, workers: usize,
    dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Totals, WorkerFailure>)
    requires scan_inputs_ok(c, swords@, cwords@, sv, ps), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(t) ==> totals_ok(t, sv, ps),
{
    let n = c.nl;
    // at most one task per physical core: two tasks on the hyperthreads of a core run slower than one (measured)
    let nt: usize = if workers > 32 { 32 } else { workers };
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut k: usize = 0;
    while k < nt
        invariant
            scan_inputs_ok(c, swords@, cwords@, sv, ps), n == c.nl,
            1 <= nt <= MAX_WORKERS, k <= nt, tasks@.len() == k,
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre() && tasks@[t].sv@ == sv && tasks@[t].ps@ == ps
                && tasks@[t].lo == split_at(n as int, nt as int, t) && tasks@[t].hi == split_at(n as int, nt as int, t + 1),
        decreases nt - k,
    {
        proof { lemma_split(n as int, nt as int, k as int); }
        let lo = k * (n / nt) + if k < n % nt { k } else { n % nt };
        let hi = lo + n / nt + if k < n % nt { 1usize } else { 0usize };
        let task = ScanTask {
            cols: c, swords: swords.clone(), cwords: cwords.clone(), lo, hi, bufs: bufs_new(), acc: acc_zero(), sv: Ghost(sv), ps: Ghost(ps),
        };
        tasks.push(task);
        k = k + 1;
    }
    let ghost tasks0 = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let ghost outs0 = outs@;
    proof {
        assert forall|u: int| 0 <= u < nt implies scan_out_ok(#[trigger] outs0[u], sv, ps,
            split_at(n as int, nt as int, u), split_at(n as int, nt as int, u + 1)) by {
            assert(tasks0[u].post(outs0[u]));
        }
    }
    let mut outs = outs;
    let mut total = acc_zero();
    proof { lemma_acc_empty(total, sv, ps, 0); }
    let mut t: usize = 0;
    proof { lemma_split(n as int, nt as int, 0); }
    while t < nt
        invariant
            scan_inputs_ok(c, swords@, cwords@, sv, ps), n == c.nl,
            1 <= nt, t <= nt, outs0.len() == nt,
            outs@ == outs0.subrange(t as int, nt as int),
            forall|u: int| 0 <= u < nt ==> scan_out_ok(#[trigger] outs0[u], sv, ps,
                split_at(n as int, nt as int, u), split_at(n as int, nt as int, u + 1)),
            acc_ok(total, sv, ps, 0, split_at(n as int, nt as int, t as int)),
        decreases nt - t,
    {
        proof { lemma_split(n as int, nt as int, t as int); }
        let ghost (lo, hi) = (split_at(n as int, nt as int, t as int), split_at(n as int, nt as int, t + 1));
        let o = outs.remove(0);
        assert(o == outs0[t as int]);
        match o.over {
            Some(g) => {
                proof {
                    let x = choose|x: int| lo <= x <= hi && lsum(sv, ps, g as int, 2, lo, x) > i128_max();
                    lemma_abs_part(sv, ps, g as int, lo, x, n as int);
                }
                return Ok(Totals::Over(g));
            },
            None => {},
        }
        match merge_acc(&mut total, &o.acc, Ghost(sv), Ghost(ps), Ghost(lo), Ghost(hi)) {
            Some(g) => {
                proof { lemma_abs_part(sv, ps, g as int, 0, hi, n as int); }
                return Ok(Totals::Over(g));
            },
            None => {},
        }
        t = t + 1;
        proof {
            assert(outs@ =~= outs0.subrange(t as int, nt as int));
        }
    }
    Ok(Totals::Sums(total))
}

// ------------------------------------------------------------------------------------------------ the general path

/// The columns of the general path: the scan's, the supplier and customer keys and nation keys.
#[derive(Clone, Copy)]
pub struct GenCols {
    pub cols: ScanCols,
    pub skey: &'static [i64],
    pub snat: &'static [i64],
    pub ckey: &'static [i64],
    pub cnat: &'static [i64],
}

pub open spec fn gen_cols_ok(g: GenCols, sv: StoresView) -> bool {
    &&& line_cols_ok(g.cols, sv)
    &&& g.skey@ == sk(sv) && g.snat@ == sn(sv) && g.ckey@ == ck(sv) && g.cnat@ == cn(sv)
    &&& keys_unique(sk(sv)) && keys_unique(ck(sv))
}

/// The row of key `k` in a key column (its length when there is none), by a linear search.
pub fn find_key(keys: &'static [i64], n: usize, k: i64) -> (r: usize)
    requires keys@.len() == n,
    ensures r <= n, r < n ==> keys@[r as int] == k, r == n ==> !has_key(keys@, k),
{
    let mut j: usize = 0;
    while j < n
        invariant keys@.len() == n, j <= n, forall|q: int| 0 <= q < j ==> keys@[q] != k,
        decreases n - j,
    {
        if keys[j] == k {
            return j;
        }
        j = j + 1;
    }
    n
}

/// Lineitem row `i`: whether it qualifies, and its group (every key looked up by search).
fn line_group_general(g: &GenCols, nation: &NationCols, ntag: &Vec<u8>, i: usize, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (r: (bool, usize))
    requires gen_cols_ok(*g, sv), nation_cols_ok(*nation, sv), ntags_ok(ntag@, sv, ps), i < g.cols.nl,
    ensures r.0 == line_qual(sv, ps, i as int), r.0 ==> r.1 < 4 && r.1 as int == line_grp(sv, ps, i as int),
{
    let ghost l = i as int;
    let c = g.cols;
    let s = find_key(g.skey, c.ns, c.lsupp[i]);
    if s == c.ns {
        return (false, 0);
    }
    proof {
        lemma_key_row(sk(sv), lsk(sv)[l]);
        assert(l_supp(sv, l) == s);
    }
    let st = nat_tag_of(nation, ntag, g.snat[s], Ghost(sv), Ghost(ps));
    let j = order_row(&c, c.lokey[i], Ghost(sv));
    if j == c.no {
        return (false, 0);
    }
    proof {
        lemma_key_row(ok(sv), lok(sv)[l]);
        assert(has_key(ok(sv), lok(sv)[l]));
        assert(l_ord(sv, l) == j);
    }
    let cr = find_key(g.ckey, c.nc, c.ocust[j]);
    if cr == c.nc {
        return (false, 0);
    }
    proof {
        lemma_key_row(ck(sv), oc(sv)[j as int]);
        assert(l_cust(sv, l) == cr);
    }
    let ct = nat_tag_of(nation, ntag, g.cnat[cr], Ghost(sv), Ghost(ps));
    let d = c.lship[i];
    let q = d >= 9131 && d <= 9861 && ((st % 2 == 1 && ct >= 2) || (st >= 2 && ct % 2 == 1));
    let base: usize = if st % 2 == 1 && ct >= 2 { 0 } else { 2 };
    (q, base + if d >= 9496 { 1usize } else { 0usize })
}

/// The scan of all lineitem rows, serial, with general key lookups.
pub fn general_pass(g: &GenCols, nation: &NationCols, ntag: &Vec<u8>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Totals)
    requires gen_cols_ok(*g, sv), nation_cols_ok(*nation, sv), ntags_ok(ntag@, sv, ps),
    ensures totals_ok(r, sv, ps),
{
    let c = g.cols;
    let mut acc = acc_zero();
    proof { lemma_acc_empty(acc, sv, ps, 0); }
    let mut i: usize = 0;
    while i < c.nl
        invariant
            gen_cols_ok(*g, sv), nation_cols_ok(*nation, sv), ntags_ok(ntag@, sv, ps), c == g.cols,
            i <= c.nl, acc_ok(acc, sv, ps, 0, i as int),
        decreases c.nl - i,
    {
        let (q, grp) = line_group_general(g, nation, ntag, i, Ghost(sv), Ghost(ps));
        match acc_add(&mut acc, &c, q, grp, i, Ghost(sv), Ghost(ps), Ghost(0)) {
            Some(h) => {
                proof { lemma_abs_part(sv, ps, h as int, 0, i + 1, n_l(sv)); }
                return Totals::Over(h);
            },
            None => {},
        }
        i = i + 1;
    }
    Totals::Sums(acc)
}

} // verus!
