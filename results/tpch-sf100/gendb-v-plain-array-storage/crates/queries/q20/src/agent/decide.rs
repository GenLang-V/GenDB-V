//! The decisions of the partsupp rows (`DecideTask`, `decide_pass`), one decide task per part-key bucket `u`
//! (`bucket`): it takes bucket `u` of every scan task's partsupp rows as local slots (the matching partsupp rows of
//! the bucket, `bucket_rows`, `gather_slots`), checks that their part keys ascend (dbgen's order; otherwise the task
//! reports failure and the query takes its general path), builds a directory over their key groups
//! (`slots::build_dir`), sums bucket `u` of every scan task's lineitem records into the first local slot of each
//! record's key pair (`agg_records`), and decides each slot from its pair's first slot (`decide_slots`): `ps_ok` of
//! its row. The buckets are small, so a task's slots and directory stay in cache while its records stream by.
//!
//! The records of bucket `u` are the records for the bucket's key set `bkeys(keys, bm, u)`, so the totals are those
//! of `agg` for that key set; a key pair lies in one bucket, and every lineitem hit of a slot's pair is in the
//! slot's bucket (`agg::lemma_first_totals`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::den_li::{sizes_ok, lemma_ltotals_bounds};
use crate::agent::keys::KEY_LIMIT;
use crate::agent::pspass::*;
use crate::agent::linepass::*;
use crate::agent::scan::*;
use crate::agent::bucket::*;
use crate::agent::common::buckets::*;
use crate::agent::slots::*;
use crate::agent::agg::*;
use crate::agent::common::selection::*;
use crate::agent::common::split::*;
use crate::agent::common::bigzero::{zeroed_i64, zeroed_i128, zeroed_u64, zeroed_usize, zeroed_bool};

verus! {

/// The first `n` slots are the partsupp rows `qs`, in order.
pub open spec fn slots_rows(spk: Seq<i64>, ssk: Seq<i64>, saq: Seq<i64>, n: int, sv: StoresView, qs: Seq<int>) -> bool {
    &&& n == qs.len() && spk.len() >= n && ssk.len() >= n && saq.len() >= n
    &&& forall|s: int| 0 <= s < n ==> #[trigger] spk[s] == pspk(sv)[qs[s]] && ssk[s] == pssk(sv)[qs[s]] && saq[s] == psaq(sv)[qs[s]]
}

/// One more slot: writing row `q`'s triple at slot `k` extends the slots by `q`.
proof fn lemma_slots_push(s0: Seq<i64>, s1: Seq<i64>, s2: Seq<i64>, k: int, sv: StoresView, qs: Seq<int>, q: int,
    t0: Seq<i64>, t1: Seq<i64>, t2: Seq<i64>)
    requires
        slots_rows(s0, s1, s2, k, sv, qs), k < s0.len(), k < s1.len(), k < s2.len(),
        t0 == s0.update(k, pspk(sv)[q]), t1 == s1.update(k, pssk(sv)[q]), t2 == s2.update(k, psaq(sv)[q]),
    ensures slots_rows(t0, t1, t2, k + 1, sv, qs.push(q)),
{
    let qs2 = qs.push(q);
    assert forall|s: int| 0 <= s < k + 1 implies #[trigger] t0[s] == pspk(sv)[qs2[s]] && t1[s] == pssk(sv)[qs2[s]]
        && t2[s] == psaq(sv)[qs2[s]] by {
        if s < k {
            assert(qs2[s] == qs[s]);
            assert(t0[s] == s0[s] && t1[s] == s1[s] && t2[s] == s2[s]);
            assert(s0[s] == pspk(sv)[qs[s]]);
        } else {
            assert(qs2[s] == q);
        }
    }
    assert(qs2.len() == k + 1);
    assert(t0.len() >= k + 1 && t1.len() >= k + 1 && t2.len() >= k + 1);
    assert(forall|s: int| 0 <= s < k + 1 ==> #[trigger] t0[s] == pspk(sv)[qs2[s]] && t1[s] == pssk(sv)[qs2[s]]
        && t2[s] == psaq(sv)[qs2[s]]);
}

/// The partsupp rows of bucket `u`: those of a matching part whose key lies in the bucket, ascending.
pub open spec fn bucket_rows(sv: StoresView, ps: Seq<Literal>, bm: u64, u: int) -> Seq<int> {
    bqrows(sv, ps, bm, u, 0, n_ps(sv) as int)
}

/// Every scan task's buckets fit their regions.
pub open spec fn all_fit(outs: Seq<ScanOut>) -> bool { forall|t: int| 0 <= t < outs.len() ==> #[trigger] outs[t].fit }

/// The local slots: bucket `u` of every scan task's partsupp rows, in task order (`None` when more than `cap`).
fn gather_slots(outs: &Vec<ScanOut>, nt: usize, nb: usize, bm: u64, u: usize, spk: &mut Vec<i64>, ssk: &mut Vec<i64>,
    saq: &mut Vec<i64>, cap: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(keys): Ghost<Seq<int>>,
    Ghost(dlo): Ghost<int>, Ghost(dhi): Ghost<int>) -> (r: Option<usize>)
    requires
        scan_all(outs@, nt as int, sv, ps, keys, dlo, dhi, nb as int, bm), all_fit(outs@), u < nb,
        old(spk)@.len() >= cap, old(ssk)@.len() >= cap, old(saq)@.len() >= cap,
    ensures
        final(spk)@.len() == old(spk)@.len(), final(ssk)@.len() == old(ssk)@.len(), final(saq)@.len() == old(saq)@.len(),
        r matches Some(n) ==> n <= cap && slots_rows(final(spk)@, final(ssk)@, final(saq)@, n as int, sv,
            bucket_rows(sv, ps, bm, u as int)),
    no_unwind
{
    let ghost nps = n_ps(sv) as int;
    let ghost p = and_pred(inp(sv, ps), kbucket(pspk(sv), bm, u as int));
    let mut k: usize = 0;
    let mut t: usize = 0;
    proof {
        lemma_split(nps, nt as int, 0, nt as int);
        assert(bqrows(sv, ps, bm, u as int, 0, 0) =~= Seq::<int>::empty());
    }
    while t < nt
        invariant
            scan_all(outs@, nt as int, sv, ps, keys, dlo, dhi, nb as int, bm), all_fit(outs@), u < nb, t <= nt,
            nps == n_ps(sv) as int, p == and_pred(inp(sv, ps), kbucket(pspk(sv), bm, u as int)),
            spk@.len() == old(spk)@.len(), ssk@.len() == old(ssk)@.len(), saq@.len() == old(saq)@.len(),
            spk@.len() >= cap, ssk@.len() >= cap, saq@.len() >= cap, k <= cap,
            slots_rows(spk@, ssk@, saq@, k as int, sv, bqrows(sv, ps, bm, u as int, 0, ps_lo(sv, nt as int, t as int))),
        decreases nt - t,
    {
        let ghost lo = ps_lo(sv, nt as int, t as int);
        let ghost hi = ps_lo(sv, nt as int, t as int + 1);
        proof {
            lemma_split(nps, nt as int, t as int, t as int + 1);
            lemma_split(nps, nt as int, 0, t as int);
            assert(scan_ok(outs@[t as int], nt as int, t as int, sv, ps, keys, dlo, dhi, nb as int, bm));
            assert(outs@[t as int].fit);
        }
        let o = &outs[t];
        let m = o.bnp[u];
        let blen = o.bps.len();
        proof {
            assert(trip_at(o.bps@, 3 * o.cp * u, m as int, pspk(sv), pssk(sv), ps_c(sv), bqrows(sv, ps, bm, u as int, lo, hi)));
            lemma_regions(o.cp as int, u as int, u as int, nb as int);
        }
        let base = 3 * o.cp * u;
        let ghost before = bqrows(sv, ps, bm, u as int, 0, lo);
        let ghost qb = bqrows(sv, ps, bm, u as int, lo, hi);
        let mut x: usize = 0;
        while x < m
            invariant
                x <= m, blen == o.bps@.len(), base as int == 3 * o.cp * u,
                trip_at(o.bps@, base as int, m as int, pspk(sv), pssk(sv), ps_c(sv), qb),
                spk@.len() == old(spk)@.len(), ssk@.len() == old(ssk)@.len(), saq@.len() == old(saq)@.len(),
                spk@.len() >= cap, ssk@.len() >= cap, saq@.len() >= cap, k <= cap,
                k == before.len() + x,
                slots_rows(spk@, ssk@, saq@, k as int, sv, before + qb.take(x as int)),
            decreases m - x,
        {
            if k >= cap {
                return None;
            }
            let ghost (s0, s1, s2) = (spk@, ssk@, saq@);
            assert(base + 3 * x + 2 < blen);
            spk[k] = o.bps[base + 3 * x];
            ssk[k] = o.bps[base + 3 * x + 1];
            saq[k] = o.bps[base + 3 * x + 2];
            proof {
                let q = qb[x as int];
                assert(o.bps@[base + 3 * x] == pspk(sv)[q] && o.bps@[base + 3 * x + 1] == pssk(sv)[q]
                    && o.bps@[base + 3 * x + 2] as int == psaq(sv)[q] as int);
                let bs = before + qb.take(x as int);
                assert(before + qb.take(x as int + 1) =~= bs.push(q));
                lemma_slots_push(s0, s1, s2, k as int, sv, bs, q, spk@, ssk@, saq@);
            }
            k = k + 1;
            x = x + 1;
        }
        proof {
            assert(qb.take(m as int) =~= qb);
            lemma_range_filter_concat(0, lo, hi, p);
        }
        t = t + 1;
    }
    proof { lemma_split(nps, nt as int, nt as int, nt as int); }
    Some(k)
}

/// Whether the first `n` part keys ascend (`no_unwind`).
fn check_ascending(spk: &Vec<i64>, n: usize) -> (r: bool)
    requires spk@.len() >= n,
    ensures r ==> ascending(spk@, n as int),
    no_unwind
{
    let mut s: usize = 1;
    while s < n
        invariant spk@.len() >= n, 1 <= s, ascending(spk@, if s <= n { s as int } else { n as int }),
        decreases n - s,
    {
        if spk[s - 1] > spk[s] {
            return false;
        }
        proof {
            assert forall|u: int, w: int| 0 <= u < w < s + 1 && w < n implies #[trigger] spk@[u] <= #[trigger] spk@[w] by {
                if w == s as int && u < s - 1 {
                    assert(spk@[u] <= spk@[s - 1]);
                }
            }
        }
        s = s + 1;
    }
    true
}

/// The totals over `[0, lo)` and the sums over the recorded rows of `[lo, hi)` make the totals over `[0, hi)`.
proof fn lemma_totals_step(sv: StoresView, dlo: int, dhi: int, keys: Seq<int>, spk: Seq<i64>, ssk: Seq<i64>, n: int, i: int, lo: int, hi: int)
    requires 0 <= lo <= hi,
    ensures
        acc_of(sv, dlo, dhi, keys, spk, ssk, n, i, lo) + seq_sum(lrecs(sv, dlo, dhi, keys, lo, hi), qterm(sv, spk, ssk, n, i))
            == acc_of(sv, dlo, dhi, keys, spk, ssk, n, i, hi),
        cnt_of(sv, dlo, dhi, keys, spk, ssk, n, i, lo) + seq_sum(lrecs(sv, dlo, dhi, keys, lo, hi), cterm(sv, spk, ssk, n, i))
            == cnt_of(sv, dlo, dhi, keys, spk, ssk, n, i, hi),
{
    let f = lrec(sv, dlo, dhi, keys);
    lemma_sum_range_filter(lo, hi, f, qterm(sv, spk, ssk, n, i));
    lemma_sum_range_filter(lo, hi, f, cterm(sv, spk, ssk, n, i));
    lemma_range_sum_split(0, lo, hi, guard(f, qterm(sv, spk, ssk, n, i)));
    lemma_range_sum_split(0, lo, hi, guard(f, cterm(sv, spk, ssk, n, i)));
}

/// The slot totals after the records `rs[..x]` of a task: each slot's sum and count over `[0, lo)` plus its terms
/// over those records, within the count bounds.
pub open spec fn totals_at(acc: Seq<i128>, cnt: Seq<u64>, m: int, sv: StoresView, dlo: int, dhi: int, keys: Seq<int>,
    spk: Seq<i64>, ssk: Seq<i64>, sn: int, lo: int, rs: Seq<int>, x: int) -> bool {
    &&& acc.len() >= m && cnt.len() >= m
    &&& forall|i: int| 0 <= i < m ==> #[trigger] acc[i] as int == acc_of(sv, dlo, dhi, keys, spk, ssk, sn, i, lo) + seq_sum(rs.take(x), qterm(sv, spk, ssk, sn, i))
        && cnt[i] as int == cnt_of(sv, dlo, dhi, keys, spk, ssk, sn, i, lo) + seq_sum(rs.take(x), cterm(sv, spk, ssk, sn, i))
        && cnt[i] <= lo + x
        && -qmax() * cnt[i] <= acc[i] <= qmax() * cnt[i]
}

/// One record `rs[x]` (row `l`) added to its first slot `s0`.
proof fn lemma_record_step(acc0: Seq<i128>, cnt0: Seq<u64>, acc1: Seq<i128>, cnt1: Seq<u64>, m: int, sv: StoresView,
    dlo: int, dhi: int, keys: Seq<int>, spk: Seq<i64>, ssk: Seq<i64>, sn: int, lo: int, rs: Seq<int>, x: int, s0: int)
    requires
        totals_at(acc0, cnt0, m, sv, dlo, dhi, keys, spk, ssk, sn, lo, rs, x), 0 <= x < rs.len(), 0 <= s0 < m,
        first_slot(spk, ssk, sn, lpk(sv)[rs[x]] as int, lsk(sv)[rs[x]] as int, s0),
        acc1 == acc0.update(s0, acc1[s0]), cnt1 == cnt0.update(s0, cnt1[s0]),
        acc1[s0] as int == acc0[s0] as int + lqt(sv)[rs[x]] as int, cnt1[s0] as int == cnt0[s0] as int + 1,
        -qmax() * (cnt0[s0] + 1) <= acc0[s0] + lqt(sv)[rs[x]] <= qmax() * (cnt0[s0] + 1),
    ensures totals_at(acc1, cnt1, m, sv, dlo, dhi, keys, spk, ssk, sn, lo, rs, x + 1),
{
    let l = rs[x];
    let tk = rs.take(x);
    assert(rs.take(x + 1) =~= tk.push(l));
    assert forall|i: int| 0 <= i < m implies #[trigger] acc1[i] as int == acc_of(sv, dlo, dhi, keys, spk, ssk, sn, i, lo) + seq_sum(rs.take(x + 1), qterm(sv, spk, ssk, sn, i))
        && cnt1[i] as int == cnt_of(sv, dlo, dhi, keys, spk, ssk, sn, i, lo) + seq_sum(rs.take(x + 1), cterm(sv, spk, ssk, sn, i))
        && cnt1[i] <= lo + x + 1
        && -qmax() * cnt1[i] <= acc1[i] <= qmax() * cnt1[i] by {
        lemma_seq_sum_push(tk, l, qterm(sv, spk, ssk, sn, i));
        lemma_seq_sum_push(tk, l, cterm(sv, spk, ssk, sn, i));
        lemma_record_terms(sv, spk, ssk, sn, l, s0, i);
        if i != s0 {
            assert(acc1[i] == acc0[i] && cnt1[i] == cnt0[i]);
        }
    }
}

/// One record `rs[x]` (row `l`) whose pair has no slot: nothing changes.
proof fn lemma_record_skip(acc: Seq<i128>, cnt: Seq<u64>, m: int, sv: StoresView,
    dlo: int, dhi: int, keys: Seq<int>, spk: Seq<i64>, ssk: Seq<i64>, sn: int, lo: int, rs: Seq<int>, x: int)
    requires
        totals_at(acc, cnt, m, sv, dlo, dhi, keys, spk, ssk, sn, lo, rs, x), 0 <= x < rs.len(),
        !has_slot(spk, ssk, sn, lpk(sv)[rs[x]] as int, lsk(sv)[rs[x]] as int),
    ensures totals_at(acc, cnt, m, sv, dlo, dhi, keys, spk, ssk, sn, lo, rs, x + 1),
{
    let l = rs[x];
    let tk = rs.take(x);
    assert(rs.take(x + 1) =~= tk.push(l));
    assert forall|i: int| 0 <= i < m implies #[trigger] acc[i] as int == acc_of(sv, dlo, dhi, keys, spk, ssk, sn, i, lo) + seq_sum(rs.take(x + 1), qterm(sv, spk, ssk, sn, i))
        && cnt[i] as int == cnt_of(sv, dlo, dhi, keys, spk, ssk, sn, i, lo) + seq_sum(rs.take(x + 1), cterm(sv, spk, ssk, sn, i))
        && cnt[i] <= lo + x + 1
        && -qmax() * cnt[i] <= acc[i] <= qmax() * cnt[i] by {
        lemma_seq_sum_push(tk, l, qterm(sv, spk, ssk, sn, i));
        lemma_seq_sum_push(tk, l, cterm(sv, spk, ssk, sn, i));
        if first_slot(spk, ssk, sn, lpk(sv)[l] as int, lsk(sv)[l] as int, i) {
            assert(spk[i] as int == lpk(sv)[l] as int && ssk[i] as int == lsk(sv)[l] as int);
        }
    }
}

/// The totals of every local slot over bucket `u` of the records of all scan tasks (`no_unwind`): the totals for
/// the bucket's key set `bks`.
fn agg_records(outs: &Vec<ScanOut>, nt: usize, nb: usize, bm: u64, u: usize, sl: &Slots, klo: i64, khi: i64, acc: &mut Vec<i128>,
    cnt: &mut Vec<u64>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(keys): Ghost<Seq<int>>,
    Ghost(bks): Ghost<Seq<int>>, Ghost(dlo): Ghost<int>, Ghost(dhi): Ghost<int>)
    requires
        scan_all(outs@, nt as int, sv, ps, keys, dlo, dhi, nb as int, bm), all_fit(outs@), u < nb, bks == bkeys(keys, bm, u as int),
        domains_ok(sv), sizes_ok(sv), slots_dir(*sl),
        sl.n > 0, klo == sl.spk@[0], khi == sl.spk@[sl.n - 1],
        old(acc)@.len() >= sl.n, old(cnt)@.len() >= sl.n,
    ensures
        final(acc)@.len() == old(acc)@.len(), final(cnt)@.len() == old(cnt)@.len(),
        forall|i: int| 0 <= i < sl.n ==> #[trigger] final(acc)@[i] as int == acc_of(sv, dlo, dhi, bks, sl.spk@, sl.ssk@, sl.n as int, i, n_l(sv) as int)
            && final(cnt)@[i] as int == cnt_of(sv, dlo, dhi, bks, sl.spk@, sl.ssk@, sl.n as int, i, n_l(sv) as int),
    no_unwind
{
    let ghost f = lrec(sv, dlo, dhi, bks);
    let ghost (spk, ssk, sn) = (sl.spk@, sl.ssk@, sl.n as int);
    let ghost nl = n_l(sv) as int;
    let m = sl.n;
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m, m == sl.n, acc@.len() == old(acc)@.len(), cnt@.len() == old(cnt)@.len(), acc@.len() >= m, cnt@.len() >= m,
            forall|k: int| 0 <= k < i ==> #[trigger] acc@[k] == 0 && cnt@[k] == 0,
        decreases m - i,
    {
        acc[i] = 0;
        cnt[i] = 0;
        i = i + 1;
    }
    let mut j: usize = 0;
    proof { lemma_split(nl, nt as int, 0, 0); }
    while j < nt
        invariant
            scan_all(outs@, nt as int, sv, ps, keys, dlo, dhi, nb as int, bm), all_fit(outs@), u < nb, bks == bkeys(keys, bm, u as int),
            domains_ok(sv), sizes_ok(sv), slots_dir(*sl), nl == n_l(sv) as int,
            f == lrec(sv, dlo, dhi, bks), j <= nt, m == sl.n, spk == sl.spk@, ssk == sl.ssk@, sn == m as int,
            m > 0, klo == spk[0], khi == spk[m - 1],
            acc@.len() == old(acc)@.len(), cnt@.len() == old(cnt)@.len(), acc@.len() >= m, cnt@.len() >= m,
            forall|i: int| 0 <= i < m ==> #[trigger] acc@[i] as int == acc_of(sv, dlo, dhi, bks, spk, ssk, sn, i, li_lo(sv, nt as int, j as int))
                && cnt@[i] as int == cnt_of(sv, dlo, dhi, bks, spk, ssk, sn, i, li_lo(sv, nt as int, j as int))
                && cnt@[i] <= li_lo(sv, nt as int, j as int)
                && -qmax() * cnt@[i] <= acc@[i] <= qmax() * cnt@[i],
        decreases nt - j,
    {
        let ghost lo = li_lo(sv, nt as int, j as int);
        let ghost hi = li_lo(sv, nt as int, j as int + 1);
        proof {
            lemma_split(nl, nt as int, j as int, j as int + 1);
            lemma_split(nl, nt as int, j as int + 1, nt as int);
            assert(scan_ok(outs@[j as int], nt as int, j as int, sv, ps, keys, dlo, dhi, nb as int, bm));
            assert(outs@[j as int].fit);
        }
        let ghost rs = lrecs(sv, dlo, dhi, bks, lo, hi);
        let o = &outs[j];
        let n = o.bnr[u];
        let rlen = o.brec.len();
        proof {
            lemma_range_filter_members(lo, hi, f);
            assert(trip_at(o.brec@, 3 * o.cr * u, n as int, lpk(sv), lsk(sv), lq_c(sv), rs));
            lemma_regions(o.cr as int, u as int, u as int, nb as int);
        }
        let base = 3 * o.cr * u;
        let mut x: usize = 0;
        while x < n
            invariant
                x <= n, trip_at(o.brec@, base as int, n as int, lpk(sv), lsk(sv), lq_c(sv), rs), rs == lrecs(sv, dlo, dhi, bks, lo, hi),
                rlen == o.brec@.len(),
                0 <= lo <= hi <= nl, nl == n_l(sv) as int, domains_ok(sv), sizes_ok(sv), slots_dir(*sl), n <= hi - lo,
                m == sl.n, spk == sl.spk@, ssk == sl.ssk@, sn == m as int, m > 0, klo == spk[0], khi == spk[m - 1],
                forall|t: int| 0 <= t < rs.len() ==> lo <= #[trigger] rs[t] < hi,
                acc@.len() == old(acc)@.len(), cnt@.len() == old(cnt)@.len(), acc@.len() >= m, cnt@.len() >= m,
                totals_at(acc@, cnt@, m as int, sv, dlo, dhi, bks, spk, ssk, sn, lo, rs, x as int),
            decreases n - x,
        {
            assert(base + 3 * x + 2 < rlen);
            let pk = o.brec[base + 3 * x];
            let ghost l = rs[x as int];
            let ghost acc0 = acc@;
            let ghost cnt0 = cnt@;
            let found = if klo <= pk && pk <= khi {
                let sk = o.brec[base + 3 * x + 1];
                proof {
                    assert(spk[0] / 64 <= pk / 64 <= spk[m - 1] / 64);
                }
                find_slot(sl, pk, sk)
            } else {
                proof {
                    // every slot's part key lies in [klo, khi]
                    assert forall|s: int| 0 <= s < m implies !(#[trigger] spk[s] as int == pk as int) by {
                        if s > 0 { assert(spk[0] <= spk[s]); }
                        if s < m - 1 { assert(spk[s] <= spk[m - 1]); }
                    }
                }
                None
            };
            proof {
                assert(lpk(sv)[l] == pk && lsk(sv)[l] == o.brec@[base + 3 * x + 1]);
                assert(0 <= l < n_l(sv));
                assert(num15(lqt(sv)[l]));
            }
            match found {
                Some(s0) => {
                    let q = o.brec[base + 3 * x + 2];
                    proof {
                        assert(q as int == lqt(sv)[l] as int);
                        let a0 = acc@[s0 as int] as int;
                        let c0 = cnt@[s0 as int] as int;
                        assert(c0 <= lo + x);
                        assert(c0 + 1 <= hi);
                        let bound = 999_999_999_999_999 * (c0 + 1);
                        assert(-bound <= a0 + q && a0 + q <= bound) by (nonlinear_arith)
                            requires -999_999_999_999_999 * c0 <= a0 <= 999_999_999_999_999 * c0,
                                -999_999_999_999_999 <= q <= 999_999_999_999_999, bound == 999_999_999_999_999 * (c0 + 1);
                        assert(bound < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff) by (nonlinear_arith)
                            requires 0 <= c0 + 1 <= 0xffff_ffff_ffff_ffff, bound == 999_999_999_999_999 * (c0 + 1);
                        assert(-qmax() * (c0 + 1) <= a0 + q && a0 + q <= qmax() * (c0 + 1));
                        assert(c0 + 1 <= 0xffff_ffff_ffff_ffff);
                    }
                    let av = acc[s0];
                    acc[s0] = av + q as i128;
                    let kv = cnt[s0];
                    cnt[s0] = kv + 1;
                    proof {
                        lemma_record_step(acc0, cnt0, acc@, cnt@, m as int, sv, dlo, dhi, bks, spk, ssk, sn, lo, rs, x as int, s0 as int);
                    }
                },
                None => {
                    proof {
                        lemma_record_skip(acc@, cnt@, m as int, sv, dlo, dhi, bks, spk, ssk, sn, lo, rs, x as int);
                    }
                },
            }
            x = x + 1;
        }
        proof {
            assert(rs.take(n as int) =~= rs);
            assert forall|i: int| 0 <= i < m implies #[trigger] acc@[i] as int == acc_of(sv, dlo, dhi, bks, spk, ssk, sn, i, hi)
                && cnt@[i] as int == cnt_of(sv, dlo, dhi, bks, spk, ssk, sn, i, hi) by {
                lemma_totals_step(sv, dlo, dhi, bks, spk, ssk, sn, i, lo, hi);
            }
        }
        j = j + 1;
    }
    proof { lemma_split(nl, nt as int, nt as int, nt as int); }
}

/// The decision of every local slot from the totals of its pair's first slot (`no_unwind`).
fn decide_slots(sl: &Slots, acc: &Vec<i128>, cnt: &Vec<u64>, ok: &mut Vec<bool>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(keys): Ghost<Seq<int>>, Ghost(qs): Ghost<Seq<int>>,
    Ghost(dlo): Ghost<int>, Ghost(dhi): Ghost<int>)
    requires
        slots_dir(*sl), slots_rows(sl.spk@, sl.ssk@, sl.saq@, sl.n as int, sv, qs), model_ok(sv), sizes_ok(sv),
        forall|t: int| 0 <= t < qs.len() ==> 0 <= #[trigger] qs[t] < n_ps(sv) && inp(sv, ps)(qs[t])
            && keys.contains(pspk(sv)[qs[t]] as int),
        acc@.len() >= sl.n, cnt@.len() >= sl.n, old(ok)@.len() >= sl.n,
        forall|i: int| 0 <= i < sl.n ==> #[trigger] acc@[i] as int == acc_of(sv, dlo, dhi, keys, sl.spk@, sl.ssk@, sl.n as int, i, n_l(sv) as int)
            && cnt@[i] as int == cnt_of(sv, dlo, dhi, keys, sl.spk@, sl.ssk@, sl.n as int, i, n_l(sv) as int),
    ensures
        final(ok)@.len() == old(ok)@.len(),
        forall|i: int| 0 <= i < sl.n ==> #[trigger] final(ok)@[i] == ps_ok(sv, ps, dlo, dhi, qs[i]),
    no_unwind
{
    let ghost (spk, ssk, sn) = (sl.spk@, sl.ssk@, sl.n as int);
    let n = sl.n;
    let mut s: usize = 0;
    while s < n
        invariant
            s <= n, n == sl.n, slots_dir(*sl), slots_rows(sl.spk@, sl.ssk@, sl.saq@, sl.n as int, sv, qs), model_ok(sv), sizes_ok(sv),
            spk == sl.spk@, ssk == sl.ssk@, sn == n as int,
            forall|t: int| 0 <= t < qs.len() ==> 0 <= #[trigger] qs[t] < n_ps(sv) && inp(sv, ps)(qs[t])
                && keys.contains(pspk(sv)[qs[t]] as int),
            acc@.len() >= n, cnt@.len() >= n, ok@.len() == old(ok)@.len(), ok@.len() >= n,
            forall|i: int| 0 <= i < n ==> #[trigger] acc@[i] as int == acc_of(sv, dlo, dhi, keys, spk, ssk, sn, i, n_l(sv) as int)
                && cnt@[i] as int == cnt_of(sv, dlo, dhi, keys, spk, ssk, sn, i, n_l(sv) as int),
            forall|i: int| 0 <= i < s ==> #[trigger] ok@[i] == ps_ok(sv, ps, dlo, dhi, qs[i]),
        decreases n - s,
    {
        let ka = sl.spk[s];
        let kb = sl.ssk[s];
        let aq = sl.saq[s];
        proof { assert(0 <= spk[s as int] && sl.g0 <= spk[s as int] / 64 < sl.g0 + sl.ng); }
        let found = find_slot(sl, ka, kb);
        let decision = match found {
            Some(c) => {
                proof {
                    let q = qs[s as int];
                    assert(pspk(sv)[q] == ka && pssk(sv)[q] == kb && psaq(sv)[q] == aq);
                    assert(inp(sv, ps)(q));
                    assert(in_part(sv, ps, ka as int));
                    assert(keys.contains(ka as int));
                    lemma_first_totals(sv, dlo, dhi, keys, spk, ssk, sn, ka as int, kb as int, c as int);
                    lemma_ltotals_bounds(sv, dlo, dhi, ka as int, kb as int);
                    assert(acc@[c as int] as int == lsum(sv, dlo, dhi, ka as int, kb as int));
                    assert(cnt@[c as int] as int == lcnt(sv, dlo, dhi, ka as int, kb as int));
                }
                cnt[c] > 0 && (aq as i128) * 200 > acc[c]
            },
            None => {
                proof {
                    assert(has_slot(spk, ssk, sn, ka as int, kb as int)) by {
                        assert(spk[s as int] as int == ka as int && ssk[s as int] as int == kb as int);
                    }
                }
                false
            },
        };
        let ghost ok0 = ok@;
        ok[s] = decision;
        proof {
            assert forall|i: int| 0 <= i < s + 1 implies #[trigger] ok@[i] == ps_ok(sv, ps, dlo, dhi, qs[i]) by {
                if i < s { assert(ok@[i] == ok0[i]); }
            }
        }
        s = s + 1;
    }
}

/// The output of one decide task: per local slot its decision and supplier key; `done` is false when the slots
/// did not fit the task's layout facts (then nothing is claimed).
pub struct DecideOut {
    pub ok: Vec<bool>,
    pub ssk: Vec<i64>,
    pub n: usize,
    pub done: bool,
}

/// What a finished decide task of bucket `u` guarantees.
pub open spec fn decide_ok(o: DecideOut, sv: StoresView, ps: Seq<Literal>, bm: u64, u: int, dlo: int, dhi: int) -> bool {
    let qs = bucket_rows(sv, ps, bm, u);
    &&& o.done ==> o.n == qs.len() && o.ok@.len() >= o.n && o.ssk@.len() >= o.n
        && forall|s: int| 0 <= s < o.n ==> #[trigger] o.ok@[s] == ps_ok(sv, ps, dlo, dhi, qs[s]) && o.ssk@[s] == pssk(sv)[qs[s]]
}

/// One decide task: bucket `u` of `nb` of the `nt` scan outputs, with buffers for `cap` slots and `dcap` directory
/// entries.
pub struct DecideTask {
    pub outs: Arc<Vec<ScanOut>>,
    pub nt: usize,
    pub nb: usize,
    pub bm: u64,
    pub u: usize,
    pub cap: usize,
    pub dcap: usize,
    pub spk: Vec<i64>,
    pub ssk: Vec<i64>,
    pub saq: Vec<i64>,
    pub dir: Vec<usize>,
    pub acc: Vec<i128>,
    pub cnt: Vec<u64>,
    pub ok: Vec<bool>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
    pub keys: Ghost<Seq<int>>,
    pub dlo: Ghost<int>,
    pub dhi: Ghost<int>,
}

impl WorkerTask for DecideTask {
    type Output = DecideOut;

    open spec fn pre(&self) -> bool {
        &&& scan_all((*self.outs)@, self.nt as int, self.sv@, self.ps@, self.keys@, self.dlo@, self.dhi@, self.nb as int, self.bm)
        &&& all_fit((*self.outs)@) && self.u < self.nb
        &&& model_ok(self.sv@) && sizes_ok(self.sv@) && keys_decide(self.keys@, self.sv@, self.ps@)
        &&& self.spk@.len() >= self.cap && self.ssk@.len() >= self.cap && self.saq@.len() >= self.cap
        &&& self.acc@.len() >= self.cap && self.cnt@.len() >= self.cap && self.ok@.len() >= self.cap
        &&& self.dir@.len() >= self.dcap
    }

    open spec fn post(&self, out: DecideOut) -> bool {
        decide_ok(out, self.sv@, self.ps@, self.bm, self.u as int, self.dlo@, self.dhi@)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.u as u64, self.u as u64)
    }

    fn run(self) -> (out: DecideOut) {
        let DecideTask { outs, nt, nb, bm, u, cap, dcap, spk, ssk, saq, dir, acc, cnt, ok, sv, ps, keys, dlo, dhi } = self;
        let ghost (sv, ps, keys, dlo, dhi) = (sv@, ps@, keys@, dlo@, dhi@);
        let ghost bks = bkeys(keys, bm, u as int);
        let ov: &Vec<ScanOut> = &*outs;
        let mut spk = spk;
        let mut ssk = ssk;
        let mut saq = saq;
        let mut dir = dir;
        let mut acc = acc;
        let mut cnt = cnt;
        let mut ok = ok;
        let ghost qs = bucket_rows(sv, ps, bm, u as int);
        let n = match gather_slots(ov, nt, nb, bm, u, &mut spk, &mut ssk, &mut saq, cap, Ghost(sv), Ghost(ps), Ghost(keys), Ghost(dlo), Ghost(dhi)) {
            Some(n) => n,
            None => { return DecideOut { ok, ssk, n: 0, done: false }; },
        };
        if n == 0 {
            return DecideOut { ok, ssk, n: 0, done: true };
        }
        if !check_ascending(&spk, n) {
            return DecideOut { ok, ssk, n: 0, done: false };
        }
        let klo = spk[0];
        let khi = spk[n - 1];
        if klo < 0 || khi >= KEY_LIMIT || n as u64 >= 0x1_0000_0000u64 {
            return DecideOut { ok, ssk, n: 0, done: false };
        }
        proof {
            crate::agent::common::bitset::lemma_word_pos(klo as u64);
            crate::agent::common::bitset::lemma_word_pos(khi as u64);
            if n > 1 { assert(spk@[0] <= spk@[n - 1]); }
            let (a, b) = (klo as u64, khi as u64);
            assert(a <= b && b < 0x8000_0000u64 ==> (a >> 6u64) <= (b >> 6u64) && (b >> 6u64) < 0x0200_0000u64) by (bit_vector);
        }
        let g0 = ((klo as u64) >> 6u64) as usize;
        let ng = ((khi as u64) >> 6u64) as usize - g0 + 1;
        if ng + 1 > dcap {
            return DecideOut { ok, ssk, n: 0, done: false };
        }
        proof {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] spk@[i] && g0 <= spk@[i] / 64 < g0 + ng by {
                if i > 0 { assert(spk@[0] <= spk@[i]); }
                if i < n - 1 { assert(spk@[i] <= spk@[n - 1]); }
            }
        }
        build_dir(&spk, n, g0, ng, &mut dir);
        let sl = Slots { spk, ssk, saq, n, dir, g0, ng };
        proof {
            let p = and_pred(inp(sv, ps), kbucket(pspk(sv), bm, u as int));
            lemma_range_filter_members(0, n_ps(sv) as int, p);
            lemma_bkeys(keys, bm, u as int);
            assert forall|t: int| 0 <= t < qs.len() implies 0 <= #[trigger] qs[t] < n_ps(sv) && inp(sv, ps)(qs[t])
                && bks.contains(pspk(sv)[qs[t]] as int) by {
                assert(p(qs[t]));
                assert(in_part(sv, ps, pspk(sv)[qs[t]] as int));
                assert(keys.contains(pspk(sv)[qs[t]] as int));
                assert(((pspk(sv)[qs[t]] as int) as i64) == pspk(sv)[qs[t]]);
            }
        }
        agg_records(ov, nt, nb, bm, u, &sl, klo, khi, &mut acc, &mut cnt, Ghost(sv), Ghost(ps), Ghost(keys), Ghost(bks), Ghost(dlo), Ghost(dhi));
        decide_slots(&sl, &acc, &cnt, &mut ok, Ghost(sv), Ghost(ps), Ghost(bks), Ghost(qs), Ghost(dlo), Ghost(dhi));
        let ghost slv = sl;
        let Slots { spk, ssk, saq, n, dir, g0, ng } = sl;
        proof {
            assert(ssk@ == slv.ssk@ && n == slv.n);
            assert(slots_rows(slv.spk@, slv.ssk@, slv.saq@, n as int, sv, qs));
            assert(n as int == qs.len());
            assert forall|s: int| 0 <= s < n implies #[trigger] ok@[s] == ps_ok(sv, ps, dlo, dhi, qs[s]) && ssk@[s] == pssk(sv)[qs[s]] by {
                assert(slv.spk@[s] == pspk(sv)[qs[s]]);
                assert(slv.ssk@[s] == pssk(sv)[qs[s]]);
            }
        }
        let out = DecideOut { ok, ssk, n, done: true };
        proof {
            assert(out.ok@ == ok@ && out.ssk@ == ssk@);
            assert(qs == bucket_rows(sv, ps, bm, u as int));
            assert(decide_ok(out, sv, ps, bm, u as int, dlo, dhi));
        }
        out
    }
}

/// The decide task of bucket `u`: its slot count (the bucket sizes of all scan tasks, summed) and directory size
/// (from the bucket's first and last part key) are read from the scan outputs; the task checks both again.
fn decide_task(outs_a: &Arc<Vec<ScanOut>>, nt: usize, nb: usize, bm: u64, u: usize,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(keys): Ghost<Seq<int>>, Ghost(dlo): Ghost<int>, Ghost(dhi): Ghost<int>)
    -> (task: DecideTask)
    requires
        scan_all((**outs_a)@, nt as int, sv, ps, keys, dlo, dhi, nb as int, bm), all_fit((**outs_a)@), u < nb <= 64,
        model_ok(sv), sizes_ok(sv), keys_decide(keys, sv, ps),
    ensures
        task.pre(), task.u == u, task.nb == nb, task.bm == bm, task.nt == nt,
        task.sv@ == sv && task.ps@ == ps && task.dlo@ == dlo && task.dhi@ == dhi,
{
    let ov: &Vec<ScanOut> = &**outs_a;
    let mut cap: usize = 0;
    let mut kfirst: i64 = 0;
    let mut klast: i64 = 0;
    let mut seen = false;
    let mut t: usize = 0;
    while t < nt
        invariant t <= nt, ov@.len() == nt, u < 64,
        decreases nt - t,
    {
        let o = &ov[t];
        if u < o.bnp.len() {
            let m = o.bnp[u];
            if m > 0 && o.cp <= usize::MAX / 192 {
                proof {
                    assert(3 * o.cp * u <= usize::MAX) by (nonlinear_arith) requires o.cp <= usize::MAX / 192, u < 64;
                }
                let base = 3 * o.cp * u;
                if base <= o.bps.len() && m <= (o.bps.len() - base) / 3 {
                    if !seen {
                        kfirst = o.bps[base];
                        seen = true;
                    }
                    klast = o.bps[base + 3 * (m - 1)];
                }
            }
            cap = match cap.checked_add(m) { Some(x) => x, None => cap };
        }
        t = t + 1;
    }
    let dcap: usize = if seen && 0 <= kfirst && kfirst <= klast && klast < KEY_LIMIT {
        proof {
            let (a, b) = (kfirst as u64, klast as u64);
            assert(a <= b && b < 0x8000_0000u64 ==> (a >> 6u64) <= (b >> 6u64) && (b >> 6u64) < 0x0200_0000u64) by (bit_vector);
        }
        ((klast as u64 >> 6u64) - (kfirst as u64 >> 6u64)) as usize + 2
    } else {
        2
    };
    if cap == 0 {
        // an empty bucket: no slots, no buffers
        return DecideTask {
            outs: outs_a.clone(), nt, nb, bm, u, cap, dcap: 0,
            spk: Vec::new(), ssk: Vec::new(), saq: Vec::new(), dir: Vec::new(),
            acc: Vec::new(), cnt: Vec::new(), ok: Vec::new(),
            sv: Ghost(sv), ps: Ghost(ps), keys: Ghost(keys), dlo: Ghost(dlo), dhi: Ghost(dhi),
        };
    }
    DecideTask {
        outs: outs_a.clone(), nt, nb, bm, u, cap, dcap,
        spk: zeroed_i64(cap), ssk: zeroed_i64(cap), saq: zeroed_i64(cap), dir: zeroed_usize(dcap),
        acc: zeroed_i128(cap), cnt: zeroed_u64(cap), ok: zeroed_bool(cap),
        sv: Ghost(sv), ps: Ghost(ps), keys: Ghost(keys), dlo: Ghost(dlo), dhi: Ghost(dhi),
    }
}

/// The decisions of all partsupp rows, one task per bucket: in parallel when `workers` covers the buckets, else one
/// after another on the calling thread. `Ok(None)` when a scan task's buckets or a decide task's layout facts fail.
pub fn decide_pass(outs: Vec<ScanOut>, workers: usize, nt: usize, nb: usize, bm: u64, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(keys): Ghost<Seq<int>>, Ghost(dlo): Ghost<int>, Ghost(dhi): Ghost<int>)
    -> (r: Result<Option<Vec<DecideOut>>, WorkerFailure>)
    requires
        scan_all(outs@, nt as int, sv, ps, keys, dlo, dhi, nb as int, bm), model_ok(sv), sizes_ok(sv), keys_decide(keys, sv, ps),
        1 <= nb <= MAX_WORKERS, 1 <= nt <= MAX_WORKERS,
    ensures
        r matches Ok(Some(res)) ==> res@.len() == nb && forall|u: int| 0 <= u < nb ==> #[trigger] res@[u].done
            && decide_ok(res@[u], sv, ps, bm, u, dlo, dhi),
{
    let mut t: usize = 0;
    while t < nt
        invariant t <= nt, outs@.len() == nt, forall|t2: int| 0 <= t2 < t ==> #[trigger] outs@[t2].fit,
        decreases nt - t,
    {
        if !outs[t].fit {
            return Ok(None);
        }
        t = t + 1;
    }
    let outs_a = Arc::new(outs);
    let serial = workers < nb;
    let mut tasks: Vec<DecideTask> = Vec::new();
    let mut res: Vec<DecideOut> = Vec::new();
    let mut u: usize = 0;
    while u < nb
        invariant
            scan_all((*outs_a)@, nt as int, sv, ps, keys, dlo, dhi, nb as int, bm), all_fit((*outs_a)@),
            model_ok(sv), sizes_ok(sv), keys_decide(keys, sv, ps),
            1 <= nb <= MAX_WORKERS, u <= nb,
            serial ==> res@.len() == u && tasks@.len() == 0,
            !serial ==> tasks@.len() == u && res@.len() == 0,
            forall|i: int| 0 <= i < res@.len() ==> decide_ok(#[trigger] res@[i], sv, ps, bm, i, dlo, dhi),
            forall|i: int| 0 <= i < tasks@.len() ==> (#[trigger] tasks@[i]).pre() && tasks@[i].u == i && tasks@[i].bm == bm
                && tasks@[i].sv@ == sv && tasks@[i].ps@ == ps && tasks@[i].dlo@ == dlo && tasks@[i].dhi@ == dhi,
        decreases nb - u,
    {
        let task = decide_task(&outs_a, nt, nb, bm, u, Ghost(sv), Ghost(ps), Ghost(keys), Ghost(dlo), Ghost(dhi));
        if serial {
            let o = task.run();
            res.push(o);
        } else {
            tasks.push(task);
        }
        u = u + 1;
    }
    if !serial {
        let ghost tasks_v = tasks@;
        res = match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => { return Err(e); },
        };
        proof {
            assert forall|i: int| 0 <= i < nb implies decide_ok(#[trigger] res@[i], sv, ps, bm, i, dlo, dhi) by {
                assert(tasks_v[i].post(res@[i]));
            }
        }
    }
    let mut u: usize = 0;
    while u < nb
        invariant
            res@.len() == nb, u <= nb,
            forall|i: int| 0 <= i < nb ==> decide_ok(#[trigger] res@[i], sv, ps, bm, i, dlo, dhi),
            forall|i: int| 0 <= i < u ==> #[trigger] res@[i].done,
        decreases nb - u,
    {
        if !res[u].done {
            return Ok(None);
        }
        u = u + 1;
    }
    Ok(Some(res))
}

} // verus!
