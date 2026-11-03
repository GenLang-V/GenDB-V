//! TPC-H Q22 (global sales opportunity) over the storages `custpart` (customer in key order: c_custkey, c_phone,
//! c_acctbal) and `orders_custidx` (an index of orders on o_custkey: a dense directory whose entry for a key is
//! empty exactly when no orders row has that key).
//!
//! Plan:
//! 1. the group of every parameter code: a lookup table of the two-byte codes (`table_ok`) and the parameter texts
//!    for any other code length;
//! 2. pass A (`scan::run_a`, parallel over customer chunks): count and sum of c_acctbal over the rows with a listed
//!    country code (`SUBSTRING(c_phone, 1, 2)`, `common::sub2`) and a positive balance; the AVG subquery is
//!    `numeric_div(sum, count)` (`exec_avg_finalize`), NULL without rows (then no row qualifies);
//! 3. pass B (`scan::run_b`): per group, count and sum of the balances of the rows with a listed code, a balance
//!    above the average (an integer coefficient threshold, `common::numthr`) and no orders (the directory entry
//!    of c_custkey is empty);
//! 4. one row per group with rows, ordered by the code bytewise (`output`).
//! Proof: `model` (what the scans compute per row), `bind` (the views describe every bound database), `sql` (the
//! statement's meaning in normal form: the subquery's value, the WHERE condition per row, the GROUP BY rows),
//! `answer` (the answers are allowed outcomes).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::{param_domain, param_typed};
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::exec::value::*;
use crate::link::query::exec_avg_finalize;

pub mod common;
pub mod model;
pub mod scan;
pub mod output;
pub mod sql;
pub mod group;
pub mod bind;
pub mod errs;
pub mod answer;
pub mod pmodel;
pub mod runs;
pub mod fbind;
pub mod fast;

use model::*;
use scan::*;
use output::*;
use sql::*;
use bind::*;
use answer::*;
use common::numthr::coeff_threshold;
use crate::spec::numeric::num_cmp;
use crate::link::query::{lemma_avg_ok, gcount, gsum};
use crate::stores::custpart::interface::common::colfmt as CPC;
use crate::stores::orders_custidx::interface as IX;
use crate::stores::cust_phoneidx::interface as PX;
use runs::{dense_ok, kern_ok, WINDOW_ROWS};
use fbind::{corder_ok, lemma_fast_shape, lemma_order, lemma_dense_keys};
use fast::{sel_ok, select_runs, make_table, estimate_bl, run_fused, combine_a, finish_b, MAX_SEL};

verus! {

/// Group size for row arithmetic: `b` itself, or `n` when `b` exceeds `n` (every row below `n` lies in group 0
/// either way), so it fits a `usize`.
fn eff_bs(b: u64, n: usize) -> (r: usize)
    requires b >= 1,
    ensures
        r >= 1,
        forall|i: int| 0 <= i < n ==> #[trigger] (i / (r as int)) == i / (b as int),
{
    if b <= n as u64 {
        b as usize
    } else if n > 0 {
        proof {
            assert forall|i: int| 0 <= i < n implies #[trigger] (i / (n as int)) == i / (b as int) by {
                assert(i / (n as int) == 0) by (nonlinear_arith) requires 0 <= i < n;
                assert(i / (b as int) == 0) by (nonlinear_arith) requires 0 <= i < b;
            }
        }
        n
    } else {
        1
    }
}

/// The lookup table of two-byte codes: entry `256 x + y` is the group of `[x, y]`.
fn build_table(pats: &Vec<&'static [u8]>, plens: &Vec<usize>, Ghost(ps): Ghost<Seq<Literal>>) -> (t: Vec<u8>)
    requires pats_ok(pats@, plens@, ps),
    ensures table_ok(t@, ps),
{
    let mut t: Vec<u8> = vec![7u8; 65536];
    let mut k: usize = 7;
    // Slots from the last to the first, so the first slot holding a code wins.
    while k > 0
        invariant
            k <= 7,
            pats_ok(pats@, plens@, ps),
            t@.len() == 65536,
            forall|x: int| 0 <= x < 65536 ==> #[trigger] t@[x] as int == gid_from(ps, k as int, seq![(x / 256) as u8, (x % 256) as u8]),
        decreases k,
    {
        k = k - 1;
        let ghost t0 = t@;
        if plens[k] == 2 {
            let p: &'static [u8] = pats[k];
            let x0 = p[0];
            let x1 = p[1];
            let key = (x0 as usize) * 256 + (x1 as usize);
            t.set(key, k as u8);
            proof {
                assert((key as int) / 256 == x0 as int) by (nonlinear_arith) requires key as int == x0 as int * 256 + x1 as int, 0 <= x1 < 256;
                assert((key as int) % 256 == x1 as int) by (nonlinear_arith) requires key as int == x0 as int * 256 + x1 as int, 0 <= x1 < 256;
                assert(ptext(ps, k as int) =~= seq![x0, x1]);
                assert forall|x: int| 0 <= x < 65536 implies #[trigger] t@[x] as int == gid_from(ps, k as int, seq![(x / 256) as u8, (x % 256) as u8]) by {
                    let c = seq![(x / 256) as u8, (x % 256) as u8];
                    if x == key as int {
                        assert(c =~= seq![x0, x1]);
                    } else {
                        // Another code: it differs from the slot's text in one of its two bytes.
                        assert(0 <= x / 256 < 256 && 0 <= x % 256 < 256);
                        assert(x == (x / 256) * 256 + x % 256);
                        if c == ptext(ps, k as int) {
                            assert(c[0] == x0 && c[1] == x1);
                            assert((x / 256) as u8 as int == x / 256);
                            assert((x % 256) as u8 as int == x % 256);
                            assert(x == key as int);
                        }
                    }
                }
            }
        } else {
            proof {
                assert forall|x: int| 0 <= x < 65536 implies #[trigger] t@[x] as int == gid_from(ps, k as int, seq![(x / 256) as u8, (x % 256) as u8]) by {
                    let c = seq![(x / 256) as u8, (x % 256) as u8];
                    assert(c.len() == 2);
                    assert(ptext(ps, k as int) != c);
                }
            }
        }
    }
    t
}

/// The parameter texts as slices (`pats_ok`).
fn param_slices(params: &Params) -> (r: (Vec<&'static [u8]>, Vec<usize>))
    ensures pats_ok(r.0@, r.1@, params@),
{
    let mut pv: Vec<&'static [u8]> = Vec::new();
    pv.push(params.p0);
    pv.push(params.p1);
    pv.push(params.p2);
    pv.push(params.p3);
    pv.push(params.p4);
    pv.push(params.p5);
    pv.push(params.p6);
    let mut lv: Vec<usize> = Vec::new();
    lv.push(params.p0.len());
    lv.push(params.p1.len());
    lv.push(params.p2.len());
    lv.push(params.p3.len());
    lv.push(params.p4.len());
    lv.push(params.p5.len());
    lv.push(params.p6.len());
    proof {
        let ps = params@;
        assert forall|k: int| 0 <= k < 7 implies (#[trigger] pv@[k])@ == ptext(ps, k) && lv@[k] == ptext(ps, k).len() by {
            if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else {}
        }
    }
    (pv, lv)
}

/// The fast path when its layout facts hold (the order of `cust_phoneidx` is present, blocks of 65536 rows, a
/// directory, customer rows sorted by a dense key); `None` sends the query to the general path.
fn try_fast(stores: &mut Stores, n: usize, bs: usize, kc: &'static [u32], kb: &'static [i64], poffs: &'static [u64],
    pbytes: &'static [u8], ac: &'static [u32], ab: &'static [i64], dir: bool, kmin: i64, offs: &'static [u32], nk: usize,
    table: &Vec<u8>, pats: &Vec<&'static [u8]>, plens: &Vec<usize>, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(v): Ghost<Cv>, Ghost(db0): Ghost<Database>) -> (r: Option<Result<Answer, QueryError>>)
    requires
        old(stores)@ == sv,
        bound_db(sv, db0),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> rows_match(v, db),
        views_of(sv, v),
        cv_ok(v),
        ps_ok(v.ps),
        v.kc == kc@ && v.kb == kb@ && v.poffs == poffs@ && v.pbytes == pbytes@ && v.ac == ac@ && v.ab == ab@,
        v.bs == bs as int && v.n == n as int && v.dir == dir && v.kmin == kmin as int && v.offs == offs@ && v.nk == nk as int,
        table_ok(table@, v.ps),
        pats_ok(pats@, plens@, v.ps),
        1 <= workers <= MAX_WORKERS,
    ensures
        final(stores)@ == sv,
        r matches Some(x) ==> answer_meets(sv, v.ps, x),
{
    proof {
        lemma_fast_shape(sv, db0);
    }
    let kindp = stores.custpart.extent_u64(20, 0, 1);
    let np = stores.cust_phoneidx.part_len(50);
    let nr = stores.cust_phoneidx.part_len(51);
    let perm = stores.cust_phoneidx.extent_u32(50, 0, np);
    let runs_p = stores.cust_phoneidx.extent_u64(51, 0, nr);
    proof {
        assert(perm@ =~= PX::perm(sv.cust_phoneidx));
        assert(runs_p@ =~= PX::runs(sv.cust_phoneidx));
        assert(kindp@ =~= CPC::u64s(sv.custpart[20]));
    }
    if np == n && n >= 1 && nr >= 2 && bs == 65536 && dir && kindp[0] == 1 {
        let last = n - 1;
        proof {
            assert(0int / v.bs == 0) by (nonlinear_arith) requires v.bs >= 1;
            assert(i64::MIN <= rkey(v, 0) <= i64::MAX);
            assert(i64::MIN <= rkey(v, last as int) <= i64::MAX);
            assert((last as int) / v.bs < v.kb.len());
        }
        let k0: i64 = kb[0] + kc[0] as i64;
        let kl: i64 = kb[last / bs] + kc[last] as i64;
        let dd: i128 = (k0 as i128) - (kmin as i128);
        if (kl as i128) - (k0 as i128) == (last as i128) && dd >= 0 && dd + (n as i128) <= usize::MAX as i128 {
            let d = dd as usize;
            let olen = offs.len();
            proof {
                lemma_order(sv, db0, v);
                lemma_dense_keys(sv, db0, v);
                assert(dense_ok(v, d as int));
                assert(offs@.len() <= usize::MAX);
                assert(kern_ok(v, perm@, ac@, ab@, offs@, d as int, nk as int));
            }
            match select_runs(poffs, pbytes, perm, runs_p, table, pats, plens, Ghost(v)) {
                Some((starts, ends, gids, sel_of)) => {
                    match query_fast(perm, runs_p, ac, ab, offs, d, nk, starts, ends, gids, sel_of, pats, plens, n,
                        workers, dispatch, Ghost(sv), Ghost(v)) {
                        Some(r) => {
                            return Some(r);
                        },
                        None => {},
                    }
                },
                None => {},
            }
        }
    }

    None
}

/// The rest of the query over the country-code order (`fast`): pass A from the fused kernel, the average, pass B
/// from the kernel's candidates, the result rows. `None` when the kernel cannot be laid out (then the general
/// path runs).
fn query_fast(perm: &'static [u32], runs_p: &'static [u64], ac: &'static [u32], ab: &'static [i64],
    offs: &'static [u32], d: usize, nk: usize, starts: Vec<usize>, ends: Vec<usize>, gids: Vec<usize>, sel_of: Vec<usize>,
    pats: &Vec<&'static [u8]>, plens: &Vec<usize>, n: usize, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(v): Ghost<Cv>) -> (r: Option<Result<Answer, QueryError>>)
    requires
        forall|db: Database| #[trigger] bound_db(sv, db) ==> rows_match(v, db),
        ps_ok(v.ps),
        v.n == n,
        kern_ok(v, perm@, ac@, ab@, offs@, d as int, nk as int),
        corder_ok(v, perm@, runs_p@),
        sel_ok(v, perm@, runs_p@, starts@, ends@, gids@, sel_of@),
        starts@.len() <= MAX_SEL,
        pats_ok(pats@, plens@, v.ps),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Some(x) ==> answer_meets(sv, v.ps, x),
{
    let ghost ps = v.ps;
    let ns = starts.len();
    // One task per range of about equal rows, at most one per window of the kernel.
    let nwin = n / WINDOW_ROWS + 1;
    let k: usize = if nwin < workers { nwin } else { workers };
    let nw = k;
    let rb = make_bounds(n, k);
    let bt = Arc::new(make_table(perm, &starts, &ends, &rb, k, Ghost(v.n)));
    let bl = estimate_bl(perm, ac, ab, &starts, &ends, Ghost(v));
    let (outs, bases, wb) = match run_fused(perm, ac, ab, offs, d, nk, bl, &bt, ns, nw, k, &rb, dispatch, Ghost(v)) {
        Ok(Some(x)) => x,
        Ok(None) => return None,
        Err(f) => return Some(Err(QueryError::WorkerFailed(f))),
    };
    let btv: &Vec<Vec<usize>> = &*bt;
    let (sum, cnt) = combine_a(&outs, k, &wb, &bases, btv, ns, nw, bl, &starts, &ends, &gids, &sel_of, runs_p,
        Ghost(v), Ghost(perm@));
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies
            cnt == gcount(g2(ps), ctab(db), Seq::empty()) && sum == gsum(g2(ps), ctab(db), Seq::empty(), 0) by {
            lemma_count_a_all(v, db);
        }
    }
    if cnt == 0 {
        // AVG over no rows is NULL: no row is above it.
        let r = Ok(Answer::Rows(Vec::new()));
        proof {
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies db_facts(v, Val::Null, db) by {
                lemma_g2_caps(db, ps);
            }
            lemma_answer_empty(sv, v, r);
        }
        return Some(r);
    }
    let avg = match exec_avg_finalize(sum, 2, cnt) {
        Ok(a) => a,
        Err(_) => {
            proof {
                lemma_answer_capacity(sv, v, sum as int, cnt as int);
            }
            return Some(Ok(Answer::Capacity));
        },
    };
    proof {
        lemma_avg_ok(sum as int, 2, cnt as int);
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies db_facts(v, avg@, db) by {
            lemma_g2_caps(db, ps);
        }
    }
    let (ca, sa) = match avg {
        EVal::Num { coeff, scale } => (coeff, scale),
        _ => {
            proof {
                assert(false);
            }
            return Some(Ok(Answer::Rows(Vec::new())));
        },
    };
    let thr = coeff_threshold(2, ca, sa);
    proof {
        assert forall|a: int| -acct_bound() < a < acct_bound() implies #[trigger] gt_avg(a, avg@) == (a > thr) by {
            assert(i128::MIN < a <= i128::MAX);
            assert(num_cmp(a, 2, ca as int, sa as nat) == num_cmp(a, 2 as u32 as nat, ca as int, sa as nat));
        }
    }
    let (cnts, sums) = if (bl as i128) <= thr {
        finish_b(&outs, k, &wb, &bases, btv, ns, nw, bl, &starts, &ends, &gids, &sel_of, runs_p, thr,
            Ghost(v), Ghost(perm@), Ghost(avg@))
    } else {
        // The estimate was above the average: list every candidate (`bl == i64::MIN`).
        if thr < (i64::MIN as i128) {
            return None;
        }
        let (outs2, bases2, wb2) = match run_fused(perm, ac, ab, offs, d, nk, i64::MIN, &bt, ns, nw, k, &rb, dispatch,
            Ghost(v)) {
            Ok(Some(x)) => x,
            Ok(None) => return None,
            Err(f) => return Some(Err(QueryError::WorkerFailed(f))),
        };
        finish_b(&outs2, k, &wb2, &bases2, btv, ns, nw, i64::MIN, &starts, &ends, &gids, &sel_of, runs_p, thr,
            Ghost(v), Ghost(perm@), Ghost(avg@))
    };
    let mut g: usize = 0;
    while g < 7
        invariant
            g <= 7,
            cnts@.len() == 7,
            forall|q: int| 0 <= q < g ==> #[trigger] cnts@[q] <= i64::MAX,
            forall|db: Database| #[trigger] bound_db(sv, db) ==> db_facts(v, avg@, db),
            ps_ok(v.ps),
            v.ps == ps,
            avg@ is Num,
            post_b(v, avg@, 0, v.n, cnts@, sums@),
        decreases 7 - g,
    {
        if cnts[g] > i64::MAX as u64 {
            proof {
                lemma_answer_overflow(sv, v, avg@, cnts@, sums@, g as int);
            }
            return Some(Ok(Answer::SqlError(SqlError::NumericValueOutOfRange)));
        }
        g = g + 1;
    }
    let ord = group_order(pats, plens, &cnts, Ghost(ps));
    let rows = output_rows(pats, plens, &cnts, &sums, &ord, Ghost(ps));
    let r = Ok(Answer::Rows(rows));
    proof {
        assert(exec_ok(v, avg@, cnts@, sums@, ord@));
        lemma_answer_rows(sv, v, avg@, cnts@, sums@, ord@, r);
    }
    Some(r)
}

/// TPC-H Q22.
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_shape(sv, db0);
        lemma_ps_ok(ps);
    }

    // ---- custpart: customer keys, phones and balances.
    let n = stores.custpart.part_len(2);
    let clay = stores.custpart.extent_u64(0, 0, 2);
    let bs = eff_bs(clay[1], n);
    let nkb = stores.custpart.part_len(3);
    let kc = stores.custpart.extent_u32(2, 0, n);
    let kb = stores.custpart.extent_i64(3, 0, nkb);
    let npo = stores.custpart.part_len(10);
    let poffs = stores.custpart.extent_u64(10, 0, npo);
    let nbytes = stores.custpart.part_len(11);
    let pbytes = stores.custpart.extent_u8(11, 0, nbytes);
    let ac = stores.custpart.extent_u32(12, 0, n);
    let nab = stores.custpart.part_len(13);
    let ab = stores.custpart.extent_i64(13, 0, nab);

    // ---- orders_custidx: the directory (or the fallback keys).
    let meta = stores.orders_custidx.extent_i64(0, 0, 2);
    let nofs = stores.orders_custidx.part_len(1);
    let offs = stores.orders_custidx.extent_u32(1, 0, nofs);
    let n_o = stores.orders_custidx.part_len(3);
    let keys = stores.orders_custidx.extent_i64(3, 0, n_o);
    let dir = meta[0] == 1 && nofs >= 1;
    let kmin = meta[1];
    let nk: usize = if nofs >= 1 { nofs - 1 } else { 0 };

    let ghost v = Cv {
        poffs: poffs@, pbytes: pbytes@, ac: ac@, ab: ab@, kc: kc@, kb: kb@, bs: bs as int, n: n as int, dir,
        kmin: kmin as int, offs: offs@, nk: nk as int, keys: keys@, n_o: n_o as int, ps,
    };
    proof {
        let (pc, pi) = (sv.custpart, sv.orders_custidx);
        assert(clay@ =~= CPC::u64s(pc[0]));
        assert(kc@ =~= CPC::u32s(pc[2]));
        assert(kb@ =~= CPC::i64s(pc[3]));
        assert(poffs@ =~= CPC::u64s(pc[10]));
        assert(pbytes@ =~= CPC::u8s(pc[11]));
        assert(ac@ =~= CPC::u32s(pc[12]));
        assert(ab@ =~= CPC::i64s(pc[13]));
        assert(meta@ =~= IX::idx_i64s(pi[0]));
        assert(offs@ =~= IX::idx_u32s(pi[1]));
        assert(keys@ =~= IX::idx_i64s(pi[3]));
        assert(views_of(sv, v));
        lemma_bind(sv, db0, v);
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies rows_match(v, db) by {
            lemma_bind(sv, db, v);
        }
    }

    // ---- the parameter codes.
    let (pv, lv) = param_slices(params);
    let table = Arc::new(build_table(&pv, &lv, Ghost(ps)));
    let pats = Arc::new(pv);
    let plens = Arc::new(lv);

    // ---- fast path: the country-code order of cust_phoneidx, with dense customer keys.
    match try_fast(stores, n, bs, kc, kb, poffs, pbytes, ac, ab, dir, kmin, offs, nk, &*table, &*pats, &*plens, workers,
        dispatch, Ghost(sv), Ghost(v), Ghost(db0)) {
        Some(r) => {
            return r;
        },
        None => {},
    }

    // ---- pass A: the AVG subquery.
    let k: usize = if n / 65536 + 1 < workers { n / 65536 + 1 } else { workers };
    let bounds = make_bounds(n, k);
    let (sum, cnt) = match run_a(poffs, pbytes, ac, ab, bs, &table, &pats, &plens, &bounds, k, dispatch, Ghost(v)) {
        Ok(o) => o,
        Err(f) => return Err(QueryError::WorkerFailed(f)),
    };
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies
            cnt == gcount(g2(ps), ctab(db), Seq::empty()) && sum == gsum(g2(ps), ctab(db), Seq::empty(), 0) by {
            lemma_count_a_all(v, db);
        }
    }
    if cnt == 0 {
        // AVG over no rows is NULL: no row is above it.
        let r = Ok(Answer::Rows(Vec::new()));
        proof {
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies db_facts(v, Val::Null, db) by {
                lemma_g2_caps(db, ps);
            }
            lemma_answer_empty(sv, v, r);
        }
        return r;
    }
    let avg = match exec_avg_finalize(sum, 2, cnt) {
        Ok(a) => a,
        Err(_) => {
            proof {
                lemma_answer_capacity(sv, v, sum as int, cnt as int);
            }
            return Ok(Answer::Capacity);
        },
    };
    proof {
        lemma_avg_ok(sum as int, 2, cnt as int);
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies db_facts(v, avg@, db) by {
            lemma_g2_caps(db, ps);
        }
    }
    let (ca, sa) = match avg {
        EVal::Num { coeff, scale } => (coeff, scale),
        _ => {
            proof {
                assert(false);
            }
            return Ok(Answer::Rows(Vec::new()));
        },
    };
    let thr = coeff_threshold(2, ca, sa);
    proof {
        assert forall|a: int| -acct_bound() < a < acct_bound() implies #[trigger] gt_avg(a, avg@) == (a > thr) by {
            assert(i128::MIN < a <= i128::MAX);
            assert(num_cmp(a, 2, ca as int, sa as nat) == num_cmp(a, 2 as u32 as nat, ca as int, sa as nat));
        }
    }

    // ---- pass B: the result rows per group.
    let (cnts, sums) = match run_b(poffs, pbytes, ac, ab, kc, kb, bs, &table, &pats, &plens, dir, kmin, offs, nk, keys,
        n_o, thr, &bounds, k, dispatch, Ghost(v), Ghost(avg@)) {
        Ok(o) => o,
        Err(f) => return Err(QueryError::WorkerFailed(f)),
    };
    let mut g: usize = 0;
    while g < 7
        invariant
            g <= 7,
            cnts@.len() == 7,
            forall|q: int| 0 <= q < g ==> #[trigger] cnts@[q] <= i64::MAX,
            forall|db: Database| #[trigger] bound_db(sv, db) ==> db_facts(v, avg@, db),
            ps_ok(v.ps),
            v.ps == ps,
            sv == old(stores)@,
            ps == params@,
            avg@ is Num,
            post_b(v, avg@, 0, v.n, cnts@, sums@),
        decreases 7 - g,
    {
        if cnts[g] > i64::MAX as u64 {
            proof {
                lemma_answer_overflow(sv, v, avg@, cnts@, sums@, g as int);
            }
            return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
        }
        g = g + 1;
    }
    let ord = group_order(&*pats, &*plens, &cnts, Ghost(ps));
    let rows = output_rows(&*pats, &*plens, &cnts, &sums, &ord, Ghost(ps));
    let r = Ok(Answer::Rows(rows));
    proof {
        assert(exec_ok(v, avg@, cnts@, sums@, ord@));
        lemma_answer_rows(sv, v, avg@, cnts@, sums@, ord@, r);
    }
    r
}

} // verus!
