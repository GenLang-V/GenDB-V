// AUTHOR MODULE ROOT (crate::agent). TPC-H Q20 over four storage uses: `part_nameidx` (part with a name order),
// `li_pkdate` (lineitem with an (l_partkey, l_shipdate) index), `suppliers` (partsupp, supplier, nation) and
// `suppliers_psrun` (only its run layout part: partsupp row j has key first + j / ratio).
//
// Plan: the matching part rows (`pfind`: two name-order ranges for a `P%` pattern, else the LIKE of every name); at
// one worker they are put in row order through a bit set (`hits::sorted_fast`), so the reads by part row and key go
// forward. One worker task per slice of that list (`kern`): per batch of parts, their keys, their partsupp rows by
// arithmetic (`kctx::run_range`, run layout) or by search, then per part its suppliers of a nation named `$3`
// (dense supplier keys: row = key - first key) and, per batch of four, their lineitem sums over the part's index
// entry (`kacc`). The calling thread merges the flags and writes s_name, s_address in supplier order (`run`: on the
// calling thread at one worker, else `outp` tasks), sorting only if that order is not the s_name order.
//
// Proof: `ast`/`nf`/`sem_*` reduce the statement's meaning to a normal form over the tables (`sem_top::lemma_body`);
// `bind_*`/`sl` restate it over the parts (`sl::lemma_sl_outcome`, for every database bound to the parts); the code
// computes `sl_outcome`; `top` turns that into `answer_meets`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::stores::part_nameidx::interface as pi;

pub mod common;
pub mod typed;
pub mod ast;
pub mod nf;
pub mod sem_li;
pub mod datewin;
pub mod sem_part;
pub mod sem_ps;
pub mod sem_top;
pub mod bind_sp;
pub mod bind_pl;
pub mod sl;
pub mod pfind;
pub mod kctx;
pub mod kacc;
pub mod kern;
pub mod run;
pub mod load;
pub mod top;
pub mod bits;
pub mod outp;
pub mod hits;

verus! {

use self::nf::*;
use self::bind_sp::*;
use self::sl::*;
use self::pfind::*;
use self::kctx::*;
use self::kern::*;
use self::top::*;
use self::bits::*;
use self::hits::*;
use self::common::likeprefix::{plain_prefix, prefix_cond, lemma_prefix_like};

/// The part rows of task `t` of `w`: `[np * t / w, np * (t + 1) / w)`.
proof fn lemma_chunk(np: int, t: int, w: int)
    requires 0 <= t < w, np >= 0,
    ensures 0 <= (np * t) / w <= (np * (t + 1)) / w <= np, t + 1 == w ==> (np * (t + 1)) / w == np,
{
    assert(0 <= np * t <= np * (t + 1) <= np * w) by (nonlinear_arith) requires 0 <= t < w, np >= 0;
    vstd::arithmetic::div_mod::lemma_div_is_ordered(np * t, np * (t + 1), w);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(np * (t + 1), np * w, w);
    vstd::arithmetic::div_mod::lemma_div_by_multiple(np, w);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(np * t, w);
}

/// The calling thread's facts about task `t`.
pub open spec fn task_ok(t: PartTask, c0: Ctx) -> bool {
    &&& t.pre()
    &&& t.ctx.sv@ == c0.sv@ && t.ctx.ps@ == c0.ps@ && t.ctx.d1g@ == c0.d1g@
    &&& t.ctx.ns == c0.ns && t.ctx.nps == c0.nps
}

/// One task per slice of the list of matching part rows.
fn make_tasks(ctx0: &Ctx, nt: usize, h: &Hits, perm: &'static [u32]) -> (tasks: Vec<PartTask>)
    requires
        ctx0.wf(),
        1 <= nt <= MAX_WORKERS,
        hits_wf(h, perm@),
        hits_ok(src_of(h, perm@), ctx0.pp(), ctx0.pat()),
    ensures
        tasks@.len() == nt,
        forall|w: int| 0 <= w < nt ==> #[trigger] task_ok(tasks@[w], *ctx0),
        forall|w: int| 0 <= w < nt ==> (#[trigger] tasks@[w]).lst()
            == src_of(h, perm@).subrange(outp::yb(h.len as int, w, nt as int), outp::yb(h.len as int, w + 1, nt as int)),
        forall|r: int| 0 <= r < ctx0.np && #[trigger] hit_row(ctx0.pp(), ctx0.pat(), r) ==> covered_by(tasks@, r),
{
    let ghost pp = ctx0.pp();
    let ghost pat = ctx0.pat();
    let ghost hl = src_of(h, perm@);
    let len = h.len;
    let ns = ctx0.ns;
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut t: usize = 0;
    let mut prev: usize = 0;
    while t < nt
        invariant
            ctx0.wf(),
            hits_wf(h, perm@), hl == src_of(h, perm@),
            hits_ok(hl, pp, pat), pp == ctx0.pp(), pat == ctx0.pat(),
            len == hl.len(), ns == ctx0.ns,
            1 <= nt <= MAX_WORKERS,
            t <= nt,
            tasks@.len() == t,
            prev as int == (len * t) / (nt as int),
            prev <= len,
            forall|w: int| 0 <= w < t ==> #[trigger] task_ok(tasks@[w], *ctx0),
            forall|w: int| 0 <= w < t ==> (#[trigger] tasks@[w]).lst()
                == hl.subrange(outp::yb(len as int, w, nt as int), outp::yb(len as int, w + 1, nt as int)),
            forall|i: int| 0 <= i < prev ==> #[trigger] covered_by(tasks@, hl[i] as int),
        decreases nt - t,
    {
        proof {
            lemma_chunk(len as int, t as int, nt as int);
            assert(len as int * (t + 1) <= 0x1_0000_0000_0000_0000 * 64) by (nonlinear_arith)
                requires len as int <= 0xffff_ffff_ffff_ffff, t + 1 <= 64;
        }
        let hi = ((len as u128 * (t as u128 + 1)) / nt as u128) as usize;
        let lo = prev;
        let ctx = ctx0.copy();
        proof {
            ctx.lemma_same_wf(ctx0);
        }
        let rl = if h.fast { Vec::new() } else { chunk(h, perm, lo, hi) };
        let n = hi - lo;
        let capo: usize = 1024 + n / 4;
        let em = Emit { fm: false, sf: Vec::new(), out: vec![0usize; capo], cnt: 0, cap: capo, ovf: false, junk: 0 };
        let bcap: usize = 256;
        let nb: usize = 0;
        let tb: Vec<u64> = vec![0u64; 1];
        proof {
            lemma_zero_bits(tb@, (tb@.len() * 64) as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ns as int, 64);
        }
        let task = PartTask { ctx, rl, fast: h.fast, perm, a1: h.a1, b1: h.b1, a2: h.a2, b2: h.b2, q0: lo, n, em, ks: vec![0i64; bcap], sts: vec![0usize; bcap], tch: vec![0u64; bcap], bcap, tb, nb, w0: vec![0usize; bcap], w1: vec![0usize; bcap] };
        proof {
            assert(task.em.wf(ns as int));
            assert(task.ctx.pat() == pat);
            assert(task.ctx.pp() == pp);
            assert(task.lst() =~= hl.subrange(lo as int, hi as int));
            assert(task.lst() =~= hl.subrange(lo as int, hi as int));
        assert forall|i: int| 0 <= i < n implies (#[trigger] task.lst()[i]) < task.ctx.np && hit_row(pp, pat, task.lst()[i] as int) by {
                assert(task.lst()[i] == hl[lo + i]);
            }
            assert(task.pre());
        }
        let ghost tasks0 = tasks@;
        tasks.push(task);
        proof {
            assert forall|w: int| 0 <= w < t + 1 implies #[trigger] task_ok(tasks@[w], *ctx0) by {
                if w < t {
                    assert(tasks@[w] == tasks0[w]);
                }
            }
            assert forall|w: int| 0 <= w < t + 1 implies (#[trigger] tasks@[w]).lst()
                == hl.subrange(outp::yb(len as int, w, nt as int), outp::yb(len as int, w + 1, nt as int)) by {
                if w < t {
                    assert(tasks@[w] == tasks0[w]);
                }
            }
            assert forall|i: int| 0 <= i < hi implies #[trigger] covered_by(tasks@, hl[i] as int) by {
                if i < prev {
                    assert(covered_by(tasks0, hl[i] as int));
                    let w = choose|w: int| 0 <= w < tasks0.len() && #[trigger] in_task(tasks0[w], hl[i] as int);
                    assert(tasks@[w] == tasks0[w]);
                    assert(in_task(tasks@[w], hl[i] as int));
                } else {
                    assert(tasks@[t as int].lst()[i - lo] == hl[i]);
                    assert(in_task(tasks@[t as int], hl[i] as int));
                }
            }
        }
        prev = hi;
        t = t + 1;
    }
    proof {
        vstd::arithmetic::div_mod::lemma_div_by_multiple(len as int, nt as int);
        assert(prev == len);
        assert forall|r: int| 0 <= r < ctx0.np && #[trigger] hit_row(pp, pat, r) implies covered_by(tasks@, r) by {
            let i = choose|i: int| 0 <= i < hl.len() && hl[i] == r;
            assert(covered_by(tasks@, hl[i] as int));
        }
    }
    tasks
}

/// The matching part rows (fast mode: two name-order ranges; general mode: the LIKE of every name) and whether
/// some name makes the LIKE fail.
fn matches(psl: &load::PartSlices, pat: &'static [u8], ctx0: &Ctx, in_row_order: bool) -> (r: (Hits, bool))
    requires
        ctx0.wf(),
        psl.np == pi::n_rows(ctx0.pp()),
        psl.offs@ == pi::name_offs(ctx0.pp()),
        psl.bytes@ == pi::name_bytes(ctx0.pp()),
        psl.perm@ == pi::perm(ctx0.pp()),
        pat@ == ctx0.pat(),
    ensures
        hits_wf(&r.0, psl.perm@),
        hits_ok(src_of(&r.0, psl.perm@), ctx0.pp(), ctx0.pat()),
        r.1 == sl_part_err(ctx0.pp(), ctx0.pat()),
{
    let ghost pp = ctx0.pp();
    let np = psl.np;
    let plen = pat.len();
    if psl.perm.len() == np && np > 0 && plen >= 2 && pat[plen - 1] == 0x25u8 {
        let (pre, _) = pat.split_at(plen - 1);
        if is_plain(pre) {
            proof {
                assert(pat@ =~= pre@.push(0x25u8));
            }
            let (a1, b1, a2, b2) = fast_ranges(psl.perm, psl.offs, psl.bytes, np, pre, Ghost(pp), Ghost(pat@));
            proof {
                if sl_part_err(pp, pat@) {
                    let q = choose|q: int| 0 <= q < pi::n_rows(pp) && #[trigger] like_of(pi::name_at(pp, q), pat@) is Err;
                    lemma_prefix_like(pi::name_at(pp, q), pre@);
                }
            }
            if b2 - a2 <= usize::MAX - (b1 - a1) {
                proof {
                    lemma_fast_src(pp, pat@, psl.perm@, a1 as int, b1 as int, a2 as int, b2 as int);
                }
                if in_row_order && np < usize::MAX - 64 {
                    // in row order: the reads by part row and key then go forward through each column
                    let hl = sorted_fast(psl.perm, a1, b1, a2, b2, np, Ghost(pp), Ghost(pat@));
                    let len = hl.len();
                    return (Hits { fast: false, a1: 0, b1: 0, a2: 0, b2: 0, len, hl }, false);
                }
                let h = Hits { fast: true, a1, b1, a2, b2, len: (b1 - a1) + (b2 - a2), hl: Vec::new() };
                return (h, false);
            }
        }
    }
    let (g, err) = like_all(psl.offs, psl.bytes, np, pat, Ghost(pp));
    let hl = hits_flags(&g, np, Ghost(pp), Ghost(pat@));
    let len = hl.len();
    (Hits { fast: false, a1: 0, b1: 0, a2: 0, b2: 0, len, hl }, err)
}

/// What the calling thread knows of a task's output.
pub open spec fn task_out(t: PartTask, e: Emit, sv: StoresView, ps: Seq<Literal>, d1: int, ns: int, nps: int) -> bool {
    &&& t.post(e)
    &&& t.ctx.sv@ == sv && t.ctx.ps@ == ps && t.ctx.d1g@ == d1
    &&& t.ctx.ns == ns && t.ctx.nps == nps
}

/// Task `w` of `nt` again, on the calling thread, with a bit-set emitter (when its list overflowed).
fn rerun(ctx0: &Ctx, h: &Hits, perm: &'static [u32], nt: usize, w: usize) -> (r: (Ghost<PartTask>, Emit))
    requires
        ctx0.wf(),
        1 <= nt <= MAX_WORKERS, w < nt,
        hits_wf(h, perm@),
        hits_ok(src_of(h, perm@), ctx0.pp(), ctx0.pat()),
    ensures
        task_ok(r.0@, *ctx0),
        r.0@.post(r.1),
        !lost(r.1),
        r.0@.lst() == src_of(h, perm@).subrange(outp::yb(h.len as int, w as int, nt as int), outp::yb(h.len as int, w + 1, nt as int)),
{
    let ghost hl = src_of(h, perm@);
    let len = h.len;
    proof {
        lemma_chunk(len as int, w as int, nt as int);
        assert(len as int * (w + 1) <= 0x1_0000_0000_0000_0000 * 64) by (nonlinear_arith)
            requires len as int <= 0xffff_ffff_ffff_ffff, w + 1 <= 64;
        assert(len as int * w <= 0x1_0000_0000_0000_0000 * 64) by (nonlinear_arith)
            requires len as int <= 0xffff_ffff_ffff_ffff, w <= 64;
    }
    let lo = ((len as u128 * (w as u128)) / nt as u128) as usize;
    let hi = ((len as u128 * (w as u128 + 1)) / nt as u128) as usize;
    let ctx = ctx0.copy();
    proof {
        ctx.lemma_same_wf(ctx0);
    }
    let rl = if h.fast { Vec::new() } else { chunk(h, perm, lo, hi) };
    let n = hi - lo;
    let ns = ctx0.ns;
    let capo: usize = 1024 + n / 4;
    let em = Emit { fm: true, sf: vec![0u64; ns / 64 + 1], out: vec![0usize; capo], cnt: 0, cap: capo, ovf: false, junk: 0 };
    proof {
        lemma_zero_bits(em.sf@, ns as int);
        assert forall|x: int| 0 <= x < ns && #[trigger] has(em, x) implies sl_s_qual(ctx0.sv@, ctx0.ps@, ctx0.d1g@, x) by {
            assert(!bit(em.sf@, x));
        }
    }
    let bcap: usize = 256;
    let nb: usize = 0;
    let tb: Vec<u64> = vec![0u64; 1];
    proof {
        lemma_zero_bits(tb@, (tb@.len() * 64) as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ns as int, 64);
    }
    let task = PartTask { ctx, rl, fast: h.fast, perm, a1: h.a1, b1: h.b1, a2: h.a2, b2: h.b2, q0: lo, n, em, ks: vec![0i64; bcap], sts: vec![0usize; bcap], tch: vec![0u64; bcap], bcap, tb, nb, w0: vec![0usize; bcap], w1: vec![0usize; bcap] };
    proof {
        assert(task.ctx.pp() == ctx0.pp() && task.ctx.pat() == ctx0.pat());
        assert(task.lst() =~= hl.subrange(lo as int, hi as int));
        assert forall|i: int| 0 <= i < n implies (#[trigger] task.lst()[i]) < task.ctx.np && hit_row(ctx0.pp(), ctx0.pat(), task.lst()[i] as int) by {
            assert(task.lst()[i] == hl[lo + i]);
        }
        assert(task.pre());
    }
    let ghost tg = task;
    let e = task.run();
    proof {
        assert(e.fm) by {
            assert(tg.post(e));
        }
    }
    (Ghost(tg), e)
}

/// The merged flags: exactly the qualifying supplier rows.
fn flags_of(outs: &Vec<Emit>, ns: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(d1): Ghost<int>,
    Ghost(ts): Ghost<Seq<PartTask>>) -> (g: Vec<u64>)
    requires
        sl_ok(sv),
        ns == tn(sv.suppliers, 13),
        ts.len() == outs@.len(),
        forall|w: int| 0 <= w < ts.len() ==> #[trigger] task_out(ts[w], outs@[w], sv, ps, d1, ns as int, tn(sv.suppliers, 0)),
        forall|w: int| 0 <= w < outs@.len() ==> !lost(#[trigger] outs@[w]),
        forall|r: int| 0 <= r < pi::n_rows(sv.part_nameidx) && #[trigger] hit_row(sv.part_nameidx, pat_of(ps), r)
            ==> covered_by(ts, r),
    ensures
        holds(g@, ns as int),
        forall|x: int| 0 <= x < ns ==> #[trigger] bit(g@, x) == sl_s_qual(sv, ps, d1, x),
{
    let ghost sp = sv.suppliers;
    proof {
        assert forall|i: int| 0 <= i < outs@.len() implies (#[trigger] outs@[i]).wf(ns as int) by {
            assert(task_out(ts[i], outs@[i], sv, ps, d1, ns as int, tn(sp, 0)));
        }
    }
    let g = run::merge(outs, ns);
    proof {
        assert forall|w: int| 0 <= w < ts.len() implies #[trigger] task_done(ts[w], outs@[w], sv, ps, d1, tn(sp, 13), tn(sp, 0)) by {
            assert(task_out(ts[w], outs@[w], sv, ps, d1, ns as int, tn(sp, 0)));
        }
        assert forall|x: int| 0 <= x < ns implies #[trigger] bit(g@, x) == sl_s_qual(sv, ps, d1, x) by {
            lemma_flags(sv, ps, d1, ts, outs@, x);
        }
    }
    g
}

/// The answer from the merged flags: the rows in supplier order (sorted if needed).
fn answer(stores: &mut Stores, g: &Vec<u64>, ns: usize, nt: usize, dispatch: &mut Dispatch, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(d1): Ghost<int>) -> (r: Result<Answer, QueryError>)
    requires
        1 <= nt <= MAX_WORKERS,
        sl_ok(old(stores)@),
        param_domain(ps), d1_ok(ps, d1),
        !(sl_outcome(old(stores)@, ps, d1) is Err),
        ns == tn(old(stores)@.suppliers, 13),
        holds(g@, ns as int),
        forall|x: int| 0 <= x < ns ==> #[trigger] bit(g@, x) == sl_s_qual(old(stores)@, ps, d1, x),
    ensures
        answer_meets(old(stores)@, ps, r),
{
    let ghost sv = stores@;
    let stx = load::supplier_text(stores);
    // one output task: build on the calling thread (no spawn, no piece copy)
    let built = if nt == 1 {
        run::build_output(g, ns, stx.sno, stx.snb, stx.sao, stx.sab, Ghost(sv), Ghost(ps), Ghost(d1))
    } else {
        match outp::par_output(g, ns, stx.sno, stx.snb, stx.sao, stx.sab, nt, dispatch, Ghost(sv), Ghost(ps), Ghost(d1)) {
            Ok(b) => b,
            Err(e) => return Err(QueryError::WorkerFailed(e)),
        }
    };
    let ghost rs = sel_rows(sv, ps, d1, ns as int);
    assert(sl_outcome(sv, ps, d1) == Ok::<Seq<Row>, SqlError>(rs));
    if built.sorted {
        let c = run::make_cols(built, Ghost(rs));
        proof {
            lemma_ok_columns(sv, ps, d1, c);
        }
        Ok(Answer::Columns(c))
    } else {
        let out = run::sorted_rows(&built.no, &built.nb, &built.ao, &built.ab, built.rows, Ghost(rs));
        proof {
            lemma_ok_rows(sv, ps, d1, out);
        }
        Ok(Answer::Rows(out))
    }
}

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
    proof {
        let db0 = choose|db: Database| bound_db(sv, db);
        lemma_bound(sv, db0);
    }
    let (d0, d1) = run::dates(params.p1, Ghost(ps));
    let ghost d1g = d1 as int;
    let nsl = load::nation_slices(stores);
    let natk = run::nation_keys(nsl.nk, nsl.nkb, nsl.nbs, nsl.noffs, nsl.nbytes, nsl.nn, params.p2, Ghost(sv.suppliers));
    let ctx0 = load::load_ctx(stores, Ghost(ps), d0, d1, natk);
    let psl = load::part_slices(stores);
    let np = psl.np;
    let ghost pp = sv.part_nameidx;
    // one worker: visit the matching parts in row order (sorted through a bit set over the part rows)
    let (hs, perr) = matches(&psl, params.p0, &ctx0, workers == 1);
    let ghost patv = params.p0@;
    let ns = ctx0.ns;
    let nps = ctx0.nps;
    let nn = nsl.nn;
    assert(perr == sl_part_err(sv.part_nameidx, patv));
    if perr && ns > 0 && nn > 0 && nps > 0 {
        proof {
            top::lemma_err(sv, ps, d1g);
        }
        return Ok(Answer::SqlError(SqlError::InvalidEscapeSequence));
    }
    // At most 32 tasks: beyond that, spawning costs more than the extra parallelism saves.
    let ntasks: usize = if workers > 32 { 32 } else { workers };
    let tasks = make_tasks(&ctx0, ntasks, &hs, psl.perm);
    let ghost ts = tasks@;
    proof {
        assert forall|i: int| 0 <= i < tasks@.len() implies #[trigger] tasks@[i].pre() by {
            assert(task_ok(tasks@[i], ctx0));
        }
    }
    let mut outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        assert forall|w: int| 0 <= w < ts.len() implies #[trigger] task_out(ts[w], outs@[w], sv, ps, d1g, ns as int, tn(sv.suppliers, 0)) by {
            assert(task_ok(ts[w], ctx0));
        }
    }
    // a task whose list overflowed runs again with a bit set
    let ghost mut ts2 = ts;
    let mut w: usize = 0;
    while w < ntasks
        invariant
            ctx0.wf(), ctx0.sv@ == sv, ctx0.ps@ == ps, ctx0.d1g@ == d1g, ns == ctx0.ns,
            1 <= ntasks <= MAX_WORKERS, w <= ntasks,
            outs@.len() == ntasks, ts2.len() == ntasks,
            hits_wf(&hs, psl.perm@), hits_ok(src_of(&hs, psl.perm@), ctx0.pp(), ctx0.pat()),
            forall|v: int| 0 <= v < ntasks ==> #[trigger] task_out(ts2[v], outs@[v], sv, ps, d1g, ns as int, tn(sv.suppliers, 0)),
            forall|v: int| 0 <= v < ntasks ==> (#[trigger] ts2[v]).lst() == ts[v].lst(),
            ts.len() == ntasks,
            forall|v: int| 0 <= v < ntasks ==> (#[trigger] ts[v]).lst()
                == src_of(&hs, psl.perm@).subrange(outp::yb(hs.len as int, v, ntasks as int), outp::yb(hs.len as int, v + 1, ntasks as int)),
            forall|v: int| 0 <= v < w ==> !lost(#[trigger] outs@[v]),
        decreases ntasks - w,
    {
        if outs[w].ovf && !outs[w].fm {
            let (tg, e) = rerun(&ctx0, &hs, psl.perm, ntasks, w);
            let ghost outs0 = outs@;
            outs.set(w, e);
            proof {
                assert(task_ok(tg@, ctx0));
                assert(ts[w as int].lst() == tg@.lst());
                ts2 = ts2.update(w as int, tg@);
                assert forall|v: int| 0 <= v < ntasks implies #[trigger] task_out(ts2[v], outs@[v], sv, ps, d1g, ns as int, tn(sv.suppliers, 0)) by {
                    if v != w {
                        assert(outs@[v] == outs0[v]);
                    }
                }
                assert forall|v: int| 0 <= v < w + 1 implies !lost(#[trigger] outs@[v]) by {
                    if v < w {
                        assert(outs@[v] == outs0[v]);
                    }
                }
            }
        }
        w = w + 1;
    }
    proof {
        assert forall|r: int| 0 <= r < pi::n_rows(sv.part_nameidx) && #[trigger] hit_row(sv.part_nameidx, pat_of(ps), r)
            implies covered_by(ts2, r) by {
            assert(covered_by(ts, r));
            let v = choose|v: int| 0 <= v < ts.len() && #[trigger] in_task(ts[v], r);
            assert(ts2[v].lst() == ts[v].lst());
            assert(in_task(ts2[v], r));
        }
    }
    let g = flags_of(&outs, ns, Ghost(sv), Ghost(ps), Ghost(d1g), Ghost(ts2));
    let nto: usize = if ntasks > 16 { 16 } else { ntasks };
    answer(stores, &g, ns, nto, dispatch, Ghost(ps), Ghost(d1g))
}

} // verus!
