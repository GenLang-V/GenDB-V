//! TPC-H Q13 (customer distribution) over the storages `custpart` (customer keys), `facts` (o_custkey through its
//! orders key index), `factext_trislice` (o_comment with 128-bit trigram signatures) and `orders_custidx` (an index of
//! orders on o_custkey: a directory whose entry lengths count the orders rows per key).
//!
//! c_count of the customer with key `k` is `total(k) - likes(k)`: the orders rows with o_custkey `k` minus those
//! whose o_comment matches `$1` (LIKE). Plan:
//! 1. phase 1 (`run`, `scan`): parallel over the orders rows, a row whose signature misses a bit the pattern needs
//!    cannot match; the other rows run the byte-level matcher (ASCII text) and the matching rows' o_custkey is
//!    gathered; non-ASCII candidates are decided on the calling thread with the general evaluator;
//! 2. phase 2 (`phase2`, `count`): parallel over the customer rows, `total(k)` from the directory minus the matches
//!    of `k`, as a histogram of c_count (a general serial path covers every other storage state);
//! 3. the histogram's pairs sorted by custdist DESC, c_count DESC.
//! The proof: `sql`, `group`, `outer` give the statement's meaning (LEFT JOIN, inner and outer GROUP BY, ORDER BY);
//! `bind` relates the storages to the database; `glue` and `answer` relate the phases' outputs to the meaning.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::{QueryError, WorkerFailure};
use crate::gendb_params::Params;
use crate::query::{param_domain, param_typed, query_spec_at};
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::fns::like::*;
use crate::spec::limits::*;
use crate::exec::value::*;
use crate::link::expr::ival;
use crate::link::query::{view_rows, gcount};
use crate::stores::factext_trislice::interface::common::colfmt as TXC;
use crate::stores::facts::interface::common::colfmt as FAC;
use crate::stores::custpart::interface::common::colfmt as CPC;
use crate::stores::orders_custidx::interface as IX;
use crate::stores::factext_trislice::interface as TX;
use crate::stores::factext_trislice::interface::trisig::sig_of;

pub mod like;
pub mod scan;
pub mod count;
pub mod glue;
pub mod run;
pub mod phase2;
pub mod sql;
pub mod group;
pub mod outer;
pub mod bind;
pub mod answer;
pub mod common;

use like::*;
use scan::*;
use count::*;
use glue::*;
use run::*;
use phase2::*;
use sql::*;
use group::*;
use outer::*;
use bind::*;
use answer::*;
use common::partition::*;

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

/// The views the query computed with describe database `db`: row counts, comments, o_custkey (`kf`), customer
/// keys.
pub open spec fn env_ok(db: Database, x: ScanCtx, kf: spec_fn(int) -> int, n_o: int, n_c: int, cc: Seq<u32>, cb: Seq<i64>,
    cbs: int) -> bool {
    &&& db_facts(db)
    &&& otab(db).len() == n_o
    &&& ctab(db).len() == n_c
    &&& forall|r: int| 0 <= r < n_o ==> #[trigger] rtext(x, r) == otext(otab(db)[r])
    &&& forall|r: int| 0 <= r < n_o ==> #[trigger] kf(r) == okv(db, r)
    &&& forall|i: int| 0 <= i < n_c ==> #[trigger] ckey(cc, cb, cbs, i) == ival(ctab(db)[i][0])
}

/// On every database the views describe, the matcher's outcomes are the statement's.
proof fn lemma_like_eq(db: Database, ps: Seq<Literal>, x: ScanCtx, kf: spec_fn(int) -> int, n_o: int, n_c: int,
    cc: Seq<u32>, cb: Seq<i64>, cbs: int, r: int)
    requires
        env_ok(db, x, kf, n_o, n_c, cc, cb, cbs),
        x.p == toks_of(ps),
        0 <= r < n_o,
    ensures
        like_r(x, r) == olike(otab(db)[r], ps),
        err_r(x, r) == (ores(otab(db)[r], ps) is Err),
{
    assert(rtext(x, r) == otext(otab(db)[r]));
}

/// The orders rows per key, as a function.
pub open spec fn totf(kf: spec_fn(int) -> int, n: int) -> spec_fn(int) -> int {
    |v: int| vcount(kf, v, 0, n) as int
}

/// The matches of key `v` are at most the rows of key `v`.
proof fn lemma_like_le(x: ScanCtx, kf: spec_fn(int) -> int, v: int, a: int, b: int)
    requires a <= b,
    ensures cnt(pr_like(x, kf, v), a, b) <= vcount(kf, v, a, b),
    decreases b - a,
{
    if b > a {
        lemma_like_le(x, kf, v, a, b - 1);
    }
}

/// The SQL error answer: some comment makes the matcher raise and there is a customer.
proof fn lemma_final_err(sv: StoresView, ps: Seq<Literal>, x: ScanCtx, kf: spec_fn(int) -> int, n_o: int, n_c: int,
    cc: Seq<u32>, cb: Seq<i64>, cbs: int)
    requires
        param_typed(ps),
        x.p == toks_of(ps),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> env_ok(db, x, kf, n_o, n_c, cc, cb, cbs),
        cnt(pr_e(x), 0, n_o) > 0,
        n_c > 0,
    ensures
        answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(SqlError::InvalidEscapeSequence))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(SqlError::InvalidEscapeSequence))) by {
        lemma_cnt_pos(pr_e(x), 0, n_o);
        let r = choose|r: int| 0 <= r < n_o && #[trigger] pr_e(x)(r);
        lemma_like_eq(db, ps, x, kf, n_o, n_c, cc, cb, cbs, r);
        assert(some_err(db, ps));
        lemma_lj_err(db, ps);
        lemma_body_err_lj(db, ps, SqlError::InvalidEscapeSequence);
    }
}

/// Per customer row, the computed value `f(i) = total(k) - likes(k)` is c_count.
proof fn lemma_f_ccnt(sv: StoresView, ps: Seq<Literal>, x: ScanCtx, kf: spec_fn(int) -> int, n_o: int, n_c: int,
    cc: Seq<u32>, cb: Seq<i64>, cbs: int, lists: Seq<Vec<i64>>, tot: spec_fn(int) -> int, f: spec_fn(int) -> int)
    requires
        x.p == toks_of(ps),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> env_ok(db, x, kf, n_o, n_c, cc, cb, cbs),
        forall|v: int| #[trigger] likes(lists, v) == cnt(pr_like(x, kf, v), 0, n_o),
        tot == totf(kf, n_o),
        forall|i: int| 0 <= i < n_c ==> #[trigger] f(i) == tot(ckey(cc, cb, cbs, i)) - likes(lists, ckey(cc, cb, cbs, i)),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] f(i) == ccnt(db, ps, i),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] f(i) == ccnt(db, ps, i) by {
        assert forall|i: int| 0 <= i < ctab(db).len() implies #[trigger] f(i) == ccnt(db, ps, i) by {
            let k = ckey(cc, cb, cbs, i);
            assert(k == ival(ctab(db)[i][0]));
            assert(env_ok(db, x, kf, n_o, n_c, cc, cb, cbs));
            lemma_ccnt(db, ps, i);
            assert forall|q: int| 0 <= q < n_o implies #[trigger] pr_like(x, kf, k)(q) == pr_olk(db, ps, k)(q) by {
                lemma_like_eq(db, ps, x, kf, n_o, n_c, cc, cb, cbs, q);
                assert(kf(q) == okv(db, q));
            }
            lemma_cnt_ext(pr_like(x, kf, k), pr_olk(db, ps, k), 0, n_o);
            assert forall|q: int| 0 <= q < n_o implies #[trigger] veq(kf, k)(q) == veq(okvf(db), k)(q) by {
                assert(kf(q) == okv(db, q));
            }
            lemma_cnt_ext(veq(kf, k), veq(okvf(db), k), 0, n_o);
        }
    }
}

/// The answer from the pairs: the rows, or 22003 when a c_count or a custdist leaves bigint.
proof fn lemma_final_pairs(sv: StoresView, ps: Seq<Literal>, x: ScanCtx, kf: spec_fn(int) -> int, n_o: int, n_c: int,
    cc: Seq<u32>, cb: Seq<i64>, cbs: int, f: spec_fn(int) -> int, pairs: Seq<(u64, u64)>, r: Result<Answer, QueryError>,
    sorted: Seq<(u64, u64)>)
    requires
        param_typed(ps),
        x.p == toks_of(ps),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> env_ok(db, x, kf, n_o, n_c, cc, cb, cbs),
        !(n_c > 0 && cnt(pr_e(x), 0, n_o) > 0),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] f(i) == ccnt(db, ps, i),
        pairs_ok(pairs, f, n_c),
        match r {
            Ok(Answer::SqlError(e)) => e == SqlError::NumericValueOutOfRange && exists|j: int| 0 <= j < pairs.len()
                && (#[trigger] pairs[j].0 > i64::MAX || pairs[j].1 > i64::MAX),
            Ok(Answer::Rows(rows)) => {
                &&& forall|j: int| 0 <= j < pairs.len() ==> #[trigger] pairs[j].0 <= i64::MAX && pairs[j].1 <= i64::MAX
                &&& sorted.len() == pairs.len()
                &&& forall|e: (u64, u64)| #[trigger] sorted.contains(e) <==> pairs.contains(e)
                &&& forall|j1: int, j2: int| 0 <= j1 < sorted.len() && 0 <= j2 < sorted.len() && j1 != j2 ==>
                        #[trigger] sorted[j1].0 != #[trigger] sorted[j2].0
                &&& forall|j1: int, j2: int| 0 <= j1 < j2 < sorted.len() ==> before(#[trigger] sorted[j1], #[trigger] sorted[j2])
                &&& view_rows(rows@) == sorted.map_values(|e: (u64, u64)| prow(e))
            },
            _ => false,
        },
    ensures
        answer_meets(sv, ps, r),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), r) by {
        assert(env_ok(db, x, kf, n_o, n_c, cc, cb, cbs));
        if some_err(db, ps) && n_c > 0 {
            let r0 = choose|r0: int| 0 <= r0 < otab(db).len() && #[trigger] ores(otab(db)[r0], ps) is Err;
            lemma_like_eq(db, ps, x, kf, n_o, n_c, cc, cb, cbs, r0);
            assert(pr_e(x)(r0));
            lemma_cnt_at(pr_e(x), 0, n_o, r0);
        }
        match r {
            Ok(Answer::Rows(rows)) => {
                lemma_rows_ok(db, ps, f, pairs, sorted, rows@);
            },
            _ => {
                if exists|j2: int| 0 <= j2 < pairs.len() && #[trigger] pairs[j2].0 > i64::MAX {
                    let j2 = choose|j2: int| 0 <= j2 < pairs.len() && #[trigger] pairs[j2].0 > i64::MAX;
                    let c2 = pairs[j2].0 as int;
                    assert(vcount(f, c2, 0, n_c) > 0);
                    let i = lemma_vcount_pos(f, c2, 0, n_c);
                    lemma_inner_overflow(db, ps, i);
                    lemma_body_err_inner(db, ps, SqlError::NumericValueOutOfRange);
                } else {
                    let j = choose|j: int| 0 <= j < pairs.len() && (#[trigger] pairs[j].0 > i64::MAX || pairs[j].1 > i64::MAX);
                    let c = pairs[j].0 as int;
                    assert forall|i: int| 0 <= i < ctab(db).len() implies #[trigger] ccnt(db, ps, i) <= int8_max() by {
                        lemma_vcount_at(f, f(i), 0, n_c, i);
                        let j3 = choose|j3: int| 0 <= j3 < pairs.len() && pairs[j3].0 as int == f(i);
                        assert(!(pairs[j3].0 > i64::MAX));
                    }
                    lemma_gcount_f(db, ps, f, c);
                    lemma_outer_overflow(db, ps, c);
                    lemma_statement(ps);
                }
            },
        }
    }
}

/// For a bound database: the views describe it.
proof fn lemma_env(sv: StoresView, db: Database, db0: Database, x: ScanCtx, kf: spec_fn(int) -> int, gather: bool,
    keyc: Seq<i64>, n_o: int, n_c: int, cc: Seq<u32>, cb: Seq<i64>, cbs: int, obs: int)
    requires
        bound_db(sv, db),
        bound_db(sv, db0),
        bind_ok(sv, db),
        bind_ok(sv, db0),
        n_o == TXC::u64s(sv.factext_trislice[12]).len() / 2,
        n_c == CPC::u32s(sv.custpart[2]).len(),
        x.offs == TXC::u64s(sv.factext_trislice[10]), x.bytes == TXC::u8s(sv.factext_trislice[11]),
        x.ic == FAC::u32s(sv.facts[71]), x.ib == FAC::u64s(sv.facts[72]),
        x.kc == FAC::u32s(sv.facts[54]), x.kb == FAC::i64s(sv.facts[55]),
        x.bs == obs, obs >= 1,
        forall|i: int| 0 <= i < n_o ==> #[trigger] (i / obs) == i / (FAC::u64s(sv.facts[48])[1] as int),
        gather == (FAC::u64s(sv.facts[73])[0] == 2),
        cc == CPC::u32s(sv.custpart[2]), cb == CPC::i64s(sv.custpart[3]),
        cbs >= 1,
        forall|i: int| 0 <= i < n_c ==> #[trigger] (i / cbs) == i / (CPC::u64s(sv.custpart[0])[1] as int),
        gather ==> kf == okf(x),
        !gather ==> kf == kcf(keyc),
        !gather ==> keyc.len() == n_o && forall|r: int| 0 <= r < n_o ==> #[trigger] idxrel(db0)[r][0] == Val::Int(keyc[r] as int),
    ensures
        env_ok(db, x, kf, n_o, n_c, cc, cb, cbs),
{
    assert(otab(db).len() == n_o);
    assert forall|r: int| 0 <= r < n_o implies #[trigger] rtext(x, r) == otext(otab(db)[r]) by {}
    if gather {
        let bs = FAC::u64s(sv.facts[48])[1] as int;
        assert forall|r: int| 0 <= r < n_o implies #[trigger] kf(r) == okv(db, r) by {
            assert(orow_ok(sv.facts, db, r));
            let s = fsrow(x.ic, x.ib, bs, r);
            assert(r / obs == r / bs);
            assert(s / obs == s / bs);
            assert(srow(x, r) == s);
        }
    } else {
        let rel_a = crate::stores::orders_custidx::declaration::stored_relations(db0);
        let rel_b = crate::stores::orders_custidx::declaration::stored_relations(db);
        assert(IX::represents(sv.orders_custidx, rel_a));
        assert(IX::represents(sv.orders_custidx, rel_b));
        IX::lemma_represents_determines(sv.orders_custidx, rel_a, rel_b);
        assert forall|r: int| 0 <= r < n_o implies #[trigger] kf(r) == okv(db, r) by {
            assert(idxrel(db)[r][0] == otab(db)[r][1]);
        }
    }
    assert forall|i: int| 0 <= i < n_c implies #[trigger] ckey(cc, cb, cbs, i) == ival(ctab(db)[i][0]) by {
        assert(crow_ok(sv.custpart, db, i));
        assert(i / cbs == i / (CPC::u64s(sv.custpart[0])[1] as int));
    }
}

/// The facts the scan and the list collection need, from a bound database.
proof fn lemma_scan_facts(sv: StoresView, db0: Database, x: ScanCtx, kf: spec_fn(int) -> int, gather: bool,
    keyc: Seq<i64>, n_o: int, pat: Seq<u8>, dang: bool, obs: int)
    requires
        bind_ok(sv, db0),
        n_o == otab(db0).len(),
        x.sig == TXC::u64s(sv.factext_trislice[12]),
        x.offs == TXC::u64s(sv.factext_trislice[10]), x.bytes == TXC::u8s(sv.factext_trislice[11]),
        x.ic == FAC::u32s(sv.facts[71]), x.ib == FAC::u64s(sv.facts[72]),
        x.kc == FAC::u32s(sv.facts[54]), x.kb == FAC::i64s(sv.facts[55]),
        x.bs == obs, obs >= 1,
        forall|i: int| 0 <= i < n_o ==> #[trigger] (i / obs) == i / (FAC::u64s(sv.facts[48])[1] as int),
        gather == (FAC::u64s(sv.facts[73])[0] == 2),
        codes_ok(x.codes, x.p),
        x.p == pat_toks(pat),
        dang == has_dang(x.codes),
        x.need0 == (if dang { 0u64 } else { need_of(x.codes, 0) }),
        x.need1 == (if dang { 0u64 } else { need_of(x.codes, 1) }),
        gather ==> kf == okf(x),
        !gather ==> kf == kcf(keyc),
        !gather ==> keyc.len() == n_o,
    ensures
        ctx_ok(x, n_o, gather),
        collect_pre(x, n_o, gather, kf, keyc, pat),
{
    let db = db0;
    assert(text_ok(sv.factext_trislice, db));
    assert forall|r: int| 0 <= r < n_o implies x.sig[2 * r] == sig_of(#[trigger] rtext(x, r), 0) && x.sig[2 * r + 1] == sig_of(rtext(x, r), 1) by {
        assert(otext(otab(db)[r]) == TXC::text_of(x.offs, x.bytes, r));
    }
    if gather {
        let bs = FAC::u64s(sv.facts[48])[1] as int;
        assert(okeys_ok(sv.facts, db));
        assert forall|r: int| 0 <= r < n_o implies #[trigger] key_readable(x, n_o, r) by {
            assert(orow_ok(sv.facts, db, r));
            let s = fsrow(x.ic, x.ib, bs, r);
            assert(r / obs == r / bs);
            assert(s / obs == s / bs);
            assert(srow(x, r) == s);
        }
        assert forall|r: int| 0 <= r < n_o implies i64::MIN <= #[trigger] kf(r) <= i64::MAX by {
            assert(key_readable(x, n_o, r));
        }
    }
}

/// The orders rows per key `tot(v)`: by the directory, or by the stored keys.
proof fn lemma_tot(sv: StoresView, db0: Database, x: ScanCtx, kf: spec_fn(int) -> int, dir: bool, offs: Seq<u32>, kmin: int,
    nk: int, keys0: Seq<i64>, n_o: int, n_c: int, cc: Seq<u32>, cb: Seq<i64>, cbs: int, tot: spec_fn(int) -> int)
    requires
        bind_ok(sv, db0),
        env_ok(db0, x, kf, n_o, n_c, cc, cb, cbs),
        dir == (IX::idx_i64s(sv.orders_custidx[0])[0] == IX::MODE_DIRECTORY),
        offs == IX::idx_u32s(sv.orders_custidx[1]),
        kmin == IX::idx_i64s(sv.orders_custidx[0])[1] as int,
        dir ==> nk == offs.len() - 1,
        keys0 == IX::idx_i64s(sv.orders_custidx[3]),
        tot == totf(kf, n_o),
    ensures
        tot_ok(dir, offs, kmin, nk, keys0, n_o, tot),
{
    let db = db0;
    assert(index_ok(sv.orders_custidx, db));
    if dir {
        assert(IX::directory_ok(kmin, nk, offs, IX::idx_u32s(sv.orders_custidx[2]), idxrel(db)));
        assert forall|v: int| #[trigger] dtotal(offs, kmin, nk, v) == tot(v) by {
            lemma_dtotal(db, sv.orders_custidx, v);
            assert forall|q: int| 0 <= q < n_o implies #[trigger] veq(okvf(db), v)(q) == veq(kf, v)(q) by {
                assert(kf(q) == okv(db, q));
            }
            lemma_cnt_ext(veq(okvf(db), v), veq(kf, v), 0, n_o);
        }
    } else {
        assert forall|v: int| #![trigger tot(v)] vcount(kcf(keys0), v, 0, n_o) == tot(v) by {
            assert forall|q: int| 0 <= q < n_o implies #[trigger] veq(kcf(keys0), v)(q) == veq(kf, v)(q) by {
                assert(kf(q) == okv(db, q));
                assert(idxrel(db)[q][0] == otab(db)[q][1]);
            }
            lemma_cnt_ext(veq(kcf(keys0), v), veq(kf, v), 0, n_o);
        }
    }
}

/// The customer keys are readable.
proof fn lemma_ckeys(sv: StoresView, db0: Database, x: ScanCtx, kf: spec_fn(int) -> int, n_o: int, n_c: int, cc: Seq<u32>,
    cb: Seq<i64>, cbs: int)
    requires
        bind_ok(sv, db0),
        env_ok(db0, x, kf, n_o, n_c, cc, cb, cbs),
        cc == CPC::u32s(sv.custpart[2]), cb == CPC::i64s(sv.custpart[3]),
        cbs >= 1,
        forall|i: int| 0 <= i < n_c ==> #[trigger] (i / cbs) == i / (CPC::u64s(sv.custpart[0])[1] as int),
    ensures
        ckeys_ok(cc, cb, cbs, n_c),
{
    assert forall|i: int| 0 <= i < n_c implies #[trigger] (i / cbs) < cb.len() by {
        assert(crow_ok(sv.custpart, db0, i));
    }
}

/// The key of every orders row from the index storage (see `canon_keys`).
fn canon_keys_of(dir: bool, kmin: i64, offs: &[u32], perm: &[u32], keys0: &[i64], n: usize,
    Ghost(p): Ghost<Seq<crate::gendb_entry::layout::PartView>>, Ghost(db): Ghost<Database>) -> (keyc: Vec<i64>)
    requires
        canon_pre(p, db),
        dir == (IX::idx_i64s(p[0])[0] == IX::MODE_DIRECTORY),
        kmin == IX::idx_i64s(p[0])[1],
        offs@ == IX::idx_u32s(p[1]), perm@ == IX::idx_u32s(p[2]), keys0@ == IX::idx_i64s(p[3]),
        n == otab(db).len(),
    ensures
        keyc@.len() == n,
        forall|r: int| 0 <= r < n ==> #[trigger] idxrel(db)[r][0] == Val::Int(keyc@[r] as int),
{
    canon_keys(dir, kmin, offs, perm, keys0, n, Ghost(idxrel(db)))
}

/// The bit-sliced signatures (parts 13, 14 of factext_trislice) and the planes of the needed bits `need0`, `need1`.
fn slice_args(stores: &mut Stores, n_o: usize, need0: u64, need1: u64, Ghost(x): Ghost<ScanCtx>, Ghost(db0): Ghost<Database>)
    -> (sl: SliceArgs)
    requires
        bound_db(old(stores)@, db0),
        n_o == otab(db0).len(),
        x.sig == TXC::u64s(old(stores)@.factext_trislice[12]),
        x.need0 == need0,
        x.need1 == need1,
    ensures
        final(stores)@ == old(stores)@,
        slice_args_ok(&sl, x, n_o as int),
{
    let ghost sv = stores@;
    let ghost pt = sv.factext_trislice;
    proof {
        lemma_bind(sv, db0);
        assert(TX::slices_ok(pt, n_o as int));
        assert(TX::slice_half_ok(pt, n_o as int, 0));
        assert(TX::slice_half_ok(pt, n_o as int, 1));
    }
    let nsl = stores.factext_trislice.part_len(13);
    let sl0 = stores.factext_trislice.extent_u64(13, 0, nsl);
    let sl1 = stores.factext_trislice.extent_u64(14, 0, nsl);
    let nw: usize = n_o / 64 + if n_o % 64 == 0 { 0 } else { 1 };
    let pq = need_planes(need0, need1);
    let sl = SliceArgs { sl0, sl1, nsl, nw, pq };
    proof {
        assert(sl0@ =~= TXC::u64s(pt[13]));
        assert(sl1@ =~= TXC::u64s(pt[14]));
        assert(nw as int == TX::plane_words(n_o as int));
        assert(TX::slices_ok(pt, n_o as int));
        assert(TX::slice_half_ok(pt, n_o as int, 0));
        assert(TX::slice_half_ok(pt, n_o as int, 1));
        reveal(sl_ok);
        assert(sl_ok(x, sl0@, sl1@, nw as int, n_o as int));
        reveal(slice_args_ok);
    }
    sl
}

/// TPC-H Q13.
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    hide(bind_ok);
    hide(collect_pre);
    hide(ctx_ok);
    hide(tot_ok);
    hide(canon_pre);
    hide(ranges_ok);
    hide(bounds_ok);
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    assert(shape_ok(sv, db0) && canon_pre(sv.orders_custidx, db0) && db_facts(db0)) by {
        lemma_bind(sv, db0);
        lemma_shape(sv, db0);
        lemma_canon_pre(sv, db0);
    }
    let pat = copy_bytes(params.p0, 0, params.p0.len());
    proof {
        assert(params.p0@.subrange(0, params.p0@.len() as int) =~= params.p0@);
        assert(pat_of(ps) == pat@);
    }

    // ---- orders text and signatures (factext_trislice), two signature words per row.
    let ghost pt = sv.factext_trislice;
    let n_o = stores.factext_trislice.part_len(12) / 2;
    assert(n_o == otab(db0).len());
    let sig = stores.factext_trislice.extent_u64(12, 0, 2 * n_o);
    let offs = stores.factext_trislice.extent_u64(10, 0, n_o + 1);
    let nbytes = stores.factext_trislice.part_len(11);
    let bytes = stores.factext_trislice.extent_u8(11, 0, nbytes);
    proof {
        assert(sig@ =~= TXC::u64s(pt[12]));
        assert(offs@ =~= TXC::u64s(pt[10]));
        assert(bytes@ =~= TXC::u8s(pt[11]));
    }

    // ---- the pattern.
    let (codes, toks) = pattern_codes(&pat);
    let dang = has_dangling(&codes);
    let (need0, need1): (u64, u64) = if dang { (0, 0) } else { need_mask(&codes) };

    // ---- o_custkey through the facts orders key index (kind 2), else from the index storage.
    let ghost pf = sv.facts;
    let olay = stores.facts.extent_u64(48, 0, 2);
    let okind = stores.facts.extent_u64(73, 0, 1);
    proof {
        assert(olay@ =~= FAC::u64s(pf[48]));
        assert(okind@ =~= FAC::u64s(pf[73]));
    }
    let obs = eff_bs(olay[1], n_o);
    let gather = okind[0] == 2;
    let nic = stores.facts.part_len(71);
    let nib = stores.facts.part_len(72);
    let nkc = stores.facts.part_len(54);
    let nkb = stores.facts.part_len(55);
    let ic = stores.facts.extent_u32(71, 0, nic);
    let ib = stores.facts.extent_u64(72, 0, nib);
    let kc = stores.facts.extent_u32(54, 0, nkc);
    let kb = stores.facts.extent_i64(55, 0, nkb);
    proof {
        assert(ic@ =~= FAC::u32s(pf[71]));
        assert(ib@ =~= FAC::u64s(pf[72]));
        assert(kc@ =~= FAC::u32s(pf[54]));
        assert(kb@ =~= FAC::i64s(pf[55]));
    }
    let ghost x = mk_ctx(sig@, offs@, bytes@, codes@, toks@, need0, need1, ic@, ib@, kc@, kb@, obs as int);

    // ---- the index storage.
    let ghost pi = sv.orders_custidx;
    let meta = stores.orders_custidx.extent_i64(0, 0, 2);
    let nofs = stores.orders_custidx.part_len(1);
    let doffs = stores.orders_custidx.extent_u32(1, 0, nofs);
    let nperm = stores.orders_custidx.part_len(2);
    let perm = stores.orders_custidx.extent_u32(2, 0, nperm);
    let nkeys = stores.orders_custidx.part_len(3);
    let keys0 = stores.orders_custidx.extent_i64(3, 0, nkeys);
    proof {
        assert(meta@ =~= IX::idx_i64s(pi[0]));
        assert(doffs@ =~= IX::idx_u32s(pi[1]));
        assert(perm@ =~= IX::idx_u32s(pi[2]));
        assert(keys0@ =~= IX::idx_i64s(pi[3]));
    }
    let dir = meta[0] == IX::MODE_DIRECTORY;
    let kmin = meta[1];
    let nk: usize = if nofs >= 1 { nofs - 1 } else { 0 };

    // The canonical keys from the index storage (only without the facts key index).
    let keyc: Vec<i64> = if gather {
        Vec::new()
    } else {
        canon_keys_of(dir, kmin, doffs, perm, keys0, n_o, Ghost(pi), Ghost(db0))
    };
    let ghost kf: spec_fn(int) -> int = if gather { okf(x) } else { kcf(keyc@) };

    // ---- customers (custpart).
    let ghost pc = sv.custpart;
    let n_c = stores.custpart.part_len(2);
    let clay = stores.custpart.extent_u64(0, 0, 2);
    let ckind = stores.custpart.extent_u64(20, 0, 1);
    let ncb = stores.custpart.part_len(3);
    let cc = stores.custpart.extent_u32(2, 0, n_c);
    let cb = stores.custpart.extent_i64(3, 0, ncb);
    proof {
        assert(clay@ =~= CPC::u64s(pc[0]));
        assert(ckind@ =~= CPC::u64s(pc[20]));
        assert(cc@ =~= CPC::u32s(pc[2]));
        assert(cb@ =~= CPC::i64s(pc[3]));
    }
    let cbs = eff_bs(clay[1], n_c);

    // The views describe every bound database.
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies env_ok(db, x, kf, n_o as int, n_c as int, cc@, cb@, cbs as int) by {
            lemma_bind(sv, db);
            lemma_bind(sv, db0);
            lemma_env(sv, db, db0, x, kf, gather, keyc@, n_o as int, n_c as int, cc@, cb@, cbs as int, obs as int);
        }
        assert(ctx_ok(x, n_o as int, gather) && collect_pre(x, n_o as int, gather, kf, keyc@, pat@)) by {
            lemma_bind(sv, db0);
            lemma_scan_facts(sv, db0, x, kf, gather, keyc@, n_o as int, pat@, dang, obs as int);
        }
    }

    // ---- phase 1 (its key lists cut into the key ranges of the phase-2 chunks).
    let k2: usize = if n_c / 65536 + 1 < workers { n_c / 65536 + 1 } else { workers };
    let (blo, bhi) = phase2_ranges(cc, cb, cbs, n_c, k2);
    let k1: usize = if n_o / 65536 + 1 < workers { n_o / 65536 + 1 } else { workers };
    let bounds = make_bounds(n_o, k1);
    let sl = slice_args(stores, n_o, need0, need1, Ghost(x), Ghost(db0));
    let outs = match run_scan(sig, offs, bytes, nbytes, &codes, need0, need1, ic, ib, kc, kb, obs, n_o, gather, &bounds, k1, toks, dispatch,
        &blo, &bhi, &sl) {
        Ok(o) => o,
        Err(f) => return Err(QueryError::WorkerFailed(f)),
    };
    let (lists, any_err, boffs, parts) = collect_lists(outs, k1, &bounds, offs, bytes, &pat, gather, ic, ib, kc, kb, obs, &keyc, n_o,
        Ghost(x), Ghost(kf), Ghost(blo@), Ghost(bhi@));
    if any_err && n_c > 0 {
        proof {
            lemma_final_err(sv, ps, x, kf, n_o as int, n_c as int, cc@, cb@, cbs as int);
        }
        return Ok(Answer::SqlError(SqlError::InvalidEscapeSequence));
    }

    // ---- phase 2: the (c_count, custdist) pairs.
    let ghost tot: spec_fn(int) -> int = totf(kf, n_o as int);
    proof {
        assert forall|v: int| #![trigger tot(v)] 0 <= likes(lists@, v) <= tot(v) <= n_o by {
            lemma_like_le(x, kf, v, 0, n_o as int);
            lemma_cnt_le(veq(kf, v), 0, n_o as int);
        }
        assert(tot_ok(dir, doffs@, kmin as int, nk as int, keys0@, n_o as int, tot)) by {
            lemma_bind(sv, db0);
            lemma_tot(sv, db0, x, kf, dir, doffs@, kmin as int, nk as int, keys0@, n_o as int, n_c as int, cc@, cb@, cbs as int, tot);
        }
        lemma_bind(sv, db0);
        lemma_ckeys(sv, db0, x, kf, n_o as int, n_c as int, cc@, cb@, cbs as int);
    }
    let ghost lv = lists@;
    let (pairs, Ghost(f)) = match phase2_pairs(cc, cb, cbs, n_c, lists, boffs, parts, &blo, &bhi, dir, doffs, kmin, nk, keys0,
        n_o, ckind[0] == 1, workers, dispatch, Ghost(tot)) {
        Ok(v) => v,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_f_ccnt(sv, ps, x, kf, n_o as int, n_c as int, cc@, cb@, cbs as int, lv, tot, f);
    }
    finish(&pairs, Ghost(sv), Ghost(ps), Ghost(x), Ghost(kf), Ghost(n_o as int), Ghost(n_c as int), Ghost(cc@), Ghost(cb@),
        Ghost(cbs as int), Ghost(f))
}

/// Phase 2: the (c_count, custdist) pairs, by the parallel histograms when the storages allow, else serially.
fn phase2_pairs(cc: &'static [u32], cb: &'static [i64], cbs: usize, n_c: usize, lists: Vec<Vec<i64>>,
    boffs: Vec<Vec<usize>>, parts: Vec<bool>, blo: &Vec<i64>, bhi: &Vec<i64>, dir: bool,
    doffs: &'static [u32], kmin: i64, nk: usize, keys0: &[i64], n_o: usize, sorted_keys: bool, workers: usize,
    dispatch: &mut Dispatch, Ghost(tot): Ghost<spec_fn(int) -> int>)
    -> (r: Result<(Vec<(u64, u64)>, Ghost<spec_fn(int) -> int>), WorkerFailure>)
    requires
        1 <= workers <= MAX_WORKERS,
        ranges_ok(blo@, bhi@),
        cuts_ok(lists@, boffs@, parts@, blo@, bhi@),
        ckeys_ok(cc@, cb@, cbs as int, n_c as int),
        tot_ok(dir, doffs@, kmin as int, nk as int, keys0@, n_o as int, tot),
        forall|v: int| #![trigger tot(v)] 0 <= likes(lists@, v) <= tot(v) <= n_o,
    ensures
        r matches Ok(v) ==> {
            &&& pairs_ok(v.0@, v.1@, n_c as int)
            &&& forall|i: int| 0 <= i < n_c ==> #[trigger] (v.1@)(i) == tot(ckey(cc@, cb@, cbs as int, i))
                    - likes(lists@, ckey(cc@, cb@, cbs as int, i))
        },
{
    let ghost lv = lists@;
    proof {
        reveal(cuts_ok);
    }
    let shared = Arc::new(lists);
    if dir && sorted_keys && (kmin as i128) + (nk as i128) <= i64::MAX as i128 {
        let k2: usize = if n_c / 65536 + 1 < workers { n_c / 65536 + 1 } else { workers };
        let sb = Arc::new(boffs);
        let sp = Arc::new(parts);
        match run_counts(cc, cb, cbs, n_c, &shared, doffs, kmin, nk, k2, dispatch, &sb, &sp, blo, bhi) {
            Ok(Some(h)) => {
                let ghost f = ccf(cc@, cb@, cbs as int, doffs@, kmin as int, nk as int, lv);
                let pairs = pairs_from_hist(&h, Ghost(f), Ghost(n_c as int));
                return Ok((pairs, Ghost(f)));
            },
            Ok(None) => {},
            Err(e) => return Err(e),
        }
    }
    let cv = general_counts(cc, cb, cbs, n_c, &*shared, dir, doffs, kmin, nk, keys0, n_o, Ghost(tot));
    let pairs = pairs_from_vals(&cv);
    Ok((pairs, Ghost(ucf(cv@))))
}

/// Whether every pair's values are bigints.
fn pairs_fit(pairs: &Vec<(u64, u64)>) -> (ok: bool)
    ensures
        ok == forall|j: int| 0 <= j < pairs@.len() ==> #[trigger] pairs@[j].0 <= i64::MAX && pairs@[j].1 <= i64::MAX,
{
    let mut j: usize = 0;
    while j < pairs.len()
        invariant
            j <= pairs@.len(),
            forall|j2: int| 0 <= j2 < j ==> #[trigger] pairs@[j2].0 <= i64::MAX && pairs@[j2].1 <= i64::MAX,
        decreases pairs@.len() - j,
    {
        if pairs[j].0 > i64::MAX as u64 || pairs[j].1 > i64::MAX as u64 {
            assert(!(pairs@[j as int].0 <= i64::MAX && pairs@[j as int].1 <= i64::MAX));
            return false;
        }
        j = j + 1;
    }
    true
}

/// Values beyond bigint are 22003; otherwise the sorted rows.
fn finish(pairs: &Vec<(u64, u64)>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(x): Ghost<ScanCtx>,
    Ghost(kf): Ghost<spec_fn(int) -> int>, Ghost(n_o): Ghost<int>, Ghost(n_c): Ghost<int>, Ghost(cc): Ghost<Seq<u32>>,
    Ghost(cb): Ghost<Seq<i64>>, Ghost(cbs): Ghost<int>, Ghost(f): Ghost<spec_fn(int) -> int>) -> (r: Result<Answer, QueryError>)
    requires
        param_typed(ps),
        x.p == toks_of(ps),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> env_ok(db, x, kf, n_o, n_c, cc, cb, cbs),
        !(n_c > 0 && cnt(pr_e(x), 0, n_o) > 0),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] f(i) == ccnt(db, ps, i),
        pairs_ok(pairs@, f, n_c),
    ensures
        answer_meets(sv, ps, r),
{
    if !pairs_fit(pairs) {
        let r = Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
        proof {
            lemma_final_pairs(sv, ps, x, kf, n_o, n_c, cc, cb, cbs, f, pairs@, r, Seq::empty());
        }
        return r;
    }
    let (rows, sorted) = output_rows(pairs);
    let r = Ok(Answer::Rows(rows));
    proof {
        lemma_final_pairs(sv, ps, x, kf, n_o, n_c, cc, cb, cbs, f, pairs@, r, sorted@);
    }
    r
}

} // verus!
