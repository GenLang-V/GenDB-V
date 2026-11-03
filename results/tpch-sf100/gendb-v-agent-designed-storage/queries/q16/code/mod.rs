//! TPC-H Q16 (parts/supplier relationship) over the admitted storages `custpart` (part) and `suppliers`
//! (partsupp, supplier).
//!
//! Plan: the part filter is evaluated once per dictionary entry (`p_brand <> $1` per brand entry, `p_type NOT LIKE
//! $2` per type entry; a failing LIKE on some part row is the statement's error) and per size (the IN list's
//! distinct sizes). The supplier subquery is an exact byte test of the comments (`supp`), run by the phase-A tasks.
//! The groups are local group codes (brand entry, type entry, size slot) of a round (`round`, one round for TPC-H's
//! 25 brands x 150 types x 8 sizes). Per round, the partitioned plan (`fast`) runs when it applies: phase A (`sel`)
//! scans part-row ranges in parallel, lists the coded rows, and appends each part's (code, supplier row) pairs,
//! packed in 32 bits, to the region of its partition of 64 codes; phase B (`gcount`) sorts each partition's entries
//! by code in cache-sized scratch and counts every code's distinct supplier rows the subquery keeps. Otherwise the
//! general plan (`kernel`, `count`) groups the pairs by code per task and counts across tasks. The groups with a
//! pair are ordered by count descending (stable counting sort over the (brand, type, size) order) and returned as
//! columns.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::query::{query_spec_at, param_domain};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_params::Params;
use crate::link::join::lemma_product_index;

pub mod common;
pub mod tables;
pub mod sqlq;
pub mod sqlrel;
pub mod model;
pub mod kernel;
pub mod count;
pub mod bind;
pub mod answer;
pub mod output;
pub mod prep;
pub mod supp;
pub mod split;
pub mod round;
pub mod fin;
pub mod insort;
pub mod sidx;
pub mod sel;
pub mod gcount;
pub mod fast;
pub mod xidx;
pub mod gset;
pub mod ixcnt;
pub mod ixplan;
pub mod ssig;

use tables::*;
use model::*;
use sqlq::*;
use sqlrel::*;
use bind::*;
use answer::lemma_tabs_typed;
use output::*;
use prep::*;
use supp::*;
use split::*;
use round::*;
use fin::*;
use insort::order_slow;
use sidx::SIdx;

verus! {

// ------------------------------------------------------------------------------------------------ inputs

/// The distinct sizes of the IN list (`size_list`) are the parameters' sizes.
proof fn lemma_sizes(m: Prm, a: Seq<i64>, sizes: Seq<i64>)
    requires
        a.len() == 8,
        m.sizes.len() == 8,
        forall|z: int| 0 <= z < 8 ==> #[trigger] m.sizes[z] == a[z] as int,
        forall|x: i64| #[trigger] sizes.contains(x) <==> a.contains(x),
        forall|p: int, q: int| 0 <= p < q < sizes.len() ==> #[trigger] sizes[p] < #[trigger] sizes[q],
    ensures sizes_ok(sizes, m), 1 <= sizes.len(),
{
    assert(a.contains(a[0]));
    assert(sizes.contains(a[0]));
    assert forall|v: int| #[trigger] listed(sizes, v) <==> m.sizes.contains(v) by {
        if listed(sizes, v) {
            let z = choose|z: int| 0 <= z < sizes.len() && sizes[z] == v;
            assert(sizes.contains(sizes[z]));
            assert(a.contains(sizes[z]));
            let w = choose|w: int| 0 <= w < a.len() && a[w] == sizes[z];
            assert(m.sizes[w] == v);
        }
        if m.sizes.contains(v) {
            let w = choose|w: int| 0 <= w < m.sizes.len() && m.sizes[w] == v;
            assert(a.contains(a[w]));
            assert(sizes.contains(a[w]));
            let z = choose|z: int| 0 <= z < sizes.len() && sizes[z] == a[w];
            assert(sizes[z] == v);
        }
    }
}

/// Supplier keys identify supplier rows.
proof fn lemma_skeys(c: Cols, t: Tabs)
    requires cols_ok(c, t), keys_unique(t),
    ensures
        forall|r1: int, r2: int| 0 <= r1 < c.s.n && 0 <= r2 < c.s.n && #[trigger] skey(c.s, r1) == #[trigger] skey(c.s, r2)
            ==> r1 == r2,
{
    assert forall|r1: int, r2: int| 0 <= r1 < c.s.n && 0 <= r2 < c.s.n
        && #[trigger] skey(c.s, r1) == #[trigger] skey(c.s, r2) implies r1 == r2 by {
        assert(supp_row_ok(c.s, t.s[r1], r1));
        assert(supp_row_ok(c.s, t.s[r2], r2));
        assert(t.s[r1][0] == t.s[r2][0]);
    }
}

/// `(x / d) * d <= x`.
proof fn lemma_div_mul(x: int, d: int)
    requires x >= 0, d >= 1,
    ensures (x / d) * d <= x, x / d >= 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, d);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x, d);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(x, d);
    assert((x / d) * d == d * (x / d)) by (nonlinear_arith);
}

// ------------------------------------------------------------------------------------------------ rounds

/// Every group so far: (brand, type) windows before `(b0, t0)` in round order.
pub open spec fn done_ok(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>, b0: int, b1: int, t0: int) -> bool {
    &&& lex_sorted(gs)
    &&& forall|k: int| 0 <= k < gs.len() ==> grp_ok(c, t, m, sizes, #[trigger] gs[k])
        && (gs[k].b < b0 || (b0 <= gs[k].b < b1 && gs[k].t < t0))
    &&& forall|b: int, tt: int, z: int| (0 <= b < b0 || (b0 <= b < b1 && tt < t0)) && 0 <= tt < c.p.type_o@.len() - 1
        && 0 <= z < sizes.len() && #[trigger] kc(c, t, m, sizes, b, tt, z) > 0
        ==> exists|k: int| 0 <= k < gs.len() && at(#[trigger] gs[k], b, tt, z)
}

/// The groups before a round's window precede it in (brand, type) order.
proof fn lemma_round_pre(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>, b0: int, b1: int, t0: int)
    requires done_ok(c, t, m, sizes, gs, b0, b1, t0), t0 == 0 || b1 == b0 + 1,
    ensures
        forall|k: int| 0 <= k < gs.len() ==> grp_ok(c, t, m, sizes, #[trigger] gs[k])
            && (gs[k].b < b0 || (gs[k].b == b0 && gs[k].t < t0)),
{
    assert forall|k: int| 0 <= k < gs.len() implies grp_ok(c, t, m, sizes, #[trigger] gs[k])
        && (gs[k].b < b0 || (gs[k].b == b0 && gs[k].t < t0)) by {}
}

/// After a round, its window is done.
proof fn lemma_round_post(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, r0: Seq<Grp>, gs: Seq<Grp>, b0: int, b1: int,
    t0: int, t1: int)
    requires
        done_ok(c, t, m, sizes, r0, b0, b1, t0),
        t0 < t1,
        gs.len() >= r0.len(),
        gs.subrange(0, r0.len() as int) == r0,
        lex_sorted(gs),
        forall|k: int| 0 <= k < gs.len() ==> grp_ok(c, t, m, sizes, #[trigger] gs[k]),
        forall|k: int| r0.len() <= k < gs.len() ==> b0 <= (#[trigger] gs[k]).b < b1 && t0 <= gs[k].t < t1,
        forall|b: int, tt: int, z: int| b0 <= b < b1 && t0 <= tt < t1 && 0 <= z < sizes.len()
            && #[trigger] kc(c, t, m, sizes, b, tt, z) > 0
            ==> exists|k: int| r0.len() <= k < gs.len() && at(#[trigger] gs[k], b, tt, z),
    ensures done_ok(c, t, m, sizes, gs, b0, b1, t1),
{
    assert forall|k: int| 0 <= k < gs.len() implies grp_ok(c, t, m, sizes, #[trigger] gs[k])
        && (gs[k].b < b0 || (b0 <= gs[k].b < b1 && gs[k].t < t1)) by {
        if k < r0.len() {
            assert(gs[k] == gs.subrange(0, r0.len() as int)[k]);
        }
    }
    assert forall|b: int, tt: int, z: int| (0 <= b < b0 || (b0 <= b < b1 && tt < t1)) && 0 <= tt < c.p.type_o@.len() - 1
        && 0 <= z < sizes.len() && #[trigger] kc(c, t, m, sizes, b, tt, z) > 0
        implies exists|k: int| 0 <= k < gs.len() && at(#[trigger] gs[k], b, tt, z) by {
        if b < b0 || tt < t0 {
            let k = choose|k: int| 0 <= k < r0.len() && at(#[trigger] r0[k], b, tt, z);
            assert(gs[k] == gs.subrange(0, r0.len() as int)[k]);
        } else {
            let k = choose|k: int| r0.len() <= k < gs.len() && at(#[trigger] gs[k], b, tt, z);
        }
    }
}

/// A brand window with every type done.
proof fn lemma_window_done(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>, b0: int, b1: int)
    requires done_ok(c, t, m, sizes, gs, b0, b1, c.p.type_o@.len() - 1), b0 <= b1,
    ensures done_ok(c, t, m, sizes, gs, b1, b1, 0),
{
    assert forall|k: int| 0 <= k < gs.len() implies grp_ok(c, t, m, sizes, #[trigger] gs[k])
        && (gs[k].b < b1 || (b1 <= gs[k].b < b1 && gs[k].t < 0)) by {}
}

/// All groups of the window rounds: `Ok(None)` when every group's count is an int8, `Ok(Some((b, tt, z)))` for a
/// group whose count is beyond int8.
fn all_rounds<S: SIdx>(c: &Cols, bok: &Vec<bool>, tlike: &Vec<bool>, sizes: &Vec<i64>, sdense: bool, sfirst: i64,
    workers: usize, dispatch: &mut Dispatch, res: &mut Vec<Grp>, Ghost(t): Ghost<Tabs>,
    Ghost(m): Ghost<Prm>) -> (r: Result<bool, QueryError>)
    requires
        world_ok(*c, t, m, sdense, sfirst),
        inputs_ok(*c, m, bok@, tlike@, sizes@),
        c.s.n as int <= S::lim(),
        1 <= workers <= MAX_WORKERS,
        old(res)@.len() == 0,
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(false) ==> exists|b: int, tt: int, z: int| 0 <= b < bok@.len() && 0 <= tt < tlike@.len()
            && 0 <= z < sizes@.len() && #[trigger] kc(*c, t, m, sizes@, b, tt, z) > i64::MAX,
        r matches Ok(true) ==> groups_ok(*c, t, m, sizes@, final(res)@),
{
    let nb = bok.len();
    let nt = tlike.len();
    let ns = sizes.len();
    proof {
        assert(done_ok(*c, t, m, sizes@, res@, 0, 0, 0));
    }
    if nb == 0 || nt == 0 {
        return Ok(true);
    }
    let bw: usize;
    let tw: usize;
    if nt <= ROUND_GROUPS / ns {
        let ghost (nti, nsi) = (nt as int, ns as int);
        proof {
            lemma_div_mul(0x40000int, nsi);
            assert(nti * nsi <= 0x40000int) by (nonlinear_arith)
                requires nti <= 0x40000int / nsi, (0x40000int / nsi) * nsi <= 0x40000int, nsi >= 1;
            assert(nti * nsi >= 1) by (nonlinear_arith) requires nti >= 1, nsi >= 1;
        }
        let per = nt * ns;
        proof {
            let pi = per as int;
            lemma_div_mul(0x40000int, pi);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(pi, 0x40000int, pi);
            vstd::arithmetic::div_mod::lemma_div_by_self(pi);
        }
        bw = ROUND_GROUPS / per;
        tw = nt;
        proof {
            assert(bw * tw * ns <= 0x40000int) by (nonlinear_arith)
                requires per as int == nt * ns, (bw as int) * (per as int) <= 0x40000int, tw == nt;
        }
    } else {
        proof {
            lemma_div_mul(0x40000int, ns as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(0x40000int, ns as int, 8int);
            assert(0x40000int / 8int == 0x8000int) by (compute);
        }
        bw = 1;
        tw = ROUND_GROUPS / ns;
        proof {
            assert(bw * tw * ns <= 0x40000int) by (nonlinear_arith)
                requires bw == 1, (tw as int) * (ns as int) <= 0x40000int;
        }
    }
    let mut b0: usize = 0;
    while b0 < nb
        invariant
            world_ok(*c, t, m, sdense, sfirst),
            inputs_ok(*c, m, bok@, tlike@, sizes@),
            c.s.n as int <= S::lim(),
            1 <= workers <= MAX_WORKERS,
            nb == bok@.len(), nt == tlike@.len(), ns == sizes@.len(), 1 <= ns <= 8, nb > 0, nt > 0,
            bw >= 1, tw >= 1, tw <= nt, tw < nt ==> bw == 1, bw * tw * ns <= 0x40000,
            b0 <= nb,
            done_ok(*c, t, m, sizes@, res@, b0 as int, b0 as int, 0),
        decreases nb - b0,
    {
        let b1 = if nb - b0 > bw { b0 + bw } else { nb };
        let mut t0: usize = 0;
        while t0 < nt
            invariant
                world_ok(*c, t, m, sdense, sfirst),
                inputs_ok(*c, m, bok@, tlike@, sizes@),
                c.s.n as int <= S::lim(),
                1 <= workers <= MAX_WORKERS,
                nb == bok@.len(), nt == tlike@.len(), ns == sizes@.len(), 1 <= ns <= 8, nb > 0, nt > 0,
                bw >= 1, tw >= 1, tw <= nt, tw < nt ==> bw == 1, bw * tw * ns <= 0x40000,
                b0 < b1 <= nb, b1 - b0 <= bw, t0 == 0 || t0 == nt || b1 == b0 + 1,
                t0 <= nt,
                done_ok(*c, t, m, sizes@, res@, b0 as int, b1 as int, t0 as int),
            decreases nt - t0,
        {
            let t1 = if nt - t0 > tw { t0 + tw } else { nt };
            proof {
                assert((b1 - b0) * (t1 - t0) * ns <= bw * tw * ns) by (nonlinear_arith)
                    requires b1 - b0 <= bw, t1 - t0 <= tw, b1 - b0 >= 1, t1 - t0 >= 1, ns >= 1;
                lemma_round_pre(*c, t, m, sizes@, res@, b0 as int, b1 as int, t0 as int);
            }
            let ghost r0 = res@;
            match run_round::<S>(c, bok, tlike, sizes, b0, b1, t0, t1, sdense, sfirst, workers, dispatch, res,
                Ghost(t), Ghost(m)) {
                Ok(true) => {},
                Ok(false) => {
                    return Ok(false);
                },
                Err(e) => {
                    return Err(e);
                },
            }
            proof {
                lemma_round_post(*c, t, m, sizes@, r0, res@, b0 as int, b1 as int, t0 as int, t1 as int);
            }
            t0 = t1;
        }
        proof {
            lemma_window_done(*c, t, m, sizes@, res@, b0 as int, b1 as int);
        }
        b0 = b1;
    }
    Ok(true)
}

/// The largest count.
fn max_count(gs: &Vec<Grp>) -> (r: u64)
    requires forall|k: int| 0 <= k < gs@.len() ==> (#[trigger] gs@[k]).cnt <= i64::MAX,
    ensures r <= i64::MAX, forall|k: int| 0 <= k < gs@.len() ==> (#[trigger] gs@[k]).cnt <= r,
{
    let n = gs.len();
    let mut maxc: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            n == gs@.len(), i <= n, maxc <= i64::MAX,
            forall|k: int| 0 <= k < n ==> (#[trigger] gs@[k]).cnt <= i64::MAX,
            forall|k: int| 0 <= k < i ==> (#[trigger] gs@[k]).cnt <= maxc,
        decreases n - i,
    {
        if gs[i].cnt > maxc {
            maxc = gs[i].cnt;
        }
        i = i + 1;
    }
    maxc
}

// ------------------------------------------------------------------------------------------------ the query

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_bound(sv, db0);
        lemma_params_ok(params@);
    }
    let ghost t = tabs_of(db0);
    let ghost m = prm_of(params@);
    let c = open_cols(stores, Ghost(cr_of(db0)), Ghost(sr_of(db0)));
    proof {
        lemma_tabs_typed(c, t);
        lemma_shape(c, t);
        lemma_skeys(c, t);
    }
    // p_type LIKE $2 per type dictionary entry; a failing pattern on some part row is the statement's error.
    let (tlike, errs, any_err) = like_table(&c.p, params.p1);
    if any_err && c.ps.n > 0 {
        match first_like_error(&c.p, &errs, Ghost(t.p), Ghost(m.pat)) {
            Some((i, err)) => {
                let r = Ok(Answer::SqlError(err));
                proof {
                    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), r) by {
                        lemma_bound_same(sv, db0, db);
                        lemma_like_err(db, params@, i as int, err);
                    }
                }
                return r;
            },
            None => {},
        }
    }
    proof {
        if !any_err {
            lemma_like_all_from_entries(c.p, t.p, m.pat, errs@);
        } else if c.ps.n == 0 {
            lemma_product_index(t.ps, t.p);
        }
        assert(like_all_ok(t, m) || prod(t).len() == 0);
    }
    // p_brand <> $1 per brand dictionary entry; the IN list's distinct sizes.
    let bok = brand_table(&c.p, params.p0);
    let arr: [i64; 8] = [params.p2, params.p3, params.p4, params.p5, params.p6, params.p7, params.p8, params.p9];
    let sizes = size_list(arr);
    proof {
        assert(m.sizes[0] == arr@[0] as int);
        assert(m.sizes[1] == arr@[1] as int);
        assert(m.sizes[2] == arr@[2] as int);
        assert(m.sizes[3] == arr@[3] as int);
        assert(m.sizes[4] == arr@[4] as int);
        assert(m.sizes[5] == arr@[5] as int);
        assert(m.sizes[6] == arr@[6] as int);
        assert(m.sizes[7] == arr@[7] as int);
        lemma_sizes(m, arr@, sizes@);
    }
    let (sfirst, sdense) = supp_dense(&c.s, Ghost(c.e32@), Ghost(c.e64@));
    // At most 32 workers: measured on this host (32 physical cores), 64 threads (hyperthreads, 2 fork-joins of
    // twice the threads) took 47-52 ms against 35-38 ms with 32.
    let workers = if workers > 32 { 32 } else { workers };
    // The groups: through the (brand, type, size) index of part_btsidx when it is present, else by the general
    // partitioned plan.
    let mut res: Vec<Grp> = Vec::new();
    let xo = if bok.len() <= 0x1000 && tlike.len() <= 0x1000 {
        xidx::open_xidx(&mut stores.part_btsidx, &c, Ghost(t), Ghost(db0))
    } else {
        None
    };
    let use_ix = match xo {
        Some(xi) => xi.nk < ixcnt::NOENT as usize,
        None => false,
    };
    let rr = if use_ix {
        let xi = xo.unwrap();
        // The subquery's s_comment signatures (storage supp_trisig) over the supplier rows of `c.s`.
        proof {
            assert forall|j: int| 0 <= j < c.s.n implies #[trigger] sr_of(db0)[1][j][6] == Val::Text(comment(c.s, j)) by {
                assert(supp_row_ok(c.s, t.s[j], j));
            }
        }
        let sg = ssig::open_ssig(&mut stores.supp_trisig, &c.s, Ghost(sr_of(db0)));
        ixplan::ix_groups(&c, xi, sg, &bok, &tlike, &sizes, sdense, sfirst, workers, dispatch, &mut res, Ghost(t), Ghost(m))
    } else if c.s.n <= 0xFFFF_FFFF {
        // Supplier row numbers in 32 bits when they fit.
        all_rounds::<u32>(&c, &bok, &tlike, &sizes, sdense, sfirst, workers, dispatch, &mut res, Ghost(t), Ghost(m))
    } else {
        all_rounds::<u64>(&c, &bok, &tlike, &sizes, sdense, sfirst, workers, dispatch, &mut res, Ghost(t), Ghost(m))
    };
    match rr {
        Ok(true) => {},
        Ok(false) => {
            let r = Ok(Answer::SqlError(crate::spec::value::SqlError::NumericValueOutOfRange));
            proof {
                let (b, tt, z) = choose|b: int, tt: int, z: int| 0 <= b < bok@.len() && 0 <= tt < tlike@.len()
                    && 0 <= z < sizes@.len() && #[trigger] kc(c, t, m, sizes@, b, tt, z) > i64::MAX;
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), r) by {
                    lemma_bound_same(sv, db0, db);
                    lemma_overflow(db, params@, c, sizes@, b, tt, z);
                }
            }
            return r;
        },
        Err(e) => {
            return Err(e);
        },
    }
    // By count descending; ties in (brand, type, size) order.
    proof {
        assert forall|k: int| 0 <= k < res@.len() implies (#[trigger] res@[k]).cnt <= i64::MAX by {
            assert(grp_ok(c, t, m, sizes@, res@[k]));
        }
    }
    let maxc = max_count(&res);
    let perm = if maxc <= (usize::MAX as u64) - 3 {
        order_groups(&res, maxc)
    } else {
        order_slow(&res)
    };
    let nres = res.len();
    let cols = answer_columns(&c, &sizes, &res, &perm);
    let r = Ok(Answer::Columns(cols));
    proof {
        assert(fin_ok(c, t, m, sizes@, res@));
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), r) by {
            lemma_bound_same(sv, db0, db);
            lemma_final(db, params@, c, sizes@, res@, perm@);
        }
    }
    r
}

} // verus!
