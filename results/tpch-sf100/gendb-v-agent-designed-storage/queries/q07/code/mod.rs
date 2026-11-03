// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! TPC-H Q7 (volume shipping) over storages `li_okruns` (facts' lineitem and orders, and the l_orderkey run starts),
//! `custpart` (customer) and `suppliers` (supplier, nation). Storage `facts` is a use only for its interface, which
//! `li_okruns`' interface states its parts with; no part of it is read.
//!
//! Plan:
//! 1. list the nations named `$1` (class 1) or `$2` (class 2) (`nation`);
//! 2. open the scan's slices (`open`); supplier and customer keys are dense when sorted with the right span (one
//!    probe per lookup, `setup`); power-of-two block sizes are shifted;
//! 3. the shipdate zone maps bound the lineitem groups that can hold lines of 1995-1996 (`setup::zone_range`);
//! 4. scan those groups in parallel (`par`, `kernel`): per line in the window whose supplier's nation has a class,
//!    look up its order's customer's class and add `l_extendedprice * (100 - l_discount)` to its group (pair of
//!    nations x year); sums are exact `i128` coefficients of scale 4, with their absolute masses. Lines are taken
//!    supplier first, their orders found through the l_orderkey runs of storage `li_okruns` (`sfast`, `runs`);
//! 5. answer one row per non-empty group in ORDER BY order (`out`), or `Capacity` when a group's mass passes
//!    `i128::MAX` (`capacity`).
//! Proof: `sqlq` (the statement on a joined row), `reduce` (the 6-way product to a lookup term per lineitem row),
//! `body` (evaluation and the GROUP BY normal form), `bind`/`line` (stored parts = table rows; a lineitem row's term
//! is the scan's line term), `answer` (the normal form's accumulators are the scan's group sums).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready, outcome_ok, capacity_domain};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::{param_domain, param_typed, query_spec_at};
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::text::lex_cmp;
use crate::exec::value::{EVal, view_row};
use crate::link::query::{view_rows, gabs};

pub mod common;
pub mod dates;
pub mod sqlq;
pub mod reduce;
pub mod body;
pub mod model;
pub mod lookup;
pub mod kernel;
pub mod bind;
pub mod line;
pub mod answer;
pub mod capacity;
pub mod out;
pub mod open;
pub mod nation;
pub mod setup;
pub mod par;
pub mod cmap;
pub mod sfast;
pub mod runs;
pub mod clus;

use sqlq::{ltext, texts, lemma_texts};
use reduce::*;
use body::*;
use model::*;
use lookup::*;
use kernel::*;
use bind::*;
use line::*;
use answer::*;
use out::*;
use open::*;
use nation::*;
use setup::*;
use par::*;
use cmap::*;
use clus::*;
use sfast::*;
use runs::*;

verus! {

/// A copy of a byte slice.
fn copy_bytes(a: &[u8]) -> (v: Vec<u8>)
    ensures v@ == a@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a@.len(), v@ == a@.subrange(0, i as int),
        decreases a@.len() - i,
    {
        v.push(a[i]);
        i = i + 1;
        proof {
            assert(v@ =~= a@.subrange(0, i as int));
        }
    }
    proof {
        assert(a@.subrange(0, a@.len() as int) =~= a@);
    }
    v
}

/// Counts and sums of the four groups as integers.
pub open spec fn ints_u(v: Seq<usize>) -> Seq<int> { v.map_values(|a: usize| a as int) }
pub open spec fn ints_i(v: Seq<i128>) -> Seq<int> { v.map_values(|a: i128| a as int) }

/// The answer rows: the non-empty groups in `ord_of` order.
fn build_rows(params: &Params, same: bool, lt: bool, cnts: &Vec<usize>, sums: &Vec<i128>) -> (r: (Vec<Vec<EVal>>, Ghost<Seq<int>>))
    requires
        texts(params@),
        same == (ltext(params@[0]) == ltext(params@[1])),
        !same ==> lt == (lex_cmp(ltext(params@[0]), ltext(params@[1])) < 0),
        cnts@.len() == 4,
        sums@.len() == 4,
    ensures out_ok(params@, ints_u(cnts@), ints_i(sums@), r.1@, view_rows(r.0@)),
{
    let ghost ps = params@;
    let ghost tc = ints_u(cnts@);
    let ghost ts = ints_i(sums@);
    proof {
        assert(ps[0] == Literal::Text(params.p0@) && ps[1] == Literal::Text(params.p1@));
    }
    let mut ord: Vec<usize> = Vec::new();
    if same {
        ord.push(0);
        ord.push(1);
    } else if lt {
        ord.push(0);
        ord.push(1);
        ord.push(2);
        ord.push(3);
    } else {
        ord.push(2);
        ord.push(3);
        ord.push(0);
        ord.push(1);
    }
    proof {
        assert(ord@.len() == ord_of(ps).len());
        assert(forall|p: int| 0 <= p < ord@.len() ==> #[trigger] ord@[p] as int == ord_of(ps)[p]);
    }
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let ghost mut pos: Seq<int> = Seq::empty();
    let mut p: usize = 0;
    while p < ord.len()
        invariant
            texts(ps), ps == params@,
            ps[0] == Literal::Text(params.p0@) && ps[1] == Literal::Text(params.p1@),
            tc == ints_u(cnts@), ts == ints_i(sums@),
            cnts@.len() == 4, sums@.len() == 4,
            ord@.len() == ord_of(ps).len(),
            forall|q: int| 0 <= q < ord@.len() ==> #[trigger] ord@[q] as int == ord_of(ps)[q],
            forall|q: int| 0 <= q < ord@.len() ==> 0 <= #[trigger] ord@[q] < 4,
            p <= ord@.len(),
            rows@.len() == pos.len(),
            forall|i: int, j: int| 0 <= i < j < pos.len() ==> #[trigger] pos[i] < #[trigger] pos[j],
            forall|i: int| 0 <= i < pos.len() ==> 0 <= #[trigger] pos[i] < p,
            forall|i: int| 0 <= i < pos.len() ==> #[trigger] tc[ord_of(ps)[pos[i]]] > 0,
            forall|i: int| 0 <= i < pos.len() ==> #[trigger] view_row(rows@[i]@) == rowof(ps, ord_of(ps)[pos[i]], ts[ord_of(ps)[pos[i]]]),
            forall|q: int| 0 <= q < p && #[trigger] tc[ord_of(ps)[q]] > 0 ==> pos.contains(q),
        decreases ord@.len() - p,
    {
        let gi = ord[p];
        let ghost pos0 = pos;
        if cnts[gi] > 0 {
            let (a, b) = if gi < 2 { (params.p0, params.p1) } else { (params.p1, params.p0) };
            let mut row: Vec<EVal> = Vec::new();
            row.push(EVal::Text(copy_bytes(a)));
            row.push(EVal::Text(copy_bytes(b)));
            row.push(EVal::Num { coeff: 1995 + (gi % 2) as i128, scale: 0 });
            row.push(EVal::Num { coeff: sums[gi], scale: 4 });
            proof {
                assert(view_row(row@) =~= rowof(ps, gi as int, ts[gi as int]));
            }
            rows.push(row);
            proof {
                pos = pos.push(p as int);
                assert(pos[pos.len() - 1] == p as int);
            }
        }
        proof {
            assert forall|q: int| 0 <= q < p + 1 && #[trigger] tc[ord_of(ps)[q]] > 0 implies pos.contains(q) by {
                if q < p {
                    let i = choose|i: int| 0 <= i < pos0.len() && pos0[i] == q;
                    assert(pos[i] == q);
                } else {
                    assert(pos[pos.len() - 1] == q);
                }
            }
            assert forall|i: int| 0 <= i < pos.len() implies #[trigger] view_row(rows@[i]@) == rowof(ps, ord_of(ps)[pos[i]], ts[ord_of(ps)[pos[i]]]) by {
                if i < pos0.len() {
                    assert(pos[i] == pos0[i]);
                }
            }
        }
        p = p + 1;
    }
    proof {
        let out = view_rows(rows@);
        assert forall|i: int| 0 <= i < pos.len() implies #[trigger] out[i] == rowof(ps, ord_of(ps)[pos[i]], ts[ord_of(ps)[pos[i]]]) by {}
    }
    (rows, Ghost(pos))
}

/// The facts about the call's slices and nation list that hold for every database bound to the parts.
pub open spec fn call_ok(sv: StoresView, c: Cols, s_stored: u64, c_stored: u64, natc: NCols, x: Ctx, ps: Seq<Literal>) -> bool {
    &&& li_from_parts(c, fpv(sv))
    &&& ord_from_parts(c, fpv(sv))
    &&& sup_from_parts_kind(c, sv.suppliers, s_stored)
    &&& cus_from_parts_kind(c, sv.custpart, c_stored)
    &&& nat_from_parts(natc, sv.suppliers)
    &&& texts(ps)
    &&& x.same == (ltext(ps[0]) == ltext(ps[1]))
    &&& forall|v: int| #[trigger] nat_cls(x, v) == pcls(natc, ps, v, natc.n_n as int)
}

/// Every database bound to the parts: the chain of links from the SQL to the scan's model.
proof fn lemma_bound_chain(sv: StoresView, db: Database, c: Cols, s_stored: u64, c_stored: u64, natc: NCols, x: Ctx,
    ps: Seq<Literal>)
    requires bound_db(sv, db), call_ok(sv, c, s_stored, c_stored, natc, x, ps),
    ensures chain_ok(db, c, x, ps, lmap(fpv(sv), c.n_l as int), omap(fpv(sv), c.n_o as int)),
{
    lemma_tables_typed(db);
    lemma_inputs_ok(db);
    lemma_okruns(sv, db);
    lemma_li(db, fpv(sv), c);
    lemma_ord(db, fpv(sv), c);
    lemma_sup(db, sv.suppliers, c, s_stored);
    lemma_cus(db, sv.custpart, c, c_stored);
    lemma_keys_ok(db, c, lmap(fpv(sv), c.n_l as int), omap(fpv(sv), c.n_o as int));
    lemma_nat(db, sv.suppliers, natc);
    assert forall|k: int| #[trigger] nat_cls(x, k) == nat_cls_db(db, ps, k) by {
        lemma_nat_ctx(db, natc, ps, k);
    }
}

/// TPC-H Q7 over storages `li_okruns`, `custpart` and `suppliers`.
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
        lemma_texts(ps);
        assert(ps[0] == Literal::Text(params.p0@) && ps[1] == Literal::Text(params.p1@));
        lemma_okruns(sv, db0);
        lemma_li_kinds(db0, fpv(sv));
        lemma_ord_kinds(db0, fpv(sv));
        lemma_sup_kinds(db0, sv.suppliers);
        lemma_cus_kinds(db0, sv.custpart);
        lemma_nat_kinds(db0, sv.suppliers);
        lemma_clus_kind(db0, fpv(sv));
    }
    let (c, s_stored, c_stored) = open_cols(stores);
    let flag = open_clus(stores);
    let natc = open_nations(&mut stores.suppliers);
    proof {
        lemma_tables_typed(db0);
        lemma_inputs_ok(db0);
        lemma_nat(db0, sv.suppliers, natc);
        lemma_li(db0, fpv(sv), c);
        lemma_ord(db0, fpv(sv), c);
        lemma_sup(db0, sv.suppliers, c, s_stored);
        lemma_cus(db0, sv.custpart, c, c_stored);
        lemma_keys_ok(db0, c, lmap(fpv(sv), c.n_l as int), omap(fpv(sv), c.n_o as int));
        lemma_runs_model(sv, c);
    }
    let clus = flag == 1;
    proof {
        if clus {
            lemma_clus(db0, fpv(sv), c);
        }
    }
    let (nk, nc) = build_nations(&natc, params);
    let same = bytes_eq(params.p0, params.p1);
    let ghost x = Ctx { nk: nk@, nc: nc@, same };
    let (sd, sk0) = check_dense_s(&c);
    let (cd, ck0) = check_dense_c(&c);
    let (sh_o, pow_o) = shift_of(c.bs_o);
    let (sh_s, pow_s) = shift_of(c.bs_s);
    let (sh_c, pow_c) = shift_of(c.bs_c);
    let s = Shifts { sh_o, pow_o, sh_s, pow_s, sh_c, pow_c };
    let (ga, gb) = zone_range(&c);
    let ntb = build_ntab(&nk, &nc, Ghost(x));
    // the class maps of the supplier and customer rows (dense keys); the general path looks suppliers up by key
    let (cmv, cm, smv, sm2) = match build_maps(&c, s, sd, sk0, cd, ck0, &nk, &nc, &ntb, workers, dispatch, Ghost(x)) {
        Ok(r) => r,
        Err(f) => return Err(QueryError::WorkerFailed(f)),
    };
    // the supplier-first path: co-clustered lines with run starts, dense keys with both maps, at most 2^20
    // suppliers (the fixed-size map), customer keys whose last key fits
    let ck_top: i128 = ck0 as i128 + c.n_c as i128 - 1;
    let rf = clus && cmv && smv && 0 < c.n_c && c.n_c < usize::MAX / 32 && ck_top <= 0x7fff_ffff_ffff_ffffi128
        && 0 < c.n_s && c.n_s <= 16 * SMW && sm2.len() <= SMW;
    let sma: Box<[u32; SMW]> = if sm2.len() <= SMW { smap_array(&sm2) } else { Box::new([0u32; SMW]) };
    proof {
        if rf {
            lemma_smap_array(c, x, sk0, sm2@, sma@);
            assert(sfast_ok(c, s, sk0, ck0, cm@, sm2@, sma@, x));
        }
    }
    let cm = Arc::new(cm);
    let sm2 = Arc::new(sm2);
    let sma = Arc::new(sma);
    let sm = build_smap(&c, s, false, sk0, &ntb, &nk, &nc, Ghost(x));
    proof {
        assert(call_ok(sv, c, s_stored, c_stored, natc, x, ps));
        assert(ncls_ok(x, nk@, nc@));
        assert(scan_ok(c, s, false, sk0, cd, ck0, nk@, nc@, ntb@, sm@, x));
        lemma_zone_lines(c, x, ga as int, gb as int);
    }
    let (sums, mass, cnts, over) = match run_scan(&c, s, false, sk0, cd, ck0, &nk, &nc, &ntb, &sm, same, cmv, &cm, smv, &sm2, rf, &sma, ga, gb, workers, dispatch, Ghost(x)) {
        Ok(o) => o,
        Err(f) => return Err(QueryError::WorkerFailed(f)),
    };
    let ghost (a, b, n) = (jlo(c, ga as int), jlo(c, gb as int), c.n_l as int);
    let ghost e = Seq::<usize>::empty();
    proof {
        // the lines outside [a, b) are in no group: the scan's sums are the sums over all lines
        assert forall|gi: int| 0 <= gi < 4 implies {
            &&& rcnt(c, x, gi, 0, n) == rcnt(c, x, gi, a, b)
            &&& rsum(c, x, gi, 0, n) == rsum(c, x, gi, a, b)
            &&& rmass(c, x, gi, 0, n) == rmass(c, x, gi, a, b)
        } by {
            lemma_r_none(c, x, gi, 0, a);
            lemma_r_none(c, x, gi, b, n);
            lemma_r_split(c, x, gi, 0, a, n);
            lemma_r_split(c, x, gi, a, b, n);
        }
    }
    if over {
        proof {
            let gi = choose|gi: int| 0 <= gi < 4 && #[trigger] rmass(c, x, gi, a, b) + lmass(c, x, gi, e, 0) > i128_max();
            assert(rmass(c, x, gi, 0, n) > i128_max());
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                lemma_bound_chain(sv, db, c, s_stored, c_stored, natc, x, ps);
                let k = krow(ps, gi);
                lemma_group_sums(db, c, x, ps, lmap(fpv(sv), n), omap(fpv(sv), c.n_o as int), k);
                lemma_r_bounds(c, x, 0, 0, n);
                lemma_r_bounds(c, x, 1, 0, n);
                lemma_r_bounds(c, x, 2, 0, n);
                lemma_r_bounds(c, x, 3, 0, n);
                assert(gabs(g7(), ship(db, ps), k, 0) > i128::MAX);
                capacity::lemma_capacity(db, ps, k);
            }
        }
        return Ok(Answer::Capacity);
    }
    let lt = crate::stores::facts::interface::common::read::bytes_cmp(params.p0, params.p0.len(), params.p1, params.p1.len()) < 0;
    let (rows, pos) = build_rows(params, same, lt, &cnts, &sums);
    proof {
        let tc = ints_u(cnts@);
        let ts = ints_i(sums@);
        let tm = ints_i(mass@);
        assert(totals_ok(c, x, tc, ts, tm)) by {
            assert forall|gi: int| 0 <= gi < 4 implies #[trigger] tc[gi] == rcnt(c, x, gi, 0, n) by {
                assert(cnts@[gi] as int == rcnt(c, x, gi, a, b) + lcnt(c, x, gi, e, 0));
            }
            assert forall|gi: int| 0 <= gi < 4 implies #[trigger] ts[gi] == rsum(c, x, gi, 0, n) by {
                assert(sums@[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, e, 0));
            }
            assert forall|gi: int| 0 <= gi < 4 implies #[trigger] tm[gi] == rmass(c, x, gi, 0, n) by {
                assert(mass@[gi] as int == rmass(c, x, gi, a, b) + lmass(c, x, gi, e, 0));
            }
        }
        assert forall|gi: int| 0 <= gi < 4 implies #[trigger] tm[gi] <= i128_max() by {
            assert(mass@[gi] as int <= i128_max());
        }
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
            lemma_bound_chain(sv, db, c, s_stored, c_stored, natc, x, ps);
            lemma_out(db, c, x, ps, lmap(fpv(sv), n), omap(fpv(sv), c.n_o as int), tc, ts, tm, pos@, view_rows(rows@));
        }
    }
    Ok(Answer::Rows(rows))
}

} // verus!
