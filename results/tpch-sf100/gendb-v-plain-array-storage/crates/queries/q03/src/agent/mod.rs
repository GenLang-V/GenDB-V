//! TPC-H Q3 (shipping priority) over the flat storages: revenue of the orders of segment `$1` dated before `$2`, from
//! their lineitems shipped after `$2`, top 10 by revenue then date.
//!
//! Plan of a call (`query`):
//! 1. customer pass (`customers`, parallel): one bit per customer row for `c_mktsegment = $1`, and whether
//!    `c_custkey` is positional (`c_custkey[r] == c_custkey[0] + r`);
//! 2. lineitem scan (`scan`, parallel over row ranges): rows are mapped to their orders row by following the key
//!    changes (checked against `o_orderkey`), and only rows whose order is dated before `$2` and that ship after it
//!    are looked at; each task returns per-order runs (`runs`);
//! 3. merge of the runs (`merge`), checked to be in order;
//! 4. when a check of 1-3 fails, the general serial path (`fallback`) computes the groups instead;
//! 5. top 10 (`topk`) and the output rows.
//! The proof: the groups are exactly the qualifying orders with their sums (`answer::groups_complete`), which with
//! the SQL meaning of the statement (`denotation`, `groups`) gives the fixed claim (`answer::lemma_answer`); a group
//! beyond the SUM capacity gives `Capacity` (`capacity`).
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::{answer_meets, stores_ready, bound_db, outcome_ok, Answer};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::{EVal, view_row};
use crate::exec::datetime::date_from_civil_exec;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::datetime::{date_from_civil, valid_ymd};
use crate::link::query::view_rows;
use crate::link::expr::i128_max;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_lineitem::interface as li;

pub mod tables;
pub mod normal_form;
pub mod denotation;
pub mod groups;
pub mod common;
pub mod answer;
pub mod runs;
pub mod scan_parts;
pub mod scan;
pub mod customers;
pub mod merge;
pub mod combine;
pub mod fallback;
pub mod topk;
pub mod plan;
pub mod capacity;

use tables::*;
use normal_form::*;
use runs::{NL_MAX, VMAX};
use scan::{ScanCols, scan_cols_ok};
use customers::{CustCols, cust_cols_ok};
use fallback::{Fallback, general_groups, general_ok};
use answer::{group_row, groups_complete, groups_capped, top_rows_ok, lemma_answer};
use topk::{groups_final, top_out_ok};

verus! {

/// The final groups: strictly increasing orders with their sums over all lineitem rows, exactly the hit orders,
/// each within the SUM capacity.
pub open spec fn final_groups(gj: Seq<usize>, gs: Seq<i128>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& gj.len() == gs.len()
    &&& forall|g: int, h: int| 0 <= g < h < gj.len() ==> gj[g] < gj[h]
    &&& forall|g: int| 0 <= g < gj.len() ==> (#[trigger] gj[g] as int) < n_o(sv)
    &&& forall|g: int| 0 <= g < gj.len() ==> #[trigger] gs[g] as int == order_sum(sv, seg_of(ps), dl_of(ps), gj[g] as int, 0, n_l(sv))
            && order_count(sv, seg_of(ps), dl_of(ps), gj[g] as int, 0, n_l(sv)) > 0
            && order_abs(sv, seg_of(ps), dl_of(ps), gj[g] as int, 0, n_l(sv)) <= i128_max()
    &&& forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv)) > 0 ==> gj.contains(j as usize)
}

/// The selection and the groups: what the final claim needs (`answer::lemma_answer`).
pub open spec fn answer_ok(sel: Seq<usize>, ss: Seq<i128>, groups: Seq<int>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& sel.len() == ss.len()
    &&& forall|k: int| 0 <= k < sel.len() ==> #[trigger] ss[k] as int == order_sum(sv, seg_of(ps), dl_of(ps), sel[k] as int, 0, n_l(sv))
    &&& forall|k: int| 0 <= k < sel.len() ==> (#[trigger] sel[k] as int) < n_o(sv)
    &&& groups_complete(sv, ps, groups)
    &&& groups_capped(sv, ps, groups)
    &&& top_rows_ok(sv, ps, groups, sel.map_values(|x: usize| x as int))
}

/// Final groups are complete and capped in the sense of `answer`.
proof fn lemma_final_answer(gj: Seq<usize>, gs: Seq<i128>, sv: StoresView, ps: Seq<Literal>)
    requires final_groups(gj, gs, sv, ps), n_o(sv) <= usize::MAX,
    ensures
        groups_complete(sv, ps, gj.map_values(|x: usize| x as int)),
        groups_capped(sv, ps, gj.map_values(|x: usize| x as int)),
{
    let groups = gj.map_values(|x: usize| x as int);
    let (seg, dl) = (seg_of(ps), dl_of(ps));
    assert(groups.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < groups.len() && 0 <= b < groups.len() && a != b implies groups[a] != groups[b] by {
            if a < b { assert(gj[a] < gj[b]); } else { assert(gj[b] < gj[a]); }
        }
    }
    assert forall|t: int| 0 <= t < groups.len() implies {
        &&& 0 <= #[trigger] groups[t] < n_o(sv)
        &&& order_ok(sv, seg, dl, groups[t])
        &&& order_count(sv, seg, dl, groups[t], 0, n_l(sv)) > 0
    } by {
        assert(groups[t] == gj[t] as int);
        assert(gs[t] as int == order_sum(sv, seg, dl, gj[t] as int, 0, n_l(sv)));
        assert(order_count(sv, seg, dl, groups[t], 0, n_l(sv)) > 0);
        if !order_ok(sv, seg, dl, groups[t]) {
            lemma_order_not_ok(sv, seg, dl, groups[t], 0, n_l(sv));
        }
    }
    assert forall|j: int| 0 <= j < n_o(sv) && order_ok(sv, seg, dl, j) && #[trigger] order_count(sv, seg, dl, j, 0, n_l(sv)) > 0
        implies groups.contains(j) by {
        assert(gj.contains(j as usize));
        let g = choose|g: int| 0 <= g < gj.len() && gj[g] == j as usize;
        assert(groups[g] == j);
    }
    assert forall|t: int| 0 <= t < groups.len() implies #[trigger] order_abs(sv, seg, dl, groups[t], 0, n_l(sv)) <= i128_max() by {
        assert(groups[t] == gj[t] as int);
        assert(gs[t] as int == order_sum(sv, seg, dl, gj[t] as int, 0, n_l(sv)));
    }
}

/// One output row: `l_orderkey, revenue, o_orderdate, o_shippriority` of order `j` with revenue `s`.
fn output_row(okey: &'static [i64], odate: &'static [i32], oship: &'static [i64], j: usize, s: i128, Ghost(sv): Ghost<StoresView>)
    -> (row: Vec<EVal>)
    requires
        okey@ == ok(sv), odate@ == od(sv), oship@ == os(sv), (j as int) < n_o(sv),
        ok(sv).len() == n_o(sv), od(sv).len() == n_o(sv), os(sv).len() == n_o(sv),
        od(sv)[j as int] as int - 10957 >= -2451545,
    ensures view_row(row@) == order_row(sv, j as int, s as int),
{
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Int(okey[j]));
    row.push(EVal::Num { coeff: s, scale: 4 });
    row.push(EVal::Date(odate[j] - 10957));
    row.push(EVal::Int(oship[j]));
    proof {
        assert(view_row(row@) =~= order_row(sv, j as int, s as int));
    }
    row
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
    let ghost db0 = choose|db: Database| bound_db(sv, db);
    proof {
        lemma_parts_shape(sv, db0);
        lemma_keys_unique(sv, db0);
        assert forall|i: int| 0 <= i < n_l(sv) implies num15(#[trigger] lp(sv)[i]) && num15(ld(sv)[i]) by {
            lemma_lineitem_row(sv, db0, i);
        }
        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] od(sv)[j] as int - 10957 >= -2451545 by {
            lemma_orders_row(sv, db0, j);
        }
    }
    // $1 and $2 (in stored days since 1970-01-01)
    let seg: &'static [u8] = params.p0;
    let seg_len = seg.len();
    let (y, mo, d) = (params.p1.y, params.p1.m, params.p1.d);
    proof {
        assert(ps[1] == Literal::Date { y: y as int, m: mo as int, d: d as int });
        assert(valid_ymd(y as int, mo as int, d as int));
        assert(date_from_civil(1, 1, 1) == -730119) by (compute);
        assert(date_from_civil(9999, 12, 31) == 2921939) by (compute);
        assert(crate::spec::datetime::days_in_month(y as int, mo as int) <= 31);
    }
    let day = date_from_civil_exec(y as i64, mo as i64, d as i64);
    let dl: i32 = (day + 10957) as i32;
    let ghost dlg: int = dl as int;
    assert(seg_of(ps) == seg@ && dl_of(ps) == dlg);
    // the columns (whole parts; the scans touch only what they need)
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let lkey = stores.flat_lineitem.extent_i64(li::L_ORDERKEY, 0, nl);
    let lship = stores.flat_lineitem.extent_i32(li::L_SHIPDATE, 0, nl);
    let lprice = stores.flat_lineitem.extent_i128(li::L_EXTENDEDPRICE, 0, nl);
    let ldisc = stores.flat_lineitem.extent_i128(li::L_DISCOUNT, 0, nl);
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let okey = stores.flat_orders.extent_i64(oi::O_ORDERKEY, 0, no);
    let ocust = stores.flat_orders.extent_i64(oi::O_CUSTKEY, 0, no);
    let odate = stores.flat_orders.extent_i32(oi::O_ORDERDATE, 0, no);
    let oship = stores.flat_orders.extent_i64(oi::O_SHIPPRIORITY, 0, no);
    let nc = stores.flat_customer.part_len(ci::C_CUSTKEY);
    let ckey = stores.flat_customer.extent_i64(ci::C_CUSTKEY, 0, nc);
    let noffs = stores.flat_customer.part_len(ci::C_MKTSEGMENT_OFFSETS);
    let coffs = stores.flat_customer.extent_i64(ci::C_MKTSEGMENT_OFFSETS, 0, noffs);
    let nbytes = stores.flat_customer.part_len(ci::C_MKTSEGMENT_BYTES);
    let cbytes = stores.flat_customer.extent_u8(ci::C_MKTSEGMENT_BYTES, 0, nbytes);
    proof {
        assert(stores@ == sv);
        assert(lkey@ =~= lk(sv) && lship@ =~= ls(sv) && lprice@ =~= lp(sv) && ldisc@ =~= ld(sv));
        assert(okey@ =~= ok(sv) && ocust@ =~= oc(sv) && odate@ =~= od(sv) && oship@ =~= os(sv));
        assert(ckey@ =~= ck(sv) && coffs@ =~= cseg_col(sv).offsets && cbytes@ =~= cseg_col(sv).bytes);
    }
    let base: i64 = if nc > 0 { ckey[0] } else { 0 };
    let cc = CustCols { ckey, offs: coffs, bytes: cbytes, seg, seg_len, bytes_len: nbytes, nc, base };
    let c = ScanCols { lkey, lship, lprice, ldisc, okey, ocust, odate, nl, no, nc, cbase: base, dl };
    assert(cust_cols_ok(cc, sv, seg@));
    assert(general_ok(c, cc, sv, seg@, dlg));
    // fast path (the tasks select the top 10 of their interior runs; only a few runs per task are combined)
    let mut fast: Option<(Vec<usize>, Vec<i128>)> = None;
    if (nl as u64) <= NL_MAX {
        assert(scan_cols_ok(c, sv, seg@, dlg));
        let (bits, positional) = match plan::customer_pass(cc, workers, dispatch, Ghost(sv), Ghost(seg@)) {
            Ok(x) => x,
            Err(e) => { return Err(QueryError::WorkerFailed(e)); },
        };
        if positional {
            fast = match plan::scan_pass(c, bits, workers, dispatch, Ghost(sv), Ghost(seg@), Ghost(dlg), Ghost(ps)) {
                Ok(g) => g,
                Err(e) => { return Err(QueryError::WorkerFailed(e)); },
            };
        }
    }
    // general path when the fast path's checks failed
    let (sel, ss, groups) = match fast {
        Some(g) => {
            let (sel, ss) = g;
            (sel, ss, Ghost(combine::qual(sv, ps)))
        },
        None => {
          let fb = general_groups(c, cc, Ghost(sv), Ghost(seg@), Ghost(dlg));
          match fb {
            Fallback::Groups(gj, gs) => {
                assert(seg_of(ps) == seg@ && dl_of(ps) == dlg);
                assert(gj@.len() == gs@.len());
                assert(forall|g: int, h: int| 0 <= g < h < gj@.len() ==> gj@[g] < gj@[h]);
                assert(forall|g: int| 0 <= g < gj@.len() ==> (#[trigger] gj@[g] as int) < n_o(sv));
                assert(forall|g: int| 0 <= g < gj@.len() ==> #[trigger] gs@[g] as int == order_sum(sv, seg_of(ps), dl_of(ps), gj@[g] as int, 0, n_l(sv))
                    && order_count(sv, seg_of(ps), dl_of(ps), gj@[g] as int, 0, n_l(sv)) > 0
                    && order_abs(sv, seg_of(ps), dl_of(ps), gj@[g] as int, 0, n_l(sv)) <= i128_max());
                assert(forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv)) > 0 ==> gj@.contains(j as usize));
                assert(final_groups(gj@, gs@, sv, ps));
                proof {
                    assert forall|a: int, b: int| 0 <= a < gj@.len() && 0 <= b < gj@.len() && a != b implies gj@[a] != gj@[b] by {
                        if a < b { assert(gj@[a] < gj@[b]); } else { assert(gj@[b] < gj@[a]); }
                    }
                    assert forall|g: int| 0 <= g < gj@.len() implies #[trigger] gs@[g] as int == topk::fin(sv, ps)(gj@[g] as int) by {
                        assert(gs@[g] as int == order_sum(sv, seg_of(ps), dl_of(ps), gj@[g] as int, 0, n_l(sv)));
                    }
                }
                assert(groups_final(gj@, gs@, sv, ps));
                let (sel, ss) = topk::top10(&gj, &gs, odate, Ghost(sv), Ghost(ps));
                proof {
                    lemma_final_answer(gj@, gs@, sv, ps);
                }
                (sel, ss, Ghost(gj@.map_values(|x: usize| x as int)))
            },
            Fallback::Overflow(m) => {
                proof {
                    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                        capacity::lemma_capacity(sv, db, ps, m as int);
                    }
                }
                return Ok(Answer::Capacity);
            },
          }
        },
    };
    assert(answer_ok(sel@, ss@, groups@, sv, ps));
    // the output rows
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut k: usize = 0;
    while k < sel.len()
        invariant
            k <= sel@.len(), sel@.len() == ss@.len(), rows@.len() == k,
            okey@ == ok(sv), odate@ == od(sv), oship@ == os(sv),
            ok(sv).len() == n_o(sv), od(sv).len() == n_o(sv), os(sv).len() == n_o(sv),
            forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] od(sv)[j] as int - 10957 >= -2451545,
            forall|q: int| 0 <= q < sel@.len() ==> (#[trigger] sel@[q] as int) < n_o(sv),
            forall|q: int| 0 <= q < sel@.len() ==> #[trigger] ss@[q] as int == order_sum(sv, seg_of(ps), dl_of(ps), sel@[q] as int, 0, n_l(sv)),
            forall|q: int| 0 <= q < k ==> view_row(#[trigger] rows@[q]@) == group_row(sv, ps, sel@[q] as int),
        decreases sel@.len() - k,
    {
        let row = output_row(okey, odate, oship, sel[k], ss[k], Ghost(sv));
        rows.push(row);
        k = k + 1;
    }
    proof {
        let sel_i = sel@.map_values(|x: usize| x as int);
        let out = sel_i.map_values(|j: int| group_row(sv, ps, j));
        assert(view_rows(rows@) =~= out) by {
            assert forall|q: int| 0 <= q < out.len() implies view_rows(rows@)[q] == out[q] by {
                assert(view_rows(rows@)[q] == view_row(rows@[q]@));
            }
        }
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
            lemma_answer(sv, db, ps, groups@, sel_i);
        }
    }
    Ok(Answer::Rows(rows))
}

} // verus!
