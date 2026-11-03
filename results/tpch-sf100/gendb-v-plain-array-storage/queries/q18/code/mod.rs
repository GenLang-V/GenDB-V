//! TPC-H Q18 (large volume customer) over the flat storages: the orders whose lineitems' total quantity exceeds
//! `$1`, with their customer's name and key, the order's key, date and total price and the quantity sum, top 100
//! by total price descending, then date.
//!
//! Plan of a call (`query`):
//! 1. read `l_orderkey`, `l_quantity`, `o_orderkey`, `o_custkey`, `o_totalprice`, `o_orderdate`, `c_custkey` and
//!    the `c_name` parts as whole stored parts (`read_cols`; nothing is copied);
//! 2. the subquery (`common::runplan::scan_all`): the lineitem rows are split into at most `workers` ranges that
//!    start at a change of `l_orderkey`; each range is scanned run by run of equal keys (`common::runscan`),
//!    keeping the keys whose quantity sum exceeds `100 * $1` (coefficients at scale 2); the range states are joined
//!    in order, checking that the keys ascend across ranges. When the keys are not in ascending runs, the general
//!    serial path sums every key over all rows instead;
//! 3. the candidates (`cands`): each such key's orders row and its customer's row (`lookup`: the row where dbgen
//!    puts the key, checked, else a search);
//! 4. the first 100 candidates by `o_totalprice DESC, o_orderdate` (`topk`), and their output rows.
//!
//! Proof: the subquery's IN condition is `subquery::in_sub` (`subquery`), the statement's body is the normal form
//! of `denotation`, whose groups are the qualifying orders with their per-key sums (`groups`); the candidates are
//! exactly those orders (`cands_ok`) and the selection a sorted top 100 (`topk::top_inv`), which `answer` turns
//! into the fixed claim. No `Capacity` outcome is possible: every SUM's absolute mass is at most
//! `n_l * 10^15 < i128::MAX`.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::{answer_meets, stores_ready, bound_db, outcome_ok, Answer};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::{EVal, view_row};
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::order::sorted_by;
use crate::link::query::{view_rows, text_wf};
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_lineitem::interface as li;

pub mod common;
pub mod tables;
pub mod lookup;
pub mod subquery;
pub mod denotation;
pub mod groups;
pub mod answer;
pub mod topk;
pub mod cands;

use tables::*;
use common::runscan::{Hit, vals_bounded, val_bound};
use common::runplan::scan_all;
use subquery::{thr_of, p_of, small};
use groups::*;
use answer::*;
use topk::{Cand, TOPK, top, top_inv, ccmp};
use cands::*;

verus! {

/// The stored columns the query reads (whole parts).
pub struct Cols {
    pub lkey: &'static [i64],
    pub lqty: &'static [i128],
    pub nl: usize,
    pub okey: &'static [i64],
    pub ocust: &'static [i64],
    pub oprice: &'static [i128],
    pub odate: &'static [i32],
    pub no: usize,
    pub ckey: &'static [i64],
    pub coffs: &'static [i64],
    pub cbytes: &'static [u8],
    pub nbytes: usize,
    pub nc: usize,
}

/// The handles are the stored columns of `sv`.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.lkey@ == lk(sv) && c.lqty@ == lq(sv) && c.nl as int == n_l(sv)
    &&& cand_cols_ok(c.okey, c.ocust, c.oprice, c.odate, c.no, c.ckey, c.nc, sv)
    &&& c.coffs@ == cname_col(sv).offsets && c.cbytes@ == cname_col(sv).bytes && c.cbytes@.len() == c.nbytes
    &&& text_wf(cname_col(sv), n_c(sv))
}

/// Read the columns (one extent per part, the whole part).
fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires old(stores)@ == sv, cols_facts(sv),
    ensures final(stores)@ == sv, cols_ok(c, sv),
{
    proof {
        assert(li::parts_wf(sv.flat_lineitem, n_l(sv)));
        assert(oi::parts_wf(sv.flat_orders, n_o(sv)));
        assert(ci::parts_wf(sv.flat_customer, n_c(sv)));
    }
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let lkey = stores.flat_lineitem.extent_i64(li::L_ORDERKEY, 0, nl);
    let lqty = stores.flat_lineitem.extent_i128(li::L_QUANTITY, 0, nl);
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let okey = stores.flat_orders.extent_i64(oi::O_ORDERKEY, 0, no);
    let ocust = stores.flat_orders.extent_i64(oi::O_CUSTKEY, 0, no);
    let oprice = stores.flat_orders.extent_i128(oi::O_TOTALPRICE, 0, no);
    let odate = stores.flat_orders.extent_i32(oi::O_ORDERDATE, 0, no);
    let nc = stores.flat_customer.part_len(ci::C_CUSTKEY);
    let ckey = stores.flat_customer.extent_i64(ci::C_CUSTKEY, 0, nc);
    let noffs = stores.flat_customer.part_len(ci::C_NAME_OFFSETS);
    let coffs = stores.flat_customer.extent_i64(ci::C_NAME_OFFSETS, 0, noffs);
    let nbytes = stores.flat_customer.part_len(ci::C_NAME_BYTES);
    let cbytes = stores.flat_customer.extent_u8(ci::C_NAME_BYTES, 0, nbytes);
    proof {
        assert(lkey@ =~= lk(sv) && lqty@ =~= lq(sv));
        assert(okey@ =~= ok(sv) && ocust@ =~= oc(sv) && oprice@ =~= otp(sv) && odate@ =~= od(sv));
        assert(ckey@ =~= ck(sv) && coffs@ =~= cname_col(sv).offsets && cbytes@ =~= cname_col(sv).bytes);
    }
    Cols { lkey, lqty, nl, okey, ocust, oprice, odate, no, ckey, coffs, cbytes, nbytes, nc }
}

/// `b[s..e]` as a vector.
fn slice_sub(b: &'static [u8], s: usize, e: usize) -> (v: Vec<u8>)
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
        assert(v@ =~= b@.subrange(s as int, i as int));
    }
    v
}

/// The output row of candidate `x`: `c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice, sum_qty`.
fn output_row(c: &Cols, x: Cand, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (row: Vec<EVal>)
    requires cols_ok(*c, sv), cand_ok(x, sv, ps),
    ensures view_row(row@) == group_row(sv, x.o as int),
{
    let ghost (o, a) = (x.o as int, x.c as int);
    proof {
        let a0 = cust_of(sv, o);
        assert(crate::agent::lookup::has_key(ck(sv), oc(sv)[o]));
        assert(0 <= a0 < n_c(sv) && ck(sv)[a0] == oc(sv)[o]);
        assert(ck(sv)[a] == ck(sv)[a0]);
        assert(a == a0);
        let t = cname_col(sv);
        assert(0 <= t.offsets[a] <= t.offsets[a + 1] <= t.bytes.len());
        assert(od(sv)[o] as int - 10957 >= -2451545);
        denotation::lemma_date32(od(sv)[o]);
    }
    let s = c.coffs[x.c] as usize;
    let e = c.coffs[x.c + 1] as usize;
    let name = slice_sub(c.cbytes, s, e);
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Text(name));
    row.push(EVal::Int(c.ckey[x.c]));
    row.push(EVal::Int(c.okey[x.o]));
    row.push(EVal::Date(c.odate[x.o] - 10957));
    row.push(EVal::Num { coeff: x.price, scale: 2 });
    row.push(EVal::Num { coeff: x.sum, scale: 2 });
    proof {
        assert(view_row(row@) =~= group_row(sv, o));
    }
    row
}

/// The groups are the candidates' orders; the selection is the selected candidates' orders.
proof fn lemma_selection(sv: StoresView, ps: Seq<Literal>, cs: Seq<Cand>, sel: Seq<usize>)
    requires cands_ok(cs, sv, ps), top_inv(cs, cs.len() as int, sel), cs.len() <= usize::MAX,
    ensures ({
        let groups = cs.map_values(|e: Cand| e.o as int);
        let sel_o = sel.map_values(|i: usize| cs[i as int].o as int);
        &&& groups_complete(sv, ps, groups)
        &&& top_rows_ok(sv, groups, sel_o)
    }),
{
    let groups = cs.map_values(|e: Cand| e.o as int);
    let sel_o = sel.map_values(|i: usize| cs[i as int].o as int);
    let rows = sel_o.map_values(|j: int| group_row(sv, j));
    // groups
    assert(groups.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < groups.len() && 0 <= b < groups.len() && a != b implies groups[a] != groups[b] by {
            assert(cs[a].o != cs[b].o);
        }
    }
    assert forall|t: int| 0 <= t < groups.len() implies 0 <= #[trigger] groups[t] < n_o(sv) && ord_ok(sv, ps, groups[t]) by {
        assert(cand_ok(cs[t], sv, ps));
    }
    assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] ord_ok(sv, ps, j) implies groups.contains(j) by {
        let t = choose|t: int| 0 <= t < cs.len() && cs[t].o == j;
        assert(groups[t] == j);
    }
    // the selection
    assert forall|t: int| 0 <= t < sel_o.len() implies groups.contains(#[trigger] sel_o[t]) by {
        assert(groups[sel[t] as int] == sel_o[t]);
    }
    assert(sel_o.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < sel_o.len() && 0 <= b < sel_o.len() && a != b implies sel_o[a] != sel_o[b] by {
            assert(sel[a] != sel[b]);
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < rows.len() implies
        crate::spec::order::keys_cmp(denotation::q_order_keys(), #[trigger] rows[a], #[trigger] rows[b]) <= 0 by {
        let (x, y) = (cs[sel[a] as int], cs[sel[b] as int]);
        assert(cand_ok(x, sv, ps) && cand_ok(y, sv, ps));
        lemma_group_row_cmp(sv, x.o as int, y.o as int);
        assert(ccmp(x, y) <= 0);
    }
    if sel_o.len() > 0 {
        let last = cs[sel[sel.len() - 1] as int];
        assert(rows.last() == group_row(sv, last.o as int));
        assert forall|j: int| #[trigger] groups.contains(j) && !sel_o.contains(j)
            implies crate::spec::order::keys_cmp(denotation::q_order_keys(), rows.last(), group_row(sv, j)) <= 0 by {
            let x = choose|x: int| 0 <= x < groups.len() && groups[x] == j;
            assert(!sel.contains(x as usize)) by {
                if sel.contains(x as usize) {
                    let t = choose|t: int| 0 <= t < sel.len() && sel[t] == x as usize;
                    assert(sel[t] as int == x);
                    assert(sel_o[t] == cs[x].o as int);
                    assert(groups[x] == cs[x].o as int);
                    assert(sel_o[t] == j);
                }
            }
            assert(ccmp(last, cs[x]) <= 0);
            assert(cand_ok(last, sv, ps) && cand_ok(cs[x], sv, ps));
            lemma_group_row_cmp(sv, last.o as int, j);
        }
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
    let ghost db0 = choose|db: Database| bound_db(sv, db);
    proof {
        lemma_cols_facts(sv, db0);
    }
    let c = read_cols(stores, Ghost(sv));
    // $1 as a quantity coefficient (scale 2)
    let thr: i128 = (params.p0 as i128) * 100;
    proof {
        assert(p_of(ps) == params.p0 as int);
        assert(thr as int == thr_of(ps));
        assert(small(sv));
        assert forall|j: int| 0 <= j < c.lqty@.len() implies -val_bound() <= #[trigger] c.lqty@[j] <= val_bound() by {
            assert(num15(lq(sv)[j]));
        }
    }
    // the subquery: the order keys whose quantity sum exceeds $1
    let hits: Vec<Hit> = match scan_all(c.lkey, c.lqty, c.nl, thr, workers, dispatch) {
        Ok(h) => h,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    // their orders and customers, then the first 100 by o_totalprice DESC, o_orderdate
    let cands = build_cands(&hits, c.okey, c.ocust, c.oprice, c.odate, c.no, c.ckey, c.nc, Ghost(sv), Ghost(ps));
    let sel = top(&cands);
    let ghost sel_o = sel@.map_values(|i: usize| cands@[i as int].o as int);
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let ns = sel.len();
    let mut k: usize = 0;
    while k < ns
        invariant
            ns == sel@.len(), k <= ns, rows@.len() == k,
            cols_ok(c, sv), cands_ok(cands@, sv, ps), top_inv(cands@, cands@.len() as int, sel@),
            sel_o == sel@.map_values(|i: usize| cands@[i as int].o as int),
            forall|q: int| 0 <= q < k ==> view_row(#[trigger] rows@[q]@) == group_row(sv, sel_o[q]),
        decreases ns - k,
    {
        let x = cands[sel[k]];
        proof {
            assert(cand_ok(cands@[sel@[k as int] as int], sv, ps));
        }
        let row = output_row(&c, x, Ghost(sv), Ghost(ps));
        rows.push(row);
        k = k + 1;
    }
    proof {
        let groups = cands@.map_values(|e: Cand| e.o as int);
        lemma_selection(sv, ps, cands@, sel@);
        let out = sel_o.map_values(|j: int| group_row(sv, j));
        assert(view_rows(rows@) =~= out) by {
            assert forall|q: int| 0 <= q < out.len() implies view_rows(rows@)[q] == out[q] by {
                assert(view_rows(rows@)[q] == view_row(rows@[q]@));
            }
        }
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies
            outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
            lemma_answer(sv, db, ps, groups, sel_o);
        }
    }
    Ok(Answer::Rows(rows))
}

} // verus!
