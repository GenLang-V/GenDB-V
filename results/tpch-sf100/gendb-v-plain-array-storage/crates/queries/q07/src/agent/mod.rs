//! TPC-H Q7 (volume shipping) over the flat storages: revenue between the nations `$1` and `$2` (either as the
//! supplier's or the customer's nation) per supplier nation, customer nation and ship year 1995/1996.
//!
//! Plan of a call (`query`):
//! 1. nation tags (`tags::nation_tags`): 1 when the name is `$1`, plus 2 when it is `$2`;
//! 2. supplier and customer passes (`plan::tag_pass`, parallel): the suppliers' and the customers' nation tags
//!    (2 bits each), and whether the supplier and customer keys are positional (`key == key[0] + row`), so a key
//!    finds its row by subtraction;
//! 3. lineitem scan (`plan::scan_pass`, one task per worker over row ranges, `scan`): per 64-row word a vectorized
//!    mask of the rows shipped in 1995-1996, then the supplier's tag on its set bits; for the remaining candidates
//!    (about 2.4%), in small batches, the order (`l_orderkey` at its dbgen position, checked) and its customer's tag
//!    decide whether the row qualifies and its group, and four groups accumulate count, volume and absolute volume. When the keys are not positional, the general serial
//!    scan (`plan::general_pass`) computes the same sums;
//! 4. an absolute volume beyond `i128::MAX` answers `Capacity` (`capacity`); otherwise the non-empty groups in
//!    ORDER BY order (`answer::out_grp`).
//! The proof: the statement's body is a GROUP BY over the projected product of six tables (`denotation`); the
//! primary keys collapse every group's sum over the product to a sum over lineitem rows (`groups`), the rows'
//! groups and tags (`lines`); `answer` and `capacity` state the fixed claim for each outcome.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::{answer_meets, stores_ready, bound_db, outcome_ok, Answer};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::{EVal, view_row};
use crate::exec::text::lex_cmp_exec;
use crate::spec::text::lex_cmp;
use crate::link::query::view_rows;
use crate::link::expr::i128_max;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;

pub mod common;
pub mod tables;
pub mod dates;
pub mod normal_form;
pub mod denotation;
pub mod lines;
pub mod groups;
pub mod scan;
pub mod tags;
pub mod plan;
pub mod answer;
pub mod capacity;

use tables::*;
use normal_form::*;
use lines::*;
use scan::*;
use tags::*;
use plan::*;
use answer::*;

verus! {

/// A copy of a byte slice.
fn copy_bytes(p: &[u8]) -> (v: Vec<u8>)
    ensures v@ == p@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len(), v@ == p@.subrange(0, i as int),
        decreases p@.len() - i,
    {
        v.push(p[i]);
        i = i + 1;
        proof { assert(v@ =~= p@.subrange(0, i as int)); }
    }
    proof { assert(v@ =~= p@); }
    v
}

/// The output row of group `g` with volume sum `s`: `supp_nation, cust_nation, l_year, revenue`.
fn group_row(p1: &[u8], p2: &[u8], g: usize, s: i128, Ghost(ps): Ghost<Seq<Literal>>) -> (row: Vec<EVal>)
    requires g < 4, p1@ == p1_of(ps), p2@ == p2_of(ps),
    ensures view_row(row@) == grp_row(ps, g as int, s as int),
{
    let (a, b) = if g < 2 { (p1, p2) } else { (p2, p1) };
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Text(copy_bytes(a)));
    row.push(EVal::Text(copy_bytes(b)));
    row.push(EVal::Num { coeff: if g % 2 == 0 { 1995 } else { 1996 }, scale: 0 });
    row.push(EVal::Num { coeff: s, scale: 4 });
    proof {
        assert(view_row(row@) =~= grp_row(ps, g as int, s as int));
    }
    row
}

/// The output rows: the non-empty groups in ORDER BY order (`answer::out_grp`).
fn output_rows(acc: &Acc, p1: &[u8], p2: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<Vec<EVal>>, Ghost<Seq<int>>))
    requires acc_ok(*acc, sv, ps, 0, n_l(sv)), p1@ == p1_of(ps), p2@ == p2_of(ps),
    ensures sel_ok(sv, ps, r.1@), view_rows(r.0@) == answer_rows(sv, ps, r.1@),
{
    let first = lex_cmp_exec(&copy_bytes(p1), &copy_bytes(p2)) <= 0;
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let ghost mut sel: Seq<int> = Seq::empty();
    let mut q: usize = 0;
    while q < 4
        invariant
            acc_ok(*acc, sv, ps, 0, n_l(sv)), p1@ == p1_of(ps), p2@ == p2_of(ps),
            first == (lex_cmp(p1_of(ps), p2_of(ps)) <= 0), q <= 4,
            forall|i: int| 0 <= i < sel.len() ==> 0 <= #[trigger] sel[i] < q,
            forall|i: int, j: int| 0 <= i < j < sel.len() ==> #[trigger] sel[i] < #[trigger] sel[j],
            forall|i: int| 0 <= i < sel.len() ==> lsum(sv, ps, out_grp(ps, #[trigger] sel[i]), 0, 0, n_l(sv)) > 0,
            forall|x: int| 0 <= x < q && lsum(sv, ps, out_grp(ps, x), 0, 0, n_l(sv)) > 0 ==> #[trigger] sel.contains(x),
            view_rows(rows@) == answer_rows(sv, ps, sel),
        decreases 4 - q,
    {
        let g: usize = if first { q } else { if q < 2 { q + 2 } else { q - 2 } };
        assert(g as int == out_grp(ps, q as int));
        let n = acc.cnt[g];
        if n > 0 {
            let row = group_row(p1, p2, g, acc.sum[g], Ghost(ps));
            let ghost rows0 = rows@;
            let ghost sel0 = sel;
            rows.push(row);
            proof {
                sel = sel.push(q as int);
                assert(view_rows(rows@) =~= answer_rows(sv, ps, sel)) by {
                    assert(view_rows(rows@) =~= view_rows(rows0).push(view_row(rows@[rows@.len() - 1]@)));
                    assert(answer_rows(sv, ps, sel) =~= answer_rows(sv, ps, sel0).push(
                        grp_row(ps, g as int, lsum(sv, ps, g as int, 1, 0, n_l(sv)))));
                }
                assert forall|x: int| 0 <= x < q + 1 && lsum(sv, ps, out_grp(ps, x), 0, 0, n_l(sv)) > 0 implies #[trigger] sel.contains(x) by {
                    if x < q {
                        assert(sel0.contains(x));
                        let i = choose|i: int| 0 <= i < sel0.len() && sel0[i] == x;
                        assert(sel[i] == x);
                    } else {
                        assert(sel[sel.len() - 1] == x);
                    }
                }
            }
        } else {
            proof {
                assert forall|x: int| 0 <= x < q + 1 && lsum(sv, ps, out_grp(ps, x), 0, 0, n_l(sv)) > 0 implies #[trigger] sel.contains(x) by {
                    if x == q {
                        assert(lsum(sv, ps, out_grp(ps, x), 0, 0, n_l(sv)) == n as int);
                    }
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert forall|g: int| 0 <= g < 4 implies #[trigger] lsum(sv, ps, g, 2, 0, n_l(sv)) <= i128_max() by {
            assert(acc.abs@[g] as int == lsum(sv, ps, g, 2, 0, n_l(sv)));
        }
    }
    (rows, Ghost(sel))
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
        assert forall|l: int| 0 <= l < n_l(sv) implies num15(#[trigger] lpr(sv)[l]) && num15(ldc(sv)[l]) by {
            lemma_lineitem_row(sv, db0, l);
        }
    }
    let p1: &'static [u8] = params.p0;
    let p2: &'static [u8] = params.p1;
    assert(p1@ == p1_of(ps) && p2@ == p2_of(ps));
    // the columns (whole parts; the scans touch only what they need)
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let lokey = stores.flat_lineitem.extent_i64(li::L_ORDERKEY, 0, nl);
    let lsupp = stores.flat_lineitem.extent_i64(li::L_SUPPKEY, 0, nl);
    let lship = stores.flat_lineitem.extent_i32(li::L_SHIPDATE, 0, nl);
    let lprice = stores.flat_lineitem.extent_i128(li::L_EXTENDEDPRICE, 0, nl);
    let ldisc = stores.flat_lineitem.extent_i128(li::L_DISCOUNT, 0, nl);
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let okey = stores.flat_orders.extent_i64(oi::O_ORDERKEY, 0, no);
    let ocust = stores.flat_orders.extent_i64(oi::O_CUSTKEY, 0, no);
    let nc = stores.flat_customer.part_len(ci::C_CUSTKEY);
    let ckey = stores.flat_customer.extent_i64(ci::C_CUSTKEY, 0, nc);
    let cnat = stores.flat_customer.extent_i64(ci::C_NATIONKEY, 0, nc);
    let ns = stores.flat_supplier.part_len(si::S_SUPPKEY);
    let skey = stores.flat_supplier.extent_i64(si::S_SUPPKEY, 0, ns);
    let snat = stores.flat_supplier.extent_i64(si::S_NATIONKEY, 0, ns);
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    let nkey = stores.flat_nation.extent_i64(ni::N_NATIONKEY, 0, nn);
    let noffs_len = stores.flat_nation.part_len(ni::N_NAME_OFFSETS);
    let noffs = stores.flat_nation.extent_i64(ni::N_NAME_OFFSETS, 0, noffs_len);
    let nbytes_len = stores.flat_nation.part_len(ni::N_NAME_BYTES);
    let nbytes = stores.flat_nation.extent_u8(ni::N_NAME_BYTES, 0, nbytes_len);
    proof {
        assert(stores@ == sv);
        assert(lokey@ =~= lok(sv) && lsupp@ =~= lsk(sv) && lship@ =~= lsd(sv) && lprice@ =~= lpr(sv) && ldisc@ =~= ldc(sv));
        assert(okey@ =~= ok(sv) && ocust@ =~= oc(sv));
        assert(ckey@ =~= ck(sv) && cnat@ =~= cn(sv) && skey@ =~= sk(sv) && snat@ =~= sn(sv));
        assert(nkey@ =~= nk(sv) && noffs@ =~= nname_col(sv).offsets && nbytes@ =~= nname_col(sv).bytes);
    }
    // 1. nation tags
    let nation = NationCols { nkey, offs: noffs, bytes: nbytes, nn };
    let ntag_v = nation_tags(&nation, p1, p2, Ghost(sv), Ghost(ps));
    let ntag = Arc::new(ntag_v);
    // 2. the supplier and customer tags and the key checks
    let sbase: i64 = if ns > 0 { skey[0] } else { 0 };
    let cbase: i64 = if nc > 0 { ckey[0] } else { 0 };
    let mut spos = false;
    let mut cpos = false;
    let mut swords: Vec<u64> = Vec::new();
    let mut cwords: Vec<u64> = Vec::new();
    if ns < usize::MAX / 2 {
        let scols = KeyCols { keys: skey, nats: snat, n: ns, base: sbase };
        let (w, p) = match tag_pass(scols, nation, ntag.clone(), workers, dispatch, Ghost(sv), Ghost(ps)) {
            Ok(x) => x,
            Err(e) => { return Err(QueryError::WorkerFailed(e)); },
        };
        swords = w;
        spos = p;
        if spos && nc < usize::MAX / 2 {
            let ccols = KeyCols { keys: ckey, nats: cnat, n: nc, base: cbase };
            let (w, p) = match tag_pass(ccols, nation, ntag.clone(), workers, dispatch, Ghost(sv), Ghost(ps)) {
                Ok(x) => x,
                Err(e) => { return Err(QueryError::WorkerFailed(e)); },
            };
            cwords = w;
            cpos = p;
        }
    }
    let fast = spos && cpos && ns as u64 <= i64::MAX as u64 && nc as u64 <= i64::MAX as u64
        && (sbase as i128) + (ns as i128) <= i64::MAX as i128 && (cbase as i128) + (nc as i128) <= i64::MAX as i128;
    let send: i64 = if fast { (sbase as i128 + ns as i128) as i64 } else { 0 };
    let cend: i64 = if fast { (cbase as i128 + nc as i128) as i64 } else { 0 };
    let c = ScanCols { lship, lsupp, lokey, lprice, ldisc, okey, ocust, nl, no, ns, nc, sbase, send, cbase, cend };
    assert(line_cols_ok(c, sv));
    // 3. the lineitem scan
    let totals = if fast {
        assert(scan_cols_ok(c, sv));
        match scan_pass(c, Arc::new(swords), Arc::new(cwords), workers, dispatch, Ghost(sv), Ghost(ps)) {
            Ok(t) => t,
            Err(e) => { return Err(QueryError::WorkerFailed(e)); },
        }
    } else {
        let gc = GenCols { cols: c, skey, snat, ckey, cnat };
        general_pass(&gc, &nation, &*ntag, Ghost(sv), Ghost(ps))
    };
    // 4. the answer
    match totals {
        Totals::Over(g) => {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                    capacity::lemma_capacity(sv, db, ps, g as int);
                }
            }
            Ok(Answer::Capacity)
        },
        Totals::Sums(acc) => {
            let (rows, sel) = output_rows(&acc, p1, p2, Ghost(sv), Ghost(ps));
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
                    lemma_answer(sv, db, ps, sel@);
                }
            }
            Ok(Answer::Rows(rows))
        },
    }
}

} // verus!
