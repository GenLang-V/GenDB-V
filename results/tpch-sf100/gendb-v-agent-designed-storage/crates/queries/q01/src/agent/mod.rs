// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
// Required item: fn query; its exact obligations: final-claim.json
//
// TPC-H Q1 over storage `li_pairmask` (storage `facts` unchanged: lineitem stored by order date, frame-of-reference
// coded, 65536-row blocks with shipdate zone maxima; plus one 64-bit mask per 2048-row chunk of the (l_returnflag,
// l_linestatus) code pairs present, so most chunks are scanned without reading either code column). Plan:
// - `spec`: the statement as an accumulator normal form (`link::query::QuerySpec`) and the proof that its SQL
//   body denotes the normal form's rows (or the exact SQL error / capacity outcome);
// - `model`, `rows`: the stored columns as an integer model, and the bridge from the storage's `represents` to
//   per-key sums over the stored rows (a permutation of the canonical rows);
// - `fast`, `scan`, `stride`, `pairmask`: the parallel vectorized scan into a dense group table, when every block's
//   bases are small and the dictionaries tiny (always for TPC-H data); task `k` of `s` takes blocks `k, k + s, ...`
//   (round-robin), a single task runs on the calling thread;
// - `general`: an exact serial scan per key for every other input;
// - `finish`: the answer from the per-key entries (rows already in ORDER BY order: the dictionaries are sorted).
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok, capacity_domain};
use crate::gendb_entry::stores::{Stores, stored_ok};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::layout::PartView;
use crate::gendb_params::Params;
use crate::exec::value::EVal;
use crate::exec::ast::{ELiteral, view_lit};
use crate::exec::expr::lit_exec;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::order::{ordered_ok, denote_body};
use crate::link::query::*;
use crate::query::{param_domain, query_spec_at};
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::declaration::stored_relations;
use crate::stores::li_pairmask::interface as LP;
use crate::stores::li_pairmask::declaration as LD;

pub mod common;
pub mod spec;
pub mod model;
pub mod rows;
pub mod finish;
pub mod general;
pub mod scan;
pub mod fast;
pub mod kern;
pub mod pairmask;
pub mod stride;

use spec::*;
use model::*;
use rows::*;
use finish::*;
use fast::{Cols, cols_model, masks_hold, MAXT};
use scan::{fast_ok, fast_table, table_entries};
use general::general_entries;

verus! {

/// Every block's bases are within the fast path's bounds.
fn blocks_ok(cols: &Cols, ng: usize, Ghost(m): Ghost<Model>) -> (b: bool)
    requires m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), model_wf(m), ng == m.nb,
    ensures b ==> forall|g: int| 0 <= g < m.nb ==> #[trigger] block_ok(m, g),
{
    let mut g: usize = 0;
    while g < ng
        invariant
            m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), model_wf(m), ng == m.nb, g <= ng,
            forall|g2: int| 0 <= g2 < g ==> #[trigger] block_ok(m, g2),
        decreases ng - g,
    {
        let q = cols.qty_b[g];
        let pr = cols.price_b[g];
        let d = cols.disc_b[g];
        let t = cols.tax_b[g];
        let s = cols.ship_b[g];
        let r = cols.rf_b[g];
        let l = cols.ls_b[g];
        if !(-0x1_0000_0000 <= q && q <= 0x1_0000_0000 && -0x1_0000_0000 <= pr && pr <= 0x1_0000_0000
            && 0 <= d && d <= 100 && 0 <= t && t <= 100 && -0x100_0000_0000 <= s && s <= 0x100_0000_0000
            && r <= 0x1_0000_0000 && l <= 0x1_0000_0000) {
            return false;
        }
        g = g + 1;
    }
    true
}

/// The lineitem parts of the storage use.
pub open spec fn li_tp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int)
}

/// Every database bound to the parts: its lineitem relation is represented by the lineitem parts.
proof fn lemma_bound_dbs(sv: crate::gendb_entry::stores::StoresView, tp: Seq<PartView>)
    requires tp == li_tp(sv.li_pairmask),
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> db.schema == crate::schema::schema_spec()
        && crate::spec::typing::db_wf(db) && lineitem_ok(tp, lineitem_rel(db)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies db.schema == crate::schema::schema_spec()
        && crate::spec::typing::db_wf(db) && lineitem_ok(tp, lineitem_rel(db)) by {
        assert(stored_ok(sv, db));
        assert(LP::represents(sv.li_pairmask, LD::stored_relations(db)));
        assert(LD::stored_relations(db) =~= stored_relations(db));
        let fp = LP::facts_parts(sv.li_pairmask);
        assert(represents(fp, stored_relations(db)));
        assert(li_tp(fp) =~= tp);
    }
}

/// With an empty dictionary there is no stored row, and the empty answer is the only allowed one.
proof fn lemma_empty_answer(sv: crate::gendb_entry::stores::StoresView, tp: Seq<PartView>, ps: Seq<Literal>, rows: Vec<Vec<EVal>>)
    requires
        rows@.len() == 0,
        tp == li_tp(sv.li_pairmask), param_domain(ps),
        tp_model(tp).nrf <= 0 || tp_model(tp).nls <= 0,
        forall|db: Database| #[trigger] bound_db(sv, db) ==> db.schema == crate::schema::schema_spec()
            && crate::spec::typing::db_wf(db) && lineitem_ok(tp, lineitem_rel(db)),
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        let rel = lineitem_rel(db);
        lemma_tp_lengths(tp, rel);
        lemma_tp_bounds(tp, rel);
        if rel.len() > 0 {
            assert(0 <= rfi(tp_model(tp), 0) < tp_model(tp).nrf);
            assert(0 <= lsi(tp_model(tp), 0) < tp_model(tp).nls);
        }
        assert(rel =~= Seq::<Row>::empty());
        let g = q1_spec(param_day(ps));
        lemma_caps_empty(g);
        lemma_body_rows(db, ps);
        lemma_query_shape(ps);
        let out: Seq<Row> = view_rows(rows@);
        assert(out =~= Seq::<Row>::empty());
        lemma_empty_grouped(g, q1_order_keys(), 0, None, out);
        lemma_ordered_link(db, query_spec_at(ps), g, rel, out);
    }
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost parts = sv.li_pairmask;
    let ghost tp = li_tp(parts);
    let ghost dbs = |db: Database| bound_db(sv, db);
    let ghost db0 = choose|db: Database| bound_db(sv, db);
    proof {
        lemma_bound_dbs(sv, tp);
        assert(bound_db(sv, db0));
        lemma_tp_lengths(tp, lineitem_rel(db0));
        assert(stored_ok(sv, db0));
        assert(LP::represents(parts, LD::stored_relations(db0)));
        assert(parts.len() == LP::LI_PAIRMASK_PARTS);
        assert forall|i: int| 0 <= i < LI_PARTS implies #[trigger] tp[i] == parts[i] by {}
    }
    let ghost m = tp_model(tp);
    // the parameter: its day number
    let lit = ELiteral::Date { y: params.p0.y, m: params.p0.m, d: params.p0.d };
    proof {
        assert(view_lit(lit) == ps[0]);
        lemma_param_lit(ps);
    }
    let p: i64 = match lit_exec(&lit) {
        Ok(EVal::Date(d)) => d as i64,
        _ => {
            proof { assert(false); }
            return Err(QueryError::Malformed);
        },
    };
    assert(p as int == param_day(ps));
    // the lineitem parts (whole parts, zero-copy)
    let s = &mut stores.li_pairmask;
    let li = LINEITEM_FIRST;
    let layout = s.extent_u64(li + LI_LAYOUT, 0, 2);
    let bsize64 = layout[1];
    let n = s.part_len(li + LI_QUANTITY_CODES);
    let ng = s.part_len(li + LI_QUANTITY_BASE);
    let nmk = s.part_len(LP::PAIR_MASKS);
    let cols = Cols {
        qty: s.extent_u16(li + LI_QUANTITY_CODES, 0, n),
        qty_b: s.extent_i64(li + LI_QUANTITY_BASE, 0, ng),
        price: s.extent_u32(li + LI_EXTENDEDPRICE_CODES, 0, n),
        price_b: s.extent_i64(li + LI_EXTENDEDPRICE_BASE, 0, ng),
        disc: s.extent_u8(li + LI_DISCOUNT_CODES, 0, n),
        disc_b: s.extent_i64(li + LI_DISCOUNT_BASE, 0, ng),
        tax: s.extent_u8(li + LI_TAX_CODES, 0, n),
        tax_b: s.extent_i64(li + LI_TAX_BASE, 0, ng),
        rf: s.extent_u8(li + LI_RETURNFLAG_CODES, 0, n),
        rf_b: s.extent_u64(li + LI_RETURNFLAG_BASE, 0, ng),
        ls: s.extent_u8(li + LI_LINESTATUS_CODES, 0, n),
        ls_b: s.extent_u64(li + LI_LINESTATUS_BASE, 0, ng),
        ship: s.extent_u16(li + LI_SHIPDATE_CODES, 0, n),
        ship_b: s.extent_i64(li + LI_SHIPDATE_BASE, 0, ng),
        ship_z: s.extent_i64(li + LI_SHIPDATE_ZMAX, 0, ng),
        mk: s.extent_u64(LP::PAIR_MASKS, 0, nmk),
        nmk,
    };
    let rf_off_len = s.part_len(li + LI_RETURNFLAG_DICT_OFFS);
    let rf_offs = s.extent_u64(li + LI_RETURNFLAG_DICT_OFFS, 0, rf_off_len);
    let rf_bytes_len = s.part_len(li + LI_RETURNFLAG_DICT_BYTES);
    let rf_bytes = s.extent_u8(li + LI_RETURNFLAG_DICT_BYTES, 0, rf_bytes_len);
    let ls_off_len = s.part_len(li + LI_LINESTATUS_DICT_OFFS);
    let ls_offs = s.extent_u64(li + LI_LINESTATUS_DICT_OFFS, 0, ls_off_len);
    let ls_bytes_len = s.part_len(li + LI_LINESTATUS_DICT_BYTES);
    let ls_bytes = s.extent_u8(li + LI_LINESTATUS_DICT_BYTES, 0, ls_bytes_len);
    proof {
        let ps_ = parts;
        assert(cols.qty@ =~= u16s(tp[LI_QUANTITY_CODES as int]));
        assert(cols.qty_b@ =~= i64s(tp[LI_QUANTITY_BASE as int]));
        assert(cols.price@ =~= u32s(tp[LI_EXTENDEDPRICE_CODES as int]));
        assert(cols.price_b@ =~= i64s(tp[LI_EXTENDEDPRICE_BASE as int]));
        assert(cols.disc@ =~= u8s(tp[LI_DISCOUNT_CODES as int]));
        assert(cols.disc_b@ =~= i64s(tp[LI_DISCOUNT_BASE as int]));
        assert(cols.tax@ =~= u8s(tp[LI_TAX_CODES as int]));
        assert(cols.tax_b@ =~= i64s(tp[LI_TAX_BASE as int]));
        assert(cols.rf@ =~= u8s(tp[LI_RETURNFLAG_CODES as int]));
        assert(cols.rf_b@ =~= u64s(tp[LI_RETURNFLAG_BASE as int]));
        assert(cols.ls@ =~= u8s(tp[LI_LINESTATUS_CODES as int]));
        assert(cols.ls_b@ =~= u64s(tp[LI_LINESTATUS_BASE as int]));
        assert(cols.ship@ =~= u16s(tp[LI_SHIPDATE_CODES as int]));
        assert(cols.ship_b@ =~= i64s(tp[LI_SHIPDATE_BASE as int]));
        assert(cols.ship_z@ =~= i64s(tp[LI_SHIPDATE_ZMAX as int]));
        assert(rf_offs@ =~= u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]));
        assert(rf_bytes@ =~= u8s(tp[LI_RETURNFLAG_DICT_BYTES as int]));
        assert(ls_offs@ =~= u64s(tp[LI_LINESTATUS_DICT_OFFS as int]));
        assert(ls_bytes@ =~= u8s(tp[LI_LINESTATUS_DICT_BYTES as int]));
        assert(cols_model(cols, m.n, m.bsize, m.nrf, m.nls) == m);
        assert(cols.mk@ =~= LP::pair_masks(parts));
        assert(LP::rf_codes(parts) == cols.rf@);
        assert(LP::ls_codes(parts) == cols.ls@);
        assert(masks_hold(cols));
    }
    if rf_off_len < 2 || ls_off_len < 2 {
        // an empty dictionary: no stored row
        let rows: Vec<Vec<EVal>> = Vec::new();
        proof {
            lemma_empty_answer(sv, tp, ps, rows);
        }
        return Ok(Answer::Rows(rows));
    }
    let nrf = rf_off_len - 1;
    let nls = ls_off_len - 1;
    proof {
        lemma_tp_model(tp, lineitem_rel(db0));
        assert forall|db: Database| #[trigger] dbs(db) implies db_ok(db, tp) by {}
    }
    // the fast path when its guards hold, else the exact general path
    let small = nrf <= MAXT && nls <= MAXT;
    if small {
        assert(nrf * nls <= MAXT * MAXT) by (nonlinear_arith) requires nrf <= MAXT, nls <= MAXT;
    }
    let t: usize = if small { nrf * nls } else { MAXT + 1 };
    let fast = t <= MAXT && bsize64 <= (usize::MAX - n) as u64 && ng <= usize::MAX / 64 && blocks_ok(&cols, ng, Ghost(m));
    let es = if fast {
        let bsize = bsize64 as usize;
        proof {
            assert(m.nb * 64 <= usize::MAX) by (nonlinear_arith) requires m.nb <= usize::MAX / 64;
            assert(fast_ok(m, nrf as int, nls as int, t as int, p as int));
        }
        match fast_table(cols, n, bsize, nrf, nls, t, p, workers, dispatch, Ghost(m)) {
            Ok((cnt, sum)) => table_entries(&cnt, &sum, nrf, nls, t, Ghost(m), Ghost(p as int)),
            Err(e) => return Err(QueryError::WorkerFailed(e)),
        }
    } else {
        general_entries(&cols, n, bsize64, nrf, nls, p, Ghost(m))
    };
    proof {
        assert(finish_pre(es@, rf_offs@, rf_bytes@, ls_offs@, ls_bytes@, tp, ps, dbs));
    }
    let r = finish_answer(&es, rf_offs, rf_bytes, ls_offs, ls_bytes, Ghost(tp), Ghost(ps), Ghost(dbs));
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), r) by {
            assert(dbs(db));
        }
    }
    r
}

} // verus!
