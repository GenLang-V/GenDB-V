// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! TPC-H Q21 (suppliers who kept orders waiting) over the storages `li_ordruns` (facts' orders stored by o_orderdate
//! with lineitem co-clustered, read through li_ordruns' inherited parts, plus the run lengths of l_orderkey) and
//! `suppliers` (supplier and nation in canonical order). `facts` is declared only because li_ordruns' interface
//! refers to it; no part is read through it.
//!
//! Plan: on the calling thread read the column slices (`load`), find the o_orderstatus dictionary entry `F`, the
//! nation keys named `$1` and their suppliers as count slots (`side`), with a key-to-slot map (`supp`). The stored
//! orders are split into ranges, one worker task each (`run`, `kernel::ScanTask`): a task word-scans the lineitem
//! rows of its orders (`wscan`; order boundaries from the run lengths, `runs`), deciding exactly each candidate row (late, a slot supplier, not ruled out by its
//! neighbours) against the EXISTS and NOT EXISTS over its order's run and the order's status, and writes the
//! counting rows as an event list; the tail task also checks that the slot names are distinct. The events are summed
//! per slot, grouped by s_name (`groups`), and the top 100 by numwait DESC, s_name are kept (`cand`) and emitted.
//! Proof: `model`/`kernel` (scan), `bind` (model = stored rows), `sqlrow`/`sqllink` (SQL meaning in normal form),
//! `answer` (rows and errors are allowed outcomes).
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::filled;
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::stores::facts::interface::common::colfmt::{text_of, text_parts_wf, dict_sorted, lemma_dict_distinct};
use crate::spec::value::*;
use crate::exec::value::{EVal, view_row};
use crate::stores::facts::interface::common::read::dict_find;
use crate::stores::suppliers::interface::common::colfmt::text_range_ok;
use crate::stores::suppliers::interface::common::read::text_slice;

pub mod common;
pub mod model;
pub mod runs;
pub mod kernel;
pub mod wscan;
pub mod supp;
pub mod side;
pub mod cand;
pub mod groups;
pub mod bind;
pub mod load;
pub mod run;
pub mod sqlrow;
pub mod typed;
pub mod sqllink;
pub mod decode;
pub mod world;
pub mod answer;

use model::*;
use side::*;
use cand::*;
use groups::*;
use bind::*;
use load::*;

verus! {

/// The result row of a candidate.
fn cand_out(sc: &SCols, srows: &Vec<usize>, cd: Cand) -> (row: Vec<EVal>)
    requires
        scols_ok(*sc),
        cd.t < srows@.len() && srows@[cd.t as int] < sc.n_s,
        cd.cnt <= i64::MAX,
    ensures view_row(row@) == cand_row(*sc, srows@, cd),
{
    let r = srows[cd.t];
    assert(text_range_ok(sc.sm_offs@, sc.sm_bytes@, r as int));
    let name = vstd::slice::slice_to_vec(text_slice(sc.sm_offs, sc.sm_bytes, r));
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Text(name));
    row.push(EVal::Int(cd.cnt as i64));
    proof {
        assert(view_row(row@) =~= cand_row(*sc, srows@, cd));
    }
    row
}

/// `bound_db` gives both storages' bindings.
/// facts' parts inside storage `li_ordruns` (its first 75 parts).
pub open spec fn fparts(sv: StoresView) -> Seq<PartView> {
    crate::stores::li_ordruns::interface::facts_parts(sv.li_ordruns)
}

proof fn lemma_bound(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        fbound(db, fparts(sv)),
        sbound(db, sv.suppliers),
        bind::lo_bound(db, sv.li_ordruns),
{
    bind::lemma_lo_bound(db, sv.li_ordruns);
}

/// The status entry `'F'` found by `dict_find` (or none: `f` is the dictionary size, no entry's index).
proof fn lemma_fcode(doffs: Seq<u64>, dbytes: Seq<u8>, found: Option<usize>, f: int)
    requires
        doffs.len() >= 1,
        text_parts_wf(doffs, dbytes, doffs.len() - 1),
        dict_sorted(doffs, dbytes, doffs.len() - 1),
        found matches Some(x) ==> x < doffs.len() - 1 && text_of(doffs, dbytes, x as int) == sqlrow::f_text() && f == x,
        found is None ==> (forall|x: int| 0 <= x < doffs.len() - 1 ==> text_of(doffs, dbytes, x) != sqlrow::f_text())
            && f == doffs.len() - 1,
    ensures world::fcode_ok(doffs, dbytes, f),
{
    let k = doffs.len() - 1;
    assert forall|d: int| 0 <= d < k implies (#[trigger] text_of(doffs, dbytes, d) == sqlrow::f_text()) == (d == f) by {
        if let Some(x) = found {
            if d < x {
                lemma_dict_distinct(doffs, dbytes, k, d, x as int);
            } else if d > x {
                lemma_dict_distinct(doffs, dbytes, k, x as int, d);
            }
        }
    }
}

/// The slot keys are distinct: distinct supplier rows (the slots' rows increase) have distinct keys.
proof fn lemma_skeys_unique(db: Database, sparts: Seq<PartView>, sc: SCols, nks: Seq<i64>, srows: Seq<usize>, skeys: Seq<i64>)
    requires
        sbound(db, sparts), scols_from_parts(sc, sparts),
        slots_ok(sc, nks, srows, skeys),
    ensures supp::keys_unique(skeys),
{
    assert forall|a: int, b: int| 0 <= a < skeys.len() && 0 <= b < skeys.len() && a != b implies #[trigger] skeys[a] != #[trigger] skeys[b] by {
        if a < b {
            assert(srows[a] < srows[b]);
        } else {
            assert(srows[b] < srows[a]);
        }
        if skeys[a] == skeys[b] {
            world::lemma_skey_distinct(db, sparts, sc, srows[a] as int, srows[b] as int);
        }
    }
}

/// TPC-H Q21 over storages `facts` and `suppliers`.
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
    let ghost nm = params.p0@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_bound(sv, db0);
    }
    proof {
        bind::lemma_lo_bound(db0, sv.li_ordruns);
    }
    let (c, doffs, dbytes, flag) = open_facts(&mut stores.li_ordruns, Ghost(db0));
    let sc = open_suppliers(&mut stores.suppliers, Ghost(db0));
    proof {
        decode::lemma_orders_cols(db0, fparts(sv), c, doffs@, dbytes@);
    }
    let k = doffs.len() - 1;
    let mut fv: Vec<u8> = Vec::new();
    fv.push(70u8);
    proof {
        assert(fv@ =~= sqlrow::f_text());
    }
    let found = dict_find(doffs, dbytes, k, fv.as_slice(), 1);
    let f: u64 = match found {
        Some(d) => d as u64,
        None => k as u64,
    };
    proof {
        lemma_fcode(doffs@, dbytes@, found, f as int);
        decode::lemma_cols_ok(db0, fparts(sv), c, doffs@, dbytes@);
        decode::lemma_keys_distinct(db0, fparts(sv), c, doffs@, dbytes@);
        if flag == 1 {
            decode::lemma_clustered(db0, fparts(sv), c, doffs@, dbytes@);
        }
        world::lemma_scols_ok(db0, sv.suppliers, sc);
    }
    let (nks, nwit) = nation_keys(&sc, params.p0);
    let (srows, skeys) = nation_suppliers(&sc, &nks);
    proof {
        lemma_skeys_unique(db0, sv.suppliers, sc, nks@, srows@, skeys@);
    }
    let sm = supp::build_map(skeys);
    // The run scan needs one run per stored orders row and the last line's order present (`lemma_runs_aligned`).
    let mut runs = false;
    if flag == 1 && c.rl.len() == c.n_o && c.n_o > 0 && c.n_l > 0 {
        proof {
            decode::lemma_runs_model(db0, sv.li_ordruns, c);
        }
        if kernel::order_pos_at(&c, Ghost(k as int), c.n_l - 1) < c.n_o {
            proof {
                runs::lemma_runs_aligned(c);
            }
            runs = true;
        }
    }
    let (tot, inc) = match run::count_all(&c, k, &sm, f, runs, workers, dispatch, &sc, &srows) {
        Ok(v) => v,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost skv = sm.skeys@;
    // Every bound database's world: the models are its stored rows.
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies
            world::world_ok(db, fparts(sv), sv.suppliers, c, sc, doffs@, dbytes@, f as int)
            && answer::slots_res(c, sc, f as int, nm, nks@, nwit@, srows@, skv, tot@) by {
            lemma_bound(sv, db);
        }
    }
    let gs = match name_groups(&sc, &srows, &tot, inc) {
        Ok(gs) => gs,
        Err(t) => {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies
                    crate::gendb_entry::outcome_ok(db, query_spec_at(ps),
                        Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
                    answer::lemma_q21_count_err(db, fparts(sv), sv.suppliers, c, sc, doffs@, dbytes@, f as int, ps, nm,
                        nks@, nwit@, srows@, skv, tot@, t as int);
                }
            }
            return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
        },
    };
    // The top 100 of the name groups' rows.
    let mut buf: Vec<Cand> = filled(K, Cand { t: 0, cnt: 0 });
    let mut len: usize = 0;
    let ng = gs.len();
    proof {
        crate::agent::common::topk::lemma_topk_empty(q21_keys(), q21_fams(), K as nat);
        assert(cands_view(sc, srows@, buf@, 0) =~= Seq::<Row>::empty());
        assert(answer::all_rows(sc, srows@, gs@, 0) =~= Seq::<Row>::empty());
    }
    let mut i: usize = 0;
    while i < ng
        invariant
            scols_ok(sc),
            ng == gs@.len(),
            i <= ng,
            buf@.len() == K,
            len <= K,
            gs_ok(sc, srows@, tot@, gs@),
            forall|t: int| 0 <= t < srows@.len() ==> #[trigger] srows@[t] < sc.n_s,
            tot@.len() == srows@.len(),
            slots_in(sc, srows@, buf@, len as int),
            crate::agent::common::topk::topk_ok(q21_keys(), q21_fams(), K as nat, cands_view(sc, srows@, buf@, len as int),
                answer::all_rows(sc, srows@, gs@, i as int)),
        decreases ng - i,
    {
        let cd = gs[i];
        proof {
            answer::lemma_all_wf(sc, srows@, tot@, gs@, i + 1);
            assert(answer::all_rows(sc, srows@, gs@, i as int).push(cand_row(sc, srows@, cd))
                =~= answer::all_rows(sc, srows@, gs@, i + 1));
        }
        len = topk_insert(&sc, &srows, &mut buf, len, cd, Ghost(answer::all_rows(sc, srows@, gs@, i as int)));
        i = i + 1;
    }
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            scols_ok(sc),
            len <= buf@.len(),
            slots_in(sc, srows@, buf@, len as int),
            i <= len,
            crate::link::query::view_rows(rows@) == cands_view(sc, srows@, buf@, i as int),
        decreases len - i,
    {
        let cd = buf[i];
        let row = cand_out(&sc, &srows, cd);
        proof {
            crate::link::outcome::lemma_view_rows_push(rows@, row);
            assert(cands_view(sc, srows@, buf@, i + 1) =~= cands_view(sc, srows@, buf@, i as int).push(cand_row(sc, srows@, cd)));
        }
        rows.push(row);
        i = i + 1;
    }
    proof {
        let out = crate::link::query::view_rows(rows@);
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies
            crate::gendb_entry::outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
            answer::lemma_q21_ordered(db, fparts(sv), sv.suppliers, c, sc, doffs@, dbytes@, f as int, ps, nm, nks@, nwit@,
                srows@, skv, tot@, gs@, out);
        }
    }
    Ok(Answer::Rows(rows))
}

} // verus!
