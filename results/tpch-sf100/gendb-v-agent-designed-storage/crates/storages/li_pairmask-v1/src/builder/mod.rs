//! Builder of storage `li_pairmask`: the 75 parts of `facts` are inherited unchanged; this builder adds one U64 mask
//! per chunk of `MASK_ROWS` stored lineitem rows: bit `rf * 8 + ls` is set for every (l_returnflag, l_linestatus)
//! code pair `(rf, ls)` that occurs in the chunk (part `PAIR_MASKS`).
//!
//! Plan: one serial scan over facts' two code columns, chunk by chunk (`scan_masks`); a code of 8 or more makes the
//! part empty (it then states nothing).
//!
//! Proof: the scan's invariant states `row_marked` for every scanned row (`lemma_bit_or`: setting a bit keeps the
//! others; `lemma_chunk_of`: rows of chunk `k` divide to `k`); facts' `represents` gives that both code parts are U8
//! (`lemma_code_kinds`) and carries over unchanged to the inherited parts.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row};
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::facts::declaration as FD;
use crate::stores::li_pairmask::interface::*;
use crate::stores::li_pairmask::declaration as D;

verus! {

/// The lineitem parts of facts.
pub open spec fn li_tp(fp: Seq<PartView>) -> Seq<PartView> {
    fp.subrange(F::LINEITEM_FIRST as int, (F::LINEITEM_FIRST + F::LI_PARTS) as int)
}

/// Setting bit `x` sets it and keeps every bit already set.
proof fn lemma_bit_or(m: u64, x: u64, y: u64)
    requires x < 64, y < 64,
    ensures
        pair_bit(m | (1u64 << x), x),
        pair_bit(m, y) ==> pair_bit(m | (1u64 << x), y),
{
    assert(((m | (1u64 << x)) >> x) & 1u64 == 1u64) by (bit_vector)
        requires x < 64;
    assert(((m >> y) & 1u64 == 1u64) ==> (((m | (1u64 << x)) >> y) & 1u64 == 1u64)) by (bit_vector)
        requires x < 64, y < 64;
}

/// Row `j` of chunk `k` (rows `k * MASK_ROWS .. (k + 1) * MASK_ROWS`) has `j / MASK_ROWS == k`.
proof fn lemma_chunk_of(j: int, k: int)
    requires k * (MASK_ROWS as int) <= j < k * (MASK_ROWS as int) + MASK_ROWS,
    ensures j / (MASK_ROWS as int) == k,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, MASK_ROWS as int, k, j - k * (MASK_ROWS as int));
}

/// Row `i`'s codes are below 8 and its pair's bit is set in `m`.
pub open spec fn code_in(rc: Seq<u8>, lc: Seq<u8>, m: u64, i: int) -> bool {
    rc[i] < 8 && lc[i] < 8 && pair_bit(m, (rc[i] * 8 + lc[i]) as u64)
}

/// The pair masks of the `n` stored rows with codes `rc`, `lc`, or an empty part when some code is 8 or more.
fn scan_masks(rc: &[u8], lc: &[u8], n: usize) -> (mk: Vec<u64>)
    requires rc@.len() == n, lc@.len() == n,
    ensures mk@.len() > 0 ==> masks_ok(rc@, lc@, mk@),
{
    let mut out: Vec<u64> = Vec::new();
    let mut s: usize = 0;
    while s < n
        invariant
            rc@.len() == n, lc@.len() == n, s <= n,
            s < n ==> s == out@.len() * MASK_ROWS,
            s == n ==> n <= out@.len() * MASK_ROWS,
            forall|j: int| 0 <= j < s ==> #[trigger] row_marked(rc@, lc@, out@, j),
        decreases n - s,
    {
        let e: usize = if n - s < MASK_ROWS { n } else { s + MASK_ROWS };
        let ghost k = out@.len() as int;
        let mut m: u64 = 0;
        let mut j: usize = s;
        while j < e
            invariant
                rc@.len() == n, lc@.len() == n, s <= j <= e <= n,
                forall|i: int| s <= i < j ==> #[trigger] code_in(rc@, lc@, m, i),
            decreases e - j,
        {
            let r = rc[j];
            let l = lc[j];
            if r >= 8 || l >= 8 {
                return Vec::new();
            }
            let x: u64 = (r as u64) * 8 + (l as u64);
            let ghost m0 = m;
            m = m | (1u64 << x);
            proof {
                lemma_bit_or(m0, x, x);
                assert forall|i: int| s <= i < j + 1 implies #[trigger] code_in(rc@, lc@, m, i) by {
                    if i < j {
                        assert(code_in(rc@, lc@, m0, i));
                        lemma_bit_or(m0, x, (rc@[i] * 8 + lc@[i]) as u64);
                    }
                }
            }
            j = j + 1;
        }
        let ghost old_out = out@;
        out.push(m);
        proof {
            assert forall|i: int| 0 <= i < e implies #[trigger] row_marked(rc@, lc@, out@, i) by {
                if i < s {
                    assert(row_marked(rc@, lc@, old_out, i));
                    assert(i / (MASK_ROWS as int) < k) by {
                        lemma_chunk_of(s as int, k);
                        vstd::arithmetic::div_mod::lemma_div_is_ordered(i, s as int, MASK_ROWS as int);
                        if i / (MASK_ROWS as int) == k {
                            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, MASK_ROWS as int);
                            assert(false);
                        }
                    }
                    assert(out@[i / (MASK_ROWS as int)] == old_out[i / (MASK_ROWS as int)]);
                } else {
                    lemma_chunk_of(i, k);
                    assert(code_in(rc@, lc@, m, i));
                }
            }
        }
        s = e;
    }
    out
}

/// facts' `represents` gives the U8 kind of both code parts.
proof fn lemma_code_kinds(fp: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires F::represents(fp, rels),
    ensures
        fp.len() == F::FACTS_PARTS,
        fp[F::LI_RETURNFLAG_CODES as int] is U8,
        fp[F::LI_LINESTATUS_CODES as int] is U8,
{
    hide(F::orders_ok);
    let tp = li_tp(fp);
    assert(F::lineitem_ok(tp, rels[0]));
    assert(F::lineitem_cols_ok(tp, F::lineitem_rows(tp, rels[0])));
    assert(tp[F::LI_RETURNFLAG_CODES as int] == fp[F::LI_RETURNFLAG_CODES as int]);
    assert(tp[F::LI_LINESTATUS_CODES as int] == fp[F::LI_LINESTATUS_CODES as int]);
}

/// For a database bound to `facts`: this storage's relations are facts', which facts' parts represent.
proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        D::stored_relations(db) == FD::stored_relations(db),
        F::represents(sv.facts, D::stored_relations(db)),
{
    hide(F::represents);
    let rels = FD::stored_relations(db);
    assert(D::stored_relations(db) =~= rels);
    assert(F::represents(sv.facts, rels));
}

/// Build the pair-mask part (the inherited parts of `facts` come first, unchanged).
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= crate::gendb_entry::parallel::MAX_WORKERS,
    ensures
        match r {
            Ok(p) => forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
                ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
            Err(QueryError::WorkerFailed(_)) => true,
            Err(_) => false,
        },
{
    let ghost sv = stores@;
    let ghost fp = sv.facts;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof {
        lemma_src(sv, db0);
        lemma_code_kinds(fp, D::stored_relations(db0));
    }
    let n = stores.facts.part_len(F::LI_RETURNFLAG_CODES);
    let n2 = stores.facts.part_len(F::LI_LINESTATUS_CODES);
    let rc = stores.facts.extent_u8(F::LI_RETURNFLAG_CODES, 0, n);
    let lc = stores.facts.extent_u8(F::LI_LINESTATUS_CODES, 0, n2);
    proof {
        assert(rc@ =~= FC::u8s(fp[F::LI_RETURNFLAG_CODES as int]));
        assert(lc@ =~= FC::u8s(fp[F::LI_LINESTATUS_CODES as int]));
    }
    let mk = if n == n2 { scan_masks(rc, lc, n) } else { Vec::new() };
    let ghost mkv = mk@;
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::U64(mk));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 1);
        assert(built[0] == PartView::U64(mkv));
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            lemma_src(sv, db);
            let parts = storage_parts(sv, built);
            assert(parts.len() == LI_PAIRMASK_PARTS);
            assert(facts_parts(parts) =~= fp);
            assert(parts[PAIR_MASKS as int] == built[0]);
            assert(pair_masks(parts) == mkv);
            assert(rf_codes(parts) == rc@);
            assert(ls_codes(parts) == lc@);
        }
    }
    Ok(out)
}

} // verus!
