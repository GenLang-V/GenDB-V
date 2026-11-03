//! Builder of storage `li_ordruns`: the 75 parts of `facts` are inherited unchanged; this builder adds the run lengths
//! of l_orderkey along the stored lineitem rows (part `RUN_LENS`).
//!
//! Plan: one scan over the stored lineitem rows, group by group (frame-of-reference: key = group base + row code),
//! extends the current run while the key repeats and closes it when the key changes (`scan_runs`). A run longer than
//! `MAX_RUN` rows makes the part empty (it then states nothing).
//!
//! Proof: `src::lemma_src` gives the stored keys (`key_at`) of facts' stored lineitem rows; the scan's invariant
//! (`runs_upto`) describes the closed runs over the keys; `lemma_runs_rows` turns it into `runs_ok` over the stored
//! rows; the inherited parts are facts' parts, so facts' `represents` carries over unchanged.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row, Val};
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::li_ordruns::interface::*;
use crate::stores::li_ordruns::declaration as D;

pub mod src;
use src::*;

verus! {

/// Row `i` of run `r` has the key of the run's first row.
pub open spec fn key_same(fp: Seq<PartView>, rl: Seq<u8>, r: int, i: int) -> bool {
    key_at(fp, run_start(rl, r) + i) == key_at(fp, run_start(rl, r))
}

/// Run `r` starts with another key than the row before it.
pub open spec fn key_split(fp: Seq<PartView>, rl: Seq<u8>, r: int) -> bool {
    key_at(fp, run_start(rl, r)) != key_at(fp, run_start(rl, r) - 1)
}

/// The closed runs `rl` cover the stored rows `[0, end)`: maximal runs of equal keys.
pub open spec fn runs_upto(fp: Seq<PartView>, rl: Seq<u8>, end: int) -> bool {
    &&& run_start(rl, rl.len() as int) == end
    &&& forall|r: int| 0 <= r < rl.len() ==> #[trigger] rl[r] >= 1
    &&& forall|r: int, i: int| 0 <= r < rl.len() && 0 <= i < rl[r] ==> #[trigger] key_same(fp, rl, r, i)
    &&& forall|r: int| 0 < r < rl.len() ==> #[trigger] key_split(fp, rl, r)
}

/// Row `j` of group `g` (rows `g * bs .. g * bs + bs`) has `j / bs == g`.
proof fn lemma_div_group(j: int, bs: int, g: int)
    requires bs >= 1, g * bs <= j < g * bs + bs,
    ensures j / bs == g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, bs, g, j - g * bs);
}

/// Closing the open run `[s, s + len)` (all keys equal, split from the closed runs) keeps `runs_upto`.
proof fn lemma_close_run(fp: Seq<PartView>, rl: Seq<u8>, s: int, len: u8)
    requires
        runs_upto(fp, rl, s),
        len >= 1,
        forall|i: int| s <= i < s + len ==> #[trigger] key_at(fp, i) == key_at(fp, s),
        rl.len() > 0 ==> key_at(fp, s) != key_at(fp, s - 1),
    ensures
        runs_upto(fp, rl.push(len), s + len),
{
    let m = rl.push(len);
    let n0 = rl.len() as int;
    assert(m.subrange(0, n0) =~= rl);
    assert forall|r: int| 0 <= r <= n0 implies #[trigger] run_start(m, r) == run_start(rl, r) by {
        lemma_run_start_prefix(m, rl, r);
    }
    assert(run_start(m, n0 + 1) == run_start(m, n0) + m[n0]);
    assert forall|r: int| 0 <= r < m.len() implies #[trigger] m[r] >= 1 by {
        if r < n0 {
            assert(m[r] == rl[r]);
        }
    }
    assert forall|r: int, i: int| 0 <= r < m.len() && 0 <= i < m[r] implies #[trigger] key_same(fp, m, r, i) by {
        if r < n0 {
            assert(m[r] == rl[r]);
            assert(key_same(fp, rl, r, i));
        } else {
            assert(key_at(fp, s + i) == key_at(fp, s));
        }
    }
    assert forall|r: int| 0 < r < m.len() implies #[trigger] key_split(fp, m, r) by {
        if r < n0 {
            assert(key_split(fp, rl, r));
        }
    }
}

/// The run lengths of the keys of the `n` stored rows (`kc`, `kb`: codes and group bases, `bs` rows per group), or
/// an empty part when some run is longer than `MAX_RUN`.
fn scan_runs(kc: &[u32], kb: &[i64], bs: usize, n: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (rl: Vec<u8>)
    requires
        bs >= 1,
        bs as int == bsize(fp),
        n as int == n_rows(fp),
        kc@ == FC::u32s(fp[F::LI_ORDERKEY_CODES as int]),
        kb@ == FC::i64s(fp[F::LI_ORDERKEY_BASE as int]),
        kc@.len() == n,
        kb@.len() * bs >= n,
        forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] key_at(fp, j) <= i64::MAX,
    ensures
        rl@.len() > 0 ==> runs_upto(fp, rl@, n as int),
{
    let mut rl: Vec<u8> = Vec::new();
    let mut prev: i64 = 0;
    let mut len: usize = 0;
    let mut s: usize = 0;
    let mut g: usize = 0;
    // Groups g = 0, 1, ...: rows [s, e) with s = g * bs.
    while s < n
        invariant
            bs >= 1,
            bs as int == bsize(fp),
            n as int == n_rows(fp),
            kc@ == FC::u32s(fp[F::LI_ORDERKEY_CODES as int]),
            kb@ == FC::i64s(fp[F::LI_ORDERKEY_BASE as int]),
            kc@.len() == n,
            kb@.len() * bs >= n,
            forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] key_at(fp, j) <= i64::MAX,
            s <= n,
            s < n ==> s == g * bs,
            s == 0 ==> len == 0 && rl@.len() == 0,
            s > 0 ==> 1 <= len <= MAX_RUN && prev as int == key_at(fp, s - 1),
            runs_upto(fp, rl@, s - len),
            forall|i: int| s - len <= i < s ==> #[trigger] key_at(fp, i) == key_at(fp, s - len),
            s > 0 && rl@.len() > 0 ==> key_at(fp, s - len) != key_at(fp, s - len - 1),
        decreases n - s,
    {
        let e: usize = if n - s < bs { n } else { s + bs };
        proof {
            assert(g * bs < kb@.len() * bs);
            assert(g < kb@.len()) by (nonlinear_arith) requires g * bs < kb@.len() * bs, bs >= 1;
        }
        let base = kb[g];
        let mut j = s;
        while j < e
            invariant
                bs >= 1,
                bs as int == bsize(fp),
                kc@ == FC::u32s(fp[F::LI_ORDERKEY_CODES as int]),
                kb@ == FC::i64s(fp[F::LI_ORDERKEY_BASE as int]),
                kc@.len() == n,
                forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] key_at(fp, j) <= i64::MAX,
                s == g * bs,
                s <= j <= e <= n,
                e <= s + bs,
                g < kb@.len(),
                base == kb@[g as int],
                j == 0 ==> len == 0 && rl@.len() == 0,
                j > 0 ==> 1 <= len <= MAX_RUN && prev as int == key_at(fp, j - 1),
                runs_upto(fp, rl@, j - len),
                forall|i: int| j - len <= i < j ==> #[trigger] key_at(fp, i) == key_at(fp, j - len),
                j > 0 && rl@.len() > 0 ==> key_at(fp, j - len) != key_at(fp, j - len - 1),
            decreases e - j,
        {
            proof {
                lemma_div_group(j as int, bs as int, g as int);
                assert(key_at(fp, j as int) == base + kc@[j as int]);
            }
            let k = base + kc[j] as i64;
            let ghost st = j - len;
            if j == 0 {
                prev = k;
                len = 1;
                proof {
                    assert(run_start(rl@, 0) == 0);
                }
            } else if k == prev {
                if len == MAX_RUN {
                    return Vec::new();
                }
                len = len + 1;
            } else {
                proof {
                    lemma_close_run(fp, rl@, st, len as u8);
                }
                rl.push(len as u8);
                prev = k;
                len = 1;
            }
            j = j + 1;
        }
        proof {
            if e < n {
                assert(e == (g + 1) * bs) by (nonlinear_arith) requires e == g * bs + bs;
            }
        }
        s = e;
        g = g + 1;
    }
    if len > 0 {
        proof {
            lemma_close_run(fp, rl@, s - len, len as u8);
        }
        rl.push(len as u8);
    }
    rl
}

/// Runs over the keys are runs over the stored rows' l_orderkey (column 0 holds `Val::Int(key_at)`).
proof fn lemma_runs_rows(fp: Seq<PartView>, rows: Seq<Row>, rl: Seq<u8>)
    requires
        rl.len() > 0 ==> runs_upto(fp, rl, rows.len() as int),
        forall|r: int| 0 <= r < rl.len() ==> #[trigger] rl[r] >= 1,
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][0] == Val::Int(key_at(fp, j)),
    ensures
        runs_ok(rows, rl),
{
    if rl.len() > 0 {
        let n = rows.len() as int;
        assert forall|r: int, i: int| 0 <= r < rl.len() && 0 <= i < rl[r] implies #[trigger] run_same(rows, rl, r, i) by {
            assert(key_same(fp, rl, r, i));
            lemma_run_start_mono(rl, 0, r);
            lemma_run_start_mono(rl, r + 1, rl.len() as int);
            lemma_run_start_next(rl, r);
            assert(run_start(rl, r) + i < n);
            assert(rows[run_start(rl, r) + i][0] == Val::Int(key_at(fp, run_start(rl, r) + i)));
            assert(rows[run_start(rl, r)][0] == Val::Int(key_at(fp, run_start(rl, r))));
        }
        assert forall|r: int| 0 < r < rl.len() implies #[trigger] run_split(rows, rl, r) by {
            assert(key_split(fp, rl, r));
            lemma_run_start_mono(rl, r, rl.len() as int);
            lemma_run_start_mono(rl, 0, r);
            assert(run_start(rl, r) < n);
            assert(run_start(rl, r) >= 1);
            assert(rows[run_start(rl, r)][0] == Val::Int(key_at(fp, run_start(rl, r))));
            assert(rows[run_start(rl, r) - 1][0] == Val::Int(key_at(fp, run_start(rl, r) - 1)));
        }
    }
}

/// The new storage's parts represent the stored relations of every database bound to the source.
proof fn lemma_built(sv: StoresView, db: Database, built: Seq<PartView>, rl: Seq<u8>)
    requires
        sources_bound(sv, db),
        built.len() == 1,
        built[0] == PartView::U8(rl),
        rl.len() > 0 ==> runs_upto(sv.facts, rl, n_rows(sv.facts)),
    ensures
        represents(storage_parts(sv, built), stored_relations(db)),
{
    let fp = sv.facts;
    let parts = storage_parts(sv, built);
    let rels = D::stored_relations(db);
    lemma_src(sv, db);
    assert(parts.len() == LI_ORDRUNS_PARTS);
    assert(facts_parts(parts) =~= fp);
    assert(parts[RUN_LENS as int] == built[0]);
    assert(run_lens(parts) == rl);
    let rows = stored_lines(parts, rels);
    assert(rows == src_rows(fp, rels));
    if rl.len() > 0 {
        assert(runs_upto(fp, rl, n_rows(fp)));
    }
    assert forall|r: int| 0 <= r < rl.len() implies #[trigger] rl[r] >= 1 by {
        assert(runs_upto(fp, rl, n_rows(fp)));
    }
    lemma_runs_rows(fp, rows, rl);
}

/// Build the run-length part (the inherited parts of `facts` come first, unchanged).
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
    }
    let lay = stores.facts.extent_u64(F::LI_LAYOUT, 0, 2);
    let n = stores.facts.part_len(F::LI_ORDERKEY_CODES);
    let nb = stores.facts.part_len(F::LI_ORDERKEY_BASE);
    let kc = stores.facts.extent_u32(F::LI_ORDERKEY_CODES, 0, n);
    let kb = stores.facts.extent_i64(F::LI_ORDERKEY_BASE, 0, nb);
    proof {
        assert(lay@ =~= FC::u64s(fp[F::LI_LAYOUT as int]));
        assert(kc@ =~= FC::u32s(fp[F::LI_ORDERKEY_CODES as int]));
        assert(kb@ =~= FC::i64s(fp[F::LI_ORDERKEY_BASE as int]));
    }
    let bs = lay[1] as usize;
    let rl = if lay[1] <= usize::MAX as u64 {
        scan_runs(kc, kb, bs, n, Ghost(fp))
    } else {
        Vec::new()
    };
    let ghost rlv = rl@;
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::U8(rl));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 1);
        assert(built[0] == PartView::U8(rlv));
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            lemma_src(sv, db);
            lemma_built(sv, db, built, rlv);
        }
    }
    Ok(out)
}

} // verus!
