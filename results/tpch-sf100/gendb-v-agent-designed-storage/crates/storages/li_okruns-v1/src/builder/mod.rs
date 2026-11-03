//! Builder of storage `li_okruns`: one pass over facts' stored lineitem rows records the first row of every maximal
//! run of equal l_orderkey (`st`), then the row count. Invariant of the pass at row `s`: the runs `[st[k], st[k + 1])`
//! closed so far are correct (`run_ok`), the open run `[last, s)` has one key, and `prev` is the key of row `s - 1`.
//! Fallback (no rows, more than `u32::MAX - 1` rows, or column parts shorter than the row count): the one-entry
//! offsets `[0]` (no runs), which satisfies the same relation.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view, owned_part_view};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{sources_ready, sources_bound, storage_parts};
use crate::spec::value::Database;
use crate::stores::facts::interface as fi;
use crate::stores::li_okruns::interface as lr;
use fi::common::colfmt::{u32s, u64s, i64s};

verus! {

/// What the builder needs of facts' lineitem parts (from `represents` of any bound database).
pub open spec fn src_ok(f: Seq<PartView>) -> bool {
    &&& f.len() == fi::FACTS_PARTS
    &&& f[fi::LI_LAYOUT as int] is U64 && u64s(f[fi::LI_LAYOUT as int]).len() == 2
    &&& f[fi::LI_ORDERKEY_CODES as int] is U32 && f[fi::LI_ORDERKEY_BASE as int] is I64
}

/// A bound database gives `src_ok`.
proof fn lemma_src_ok(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.facts),
{
    let f = sv.facts;
    let rels = crate::stores::facts::declaration::stored_relations(db);
    assert(fi::represents(f, rels));
    let tp = f.subrange(fi::LINEITEM_FIRST as int, (fi::LINEITEM_FIRST + fi::LI_PARTS) as int);
    assert(fi::lineitem_ok(tp, rels[0]));
    assert(fi::LINEITEM_FIRST == 0);
    assert(tp[fi::LI_LAYOUT as int] == f[fi::LI_LAYOUT as int]);
    assert(tp[fi::LI_ORDERKEY_CODES as int] == f[fi::LI_ORDERKEY_CODES as int]);
    assert(tp[fi::LI_ORDERKEY_BASE as int] == f[fi::LI_ORDERKEY_BASE as int]);
    let rows = fi::lineitem_rows(tp, rels[0]);
    assert(fi::lineitem_cols_ok(tp, rows));
}

/// l_orderkey of stored row `s` of facts' parts `f`, as `okey_at` reads it.
pub open spec fn fkey(f: Seq<PartView>, s: int) -> int {
    lr::okey_at(f, s)
}

/// The key of stored row `s`.
fn key_exec(kc: &[u32], kb: &[i64], bs: usize, n: usize, s: usize, Ghost(f): Ghost<Seq<PartView>>) -> (k: i128)
    requires
        src_ok(f),
        kc@ == u32s(f[fi::LI_ORDERKEY_CODES as int]), kb@ == i64s(f[fi::LI_ORDERKEY_BASE as int]),
        bs as int == lr::li_bsize(f), bs >= 1,
        kc@.len() == n, n <= kb@.len() * bs,
        s < n,
    ensures
        k as int == fkey(f, s as int),
{
    proof {
        fi::common::read::lemma_div_lt(s as int, bs as int, kb@.len() as int);
    }
    kb[s / bs] as i128 + kc[s] as i128
}

/// Runs `[0, k)` of `st` over facts' parts `f` with `n` rows are correct (as `run_ok` states them).
pub open spec fn closed_ok(f: Seq<PartView>, st: Seq<u32>, n: int, k: int) -> bool {
    forall|x: int| 0 <= x < k ==> #[trigger] run_at(f, st, n, x)
}

/// Run `x` of `st`: nonempty inside `n` rows, one key, another key right after it.
pub open spec fn run_at(f: Seq<PartView>, st: Seq<u32>, n: int, x: int) -> bool {
    let a = st[x] as int;
    let b = st[x + 1] as int;
    &&& a < b <= n
    &&& forall|s: int| a <= s < b ==> #[trigger] fkey(f, s) == fkey(f, a)
    &&& b < n ==> fkey(f, b) != fkey(f, b - 1)
}

/// The run offsets over facts' parts `f` (`n` = their row count): at least one entry, the first 0, every run correct.
fn run_starts(stores: &mut Stores, Ghost(f): Ghost<Seq<PartView>>) -> (st: Vec<u32>)
    requires old(stores)@.facts == f, src_ok(f),
    ensures
        final(stores)@ == old(stores)@,
        st@.len() >= 1,
        st@[0] == 0,
        closed_ok(f, st@, lr::li_rows(f), st@.len() - 1),
{
    let lay = stores.facts.extent_u64(fi::LI_LAYOUT, 0, 2);
    let n64 = lay[0];
    let bs64 = lay[1];
    proof {
        assert(lay@ =~= u64s(f[fi::LI_LAYOUT as int]));
    }
    let mut st: Vec<u32> = Vec::new();
    st.push(0);
    if n64 == 0 || n64 >= 0xffff_ffff || bs64 == 0 || bs64 > 0xffff_ffff {
        return st;
    }
    let n = n64 as usize;
    let bs = bs64 as usize;
    let kc = stores.facts.extent_u32(fi::LI_ORDERKEY_CODES, 0, stores.facts.part_len(fi::LI_ORDERKEY_CODES));
    let kb = stores.facts.extent_i64(fi::LI_ORDERKEY_BASE, 0, stores.facts.part_len(fi::LI_ORDERKEY_BASE));
    proof {
        assert(kc@ =~= u32s(f[fi::LI_ORDERKEY_CODES as int]));
        assert(kb@ =~= i64s(f[fi::LI_ORDERKEY_BASE as int]));
    }
    let nb = kb.len() as u128;
    let bw = bs as u128;
    assert(nb * bw <= 0xffff_ffff_ffff_ffff * 0xffff_ffffu128) by (nonlinear_arith)
        requires nb <= 0xffff_ffff_ffff_ffff, bw <= 0xffff_ffff;
    if kc.len() != n || nb * bw < n as u128 {
        return st;
    }
    let mut prev = key_exec(kc, kb, bs, n, 0, Ghost(f));
    let mut last: usize = 0;
    let mut s: usize = 1;
    while s < n
        invariant
            src_ok(f), n as int == lr::li_rows(f), n < 0xffff_ffff,
            kc@ == u32s(f[fi::LI_ORDERKEY_CODES as int]), kb@ == i64s(f[fi::LI_ORDERKEY_BASE as int]),
            bs as int == lr::li_bsize(f), bs >= 1,
            kc@.len() == n, n <= kb@.len() * bs,
            1 <= s <= n,
            st@.len() >= 1, st@[0] == 0,
            last == st@[st@.len() - 1], last < s,
            closed_ok(f, st@, n as int, st@.len() - 1),
            forall|t: int| last <= t < s ==> #[trigger] fkey(f, t) == fkey(f, last as int),
            prev as int == fkey(f, s - 1),
        decreases n - s,
    {
        let k = key_exec(kc, kb, bs, n, s, Ghost(f));
        if k != prev {
            let ghost s0 = st@;
            st.push(s as u32);
            proof {
                let x = s0.len() - 1;
                assert(st@[x] == s0[x]);
                assert(st@[x + 1] == s as u32);
                assert(run_at(f, st@, n as int, x));
                assert forall|y: int| 0 <= y < st@.len() - 1 implies #[trigger] run_at(f, st@, n as int, y) by {
                    if y < x {
                        assert(run_at(f, s0, n as int, y));
                        assert(st@[y] == s0[y] && st@[y + 1] == s0[y + 1]);
                    }
                }
            }
            last = s;
        }
        prev = k;
        s = s + 1;
    }
    let ghost s0 = st@;
    st.push(n as u32);
    proof {
        let x = s0.len() - 1;
        assert(st@[x] == s0[x]);
        assert(st@[x + 1] == n as u32);
        assert(run_at(f, st@, n as int, x));
        assert forall|y: int| 0 <= y < st@.len() - 1 implies #[trigger] run_at(f, st@, n as int, y) by {
            if y < x {
                assert(run_at(f, s0, n as int, y));
                assert(st@[y] == s0[y] && st@[y + 1] == s0[y + 1]);
            }
        }
    }
    st
}

/// li_okruns' stored relations are facts' (the same declaration).
proof fn lemma_same_relations(db: Database)
    ensures crate::stores::li_okruns::declaration::stored_relations(db) == crate::stores::facts::declaration::stored_relations(db),
{
    assert(crate::stores::li_okruns::declaration::stored_cols_t0() =~= crate::stores::facts::declaration::stored_cols_t0());
    assert(crate::stores::li_okruns::declaration::stored_cols_t1() =~= crate::stores::facts::declaration::stored_cols_t1());
    assert(crate::stores::li_okruns::declaration::stored_relations(db) =~= crate::stores::facts::declaration::stored_relations(db));
}

/// The parts of facts followed by the run offsets satisfy `represents` for every bound database.
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db) ==>
            crate::gendb_entry::storage::represents(storage_parts(old(stores)@, owned_parts_view(p@)),
                crate::gendb_entry::storage::stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost sv = stores@;
    let ghost f = sv.facts;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof { lemma_src_ok(sv, db0); }
    let st = run_starts(stores, Ghost(f));
    let ghost stv = st@;
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U32(st));
    proof {
        let built = owned_parts_view(parts@);
        assert(built.len() == 1);
        assert(built[0] == owned_part_view(parts@[0]));
        let all = storage_parts(sv, built);
        assert(all == f + built);
        assert(all.len() == lr::LI_OKRUNS_PARTS);
        assert(all.subrange(0, lr::FACTS_PARTS as int) =~= f);
        assert(all[lr::RUN_STARTS as int] == built[0]);
        assert(lr::starts(all) == stv);
        assert(all[fi::LI_LAYOUT as int] == f[fi::LI_LAYOUT as int]);
        assert(all[fi::LI_ORDERKEY_CODES as int] == f[fi::LI_ORDERKEY_CODES as int]);
        assert(all[fi::LI_ORDERKEY_BASE as int] == f[fi::LI_ORDERKEY_BASE as int]);
        assert forall|s: int| #[trigger] lr::okey_at(all, s) == fkey(f, s) by {}
        assert(lr::li_rows(all) == lr::li_rows(f));
        assert forall|k: int| 0 <= k < lr::nruns(all) implies #[trigger] lr::run_ok(all, k) by {
            assert(run_at(f, stv, lr::li_rows(f), k));
        }
        assert(lr::runs_ok(all));
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies
            lr::represents(all, crate::stores::li_okruns::declaration::stored_relations(db)) by {
            lemma_same_relations(db);
        }
    }
    Ok(parts)
}

} // verus!
