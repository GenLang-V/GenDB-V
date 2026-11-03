//! Builder of storage `suppliers_psrun` (storage `suppliers`, extended by the run layout of partsupp's ps_partkey)
//! from storage `suppliers`: `first` is the ps_partkey of row 0 and `ratio` the length of its run; one pass over
//! the ps_partkey codes (`check_runs`) confirms that row `k` has ps_partkey `first + k / ratio`. The new part is
//! `[ratio, first]`, or `[0, 0]` when the check fails (or partsupp is empty).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row, Val};
use crate::spec::int::{int_in_range, IntKind};
use crate::link::source::rows_in_columns;
use crate::stores::suppliers::interface as S;
use crate::stores::suppliers::declaration as SD;
use crate::stores::suppliers::interface::common::colfmt as CF;
use crate::stores::suppliers::interface::common::read as CR;
use crate::stores::suppliers_psrun::interface as I;
use crate::stores::suppliers_psrun::declaration as D;

verus! {

/// Part indices of the partsupp columns of `suppliers` the builder reads.
pub const P_LAYOUT: usize = 0;
pub const P_GROUPS: usize = 1;
pub const P_KEY_CODES: usize = 2;
pub const P_KEY_BASE: usize = 3;

/// ps_partkey of stored row `k`: the frame-of-reference value `base[k / bsize] + code[k]`.
pub open spec fn key_at(kc: Seq<u32>, kb: Seq<i64>, bsize: int, k: int) -> int {
    kb[k / bsize] + kc[k]
}

/// The source facts the builder uses, over the parts `p` of `suppliers` and the partsupp relation `ps`.
pub open spec fn src_ok(p: Seq<PartView>, ps: Seq<Row>, bsize: int) -> bool {
    let n = ps.len() as int;
    let (kc, kb) = (CF::u32s(p[P_KEY_CODES as int]), CF::i64s(p[P_KEY_BASE as int]));
    &&& p.len() == S::SUPPLIERS_PARTS
    &&& bsize >= 1
    &&& p[P_KEY_CODES as int] is U32 && p[P_KEY_BASE as int] is I64
    &&& kc.len() == n
    &&& forall|k: int| 0 <= k < n ==> #[trigger] (k / bsize) < kb.len()
    &&& forall|k: int| 0 <= k < n ==> {
            &&& i64::MIN <= #[trigger] key_at(kc, kb, bsize, k) <= i64::MAX
            &&& ps[k][0] == Val::Int(key_at(kc, kb, bsize, k))
        }
}

/// The group size the builder uses: the stored one, or `n` when the stored one exceeds `n` (every row in group 0
/// either way).
pub open spec fn eff_bsize(p: Seq<PartView>, n: int) -> int {
    let b0 = CF::u64s(p[P_LAYOUT as int])[1] as int;
    if b0 <= n { b0 } else { n }
}

/// The per-row facts of partsupp's ps_partkey column at the stored group size.
proof fn lemma_src_rows(p: Seq<PartView>, ps: Seq<Row>)
    requires
        p.len() == S::SUPPLIERS_PARTS,
        S::partsupp_ok(p.subrange(S::PARTSUPP_FIRST as int, (S::PARTSUPP_FIRST + S::PS_PARTS) as int), ps),
        rows_in_columns(ps, SD::stored_columns_t0()),
    ensures
        p[P_LAYOUT as int] is U64 && CF::u64s(p[P_LAYOUT as int]).len() == 2,
        src_ok(p, ps, CF::u64s(p[P_LAYOUT as int])[1] as int),
{
    let tp = p.subrange(S::PARTSUPP_FIRST as int, (S::PARTSUPP_FIRST + S::PS_PARTS) as int);
    assert(tp[S::PS_LAYOUT as int] == p[P_LAYOUT as int]);
    assert(tp[S::PS_GROUPS as int] == p[P_GROUPS as int]);
    assert(tp[S::PS_PARTKEY_CODES as int] == p[P_KEY_CODES as int]);
    assert(tp[S::PS_PARTKEY_BASE as int] == p[P_KEY_BASE as int]);
    let n = ps.len() as int;
    let bsize = CF::u64s(p[P_LAYOUT as int])[1] as int;
    let gp = p[P_GROUPS as int];
    let (kcp, kbp) = (p[P_KEY_CODES as int], p[P_KEY_BASE as int]);
    let (kc, kb) = (CF::u32s(kcp), CF::i64s(kbp));
    assert(S::table_layout_ok(tp, n));
    assert(CF::groups_part_ok(gp, n, bsize));
    CF::lemma_uniform_groups(gp, n, bsize);
    CF::lemma_nblocks(n, bsize);
    assert(CF::int_col(ps, 0, CF::u64s(gp), kbp, kcp));
    assert forall|k: int| 0 <= k < n implies #[trigger] (k / bsize) < kb.len() by {
        assert(k / bsize < CF::nblocks_of(n, bsize)) by {
            assert(k / bsize <= (n - 1) / bsize) by (nonlinear_arith) requires 0 <= k <= n - 1, bsize >= 1;
            assert(((n - 1) / bsize) * bsize <= n - 1) by (nonlinear_arith) requires n >= 1, bsize >= 1;
            assert((n - 1) / bsize < (n + bsize - 1) / bsize) by (nonlinear_arith) requires n >= 1, bsize >= 1;
        }
    }
    assert forall|k: int| 0 <= k < n implies {
        &&& i64::MIN <= #[trigger] key_at(kc, kb, bsize, k) <= i64::MAX
        &&& ps[k][0] == Val::Int(key_at(kc, kb, bsize, k))
    } by {
        CR::lemma_for_row(gp, n, bsize, kbp, kcp, k);
        assert(ps[k][0] == Val::Int(CF::for_at(CF::u64s(gp), kbp, kcp, k)));
        assert(ps[k].len() == SD::stored_columns_t0().len());
        assert(crate::spec::typing::value_in_column(ps[k][0], SD::stored_columns_t0()[0]));
        assert(int_in_range(IntKind::Int8, key_at(kc, kb, bsize, k)));
    }
}

/// The facts at the effective group size (`eff_bsize`): every row keeps its group.
proof fn lemma_src_eff(p: Seq<PartView>, ps: Seq<Row>)
    requires
        p[P_LAYOUT as int] is U64 && CF::u64s(p[P_LAYOUT as int]).len() == 2,
        src_ok(p, ps, CF::u64s(p[P_LAYOUT as int])[1] as int),
        ps.len() >= 1,
    ensures src_ok(p, ps, eff_bsize(p, ps.len() as int)),
{
    let n = ps.len() as int;
    let b0 = CF::u64s(p[P_LAYOUT as int])[1] as int;
    let b = eff_bsize(p, n);
    let (kc, kb) = (CF::u32s(p[P_KEY_CODES as int]), CF::i64s(p[P_KEY_BASE as int]));
    assert forall|k: int| 0 <= k < n implies #[trigger] (k / b) == k / b0 by {
        if b0 > n {
            assert(k / b == 0) by (nonlinear_arith) requires 0 <= k < b;
            assert(k / b0 == 0) by (nonlinear_arith) requires 0 <= k < b0;
        }
    }
    assert forall|k: int| 0 <= k < n implies #[trigger] (k / b) < kb.len() by {
        assert(k / b == k / b0);
    }
    assert forall|k: int| 0 <= k < n implies {
        &&& i64::MIN <= #[trigger] key_at(kc, kb, b, k) <= i64::MAX
        &&& ps[k][0] == Val::Int(key_at(kc, kb, b, k))
    } by {
        assert(k / b == k / b0);
        assert(key_at(kc, kb, b, k) == key_at(kc, kb, b0, k));
    }
}

/// For a database bound to `suppliers`: the stored relations are suppliers', which it represents.
proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        D::stored_relations(db) == SD::stored_relations(db),
        S::represents(sv.suppliers, D::stored_relations(db)),
        rows_in_columns(D::stored_relations(db)[0], SD::stored_columns_t0()),
{
    assert(D::stored_relations(db) =~= SD::stored_relations(db));
    SD::lemma_stored_relations(db);
}

/// Every row `k < n` has ps_partkey `first + k / ratio`, or the answer is false.
fn check_runs(kc: &[u32], kb: &[i64], bsize: usize, n: usize, first: i64, ratio: usize, Ghost(ps): Ghost<Seq<Row>>) -> (ok: bool)
    requires
        bsize >= 1, ratio >= 1,
        ps.len() == n,
        kc@.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] (k / bsize as int) < kb@.len(),
        forall|k: int| 0 <= k < n ==> {
            &&& i64::MIN <= #[trigger] key_at(kc@, kb@, bsize as int, k) <= i64::MAX
            &&& ps[k][0] == Val::Int(key_at(kc@, kb@, bsize as int, k))
        },
    ensures ok ==> forall|k: int| 0 <= k < n ==> #[trigger] ps[k][0] == Val::Int(first + k / (ratio as int)),
{
    let mut k: usize = 0;
    while k < n
        invariant
            bsize >= 1, ratio >= 1,
            ps.len() == n,
            kc@.len() == n,
            forall|q: int| 0 <= q < n ==> #[trigger] (q / bsize as int) < kb@.len(),
            forall|q: int| 0 <= q < n ==> {
                &&& i64::MIN <= #[trigger] key_at(kc@, kb@, bsize as int, q) <= i64::MAX
                &&& ps[q][0] == Val::Int(key_at(kc@, kb@, bsize as int, q))
            },
            k <= n,
            forall|q: int| 0 <= q < k ==> #[trigger] ps[q][0] == Val::Int(first + q / (ratio as int)),
        decreases n - k,
    {
        assert((k as int) / (bsize as int) < kb@.len());
        assert(i64::MIN <= key_at(kc@, kb@, bsize as int, k as int) <= i64::MAX);
        let key: i64 = kb[k / bsize] + kc[k] as i64;
        if key as i128 != first as i128 + (k / ratio) as i128 {
            return false;
        }
        k = k + 1;
    }
    true
}

/// Build the run layout part `[ratio, first]` after the inherited suppliers parts.
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
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    let ghost ps = D::stored_relations(db0)[0];
    let ghost p = sv.suppliers;
    proof {
        lemma_src(sv, db0);
        lemma_src_rows(p, ps);
        // Every database bound to the source has the same relations (the parts determine them).
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies D::stored_relations(db) == D::stored_relations(db0) by {
            lemma_src(sv, db);
            S::lemma_represents_determines(p, D::stored_relations(db), D::stored_relations(db0));
        }
    }
    let n = stores.suppliers.part_len(P_KEY_CODES);
    let mut ratio: i64 = 0;
    let mut first: i64 = 0;
    if n > 0 && n < 4294967295usize {
        let lay = stores.suppliers.extent_u64(P_LAYOUT, 0, 2);
        let b64 = lay[1];
        let bsize: usize = if b64 <= n as u64 { b64 as usize } else { n };
        let nb = stores.suppliers.part_len(P_KEY_BASE);
        let kc = stores.suppliers.extent_u32(P_KEY_CODES, 0, n);
        let kb = stores.suppliers.extent_i64(P_KEY_BASE, 0, nb);
        proof {
            assert(lay@ =~= CF::u64s(p[P_LAYOUT as int]));
            assert(kc@ =~= CF::u32s(p[P_KEY_CODES as int]));
            assert(kb@ =~= CF::i64s(p[P_KEY_BASE as int]));
            lemma_src_eff(p, ps);
            assert(bsize as int == eff_bsize(p, n as int));
        }
        assert(i64::MIN <= key_at(kc@, kb@, bsize as int, 0) <= i64::MAX);
        let f: i64 = kb[0 / bsize] + kc[0] as i64;
        // The length of the first key's run.
        let mut run: usize = 1;
        while run < n && kb[run / bsize] as i128 + kc[run] as i128 == f as i128
            invariant
                1 <= run <= n, bsize >= 1, kc@.len() == n,
                forall|k: int| 0 <= k < n ==> #[trigger] (k / bsize as int) < kb@.len(),
            decreases n - run,
        {
            assert((run as int) / (bsize as int) < kb@.len());
            run = run + 1;
        }
        if check_runs(kc, kb, bsize, n, f, run, Ghost(ps)) {
            ratio = run as i64;
            first = f;
        }
    }
    let mut meta: Vec<i64> = Vec::new();
    meta.push(ratio);
    meta.push(first);
    let ghost mv = meta@;
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::I64(meta));
    proof {
        let built = owned_parts_view(out@);
        assert(built[0] == PartView::I64(mv));
        assert(I::run_ok(mv, ps));
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            lemma_src(sv, db);
            let parts = storage_parts(sv, built);
            assert(parts =~= p + built);
            assert(parts.subrange(0, I::SUPPLIERS_PARTS as int) =~= p);
            assert(parts[I::RUN as int] == PartView::I64(mv));
            assert(D::stored_relations(db)[0] == ps);
        }
    }
    Ok(out)
}

} // verus!
