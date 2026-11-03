//! Builder of storage `psrun`: one pass over suppliers' partsupp ps_partkey (U32 FOR codes + I64 group bases, uniform
//! groups of `bt` rows; the key of row `i` is `base[i / bt] + code[i]`, `src_key`). The ratio `r` is the length of the
//! first key's run (at least 1). Every block of `RUN_ROWS` rows whose first key `k` fits `i64` (and is not `NO_RUN`) and
//! whose every row `i` has key `k + (i - start) / r` gets the entry `k`; every other block gets `NO_RUN`. suppliers'
//! `represents` gives the row values of the key column (`lemma_src_key`).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view, owned_part_view};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{sources_ready, sources_bound, storage_parts};
use crate::spec::value::{Database, Row, Val};
use crate::stores::suppliers::interface as si;
use crate::stores::psrun::interface as pr;
use si::common::colfmt::{u32s, u64s, i64s, groups_part_ok, nblocks_of, int_col_at, for_at, base_at, code_at,
    lemma_uniform_groups, gs_at};

verus! {

/// suppliers' partsupp layout part (`[rows, block rows]`).
pub const PS_LAYOUT: usize = 0;
/// suppliers' partsupp group starts.
pub const PS_GROUPS: usize = 1;
/// suppliers' ps_partkey U32 codes.
pub const PS_KEY_CODES: usize = 2;
/// suppliers' ps_partkey I64 group bases.
pub const PS_KEY_BASE: usize = 3;

/// Partsupp rows (suppliers' parts `f`).
pub open spec fn src_rows(f: Seq<PartView>) -> int {
    u64s(f[PS_LAYOUT as int])[0] as int
}

/// Rows per group of suppliers' partsupp.
pub open spec fn src_bt(f: Seq<PartView>) -> int {
    u64s(f[PS_LAYOUT as int])[1] as int
}

/// The key of partsupp row `i`: its group's base plus its code.
pub open spec fn src_key(f: Seq<PartView>, i: int) -> int {
    i64s(f[PS_KEY_BASE as int])[i / src_bt(f)] + u32s(f[PS_KEY_CODES as int])[i]
}

/// What the builder needs of suppliers' parts `f`: the layout, uniform groups, and the key column's shape.
pub open spec fn src_ok(f: Seq<PartView>) -> bool {
    &&& f.len() == si::SUPPLIERS_PARTS
    &&& f[PS_LAYOUT as int] is U64 && u64s(f[PS_LAYOUT as int]).len() == 2
    &&& groups_part_ok(f[PS_GROUPS as int], src_rows(f), src_bt(f))
    &&& f[PS_KEY_CODES as int] is U32 && u32s(f[PS_KEY_CODES as int]).len() == src_rows(f)
    &&& f[PS_KEY_BASE as int] is I64 && i64s(f[PS_KEY_BASE as int]).len() == nblocks_of(src_rows(f), src_bt(f))
}

/// The partsupp rows of a bound database: as many as the layout says, each with key `src_key`.
pub open spec fn rows_keyed(f: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& rel.len() == src_rows(f)
    &&& forall|i: int| 0 <= i < rel.len() ==> #[trigger] rel[i][0] == Val::Int(src_key(f, i))
}

/// A bound database gives `src_ok` and the key of every partsupp row.
proof fn lemma_src_key(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        src_ok(sv.suppliers),
        rows_keyed(sv.suppliers, crate::stores::suppliers::declaration::stored_relations(db)[0]),
{
    let f = sv.suppliers;
    let rels = crate::stores::suppliers::declaration::stored_relations(db);
    assert(si::represents(f, rels));
    let tp = f.subrange(si::PARTSUPP_FIRST as int, (si::PARTSUPP_FIRST + si::PS_PARTS) as int);
    let rel = rels[0];
    assert(si::partsupp_ok(tp, rel));
    assert(tp[0] == f[PS_LAYOUT as int]);
    assert(tp[1] == f[PS_GROUPS as int]);
    assert(tp[2] == f[PS_KEY_CODES as int]);
    assert(tp[3] == f[PS_KEY_BASE as int]);
    assert(si::table_layout_ok(tp, rel.len() as int));
    assert(int_col_at(tp, 1, 2, 3, rel, 0));
    let n = rel.len() as int;
    let bt = src_bt(f);
    lemma_uniform_groups(f[PS_GROUPS as int], n, bt);
    assert forall|i: int| 0 <= i < n implies #[trigger] rel[i][0] == Val::Int(src_key(f, i)) by {
        si::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], i);
        assert(rel[i][0] == Val::Int(for_at(gs_at(tp, 1), tp[3], tp[2], i)));
    }
}

/// The key of row `i`, computed (in `i128`, so no overflow).
fn key_at(codes: &[u32], bases: &[i64], bt: usize, i: usize, Ghost(f): Ghost<Seq<PartView>>) -> (k: i128)
    requires
        src_ok(f), codes@ == u32s(f[PS_KEY_CODES as int]), bases@ == i64s(f[PS_KEY_BASE as int]),
        bt as int == src_bt(f), (i as int) < src_rows(f),
    ensures k == src_key(f, i as int),
{
    let ghost n = src_rows(f);
    proof {
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(i as int, bt as int);
        si::common::colfmt::lemma_nblocks(n, bt as int);
        si::common::read::lemma_div_lt(i as int, bt as int, nblocks_of(n, bt as int));
    }
    bases[i / bt] as i128 + codes[i] as i128
}

/// The length of the first key's run (at least 1).
fn first_run(codes: &[u32], bases: &[i64], bt: usize, n: usize, Ghost(f): Ghost<Seq<PartView>>) -> (r: usize)
    requires
        src_ok(f), codes@ == u32s(f[PS_KEY_CODES as int]), bases@ == i64s(f[PS_KEY_BASE as int]),
        bt as int == src_bt(f), n as int == src_rows(f),
    ensures r >= 1, n > 0 ==> r <= n,
{
    if n == 0 {
        return 1;
    }
    let k0 = key_at(codes, bases, bt, 0, Ghost(f));
    let mut r: usize = 1;
    while r < n && key_at(codes, bases, bt, r, Ghost(f)) == k0
        invariant
            src_ok(f), codes@ == u32s(f[PS_KEY_CODES as int]), bases@ == i64s(f[PS_KEY_BASE as int]),
            bt as int == src_bt(f), n as int == src_rows(f),
            1 <= r <= n,
        decreases n - r,
    {
        r = r + 1;
    }
    r
}

/// The entry of the block `[s, e)`: its first key when every row `i` has key `first + (i - s) / r` and the key fits
/// `i64` (and is not `NO_RUN`), else `NO_RUN`.
fn block_entry(codes: &[u32], bases: &[i64], bt: usize, s: usize, e: usize, r: usize, Ghost(f): Ghost<Seq<PartView>>)
    -> (k: i64)
    requires
        src_ok(f), codes@ == u32s(f[PS_KEY_CODES as int]), bases@ == i64s(f[PS_KEY_BASE as int]),
        bt as int == src_bt(f), s < e, e as int <= src_rows(f), r >= 1,
    ensures
        k != pr::NO_RUN ==> forall|i: int| s <= i < e ==> #[trigger] src_key(f, i) == k + (i - s) / (r as int),
{
    let k0 = key_at(codes, bases, bt, s, Ghost(f));
    if k0 <= i64::MIN as i128 || k0 > i64::MAX as i128 {
        return pr::NO_RUN;
    }
    let mut i = s;
    while i < e
        invariant
            src_ok(f), codes@ == u32s(f[PS_KEY_CODES as int]), bases@ == i64s(f[PS_KEY_BASE as int]),
            bt as int == src_bt(f), s <= i <= e, e as int <= src_rows(f), r >= 1,
            k0 == src_key(f, s as int),
            forall|i2: int| s <= i2 < i ==> #[trigger] src_key(f, i2) == k0 + (i2 - s) / (r as int),
        decreases e - i,
    {
        let want: i128 = k0 + ((i - s) / r) as i128;
        if key_at(codes, bases, bt, i, Ghost(f)) != want {
            return pr::NO_RUN;
        }
        i = i + 1;
    }
    k0 as i64
}

/// The runs part: the ratio, then the entry of every block of `RUN_ROWS` rows.
fn runs(stores: &mut Stores, Ghost(f): Ghost<Seq<PartView>>) -> (v: Vec<i64>)
    requires old(stores)@.suppliers == f, src_ok(f),
    ensures
        final(stores)@ == old(stores)@,
        v@.len() == pr::run_blocks(src_rows(f)) + 1,
        v@[0] >= 1,
        forall|b: int| 0 <= b < pr::run_blocks(src_rows(f)) && #[trigger] v@[b + 1] != pr::NO_RUN ==>
            forall|i: int| b * pr::RUN_ROWS <= i < src_rows(f) && i < b * pr::RUN_ROWS + pr::RUN_ROWS
                ==> #[trigger] src_key(f, i) == v@[b + 1] + (i - b * pr::RUN_ROWS) / (v@[0] as int),
{
    let lay = stores.suppliers.extent_u64(PS_LAYOUT, 0, 2);
    proof {
        assert(lay@ =~= u64s(f[PS_LAYOUT as int]));
    }
    let n = stores.suppliers.part_len(PS_KEY_CODES);
    let nb = stores.suppliers.part_len(PS_KEY_BASE);
    let rb = pr::RUN_ROWS;
    let nrb = run_blocks_exec(n);
    if lay[1] > n as u64 || n as u64 >= 0x4000_0000_0000_0000u64 {
        // Groups larger than the table (never written by suppliers' builder): no run entries.
        return no_runs(nrb, Ghost(src_rows(f)));
    }
    let bt = lay[1] as usize;
    let codes = stores.suppliers.extent_u32(PS_KEY_CODES, 0, n);
    let bases = stores.suppliers.extent_i64(PS_KEY_BASE, 0, nb);
    proof {
        assert(codes@ =~= u32s(f[PS_KEY_CODES as int]));
        assert(bases@ =~= i64s(f[PS_KEY_BASE as int]));
    }
    let r = first_run(codes, bases, bt, n, Ghost(f));
    let ghost ri = r as int;
    let mut v: Vec<i64> = Vec::new();
    v.push(r as i64);
    let mut b: usize = 0;
    while b < nrb
        invariant
            src_ok(f), codes@ == u32s(f[PS_KEY_CODES as int]), bases@ == i64s(f[PS_KEY_BASE as int]),
            bt as int == src_bt(f), n as int == src_rows(f), rb == pr::RUN_ROWS,
            nrb as int == pr::run_blocks(n as int),
            r >= 1, ri == r, r < 0x8000_0000_0000_0000,
            stores@ == old(stores)@,
            b <= nrb, v@.len() == b + 1, v@[0] == r as i64,
            forall|b2: int| 0 <= b2 < b && #[trigger] v@[b2 + 1] != pr::NO_RUN ==>
                forall|i: int| b2 * pr::RUN_ROWS <= i < n && i < b2 * pr::RUN_ROWS + pr::RUN_ROWS
                    ==> #[trigger] src_key(f, i) == v@[b2 + 1] + (i - b2 * pr::RUN_ROWS) / ri,
        decreases nrb - b,
    {
        proof {
            let (bi, ni) = (b as int, n as int);
            assert(bi * 65536 < ni) by (nonlinear_arith)
                requires bi < (ni + 65535) / 65536, bi >= 0, ni >= 0;
        }
        let s = b * rb;
        let e = if n - s > rb { s + rb } else { n };
        let k = block_entry(codes, bases, bt, s, e, r, Ghost(f));
        let ghost v0 = v@;
        v.push(k);
        proof {
            assert forall|b2: int| 0 <= b2 < b + 1 && #[trigger] v@[b2 + 1] != pr::NO_RUN implies
                forall|i: int| b2 * pr::RUN_ROWS <= i < n && i < b2 * pr::RUN_ROWS + pr::RUN_ROWS
                    ==> #[trigger] src_key(f, i) == v@[b2 + 1] + (i - b2 * pr::RUN_ROWS) / ri by {
                if b2 < b {
                    assert(v@[b2 + 1] == v0[b2 + 1]);
                } else {
                    assert(v@[b2 + 1] == k);
                }
            }
        }
        b = b + 1;
    }
    proof {
        assert(r as i64 as int == r as int);
    }
    v
}

/// The number of blocks of `RUN_ROWS` rows over `n` rows.
fn run_blocks_exec(n: usize) -> (nrb: usize)
    ensures nrb as int == pr::run_blocks(n as int),
{
    let q = n / pr::RUN_ROWS;
    let m = n % pr::RUN_ROWS;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 65536);
        if m == 0 {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(n + 65535, 65536, q as int, 65535);
        } else {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(n + 65535, 65536, q + 1, m - 1);
        }
    }
    if m == 0 { q } else { q + 1 }
}

/// `nrb` blocks without a run (ratio 1).
fn no_runs(nrb: usize, Ghost(n): Ghost<int>) -> (v: Vec<i64>)
    requires nrb as int == pr::run_blocks(n),
    ensures
        v@.len() == pr::run_blocks(n) + 1,
        v@[0] == 1,
        forall|b: int| 0 <= b < pr::run_blocks(n) ==> #[trigger] v@[b + 1] == pr::NO_RUN,
{
    let mut v: Vec<i64> = Vec::new();
    v.push(1);
    let mut b: usize = 0;
    while b < nrb
        invariant b <= nrb, v@.len() == b + 1, v@[0] == 1, forall|b2: int| 0 <= b2 < b ==> #[trigger] v@[b2 + 1] == pr::NO_RUN,
        decreases nrb - b,
    {
        v.push(pr::NO_RUN);
        b = b + 1;
    }
    v
}

/// psrun's stored relations are suppliers' (the same declaration).
proof fn lemma_same_relations(db: Database)
    ensures crate::stores::psrun::declaration::stored_relations(db) == crate::stores::suppliers::declaration::stored_relations(db),
{
    assert(crate::stores::psrun::declaration::stored_cols_t0() =~= crate::stores::suppliers::declaration::stored_cols_t0());
    assert(crate::stores::psrun::declaration::stored_cols_t1() =~= crate::stores::suppliers::declaration::stored_cols_t1());
    assert(crate::stores::psrun::declaration::stored_cols_t2() =~= crate::stores::suppliers::declaration::stored_cols_t2());
    assert(crate::stores::psrun::declaration::stored_cols_t3() =~= crate::stores::suppliers::declaration::stored_cols_t3());
    assert(crate::stores::psrun::declaration::stored_relations(db) =~= crate::stores::suppliers::declaration::stored_relations(db));
}

/// The parts of suppliers followed by the runs satisfy `represents` for every bound database.
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
    let ghost f = sv.suppliers;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof { lemma_src_key(sv, db0); }
    let v = runs(stores, Ghost(f));
    let ghost rv = v@;
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::I64(v));
    proof {
        let built = owned_parts_view(parts@);
        assert(built.len() == 1);
        assert(built[0] == owned_part_view(parts@[0]));
        let all = storage_parts(sv, built);
        assert(all == f + built);
        assert(all.len() == pr::PSRUN_PARTS);
        assert(all.subrange(0, pr::SUPPLIERS_PARTS as int) =~= f);
        assert(all[pr::RUNS as int] == built[0]);
        assert(i64s(all[pr::RUNS as int]) == rv);
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies
            pr::represents(all, crate::stores::psrun::declaration::stored_relations(db)) by {
            lemma_same_relations(db);
            lemma_src_key(sv, db);
            let rel = crate::stores::suppliers::declaration::stored_relations(db)[0];
            assert(rows_keyed(f, rel));
            let p = all[pr::RUNS as int];
            assert forall|b: int| 0 <= b < pr::run_blocks(rel.len() as int) && #[trigger] i64s(p)[b + 1] != pr::NO_RUN
                implies pr::block_run(rel, b, i64s(p)[b + 1] as int, i64s(p)[0] as int) by {
                assert forall|i: int| b * pr::RUN_ROWS <= i < rel.len() && i < b * pr::RUN_ROWS + pr::RUN_ROWS
                    implies #[trigger] rel[i][0] == Val::Int(i64s(p)[b + 1] as int + (i - b * pr::RUN_ROWS) / (i64s(p)[0] as int)) by {
                    assert(src_key(f, i) == rv[b + 1] + (i - b * pr::RUN_ROWS) / (rv[0] as int));
                }
            }
            assert(pr::runs_ok(p, rel));
        }
    }
    Ok(parts)
}

} // verus!
