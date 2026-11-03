//! Builder of storage `suppliers_rank` from storage `suppliers` (whose 48 parts it keeps unchanged in front): two
//! indexes, each computed by plain code and then checked at run time before it is stored, so only the checks carry
//! proof obligations.
//!
//! - `build_sbal`: the supplier rows sorted by s_acctbal descending (merge sort of `(max - balance) << 32 | row`
//!   keys), checked to be a bijection of the rows (`perm::check_perm`) in descending balance order; else empty.
//! - `build_psdir`: a counting sort of the partsupp rows by ps_suppkey into a dense directory over
//!   `kmin .. kmax` (when there are at most `rows + 1` keys), checked to be a bijection whose entry `e` holds only rows
//!   of key `kmin + e`, with offsets from 0 to the row count, nondecreasing; else mode 0 (no directory).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row, Val};
use crate::link::source::rows_in_columns;
use crate::stores::suppliers::interface as S;
use crate::stores::suppliers::declaration as SD;
use crate::stores::suppliers::interface::common::colfmt as CF;
use crate::stores::suppliers_rank::interface as I;
use crate::stores::suppliers_rank::declaration as D;

pub mod perm;
pub mod sort64;
pub mod src;

use perm::{check_perm, perm_view_ok, covered_u32};
use sort64::msort64;
use src::*;

verus! {

/// A checked bijection is a permutation in the interface's sense.
proof fn lemma_perm(v: Seq<u32>, n: int)
    requires perm_view_ok(v, n),
    ensures I::perm_ok(v, n),
{
    assert forall|r: int| 0 <= r < n implies #[trigger] I::listed(v, r) by {
        assert(covered_u32(v, r));
    }
}

// ------------------------------------------------------------------------------------------------ SBAL

/// The supplier rows in descending s_acctbal order (`c`, `b`, `bs`: the s_acctbal column of the `n` rows of `s`), or
/// empty when they cannot be ordered this way (more than `u32::MAX` rows, or a balance range over 32 bits).
fn build_sbal(c: &[u32], b: &[i64], bs: usize, n: usize, Ghost(s): Ghost<Seq<Row>>) -> (sb: Vec<u32>)
    requires col_ok(c@, b@, bs as int, n as int), acct_rows(s, c@, b@, bs as int), s.len() == n,
    ensures I::sbal_ok(sb@, s),
{
    if n == 0 || n > 0xffff_ffff {
        return Vec::new();
    }
    assert(0int / (bs as int) < b@.len());
    assert(i64::MIN <= for_val(c@, b@, bs as int, 0) <= i64::MAX);
    // The largest balance.
    let mut amax: i64 = b[0 / bs] + c[0] as i64;
    let mut j: usize = 1;
    while j < n
        invariant col_ok(c@, b@, bs as int, n as int), 1 <= j <= n,
        decreases n - j,
    {
        assert((j as int) / (bs as int) < b@.len());
        assert(i64::MIN <= for_val(c@, b@, bs as int, j as int) <= i64::MAX);
        let v: i64 = b[j / bs] + c[j] as i64;
        if v > amax {
            amax = v;
        }
        j = j + 1;
    }
    // Sort keys: (amax - balance) in the high 32 bits (ascending = balance descending), the row in the low ones.
    let mut keys: Vec<u64> = Vec::with_capacity(n);
    j = 0;
    while j < n
        invariant col_ok(c@, b@, bs as int, n as int), j <= n, keys@.len() == j, n <= 0xffff_ffff,
        decreases n - j,
    {
        assert((j as int) / (bs as int) < b@.len());
        assert(i64::MIN <= for_val(c@, b@, bs as int, j as int) <= i64::MAX);
        let v: i64 = b[j / bs] + c[j] as i64;
        let d: i128 = amax as i128 - v as i128;
        if d < 0 || d > 0xffff_ffff {
            return Vec::new();
        }
        keys.push(((d as u64) << 32u64) | (j as u64));
        j = j + 1;
    }
    let mut tmp: Vec<u64> = vec![0u64; n];
    msort64(&mut keys, &mut tmp, 0, n, Ghost(|x: u64| true));
    let mut sb: Vec<u32> = Vec::with_capacity(n);
    j = 0;
    while j < n
        invariant j <= n, keys@.len() == n, sb@.len() == j,
        decreases n - j,
    {
        sb.push((keys[j] & 0xffff_ffffu64) as u32);
        j = j + 1;
    }
    if !check_perm(&sb) {
        return Vec::new();
    }
    // Check the descending order.
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            col_ok(c@, b@, bs as int, n as int), acct_rows(s, c@, b@, bs as int), s.len() == n,
            perm_view_ok(sb@, n as int), i < n,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] I::desc_at(sb@, s, i2),
        decreases n - i,
    {
        let r1 = sb[i] as usize;
        let r2 = sb[i + 1] as usize;
        assert((r1 as int) / (bs as int) < b@.len());
        assert((r2 as int) / (bs as int) < b@.len());
        assert(i64::MIN <= for_val(c@, b@, bs as int, r1 as int) <= i64::MAX);
        assert(i64::MIN <= for_val(c@, b@, bs as int, r2 as int) <= i64::MAX);
        let v1: i64 = b[r1 / bs] + c[r1] as i64;
        let v2: i64 = b[r2 / bs] + c[r2] as i64;
        if v1 < v2 {
            return Vec::new();
        }
        proof {
            assert(s[r1 as int][5] == (Val::Num { coeff: for_val(c@, b@, bs as int, r1 as int), scale: 2 }));
            assert(s[r2 as int][5] == (Val::Num { coeff: for_val(c@, b@, bs as int, r2 as int), scale: 2 }));
            assert(I::desc_at(sb@, s, i as int));
        }
        i = i + 1;
    }
    proof { lemma_perm(sb@, n as int); }
    sb
}

// ------------------------------------------------------------------------------------------------ ps_suppkey directory

/// The "no directory" result (mode 0).
fn no_dir() -> (r: (Vec<i64>, Vec<u32>, Vec<u32>))
    ensures r.0@.len() == 2, r.0@[0] == 0,
{
    let mut meta: Vec<i64> = Vec::new();
    meta.push(0);
    meta.push(0);
    (meta, Vec::new(), Vec::new())
}

/// Entry of row `k`'s key in a directory starting at `kmin` with `nk` entries, if inside.
#[inline]
fn entry_of(c: &[u32], b: &[i64], bs: usize, n: usize, k: usize, kmin: i64, nk: usize) -> (e: Option<usize>)
    requires col_ok(c@, b@, bs as int, n as int), k < n,
    ensures e matches Some(x) ==> x < nk && for_val(c@, b@, bs as int, k as int) == kmin + x,
{
    assert((k as int) / (bs as int) < b@.len());
    assert(i64::MIN <= for_val(c@, b@, bs as int, k as int) <= i64::MAX);
    let v: i64 = b[k / bs] + c[k] as i64;
    let d: i128 = v as i128 - kmin as i128;
    if d >= 0 && d < nk as i128 { Some(d as usize) } else { None }
}

/// The ps_suppkey directory of the `n` partsupp rows `ps` (`c`, `b`, `bs`: their ps_suppkey column): `[mode, kmin]`,
/// offsets and permutation.
fn build_psdir(c: &[u32], b: &[i64], bs: usize, n: usize, Ghost(ps): Ghost<Seq<Row>>) -> (r: (Vec<i64>, Vec<u32>, Vec<u32>))
    requires col_ok(c@, b@, bs as int, n as int), suppkey_rows(ps, c@, b@, bs as int), ps.len() == n,
    ensures I::psdir_ok(r.0@, r.1@, r.2@, ps),
{
    if n == 0 || n >= 0x7fff_0000 {
        return no_dir();
    }
    assert(0int / (bs as int) < b@.len());
    assert(i64::MIN <= for_val(c@, b@, bs as int, 0) <= i64::MAX);
    // The key range.
    let mut kmin: i64 = b[0 / bs] + c[0] as i64;
    let mut kmax: i64 = kmin;
    let mut k: usize = 1;
    while k < n
        invariant col_ok(c@, b@, bs as int, n as int), 1 <= k <= n, kmin <= kmax,
        decreases n - k,
    {
        assert((k as int) / (bs as int) < b@.len());
        assert(i64::MIN <= for_val(c@, b@, bs as int, k as int) <= i64::MAX);
        let v: i64 = b[k / bs] + c[k] as i64;
        if v < kmin {
            kmin = v;
        }
        if v > kmax {
            kmax = v;
        }
        k = k + 1;
    }
    let span: i128 = kmax as i128 - kmin as i128 + 1;
    if span > n as i128 + 1 {
        return no_dir();
    }
    let nk = span as usize;
    assert(nk <= n + 1);
    // Counting sort: offs[e + 1] counts key kmin + e, then prefix sums.
    let mut offs: Vec<u32> = vec![0u32; nk + 1];
    k = 0;
    while k < n
        invariant col_ok(c@, b@, bs as int, n as int), k <= n, offs@.len() == nk + 1,
        decreases n - k,
    {
        match entry_of(c, b, bs, n, k, kmin, nk) {
            Some(e) => {
                let x = offs[e + 1];
                if x == 0xffff_ffffu32 {
                    return no_dir();
                }
                offs.set(e + 1, x + 1);
            },
            None => {
                return no_dir();
            },
        }
        k = k + 1;
    }
    let mut e: usize = 1;
    while e <= nk
        invariant offs@.len() == nk + 1, 1 <= e <= nk + 1, nk <= n + 1, n < 0x7fff_0000,
        decreases nk + 1 - e,
    {
        let s: u64 = offs[e - 1] as u64 + offs[e] as u64;
        if s > 0xffff_ffffu64 {
            return no_dir();
        }
        offs.set(e, s as u32);
        e = e + 1;
    }
    // Scatter the rows (ascending within each key).
    let mut pos: Vec<u32> = Vec::with_capacity(nk);
    e = 0;
    while e < nk
        invariant offs@.len() == nk + 1, e <= nk, pos@.len() == e,
        decreases nk - e,
    {
        pos.push(offs[e]);
        e = e + 1;
    }
    let mut perm: Vec<u32> = vec![0u32; n];
    k = 0;
    while k < n
        invariant col_ok(c@, b@, bs as int, n as int), k <= n, pos@.len() == nk, perm@.len() == n, n < 0xffff_ffff,
        decreases n - k,
    {
        match entry_of(c, b, bs, n, k, kmin, nk) {
            Some(e) => {
                let p = pos[e];
                if p as usize >= n {
                    return no_dir();
                }
                perm.set(p as usize, k as u32);
                pos.set(e, p + 1);
            },
            None => {
                return no_dir();
            },
        }
        k = k + 1;
    }
    // Checks: bijection, offsets from 0 to n and nondecreasing, every position's key.
    if !check_perm(&perm) {
        return no_dir();
    }
    if offs[0] != 0 || offs[nk] as usize != n {
        return no_dir();
    }
    e = 0;
    while e < nk
        invariant
            offs@.len() == nk + 1, e <= nk,
            forall|e2: int| 0 <= e2 < e ==> #[trigger] I::offs_le(offs@, e2),
        decreases nk - e,
    {
        if offs[e] > offs[e + 1] {
            return no_dir();
        }
        e = e + 1;
    }
    e = 0;
    while e < nk
        invariant
            col_ok(c@, b@, bs as int, n as int), suppkey_rows(ps, c@, b@, bs as int), ps.len() == n,
            offs@.len() == nk + 1, e <= nk, perm@.len() == n,
            offs@[nk as int] == n,
            forall|e2: int| 0 <= e2 < nk ==> #[trigger] I::offs_le(offs@, e2),
            forall|e2: int, p: int| 0 <= e2 < e && #[trigger] I::in_entry(offs@, e2, p)
                ==> perm@[p] < n && ps[perm@[p] as int][1] == Val::Int(kmin + e2),
        decreases nk - e,
    {
        proof {
            lemma_offs_upto(offs@, e as int + 1, nk as int);
            assert(I::offs_le(offs@, e as int));
        }
        let hi = offs[e + 1] as usize;
        let mut p = offs[e] as usize;
        while p < hi
            invariant
                col_ok(c@, b@, bs as int, n as int), suppkey_rows(ps, c@, b@, bs as int), ps.len() == n,
                offs@.len() == nk + 1, e < nk, perm@.len() == n,
                hi == offs@[e + 1], hi <= n, offs@[e as int] <= p <= hi,
                forall|p2: int| offs@[e as int] <= p2 < p ==> perm@[p2] < n && ps[perm@[p2] as int][1] == Val::Int(kmin + e),
            decreases hi - p,
        {
            let r = perm[p] as usize;
            if r >= n {
                return no_dir();
            }
            match entry_of(c, b, bs, n, r, kmin, nk) {
                Some(x) => {
                    if x != e {
                        return no_dir();
                    }
                    assert(ps[r as int][1] == Val::Int(for_val(c@, b@, bs as int, r as int)));
                },
                None => {
                    return no_dir();
                },
            }
            p = p + 1;
        }
        proof {
            assert forall|e2: int, p2: int| 0 <= e2 < e + 1 && #[trigger] I::in_entry(offs@, e2, p2)
                implies perm@[p2] < n && ps[perm@[p2] as int][1] == Val::Int(kmin + e2) by {
                if e2 < e {
                } else {
                    assert(offs@[e as int] <= p2 < hi);
                }
            }
        }
        e = e + 1;
    }
    let mut meta: Vec<i64> = Vec::new();
    meta.push(I::MODE_DIRECTORY);
    meta.push(kmin);
    proof {
        lemma_perm(perm@, n as int);
        assert forall|e2: int, p: int| 0 <= e2 < offs@.len() - 1 && #[trigger] I::in_entry(offs@, e2, p)
            implies ps[perm@[p] as int][1] == Val::Int(meta@[1] + e2) by {
        }
    }
    (meta, offs, perm)
}

/// `offs[e] <= offs[nk]` for `e <= nk` when adjacent offsets are ordered.
proof fn lemma_offs_upto(offs: Seq<u32>, e: int, nk: int)
    requires 0 <= e <= nk < offs.len(), forall|e2: int| 0 <= e2 < nk ==> #[trigger] I::offs_le(offs, e2),
    ensures offs[e] <= offs[nk],
    decreases nk - e,
{
    if e < nk {
        lemma_offs_upto(offs, e + 1, nk);
        assert(I::offs_le(offs, e));
    }
}

// ------------------------------------------------------------------------------------------------ build

/// For a database bound to `suppliers`: the stored relations are suppliers', which it represents.
proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        D::stored_relations(db) == SD::stored_relations(db),
        S::represents(sv.suppliers, D::stored_relations(db)),
        rows_in_columns(D::stored_relations(db)[0], SD::stored_columns_t0()),
        rows_in_columns(D::stored_relations(db)[1], SD::stored_columns_t1()),
{
    assert(D::stored_relations(db) =~= SD::stored_relations(db));
    SD::lemma_stored_relations(db);
}

/// Build the four index parts after the inherited suppliers parts.
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
    let ghost rels = D::stored_relations(db0);
    let ghost ps = rels[0];
    let ghost s = rels[1];
    let ghost p = sv.suppliers;
    proof {
        lemma_src(sv, db0);
        lemma_acct_src(p, s);
        lemma_suppkey_src(p, ps);
        // Every database bound to the source has the same relations (the parts determine them).
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies D::stored_relations(db) == rels by {
            lemma_src(sv, db);
            S::lemma_represents_determines(p, D::stored_relations(db), rels);
        }
    }
    // SBAL.
    let ns = stores.suppliers.part_len(SU_ACCT_CODES);
    let sb: Vec<u32> = if ns >= 1 {
        let (ac, ab, abs) = open_col(&mut stores.suppliers, SU_LAYOUT, SU_ACCT_CODES, SU_ACCT_BASE, ns);
        proof {
            let b0 = CF::u64s(p[SU_LAYOUT as int])[1] as int;
            assert forall|j: int| 0 <= j < s.len() implies #[trigger] s[j][5] == (Val::Num { coeff: for_val(ac@, ab@, abs as int, j), scale: 2 }) by {
                assert(s[j][5] == (Val::Num { coeff: for_val(ac@, ab@, b0, j), scale: 2 }));
            }
        }
        build_sbal(ac, ab, abs, ns, Ghost(s))
    } else {
        Vec::new()
    };
    // The ps_suppkey directory.
    let nps = stores.suppliers.part_len(PS_SUPP_CODES);
    let (meta, offs, perm) = if nps >= 1 {
        let (kc, kb, kbs) = open_col(&mut stores.suppliers, PS_LAYOUT, PS_SUPP_CODES, PS_SUPP_BASE, nps);
        proof {
            let b0 = CF::u64s(p[PS_LAYOUT as int])[1] as int;
            assert forall|k: int| 0 <= k < ps.len() implies #[trigger] ps[k][1] == Val::Int(for_val(kc@, kb@, kbs as int, k)) by {
                assert(ps[k][1] == Val::Int(for_val(kc@, kb@, b0, k)));
            }
        }
        build_psdir(kc, kb, kbs, nps, Ghost(ps))
    } else {
        no_dir()
    };
    let ghost (sbv, mv, ov, pv) = (sb@, meta@, offs@, perm@);
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::U32(sb));
    out.push(OwnedPart::I64(meta));
    out.push(OwnedPart::U32(offs));
    out.push(OwnedPart::U32(perm));
    proof {
        let built = owned_parts_view(out@);
        assert(built[0] == PartView::U32(sbv));
        assert(built[1] == PartView::I64(mv));
        assert(built[2] == PartView::U32(ov));
        assert(built[3] == PartView::U32(pv));
        if nps == 0 {
            assert(I::psdir_ok(mv, ov, pv, ps));
        }
        if ns == 0 {
            assert(I::sbal_ok(sbv, s));
        }
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            lemma_src(sv, db);
            let parts = storage_parts(sv, built);
            assert(parts =~= p + built);
            assert(parts.subrange(0, I::SUPPLIERS_PARTS as int) =~= p);
            assert(parts[I::SBAL as int] == PartView::U32(sbv));
            assert(parts[I::PSMETA as int] == PartView::I64(mv));
            assert(parts[I::PSOFFS as int] == PartView::U32(ov));
            assert(parts[I::PSPERM as int] == PartView::U32(pv));
            assert(D::stored_relations(db) == rels);
        }
    }
    Ok(out)
}

} // verus!
