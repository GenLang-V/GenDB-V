//! Builder side of key indexes (`interface::common::keyidx`): the run-time sortedness check of a key column, and
//! the lemmas that give `keyidx_ok` for kind 1 (stored rows sorted by key) and kind 2 (an index of stored rows in
//! key order: the inverse of a clustered table's row map, when its canonical rows are sorted by key).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::builder::iface::common::colfmt::*;
use crate::builder::iface::common::keyidx::*;
use crate::builder::common::perm::*;
use crate::builder::common::colsrc::*;
use crate::builder::common::forenc::*;
use crate::builder::common::codes::Code;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::builder::common::cluster::{invert_perm, counting_perm};

verus! {

/// `true` exactly when `c` is nondecreasing.
pub fn check_nondecreasing(c: &[i64]) -> (b: bool)
    ensures b ==> forall|i: int| 0 <= i < c@.len() - 1 ==> #[trigger] c@[i] <= c@[i + 1],
{
    let n = c.len();
    if n == 0 {
        return true;
    }
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            n == c@.len(),
            n >= 1,
            i + 1 <= n,
            forall|q: int| 0 <= q < i ==> #[trigger] c@[q] <= c@[q + 1],
        decreases n - i,
    {
        if c[i] > c[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}

/// Kind 1: stored rows (canonical order) sorted by the key column `col`, whose FOR parts decode to `col`.
pub proof fn lemma_keyidx_sorted(kc: Seq<u32>, kb: Seq<i64>, bsize: int, n: int, col: Seq<i64>)
    requires
        bsize >= 1,
        n >= 0,
        kc.len() == n,
        kb.len() * bsize >= n,
        col.len() == n,
        forall|j: int| 0 <= j < n ==> #[trigger] fkey(kc, kb, bsize, j) == col[j] as int,
        forall|i: int| 0 <= i < col.len() - 1 ==> #[trigger] col[i] <= col[i + 1],
    ensures
        keyidx_ok(kc, kb, Seq::empty(), Seq::empty(), bsize, 1, n),
{
    assert forall|r: int| 0 <= r < n - 1 implies #[trigger] sorted_at(kc, kb, Seq::empty(), Seq::empty(), bsize, 1, r) by {
        assert(fkey(kc, kb, bsize, r) == col[r] as int);
        assert(fkey(kc, kb, bsize, r + 1) == col[r + 1] as int);
    }
}

/// Kind 2: the index column decodes to `inv`, a bijection with `rmap[inv[r]] == r`, and the canonical keys `col`
/// are sorted; the key of stored row `j` is the canonical key of `rmap[j]`.
pub proof fn lemma_keyidx_perm(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bsize: int, n: int,
    col: Seq<i64>, rmap: Seq<u64>, inv: Seq<u64>)
    requires
        bsize >= 1,
        n >= 0,
        kc.len() == n,
        kb.len() * bsize >= n,
        ic.len() == n,
        ib.len() * bsize >= n,
        col.len() == n,
        rmap.len() == n,
        inv.len() == n,
        is_perm(map_view(inv), n),
        forall|r: int| 0 <= r < n ==> #[trigger] fidx(ic, ib, bsize, r) == inv[r] as int,
        forall|r: int| 0 <= r < n ==> inv[r] < n && #[trigger] rmap[inv[r] as int] == r,
        forall|j: int| 0 <= j < n ==> rmap[j] < n && #[trigger] fkey(kc, kb, bsize, j) == col[rmap[j] as int] as int,
        forall|i: int| 0 <= i < col.len() - 1 ==> #[trigger] col[i] <= col[i + 1],
    ensures
        keyidx_ok(kc, kb, ic, ib, bsize, 2, n),
{
    assert(idx_map(ic, ib, bsize, n) =~= map_view(inv));
    assert forall|r: int| 0 <= r < n - 1 implies #[trigger] sorted_at(kc, kb, ic, ib, bsize, 2, r) by {
        assert(fidx(ic, ib, bsize, r) == inv[r] as int);
        assert(fidx(ic, ib, bsize, r + 1) == inv[r + 1] as int);
        assert(rmap[inv[r] as int] == r);
        assert(rmap[inv[r + 1] as int] == r + 1);
        assert(fkey(kc, kb, bsize, inv[r] as int) == col[r] as int);
        assert(fkey(kc, kb, bsize, inv[r + 1] as int) == col[r + 1] as int);
    }
}

/// Kind 0 (no order known) holds for any well-shaped key column.
pub proof fn lemma_keyidx_none(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bsize: int, n: int)
    requires
        bsize >= 1,
        n >= 0,
        kc.len() == n,
        kb.len() * bsize >= n,
    ensures
        keyidx_ok(kc, kb, ic, ib, bsize, 0, n),
{
}

/// Every row of an encoded column decodes (base of its block plus its code) to its source value.
pub proof fn lemma_for_col_rows<C: Code>(c: ForCol<C>, src: ValSrc, rm: RowMap, n: int, bsize: int)
    requires
        for_col_ok(c, src, rm, n, bsize),
        bsize >= 1,
        n >= 0,
    ensures
        c.codes@.len() == n,
        c.bases@.len() * bsize >= n,
        forall|r: int| 0 <= r < n ==> #[trigger] c.bases@[r / bsize] + C::val(c.codes@[r]) == src_val(src, rm_at(rm, r)),
{
    lemma_nblocks(n, bsize);
    assert(nblocks_of(n, bsize) == nblocks(n, bsize));
    assert forall|r: int| 0 <= r < n implies #[trigger] c.bases@[r / bsize] + C::val(c.codes@[r]) == src_val(src, rm_at(rm, r)) by {
        let g = r / bsize;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r, bsize);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(r, bsize);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(r, bsize);
        assert(bsize * g == g * bsize) by (nonlinear_arith);
        assert((g + 1) * bsize == g * bsize + bsize) by (nonlinear_arith);
        crate::builder::iface::common::read::lemma_div_lt(r, bsize, nblocks(n, bsize));
        assert(block_ok(src, rm, n, bsize, g, c.bases@[g], c.zmax@[g], c.codes@, 0));
        assert(blk_lo(bsize, g) <= r < blk_hi(n, bsize, g));
        assert(c.bases@[g] + C::val(c.codes@[r - 0]) == src_val(src, rm_at(rm, r)));
    }
}

/// The key of every stored row of an encoded U32 key column (with its bases as `kb`) is its source value.
pub proof fn lemma_fkey_col(c: ForCol<u32>, src: ValSrc, rm: RowMap, kb: Seq<i64>, n: int, bsize: int)
    requires
        for_col_ok(c, src, rm, n, bsize),
        bsize >= 1,
        n >= 0,
        kb.len() == c.bases@.len(),
        forall|g: int| 0 <= g < kb.len() ==> #[trigger] kb[g] as int == c.bases@[g] as int,
    ensures
        c.codes@.len() == n,
        kb.len() * bsize >= n,
        forall|j: int| 0 <= j < n ==> #[trigger] fkey(c.codes@, kb, bsize, j) == src_val(src, rm_at(rm, j)),
{
    lemma_for_col_rows(c, src, rm, n, bsize);
    assert forall|j: int| 0 <= j < n implies #[trigger] fkey(c.codes@, kb, bsize, j) == src_val(src, rm_at(rm, j)) by {
        assert(c.bases@[j / bsize] + u32::val(c.codes@[j]) == src_val(src, rm_at(rm, j)));
        crate::builder::iface::common::read::lemma_div_lt(j, bsize, kb.len() as int);
    }
}

/// Kind 1 when the key column `col` (in stored order) is sorted, else kind 0.
pub fn build_keyidx_sorted(col: &[i64], n: usize, bsize: usize, kc: Ghost<Seq<u32>>, kb: Ghost<Seq<i64>>) -> (kind: u64)
    requires
        col@.len() == n,
        bsize >= 1,
        kc@.len() == n,
        kb@.len() * bsize >= n,
        forall|j: int| 0 <= j < n ==> #[trigger] fkey(kc@, kb@, bsize as int, j) == col@[j] as int,
    ensures
        keyidx_ok(kc@, kb@, Seq::empty(), Seq::empty(), bsize as int, kind, n as int),
{
    if check_nondecreasing(col) {
        proof {
            lemma_keyidx_sorted(kc@, kb@, bsize as int, n as int, col@);
        }
        1
    } else {
        proof {
            lemma_keyidx_none(kc@, kb@, Seq::empty(), Seq::empty(), bsize as int, n as int);
        }
        0
    }
}

/// Kind 2 for a clustered table (stored row `j` is canonical row `rmv[j]`) whose canonical key column `col` is
/// sorted: the index lists the stored rows in canonical order (the inverse map, FOR coded over the table's groups).
/// Otherwise kind 0 with empty index parts.
pub fn build_keyidx_perm(col: &[i64], rmv: &Arc<Vec<u64>>, n: usize, bsize: usize, kc: Ghost<Seq<u32>>, kb: Ghost<Seq<i64>>,
    workers: usize, dispatch: &mut Dispatch) -> (r: Result<(Vec<u32>, Vec<u64>, u64), QueryError>)
    requires
        col@.len() == n,
        rmv@.len() == n,
        is_perm(map_view(rmv@), n as int),
        bsize >= 1,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
        kc@.len() == n,
        kb@.len() * bsize >= n,
        forall|j: int| 0 <= j < n ==> #[trigger] fkey(kc@, kb@, bsize as int, j) == col@[rmv@[j] as int] as int,
    ensures
        r matches Ok((ic, ib, kind)) ==> keyidx_ok(kc@, kb@, ic@, ib@, bsize as int, kind, n as int),
        r matches Ok((ic, ib, kind)) ==> (kind == 2 ==> forall|p: int| 0 <= p < n ==>
            #[trigger] rmv@[fidx(ic@, ib@, bsize as int, p)] as int == p),
        r matches Err(e) ==> e is WorkerFailed,
{
    let inv = invert_perm(rmv);
    let ghost inv_view = inv@;
    if check_perm(&inv) && check_nondecreasing(col) {
        let inv_arc = Arc::new(inv);
        proof {
            crate::builder::common::assemble::lemma_map_rm(inv_arc, n as int);
        }
        match encode_column::<u32>(&ValSrc::Pos, &RowMap::Map(inv_arc.clone()), n, bsize, false, workers, dispatch) {
            Ok(Some(c)) => {
                proof {
                    crate::builder::common::assemble::lemma_col_ranges(c, ValSrc::Pos, RowMap::Map(inv_arc), n as int, bsize as int);
                }
                let ib = crate::builder::common::assemble::bases_u64(&c.bases);
                proof {
                    lemma_for_col_rows(c, ValSrc::Pos, RowMap::Map(inv_arc), n as int, bsize as int);
                    assert forall|r: int| 0 <= r < n implies #[trigger] fidx(c.codes@, ib@, bsize as int, r) == inv_view[r] as int by {
                        assert(c.bases@[r / (bsize as int)] + u32::val(c.codes@[r]) == src_val(ValSrc::Pos, rm_at(RowMap::Map(inv_arc), r)));
                        crate::builder::iface::common::read::lemma_div_lt(r, bsize as int, ib@.len() as int);
                    }
                    assert forall|j: int| 0 <= j < n implies #[trigger] rmv@[j] < n by {
                        assert(0 <= map_view(rmv@)[j] < n);
                    }
                    lemma_keyidx_perm(kc@, kb@, c.codes@, ib@, bsize as int, n as int, col@, rmv@, inv_view);
                    assert forall|p: int| 0 <= p < n implies #[trigger] rmv@[fidx(c.codes@, ib@, bsize as int, p)] as int == p by {
                        assert(fidx(c.codes@, ib@, bsize as int, p) == inv_view[p] as int);
                    }
                }
                return Ok((c.codes, ib, 2));
            },
            Ok(None) => {},
            Err(e) => return Err(QueryError::WorkerFailed(e)),
        }
    }
    proof {
        lemma_keyidx_none(kc@, kb@, Seq::empty(), Seq::empty(), bsize as int, n as int);
    }
    Ok((Vec::new(), Vec::new(), 0))
}

/// Kind 2 by sorting: for a table stored in the order `rmv` (stored row -> canonical row) with canonical key column
/// `col`, the index lists the stored rows stably sorted by key (a counting sort over the key range, checked to be a
/// bijection and sorted at run time); kind 0 with empty index parts when a check fails or the range is too wide.
pub fn build_keyidx_sortperm(col: &[i64], rmv: &Arc<Vec<u64>>, n: usize, bsize: usize, kc: Ghost<Seq<u32>>,
    kb: Ghost<Seq<i64>>, workers: usize, dispatch: &mut Dispatch) -> (r: Result<(Vec<u32>, Vec<u64>, u64), QueryError>)
    requires
        col@.len() == n,
        rmv@.len() == n,
        is_perm(map_view(rmv@), n as int),
        bsize >= 1,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
        kc@.len() == n,
        kb@.len() * bsize >= n,
        forall|j: int| 0 <= j < n ==> #[trigger] fkey(kc@, kb@, bsize as int, j) == col@[rmv@[j] as int] as int,
    ensures
        r matches Ok((ic, ib, kind)) ==> keyidx_ok(kc@, kb@, ic@, ib@, bsize as int, kind, n as int),
        r matches Err(e) ==> e is WorkerFailed,
{
    proof {
        assert forall|j: int| 0 <= j < n implies #[trigger] rmv@[j] < n by {
            assert(0 <= map_view(rmv@)[j] < n);
        }
    }
    if n == 0 {
        proof {
            lemma_keyidx_none(kc@, kb@, Seq::empty(), Seq::empty(), bsize as int, n as int);
        }
        return Ok((Vec::new(), Vec::new(), 0));
    }
    // Key range.
    let mut kmin: i64 = col[0];
    let mut kmax: i64 = col[0];
    let mut i: usize = 1;
    while i < n
        invariant
            n == col@.len(),
            1 <= i <= n,
            kmin <= kmax,
            forall|q: int| 0 <= q < i ==> kmin <= #[trigger] col@[q] <= kmax,
        decreases n - i,
    {
        if col[i] < kmin {
            kmin = col[i];
        }
        if col[i] > kmax {
            kmax = col[i];
        }
        i = i + 1;
    }
    if kmax as i128 - kmin as i128 >= 2147483648i128 {
        proof {
            lemma_keyidx_none(kc@, kb@, Seq::empty(), Seq::empty(), bsize as int, n as int);
        }
        return Ok((Vec::new(), Vec::new(), 0));
    }
    // Sort keys of the stored rows.
    let mut keys: Vec<u32> = Vec::with_capacity(n);
    let mut j: usize = 0;
    while j < n
        invariant
            n == col@.len(),
            n == rmv@.len(),
            forall|q: int| 0 <= q < n ==> #[trigger] rmv@[q] < n,
            forall|q: int| 0 <= q < n ==> kmin <= #[trigger] col@[q] <= kmax,
            kmax - kmin < 2147483648,
            j <= n,
            keys@.len() == j,
        decreases n - j,
    {
        let c = rmv[j] as usize;
        keys.push((col[c] - kmin) as u32);
        j = j + 1;
    }
    let nkeys = (kmax - kmin + 1) as usize;
    let p = counting_perm(&keys, nkeys);
    // Check the order: the canonical key of the stored row at each position never decreases.
    let mut sorted = true;
    let mut r: usize = 0;
    while r + 1 < n
        invariant
            n == col@.len(),
            n == rmv@.len(),
            p@.len() == n,
            is_perm(map_view(p@), n as int),
            forall|q: int| 0 <= q < n ==> #[trigger] rmv@[q] < n,
            r + 1 <= n,
            sorted ==> forall|q: int| 0 <= q < r ==> #[trigger] col@[rmv@[p@[q] as int] as int] <= col@[rmv@[p@[q + 1] as int] as int],
        decreases n - r,
    {
        proof {
            assert(0 <= map_view(p@)[r as int] < n);
            assert(0 <= map_view(p@)[r + 1] < n);
        }
        let a = col[rmv[p[r] as usize] as usize];
        let b = col[rmv[p[r + 1] as usize] as usize];
        if a > b {
            sorted = false;
        }
        r = r + 1;
    }
    if !sorted {
        proof {
            lemma_keyidx_none(kc@, kb@, Seq::empty(), Seq::empty(), bsize as int, n as int);
        }
        return Ok((Vec::new(), Vec::new(), 0));
    }
    let ghost pv = p@;
    let p_arc = Arc::new(p);
    proof {
        crate::builder::common::assemble::lemma_map_rm(p_arc, n as int);
    }
    match encode_column::<u32>(&ValSrc::Pos, &RowMap::Map(p_arc.clone()), n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => {
            proof {
                crate::builder::common::assemble::lemma_col_ranges(c, ValSrc::Pos, RowMap::Map(p_arc), n as int, bsize as int);
            }
            let ib = crate::builder::common::assemble::bases_u64(&c.bases);
            proof {
                lemma_for_col_rows(c, ValSrc::Pos, RowMap::Map(p_arc), n as int, bsize as int);
                assert forall|q: int| 0 <= q < n implies #[trigger] fidx(c.codes@, ib@, bsize as int, q) == pv[q] as int by {
                    assert(c.bases@[q / (bsize as int)] + u32::val(c.codes@[q]) == src_val(ValSrc::Pos, rm_at(RowMap::Map(p_arc), q)));
                    crate::builder::iface::common::read::lemma_div_lt(q, bsize as int, ib@.len() as int);
                }
                assert(idx_map(c.codes@, ib@, bsize as int, n as int) =~= map_view(pv));
                assert forall|q: int| 0 <= q < n - 1 implies #[trigger] sorted_at(kc@, kb@, c.codes@, ib@, bsize as int, 2, q) by {
                    assert(0 <= map_view(pv)[q] < n);
                    assert(0 <= map_view(pv)[q + 1] < n);
                    assert(fkey(kc@, kb@, bsize as int, pv[q] as int) == col@[rmv@[pv[q] as int] as int] as int);
                    assert(fkey(kc@, kb@, bsize as int, pv[q + 1] as int) == col@[rmv@[pv[q + 1] as int] as int] as int);
                }
            }
            Ok((c.codes, ib, 2))
        },
        Ok(None) => {
            proof {
                lemma_keyidx_none(kc@, kb@, Seq::empty(), Seq::empty(), bsize as int, n as int);
            }
            Ok((Vec::new(), Vec::new(), 0))
        },
        Err(e) => Err(QueryError::WorkerFailed(e)),
    }
}

} // verus!
