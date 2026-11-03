//! Key indexes over a frame-of-reference key column (U32 codes, I64 bases, uniform groups of `bsize` rows).
//! The index kind is a stored flag:
//! - kind 0: no order is known; lookups scan;
//! - kind 1: the stored rows are sorted by key (nondecreasing); lookups binary-search the rows;
//! - kind 2: an index column (U32 codes, U64 bases, the same uniform groups) lists the stored rows in key order
//!   (a bijection of `[0, n)`); lookups binary-search the index.
//! `irow(r)` is the stored row at index position `r` (`r` itself for kinds 0 and 1). `key_find` is sound and complete;
//! `key_range` (kinds 1 and 2) returns the index positions `[lo, hi)` holding exactly the rows of one key.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use super::colfmt::*;
use super::read::lemma_div_lt;

verus! {

/// Key of stored row `j`: `bases[j / bsize] + codes[j]`.
pub open spec fn fkey(kc: Seq<u32>, kb: Seq<i64>, bsize: int, j: int) -> int {
    kb[j / bsize] + kc[j]
}

/// Value at index position `r` of a U32/U64 FOR index column.
pub open spec fn fidx(ic: Seq<u32>, ib: Seq<u64>, bsize: int, r: int) -> int {
    ib[r / bsize] + ic[r]
}

/// Stored row at index position `r`.
pub open spec fn irow(kind: u64, ic: Seq<u32>, ib: Seq<u64>, bsize: int, r: int) -> int {
    if kind == 2 { fidx(ic, ib, bsize, r) } else { r }
}

/// The index is ordered at position `r`: the key at `r` is at most the key at `r + 1`.
pub open spec fn sorted_at(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bsize: int, kind: u64, r: int) -> bool {
    fkey(kc, kb, bsize, irow(kind, ic, ib, bsize, r)) <= fkey(kc, kb, bsize, irow(kind, ic, ib, bsize, r + 1))
}

/// The index column as a row map.
pub open spec fn idx_map(ic: Seq<u32>, ib: Seq<u64>, bsize: int, n: int) -> Seq<int> {
    Seq::new(n as nat, |r: int| fidx(ic, ib, bsize, r))
}

/// A key index of kind `kind` over the `n` stored rows of key column `kc`/`kb`.
pub open spec fn keyidx_ok(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bsize: int, kind: u64, n: int) -> bool {
    &&& bsize >= 1
    &&& n >= 0
    &&& kc.len() == n
    &&& kb.len() * bsize >= n
    &&& kind <= 2
    &&& kind == 2 ==> ic.len() == n && ib.len() * bsize >= n && is_perm(idx_map(ic, ib, bsize, n), n)
    &&& kind >= 1 ==> forall|r: int| 0 <= r < n - 1 ==> #[trigger] sorted_at(kc, kb, ic, ib, bsize, kind, r)
}

/// Index positions map to stored rows below `n`.
pub proof fn lemma_irow_bound(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bsize: int, kind: u64, n: int, r: int)
    requires
        keyidx_ok(kc, kb, ic, ib, bsize, kind, n),
        0 <= r < n,
    ensures
        0 <= irow(kind, ic, ib, bsize, r) < n,
{
    if kind == 2 {
        assert(idx_map(ic, ib, bsize, n)[r] == fidx(ic, ib, bsize, r));
    }
}

/// Keys are nondecreasing along the index.
pub proof fn lemma_sorted_le(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bsize: int, kind: u64, n: int, a: int, b: int)
    requires
        keyidx_ok(kc, kb, ic, ib, bsize, kind, n),
        kind >= 1,
        0 <= a <= b < n,
    ensures
        fkey(kc, kb, bsize, irow(kind, ic, ib, bsize, a)) <= fkey(kc, kb, bsize, irow(kind, ic, ib, bsize, b)),
    decreases b - a,
{
    if a < b {
        lemma_sorted_le(kc, kb, ic, ib, bsize, kind, n, a, b - 1);
        assert(sorted_at(kc, kb, ic, ib, bsize, kind, b - 1));
    }
}

/// Key at index position `r` (decoded in `i128`, so no overflow).
fn key_at_pos(kc: &[u32], kb: &[i64], ic: &[u32], ib: &[u64], bsize: usize, kind: u64, n: usize, r: usize) -> (v: i128)
    requires
        keyidx_ok(kc@, kb@, ic@, ib@, bsize as int, kind, n as int),
        r < n,
    ensures
        v == fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, r as int)),
    no_unwind
{
    proof {
        lemma_irow_bound(kc@, kb@, ic@, ib@, bsize as int, kind, n as int, r as int);
        lemma_div_lt(r as int, bsize as int, kb@.len() as int);
        if kind == 2 {
            lemma_div_lt(r as int, bsize as int, ib@.len() as int);
        }
    }
    let j: usize = if kind == 2 { (ib[r / bsize] as i128 + ic[r] as i128) as usize } else { r };
    proof {
        lemma_div_lt(j as int, bsize as int, kb@.len() as int);
    }
    kb[j / bsize] as i128 + kc[j] as i128
}

/// A stored row with key `k`, or `None` exactly when no stored row has key `k`.
pub fn key_find(kc: &[u32], kb: &[i64], ic: &[u32], ib: &[u64], bsize: usize, kind: u64, n: usize, k: i128) -> (r: Option<usize>)
    requires
        keyidx_ok(kc@, kb@, ic@, ib@, bsize as int, kind, n as int),
    ensures
        r matches Some(j) ==> j < n && fkey(kc@, kb@, bsize as int, j as int) == k,
        r is None ==> forall|j: int| 0 <= j < n ==> #[trigger] fkey(kc@, kb@, bsize as int, j) != k,
    no_unwind
{
    if kind == 0 {
        let mut j: usize = 0;
        while j < n
            invariant
                keyidx_ok(kc@, kb@, ic@, ib@, bsize as int, kind, n as int),
                kind == 0,
                j <= n,
                forall|i: int| 0 <= i < j ==> #[trigger] fkey(kc@, kb@, bsize as int, i) != k,
            decreases n - j,
        {
            if key_at_pos(kc, kb, ic, ib, bsize, kind, n, j) == k {
                return Some(j);
            }
            j = j + 1;
        }
        return None;
    }
    let (lo, hi) = key_range(kc, kb, ic, ib, bsize, kind, n, k);
    if lo < hi {
        proof {
            lemma_irow_bound(kc@, kb@, ic@, ib@, bsize as int, kind, n as int, lo as int);
            if kind == 2 {
                lemma_div_lt(lo as int, bsize as int, ib@.len() as int);
            }
        }
        let j: usize = if kind == 2 { (ib[lo / bsize] as i128 + ic[lo] as i128) as usize } else { lo };
        Some(j)
    } else {
        proof {
            assert forall|j: int| 0 <= j < n implies #[trigger] fkey(kc@, kb@, bsize as int, j) != k by {
                if kind == 2 {
                    assert(covered(idx_map(ic@, ib@, bsize as int, n as int), j));
                    let r = choose|r: int| 0 <= r < n && idx_map(ic@, ib@, bsize as int, n as int)[r] == j;
                    assert(irow(kind, ic@, ib@, bsize as int, r) == j);
                } else {
                    assert(irow(kind, ic@, ib@, bsize as int, j) == j);
                }
            }
        }
        None
    }
}

/// A stored row with key `k`: stored row `guess` when it has the key (one probe, for dense keys), else `key_find`.
pub fn key_find_guess(kc: &[u32], kb: &[i64], ic: &[u32], ib: &[u64], bsize: usize, kind: u64, n: usize, k: i128,
    guess: usize) -> (r: Option<usize>)
    requires
        keyidx_ok(kc@, kb@, ic@, ib@, bsize as int, kind, n as int),
    ensures
        r matches Some(j) ==> j < n && fkey(kc@, kb@, bsize as int, j as int) == k,
        r is None ==> forall|j: int| 0 <= j < n ==> #[trigger] fkey(kc@, kb@, bsize as int, j) != k,
    no_unwind
{
    if guess < n {
        proof {
            lemma_div_lt(guess as int, bsize as int, kb@.len() as int);
        }
        if kb[guess / bsize] as i128 + kc[guess] as i128 == k {
            return Some(guess);
        }
    }
    key_find(kc, kb, ic, ib, bsize, kind, n, k)
}

/// For kinds 1 and 2: the index positions `[lo, hi)` holding exactly the rows of key `k` (`lo == hi`: none).
pub fn key_range(kc: &[u32], kb: &[i64], ic: &[u32], ib: &[u64], bsize: usize, kind: u64, n: usize, k: i128) -> (r: (usize, usize))
    requires
        keyidx_ok(kc@, kb@, ic@, ib@, bsize as int, kind, n as int),
        kind >= 1,
    ensures
        r.0 <= r.1 <= n,
        forall|p: int| 0 <= p < n ==> (r.0 <= p < r.1 <==> #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) == k),
    no_unwind
{
    // Lower bound: first position with key >= k.
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant
            keyidx_ok(kc@, kb@, ic@, ib@, bsize as int, kind, n as int),
            kind >= 1,
            lo <= hi <= n,
            forall|p: int| 0 <= p < lo ==> #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) < k,
            forall|p: int| hi <= p < n ==> #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) >= k,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if key_at_pos(kc, kb, ic, ib, bsize, kind, n, mid) < k {
            proof {
                assert forall|p: int| 0 <= p < mid + 1 implies #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) < k by {
                    lemma_sorted_le(kc@, kb@, ic@, ib@, bsize as int, kind, n as int, p, mid as int);
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|p: int| mid <= p < n implies #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) >= k by {
                    lemma_sorted_le(kc@, kb@, ic@, ib@, bsize as int, kind, n as int, mid as int, p);
                }
            }
            hi = mid;
        }
    }
    let first = lo;
    // Upper bound: first position with key > k.
    let mut lo2: usize = first;
    let mut hi2: usize = n;
    while lo2 < hi2
        invariant
            keyidx_ok(kc@, kb@, ic@, ib@, bsize as int, kind, n as int),
            kind >= 1,
            first <= lo2 <= hi2 <= n,
            forall|p: int| 0 <= p < first ==> #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) < k,
            forall|p: int| first <= p < n ==> #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) >= k,
            forall|p: int| first <= p < lo2 ==> #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) <= k,
            forall|p: int| hi2 <= p < n ==> #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) > k,
        decreases hi2 - lo2,
    {
        let mid = lo2 + (hi2 - lo2) / 2;
        if key_at_pos(kc, kb, ic, ib, bsize, kind, n, mid) <= k {
            proof {
                assert forall|p: int| first <= p < mid + 1 implies #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) <= k by {
                    lemma_sorted_le(kc@, kb@, ic@, ib@, bsize as int, kind, n as int, p, mid as int);
                }
            }
            lo2 = mid + 1;
        } else {
            proof {
                assert forall|p: int| mid <= p < n implies #[trigger] fkey(kc@, kb@, bsize as int, irow(kind, ic@, ib@, bsize as int, p)) > k by {
                    lemma_sorted_le(kc@, kb@, ic@, ib@, bsize as int, kind, n as int, mid as int, p);
                }
            }
            hi2 = mid;
        }
    }
    (first, lo2)
}

/// The key of stored row `j` is its FOR value (`colfmt::for_at`) when the key column has U32 codes and I64 bases
/// over uniform groups of `bsize` rows.
pub proof fn lemma_fkey_for_at(gp: PartView, n: int, bsize: int, kb: PartView, kc: PartView, j: int)
    requires
        groups_part_ok(gp, n, bsize),
        kb is I64,
        kc is U32,
        0 <= j < n,
    ensures
        fkey(u32s(kc), i64s(kb), bsize, j) == for_at(u64s(gp), kb, kc, j),
{
    super::read::lemma_for_row(gp, n, bsize, kb, kc, j);
}

} // verus!
