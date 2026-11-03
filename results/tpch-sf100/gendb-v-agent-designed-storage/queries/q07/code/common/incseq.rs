//! Search and stepping in a strictly increasing `u32` sequence (run starts, offsets): the last entry at or below a
//! value by binary search (`find_le`) and by a forward step from a known entry (`step_le`, eight entries at a time
//! with a branch-free count, so a cursor that moves a few entries per call costs about one compare block). The
//! sequence's length `n` is passed along (worker code reads no slice length).
use vstd::prelude::*;

verus! {

/// `st` strictly increases.
pub open spec fn inc(st: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < st.len() - 1 ==> #[trigger] st[k] < st[k + 1]
}

/// Entries of a strictly increasing sequence increase between any two positions.
pub proof fn lemma_inc(st: Seq<u32>, a: int, b: int)
    requires inc(st), 0 <= a <= b < st.len(),
    ensures a < b ==> st[a] < st[b], st[a] <= st[b],
    decreases b - a,
{
    if a < b {
        lemma_inc(st, a, b - 1);
        assert(st[b - 1] < st[b]);
    }
}

/// `r` is the last entry at or below `v`: `st[r] <= v`, and the next entry (if any) is above `v`.
pub open spec fn last_le(st: Seq<u32>, v: int, r: int) -> bool {
    &&& 0 <= r < st.len()
    &&& st[r] <= v
    &&& r + 1 < st.len() ==> st[r + 1] > v
}

/// The last entry of `st` (`n` entries) at or below `v` (binary search), when the first entry is at or below `v`.
pub fn find_le(st: &[u32], n: usize, v: u32) -> (r: Option<usize>)
    requires inc(st@), n == st@.len(),
    ensures
        r matches Some(k) ==> last_le(st@, v as int, k as int),
        r is None ==> st@.len() == 0 || st@[0] > v,
    no_unwind
{
    if n == 0 || st[0] > v {
        return None;
    }
    // st[lo] <= v; hi == n or st[hi] > v
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while hi - lo > 1
        invariant
            n == st@.len(), inc(st@),
            0 <= lo < hi <= n,
            st@[lo as int] <= v,
            hi < n ==> st@[hi as int] > v,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if st[mid] <= v {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    proof {
        if lo + 1 < n {
            assert(hi == lo + 1);
        }
    }
    Some(lo)
}

/// The entries `r + 1 .. r + 9` at or below `v` (a prefix of the window, since `st` increases).
#[inline(always)]
fn count8(st: &[u32], n: usize, r: usize, v: u32) -> (cnt: usize)
    requires inc(st@), n == st@.len(), r + 9 <= n,
    ensures
        cnt <= 8,
        forall|t: int| 0 <= t < cnt ==> #[trigger] st@[r + 1 + t] <= v,
        cnt < 8 ==> st@[r + 1 + cnt] > v,
    no_unwind
{
    let (_, tail) = st.split_at(r + 1);
    let (w, _) = tail.split_at(8);
    let mut cnt: usize = 0;
    let mut i: usize = 0;
    while i < 8
        invariant
            w@.len() == 8, i <= 8, cnt <= i,
            forall|t: int| 0 <= t < 8 ==> #[trigger] w@[t] == st@[r + 1 + t],
            inc(st@), r + 9 <= st@.len(),
            forall|t: int| 0 <= t < cnt ==> #[trigger] w@[t] <= v,
            forall|t: int| cnt <= t < i ==> #[trigger] w@[t] > v,
        decreases 8 - i,
    {
        let le: usize = if w[i] <= v { 1 } else { 0 };
        proof {
            if le == 1 && cnt < i {
                // an earlier entry above v would be above w[i] too
                lemma_inc(st@, r + 1 + cnt, r + 1 + i);
                assert(w@[cnt as int] > v);
            }
        }
        cnt = cnt + le;
        i = i + 1;
    }
    proof {
        assert forall|t: int| 0 <= t < cnt implies #[trigger] st@[r + 1 + t] <= v by {
            assert(w@[t] <= v);
        }
        if cnt < 8 {
            assert(w@[cnt as int] > v);
        }
    }
    cnt
}

/// From an entry `r` at or below `v`, the last entry at or below `v` (a forward step) of `st` (`n` entries).
#[inline(always)]
pub fn step_le(st: &[u32], n: usize, r: usize, v: u32) -> (r2: usize)
    requires inc(st@), n == st@.len(), r < n, st@[r as int] <= v,
    ensures r <= r2, last_le(st@, v as int, r2 as int),
    no_unwind
{
    let mut cur = r;
    while n - cur > 8
        invariant n == st@.len(), inc(st@), r <= cur < n, st@[cur as int] <= v,
        decreases n - cur,
    {
        let cnt = count8(st, n, cur, v);
        if cnt < 8 {
            let r2 = cur + cnt;
            proof {
                if cnt > 0 {
                    let t = cnt - 1;
                    assert(st@[cur + 1 + t] <= v);
                    assert(cur + 1 + t == r2);
                } else {
                    assert(r2 == cur);
                }
                assert(st@[r2 as int] <= v);
                assert(st@[cur + 1 + cnt] > v);
                assert(cur + 1 + cnt == r2 + 1);
                assert(last_le(st@, v as int, r2 as int));
            }
            return r2;
        }
        proof {
            assert(st@[cur + 1 + 7] <= v);
        }
        cur = cur + 8;
    }
    while cur + 1 < n && st[cur + 1] <= v
        invariant n == st@.len(), r <= cur < n, st@[cur as int] <= v,
        decreases n - cur,
    {
        cur = cur + 1;
    }
    cur
}

} // verus!
