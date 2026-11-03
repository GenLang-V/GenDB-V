//! The group table a scan of partsupp rows `lo .. hi` produces, and its loop invariant.
//!
//! With the rows sorted by ps_partkey, the qualifying rows of one key are consecutive among the qualifying rows,
//! so a scan sees one run per key: keys strictly increasing. A run whose SUM is above the bound `lb` is emitted as
//! `(key, SUM)`; a run at or below `lb` may be dropped (`lb` is a lower bound of the HAVING threshold, so such a
//! group cannot pass). `groups_ok`: every emitted SUM is the key's whole SUM over the range, and every key with a
//! qualifying row and a SUM above `lb` is emitted. While scanning, the open run is `(cur, acc)` (`scan_inv`); a
//! dropped run's key is below the open run's, so no later row changes its SUM. `lemma_step_skip` /
//! `lemma_step_same` / `lemma_step_new` advance the invariant by one row.
use vstd::prelude::*;
use crate::spec::numeric::abs;
use super::tables::*;
use super::rows::*;

verus! {

/// The rows `lo .. hi` are sorted by key.
pub open spec fn sorted_rows(t: Tabs, lo: int, hi: int) -> bool {
    forall|a: int, b: int| lo <= a <= b < hi ==> #[trigger] rkey(t, a) <= #[trigger] rkey(t, b)
}

/// The emitted groups `keys/sums[0 .. len]` of the rows `lo .. r`, without the open run.
pub open spec fn closed_ok(t: Tabs, name: Seq<u8>, lo: int, r: int, keys: Seq<i64>, sums: Seq<i128>, len: int) -> bool {
    &&& 0 <= len <= keys.len() && len <= sums.len()
    &&& forall|i: int| 0 <= i < len ==> #[trigger] sums[i] as int == ksum(t, name, keys[i] as int, lo, r)
            && kcnt(t, name, keys[i] as int, lo, r) > 0
    &&& forall|i: int, j: int| 0 <= i < j < len ==> #[trigger] keys[i] < #[trigger] keys[j]
}

/// The scan's invariant at row `r`: the emitted groups, the open run `(cur, acc)` (key of row `cur_row`) after them,
/// and every other key with a qualifying row dropped: below the open run, with a SUM at most `lb`.
pub open spec fn scan_inv(t: Tabs, name: Seq<u8>, lo: int, r: int, keys: Seq<i64>, sums: Seq<i128>, len: int,
    have: bool, cur: i64, acc: i128, cur_row: int, lb: i128) -> bool
{
    &&& closed_ok(t, name, lo, r, keys, sums, len)
    &&& have ==> {
        &&& acc as int == ksum(t, name, cur as int, lo, r)
        &&& kcnt(t, name, cur as int, lo, r) > 0
        &&& lo <= cur_row < r
        &&& rkey(t, cur_row) == cur
        &&& forall|i: int| 0 <= i < len ==> #[trigger] keys[i] < cur
    }
    &&& !have ==> len == 0
    &&& forall|k: int| #[trigger] kcnt(t, name, k, lo, r) > 0 ==>
            (exists|i: int| 0 <= i < len && keys[i] as int == k) || (have && k == cur as int)
            || (have && k < cur && ksum(t, name, k, lo, r) <= lb)
}

/// The groups of rows `lo .. hi`: keys strictly increasing, each SUM the key's SUM over the range, each key with a
/// qualifying row, and every key with a qualifying row and a SUM above `lb` present.
pub open spec fn groups_ok(t: Tabs, name: Seq<u8>, lo: int, hi: int, keys: Seq<i64>, sums: Seq<i128>, len: int, lb: i128) -> bool {
    &&& closed_ok(t, name, lo, hi, keys, sums, len)
    &&& forall|k: int| #[trigger] kcnt(t, name, k, lo, hi) > 0 && ksum(t, name, k, lo, hi) > lb ==>
            exists|i: int| 0 <= i < len && keys[i] as int == k
}

pub proof fn lemma_scan_start(t: Tabs, name: Seq<u8>, lo: int, keys: Seq<i64>, sums: Seq<i128>, lb: i128)
    ensures scan_inv(t, name, lo, lo, keys, sums, 0, false, 0, 0, 0, lb),
{
}

/// A non-qualifying row changes nothing.
pub proof fn lemma_step_skip(t: Tabs, name: Seq<u8>, lo: int, r: int, keys: Seq<i64>, sums: Seq<i128>, len: int,
    have: bool, cur: i64, acc: i128, cur_row: int, lb: i128)
    requires lo <= r, scan_inv(t, name, lo, r, keys, sums, len, have, cur, acc, cur_row, lb), !rowq(t, name, r),
    ensures scan_inv(t, name, lo, r + 1, keys, sums, len, have, cur, acc, cur_row, lb),
{
    assert forall|k: int| #[trigger] kcnt(t, name, k, lo, r + 1) == kcnt(t, name, k, lo, r)
        && ksum(t, name, k, lo, r + 1) == ksum(t, name, k, lo, r) by {}
}

/// A qualifying row of the open run's key adds to the run.
pub proof fn lemma_step_same(t: Tabs, name: Seq<u8>, lo: int, r: int, keys: Seq<i64>, sums: Seq<i128>, len: int,
    cur: i64, acc: i128, cur_row: int, acc2: i128, lb: i128)
    requires
        lo <= r, scan_inv(t, name, lo, r, keys, sums, len, true, cur, acc, cur_row, lb),
        rowq(t, name, r), rkey(t, r) == cur, acc2 == acc + rval(t, r),
    ensures scan_inv(t, name, lo, r + 1, keys, sums, len, true, cur, acc2, cur_row, lb),
{
    assert forall|k: int| k != cur ==> #[trigger] kcnt(t, name, k, lo, r + 1) == kcnt(t, name, k, lo, r)
        && ksum(t, name, k, lo, r + 1) == ksum(t, name, k, lo, r) by {}
    assert forall|i: int| 0 <= i < len implies #[trigger] sums[i] as int == ksum(t, name, keys[i] as int, lo, r + 1)
        && kcnt(t, name, keys[i] as int, lo, r + 1) > 0 by {
        assert(keys[i] < cur);
    }
    assert forall|k: int| #[trigger] kcnt(t, name, k, lo, r + 1) > 0 implies
        (exists|i: int| 0 <= i < len && keys[i] as int == k) || k == cur as int
        || (k < cur && ksum(t, name, k, lo, r + 1) <= lb) by {
        if k != cur {
            assert(kcnt(t, name, k, lo, r) > 0);
        }
    }
}

/// A qualifying row of a new key (above the open run's key) closes the run, emitted when its SUM is above `lb`
/// (`emit`), and opens a new one.
pub proof fn lemma_step_new(t: Tabs, name: Seq<u8>, lo: int, r: int, keys: Seq<i64>, sums: Seq<i128>, len: int,
    have: bool, cur: i64, acc: i128, cur_row: int, keys2: Seq<i64>, sums2: Seq<i128>, len2: int, k2: i64, v2: i128,
    lb: i128, emit: bool)
    requires
        lo <= r, scan_inv(t, name, lo, r, keys, sums, len, have, cur, acc, cur_row, lb),
        rowq(t, name, r), rkey(t, r) == k2, v2 == rval(t, r),
        have ==> cur < k2,
        emit == (have && acc > lb),
        emit ==> len < keys.len() && len < sums.len() && keys2 == keys.update(len, cur) && sums2 == sums.update(len, acc)
            && len2 == len + 1,
        !emit ==> keys2 == keys && sums2 == sums && len2 == len,
    ensures scan_inv(t, name, lo, r + 1, keys2, sums2, len2, true, k2, v2, r, lb),
{
    lemma_bounds(t, name, k2 as int, lo, r);
    // The new key has no qualifying row before `r`: it is above every emitted key, the open run and every dropped key.
    if kcnt(t, name, k2 as int, lo, r) > 0 {
        if have {
            assert(!(exists|i: int| 0 <= i < len && keys[i] as int == k2 as int)) by {
                if exists|i: int| 0 <= i < len && keys[i] as int == k2 as int {
                    let i = choose|i: int| 0 <= i < len && keys[i] as int == k2 as int;
                    assert(keys[i] < cur);
                }
            }
        }
        assert(false);
    }
    lemma_kzero(t, name, k2 as int, lo, r);
    assert forall|k: int| k != k2 ==> #[trigger] kcnt(t, name, k, lo, r + 1) == kcnt(t, name, k, lo, r)
        && ksum(t, name, k, lo, r + 1) == ksum(t, name, k, lo, r) by {}
    assert(kcnt(t, name, k2 as int, lo, r + 1) == 1);
    assert forall|i: int| 0 <= i < len2 implies #[trigger] sums2[i] as int == ksum(t, name, keys2[i] as int, lo, r + 1)
        && kcnt(t, name, keys2[i] as int, lo, r + 1) > 0 by {
        if i < len {
            assert(keys2[i] == keys[i] && sums2[i] == sums[i]);
            if have { assert(keys[i] < cur); }
        } else {
            assert(keys2[i] == cur && sums2[i] == acc);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < len2 implies #[trigger] keys2[i] < #[trigger] keys2[j] by {
        if j < len {
            assert(keys2[i] == keys[i] && keys2[j] == keys[j]);
        } else {
            assert(keys2[i] == keys[i]);
        }
    }
    assert forall|i: int| 0 <= i < len2 implies #[trigger] keys2[i] < k2 by {
        if i < len {
            assert(keys2[i] == keys[i]);
            if have { assert(keys[i] < cur); }
        }
    }
    assert forall|k: int| #[trigger] kcnt(t, name, k, lo, r + 1) > 0 implies
        (exists|i: int| 0 <= i < len2 && keys2[i] as int == k) || k == k2 as int
        || (k < k2 && ksum(t, name, k, lo, r + 1) <= lb) by {
        if k != k2 {
            assert(kcnt(t, name, k, lo, r) > 0);
            if exists|i: int| 0 <= i < len && keys[i] as int == k {
                let i = choose|i: int| 0 <= i < len && keys[i] as int == k;
                assert(keys2[i] == keys[i]);
            } else if have && k == cur {
                if emit {
                    assert(keys2[len] == cur);
                } else {
                    assert(ksum(t, name, k, lo, r) == acc);
                }
            } else {
                assert(have && k < cur && ksum(t, name, k, lo, r) <= lb);
            }
        }
    }
}

/// The end of the range: closing the open run (emitted when its SUM is above `lb`) gives the range's groups.
pub proof fn lemma_scan_end(t: Tabs, name: Seq<u8>, lo: int, hi: int, keys: Seq<i64>, sums: Seq<i128>, len: int,
    have: bool, cur: i64, acc: i128, cur_row: int, keys2: Seq<i64>, sums2: Seq<i128>, len2: int, lb: i128, emit: bool)
    requires
        lo <= hi, scan_inv(t, name, lo, hi, keys, sums, len, have, cur, acc, cur_row, lb),
        emit == (have && acc > lb),
        emit ==> len < keys.len() && len < sums.len() && keys2 == keys.update(len, cur) && sums2 == sums.update(len, acc)
            && len2 == len + 1,
        !emit ==> keys2 == keys && sums2 == sums && len2 == len,
    ensures groups_ok(t, name, lo, hi, keys2, sums2, len2, lb),
{
    assert forall|i: int| 0 <= i < len2 implies #[trigger] sums2[i] as int == ksum(t, name, keys2[i] as int, lo, hi)
        && kcnt(t, name, keys2[i] as int, lo, hi) > 0 by {
        if i < len {
            assert(keys2[i] == keys[i] && sums2[i] == sums[i]);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < len2 implies #[trigger] keys2[i] < #[trigger] keys2[j] by {
        if j < len {
            assert(keys2[i] == keys[i] && keys2[j] == keys[j]);
        } else {
            assert(keys2[i] == keys[i]);
        }
    }
    assert forall|k: int| #[trigger] kcnt(t, name, k, lo, hi) > 0 && ksum(t, name, k, lo, hi) > lb implies
        exists|i: int| 0 <= i < len2 && keys2[i] as int == k by {
        if exists|i: int| 0 <= i < len && keys[i] as int == k {
            let i = choose|i: int| 0 <= i < len && keys[i] as int == k;
            assert(keys2[i] == keys[i]);
        } else if have && k == cur {
            assert(ksum(t, name, k, lo, hi) == acc);
            assert(keys2[len] == cur);
        }
    }
}

} // verus!
