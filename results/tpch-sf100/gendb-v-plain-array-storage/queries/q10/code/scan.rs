//! The scan task (`STask`): orders rows `[olo, ohi)` and the pair checks of lineitem rows `[lo, hi)`.
//!
//! The task walks its orders in batches of at most `BATCH` rows:
//! 1. `win_rows`: the rows in the date window, ascending (64-row masks of branch-free compares, then their set bits);
//! 2. `gather_orders`: their keys and customer rows (`-1` when the customer key is outside the positional range);
//! 3. `find_runs`: the run of each order's key in `l_orderkey` (`agent::runs`), searched forward from the end of the
//!    previous run;
//! 4. the adjacent pairs of `l_orderkey` the runs passed are checked while they are cached (`runs::check_pairs`);
//! 5. `touch`: one load per cache line the next step reads, all independent, so the misses overlap;
//! 6. `emit_batch`: each run's `R` rows summed (`run_value`), and every order with an `R` row appended to the bucket
//!    of its customer row (`CPB` customers per bucket).
//! Finally it checks the remaining pairs of its lineitem rows.
//!
//! Buckets: bucket `b` of the task owns positions `[b * rcap, (b + 1) * rcap)` of `rv`; `cnt[b]` are filled. An
//! entry packs the order's encoded revenue (`agent::enc`, below `PCAP`) and its customer row's offset in the bucket
//! as `enc * CPB + (row - b * CPB)`: one 8-byte store per hit. A full bucket fails the task. What the task proves
//! (`chunk_post`): its pairs are in order; each bucket lists its hitting orders ascending with their customer rows
//! (`bucket_ok`); and *when `l_orderkey` is sorted* (which the plan concludes from all tasks' pairs) each listed
//! revenue is the order's revenue over all lineitem rows and every hitting order of the task's rows is listed.
//! Nothing depends on the stored row order for correctness: unexpected data only fails a check.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::link::query::text_at;
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::xcols::*;
use crate::agent::enc::*;
use crate::agent::runs::*;
use crate::agent::common::bits::*;
use crate::agent::common::tz::*;

verus! {

/// Orders rows per batch.
pub const BATCH: usize = 4096;

/// Customer rows per bucket.
pub const CPB: usize = 131072;

/// Bound of the encoded revenue of a packed entry: `enc * CPB + offset` stays below `2^63`.
pub const PCAP: i64 = 0x4000_0000_0000;

/// Longest run summed (longer runs fail the task; TPC-H orders have at most 7 lineitems).
pub const MAXRUN: usize = 64;

// ------------------------------------------------------------------------------------------------ specifications

/// The customer row of orders row `j` (its customer key less the positional base; may lie outside the table).
pub open spec fn crow(sv: StoresView, cbase: int, j: int) -> int { oc(sv)[j] as int - cbase }

/// The key of orders row `j`.
pub open spec fn okey(sv: StoresView, j: int) -> int { ok(sv)[j] as int }

/// The encoded-revenue part of a packed bucket entry.
pub open spec fn pk_hi(v: i64) -> int { v as int / (CPB as int) }

/// The customer-row offset (inside its bucket) of a packed bucket entry.
pub open spec fn pk_lo(v: i64) -> int { v as int % (CPB as int) }

/// `e` encodes the revenue `s` with count `k` (`agent::enc`) and fits a packed entry.
pub open spec fn pk_rev_ok(e: int, s: int, k: int) -> bool {
    &&& 0 <= s && 0 <= k && (k == 0 ==> s == 0)
    &&& e == enc(s, k) && e < PCAP as int
}

/// Orders row `j` is in the window and its customer row inside the customer table.
pub open spec fn qualifies(sv: StoresView, dlo: int, dhi: int, cbase: int, j: int) -> bool {
    win(sv, dlo, dhi, j) && 0 <= crow(sv, cbase, j) < n_c(sv)
}

/// Orders row `j` qualifies and some lineitem row hits its key.
pub open spec fn ohit(sv: StoresView, dlo: int, dhi: int, cbase: int, j: int) -> bool {
    qualifies(sv, dlo, dhi, cbase, j) && kcnt(sv, okey(sv, j), 0, n_l(sv)) > 0
}

/// The bucket of orders row `j`.
pub open spec fn obk(sv: StoresView, cbase: int, j: int) -> int { crow(sv, cbase, j) / (CPB as int) }

/// The rows `bi[0..m)` are exactly the rows of `[i0, i1)` in the window, ascending.
pub open spec fn win_list(sv: StoresView, dlo: int, dhi: int, bi: Seq<usize>, m: int, i0: int, i1: int) -> bool {
    &&& 0 <= m <= bi.len()
    &&& forall|x: int| 0 <= x < m ==> i0 <= #[trigger] bi[x] < i1 && win(sv, dlo, dhi, bi[x] as int)
    &&& forall|x: int, y: int| 0 <= x < y < m ==> #[trigger] bi[x] < #[trigger] bi[y]
    &&& forall|r: int| i0 <= r < i1 && win(sv, dlo, dhi, r) ==> exists|x: int| 0 <= x < m && #[trigger] bi[x] == r
}

/// Entry `p` of bucket `b` is the hitting orders row `j` of that bucket, packed with its customer row's offset and
/// (on sorted keys) its encoded revenue.
pub open spec fn entry_ok(c: Cols, sv: StoresView, rv: Seq<i64>, rcap: int, b: int, p: int, j: int) -> bool {
    &&& ohit(sv, c.dlo as int, c.dhi as int, c.cbase as int, j)
    &&& obk(sv, c.cbase as int, j) == b
    &&& 0 <= rv[b * rcap + p]
    &&& pk_lo(rv[b * rcap + p]) == crow(sv, c.cbase as int, j) - b * (CPB as int)
    &&& lk_sorted(sv) ==> pk_rev_ok(pk_hi(rv[b * rcap + p]), ksum(sv, okey(sv, j), 0, n_l(sv)),
            kcnt(sv, okey(sv, j), 0, n_l(sv)) as int)
}

/// Bucket `b` lists the hitting orders of `[olo, ohi)` in it, ascending (all of them on sorted keys).
pub open spec fn bucket_ok(c: Cols, sv: StoresView, rv: Seq<i64>, cnt: Seq<usize>, lists: Seq<Seq<int>>,
    rcap: int, olo: int, ohi: int, b: int) -> bool
{
    let l = lists[b];
    let n = cnt[b] as int;
    &&& l.len() == n && n <= rcap
    &&& forall|p: int| 0 <= p < n ==> olo <= #[trigger] l[p] < ohi
    &&& forall|p: int, q: int| 0 <= p < q < n ==> #[trigger] l[p] < #[trigger] l[q]
    &&& forall|p: int| 0 <= p < n ==> entry_ok(c, sv, rv, rcap, b, p, #[trigger] l[p])
    &&& lk_sorted(sv) ==> forall|j: int| olo <= j < ohi && ohit(sv, c.dlo as int, c.dhi as int, c.cbase as int, j)
            && obk(sv, c.cbase as int, j) == b ==> #[trigger] l.contains(j)
}

/// Every bucket of a task is `bucket_ok`.
pub open spec fn buckets_ok(c: Cols, sv: StoresView, rv: Seq<i64>, cnt: Seq<usize>, lists: Seq<Seq<int>>,
    nb: int, rcap: int, olo: int, ohi: int) -> bool
{
    &&& 0 <= rcap && rv.len() == nb * rcap && cnt.len() == nb && lists.len() == nb
    &&& forall|b: int| 0 <= b < nb ==> #[trigger] bucket_ok(c, sv, rv, cnt, lists, rcap, olo, ohi, b)
}

/// On sorted keys, every qualifying order of `[olo, ohi)` has its absolute mass equal to its revenue.
pub open spec fn abs_ok(c: Cols, sv: StoresView, olo: int, ohi: int) -> bool {
    lk_sorted(sv) ==> forall|j: int| olo <= j < ohi && qualifies(sv, c.dlo as int, c.dhi as int, c.cbase as int, j) ==>
        #[trigger] kabs(sv, okey(sv, j), 0, n_l(sv)) == ksum(sv, okey(sv, j), 0, n_l(sv))
}

// ------------------------------------------------------------------------------------------------ bucket lemmas

/// Positions of different buckets differ.
proof fn lemma_pos_distinct(b: int, p: int, b2: int, p2: int, rcap: int)
    requires 0 <= p < rcap, 0 <= p2 < rcap, b != b2, 0 <= b, 0 <= b2,
    ensures b * rcap + p != b2 * rcap + p2,
{
    if b < b2 {
        assert((b + 1) * rcap <= b2 * rcap) by (nonlinear_arith) requires b + 1 <= b2, rcap >= 0;
        assert((b + 1) * rcap == b * rcap + rcap) by (nonlinear_arith);
    } else {
        assert((b2 + 1) * rcap <= b * rcap) by (nonlinear_arith) requires b2 + 1 <= b, rcap >= 0;
        assert((b2 + 1) * rcap == b2 * rcap + rcap) by (nonlinear_arith);
    }
}

/// A position of bucket `b < nb` lies inside the buffers.
pub proof fn lemma_pos_bound(b: int, p: int, nb: int, rcap: int)
    requires 0 <= b < nb, 0 <= p < rcap,
    ensures 0 <= b * rcap + p < nb * rcap,
{
    assert(0 <= b * rcap + p < nb * rcap) by (nonlinear_arith) requires 0 <= b < nb, 0 <= p < rcap;
}

/// The bucket of a customer row is below `nb` when `nb` buckets cover the customers.
pub proof fn lemma_bucket_bound(cr: int, nc: int, nb: int)
    requires 0 <= cr < nc, nc <= nb * (CPB as int),
    ensures 0 <= cr / (CPB as int) < nb,
{
    assert(0 <= cr / (CPB as int) < nb) by (nonlinear_arith) requires 0 <= cr < nc, nc <= nb * 131072;
}

/// Extending the processed rows over rows that (on sorted keys) do not hit keeps every bucket.
proof fn lemma_extend(c: Cols, sv: StoresView, rv: Seq<i64>, cnt: Seq<usize>, lists: Seq<Seq<int>>,
    nb: int, rcap: int, olo: int, ohi: int, ohi2: int)
    requires
        buckets_ok(c, sv, rv, cnt, lists, nb, rcap, olo, ohi), ohi <= ohi2,
        lk_sorted(sv) ==> forall|j: int| ohi <= j < ohi2 ==> !#[trigger] ohit(sv, c.dlo as int, c.dhi as int, c.cbase as int, j),
    ensures buckets_ok(c, sv, rv, cnt, lists, nb, rcap, olo, ohi2),
{
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    assert forall|b: int| 0 <= b < nb implies #[trigger] bucket_ok(c, sv, rv, cnt, lists, rcap, olo, ohi2, b) by {
        assert(bucket_ok(c, sv, rv, cnt, lists, rcap, olo, ohi, b));
        let l = lists[b];
        if lk_sorted(sv) {
            assert forall|j: int| olo <= j < ohi2 && ohit(sv, dlo, dhi, cbase, j) && obk(sv, cbase, j) == b
                implies #[trigger] l.contains(j) by {
                if j >= ohi { assert(!ohit(sv, dlo, dhi, cbase, j)); }
            }
        }
    }
}

/// Appending hitting row `j == ohi` to its bucket `b` (the packed entry `e` at position `b * rcap + cnt[b]`) keeps
/// every bucket and processes row `j`.
proof fn lemma_push(c: Cols, sv: StoresView, rv: Seq<i64>, cnt: Seq<usize>, lists: Seq<Seq<int>>,
    nb: int, rcap: int, olo: int, j: int, b: int, e: i64)
    requires
        buckets_ok(c, sv, rv, cnt, lists, nb, rcap, olo, j), olo <= j,
        0 <= b < nb, cnt[b] < rcap, rcap <= usize::MAX,
        ohit(sv, c.dlo as int, c.dhi as int, c.cbase as int, j), obk(sv, c.cbase as int, j) == b,
        0 <= e, pk_lo(e) == crow(sv, c.cbase as int, j) - b * (CPB as int),
        lk_sorted(sv) ==> pk_rev_ok(pk_hi(e), ksum(sv, okey(sv, j), 0, n_l(sv)), kcnt(sv, okey(sv, j), 0, n_l(sv)) as int),
    ensures ({
        let pos = b * rcap + cnt[b];
        buckets_ok(c, sv, rv.update(pos, e), cnt.update(b, (cnt[b] + 1) as usize),
            lists.update(b, lists[b].push(j)), nb, rcap, olo, j + 1)
    }),
{
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    let pos = b * rcap + cnt[b];
    assert(bucket_ok(c, sv, rv, cnt, lists, rcap, olo, j, b));
    lemma_pos_bound(b, cnt[b] as int, nb, rcap);
    let rv2 = rv.update(pos, e);
    let cnt2 = cnt.update(b, (cnt[b] + 1) as usize);
    let lists2 = lists.update(b, lists[b].push(j));
    lemma_pos_bound(b, cnt[b] as int, nb, rcap);
    assert forall|b2: int| 0 <= b2 < nb implies #[trigger] bucket_ok(c, sv, rv2, cnt2, lists2, rcap, olo, j + 1, b2) by {
        assert(bucket_ok(c, sv, rv, cnt, lists, rcap, olo, j, b2));
        let l = lists[b2];
        let n = cnt[b2] as int;
        if b2 != b {
            assert(lists2[b2] == l && cnt2[b2] == cnt[b2]);
            assert forall|p: int| 0 <= p < n implies entry_ok(c, sv, rv2, rcap, b2, p, #[trigger] l[p]) by {
                assert(entry_ok(c, sv, rv, rcap, b2, p, l[p]));
                lemma_pos_distinct(b2, p, b, cnt[b] as int, rcap);
                lemma_pos_bound(b2, p, nb, rcap);
            }
            if lk_sorted(sv) {
                assert forall|j2: int| olo <= j2 < j + 1 && ohit(sv, dlo, dhi, cbase, j2) && obk(sv, cbase, j2) == b2
                    implies #[trigger] l.contains(j2) by {}
            }
        } else {
            let l2 = l.push(j);
            assert(lists2[b] == l2 && cnt2[b] as int == n + 1);
            assert forall|p: int| 0 <= p < n + 1 implies olo <= #[trigger] l2[p] < j + 1 by {
                if p < n { assert(l2[p] == l[p]); }
            }
            assert forall|p: int, q: int| 0 <= p < q < n + 1 implies #[trigger] l2[p] < #[trigger] l2[q] by {
                if q < n { assert(l2[p] == l[p] && l2[q] == l[q]); } else { assert(l2[p] == l[p]); }
            }
            assert forall|p: int| 0 <= p < n + 1 implies entry_ok(c, sv, rv2, rcap, b, p, #[trigger] l2[p]) by {
                if p < n {
                    assert(l2[p] == l[p]);
                    assert(entry_ok(c, sv, rv, rcap, b, p, l[p]));
                    lemma_pos_bound(b, p, nb, rcap);
                    assert(b * rcap + p != pos);
                } else {
                    assert(l2[p] == j);
                }
            }
            if lk_sorted(sv) {
                assert forall|j2: int| olo <= j2 < j + 1 && ohit(sv, dlo, dhi, cbase, j2) && obk(sv, cbase, j2) == b
                    implies #[trigger] l2.contains(j2) by {
                    if j2 < j {
                        assert(l.contains(j2));
                        let p = choose|p: int| 0 <= p < l.len() && l[p] == j2;
                        assert(l2[p] == j2);
                    } else {
                        assert(l2[n] == j);
                    }
                }
            }
        }
    }
}

/// The packed entry `v = e * CPB + cr % CPB` of customer row `cr` (in bucket `cr / CPB`) and encoded revenue
/// `1 <= e < PCAP` fits `i64` and unpacks to `e` and the row's offset in its bucket.
proof fn lemma_pack(cr: int, e: int, v: int)
    requires 0 <= cr, 1 <= e < PCAP as int, v == e * 131072 + cr % 131072,
    ensures
        0 <= v <= i64::MAX, v / (CPB as int) == e, v % (CPB as int) == cr - (cr / (CPB as int)) * (CPB as int),
{
    let x = cr % 131072;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(cr, 131072);
    assert(0 <= x < 131072);
    assert(0 <= v <= i64::MAX) by (nonlinear_arith) requires v == e * 131072 + x, 1 <= e < 0x4000_0000_0000, 0 <= x < 131072;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(v, 131072, e, x);
    assert(x == cr - (cr / 131072) * 131072) by (nonlinear_arith) requires cr == 131072 * (cr / 131072) + x;
}

// ------------------------------------------------------------------------------------------------ 1. the window

/// The window mask of the `wl` rows from `base`: bit `u` set exactly when row `base + u` is in the window.
#[inline(always)]
fn word_mask(c: &Cols, base: usize, wl: usize, Ghost(sv): Ghost<StoresView>) -> (msk: u64)
    requires cols_ok(*c, sv), 1 <= wl <= 64, base + wl <= c.no,
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(msk, u) == ((u as int) < wl && win(sv, c.dlo as int, c.dhi as int, base + u)),
    no_unwind
{
    let ghost (dlo, dhi) = (c.dlo as int, c.dhi as int);
    let mut msk: u64 = 0;
    let mut j: usize = 0;
    proof {
        assert forall|u: u64| u < 64 implies #[trigger] bit(msk, u) == ((u as int) < j && win(sv, dlo, dhi, base + u)) by {
            lemma_bit_zero(u);
        }
    }
    while j < wl
        invariant
            cols_ok(*c, sv), 1 <= wl <= 64, base + wl <= c.no, j <= wl, dlo == c.dlo, dhi == c.dhi,
            forall|u: u64| u < 64 ==> #[trigger] bit(msk, u) == ((u as int) < j && win(sv, dlo, dhi, base + u)),
        decreases wl - j,
    {
        let d = c.od[base + j] as i64;
        let f: u64 = (d >= c.dlo) as u64 - (d >= c.dhi) as u64;
        proof {
            assert(od(sv)[base + j] == c.od@[base + j]);
            assert(f <= 1 && (f == 1) == win(sv, dlo, dhi, base + j));
            assert(!bit(msk, j as u64));
            assert forall|u: u64| u < 64 implies #[trigger] bit(msk | (f << (j as u64)), u)
                == ((u as int) < j + 1 && win(sv, dlo, dhi, base + u)) by {
                lemma_bit_set(msk, f, j as u64, u);
            }
        }
        msk = msk | (f << (j as u64));
        j = j + 1;
    }
    msk
}

/// Appends `base + u` for every set bit `u` of `msk`, ascending (the rows of the word that are in the window).
#[inline(always)]
fn extract(msk: u64, base: usize, wl: usize, bi: &mut Vec<usize>, m0: usize, tzt: &[u8; 64], Ghost(sv): Ghost<StoresView>,
    Ghost(dlo): Ghost<int>, Ghost(dhi): Ghost<int>, Ghost(i0): Ghost<int>) -> (m: usize)
    requires
        1 <= wl <= 64, 0 <= i0 <= base, base + wl - i0 <= old(bi)@.len(), tzt@.len() == 64, base + wl <= usize::MAX,
        forall|u: u64| u < 64 ==> #[trigger] bit(msk, u) == ((u as int) < wl && win(sv, dlo, dhi, base + u)),
        win_list(sv, dlo, dhi, old(bi)@, m0 as int, i0, base as int), m0 <= base - i0,
    ensures
        final(bi)@.len() == old(bi)@.len(), m <= base + wl - i0,
        win_list(sv, dlo, dhi, final(bi)@, m as int, i0, base + wl),
    no_unwind
{
    let mut cur = msk;
    let mut m = m0;
    while cur != 0
        invariant
            1 <= wl <= 64, 0 <= i0 <= base, base + wl - i0 <= bi@.len(), tzt@.len() == 64, bi@.len() == old(bi)@.len(),
            base + wl <= usize::MAX,
            forall|u: u64| u < 64 ==> #[trigger] bit(msk, u) == ((u as int) < wl && win(sv, dlo, dhi, base + u)),
            m0 <= m, m0 <= base - i0, m <= base + wl - i0,
            win_list(sv, dlo, dhi, bi@, m0 as int, i0, base as int),
            forall|x: int| 0 <= x < m0 ==> #[trigger] bi@[x] == old(bi)@[x],
            forall|u: u64| u < 64 && #[trigger] bit(cur, u) ==> bit(msk, u),
            // the emitted rows: set bits of msk below every set bit of cur, ascending, one per cleared bit
            forall|x: int| m0 <= x < m ==> base + (x - m0) <= #[trigger] bi@[x] < base + wl && win(sv, dlo, dhi, bi@[x] as int),
            forall|x: int, u: u64| m0 <= x < m && u < 64 && #[trigger] bit(cur, u) ==> #[trigger] bi@[x] < base + u,
            forall|x: int, y: int| m0 <= x < y < m ==> #[trigger] bi@[x] < #[trigger] bi@[y],
            forall|u: u64| u < 64 && #[trigger] bit(msk, u) && !bit(cur, u) ==> exists|x: int| m0 <= x < m && #[trigger] bi@[x] == base + u,
        decreases cur,
    {
        let t = tz64(cur, tzt);
        proof {
            lemma_first_bit(cur);
            assert(bit(cur, t as u64));
            assert(bit(msk, t as u64));
            assert((t as int) < wl);
            if m > m0 {
                assert(bi@[m - 1] < base + t);
                assert(base + (m - 1 - m0) <= bi@[m - 1]);
            }
            assert(m - m0 <= t);
        }
        let ghost b0 = bi@;
        let ghost c0 = cur;
        bi[m] = base + t as usize;
        let c1 = cur & (cur - 1);
        proof {
            assert(c0 != 0 ==> c0 & sub(c0, 1) < c0) by (bit_vector);
            assert(cur - 1 == sub(cur, 1));
            assert forall|u: u64| u < 64 implies #[trigger] bit(c1, u) == (bit(c0, u) && u != t as u64) by {
                lemma_clear_lowest(c0, t as u64, u);
            }
            assert forall|x: int| 0 <= x < m0 implies #[trigger] bi@[x] == old(bi)@[x] by { assert(bi@[x] == b0[x]); }
            assert forall|x: int| 0 <= x < m0 implies #[trigger] bi@[x] == b0[x] by {}
            assert(win_list(sv, dlo, dhi, bi@, m0 as int, i0, base as int)) by {
                assert forall|r: int| i0 <= r < base && win(sv, dlo, dhi, r) implies exists|x: int| 0 <= x < m0 && #[trigger] bi@[x] == r by {
                    let x = choose|x: int| 0 <= x < m0 && #[trigger] b0[x] == r;
                    assert(bi@[x] == r);
                }
            }
            assert forall|x: int, u: u64| m0 <= x < m + 1 && u < 64 && #[trigger] bit(c1, u) implies #[trigger] bi@[x] < base + u by {
                assert(bit(c0, u) && u != t as u64);
                if x < m { assert(bi@[x] == b0[x]); } else {
                    assert(forall|v: u64| v < t ==> !#[trigger] bit(c0, v));
                    assert(u > t as u64);
                }
            }
            assert forall|x: int| m0 <= x < m + 1 implies base + (x - m0) <= #[trigger] bi@[x] < base + wl
                && win(sv, dlo, dhi, bi@[x] as int) by {
                if x < m {
                    assert(bi@[x] == b0[x]);
                } else {
                    if m > m0 { assert(b0[m - 1] < base + t); assert(base + (m - 1 - m0) <= b0[m - 1]); }
                }
            }
            assert forall|x: int, y: int| m0 <= x < y < m + 1 implies #[trigger] bi@[x] < #[trigger] bi@[y] by {
                assert(bi@[x] == b0[x]);
                if y < m { assert(bi@[y] == b0[y]); } else { assert(b0[x] < base + t); }
            }
            assert forall|u: u64| u < 64 && #[trigger] bit(msk, u) && !bit(c1, u) implies exists|x: int| m0 <= x < m + 1 && #[trigger] bi@[x] == base + u by {
                if u == t as u64 {
                    assert(bi@[m as int] == base + u);
                } else {
                    assert(!bit(c0, u));
                    let x = choose|x: int| m0 <= x < m && #[trigger] b0[x] == base + u;
                    assert(bi@[x] == base + u);
                }
            }
        }
        cur = c1;
        assert(m + 1 <= base + wl - i0);
        m = m + 1;
    }
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(cur, u) by {
            assert(cur == 0);
            lemma_bit_zero(u);
        }
        // the emitted rows are exactly the window rows of the word
        let bf = bi@;
        assert forall|x: int| 0 <= x < m implies (i0 <= #[trigger] bf[x] < base + wl && win(sv, dlo, dhi, bf[x] as int)) by {
            if x < m0 {} else {}
        }
        assert forall|x: int, y: int| 0 <= x < y < m implies #[trigger] bf[x] < #[trigger] bf[y] by {
            if y >= m0 && x < m0 {
                assert(bf[x] < base);
            }
        }
        assert forall|r: int| i0 <= r < base + wl && win(sv, dlo, dhi, r) implies exists|x: int| 0 <= x < m && #[trigger] bf[x] == r by {
            if r < base {
                let x = choose|x: int| 0 <= x < m0 && #[trigger] bf[x] == r;
            } else {
                let u = (r - base) as u64;
                assert(bit(msk, u));
                let x = choose|x: int| m0 <= x < m && #[trigger] bf[x] == base + u;
            }
        }
        if m > m0 {
            assert(base + (m - 1 - m0) <= bf[m - 1] < base + wl);
        }
    }
    m
}

/// The rows of `[i0, i1)` in the window, ascending, into `bi[0..m)`.
fn win_rows(c: &Cols, i0: usize, i1: usize, bi: &mut Vec<usize>, tzt: &[u8; 64], Ghost(sv): Ghost<StoresView>) -> (m: usize)
    requires cols_ok(*c, sv), i0 <= i1 <= c.no, i1 - i0 <= old(bi)@.len(), tzt@.len() == 64,
    ensures
        final(bi)@.len() == old(bi)@.len(), m <= i1 - i0,
        win_list(sv, c.dlo as int, c.dhi as int, final(bi)@, m as int, i0 as int, i1 as int),
    no_unwind
{
    let ghost (dlo, dhi) = (c.dlo as int, c.dhi as int);
    let mut m: usize = 0;
    let mut base = i0;
    while base < i1
        invariant
            cols_ok(*c, sv), i0 <= base <= i1 <= c.no, i1 - i0 <= bi@.len(), tzt@.len() == 64, dlo == c.dlo, dhi == c.dhi,
            bi@.len() == old(bi)@.len(), m <= base - i0,
            win_list(sv, dlo, dhi, bi@, m as int, i0 as int, base as int),
        decreases i1 - base,
    {
        let wl = if i1 - base >= 64 { 64 } else { i1 - base };
        let msk = word_mask(c, base, wl, Ghost(sv));
        m = extract(msk, base, wl, bi, m, tzt, Ghost(sv), Ghost(dlo), Ghost(dhi), Ghost(i0 as int));
        base = base + wl;
    }
    m
}

// ------------------------------------------------------------------------------------------------ 2. keys, customers

/// The key of every listed row, and its customer row (`-1` when outside `[0, nc)`).
#[inline(always)]
fn gather_orders(c: &Cols, m: usize, bi: &Vec<usize>, bk: &mut Vec<i64>, bc: &mut Vec<i64>, Ghost(sv): Ghost<StoresView>)
    requires
        cols_ok(*c, sv), m <= bi@.len(), m <= old(bk)@.len(), m <= old(bc)@.len(), c.nc < 0x8000_0000,
        forall|x: int| 0 <= x < m ==> #[trigger] bi@[x] < c.no,
    ensures
        final(bk)@.len() == old(bk)@.len(), final(bc)@.len() == old(bc)@.len(),
        forall|x: int| 0 <= x < m ==> #[trigger] final(bk)@[x] as int == okey(sv, bi@[x] as int),
        forall|x: int| 0 <= x < m ==> (#[trigger] final(bc)@[x] >= 0) == (0 <= crow(sv, c.cbase as int, bi@[x] as int) < n_c(sv)),
        forall|x: int| 0 <= x < m && #[trigger] final(bc)@[x] >= 0 ==> final(bc)@[x] as int == crow(sv, c.cbase as int, bi@[x] as int),
    no_unwind
{
    let mut x: usize = 0;
    while x < m
        invariant
            cols_ok(*c, sv), m <= bi@.len(), m <= bk@.len(), m <= bc@.len(), c.nc < 0x8000_0000, x <= m,
            forall|y: int| 0 <= y < m ==> #[trigger] bi@[y] < c.no,
            bk@.len() == old(bk)@.len(), bc@.len() == old(bc)@.len(),
            forall|y: int| 0 <= y < x ==> #[trigger] bk@[y] as int == okey(sv, bi@[y] as int),
            forall|y: int| 0 <= y < x ==> (#[trigger] bc@[y] >= 0) == (0 <= crow(sv, c.cbase as int, bi@[y] as int) < n_c(sv)),
            forall|y: int| 0 <= y < x && #[trigger] bc@[y] >= 0 ==> bc@[y] as int == crow(sv, c.cbase as int, bi@[y] as int),
        decreases m - x,
    {
        let r = bi[x];
        let k = c.ok[r];
        let d: i128 = c.oc[r] as i128 - c.cbase as i128;
        let cr: i64 = if d >= 0 && d < c.nc as i128 { d as i64 } else { -1 };
        proof {
            assert(ok(sv)[r as int] == k && oc(sv)[r as int] == c.oc@[r as int]);
        }
        bk[x] = k;
        bc[x] = cr;
        x = x + 1;
    }
}

// ------------------------------------------------------------------------------------------------ 3. runs

/// The run of every listed order with a customer, searched from the hint `pp`; `None` when a found row does not
/// start a run (keys out of order).
#[inline(always)]
fn find_runs(c: &Cols, m: usize, bk: &Vec<i64>, bc: &Vec<i64>, bs: &mut Vec<usize>, be: &mut Vec<usize>, pp: usize,
    hi: usize, Ghost(sv): Ghost<StoresView>) -> (r: Option<usize>)
    requires
        cols_ok(*c, sv), m <= bk@.len(), m <= bc@.len(), m <= old(bs)@.len(), m <= old(be)@.len(), pp <= hi <= c.nl,
    ensures
        final(bs)@.len() == old(bs)@.len(), final(be)@.len() == old(be)@.len(),
        r matches Some(p) ==> p <= hi
            && (forall|x: int| 0 <= x < m ==> #[trigger] final(bs)@[x] <= final(be)@[x] <= c.nl)
            && (forall|x: int| 0 <= x < m && #[trigger] bc@[x] >= 0 ==> run_ok(sv, bk@[x] as int, final(bs)@[x] as int, final(be)@[x] as int)),
    no_unwind
{
    let mut p = pp;
    let mut x: usize = 0;
    while x < m
        invariant
            cols_ok(*c, sv), m <= bk@.len(), m <= bc@.len(), m <= bs@.len(), m <= be@.len(), p <= hi <= c.nl, x <= m,
            bs@.len() == old(bs)@.len(), be@.len() == old(be)@.len(),
            forall|y: int| 0 <= y < x ==> #[trigger] bs@[y] <= be@[y] <= c.nl,
            forall|y: int| 0 <= y < x && #[trigger] bc@[y] >= 0 ==> run_ok(sv, bk@[y] as int, bs@[y] as int, be@[y] as int),
        decreases m - x,
    {
        if bc[x] >= 0 {
            let k = bk[x];
            match run_start(c, k, p, hi, Ghost(sv)) {
                Some(s) => {
                    let e = run_end(c, k, s, Ghost(sv));
                    bs[x] = s;
                    be[x] = e;
                    p = if e < hi { e } else { hi };
                },
                None => {
                    return None;
                },
            }
        } else {
            bs[x] = 0;
            be[x] = 0;
        }
        x = x + 1;
    }
    Some(p)
}

// ------------------------------------------------------------------------------------------------ 5. touch

/// One load from each cache line the run sums read first (offsets, flag bytes, prices, discounts), folded into a
/// value the caller keeps: independent loads, so their misses overlap.
#[inline(always)]
fn touch(c: &Cols, m: usize, bs: &Vec<usize>, be: &Vec<usize>, Ghost(sv): Ghost<StoresView>) -> (sink: i64)
    requires cols_ok(*c, sv), m <= bs@.len(), m <= be@.len(), forall|x: int| 0 <= x < m ==> #[trigger] bs@[x] <= be@[x] <= c.nl,
    no_unwind
{
    let ghost nl = c.nl;
    let rfo = c.rfo;
    let rfb = c.rfb;
    let lp = c.lp;
    let ld = c.ld;
    proof {
        assert(rfo@.len() == nl + 1 && lp@.len() == nl && ld@.len() == nl);
        assert(forall|i: int| 0 <= i < nl ==> 0 <= #[trigger] rfo@[i] <= rfo@[i + 1] <= rfb@.len());
    }
    let mut sink: i64 = 0;
    let mut x: usize = 0;
    while x < m
        invariant
            m <= bs@.len(), m <= be@.len(), x <= m, rfo@.len() == nl + 1, lp@.len() == nl, ld@.len() == nl,
            forall|y: int| 0 <= y < m ==> #[trigger] bs@[y] <= be@[y] <= nl,
        decreases m - x,
    {
        let s = bs[x];
        let e = be[x];
        if s < e {
            sink = sink ^ rfo[s] ^ rfo[e] ^ (#[verifier::truncate] (lp[s] as i64)) ^ (#[verifier::truncate] (lp[e - 1] as i64))
                ^ (#[verifier::truncate] (ld[s] as i64)) ^ (#[verifier::truncate] (ld[e - 1] as i64));
        }
        x = x + 1;
    }
    let mut x: usize = 0;
    while x < m
        invariant
            m <= bs@.len(), m <= be@.len(), x <= m, rfo@.len() == nl + 1,
            forall|i: int| 0 <= i < nl ==> 0 <= #[trigger] rfo@[i] <= rfo@[i + 1] <= rfb@.len(),
            forall|y: int| 0 <= y < m ==> #[trigger] bs@[y] <= be@[y] <= nl,
        decreases m - x,
    {
        let s = bs[x];
        if s < be[x] {
            let o0 = rfo[s];
            let o1 = rfo[s + 1];
            if o1 - o0 == 1 {
                sink = sink ^ (rfb[o0 as usize] as i64);
            }
        }
        x = x + 1;
    }
    sink
}

// ------------------------------------------------------------------------------------------------ 6. run sums, output

/// The `R` test of lineitem row `i`: its flag is exactly the byte `R`.
#[inline(always)]
pub fn is_r_exec(c: &Cols, i: usize, Ghost(sv): Ghost<StoresView>) -> (b: bool)
    requires cols_ok(*c, sv), i < c.nl,
    ensures b == is_r(sv, i as int),
    no_unwind
{
    let o0 = c.rfo[i];
    let o1 = c.rfo[i + 1];
    proof {
        assert(0 <= rf_col(sv).offsets[i as int] <= rf_col(sv).offsets[i + 1] <= rf_col(sv).bytes.len());
    }
    if o1 - o0 == 1 {
        let byte = c.rfb[o0 as usize];
        proof {
            let t = text_at(rf_col(sv), i as int);
            assert(t.len() == 1 && t[0] == byte);
            if byte == 82u8 { assert(t =~= seq![82u8]); }
        }
        byte == 82u8
    } else {
        proof {
            assert(text_at(rf_col(sv), i as int).len() != 1);
        }
        false
    }
}

/// The sum and count of the `R` rows of the run `[s, e)` of key `k`; `None` when the run is longer than `MAXRUN`, an
/// `R` row has a price outside `[0, 10^15)` or a discount outside `[0, 100]`, or the sum reaches `CAP`.
#[inline(always)]
fn run_value(c: &Cols, s: usize, e: usize, Ghost(k): Ghost<int>, Ghost(sv): Ghost<StoresView>) -> (r: Option<(i64, u64)>)
    requires cols_ok(*c, sv), s <= e <= c.nl, forall|y: int| s <= y < e ==> #[trigger] lk(sv)[y] as int == k,
    ensures
        r matches Some((sum, cn)) ==> {
            &&& sum as int == ksum(sv, k, s as int, e as int)
            &&& cn as int == kcnt(sv, k, s as int, e as int)
            &&& kabs(sv, k, s as int, e as int) == ksum(sv, k, s as int, e as int)
            &&& 0 <= sum < CAP
        },
    no_unwind
{
    if e - s > MAXRUN {
        return None;
    }
    let mut sum: i64 = 0;
    let mut cn: u64 = 0;
    let mut bad: u64 = 0;
    let mut i = s;
    while i < e
        invariant
            cols_ok(*c, sv), s <= i <= e <= c.nl, e - s <= MAXRUN, forall|y: int| s <= y < e ==> #[trigger] lk(sv)[y] as int == k,
            bad <= i - s, cn <= i - s,
            0 <= sum <= (i - s) * 100_000_000_000_000_000,
            bad == 0 ==> sum as int == ksum(sv, k, s as int, i as int) && cn as int == kcnt(sv, k, s as int, i as int)
                && kabs(sv, k, s as int, i as int) == ksum(sv, k, s as int, i as int),
        decreases e - i,
    {
        // no branch on the flag or the bounds: the `R` rows are about half of the rows, at random
        let isr = is_r_exec(c, i, Ghost(sv));
        let p = c.lp[i];
        let d = c.ld[i];
        let okv = p >= 0 && p < 1_000_000_000_000_000 && d >= 0 && d <= 100;
        let v: i64 = if okv {
            let pr = p as i64;
            let dc = 100 - d as i64;
            proof {
                assert(0 <= pr * dc <= 100_000_000_000_000_000) by (nonlinear_arith)
                    requires 0 <= pr < 1_000_000_000_000_000, 0 <= dc <= 100;
            }
            pr * dc
        } else { 0 };
        let h: u64 = if isr { 1 } else { 0 };
        let nv: u64 = if okv { 0 } else { 1 };
        proof {
            if okv {
                assert(0 <= v <= 100_000_000_000_000_000) by (nonlinear_arith)
                    requires v == (p as i64) * (100 - d as i64), 0 <= p < 1_000_000_000_000_000, 0 <= d <= 100;
                assert(lval(sv, i as int) == v as int) by (nonlinear_arith)
                    requires lval(sv, i as int) == p * (100 - d), v == (p as i64) * (100 - d as i64),
                        0 <= p < 1_000_000_000_000_000, 0 <= d <= 100;
            }
            assert(lhit(sv, k, i as int) == isr);
            assert((i + 1 - s) * 100_000_000_000_000_000 == (i - s) * 100_000_000_000_000_000 + 100_000_000_000_000_000)
                by (nonlinear_arith);
            assert((i + 1 - s) * 100_000_000_000_000_000 <= 64 * 100_000_000_000_000_000) by (nonlinear_arith)
                requires i + 1 - s <= 64;
        }
        let hv: i64 = (h as i64) * v;
        proof {
            assert(hv == if isr { v } else { 0 }) by (nonlinear_arith) requires hv == (h as i64) * v, h == if isr { 1u64 } else { 0u64 };
        }
        bad = bad + h * nv;
        sum = sum + hv;
        cn = cn + h;
        proof {
            assert(h * nv <= 1) by (nonlinear_arith) requires h <= 1, nv <= 1;
            assert(h * nv == 0 ==> (isr ==> okv)) by (nonlinear_arith) requires h == if isr { 1u64 } else { 0u64 }, nv == if okv { 0u64 } else { 1u64 };
        }
        i = i + 1;
    }
    if bad != 0 || sum >= CAP {
        return None;
    }
    Some((sum, cn))
}

/// Appends the hitting orders of the batch to their buckets (see the module header); `false` when a run sum fails or
/// a bucket is full.
#[verifier::loop_isolation(false)]
fn emit_batch(c: &Cols, m: usize, bi: &Vec<usize>, bk: &Vec<i64>, bc: &Vec<i64>, bs: &Vec<usize>, be: &Vec<usize>,
    rv: &mut Vec<i64>, cnt: &mut Vec<usize>, nb: usize, rcap: usize,
    Ghost(lists0): Ghost<Seq<Seq<int>>>, Ghost(sv): Ghost<StoresView>, Ghost(olo): Ghost<int>, Ghost(i0): Ghost<int>,
    Ghost(i1): Ghost<int>) -> (r: (bool, Ghost<Seq<Seq<int>>>))
    requires
        cols_ok(*c, sv), c.nc < 0x8000_0000, c.nc <= nb * CPB, olo <= i0 <= i1 <= c.no, nb * rcap <= usize::MAX,
        m <= bk@.len(), m <= bc@.len(), m <= bs@.len(), m <= be@.len(),
        win_list(sv, c.dlo as int, c.dhi as int, bi@, m as int, i0, i1),
        forall|x: int| 0 <= x < m ==> #[trigger] bk@[x] as int == okey(sv, bi@[x] as int),
        forall|x: int| 0 <= x < m ==> (#[trigger] bc@[x] >= 0) == (0 <= crow(sv, c.cbase as int, bi@[x] as int) < n_c(sv)),
        forall|x: int| 0 <= x < m && #[trigger] bc@[x] >= 0 ==> bc@[x] as int == crow(sv, c.cbase as int, bi@[x] as int),
        forall|x: int| 0 <= x < m && #[trigger] bc@[x] >= 0 ==> run_ok(sv, bk@[x] as int, bs@[x] as int, be@[x] as int),
        buckets_ok(*c, sv, old(rv)@, old(cnt)@, lists0, nb as int, rcap as int, olo, i0),
        abs_ok(*c, sv, olo, i0),
    ensures
        r.0 ==> buckets_ok(*c, sv, final(rv)@, final(cnt)@, r.1@, nb as int, rcap as int, olo, i1),
        r.0 ==> abs_ok(*c, sv, olo, i1),
        final(rv)@.len() == old(rv)@.len(), final(cnt)@.len() == old(cnt)@.len(),
    no_unwind
{
    let ghost (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    let ghost mut lists = lists0;
    let ghost mut done: int = i0;
    let mut x: usize = 0;
    while x < m
        invariant
            x <= m, i0 <= done <= i1,
            x < m ==> done <= bi@[x as int], nb * rcap <= usize::MAX,
            x > 0 ==> done == bi@[x - 1] + 1,
            rv@.len() == old(rv)@.len(), cnt@.len() == old(cnt)@.len(),
            buckets_ok(*c, sv, rv@, cnt@, lists, nb as int, rcap as int, olo, done),
            abs_ok(*c, sv, olo, done),
        decreases m - x,
    {
        let j = bi[x];
        // the rows before j since the last listed row are not in the window
        proof {
            assert forall|r: int| done <= r < j implies !win(sv, dlo, dhi, r) by {
                if win(sv, dlo, dhi, r) {
                    let y = choose|y: int| 0 <= y < m && #[trigger] bi@[y] == r;
                    if y < x { if x > 0 { assert(bi@[y] <= bi@[x - 1]); } }
                    if y > x { assert(bi@[x as int] < bi@[y]); }
                }
            }
            assert(lk_sorted(sv) ==> forall|r: int| done <= r < j ==> !#[trigger] ohit(sv, dlo, dhi, cbase, r));
            lemma_extend(*c, sv, rv@, cnt@, lists, nb as int, rcap as int, olo, done, j as int);
            done = j as int;
        }
        let cr = bc[x];
        if cr >= 0 {
            let k = bk[x];
            let s = bs[x];
            let e = be[x];
            proof {
                assert(run_ok(sv, k as int, s as int, e as int));
                assert(qualifies(sv, dlo, dhi, cbase, j as int));
            }
            match run_value(c, s, e, Ghost(k as int), Ghost(sv)) {
                None => { return (false, Ghost(lists)); },
                Some((sum, cn)) => {
                    proof {
                        lemma_run_part(sv, k as int, s as int, e as int);
                        if lk_sorted(sv) {
                            lemma_run_all(sv, k as int, s as int, e as int);
                        }
                    }
                    if cn > 0 {
                        let cru = cr as usize;
                        let b = cru / CPB;
                        proof { lemma_bucket_bound(cru as int, c.nc as int, nb as int); }
                        let f = cnt[b];
                        if f >= rcap {
                            return (false, Ghost(lists));
                        }
                        proof {
                            lemma_pos_bound(b as int, f as int, nb as int, rcap as int);
                        }
                        if sum >= PCAP - 1 {
                            return (false, Ghost(lists));
                        }
                        let pos = b * rcap + f;
                        let x = cru % CPB;
                        let v: i64 = (sum + 1) * 131072 + x as i64;
                        proof {
                            assert(ohit(sv, dlo, dhi, cbase, j as int));
                            assert(obk(sv, cbase, j as int) == b);
                            lemma_pack(cru as int, (sum + 1) as int, v as int);
                            lemma_push(*c, sv, rv@, cnt@, lists, nb as int, rcap as int, olo, j as int, b as int, v);
                        }
                        rv[pos] = v;
                        cnt[b] = f + 1;
                        proof {
                            lists = lists.update(b as int, lists[b as int].push(j as int));
                        }
                    } else {
                        proof {
                            assert(lk_sorted(sv) ==> !ohit(sv, dlo, dhi, cbase, j as int));
                            lemma_extend(*c, sv, rv@, cnt@, lists, nb as int, rcap as int, olo, j as int, j + 1);
                        }
                    }
                    proof {
                        if lk_sorted(sv) {
                            assert(kabs(sv, okey(sv, j as int), 0, n_l(sv)) == ksum(sv, okey(sv, j as int), 0, n_l(sv)));
                        }
                    }
                },
            }
        } else {
            proof {
                assert(!qualifies(sv, dlo, dhi, cbase, j as int));
                lemma_extend(*c, sv, rv@, cnt@, lists, nb as int, rcap as int, olo, j as int, j + 1);
            }
        }
        proof {
            done = j + 1;
            assert(abs_ok(*c, sv, olo, done)) by {
                if lk_sorted(sv) {
                    assert forall|r: int| olo <= r < done && qualifies(sv, dlo, dhi, cbase, r) implies
                        #[trigger] kabs(sv, okey(sv, r), 0, n_l(sv)) == ksum(sv, okey(sv, r), 0, n_l(sv)) by {
                        if r == j {} else {
                            assert(abs_ok(*c, sv, olo, j as int));
                        }
                    }
                }
            }
        }
        x = x + 1;
    }
    proof {
        assert forall|r: int| done <= r < i1 implies !win(sv, dlo, dhi, r) by {
            if win(sv, dlo, dhi, r) {
                let y = choose|y: int| 0 <= y < m && #[trigger] bi@[y] == r;
                if m > 0 { assert(bi@[y] <= bi@[m - 1]); }
            }
        }
        assert(lk_sorted(sv) ==> forall|r: int| done <= r < i1 ==> !#[trigger] ohit(sv, dlo, dhi, cbase, r));
        lemma_extend(*c, sv, rv@, cnt@, lists, nb as int, rcap as int, olo, done, i1);
        assert(abs_ok(*c, sv, olo, i1)) by {
            if lk_sorted(sv) {
                assert forall|r: int| olo <= r < i1 && qualifies(sv, dlo, dhi, cbase, r) implies
                    #[trigger] kabs(sv, okey(sv, r), 0, n_l(sv)) == ksum(sv, okey(sv, r), 0, n_l(sv)) by {
                    if r >= done { assert(!win(sv, dlo, dhi, r)); }
                }
            }
        }
    }
    (true, Ghost(lists))
}

// ------------------------------------------------------------------------------------------------ the task

pub struct STask {
    pub c: Cols,
    pub lo: usize,
    pub hi: usize,
    pub olo: usize,
    pub ohi: usize,
    pub nb: usize,
    pub rcap: usize,
    pub rv: Vec<i64>,
    pub cnt: Vec<usize>,
    pub bi: Vec<usize>,
    pub bk: Vec<i64>,
    pub bc: Vec<i64>,
    pub bs: Vec<usize>,
    pub be: Vec<usize>,
    pub sv: Ghost<StoresView>,
}

pub struct SOut {
    pub ok: bool,
    pub nb: usize,
    pub rcap: usize,
    pub rv: Vec<i64>,
    pub cnt: Vec<usize>,
    pub lists: Ghost<Seq<Seq<int>>>,
    pub sink: i64,
}

/// The first pair a task checks: row `lo + 1` (or the end of the table).
pub open spec fn pair_lo(nl: int, lo: int) -> int { if lo + 1 < nl { lo + 1 } else { nl } }

/// The end of the pairs a task checks: the row after `hi`, or the end of the table.
pub open spec fn pair_hi(nl: int, hi: int) -> int { if hi + 1 < nl { hi + 1 } else { nl } }

/// The task's input: ranges inside the tables, empty buckets covering the customers, batch buffers.
pub open spec fn scan_pre(t: STask) -> bool {
    &&& cols_ok(t.c, t.sv@)
    &&& t.lo <= t.hi <= t.c.nl && t.olo <= t.ohi <= t.c.no
    &&& t.c.nc < 0x8000_0000 && t.c.nc <= t.nb * CPB && t.nb * t.rcap <= usize::MAX
    &&& t.rv@.len() == t.nb * t.rcap && t.cnt@.len() == t.nb
    &&& forall|b: int| 0 <= b < t.nb ==> #[trigger] t.cnt@[b] == 0
    &&& t.bi@.len() == BATCH && t.bk@.len() == BATCH && t.bc@.len() == BATCH && t.bs@.len() == BATCH && t.be@.len() == BATCH
}

/// The task's result: its buffers, and when it succeeds its pairs in order, its buckets and the absolute masses of
/// its orders.
pub open spec fn scan_post(c: Cols, sv: StoresView, lo: int, hi: int, olo: int, ohi: int, nb: int, rcap: int, out: SOut) -> bool {
    &&& out.nb == nb && out.rcap == rcap && nb * rcap <= usize::MAX
    &&& out.rv@.len() == nb * rcap && out.cnt@.len() == nb && out.lists@.len() == nb
    &&& out.ok ==> {
        &&& pairs_ok(lk(sv), pair_lo(n_l(sv), lo), pair_hi(n_l(sv), hi))
        &&& buckets_ok(c, sv, out.rv@, out.cnt@, out.lists@, nb, rcap, olo, ohi)
        &&& abs_ok(c, sv, olo, ohi)
    }
}

impl WorkerTask for STask {
    type Output = SOut;

    open spec fn pre(&self) -> bool { scan_pre(*self) }

    open spec fn post(&self, out: SOut) -> bool {
        scan_post(self.c, self.sv@, self.lo as int, self.hi as int, self.olo as int, self.ohi as int, self.nb as int,
            self.rcap as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    #[verifier::loop_isolation(false)]
    fn run(self) -> (out: SOut) {
        let STask { c, lo, hi, olo, ohi, nb, rcap, rv, cnt, bi, bk, bc, bs, be, sv } = self;
        let ghost sv = sv@;
        let mut rv = rv;
        let mut cnt = cnt;
        let mut bi = bi;
        let mut bk = bk;
        let mut bc = bc;
        let mut bs = bs;
        let mut be = be;
        let tzt = tz_table_array();
        let nl = c.nl;
        let ghost mut lists: Seq<Seq<int>> = Seq::new(nb as nat, |b: int| Seq::<int>::empty());
        let mut sink: i64 = 0;
        let mut pp = lo;
        let chk0 = if nl > 0 && lo < nl - 1 { lo + 1 } else { nl };
        let cend = if nl > 0 && hi < nl - 1 { hi + 1 } else { nl };
        let mut chk = chk0;
        proof {
            assert(buckets_ok(c, sv, rv@, cnt@, lists, nb as int, rcap as int, olo as int, olo as int)) by {
                assert forall|b: int| 0 <= b < nb implies #[trigger] bucket_ok(c, sv, rv@, cnt@, lists, rcap as int,
                    olo as int, olo as int, b) by {
                    assert(cnt@[b] == 0);
                    assert(lists[b] =~= Seq::<int>::empty());
                }
            }
        }
        let mut i0 = olo;
        while i0 < ohi
            invariant
                cols_ok(c, sv), lo <= hi <= nl, nl == c.nl, olo <= i0 <= ohi <= c.no, c.nc < 0x8000_0000, c.nc <= nb * CPB,
                nb * rcap <= usize::MAX,
                pp <= hi, chk0 == pair_lo(nl as int, lo as int), cend == pair_hi(nl as int, hi as int), chk0 <= chk <= cend,
                pairs_ok(lk(sv), chk0 as int, chk as int),
                bi@.len() == BATCH, bk@.len() == BATCH, bc@.len() == BATCH, bs@.len() == BATCH, be@.len() == BATCH,
                tzt@.len() == 64,
                rv@.len() == nb * rcap, cnt@.len() == nb,
                buckets_ok(c, sv, rv@, cnt@, lists, nb as int, rcap as int, olo as int, i0 as int),
                abs_ok(c, sv, olo as int, i0 as int),
            decreases ohi - i0,
        {
            let i1 = if ohi - i0 > BATCH { i0 + BATCH } else { ohi };
            let m = win_rows(&c, i0, i1, &mut bi, &tzt, Ghost(sv));
            gather_orders(&c, m, &bi, &mut bk, &mut bc, Ghost(sv));
            let p2 = match find_runs(&c, m, &bk, &bc, &mut bs, &mut be, pp, hi, Ghost(sv)) {
                Some(p) => p,
                None => {
                    return SOut { ok: false, nb, rcap, rv, cnt, lists: Ghost(lists), sink };
                },
            };
            pp = p2;
            let pe = if pp < cend { pp } else { cend };
            if chk < pe {
                if !check_pairs(&c, chk, pe, Ghost(sv)) {
                    return SOut { ok: false, nb, rcap, rv, cnt, lists: Ghost(lists), sink };
                }
                proof { lemma_pairs_join(lk(sv), chk0 as int, chk as int, pe as int); }
                chk = pe;
            }
            sink = sink ^ touch(&c, m, &bs, &be, Ghost(sv));
            let (okb, l2) = emit_batch(&c, m, &bi, &bk, &bc, &bs, &be, &mut rv, &mut cnt, nb, rcap, Ghost(lists),
                Ghost(sv), Ghost(olo as int), Ghost(i0 as int), Ghost(i1 as int));
            if !okb {
                return SOut { ok: false, nb, rcap, rv, cnt, lists: Ghost(lists), sink };
            }
            proof { lists = l2@; }
            i0 = i1;
        }
        if chk < cend {
            if !check_pairs(&c, chk, cend, Ghost(sv)) {
                return SOut { ok: false, nb, rcap, rv, cnt, lists: Ghost(lists), sink };
            }
            proof { lemma_pairs_join(lk(sv), chk0 as int, chk as int, cend as int); }
        }
        SOut { ok: true, nb, rcap, rv, cnt, lists: Ghost(lists), sink }
    }
}

} // verus!
