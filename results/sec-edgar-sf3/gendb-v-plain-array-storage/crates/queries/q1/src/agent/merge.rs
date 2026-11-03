//! Combining the range scans of consecutive row ranges `[b[t], b[t + 1])` into the groups of the whole table:
//! local groups of each range are matched by key to global groups (`maps[t][lg]`), counts and sums add up
//! (`lemma_split`). Distinct adsh counts come from the ranges' bit sets: global group `g` has a value of `sub` row
//! `id` exactly when some range has a local group mapped to `g` with bit set at `id` (`in_g`); counting these ids
//! counts the group's adsh values because distinct `sub` rows hold distinct values (primary key of `sub`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::cols::*;
use crate::agent::spec::*;
use crate::agent::dict::*;
use crate::agent::kernel::*;
use crate::agent::common::bytes::*;
use crate::agent::common::bits::*;

verus! {

/// Result of one range scan.
pub struct ScanOut {
    pub status: u8,
    pub ng: usize,
    pub acc: Acc,
}

/// The scan of rows `[lo, hi)` as a worker task.
pub struct ScanTask {
    pub c: Cols,
    pub dict: Arc<Dict>,
    pub t: Ghost<Seq<Row>>,
    pub lo: usize,
    pub hi: usize,
    pub acc: Acc,
    pub cache: Vec<u64>,
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& cols_wf(self.c)
        &&& corr(self.c, self.t@)
        &&& dict_wf(self.c, *self.dict)
        &&& self.lo <= self.hi <= self.c.n
        &&& fresh(self.c, self.acc)
        &&& cache_ok(self.c, self.cache@)
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        out.status == ST_OK ==> out_ok(self.c, self.t@, self.lo as int, self.hi as int, out.ng as int, out.acc)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let d: &Dict = &*self.dict;
        let (status, ng, acc) = scan_range(&self.c, d, self.t, self.lo, self.hi, self.acc, self.cache);
        ScanOut { status, ng, acc }
    }
}

/// The groups of the whole table: first rows, counts, line sums and distinct adsh counts.
pub struct Groups {
    pub rep: Vec<usize>,
    pub cnt: Vec<u64>,
    pub sum: Vec<i128>,
    pub dcnt: Vec<u64>,
}

/// Global groups over rows `[0, hi)`: qualifying first rows, pairwise different keys, covering every qualifying row,
/// with the count and sum of each group.
pub open spec fn merged_ok(t: Seq<Row>, n: int, hi: int, rep: Seq<usize>, cnt: Seq<u64>, sum: Seq<i128>) -> bool {
    &&& cnt.len() == rep.len() && sum.len() == rep.len() && rep.len() <= 64
    &&& forall|g: int| 0 <= g < rep.len() ==> #[trigger] rep[g] < n && qual(t[rep[g] as int])
    &&& forall|g1: int, g2: int| 0 <= g1 < rep.len() && 0 <= g2 < rep.len() && g1 != g2
        ==> #[trigger] gkey(t, rep, g1) != #[trigger] gkey(t, rep, g2)
    &&& forall|j: int| 0 <= j < hi && qual(#[trigger] t[j]) ==> exists|g: int| 0 <= g < rep.len() && key_of(t[j]) == gkey(t, rep, g)
    &&& forall|g: int| 0 <= g < rep.len() ==> #[trigger] cnt[g] == cnt_r(t, gkey(t, rep, g), 0, hi)
    &&& forall|g: int| 0 <= g < rep.len() ==> #[trigger] sum[g] == sum_r(t, gkey(t, rep, g), 0, hi)
}

/// Task boundaries: `b[0] = 0`, nondecreasing, `b[nt] = n`, and each task's scan result.
pub open spec fn tasks_ok(c: Cols, t: Seq<Row>, b: Seq<usize>, outs: Seq<ScanOut>) -> bool {
    &&& b.len() == outs.len() + 1
    &&& b[0] == 0
    &&& b[outs.len() as int] == c.n
    &&& forall|k: int| 0 <= k < outs.len() ==> #[trigger] b[k] <= b[k + 1]
    &&& forall|k: int| 0 <= k < outs.len() ==> (#[trigger] outs[k]).status == ST_OK
        && out_ok(c, t, b[k] as int, b[k + 1] as int, outs[k].ng as int, outs[k].acc)
}

/// The map of task `k`'s local groups to global groups (keys agree).
pub open spec fn map_ok(t: Seq<Row>, rep: Seq<usize>, out: ScanOut, map: Seq<usize>) -> bool {
    &&& map.len() == GCAP
    &&& forall|lg: int| 0 <= lg < out.ng ==> (#[trigger] map[lg]) < rep.len() && map[lg] < 64
        && gkey(t, rep, map[lg] as int) == gkey(t, out.acc.rep@, lg)
}

/// Whether the keys (stmt, rfile) of rows `i` and `j` are equal (both qualifying).
fn same_key(c: &Cols, Ghost(t): Ghost<Seq<Row>>, i: usize, j: usize) -> (r: bool)
    requires cols_wf(*c), corr(*c, t), i < c.n, j < c.n, qual(t[i as int]), qual(t[j as int]),
    ensures r == (key_of(t[i as int]) == key_of(t[j as int])),
{
    proof {
        lemma_key_eq(*c, t, i as int, j as int);
        assert(0 <= c.stmt_off@[i as int] <= c.stmt_off@[i + 1] <= c.stmt@.len());
        assert(0 <= c.stmt_off@[j as int] <= c.stmt_off@[j + 1] <= c.stmt@.len());
        assert(0 <= c.rfile_off@[i as int] <= c.rfile_off@[i + 1] <= c.rfile@.len());
        assert(0 <= c.rfile_off@[j as int] <= c.rfile_off@[j + 1] <= c.rfile@.len());
    }
    let s0 = c.stmt_off[i] as usize;
    let s1 = c.stmt_off[i + 1] as usize;
    let t0 = c.stmt_off[j] as usize;
    let t1 = c.stmt_off[j + 1] as usize;
    let r0 = c.rfile_off[i] as usize;
    let r1 = c.rfile_off[i + 1] as usize;
    let u0 = c.rfile_off[j] as usize;
    let u1 = c.rfile_off[j + 1] as usize;
    eq_ranges(c.stmt, c.stmt_len, s0, s1, c.stmt, c.stmt_len, t0, t1)
        && eq_ranges(c.rfile, c.rfile_len, r0, r1, c.rfile, c.rfile_len, u0, u1)
}

/// The global group with row `row`'s key, if any.
pub fn find_global(c: &Cols, Ghost(t): Ghost<Seq<Row>>, Ghost(hi): Ghost<int>, rep: &Vec<usize>, row: usize) -> (r: Option<usize>)
    requires
        cols_wf(*c), corr(*c, t), hi <= c.n, row < c.n, qual(t[row as int]),
        forall|g: int| 0 <= g < rep@.len() ==> #[trigger] rep@[g] < hi && qual(t[rep@[g] as int]),
    ensures
        r matches Some(g) ==> g < rep@.len() && gkey(t, rep@, g as int) == key_of(t[row as int]),
        r is None ==> forall|g: int| 0 <= g < rep@.len() ==> #[trigger] gkey(t, rep@, g) != key_of(t[row as int]),
{
    let mut g: usize = 0;
    while g < rep.len()
        invariant
            cols_wf(*c), corr(*c, t), hi <= c.n, row < c.n, qual(t[row as int]), g <= rep@.len(),
            forall|g2: int| 0 <= g2 < rep@.len() ==> #[trigger] rep@[g2] < hi && qual(t[rep@[g2] as int]),
            forall|g2: int| 0 <= g2 < g ==> #[trigger] gkey(t, rep@, g2) != key_of(t[row as int]),
        decreases rep@.len() - g,
    {
        proof { assert(rep@[g as int] < hi); }
        if same_key(c, Ghost(t), rep[g], row) {
            return Some(g);
        }
        g = g + 1;
    }
    None
}

/// Global group `g` gets a range's rows from a local group mapped to it so far.
pub open spec fn mapped(map: Seq<usize>, lg: int, g: int) -> bool {
    exists|lg2: int| 0 <= lg2 < lg && #[trigger] map[lg2] == g
}

/// Step 1 for task range `[lo, hi)`: maps each local group to the global group with its key, adding missing global
/// groups (with no rows before `lo`). `None` when there would be more than 64 global groups.
fn map_task(c: &Cols, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>, out: &ScanOut,
    rep: &mut Vec<usize>, cnt: &mut Vec<u64>, sum: &mut Vec<i128>) -> (r: Option<Vec<usize>>)
    requires
        cols_wf(*c), corr(*c, t), 0 <= lo <= hi <= c.n,
        out_ok(*c, t, lo, hi, out.ng as int, out.acc),
        merged_ok(t, c.n as int, lo, old(rep)@, old(cnt)@, old(sum)@),
    ensures
        r matches Some(map) ==> {
            &&& merged_ok(t, c.n as int, lo, final(rep)@, final(cnt)@, final(sum)@)
            &&& map_ok(t, final(rep)@, *out, map@)
            &&& final(rep)@.len() >= old(rep)@.len()
            &&& final(rep)@.subrange(0, old(rep)@.len() as int) == old(rep)@
        },
{
    let ghost rep0 = rep@;
    let mut map: Vec<usize> = vec![0usize; GCAP];
    let mut lg: usize = 0;
    proof { assert(groups_ok(t, lo, hi, hi, out.ng as int, out.acc.rep@)); }
    while lg < out.ng
        invariant
            cols_wf(*c), corr(*c, t), 0 <= lo <= hi <= c.n,
            out_ok(*c, t, lo, hi, out.ng as int, out.acc),
            merged_ok(t, c.n as int, lo, rep@, cnt@, sum@),
            lg <= out.ng, out.ng <= GCAP, map@.len() == GCAP,
            rep@.len() >= rep0.len(), rep@.subrange(0, rep0.len() as int) == rep0,
            forall|lg2: int| 0 <= lg2 < lg ==> (#[trigger] map@[lg2]) < rep@.len() && map@[lg2] < 64
                && gkey(t, rep@, map@[lg2] as int) == gkey(t, out.acc.rep@, lg2),
        decreases out.ng - lg,
    {
        let row = out.acc.rep[lg];
        proof {
            assert(lo <= row < hi);
            assert(qual(t[row as int]));
        }
        let g = match find_global(c, Ghost(t), Ghost(c.n as int), rep, row) {
            Some(g) => g,
            None => {
                if rep.len() >= 64 {
                    return None;
                }
                let ghost rep1 = rep@;
                let ghost cnt1 = cnt@;
                let ghost sum1 = sum@;
                let key = Ghost(key_of(t[row as int]));
                proof {
                    // No row before `lo` has the new key: it would be in an existing global group.
                    assert forall|j: int| 0 <= j < lo implies !#[trigger] hit(t[j], key@) by {
                        if hit(t[j], key@) {
                            let g2 = choose|g2: int| 0 <= g2 < rep1.len() && key_of(t[j]) == gkey(t, rep1, g2);
                            assert(gkey(t, rep1, g2) != key@);
                        }
                    }
                    lemma_no_hit(t, key@, 0, lo);
                }
                rep.push(row);
                cnt.push(0);
                sum.push(0);
                proof {
                    let rep2 = rep@;
                    assert forall|g2: int| 0 <= g2 < rep1.len() implies #[trigger] gkey(t, rep2, g2) == gkey(t, rep1, g2) by {
                        assert(rep2[g2] == rep1[g2]);
                    }
                    assert(gkey(t, rep2, rep1.len() as int) == key@);
                    assert forall|g1: int, g2: int| 0 <= g1 < rep2.len() && 0 <= g2 < rep2.len() && g1 != g2
                        implies #[trigger] gkey(t, rep2, g1) != #[trigger] gkey(t, rep2, g2) by {
                        if g1 < rep1.len() && g2 < rep1.len() {
                            assert(gkey(t, rep1, g1) != gkey(t, rep1, g2));
                        }
                    }
                    assert forall|j: int| 0 <= j < lo && qual(#[trigger] t[j]) implies exists|g3: int| 0 <= g3 < rep2.len() && key_of(t[j]) == gkey(t, rep2, g3) by {
                        let g3 = choose|g3: int| 0 <= g3 < rep1.len() && key_of(t[j]) == gkey(t, rep1, g3);
                        assert(gkey(t, rep2, g3) == gkey(t, rep1, g3));
                    }
                    assert forall|g2: int| 0 <= g2 < rep2.len() implies #[trigger] cnt@[g2] == cnt_r(t, gkey(t, rep2, g2), 0, lo) by {
                        if g2 < rep1.len() {
                            assert(cnt1[g2] == cnt_r(t, gkey(t, rep1, g2), 0, lo));
                        }
                    }
                    assert forall|g2: int| 0 <= g2 < rep2.len() implies #[trigger] sum@[g2] == sum_r(t, gkey(t, rep2, g2), 0, lo) by {
                        if g2 < rep1.len() {
                            assert(sum1[g2] == sum_r(t, gkey(t, rep1, g2), 0, lo));
                        }
                    }
                    assert(rep2.subrange(0, rep0.len() as int) =~= rep0);
                    assert forall|lg2: int| 0 <= lg2 < lg implies (#[trigger] map@[lg2]) < rep2.len() && map@[lg2] < 64
                        && gkey(t, rep2, map@[lg2] as int) == gkey(t, out.acc.rep@, lg2) by {
                        assert(gkey(t, rep2, map@[lg2] as int) == gkey(t, rep1, map@[lg2] as int));
                    }
                }
                rep.len() - 1
            },
        };
        map.set(lg, g);
        lg = lg + 1;
    }
    Some(map)
}

/// Local groups map to different global groups.
proof fn lemma_map_inj(t: Seq<Row>, rep: Seq<usize>, out: ScanOut, map: Seq<usize>, c: Cols, lo: int, hi: int)
    requires
        map_ok(t, rep, out, map), out_ok(c, t, lo, hi, out.ng as int, out.acc),
    ensures
        forall|l1: int, l2: int| 0 <= l1 < out.ng && 0 <= l2 < out.ng && l1 != l2 ==> #[trigger] map[l1] != #[trigger] map[l2],
{
    assert forall|l1: int, l2: int| 0 <= l1 < out.ng && 0 <= l2 < out.ng && l1 != l2 implies #[trigger] map[l1] != #[trigger] map[l2] by {
        assert(gkey(t, out.acc.rep@, l1) != gkey(t, out.acc.rep@, l2));
    }
}

/// Counts and sums of global groups after adding the local groups `[0, lg)` of range `[lo, hi)`.
pub open spec fn adding_ok(t: Seq<Row>, lo: int, hi: int, rep: Seq<usize>, cnt: Seq<u64>, sum: Seq<i128>, map: Seq<usize>, lg: int) -> bool {
    &&& forall|g: int| 0 <= g < rep.len() ==> #[trigger] cnt[g] == cnt_r(t, gkey(t, rep, g), 0, lo)
        + if mapped(map, lg, g) { cnt_r(t, gkey(t, rep, g), lo, hi) } else { 0 }
    &&& forall|g: int| 0 <= g < rep.len() ==> #[trigger] sum[g] == sum_r(t, gkey(t, rep, g), 0, lo)
        + if mapped(map, lg, g) { sum_r(t, gkey(t, rep, g), lo, hi) } else { 0 }
}

/// Step 2 for task range `[lo, hi)`: adds each local group's count and sum to its global group.
fn add_task(c: &Cols, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>, out: &ScanOut,
    map: &Vec<usize>, rep: &Vec<usize>, cnt: &mut Vec<u64>, sum: &mut Vec<i128>)
    requires
        cols_wf(*c), corr(*c, t), 0 <= lo <= hi <= c.n,
        out_ok(*c, t, lo, hi, out.ng as int, out.acc),
        merged_ok(t, c.n as int, lo, rep@, old(cnt)@, old(sum)@),
        map_ok(t, rep@, *out, map@),
    ensures
        merged_ok(t, c.n as int, hi, rep@, final(cnt)@, final(sum)@),
{
    proof {
        lemma_map_inj(t, rep@, *out, map@, *c, lo, hi);
        assert(adding_ok(t, lo, hi, rep@, cnt@, sum@, map@, 0));
    }
    let mut lg: usize = 0;
    while lg < out.ng
        invariant
            cols_wf(*c), corr(*c, t), 0 <= lo <= hi <= c.n,
            out_ok(*c, t, lo, hi, out.ng as int, out.acc),
            map_ok(t, rep@, *out, map@),
            forall|l1: int, l2: int| 0 <= l1 < out.ng && 0 <= l2 < out.ng && l1 != l2 ==> #[trigger] map@[l1] != #[trigger] map@[l2],
            cnt@.len() == rep@.len(), sum@.len() == rep@.len(), rep@.len() <= 64,
            lg <= out.ng,
            adding_ok(t, lo, hi, rep@, cnt@, sum@, map@, lg as int),
        decreases out.ng - lg,
    {
        let g = map[lg];
        let ghost key = gkey(t, rep@, g as int);
        proof {
            assert(key == gkey(t, out.acc.rep@, lg as int));
            assert(!mapped(map@, lg as int, g as int)) by {
                if mapped(map@, lg as int, g as int) {
                    let l2 = choose|l2: int| 0 <= l2 < lg && #[trigger] map@[l2] == g;
                    assert(map@[l2] != map@[lg as int]);
                }
            }
            assert(cnt@[g as int] == cnt_r(t, key, 0, lo));
            assert(sum@[g as int] == sum_r(t, key, 0, lo));
            assert(out.acc.cnt@[lg as int] == cnt_r(t, key, lo, hi));
            assert(out.acc.sum@[lg as int] == sum_r(t, key, lo, hi));
            lemma_split(t, key, 0, lo, hi);
            lemma_bounds_m(*c, t, 0, hi, key);
        }
        let ghost cnt0 = cnt@;
        let ghost sum0 = sum@;
        let nc = cnt[g] + out.acc.cnt[lg];
        cnt.set(g, nc);
        let ns = sum[g] + out.acc.sum[lg];
        sum.set(g, ns);
        proof {
            assert forall|g2: int| #![auto] 0 <= g2 < rep@.len() implies mapped(map@, lg + 1, g2) == (mapped(map@, lg as int, g2) || g2 == g) by {
                if g2 == g {
                    assert(map@[lg as int] == g2);
                }
                if mapped(map@, lg + 1, g2) && g2 != g {
                    let l2 = choose|l2: int| 0 <= l2 < lg + 1 && #[trigger] map@[l2] == g2;
                    assert(l2 < lg);
                }
            }
            assert(adding_ok(t, lo, hi, rep@, cnt@, sum@, map@, lg + 1));
        }
        lg = lg + 1;
    }
    proof {
        let rep_ = rep@;
        // A global group without a local group has no rows in the range.
        assert forall|g: int| 0 <= g < rep_.len() && !mapped(map@, out.ng as int, g)
            implies cnt_r(t, #[trigger] gkey(t, rep_, g), lo, hi) == 0 && sum_r(t, gkey(t, rep_, g), lo, hi) == 0 by {
            let key = gkey(t, rep_, g);
            assert forall|j: int| lo <= j < hi implies !#[trigger] hit(t[j], key) by {
                if hit(t[j], key) {
                    assert(groups_ok(t, lo, hi, hi, out.ng as int, out.acc.rep@));
                    let l = choose|l: int| 0 <= l < out.ng && key_of(t[j]) == gkey(t, out.acc.rep@, l);
                    assert(gkey(t, rep_, map@[l] as int) == key);
                    assert(map@[l] == g);
                }
            }
            lemma_no_hit(t, key, lo, hi);
        }
        assert forall|g: int| 0 <= g < rep_.len() implies #[trigger] cnt@[g] == cnt_r(t, gkey(t, rep_, g), 0, hi) by {
            lemma_split(t, gkey(t, rep_, g), 0, lo, hi);
        }
        assert forall|g: int| 0 <= g < rep_.len() implies #[trigger] sum@[g] == sum_r(t, gkey(t, rep_, g), 0, hi) by {
            lemma_split(t, gkey(t, rep_, g), 0, lo, hi);
        }
        assert forall|j: int| 0 <= j < hi && qual(#[trigger] t[j]) implies exists|g: int| 0 <= g < rep_.len() && key_of(t[j]) == gkey(t, rep_, g) by {
            if j >= lo {
                assert(groups_ok(t, lo, hi, hi, out.ng as int, out.acc.rep@));
                let l = choose|l: int| 0 <= l < out.ng && key_of(t[j]) == gkey(t, out.acc.rep@, l);
                assert(gkey(t, rep_, map@[l] as int) == key_of(t[j]));
            }
        }
    }
}

/// Counts are bounded by the range length (so they fit `u64`), sums by `2^31` per row.
pub proof fn lemma_bounds_m(c: Cols, t: Seq<Row>, lo: int, hi: int, k: Row)
    requires corr(c, t), 0 <= lo <= hi <= c.n,
    ensures
        cnt_r(t, k, lo, hi) <= hi - lo,
        cnt_r(t, k, lo, hi) <= u64::MAX,
        -0x8000_0000 * cnt_r(t, k, lo, hi) <= sum_r(t, k, lo, hi) <= 0x8000_0000 * cnt_r(t, k, lo, hi),
{
    lemma_cnt_le(t, k, lo, hi);
    assert forall|j: int| lo <= j < hi implies -0x8000_0000 <= #[trigger] line_of(t[j]) < 0x8000_0000 by {
        assert(row_corr(c, t[j], j));
    }
    lemma_sum_bound(t, k, lo, hi);
}

/// Merged global groups and the maps of every task.
pub struct Merged {
    pub rep: Vec<usize>,
    pub cnt: Vec<u64>,
    pub sum: Vec<i128>,
    pub maps: Vec<Vec<usize>>,
}

pub open spec fn maps_ok(t: Seq<Row>, rep: Seq<usize>, outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, k: int) -> bool {
    forall|k2: int| 0 <= k2 < k ==> #[trigger] map_ok(t, rep, outs[k2], maps[k2]@)
}

/// Appending global groups keeps every map.
proof fn lemma_maps_grow(t: Seq<Row>, rep: Seq<usize>, rep2: Seq<usize>, outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, k: int)
    requires
        maps_ok(t, rep, outs, maps, k),
        rep2.len() >= rep.len(), rep2.subrange(0, rep.len() as int) == rep,
    ensures
        maps_ok(t, rep2, outs, maps, k),
{
    assert forall|k2: int| 0 <= k2 < k implies #[trigger] map_ok(t, rep2, outs[k2], maps[k2]@) by {
        let m = maps[k2]@;
        assert(map_ok(t, rep, outs[k2], m));
        assert forall|lg: int| 0 <= lg < outs[k2].ng implies (#[trigger] m[lg]) < rep2.len() && m[lg] < 64
            && gkey(t, rep2, m[lg] as int) == gkey(t, outs[k2].acc.rep@, lg) by {
            assert(rep2[m[lg] as int] == rep2.subrange(0, rep.len() as int)[m[lg] as int]);
        }
    }
}

/// Merges the range scans of all tasks (in task order); `None` when there are more than 64 groups.
pub fn merge_groups(c: &Cols, Ghost(t): Ghost<Seq<Row>>, outs: &Vec<ScanOut>, b: &Vec<usize>) -> (r: Option<Merged>)
    requires
        cols_wf(*c), corr(*c, t), tasks_ok(*c, t, b@, outs@),
    ensures
        r matches Some(mg) ==> {
            &&& merged_ok(t, c.n as int, c.n as int, mg.rep@, mg.cnt@, mg.sum@)
            &&& mg.maps@.len() == outs@.len()
            &&& maps_ok(t, mg.rep@, outs@, mg.maps@, outs@.len() as int)
        },
{
    let mut rep: Vec<usize> = Vec::new();
    let mut cnt: Vec<u64> = Vec::new();
    let mut sum: Vec<i128> = Vec::new();
    let mut maps: Vec<Vec<usize>> = Vec::new();
    let mut k: usize = 0;
    while k < outs.len()
        invariant
            cols_wf(*c), corr(*c, t), tasks_ok(*c, t, b@, outs@), k <= outs@.len(),
            merged_ok(t, c.n as int, b@[k as int] as int, rep@, cnt@, sum@),
            maps@.len() == k,
            maps_ok(t, rep@, outs@, maps@, k as int),
        decreases outs@.len() - k,
    {
        let ghost rep0 = rep@;
        proof {
            assert(outs@[k as int].status == ST_OK);
            assert(b@[k as int] <= b@[k + 1]);
            assert(b@[k + 1] <= c.n) by {
                assert(out_ok(*c, t, b@[k as int] as int, b@[k + 1] as int, outs@[k as int].ng as int, outs@[k as int].acc));
            }
        }
        let map = match map_task(c, Ghost(t), Ghost(b@[k as int] as int), Ghost(b@[k + 1] as int), &outs[k], &mut rep, &mut cnt, &mut sum) {
            Some(m) => m,
            None => return None,
        };
        add_task(c, Ghost(t), Ghost(b@[k as int] as int), Ghost(b@[k + 1] as int), &outs[k], &map, &rep, &mut cnt, &mut sum);
        let ghost maps0 = maps@;
        maps.push(map);
        proof {
            lemma_maps_grow(t, rep0, rep@, outs@, maps0, k as int);
            assert forall|k2: int| 0 <= k2 < k + 1 implies #[trigger] map_ok(t, rep@, outs@[k2], maps@[k2]@) by {
                if k2 < k {
                    assert(maps@[k2] == maps0[k2]);
                }
            }
        }
        k = k + 1;
    }
    Some(Merged { rep, cnt, sum, maps })
}

} // verus!
