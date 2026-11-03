//! Distinct adsh counts of the global groups from the tasks' bit sets: `in_g(.., g, id)` says that some task has a
//! local group mapped to global group `g` with bit set at `sub` row `id`; `idcount` counts those ids over a range.
//! `count_range` computes the counts of every global group over an id range (a worker task); `lemma_idcount_aset`
//! proves that over all ids the count is the number of distinct adsh values of the group, given that distinct
//! `sub` rows hold distinct values.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::cols::*;
use crate::agent::spec::*;
use crate::agent::kernel::*;
use crate::agent::merge::*;
use crate::agent::common::bits::*;

verus! {

/// Some task has a local group mapped to global group `g` with the bit of `sub` row `id` set.
pub open spec fn in_g(outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, g: int, id: int) -> bool {
    exists|k: int, lg: int| 0 <= k < outs.len() && 0 <= lg < outs[k].ng && #[trigger] maps[k]@[lg] == g
        && bit16(outs[k].acc.mask@[id], lg as u16)
}

/// Number of ids in `[lo, hi)` with `in_g`.
pub open spec fn idcount(outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, g: int, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo {
        0
    } else {
        idcount(outs, maps, g, lo, hi - 1) + if in_g(outs, maps, g, hi - 1) { 1nat } else { 0nat }
    }
}

pub proof fn lemma_idcount_split(outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, g: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures idcount(outs, maps, g, lo, hi) == idcount(outs, maps, g, lo, mid) + idcount(outs, maps, g, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_idcount_split(outs, maps, g, lo, mid, hi - 1);
    }
}

/// Shapes the count phase reads: every task's maps (into `ng <= 64` global groups) and bit sets (`m` ids).
pub open spec fn count_inputs(outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, ng: int, m: int) -> bool {
    &&& maps.len() == outs.len()
    &&& 0 <= ng <= 64
    &&& forall|k: int| 0 <= k < outs.len() ==> {
        &&& (#[trigger] outs[k]).ng <= GCAP
        &&& outs[k].acc.mask@.len() == m
        &&& maps[k]@.len() == GCAP
        &&& forall|lg: int| 0 <= lg < outs[k].ng ==> #[trigger] maps[k]@[lg] < ng
    }
}

/// Global groups `id` belongs to through tasks `[0, k)` (and, of task `k`, local groups `[0, lg)`).
pub open spec fn upto(outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, g: int, id: int, k: int, lg: int) -> bool {
    exists|k2: int, l2: int| 0 <= k2 <= k && k2 < outs.len() && 0 <= l2 < outs[k2].ng && (k2 < k || l2 < lg)
        && #[trigger] maps[k2]@[l2] == g && bit16(outs[k2].acc.mask@[id], l2 as u16)
}

proof fn lemma_bit_test16(x: u16, b: u16)
    requires b < 16,
    ensures ((x >> b) & 1u16 != 0) == bit16(x, b),
{
    assert(((x >> b) & 1u16 != 0) == ((x >> b) & 1u16 == 1u16)) by (bit_vector);
}

proof fn lemma_bit_test64(x: u64, b: u64)
    requires b < 64,
    ensures ((x >> b) & 1u64 != 0) == bit64(x, b),
{
    assert(((x >> b) & 1u64 != 0) == ((x >> b) & 1u64 == 1u64)) by (bit_vector);
}

/// Adding bit `lg` of `mt` (as `bit`) at position `gg` adds `gg` exactly when the bit is set.
proof fn lemma_add_bit(c0: u64, mt: u16, lg: u16, bit: u64, gg: u64)
    requires lg < 16, gg < 64, bit == ((mt >> lg) & 1u16) as u64,
    ensures
        (mt >> lg) & 1u16 != 0 ==> c0 | (bit << gg) == c0 | (1u64 << gg),
        (mt >> lg) & 1u16 == 0 ==> c0 | (bit << gg) == c0,
{
    let b16 = (mt >> lg) & 1u16;
    assert(b16 == 0u16 || b16 == 1u16) by (bit_vector) requires b16 == (mt >> lg) & 1u16;
    if b16 == 1u16 {
        assert(bit == 1u64);
        assert(c0 | (1u64 << gg) == c0 | (1u64 << gg));
    } else {
        assert(bit == 0u64);
        assert(c0 | (0u64 << gg) == c0) by (bit_vector) requires gg < 64u64;
    }
}

/// Bit `g` of `x` as 0 or 1.
proof fn lemma_bit01(x: u64, g: u64)
    requires g < 64,
    ensures
        (x >> g) & 1u64 <= 1,
        ((x >> g) & 1u64 == 1) == ((x >> g) & 1u64 != 0),
{
    assert((x >> g) & 1u64 <= 1 && (((x >> g) & 1u64 == 1) == ((x >> g) & 1u64 != 0))) by (bit_vector) requires g < 64u64;
}

/// The global groups of `sub` row `id`, as a 64-bit set.
fn groups_of(outs: &Vec<ScanOut>, maps: &Vec<Vec<usize>>, Ghost(ng): Ghost<int>, Ghost(m): Ghost<int>, id: usize) -> (comb: u64)
    requires count_inputs(outs@, maps@, ng, m), id < m,
    ensures forall|g: u64| g < 64 ==> #[trigger] bit64(comb, g) == in_g(outs@, maps@, g as int, id as int),
    no_unwind
{
    let nt = outs.len();
    let mut comb: u64 = 0;
    let mut k: usize = 0;
    proof {
        assert forall|g: u64| g < 64 implies #[trigger] bit64(comb, g) == upto(outs@, maps@, g as int, id as int, 0, 0) by {
            lemma_zero64(g);
        }
    }
    while k < nt
        invariant
            count_inputs(outs@, maps@, ng, m), id < m, nt == outs@.len(), k <= nt,
            forall|g: u64| g < 64 ==> #[trigger] bit64(comb, g) == upto(outs@, maps@, g as int, id as int, k as int, 0),
        decreases nt - k,
    {
        let mt = outs[k].acc.mask[id];
        // Most tasks have no group at a given id: their bit set is empty and no local group is visited.
        let nl = if mt == 0 { 0 } else { outs[k].ng };
        proof { assert(outs@[k as int].ng <= GCAP); }
        let mut lg: usize = 0;
        while lg < nl
            invariant
                count_inputs(outs@, maps@, ng, m), id < m, nt == outs@.len(), k < nt, lg <= nl,
                nl == outs@[k as int].ng || (nl == 0 && mt == 0), nl <= GCAP,
                mt == outs@[k as int].acc.mask@[id as int],
                forall|g: u64| g < 64 ==> #[trigger] bit64(comb, g) == upto(outs@, maps@, g as int, id as int, k as int, lg as int),
            decreases nl - lg,
        {
            let ghost comb0 = comb;
            proof { lemma_bit_test16(mt, lg as u16); }
            // Branch-free: the group's bit (0 or 1) shifted to its global group.
            let gg = maps[k][lg];
            proof { assert(maps@[k as int]@[lg as int] < ng); }
            let bit = ((mt >> (lg as u16)) & 1u16) as u64;
            comb = comb | (bit << (gg as u64));
            proof { lemma_add_bit(comb0, mt, lg as u16, bit, gg as u64); }
            if (mt >> (lg as u16)) & 1u16 != 0 {
                proof {
                    assert forall|g: u64| g < 64 implies #[trigger] bit64(comb, g) == upto(outs@, maps@, g as int, id as int, k as int, lg + 1) by {
                        lemma_or64(comb0, 1u64 << (gg as u64), g);
                        lemma_one64(gg as u64, g);
                        if upto(outs@, maps@, g as int, id as int, k as int, lg + 1) && !(g == gg as u64) {
                            let (k2, l2) = choose|k2: int, l2: int| 0 <= k2 <= k && k2 < outs@.len() && 0 <= l2 < outs@[k2].ng && (k2 < k || l2 < lg + 1)
                                && #[trigger] maps@[k2]@[l2] == g as int && bit16(outs@[k2].acc.mask@[id as int], l2 as u16);
                            assert(k2 < k || l2 < lg);
                        }
                        if g == gg as u64 {
                            assert(maps@[k as int]@[lg as int] == g as int);
                        }
                    }
                }
            } else {
                proof {
                    assert forall|g: u64| g < 64 implies #[trigger] bit64(comb, g) == upto(outs@, maps@, g as int, id as int, k as int, lg + 1) by {
                        if upto(outs@, maps@, g as int, id as int, k as int, lg + 1) {
                            let (k2, l2) = choose|k2: int, l2: int| 0 <= k2 <= k && k2 < outs@.len() && 0 <= l2 < outs@[k2].ng && (k2 < k || l2 < lg + 1)
                                && #[trigger] maps@[k2]@[l2] == g as int && bit16(outs@[k2].acc.mask@[id as int], l2 as u16);
                            if k2 == k && l2 == lg {
                                assert(false);
                            }
                        }
                    }
                }
            }
            lg = lg + 1;
        }
        proof {
            assert forall|g: u64| g < 64 implies #[trigger] bit64(comb, g) == upto(outs@, maps@, g as int, id as int, k + 1, 0) by {
                if upto(outs@, maps@, g as int, id as int, k as int, nl as int) {
                    let (k2, l2) = choose|k2: int, l2: int| 0 <= k2 <= k && k2 < outs@.len() && 0 <= l2 < outs@[k2].ng && (k2 < k || l2 < nl)
                        && #[trigger] maps@[k2]@[l2] == g as int && bit16(outs@[k2].acc.mask@[id as int], l2 as u16);
                    assert(upto(outs@, maps@, g as int, id as int, k + 1, 0));
                }
                if upto(outs@, maps@, g as int, id as int, k + 1, 0) {
                    let (k2, l2) = choose|k2: int, l2: int| 0 <= k2 <= k + 1 && k2 < outs@.len() && 0 <= l2 < outs@[k2].ng && (k2 < k + 1 || l2 < 0)
                        && #[trigger] maps@[k2]@[l2] == g as int && bit16(outs@[k2].acc.mask@[id as int], l2 as u16);
                    if k2 == k && nl != outs@[k as int].ng {
                        lemma_zero16(l2 as u16);
                        assert(false);
                    }
                    assert(upto(outs@, maps@, g as int, id as int, k as int, nl as int));
                }
            }
        }
        k = k + 1;
    }
    proof {
        assert forall|g: u64| g < 64 implies #[trigger] bit64(comb, g) == in_g(outs@, maps@, g as int, id as int) by {
            if in_g(outs@, maps@, g as int, id as int) {
                let (k2, l2) = choose|k2: int, l2: int| 0 <= k2 < outs@.len() && 0 <= l2 < outs@[k2].ng && #[trigger] maps@[k2]@[l2] == g as int
                    && bit16(outs@[k2].acc.mask@[id as int], l2 as u16);
                assert(upto(outs@, maps@, g as int, id as int, nt as int, 0));
            }
            if upto(outs@, maps@, g as int, id as int, nt as int, 0) {
                let (k2, l2) = choose|k2: int, l2: int| 0 <= k2 <= nt && k2 < outs@.len() && 0 <= l2 < outs@[k2].ng && (k2 < nt || l2 < 0)
                    && #[trigger] maps@[k2]@[l2] == g as int && bit16(outs@[k2].acc.mask@[id as int], l2 as u16);
                assert(in_g(outs@, maps@, g as int, id as int));
            }
        }
    }
    comb
}

/// Counts of every global group `g < ng` over the ids `[lo, hi)`, added to `out` (zero on entry).
pub fn count_range(outs: &Vec<ScanOut>, maps: &Vec<Vec<usize>>, ng: usize, Ghost(m): Ghost<int>, lo: usize, hi: usize,
    out: Vec<u64>) -> (r: Vec<u64>)
    requires
        count_inputs(outs@, maps@, ng as int, m), lo <= hi <= m,
        out@.len() == 64, forall|g: int| 0 <= g < 64 ==> #[trigger] out@[g] == 0,
    ensures
        r@.len() == 64,
        forall|g: int| 0 <= g < ng ==> #[trigger] r@[g] == idcount(outs@, maps@, g, lo as int, hi as int),
    no_unwind
{
    let mut res = out;
    let mut id = lo;
    while id < hi
        invariant
            count_inputs(outs@, maps@, ng as int, m), lo <= id <= hi, hi <= m, res@.len() == 64,
            forall|g: int| 0 <= g < ng ==> #[trigger] res@[g] == idcount(outs@, maps@, g, lo as int, id as int),
            forall|g: int| 0 <= g < ng ==> #[trigger] res@[g] <= id - lo,
        decreases hi - id,
    {
        let comb = groups_of(outs, maps, Ghost(ng as int), Ghost(m), id);
        let ghost res0 = res@;
        // An id of no group (most ids of a range) changes no count.
        let ngl = if comb == 0 { 0 } else { ng };
        proof {
            if comb == 0 {
                assert forall|g2: int| 0 <= g2 < ng implies #[trigger] idcount(outs@, maps@, g2, lo as int, id + 1)
                    == idcount(outs@, maps@, g2, lo as int, id as int) by {
                    lemma_zero64(g2 as u64);
                    assert(!in_g(outs@, maps@, g2, id as int));
                }
            }
        }
        let mut g: usize = 0;
        while g < ngl
            invariant
                count_inputs(outs@, maps@, ng as int, m), lo <= id < hi, hi <= m, res@.len() == 64, g <= ngl,
                ngl == ng || (ngl == 0 && comb == 0),
                comb == 0 ==> forall|g2: int| 0 <= g2 < ng ==> #[trigger] idcount(outs@, maps@, g2, lo as int, id + 1)
                    == idcount(outs@, maps@, g2, lo as int, id as int),
                forall|g2: u64| g2 < 64 ==> #[trigger] bit64(comb, g2) == in_g(outs@, maps@, g2 as int, id as int),
                forall|g2: int| 0 <= g2 < ng ==> #[trigger] res0[g2] == idcount(outs@, maps@, g2, lo as int, id as int),
                forall|g2: int| 0 <= g2 < ng ==> #[trigger] res0[g2] <= id - lo,
                forall|g2: int| 0 <= g2 < g ==> #[trigger] res@[g2] == idcount(outs@, maps@, g2, lo as int, id + 1),
                forall|g2: int| g <= g2 < 64 ==> #[trigger] res@[g2] == res0[g2],
                forall|g2: int| 0 <= g2 < g ==> #[trigger] res@[g2] <= id + 1 - lo,
            decreases ngl - g,
        {
            proof {
                lemma_bit_test64(comb, g as u64);
                assert(bit64(comb, g as u64) == in_g(outs@, maps@, g as int, id as int));
            }
            let bit = (comb >> (g as u64)) & 1u64;
            proof { lemma_bit01(comb, g as u64); }
            res[g] = res[g] + bit;
            g = g + 1;
        }
        proof {
            assert forall|g2: int| 0 <= g2 < ng implies #[trigger] res@[g2] == idcount(outs@, maps@, g2, lo as int, id + 1)
                && res@[g2] <= id + 1 - lo by {
                if ngl == 0 {
                    assert(res@[g2] == res0[g2]);
                }
            }
        }
        id = id + 1;
    }
    res
}

/// Phase 2 as a worker task: counts over the ids `[lo, hi)`.
pub struct CountTask {
    pub outs: Arc<Vec<ScanOut>>,
    pub maps: Arc<Vec<Vec<usize>>>,
    pub ng: usize,
    pub m: Ghost<int>,
    pub lo: usize,
    pub hi: usize,
    pub out: Vec<u64>,
}

impl WorkerTask for CountTask {
    type Output = Vec<u64>;

    open spec fn pre(&self) -> bool {
        &&& count_inputs(self.outs@, self.maps@, self.ng as int, self.m@)
        &&& self.lo <= self.hi <= self.m@
        &&& self.out@.len() == 64
        &&& forall|g: int| 0 <= g < 64 ==> #[trigger] self.out@[g] == 0
    }

    open spec fn post(&self, r: Vec<u64>) -> bool {
        &&& r@.len() == 64
        &&& forall|g: int| 0 <= g < self.ng ==> #[trigger] r@[g] == idcount(self.outs@, self.maps@, g, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (r: Vec<u64>) {
        let outs: &Vec<ScanOut> = &*self.outs;
        let maps: &Vec<Vec<usize>> = &*self.maps;
        count_range(outs, maps, self.ng, self.m, self.lo, self.hi, self.out)
    }
}

/// Distinct `sub` rows hold distinct adsh values (the primary key of `sub`).
pub open spec fn sub_distinct(c: Cols) -> bool {
    forall|j1: int, j2: int| 0 <= j1 < c.m && 0 <= j2 < c.m && j1 != j2 ==> #[trigger] c.subtext(j1) != #[trigger] c.subtext(j2)
}

/// The adsh values of the ids in `[lo, hi)` with `in_g`.
pub open spec fn img(c: Cols, outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, g: int, lo: int, hi: int) -> Set<Val>
    decreases hi - lo,
{
    if hi <= lo {
        Set::empty()
    } else if in_g(outs, maps, g, hi - 1) {
        img(c, outs, maps, g, lo, hi - 1).insert(Val::Text(c.subtext(hi - 1)))
    } else {
        img(c, outs, maps, g, lo, hi - 1)
    }
}

proof fn lemma_img_witness(c: Cols, outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, g: int, lo: int, hi: int, v: Val)
    requires img(c, outs, maps, g, lo, hi).contains(v),
    ensures exists|id: int| lo <= id < hi && #[trigger] in_g(outs, maps, g, id) && v == Val::Text(c.subtext(id)),
    decreases hi - lo,
{
    if hi > lo {
        if in_g(outs, maps, g, hi - 1) && v == Val::Text(c.subtext(hi - 1)) {
        } else {
            lemma_img_witness(c, outs, maps, g, lo, hi - 1, v);
        }
    }
}

proof fn lemma_img_member(c: Cols, outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, g: int, lo: int, hi: int, id: int)
    requires lo <= id < hi, in_g(outs, maps, g, id),
    ensures img(c, outs, maps, g, lo, hi).contains(Val::Text(c.subtext(id))),
    decreases hi - lo,
{
    if id < hi - 1 {
        lemma_img_member(c, outs, maps, g, lo, hi - 1, id);
    }
}

/// With distinct values per `sub` row, the image has one value per counted id.
proof fn lemma_img_len(c: Cols, outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, g: int, lo: int, hi: int)
    requires sub_distinct(c), 0 <= lo <= hi <= c.m,
    ensures img(c, outs, maps, g, lo, hi).len() == idcount(outs, maps, g, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_img_len(c, outs, maps, g, lo, hi - 1);
        let v = Val::Text(c.subtext(hi - 1));
        if in_g(outs, maps, g, hi - 1) && img(c, outs, maps, g, lo, hi - 1).contains(v) {
            lemma_img_witness(c, outs, maps, g, lo, hi - 1, v);
            let id = choose|id: int| lo <= id < hi - 1 && #[trigger] in_g(outs, maps, g, id) && v == Val::Text(c.subtext(id));
            assert(c.subtext(id) != c.subtext(hi - 1));
        }
    }
}

/// A row of the table lies in some task's range.
proof fn lemma_task_of(b: Seq<usize>, nt: int, j: int, kk: int)
    requires
        b.len() == nt + 1, 0 <= kk <= nt, b[0] <= j < b[kk],
        forall|k: int| 0 <= k < nt ==> #[trigger] b[k] <= b[k + 1],
    ensures exists|k: int| 0 <= k < kk && #[trigger] b[k] <= j && j < b[k + 1],
    decreases kk,
{
    if j < b[kk - 1] {
        lemma_task_of(b, nt, j, kk - 1);
        let k = choose|k: int| 0 <= k < kk - 1 && #[trigger] b[k] <= j && j < b[k + 1];
        assert(b[k] <= j && j < b[k + 1]);
    } else {
        assert(b[kk - 1] <= j && j < b[kk - 1 + 1]);
    }
}

/// The count of ids of global group `g` is the number of its distinct adsh values.
pub proof fn lemma_idcount_aset(c: Cols, t: Seq<Row>, b: Seq<usize>, outs: Seq<ScanOut>, rep: Seq<usize>, cnt: Seq<u64>,
    sum: Seq<i128>, maps: Seq<Vec<usize>>, g: int)
    requires
        cols_wf(c), corr(c, t), tasks_ok(c, t, b, outs),
        merged_ok(t, c.n as int, c.n as int, rep, cnt, sum),
        maps.len() == outs.len(), maps_ok(t, rep, outs, maps, outs.len() as int),
        sub_distinct(c), 0 <= g < rep.len(),
    ensures
        idcount(outs, maps, g, 0, c.m as int) == aset_r(t, gkey(t, rep, g), 0, c.n as int).len(),
{
    let key = gkey(t, rep, g);
    let n = c.n as int;
    let nt = outs.len() as int;
    let im = img(c, outs, maps, g, 0, c.m as int);
    let a = aset_r(t, key, 0, n);
    lemma_img_len(c, outs, maps, g, 0, c.m as int);
    assert forall|v: Val| im.contains(v) implies a.contains(v) by {
        lemma_img_witness(c, outs, maps, g, 0, c.m as int, v);
        let id = choose|id: int| 0 <= id < c.m && #[trigger] in_g(outs, maps, g, id) && v == Val::Text(c.subtext(id));
        let (k, lg) = choose|k: int, lg: int| 0 <= k < outs.len() && 0 <= lg < outs[k].ng && #[trigger] maps[k]@[lg] == g
            && bit16(outs[k].acc.mask@[id], lg as u16);
        let (lo, hi) = (b[k] as int, b[k + 1] as int);
        assert(outs[k].status == ST_OK && out_ok(c, t, lo, hi, outs[k].ng as int, outs[k].acc));
        assert(map_ok(t, rep, outs[k], maps[k]@));
        assert(gkey(t, outs[k].acc.rep@, lg) == key);
        assert(mask_sound(c, t, lo, hi, outs[k].ng as int, outs[k].acc.rep@, outs[k].acc.mask@));
        assert(bit16(outs[k].acc.mask@[id], lg as u16));
        assert(aset_r(t, gkey(t, outs[k].acc.rep@, (lg as u16) as int), lo, hi).contains(Val::Text(c.subtext(id))));
        lemma_split(t, key, 0, lo, n);
        lemma_split(t, key, lo, hi, n);
    }
    assert forall|v: Val| a.contains(v) implies im.contains(v) by {
        lemma_aset_witness(t, key, 0, n, v);
        let j = choose|j: int| 0 <= j < n && #[trigger] hit(t[j], key) && t[j][0] == v;
        lemma_task_of(b, nt, j, nt);
        let k = choose|k: int| 0 <= k < nt && #[trigger] b[k] <= j && j < b[k + 1];
        let (lo, hi) = (b[k] as int, b[k + 1] as int);
        assert(outs[k].status == ST_OK && out_ok(c, t, lo, hi, outs[k].ng as int, outs[k].acc));
        let lrep = outs[k].acc.rep@;
        assert(groups_ok(t, lo, hi, hi, outs[k].ng as int, lrep));
        let lg = choose|lg: int| 0 <= lg < outs[k].ng && key_of(t[j]) == gkey(t, lrep, lg);
        assert(map_ok(t, rep, outs[k], maps[k]@));
        let g2 = maps[k]@[lg] as int;
        assert(gkey(t, rep, g2) == key);
        assert(g2 == g);
        lemma_aset_member(t, key, lo, hi, j);
        assert(mask_complete(c, t, lo, hi, outs[k].ng as int, lrep, outs[k].acc.mask@));
        assert(aset_r(t, gkey(t, lrep, lg), lo, hi).contains(v));
        let id = choose|id: int| 0 <= id < c.m && Val::Text(c.subtext(id)) == v && #[trigger] bit16(outs[k].acc.mask@[id], lg as u16);
        assert(in_g(outs, maps, g, id));
        lemma_img_member(c, outs, maps, g, 0, c.m as int, id);
    }
    assert(im =~= a);
}

} // verus!
