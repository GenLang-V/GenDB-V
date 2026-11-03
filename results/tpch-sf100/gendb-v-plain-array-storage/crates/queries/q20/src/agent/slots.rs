//! Slots: partsupp rows held as three arrays (part key, supplier key, availability) of which the first `n` entries
//! count, with a directory over groups of 64 part keys starting at group `g0` (`dir[g]` is the number of slots whose
//! part key is below `64 * (g0 + g)`, `slots_dir`). The directory needs the slots' part keys ascending.
//!
//! A lookup (`find_slot`) of a key pair `(a, b)` scans the slots of `a`'s group and returns the first slot with that
//! pair (`first_slot`), which is the first such slot overall; `build_dir` fills the directory of ascending slots.
use vstd::prelude::*;

verus! {

/// Slot arrays (the first `n` entries count) and their directory over the groups `g0 .. g0 + ng`.
pub struct Slots {
    pub spk: Vec<i64>,
    pub ssk: Vec<i64>,
    pub saq: Vec<i64>,
    pub n: usize,
    pub dir: Vec<usize>,
    pub g0: usize,
    pub ng: usize,
}

/// The first `n` part keys ascend.
pub open spec fn ascending(spk: Seq<i64>, n: int) -> bool {
    forall|s: int, t: int| 0 <= s < t < n ==> #[trigger] spk[s] <= #[trigger] spk[t]
}

/// The slots' part keys ascend inside the groups `g0 .. g0 + ng`, and `dir[g]` counts the slots below group `g0 + g`.
pub open spec fn slots_dir(sl: Slots) -> bool {
    &&& sl.dir@.len() >= sl.ng + 1 && sl.spk@.len() >= sl.n && sl.ssk@.len() >= sl.n && sl.saq@.len() >= sl.n
    &&& sl.ng <= 0x0400_0000 && sl.g0 <= 0x0400_0000 && sl.n < 0x1_0000_0000
    &&& ascending(sl.spk@, sl.n as int)
    &&& forall|s: int| 0 <= s < sl.n ==> 0 <= #[trigger] sl.spk@[s] && sl.g0 <= sl.spk@[s] / 64 < sl.g0 + sl.ng
    &&& forall|g: int| 0 <= g <= sl.ng ==> #[trigger] sl.dir@[g] <= sl.n
    &&& forall|g: int, s: int| 0 <= g <= sl.ng && 0 <= s < sl.n ==> (s < #[trigger] sl.dir@[g]) == (#[trigger] sl.spk@[s] / 64 < sl.g0 + g)
}

/// Some slot of the first `n` has the pair `(a, b)`.
pub open spec fn has_slot(spk: Seq<i64>, ssk: Seq<i64>, n: int, a: int, b: int) -> bool {
    exists|s: int| 0 <= s < n && #[trigger] spk[s] as int == a && ssk[s] as int == b
}

/// `s` is the first slot with the pair `(a, b)`.
pub open spec fn first_slot(spk: Seq<i64>, ssk: Seq<i64>, n: int, a: int, b: int, s: int) -> bool {
    &&& 0 <= s < n && s < spk.len() && s < ssk.len() && spk[s] as int == a && ssk[s] as int == b
    &&& forall|t: int| 0 <= t < s ==> !(#[trigger] spk[t] as int == a && ssk[t] as int == b)
}

/// The first slot is unique.
pub proof fn lemma_first_unique(spk: Seq<i64>, ssk: Seq<i64>, n: int, a: int, b: int, s: int, t: int)
    requires first_slot(spk, ssk, n, a, b, s), first_slot(spk, ssk, n, a, b, t),
    ensures s == t,
{
    if s < t { assert(!(spk[s] as int == a && ssk[s] as int == b)); }
    if t < s { assert(!(spk[t] as int == a && ssk[t] as int == b)); }
}

/// The first slot of the pair `(a, b)` (`no_unwind`), for a key `a` in the directory's groups.
#[inline(always)]
pub fn find_slot(sl: &Slots, a: i64, b: i64) -> (r: Option<usize>)
    requires slots_dir(*sl), 0 <= a, sl.g0 <= (a as int) / 64 < sl.g0 + sl.ng,
    ensures
        r matches Some(s) ==> first_slot(sl.spk@, sl.ssk@, sl.n as int, a as int, b as int, s as int),
        r is None ==> !has_slot(sl.spk@, sl.ssk@, sl.n as int, a as int, b as int),
    no_unwind
{
    let au = a as u64;
    proof { crate::agent::common::bitset::lemma_word_pos(au); }
    let g = (au >> 6u64) as usize - sl.g0;
    let mut s = sl.dir[g];
    let e = sl.dir[g + 1];
    proof {
        // the slots before the group have smaller keys
        assert forall|t: int| 0 <= t < s implies !(#[trigger] sl.spk@[t] as int == a as int) by {
            assert((t < sl.dir@[g as int]) == (sl.spk@[t] / 64 < sl.g0 + g));
        }
    }
    while s < e
        invariant
            slots_dir(*sl), 0 <= a, sl.g0 + g == (a as int) / 64, g < sl.ng, e == sl.dir@[g + 1], s <= sl.n,
            forall|t: int| 0 <= t < s ==> !(#[trigger] sl.spk@[t] as int == a as int && sl.ssk@[t] as int == b as int),
        decreases e - s,
    {
        if sl.spk[s] == a && sl.ssk[s] == b {
            return Some(s);
        }
        s = s + 1;
    }
    proof {
        // the slots from the group's end on have larger keys
        assert forall|t: int| 0 <= t < sl.n implies !(#[trigger] sl.spk@[t] as int == a as int && sl.ssk@[t] as int == b as int) by {
            if t >= s {
                assert((t < sl.dir@[g as int + 1]) == (sl.spk@[t] / 64 < sl.g0 + g + 1));
                if sl.spk@[t] as int == a as int {
                    assert(sl.spk@[t] / 64 == sl.g0 + g);
                }
            }
        }
    }
    None
}

/// The directory of `n` ascending slots over the groups `g0 .. g0 + ng` into `dir` (`no_unwind`).
pub fn build_dir(spk: &Vec<i64>, n: usize, g0: usize, ng: usize, dir: &mut Vec<usize>)
    requires
        spk@.len() >= n, old(dir)@.len() >= ng + 1, ng <= 0x0400_0000, g0 <= 0x0400_0000,
        ascending(spk@, n as int),
        forall|u: int| 0 <= u < n ==> 0 <= #[trigger] spk@[u] && g0 <= spk@[u] / 64 < g0 + ng,
    ensures
        final(dir)@.len() == old(dir)@.len(),
        forall|h: int| 0 <= h <= ng ==> #[trigger] final(dir)@[h] <= n,
        forall|h: int, u: int| 0 <= h <= ng && 0 <= u < n ==> (u < #[trigger] final(dir)@[h]) == (#[trigger] spk@[u] / 64 < g0 + h),
    no_unwind
{
    let mut g: usize = 0;
    let mut s: usize = 0;
    while s < n
        invariant
            spk@.len() >= n, s <= n, dir@.len() == old(dir)@.len(), dir@.len() >= ng + 1, ng <= 0x0400_0000, g0 <= 0x0400_0000,
            ascending(spk@, n as int),
            forall|u: int| 0 <= u < n ==> 0 <= #[trigger] spk@[u] && g0 <= spk@[u] / 64 < g0 + ng,
            g == if s == 0 { 0 } else { spk@[s - 1] / 64 + 1 - g0 }, g <= ng,
            forall|h: int| 0 <= h < g ==> #[trigger] dir@[h] <= n,
            forall|h: int, u: int| 0 <= h < g && 0 <= u < n ==> (u < #[trigger] dir@[h]) == (#[trigger] spk@[u] / 64 < g0 + h),
        decreases n - s,
    {
        let v = spk[s];
        proof { crate::agent::common::bitset::lemma_word_pos(v as u64); }
        let gs = ((v as u64) >> 6u64) as usize - g0;
        let ghost gb = g;
        while g <= gs
            invariant
                spk@.len() >= n, s < n, dir@.len() == old(dir)@.len(), dir@.len() >= ng + 1, gs + g0 == spk@[s as int] / 64, gs < ng,
                ascending(spk@, n as int),
                forall|u: int| 0 <= u < n ==> 0 <= #[trigger] spk@[u] && g0 <= spk@[u] / 64 < g0 + ng,
                gb <= g <= gs + 1, gb == if s == 0 { 0 } else { spk@[s - 1] / 64 + 1 - g0 },
                forall|h: int| 0 <= h < g ==> #[trigger] dir@[h] <= n,
                forall|h: int, u: int| 0 <= h < g && 0 <= u < n ==> (u < #[trigger] dir@[h]) == (#[trigger] spk@[u] / 64 < g0 + h),
            decreases gs + 1 - g,
        {
            dir[g] = s;
            proof {
                assert forall|u: int| 0 <= u < n implies (u < dir@[g as int]) == (#[trigger] spk@[u] / 64 < g0 + g) by {
                    if u < s {
                        assert(spk@[u] <= spk@[s - 1]);
                        assert(spk@[u] / 64 <= spk@[s - 1] / 64);
                    } else {
                        if u > s { assert(spk@[s as int] <= spk@[u]); }
                        assert(spk@[s as int] / 64 <= spk@[u] / 64);
                    }
                }
            }
            g = g + 1;
        }
        s = s + 1;
    }
    while g <= ng
        invariant
            spk@.len() >= n, dir@.len() == old(dir)@.len(), dir@.len() >= ng + 1, ng <= 0x0400_0000, g <= ng + 1,
            forall|u: int| 0 <= u < n ==> 0 <= #[trigger] spk@[u] && g0 <= spk@[u] / 64 < g0 + ng,
            n == 0 || g >= spk@[n - 1] / 64 + 1 - g0,
            ascending(spk@, n as int),
            forall|h: int| 0 <= h < g ==> #[trigger] dir@[h] <= n,
            forall|h: int, u: int| 0 <= h < g && 0 <= u < n ==> (u < #[trigger] dir@[h]) == (#[trigger] spk@[u] / 64 < g0 + h),
        decreases ng + 1 - g,
    {
        dir[g] = n;
        proof {
            assert forall|u: int| 0 <= u < n implies (u < dir@[g as int]) == (#[trigger] spk@[u] / 64 < g0 + g) by {
                if u < n - 1 { assert(spk@[u] <= spk@[n - 1]); }
            }
        }
        g = g + 1;
    }
}

} // verus!
