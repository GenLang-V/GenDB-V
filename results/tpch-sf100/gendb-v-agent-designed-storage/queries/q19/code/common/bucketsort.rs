//! Stable bucket sort (counting sort) of `u32` values by a key: the segment specification of the sorted output and
//! the lemmas that sums over it equal sums over the input.
//!
//! A sequence `s` with every key in `0 .. nb` (`keys_in`) is sorted into `out` when bucket `b` occupies the slots
//! `start(s, key, b) .. start(s, key, b + 1)` of `out` and holds `bsel(s, key, b)`: the values of `s` with key `b`,
//! in their order in `s` (`sorted_by`). Then any sum over the first `s.len()` slots of `out` is the sum over `s`
//! (`lemma_sorted_sum`).
//!
//! The usual algorithm: count the values per bucket (`lemma_bsel_push` steps the counts), turn the counts into
//! bucket starts (`counts_to_starts`), then write the values of `s` in order, each at its bucket's cursor
//! (`scatter_inv`, stepped by `lemma_scatter_step`); after the last value the cursors are the bucket ends and `out`
//! is sorted (`lemma_scatter_done`).
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------------------ sums and buckets

/// `f` summed over `s`.
pub open spec fn sumf(s: Seq<u32>, f: spec_fn(u32) -> int) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sumf(s.drop_last(), f) + f(s.last()) }
}

/// The values of `s` whose key is `b`, in order.
pub open spec fn bsel(s: Seq<u32>, key: spec_fn(u32) -> int, b: int) -> Seq<u32>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if key(s.last()) == b {
        bsel(s.drop_last(), key, b).push(s.last())
    } else {
        bsel(s.drop_last(), key, b)
    }
}

/// Number of values of `s` with key `b`.
pub open spec fn cnt(s: Seq<u32>, key: spec_fn(u32) -> int, b: int) -> int {
    bsel(s, key, b).len() as int
}

/// `g` summed over `lo .. hi`.
pub open spec fn sumb(g: spec_fn(int) -> int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { sumb(g, lo, hi - 1) + g(hi - 1) }
}

/// The first slot of bucket `b`: the number of values with a smaller key (from `0`).
pub open spec fn start(s: Seq<u32>, key: spec_fn(u32) -> int, b: int) -> int {
    sumb(|c: int| cnt(s, key, c), 0, b)
}

/// Every key of `s` lies in `0 .. nb`.
pub open spec fn keys_in(s: Seq<u32>, key: spec_fn(u32) -> int, nb: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] key(s[i]) < nb
}

/// `out` holds `s` sorted into its `nb` buckets.
pub open spec fn sorted_by(out: Seq<u32>, s: Seq<u32>, key: spec_fn(u32) -> int, nb: int) -> bool {
    &&& s.len() <= out.len()
    &&& forall|b: int| #![trigger bsel(s, key, b)] 0 <= b < nb ==>
            out.subrange(start(s, key, b), start(s, key, b + 1)) == bsel(s, key, b)
}

// ------------------------------------------------------------------------------------------------ basic lemmas

pub proof fn lemma_sumf_push(s: Seq<u32>, f: spec_fn(u32) -> int, x: u32)
    ensures sumf(s.push(x), f) == sumf(s, f) + f(x),
{
    assert(s.push(x).drop_last() =~= s);
}

pub proof fn lemma_sumf_append(a: Seq<u32>, b: Seq<u32>, f: spec_fn(u32) -> int)
    ensures sumf(a + b, f) == sumf(a, f) + sumf(b, f),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_sumf_append(a, b.drop_last(), f);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// The values of a prefix one longer.
pub proof fn lemma_sumf_take(s: Seq<u32>, f: spec_fn(u32) -> int, i: int)
    requires 0 <= i < s.len(),
    ensures sumf(s.take(i + 1), f) == sumf(s.take(i), f) + f(s[i]),
{
    assert(s.take(i + 1) =~= s.take(i).push(s[i]));
    lemma_sumf_push(s.take(i), f, s[i]);
}

/// Sums of nonnegative terms: a prefix sums to at most the whole, and every sum is nonnegative.
pub proof fn lemma_sumf_prefix_le(s: Seq<u32>, f: spec_fn(u32) -> int, i: int)
    requires
        0 <= i <= s.len(),
        forall|x: u32| #[trigger] f(x) >= 0,
    ensures 0 <= sumf(s.take(i), f) <= sumf(s, f),
    decreases s.len(),
{
    if i == s.len() {
        assert(s.take(i) =~= s);
        lemma_sumf_nonneg(s, f);
    } else {
        let d = s.drop_last();
        lemma_sumf_prefix_le(d, f, i);
        assert(d.take(i) =~= s.take(i));
    }
}

pub proof fn lemma_sumf_nonneg(s: Seq<u32>, f: spec_fn(u32) -> int)
    requires forall|x: u32| #[trigger] f(x) >= 0,
    ensures sumf(s, f) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_sumf_nonneg(s.drop_last(), f);
    }
}

/// Termwise `-g <= f <= g` carries over to the sums.
pub proof fn lemma_sumf_within(s: Seq<u32>, f: spec_fn(u32) -> int, g: spec_fn(u32) -> int)
    requires forall|x: u32| -#[trigger] g(x) <= f(x) <= g(x),
    ensures -sumf(s, g) <= sumf(s, f) <= sumf(s, g),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_sumf_within(s.drop_last(), f, g);
    }
}

/// Termwise `h == 0 ==> g == 0` with `h, g >= 0`: a zero `h` sum has a zero `g` sum.
pub proof fn lemma_sumf_zero_with(s: Seq<u32>, h: spec_fn(u32) -> int, g: spec_fn(u32) -> int)
    requires
        forall|x: u32| #[trigger] h(x) >= 0,
        forall|x: u32| #[trigger] g(x) >= 0,
        forall|x: u32| #[trigger] h(x) == 0 ==> g(x) == 0,
        sumf(s, h) == 0,
    ensures sumf(s, g) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_sumf_nonneg(s.drop_last(), h);
        lemma_sumf_zero_with(s.drop_last(), h, g);
    }
}

pub proof fn lemma_bsel_push(s: Seq<u32>, key: spec_fn(u32) -> int, b: int, x: u32)
    ensures bsel(s.push(x), key, b) == if key(x) == b { bsel(s, key, b).push(x) } else { bsel(s, key, b) },
{
    assert(s.push(x).drop_last() =~= s);
}

/// The count of a prefix is at most the count of the whole.
pub proof fn lemma_cnt_prefix(s: Seq<u32>, key: spec_fn(u32) -> int, b: int, i: int)
    requires 0 <= i <= s.len(),
    ensures cnt(s.take(i), key, b) <= cnt(s, key, b),
    decreases s.len(),
{
    if i == s.len() {
        assert(s.take(i) =~= s);
    } else {
        let d = s.drop_last();
        lemma_cnt_prefix(d, key, b, i);
        assert(d.take(i) =~= s.take(i));
    }
}

/// `sumb` over `lo .. hi` when one term grows by `d`.
pub proof fn lemma_sumb_bump(g: spec_fn(int) -> int, h: spec_fn(int) -> int, lo: int, hi: int, k: int, d: int)
    requires
        lo <= k < hi,
        forall|b: int| lo <= b < hi && b != k ==> #[trigger] h(b) == g(b),
        h(k) == g(k) + d,
    ensures sumb(h, lo, hi) == sumb(g, lo, hi) + d,
    decreases hi - lo,
{
    if hi - 1 == k {
        lemma_sumb_ext(g, h, lo, hi - 1);
    } else {
        lemma_sumb_bump(g, h, lo, hi - 1, k, d);
    }
}

/// `sumb` depends only on the terms in range.
pub proof fn lemma_sumb_ext(g: spec_fn(int) -> int, h: spec_fn(int) -> int, lo: int, hi: int)
    requires forall|b: int| lo <= b < hi ==> #[trigger] h(b) == g(b),
    ensures sumb(h, lo, hi) == sumb(g, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_sumb_ext(g, h, lo, hi - 1);
    }
}

/// `sumb` of nonnegative terms is monotone in `hi`.
pub proof fn lemma_sumb_mono(g: spec_fn(int) -> int, lo: int, h1: int, h2: int)
    requires
        lo <= h1 <= h2,
        forall|b: int| lo <= b < h2 ==> #[trigger] g(b) >= 0,
    ensures sumb(g, lo, h1) <= sumb(g, lo, h2),
    decreases h2 - h1,
{
    if h2 > h1 {
        lemma_sumb_mono(g, lo, h1, h2 - 1);
    }
}

/// Bucket starts are nondecreasing.
pub proof fn lemma_start_mono(s: Seq<u32>, key: spec_fn(u32) -> int, b1: int, b2: int)
    requires 0 <= b1 <= b2,
    ensures 0 <= start(s, key, b1) <= start(s, key, b2),
{
    lemma_sumb_mono(|c: int| cnt(s, key, c), 0, 0, b1);
    lemma_sumb_mono(|c: int| cnt(s, key, c), 0, b1, b2);
}

/// The next start is this start plus this bucket's count.
pub proof fn lemma_start_next(s: Seq<u32>, key: spec_fn(u32) -> int, b: int)
    requires 0 <= b,
    ensures start(s, key, b + 1) == start(s, key, b) + cnt(s, key, b),
{
}

// ------------------------------------------------------------------------------------------------ partition

/// Summing each bucket's values over every bucket sums every value; the bucket sizes add up to the length.
pub proof fn lemma_partition(s: Seq<u32>, key: spec_fn(u32) -> int, nb: int, f: spec_fn(u32) -> int)
    requires keys_in(s, key, nb),
    ensures
        sumb(|b: int| sumf(bsel(s, key, b), f), 0, nb) == sumf(s, f),
        start(s, key, nb) == s.len(),
    decreases s.len(),
{
    if s.len() == 0 {
        lemma_sumb_zero(|b: int| sumf(bsel(s, key, b), f), 0, nb);
        lemma_sumb_zero(|c: int| cnt(s, key, c), 0, nb);
    } else {
        let d = s.drop_last();
        let x = s.last();
        let k = key(x);
        assert(keys_in(d, key, nb)) by {
            assert forall|i: int| 0 <= i < d.len() implies 0 <= #[trigger] key(d[i]) < nb by {
                assert(d[i] == s[i]);
            }
        }
        lemma_partition(d, key, nb, f);
        assert(s =~= d.push(x));
        assert(0 <= k < nb) by {
            assert(s[s.len() - 1] == x);
        }
        let g1 = |b: int| sumf(bsel(d, key, b), f);
        let h1 = |b: int| sumf(bsel(s, key, b), f);
        assert forall|b: int| 0 <= b < nb && b != k implies #[trigger] h1(b) == g1(b) by {
            lemma_bsel_push(d, key, b, x);
        }
        lemma_bsel_push(d, key, k, x);
        lemma_sumf_push(bsel(d, key, k), f, x);
        lemma_sumb_bump(g1, h1, 0, nb, k, f(x));
        let g2 = |c: int| cnt(d, key, c);
        let h2 = |c: int| cnt(s, key, c);
        assert forall|b: int| 0 <= b < nb && b != k implies #[trigger] h2(b) == g2(b) by {
            lemma_bsel_push(d, key, b, x);
        }
        lemma_sumb_bump(g2, h2, 0, nb, k, 1);
        lemma_sumf_push(d, f, x);
    }
}

pub proof fn lemma_sumb_zero(g: spec_fn(int) -> int, lo: int, hi: int)
    requires forall|b: int| lo <= b < hi ==> #[trigger] g(b) == 0,
    ensures sumb(g, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_sumb_zero(g, lo, hi - 1);
    }
}

/// The sorted output's first `s.len()` slots sum like `s`.
pub proof fn lemma_sorted_sum(out: Seq<u32>, s: Seq<u32>, key: spec_fn(u32) -> int, nb: int, f: spec_fn(u32) -> int)
    requires
        0 <= nb,
        keys_in(s, key, nb),
        sorted_by(out, s, key, nb),
    ensures sumf(out.take(s.len() as int), f) == sumf(s, f),
{
    lemma_partition(s, key, nb, f);
    lemma_sorted_prefix(out, s, key, nb, f, nb);
}

/// Over the first `c` buckets: the slots `0 .. start(c)` sum like those buckets.
proof fn lemma_sorted_prefix(out: Seq<u32>, s: Seq<u32>, key: spec_fn(u32) -> int, nb: int, f: spec_fn(u32) -> int, c: int)
    requires
        0 <= c <= nb,
        keys_in(s, key, nb),
        sorted_by(out, s, key, nb),
        start(s, key, nb) == s.len(),
    ensures sumf(out.take(start(s, key, c)), f) == sumb(|b: int| sumf(bsel(s, key, b), f), 0, c),
    decreases c,
{
    lemma_start_mono(s, key, c, nb);
    if c == 0 {
        assert(out.take(0) =~= Seq::<u32>::empty());
    } else {
        lemma_sorted_prefix(out, s, key, nb, f, c - 1);
        let (a, b) = (start(s, key, c - 1), start(s, key, c));
        lemma_start_mono(s, key, c - 1, c);
        assert(out.take(b) =~= out.take(a) + out.subrange(a, b));
        lemma_sumf_append(out.take(a), out.subrange(a, b), f);
        let _ = bsel(s, key, c - 1);
        assert(out.subrange(a, b) == bsel(s, key, c - 1));
    }
}

// ------------------------------------------------------------------------------------------------ scatter

/// While scattering: `w` (a prefix of `s`) is written; bucket `b`'s cursor is `offs[b]`, its slots
/// `start(b) .. offs[b]` hold `w`'s values with key `b`.
pub open spec fn scatter_inv(out: Seq<u32>, offs: Seq<u32>, w: Seq<u32>, s: Seq<u32>, key: spec_fn(u32) -> int, nb: int) -> bool {
    &&& nb <= offs.len()
    &&& start(s, key, nb) <= out.len()
    &&& s.len() <= u32::MAX
    &&& w.len() <= s.len()
    &&& s.take(w.len() as int) == w
    &&& forall|b: int| 0 <= b < nb ==> #[trigger] offs[b] == start(s, key, b) + cnt(w, key, b)
    &&& forall|b: int| 0 <= b < nb ==> #[trigger] out.subrange(start(s, key, b), offs[b] as int) == bsel(w, key, b)
}

/// The scatter's start: cursors at the bucket starts, nothing written.
pub proof fn lemma_scatter_init(out: Seq<u32>, offs: Seq<u32>, s: Seq<u32>, key: spec_fn(u32) -> int, nb: int)
    requires
        nb <= offs.len(),
        start(s, key, nb) <= out.len(),
        s.len() <= u32::MAX,
        forall|b: int| 0 <= b < nb ==> #[trigger] offs[b] == start(s, key, b),
    ensures scatter_inv(out, offs, Seq::empty(), s, key, nb),
{
    assert(s.take(0) =~= Seq::<u32>::empty());
    assert forall|b: int| 0 <= b < nb implies #[trigger] out.subrange(start(s, key, b), offs[b] as int)
        == bsel(Seq::<u32>::empty(), key, b) by {
        lemma_start_mono(s, key, b, nb);
        assert(out.subrange(start(s, key, b), offs[b] as int) =~= Seq::<u32>::empty());
    }
}

/// Writing the next value `s[w.len()]` (key `k`) at its bucket's cursor and advancing the cursor.
pub proof fn lemma_scatter_step(out: Seq<u32>, offs: Seq<u32>, w: Seq<u32>, s: Seq<u32>, key: spec_fn(u32) -> int,
    nb: int, k: int)
    requires
        scatter_inv(out, offs, w, s, key, nb),
        keys_in(s, key, nb),
        w.len() < s.len(),
        k == key(s[w.len() as int]),
    ensures ({
        let x = s[w.len() as int];
        let p = offs[k] as int;
        &&& 0 <= k < nb
        &&& start(s, key, k) <= p < start(s, key, k + 1) <= start(s, key, nb)
        &&& scatter_inv(out.update(p, x), offs.update(k, (p + 1) as u32), w.push(x), s, key, nb)
    }),
{
    let x = s[w.len() as int];
    let i = w.len() as int;
    let w2 = w.push(x);
    let p = offs[k] as int;
    lemma_partition(s, key, nb, |y: u32| 0int);
    lemma_start_next(s, key, k);
    assert(s.take(i + 1) =~= w2);
    lemma_cnt_prefix(s, key, k, i + 1);
    lemma_bsel_push(w, key, k, x);
    lemma_start_mono(s, key, k + 1, nb);
    lemma_start_mono(s, key, 0, k);
    let out2 = out.update(p, x);
    let offs2 = offs.update(k, (p + 1) as u32);
    assert forall|b: int| 0 <= b < nb implies #[trigger] offs2[b] == start(s, key, b) + cnt(w2, key, b) by {
        lemma_bsel_push(w, key, b, x);
    }
    assert forall|b: int| 0 <= b < nb implies #[trigger] out2.subrange(start(s, key, b), offs2[b] as int)
        == bsel(w2, key, b) by {
        lemma_bsel_push(w, key, b, x);
        lemma_cnt_prefix(s, key, b, i);
        assert(s.take(i) =~= w);
        lemma_start_next(s, key, b);
        lemma_start_mono(s, key, b, nb);
        lemma_start_mono(s, key, b + 1, nb);
        if b == k {
            assert(out2.subrange(start(s, key, b), offs2[b] as int)
                =~= out.subrange(start(s, key, b), offs[b] as int).push(x));
        } else if b < k {
            lemma_start_mono(s, key, b + 1, k);
            assert(out2.subrange(start(s, key, b), offs2[b] as int) =~= out.subrange(start(s, key, b), offs[b] as int));
        } else {
            lemma_start_mono(s, key, k + 1, b);
            lemma_start_mono(s, key, b, nb);
            assert(out2.subrange(start(s, key, b), offs2[b] as int) =~= out.subrange(start(s, key, b), offs[b] as int));
        }
    }
}

/// Every value written: `out` is sorted.
pub proof fn lemma_scatter_done(out: Seq<u32>, offs: Seq<u32>, s: Seq<u32>, key: spec_fn(u32) -> int, nb: int)
    requires
        scatter_inv(out, offs, s, s, key, nb),
        keys_in(s, key, nb),
    ensures sorted_by(out, s, key, nb),
{
    lemma_partition(s, key, nb, |x: u32| 0int);
    assert forall|b: int| #![trigger bsel(s, key, b)] 0 <= b < nb implies
        out.subrange(start(s, key, b), start(s, key, b + 1)) == bsel(s, key, b) by {
        lemma_start_next(s, key, b);
        assert(out.subrange(start(s, key, b), offs[b] as int) == bsel(s, key, b));
    }
}

// ------------------------------------------------------------------------------------------------ bucket starts

/// Turns the per-bucket counts `offs[0 .. nb]` of `s` into the bucket starts, in place.
pub fn counts_to_starts(offs: &mut Vec<u32>, nb: usize, Ghost(s): Ghost<Seq<u32>>, Ghost(key): Ghost<spec_fn(u32) -> int>)
    requires
        nb <= old(offs)@.len(),
        keys_in(s, key, nb as int),
        s.len() <= u32::MAX,
        forall|b: int| 0 <= b < nb ==> #[trigger] old(offs)@[b] == cnt(s, key, b),
    ensures
        final(offs)@.len() == old(offs)@.len(),
        forall|b: int| 0 <= b < nb ==> #[trigger] final(offs)@[b] == start(s, key, b),
    no_unwind
{
    proof {
        lemma_partition(s, key, nb as int, |x: u32| 0int);
    }
    let ghost o0 = offs@;
    let mut run: u32 = 0;
    let mut b: usize = 0;
    while b < nb
        invariant
            nb <= offs@.len(),
            offs@.len() == o0.len(),
            b <= nb,
            start(s, key, nb as int) == s.len(),
            s.len() <= u32::MAX,
            run == start(s, key, b as int),
            forall|c: int| 0 <= c < b ==> #[trigger] offs@[c] == start(s, key, c),
            forall|c: int| b <= c < nb ==> #[trigger] offs@[c] == cnt(s, key, c),
        decreases nb - b,
    {
        let c = offs[b];
        proof {
            lemma_start_mono(s, key, b + 1, nb as int);
        }
        crate::gendb_entry::work::put(offs, b, run);
        run = run + c;
        b = b + 1;
    }
}

} // verus!
