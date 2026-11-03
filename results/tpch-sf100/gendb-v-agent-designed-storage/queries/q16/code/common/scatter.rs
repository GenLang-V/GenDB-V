//! Stable counting sort of `(key, value)` pairs by key into a preallocated buffer, without allocation (usable in
//! worker bodies).
//!
//! Input: `keys[0 .. n]` (each below `nk`) and `vals[0 .. n]`. Output: `offs` (`nk + 1` entries, from 0 to `n`,
//! nondecreasing) and `out`, where `out[offs[g] .. offs[g + 1]]` is exactly `sel(keys, vals, n, g)`, the values whose
//! key is `g` in input order (`scattered`). The pass counts every key, turns the counts into starts, writes every
//! value at its key's cursor (`offs[g]` moves to the end of key `g`'s segment) and shifts the cursors back to starts.
use vstd::prelude::*;

verus! {

/// A key type: its value as a `usize` index.
pub trait KeyIdx: Copy {
    spec fn ix(&self) -> nat;

    fn to_usize(&self) -> (r: usize)
        ensures r == self.ix(),
        no_unwind;
}

impl KeyIdx for u32 {
    open spec fn ix(&self) -> nat {
        *self as nat
    }

    fn to_usize(&self) -> (r: usize) {
        *self as usize
    }
}

impl KeyIdx for usize {
    open spec fn ix(&self) -> nat {
        *self as nat
    }

    fn to_usize(&self) -> (r: usize) {
        *self
    }
}

/// The values of the first `n` pairs whose key is `g`, in input order.
pub open spec fn sel<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, g: int) -> Seq<V>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else if keys[n - 1].ix() == g {
        sel(keys, vals, n - 1, g).push(vals[n - 1])
    } else {
        sel(keys, vals, n - 1, g)
    }
}

/// The number of the first `n` pairs whose key is `g`.
pub open spec fn cnt<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, g: int) -> int {
    sel(keys, vals, n, g).len() as int
}

/// Start of key `g`'s segment: the pairs with a smaller key.
pub open spec fn start<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, g: int) -> int
    decreases g,
{
    if g <= 0 { 0 } else { start(keys, vals, n, g - 1) + cnt(keys, vals, n, g - 1) }
}

/// The output of the sort: offsets from 0 to `n`, and every key's segment holds its values in input order.
pub open spec fn scattered<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, nk: int, offs: Seq<usize>, out: Seq<V>) -> bool {
    &&& offs.len() == nk + 1
    &&& offs[0] == 0
    &&& offs[nk] == n
    &&& n <= out.len()
    &&& forall|g: int| 0 <= g < nk ==> #[trigger] offs[g] <= offs[g + 1]
    &&& forall|g: int| 0 <= g < nk ==> out.subrange(#[trigger] offs[g] as int, offs[g + 1] as int) == sel(keys, vals, n, g)
}

proof fn lemma_sel_step<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, g: int)
    requires n >= 0,
    ensures
        sel(keys, vals, n + 1, g) == if keys[n].ix() == g { sel(keys, vals, n, g).push(vals[n]) } else { sel(keys, vals, n, g) },
{
}

/// A value of `sel(keys, vals, n, g)` is the value of some pair below `n` with key `g`, and every such value is one.
pub proof fn lemma_sel_mem<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, g: int, v: V)
    requires 0 <= n <= keys.len(), n <= vals.len(),
    ensures sel(keys, vals, n, g).contains(v) <==> exists|k: int| 0 <= k < n && keys[k].ix() == g && #[trigger] vals[k] == v,
    decreases n,
{
    if n > 0 {
        lemma_sel_mem(keys, vals, n - 1, g, v);
        lemma_sel_step(keys, vals, n - 1, g);
        let s0 = sel(keys, vals, n - 1, g);
        let s1 = sel(keys, vals, n, g);
        if keys[n - 1].ix() == g {
            assert(s1 == s0.push(vals[n - 1]));
            if s1.contains(v) {
                let w = choose|w: int| 0 <= w < s1.len() && s1[w] == v;
                if w < s0.len() {
                    assert(s0[w] == v);
                    assert(s0.contains(v));
                } else {
                    assert(vals[n - 1] == v);
                }
            }
            if s0.contains(v) {
                let w = choose|w: int| 0 <= w < s0.len() && s0[w] == v;
                assert(s1[w] == v);
            }
            if vals[n - 1] == v {
                assert(s1[s0.len() as int] == v);
            }
        } else {
            assert(s1 == s0);
        }
        if exists|k: int| 0 <= k < n && keys[k].ix() == g && #[trigger] vals[k] == v {
            let k = choose|k: int| 0 <= k < n && keys[k].ix() == g && #[trigger] vals[k] == v;
            if k < n - 1 {
                assert(exists|k2: int| 0 <= k2 < n - 1 && keys[k2].ix() == g && #[trigger] vals[k2] == v);
            }
        }
    } else {
        assert(sel(keys, vals, 0, g) =~= Seq::<V>::empty());
    }
}

/// The offsets of a sort lie between 0 and the pair count.
pub proof fn lemma_offs_le<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, nk: int, offs: Seq<usize>, out: Seq<V>, g: int)
    requires scattered(keys, vals, n, nk, offs, out), 0 <= g <= nk,
    ensures 0 <= offs[g] <= n,
    decreases nk - g,
{
    if g < nk {
        lemma_offs_le(keys, vals, n, nk, offs, out, g + 1);
        assert(offs[g] <= offs[g + 1]);
    }
}

/// Counts grow with the prefix.
proof fn lemma_cnt_mono<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, a: int, b: int, g: int)
    requires 0 <= a <= b,
    ensures cnt(keys, vals, a, g) <= cnt(keys, vals, b, g),
    decreases b - a,
{
    if a < b {
        lemma_cnt_mono(keys, vals, a, b - 1, g);
        lemma_sel_step(keys, vals, b - 1, g);
    }
}

/// Starts are nondecreasing.
proof fn lemma_start_mono<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, a: int, b: int)
    requires 0 <= a <= b,
    ensures start(keys, vals, n, a) <= start(keys, vals, n, b),
    decreases b - a,
{
    if a < b {
        lemma_start_mono(keys, vals, n, a, b - 1);
    }
}

/// The counts of all keys below `nk` add up to `n` when every key is below `nk`.
proof fn lemma_start_total<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, nk: int)
    requires
        0 <= n <= keys.len(),
        nk >= 0,
        forall|k: int| 0 <= k < n ==> (#[trigger] keys[k]).ix() < nk,
    ensures start(keys, vals, n, nk) == n,
    decreases n,
{
    if n > 0 {
        lemma_start_total(keys, vals, n - 1, nk);
        // start(n, g) = start(n - 1, g) + [keys[n - 1] < g] for every g.
        lemma_start_shift(keys, vals, n - 1, nk);
    } else {
        lemma_start_zero(keys, vals, nk);
    }
}

proof fn lemma_start_zero<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, g: int)
    requires g >= 0,
    ensures start(keys, vals, 0, g) == 0,
    decreases g,
{
    if g > 0 {
        lemma_start_zero(keys, vals, g - 1);
    }
}

/// Adding pair `n` adds one to the start of every key above its key.
proof fn lemma_start_shift<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, g: int)
    requires 0 <= n, g >= 0,
    ensures start(keys, vals, n + 1, g) == start(keys, vals, n, g) + if keys[n].ix() < g { 1int } else { 0int },
    decreases g,
{
    if g > 0 {
        lemma_start_shift(keys, vals, n, g - 1);
        lemma_sel_step(keys, vals, n, g - 1);
    }
}

/// Counting: after the first `k` pairs, `offs[g + 1]` is the count of key `g` (and `offs[0]` is 0).
pub open spec fn counted<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, k: int, nk: int, offs: Seq<usize>) -> bool {
    &&& offs.len() == nk + 1
    &&& offs[0] == 0
    &&& forall|g: int| 0 <= g < nk ==> #[trigger] offs[g + 1] == cnt(keys, vals, k, g)
}

/// Scattering: after the first `k` pairs, every key's cursor is its start plus its count so far, and its filled
/// prefix holds its values so far.
pub open spec fn placing<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, k: int, nk: int, offs: Seq<usize>, out: Seq<V>) -> bool {
    &&& offs.len() == nk + 1
    &&& forall|g: int| 0 <= g < nk ==> #[trigger] offs[g] == start(keys, vals, n, g) + cnt(keys, vals, k, g)
    &&& forall|g: int| 0 <= g < nk ==> out.subrange(start(keys, vals, n, g), #[trigger] offs[g] as int) == sel(keys, vals, k, g)
}

/// Writing pair `k` at its key's cursor keeps every other key's filled prefix.
proof fn lemma_place_step<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, k: int, nk: int, offs: Seq<usize>,
    out: Seq<V>)
    requires
        0 <= k < n <= keys.len(),
        n <= usize::MAX,
        nk >= 0,
        n <= vals.len(),
        forall|q: int| 0 <= q < n ==> (#[trigger] keys[q]).ix() < nk,
        placing(keys, vals, n, k, nk, offs, out),
        n <= out.len(),
    ensures ({
        let g = keys[k].ix() as int;
        let p = offs[g] as int;
        &&& start(keys, vals, n, g) <= p < start(keys, vals, n, g + 1)
        &&& p < out.len()
        &&& placing(keys, vals, n, k + 1, nk, offs.update(g, (p + 1) as usize), out.update(p, vals[k]))
    }),
{
    let g = keys[k].ix() as int;
    let p = offs[g] as int;
    lemma_sel_step(keys, vals, k, g);
    lemma_cnt_mono(keys, vals, k + 1, n, g);
    lemma_start_mono(keys, vals, n, g + 1, nk);
    lemma_start_total(keys, vals, n, nk);
    lemma_start_mono(keys, vals, n, g, g + 1);
    assert(start(keys, vals, n, g + 1) == start(keys, vals, n, g) + cnt(keys, vals, n, g));
    assert(p + 1 <= n);
    let offs2 = offs.update(g, (p + 1) as usize);
    let out2 = out.update(p, vals[k]);
    assert forall|h: int| 0 <= h < nk implies #[trigger] offs2[h] == start(keys, vals, n, h) + cnt(keys, vals, k + 1, h) by {
        lemma_sel_step(keys, vals, k, h);
    }
    assert forall|h: int| 0 <= h < nk implies out2.subrange(start(keys, vals, n, h), #[trigger] offs2[h] as int)
        == sel(keys, vals, k + 1, h) by {
        lemma_sel_step(keys, vals, k, h);
        let sh = start(keys, vals, n, h);
        lemma_start_mono(keys, vals, n, 0, h);
        lemma_cnt_mono(keys, vals, k, n, h);
        lemma_start_mono(keys, vals, n, h, h + 1);
        lemma_start_mono(keys, vals, n, h + 1, nk);
        if h == g {
            assert(offs[g] == sh + cnt(keys, vals, k, g));
            assert(sh <= p < out.len());
            assert(out2.subrange(sh, p + 1) =~= out.subrange(sh, p).push(vals[k])) by {
                assert forall|q: int| 0 <= q < p + 1 - sh implies #[trigger] out2.subrange(sh, p + 1)[q]
                    == out.subrange(sh, p).push(vals[k])[q] by {
                    if q < p - sh {
                        assert(out2[sh + q] == out[sh + q]);
                    }
                }
            }
        } else {
            // Key h's filled prefix lies in its own segment, which does not hold p.
            lemma_cnt_mono(keys, vals, k, n, h);
            if h < g {
                lemma_start_mono(keys, vals, n, h + 1, g);
            } else {
                lemma_start_mono(keys, vals, n, g + 1, h);
            }
            let e = offs[h] as int;
            assert(e == sh + cnt(keys, vals, k, h));
            assert(sh <= e <= out.len());
            assert(p < sh || p >= e);
            assert(out2.subrange(sh, e) =~= out.subrange(sh, e)) by {
                assert forall|q: int| 0 <= q < e - sh implies #[trigger] out2.subrange(sh, e)[q] == out.subrange(sh, e)[q] by {
                    assert(out2[sh + q] == out[sh + q]);
                }
            }
        }
    }
}

/// Sorts the first `n` pairs by key (stable) into `out` with the segment offsets in `offs`.
pub fn scatter<K: KeyIdx, V: Copy>(keys: &Vec<K>, vals: &Vec<V>, n: usize, nk: usize, offs: &mut Vec<usize>,
    out: &mut Vec<V>)
    requires
        n <= keys@.len(),
        n <= vals@.len(),
        n <= old(out)@.len(),
        old(offs)@.len() == nk + 1,
        nk < usize::MAX,
        forall|g: int| 0 <= g <= nk ==> #[trigger] old(offs)@[g] == 0,
        forall|k: int| 0 <= k < n ==> (#[trigger] keys@[k]).ix() < nk,
    ensures
        final(out)@.len() == old(out)@.len(),
        scattered(keys@, vals@, n as int, nk as int, final(offs)@, final(out)@),
    no_unwind
{
    let ghost ks = keys@;
    let ghost vs = vals@;
    // Counts.
    let mut k: usize = 0;
    proof {
        assert forall|g: int| 0 <= g < nk implies #[trigger] offs@[g + 1] == cnt(ks, vs, 0, g) by {}
    }
    while k < n
        invariant
            n <= ks.len(), n <= vs.len(), ks == keys@, vs == vals@,
            k <= n,
            forall|q: int| 0 <= q < n ==> (#[trigger] ks[q]).ix() < nk,
            counted(ks, vs, k as int, nk as int, offs@),
        decreases n - k,
    {
        let g = keys[k].to_usize();
        proof {
            lemma_sel_step(ks, vs, k as int, g as int);
            lemma_cnt_mono(ks, vs, k as int + 1, n as int, g as int);
            assert(cnt(ks, vs, n as int, g as int) <= n) by {
                lemma_cnt_bound(ks, vs, n as int, g as int);
            }
        }
        let c = offs[g + 1];
        offs[g + 1] = c + 1;
        proof {
            assert forall|h: int| 0 <= h < nk implies #[trigger] offs@[h + 1] == cnt(ks, vs, k + 1, h) by {
                lemma_sel_step(ks, vs, k as int, h);
            }
        }
        k = k + 1;
    }
    // Starts.
    let mut g: usize = 0;
    proof {
        lemma_start_total(ks, vs, n as int, nk as int);
        assert forall|h: int| 0 < h <= nk implies #[trigger] offs@[h] == cnt(ks, vs, n as int, h - 1) by {
            assert(offs@[(h - 1) + 1] == cnt(ks, vs, n as int, h - 1));
        }
    }
    while g < nk
        invariant
            n <= ks.len(), ks == keys@, vs == vals@,
            g <= nk,
            forall|q: int| 0 <= q < n ==> (#[trigger] ks[q]).ix() < nk,
            offs@.len() == nk + 1,
            start(ks, vs, n as int, nk as int) == n,
            forall|h: int| 0 <= h <= g ==> #[trigger] offs@[h] == start(ks, vs, n as int, h),
            forall|h: int| g < h <= nk ==> #[trigger] offs@[h] == cnt(ks, vs, n as int, h - 1),
        decreases nk - g,
    {
        proof {
            lemma_start_mono(ks, vs, n as int, g as int + 1, nk as int);
        }
        let a = offs[g];
        let b = offs[g + 1];
        offs[g + 1] = a + b;
        g = g + 1;
    }
    // Scatter.
    let ghost out0 = out@;
    proof {
        assert forall|h: int| 0 <= h < nk implies #[trigger] offs@[h] == start(ks, vs, n as int, h) + cnt(ks, vs, 0, h) by {}
        assert forall|h: int| 0 <= h < nk implies out@.subrange(start(ks, vs, n as int, h), #[trigger] offs@[h] as int)
            == sel(ks, vs, 0, h) by {
            lemma_start_mono(ks, vs, n as int, h, nk as int);
            assert(out@.subrange(start(ks, vs, n as int, h), offs@[h] as int) =~= Seq::<V>::empty());
        }
    }
    let mut k: usize = 0;
    while k < n
        invariant
            n <= ks.len(), n <= vs.len(), ks == keys@, vs == vals@,
            k <= n,
            n <= out@.len(), out@.len() == out0.len(),
            forall|q: int| 0 <= q < n ==> (#[trigger] ks[q]).ix() < nk,
            placing(ks, vs, n as int, k as int, nk as int, offs@, out@),
            offs@[nk as int] == n,
        decreases n - k,
    {
        let g = keys[k].to_usize();
        proof {
            lemma_place_step(ks, vs, n as int, k as int, nk as int, offs@, out@);
            lemma_start_mono(ks, vs, n as int, g as int + 1, nk as int);
            lemma_start_total(ks, vs, n as int, nk as int);
        }
        let p = offs[g];
        out[p] = vals[k];
        offs[g] = p + 1;
        k = k + 1;
    }
    // Every cursor ended at its key's end, the next key's start: shift back.
    proof {
        assert forall|h: int| 0 <= h < nk implies #[trigger] offs@[h] == start(ks, vs, n as int, h + 1) by {}
        assert forall|h: int| 0 <= h < nk implies out@.subrange(start(ks, vs, n as int, h), start(ks, vs, n as int, h + 1))
            == #[trigger] sel(ks, vs, n as int, h) by {
            assert(offs@[h] == start(ks, vs, n as int, h + 1));
            lemma_start_mono(ks, vs, n as int, h, h + 1);
            lemma_start_mono(ks, vs, n as int, h + 1, nk as int);
        }
    }
    let ghost outf = out@;
    let mut h: usize = nk;
    while h > 0
        invariant
            ks == keys@, vs == vals@,
            h <= nk,
            offs@.len() == nk + 1,
            out@ == outf,
            start(ks, vs, n as int, nk as int) == n,
            forall|q: int| 0 <= q < h ==> #[trigger] offs@[q] == start(ks, vs, n as int, q + 1),
            forall|q: int| h < q <= nk ==> #[trigger] offs@[q] == start(ks, vs, n as int, q),
            h == nk ==> offs@[nk as int] == n,
        decreases h,
    {
        let v = offs[h - 1];
        offs[h] = v;
        h = h - 1;
    }
    offs[0] = 0;
    proof {
        lemma_start_total(ks, vs, n as int, nk as int);
        assert(offs@[nk as int] == start(ks, vs, n as int, nk as int));
        assert forall|q: int| 0 <= q < nk implies #[trigger] offs@[q] <= offs@[q + 1] by {
            lemma_start_mono(ks, vs, n as int, q, q + 1);
        }
        assert forall|q: int| 0 <= q < nk implies out@.subrange(#[trigger] offs@[q] as int, offs@[q + 1] as int)
            == sel(ks, vs, n as int, q) by {
            assert(offs@[q] == start(ks, vs, n as int, q));
            assert(offs@[q + 1] == start(ks, vs, n as int, q + 1));
            assert(outf.subrange(start(ks, vs, n as int, q), start(ks, vs, n as int, q + 1)) == sel(ks, vs, n as int, q));
        }
    }
}

/// The keys of `scatter_hi`: the high bits `v >> sh` of every value.
pub open spec fn hi_keys(vals: Seq<u32>, sh: u32) -> Seq<usize> {
    Seq::new(vals.len(), |k: int| (vals[k] >> sh) as usize)
}

/// Sorts the first `n` values by their high bits `v >> sh` (stable) into `out` with the segment offsets in `offs`:
/// `scatter` with the keys `hi_keys(vals, sh)` computed on the fly.
pub fn scatter_hi(vals: &Vec<u32>, sh: u32, n: usize, nk: usize, offs: &mut Vec<usize>, out: &mut Vec<u32>)
    requires
        sh < 32,
        n <= vals@.len(),
        n <= old(out)@.len(),
        old(offs)@.len() == nk + 1,
        nk < usize::MAX,
        forall|g: int| 0 <= g <= nk ==> #[trigger] old(offs)@[g] == 0,
        forall|k: int| 0 <= k < n ==> ((#[trigger] vals@[k] >> sh) as int) < nk,
    ensures
        final(out)@.len() == old(out)@.len(),
        scattered(hi_keys(vals@, sh), vals@, n as int, nk as int, final(offs)@, final(out)@),
    no_unwind
{
    let ghost ks = hi_keys(vals@, sh);
    let ghost vs = vals@;
    proof {
        assert forall|q: int| 0 <= q < n implies (#[trigger] ks[q]).ix() < nk by {
            assert(ks[q] == (vals@[q] >> sh) as usize);
        }
    }
    // Counts.
    let mut k: usize = 0;
    proof {
        assert forall|g: int| 0 <= g < nk implies #[trigger] offs@[g + 1] == cnt(ks, vs, 0, g) by {}
    }
    while k < n
        invariant
            sh < 32,
            n <= ks.len(), n <= vs.len(), ks == hi_keys(vals@, sh), vs == vals@,
            k <= n,
            forall|q: int| 0 <= q < n ==> (#[trigger] ks[q]).ix() < nk,
            counted(ks, vs, k as int, nk as int, offs@),
        decreases n - k,
    {
        let g = (vals[k] >> sh) as usize;
        proof {
            assert(ks[k as int] == g);
            lemma_sel_step(ks, vs, k as int, g as int);
            lemma_cnt_mono(ks, vs, k as int + 1, n as int, g as int);
            assert(cnt(ks, vs, n as int, g as int) <= n) by {
                lemma_cnt_bound(ks, vs, n as int, g as int);
            }
        }
        let c = offs[g + 1];
        offs[g + 1] = c + 1;
        proof {
            assert forall|h: int| 0 <= h < nk implies #[trigger] offs@[h + 1] == cnt(ks, vs, k + 1, h) by {
                lemma_sel_step(ks, vs, k as int, h);
            }
        }
        k = k + 1;
    }
    // Starts.
    let mut g: usize = 0;
    proof {
        lemma_start_total(ks, vs, n as int, nk as int);
        assert forall|h: int| 0 < h <= nk implies #[trigger] offs@[h] == cnt(ks, vs, n as int, h - 1) by {
            assert(offs@[(h - 1) + 1] == cnt(ks, vs, n as int, h - 1));
        }
    }
    while g < nk
        invariant
            n <= ks.len(), ks == hi_keys(vals@, sh), vs == vals@,
            g <= nk,
            forall|q: int| 0 <= q < n ==> (#[trigger] ks[q]).ix() < nk,
            offs@.len() == nk + 1,
            start(ks, vs, n as int, nk as int) == n,
            forall|h: int| 0 <= h <= g ==> #[trigger] offs@[h] == start(ks, vs, n as int, h),
            forall|h: int| g < h <= nk ==> #[trigger] offs@[h] == cnt(ks, vs, n as int, h - 1),
        decreases nk - g,
    {
        proof {
            lemma_start_mono(ks, vs, n as int, g as int + 1, nk as int);
        }
        let a = offs[g];
        let b = offs[g + 1];
        offs[g + 1] = a + b;
        g = g + 1;
    }
    // Scatter.
    let ghost out0 = out@;
    proof {
        assert forall|h: int| 0 <= h < nk implies #[trigger] offs@[h] == start(ks, vs, n as int, h) + cnt(ks, vs, 0, h) by {}
        assert forall|h: int| 0 <= h < nk implies out@.subrange(start(ks, vs, n as int, h), #[trigger] offs@[h] as int)
            == sel(ks, vs, 0, h) by {
            lemma_start_mono(ks, vs, n as int, h, nk as int);
            assert(out@.subrange(start(ks, vs, n as int, h), offs@[h] as int) =~= Seq::<u32>::empty());
        }
    }
    let mut k: usize = 0;
    while k < n
        invariant
            sh < 32,
            n <= ks.len(), n <= vs.len(), ks == hi_keys(vals@, sh), vs == vals@,
            k <= n,
            n <= out@.len(), out@.len() == out0.len(),
            forall|q: int| 0 <= q < n ==> (#[trigger] ks[q]).ix() < nk,
            placing(ks, vs, n as int, k as int, nk as int, offs@, out@),
            offs@[nk as int] == n,
        decreases n - k,
    {
        let g = (vals[k] >> sh) as usize;
        proof {
            assert(ks[k as int] == g);
            lemma_place_step(ks, vs, n as int, k as int, nk as int, offs@, out@);
            lemma_start_mono(ks, vs, n as int, g as int + 1, nk as int);
            lemma_start_total(ks, vs, n as int, nk as int);
        }
        let p = offs[g];
        out[p] = vals[k];
        offs[g] = p + 1;
        k = k + 1;
    }
    // Every cursor ended at its key's end, the next key's start: shift back.
    proof {
        assert forall|h: int| 0 <= h < nk implies #[trigger] offs@[h] == start(ks, vs, n as int, h + 1) by {}
        assert forall|h: int| 0 <= h < nk implies out@.subrange(start(ks, vs, n as int, h), start(ks, vs, n as int, h + 1))
            == #[trigger] sel(ks, vs, n as int, h) by {
            assert(offs@[h] == start(ks, vs, n as int, h + 1));
            lemma_start_mono(ks, vs, n as int, h, h + 1);
            lemma_start_mono(ks, vs, n as int, h + 1, nk as int);
        }
    }
    let ghost outf = out@;
    let mut h: usize = nk;
    while h > 0
        invariant
            ks == hi_keys(vals@, sh), vs == vals@,
            h <= nk,
            offs@.len() == nk + 1,
            out@ == outf,
            start(ks, vs, n as int, nk as int) == n,
            forall|q: int| 0 <= q < h ==> #[trigger] offs@[q] == start(ks, vs, n as int, q + 1),
            forall|q: int| h < q <= nk ==> #[trigger] offs@[q] == start(ks, vs, n as int, q),
            h == nk ==> offs@[nk as int] == n,
        decreases h,
    {
        let v = offs[h - 1];
        offs[h] = v;
        h = h - 1;
    }
    offs[0] = 0;
    proof {
        lemma_start_total(ks, vs, n as int, nk as int);
        assert(offs@[nk as int] == start(ks, vs, n as int, nk as int));
        assert forall|q: int| 0 <= q < nk implies #[trigger] offs@[q] <= offs@[q + 1] by {
            lemma_start_mono(ks, vs, n as int, q, q + 1);
        }
        assert forall|q: int| 0 <= q < nk implies out@.subrange(#[trigger] offs@[q] as int, offs@[q + 1] as int)
            == sel(ks, vs, n as int, q) by {
            assert(offs@[q] == start(ks, vs, n as int, q));
            assert(offs@[q + 1] == start(ks, vs, n as int, q + 1));
            assert(outf.subrange(start(ks, vs, n as int, q), start(ks, vs, n as int, q + 1)) == sel(ks, vs, n as int, q));
        }
    }
}

/// A count is at most the number of pairs.
proof fn lemma_cnt_bound<K: KeyIdx, V>(keys: Seq<K>, vals: Seq<V>, n: int, g: int)
    requires n >= 0,
    ensures cnt(keys, vals, n, g) <= n,
    decreases n,
{
    if n > 0 {
        lemma_cnt_bound(keys, vals, n - 1, g);
        lemma_sel_step(keys, vals, n - 1, g);
    }
}

} // verus!
