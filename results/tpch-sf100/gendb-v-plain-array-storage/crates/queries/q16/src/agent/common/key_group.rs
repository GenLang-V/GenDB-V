//! Grouping of packed entries by key (a counting sort, `no_unwind`, preallocated buffers): an entry `e: u64` holds
//! the key `(e >> 32) - base` and the value `e & 0xFFFF_FFFF`. `group_by_key` writes the values of every key `k`
//! (keys `0..ng`) into one segment of `vals`, in input order: segment `k` is `kstart(k) .. kstart(k + 1)` and holds
//! `kvals(k)`; afterwards `ends[k] == kstart(k + 1)`.
use vstd::prelude::*;

verus! {

/// The key and the value of an entry.
pub open spec fn ekey(e: u64, base: int) -> int {
    (e >> 32u64) as int - base
}

pub open spec fn evalue(e: u64) -> u32 {
    (e & 0xFFFF_FFFFu64) as u32
}

/// Number of entries with key `k`.
pub open spec fn kcount(es: Seq<u64>, base: int, k: int) -> nat
    decreases es.len(),
{
    if es.len() == 0 { 0 } else { kcount(es.drop_last(), base, k) + if ekey(es.last(), base) == k { 1nat } else { 0nat } }
}

/// The values with key `k`, in order.
pub open spec fn kvals(es: Seq<u64>, base: int, k: int) -> Seq<u32>
    decreases es.len(),
{
    if es.len() == 0 {
        Seq::empty()
    } else {
        let v = kvals(es.drop_last(), base, k);
        if ekey(es.last(), base) == k { v.push(evalue(es.last())) } else { v }
    }
}

/// Start of segment `k`: the entries with smaller keys.
pub open spec fn kstart(es: Seq<u64>, base: int, k: int) -> nat
    decreases k,
{
    if k <= 0 { 0 } else { kstart(es, base, k - 1) + kcount(es, base, k - 1) }
}

/// Every key lies in `0..ng`.
pub open spec fn keys_in(es: Seq<u64>, base: int, ng: int) -> bool {
    forall|i: int| 0 <= i < es.len() ==> 0 <= #[trigger] ekey(es[i], base) < ng
}

/// `kvals` has `kcount` values.
pub proof fn lemma_kvals_len(es: Seq<u64>, base: int, k: int)
    ensures kvals(es, base, k).len() == kcount(es, base, k),
    decreases es.len(),
{
    if es.len() > 0 { lemma_kvals_len(es.drop_last(), base, k); }
}

/// One more entry: the counts and values of its key grow by it.
pub proof fn lemma_step(es: Seq<u64>, base: int, i: int, k: int)
    requires 0 <= i < es.len(),
    ensures
        kcount(es.take(i + 1), base, k) == kcount(es.take(i), base, k) + if ekey(es[i], base) == k { 1nat } else { 0nat },
        kvals(es.take(i + 1), base, k) == if ekey(es[i], base) == k { kvals(es.take(i), base, k).push(evalue(es[i])) } else { kvals(es.take(i), base, k) },
{
    assert(es.take(i + 1).drop_last() =~= es.take(i));
    assert(es.take(i + 1).last() == es[i]);
}

/// Counts of a prefix are at most the counts of the whole.
pub proof fn lemma_count_prefix(es: Seq<u64>, base: int, i: int, k: int)
    requires 0 <= i <= es.len(),
    ensures kcount(es.take(i), base, k) <= kcount(es, base, k),
    decreases es.len() - i,
{
    if i < es.len() {
        lemma_count_prefix(es, base, i + 1, k);
        lemma_step(es, base, i, k);
    } else {
        assert(es.take(i) =~= es);
    }
}

/// The segments are ordered: segment `k1` ends no later than segment `k2 > k1` starts.
pub proof fn lemma_start_mono(es: Seq<u64>, base: int, k1: int, k2: int)
    requires 0 <= k1 < k2,
    ensures kstart(es, base, k1) + kcount(es, base, k1) <= kstart(es, base, k2),
    decreases k2 - k1,
{
    if k2 > k1 + 1 {
        lemma_start_mono(es, base, k1, k2 - 1);
    }
}

/// Every segment `k < ng` ends by `kstart(ng)`.
pub proof fn lemma_segment_end(es: Seq<u64>, base: int, k: int, ng: int)
    requires 0 <= k < ng,
    ensures kstart(es, base, k) + kcount(es, base, k) <= kstart(es, base, ng),
{
    if k + 1 < ng {
        lemma_start_mono(es, base, k, ng);
    } else {
        assert(kstart(es, base, ng) == kstart(es, base, ng - 1) + kcount(es, base, ng - 1));
    }
}

/// All entries: the segments of the keys `0..ng` end at `|es|`.
pub proof fn lemma_total(es: Seq<u64>, base: int, ng: int)
    requires keys_in(es, base, ng), ng >= 0,
    ensures kstart(es, base, ng) == es.len(),
    decreases es.len(),
{
    if es.len() > 0 {
        let d = es.drop_last();
        assert(keys_in(d, base, ng)) by {
            assert forall|i: int| 0 <= i < d.len() implies 0 <= #[trigger] ekey(d[i], base) < ng by { assert(d[i] == es[i]); }
        }
        lemma_total(d, base, ng);
        let k0 = ekey(es.last(), base);
        assert(0 <= k0 < ng) by { assert(es.last() == es[es.len() - 1]); }
        lemma_start_grow(es, base, k0, ng);
    } else {
        lemma_start_empty(es, base, ng);
    }
}

proof fn lemma_start_empty(es: Seq<u64>, base: int, k: int)
    requires es.len() == 0,
    ensures kstart(es, base, k) == 0,
    decreases k,
{
    if k > 0 { lemma_start_empty(es, base, k - 1); }
}

/// Adding the last entry (key `k0 < k`) raises `kstart(k)` by one.
proof fn lemma_start_grow(es: Seq<u64>, base: int, k0: int, k: int)
    requires es.len() > 0, ekey(es.last(), base) == k0, 0 <= k0 < k,
    ensures kstart(es, base, k) == kstart(es.drop_last(), base, k) + 1,
    decreases k,
{
    let d = es.drop_last();
    if k - 1 > k0 {
        lemma_start_grow(es, base, k0, k - 1);
        assert(kcount(es, base, k - 1) == kcount(d, base, k - 1));
    } else {
        lemma_start_same(es, base, k0);
        assert(kcount(es, base, k0) == kcount(d, base, k0) + 1);
    }
}

/// Below the last entry's key, the starts are unchanged.
proof fn lemma_start_same(es: Seq<u64>, base: int, k: int)
    requires es.len() > 0, ekey(es.last(), base) >= k,
    ensures kstart(es, base, k) == kstart(es.drop_last(), base, k),
    decreases k,
{
    if k > 0 {
        lemma_start_same(es, base, k - 1);
        assert(kcount(es, base, k - 1) == kcount(es.drop_last(), base, k - 1));
    }
}

/// Group the first `m` entries by key (see the module comment).
pub fn group_by_key(ent: &Vec<u64>, m: usize, base: u64, ng: usize, ends: &mut Vec<usize>, vals: &mut Vec<u32>)
    requires
        m <= ent@.len(), ng < usize::MAX,
        keys_in(ent@.take(m as int), base as int, ng as int),
        old(ends)@.len() == ng + 1,
        forall|k: int| 0 <= k <= ng ==> #[trigger] old(ends)@[k] == 0,
        old(vals)@.len() >= m,
    ensures ({
        let es = ent@.take(m as int);
        &&& final(ends)@.len() == ng + 1 && final(vals)@.len() == old(vals)@.len()
        &&& kstart(es, base as int, ng as int) == m
        &&& forall|k: int| 0 <= k < ng ==> #[trigger] final(ends)@[k] == kstart(es, base as int, k + 1)
        &&& forall|k: int| 0 <= k < ng ==> #[trigger] final(vals)@.subrange(kstart(es, base as int, k) as int,
            kstart(es, base as int, k + 1) as int) == kvals(es, base as int, k)
    }),
    no_unwind
{
    let ghost es = ent@.take(m as int);
    let ghost b = base as int;
    proof { lemma_total(es, b, ng as int); }
    // Count: ends[k] = number of entries with key k.
    let mut i: usize = 0;
    while i < m
        invariant
            m <= ent@.len(), es == ent@.take(m as int), b == base as int, keys_in(es, b, ng as int),
            i <= m, ends@.len() == ng + 1, kstart(es, b, ng as int) == m,
            forall|k: int| 0 <= k < ng ==> #[trigger] ends@[k] == kcount(es.take(i as int), b, k),
            forall|k: int| 0 <= k < ng ==> #[trigger] kcount(es.take(i as int), b, k) <= kcount(es, b, k),
            ends@[ng as int] == 0,
        decreases m - i,
    {
        let e = ent[i];
        proof { assert(es[i as int] == e); assert(0 <= ekey(e, b) < ng); }
        let k = ((e >> 32u64) - base) as usize;
        proof {
            assert forall|k2: int| 0 <= k2 < ng implies kcount(es.take(i + 1), b, k2) <= kcount(es, b, k2) by {
                lemma_count_prefix(es, b, i + 1, k2);
            }
            lemma_step(es, b, i as int, k as int);
            assert(kcount(es.take(i as int), b, k as int) < kcount(es, b, k as int));
            lemma_segment_end(es, b, k as int, ng as int);
        }
        ends[k] = ends[k] + 1;
        proof {
            assert forall|k2: int| 0 <= k2 < ng implies #[trigger] ends@[k2] == kcount(es.take(i + 1), b, k2) by {
                lemma_step(es, b, i as int, k2);
            }
        }
        i = i + 1;
    }
    proof { assert(es.take(m as int) =~= es); }
    // Starts: ends[k] = kstart(k), acc = kstart(k) after k.
    let mut acc: usize = 0;
    let mut k: usize = 0;
    while k < ng
        invariant
            es == ent@.take(m as int), b == base as int, keys_in(es, b, ng as int), kstart(es, b, ng as int) == m,
            k <= ng, ends@.len() == ng + 1, acc == kstart(es, b, k as int),
            forall|j: int| 0 <= j < k ==> #[trigger] ends@[j] == kstart(es, b, j),
            forall|j: int| k <= j < ng ==> #[trigger] ends@[j] == kcount(es, b, j),
        decreases ng - k,
    {
        let c = ends[k];
        proof {
            assert(kstart(es, b, k as int + 1) == acc + c);
            if (k as int) + 1 < ng { lemma_start_mono(es, b, k as int, ng as int); }
            assert(kstart(es, b, k as int + 1) <= m);
        }
        ends[k] = acc;
        acc = acc + c;
        k = k + 1;
    }
    // Scatter: ends[k] = kstart(k) + kcount(prefix, k), segment prefixes hold kvals(prefix, k).
    proof {
        assert(es.take(0) =~= Seq::<u64>::empty());
        assert forall|j: int| 0 <= j < ng implies #[trigger] vals@.subrange(kstart(es, b, j) as int, ends@[j] as int)
            == kvals(es.take(0), b, j) by {
            assert(kvals(es.take(0), b, j) == Seq::<u32>::empty());
            assert(kcount(es.take(0), b, j) == 0);
            lemma_segment_end(es, b, j, ng as int);
            assert(vals@.subrange(kstart(es, b, j) as int, ends@[j] as int) =~= Seq::<u32>::empty());
        }
        assert forall|j: int| 0 <= j < ng implies #[trigger] kcount(es.take(0), b, j) <= kcount(es, b, j) by {
            assert(kcount(es.take(0), b, j) == 0);
        }
        assert forall|j: int| 0 <= j < ng implies #[trigger] ends@[j] == kstart(es, b, j) + kcount(es.take(0), b, j) by {
            assert(kcount(es.take(0), b, j) == 0);
        }
        assert forall|j: int| 0 <= j < ng implies kstart(es, b, j) + kcount(es, b, j) <= m by {
            lemma_segment_end(es, b, j, ng as int);
        }
    }
    let mut i: usize = 0;
    while i < m
        invariant
            m <= ent@.len(), es == ent@.take(m as int), b == base as int, keys_in(es, b, ng as int), kstart(es, b, ng as int) == m,
            i <= m, ends@.len() == ng + 1, vals@.len() >= m, vals@.len() == old(vals)@.len(),
            forall|j: int| 0 <= j < ng ==> #[trigger] ends@[j] == kstart(es, b, j) + kcount(es.take(i as int), b, j),
            forall|j: int| 0 <= j < ng ==> #[trigger] kcount(es.take(i as int), b, j) <= kcount(es, b, j),
            forall|j: int| 0 <= j < ng ==> kstart(es, b, j) + kcount(es, b, j) <= m,
            forall|j: int| 0 <= j < ng ==> #[trigger] vals@.subrange(kstart(es, b, j) as int, ends@[j] as int)
                == kvals(es.take(i as int), b, j),
        decreases m - i,
    {
        let e = ent[i];
        proof { assert(es[i as int] == e); assert(0 <= ekey(e, b) < ng); }
        let k = ((e >> 32u64) - base) as usize;
        let p = ends[k];
        let ghost vals0 = vals@;
        let ghost ends0 = ends@;
        proof {
            lemma_step(es, b, i as int, k as int);
            lemma_count_prefix(es, b, i + 1, k as int);
            assert(p < kstart(es, b, k as int) + kcount(es, b, k as int));
            assert(kstart(es, b, k as int) + kcount(es, b, k as int) <= m);
            assert((e & 0xFFFF_FFFFu64) <= 0xFFFF_FFFFu64) by (bit_vector);
        }
        vals[p] = (e & 0xFFFF_FFFFu64) as u32;
        ends[k] = p + 1;
        proof {
            assert forall|j: int| 0 <= j < ng implies #[trigger] ends@[j] == kstart(es, b, j) + kcount(es.take(i + 1), b, j) by {
                lemma_step(es, b, i as int, j);
            }
            assert forall|j: int| 0 <= j < ng implies #[trigger] kcount(es.take(i + 1), b, j) <= kcount(es, b, j) by {
                lemma_count_prefix(es, b, i + 1, j);
            }
            assert forall|j: int| 0 <= j < ng implies #[trigger] vals@.subrange(kstart(es, b, j) as int, ends@[j] as int)
                == kvals(es.take(i + 1), b, j) by {
                lemma_step(es, b, i as int, j);
                let s = kstart(es, b, j) as int;
                let e0 = ends0[j] as int;
                assert(vals0.subrange(s, e0) == kvals(es.take(i as int), b, j));
                lemma_count_prefix(es, b, i as int, j);
                if j == k as int {
                    assert(vals@.subrange(s, e0 + 1) =~= vals0.subrange(s, e0).push(evalue(e)));
                } else {
                    // Segment `j` is disjoint from position `p` of segment `k`.
                    if j < k as int {
                        lemma_start_mono(es, b, j, k as int);
                        assert(e0 <= p);
                    } else {
                        lemma_start_mono(es, b, k as int, j);
                        assert(p < s);
                    }
                    assert(vals@.subrange(s, e0) =~= vals0.subrange(s, e0));
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(es.take(m as int) =~= es);
        assert forall|j: int| 0 <= j < ng implies #[trigger] ends@[j] == kstart(es, b, j + 1) by {
            assert(kstart(es, b, j + 1) == kstart(es, b, j) + kcount(es, b, j));
            assert(ends@[j] == kstart(es, b, j) + kcount(es.take(m as int), b, j));
        }
        assert forall|j: int| 0 <= j < ng implies #[trigger] vals@.subrange(kstart(es, b, j) as int, kstart(es, b, j + 1) as int)
            == kvals(es, b, j) by {
            assert(kstart(es, b, j + 1) == kstart(es, b, j) + kcount(es, b, j));
            assert(ends@[j] == kstart(es, b, j) + kcount(es.take(m as int), b, j));
            assert(vals@.subrange(kstart(es, b, j) as int, ends@[j] as int) == kvals(es.take(m as int), b, j));
        }
    }
}


/// Every value of `kvals(k)` is the value of an entry with key `k`.
pub proof fn lemma_kvals_src(es: Seq<u64>, base: int, k: int, p: int)
    requires 0 <= p < kvals(es, base, k).len(),
    ensures exists|i: int| 0 <= i < es.len() && ekey(es[i], base) == k && #[trigger] evalue(es[i]) == kvals(es, base, k)[p],
    decreases es.len(),
{
    let d = es.drop_last();
    lemma_kvals_len(d, base, k);
    if p < kvals(d, base, k).len() {
        lemma_kvals_src(d, base, k, p);
        let i = choose|i: int| 0 <= i < d.len() && ekey(d[i], base) == k && #[trigger] evalue(d[i]) == kvals(d, base, k)[p];
        assert(es[i] == d[i]);
    } else {
        assert(es[es.len() - 1] == es.last());
    }
}

/// The value of every entry lies in `kvals` of its key.
pub proof fn lemma_kvals_has(es: Seq<u64>, base: int, i: int)
    requires 0 <= i < es.len(),
    ensures kvals(es, base, ekey(es[i], base)).contains(evalue(es[i])),
    decreases es.len(),
{
    let d = es.drop_last();
    let k = ekey(es[i], base);
    if i < es.len() - 1 {
        assert(d[i] == es[i]);
        lemma_kvals_has(d, base, i);
        let v = kvals(d, base, k);
        let x = choose|x: int| 0 <= x < v.len() && v[x] == evalue(es[i]);
        assert(kvals(es, base, k)[x] == v[x]);
    } else {
        assert(es.last() == es[i]);
        let v = kvals(d, base, k);
        assert(kvals(es, base, k) == v.push(evalue(es[i])));
        assert(kvals(es, base, k)[v.len() as int] == evalue(es[i]));
    }
}

/// When a rank of the values strictly increases along the entries, it strictly increases along every `kvals`
/// (`kvals` keeps the input order).
pub proof fn lemma_kvals_increasing(es: Seq<u64>, base: int, k: int, rank: spec_fn(u32) -> int)
    requires forall|i: int, j: int| 0 <= i < j < es.len() ==> rank(evalue(#[trigger] es[i])) < rank(evalue(#[trigger] es[j])),
    ensures forall|p: int, q: int| 0 <= p < q < kvals(es, base, k).len()
        ==> rank(#[trigger] kvals(es, base, k)[p]) < rank(#[trigger] kvals(es, base, k)[q]),
    decreases es.len(),
{
    if es.len() > 0 {
        let d = es.drop_last();
        assert forall|i: int, j: int| 0 <= i < j < d.len() implies rank(evalue(#[trigger] d[i])) < rank(evalue(#[trigger] d[j])) by {
            assert(d[i] == es[i] && d[j] == es[j]);
        }
        lemma_kvals_increasing(d, base, k, rank);
        let v = kvals(d, base, k);
        if ekey(es.last(), base) == k {
            let w = kvals(es, base, k);
            assert(w == v.push(evalue(es.last())));
            assert forall|p: int, q: int| 0 <= p < q < w.len() implies rank(#[trigger] w[p]) < rank(#[trigger] w[q]) by {
                if q < v.len() {
                    assert(w[p] == v[p] && w[q] == v[q]);
                } else {
                    assert(w[p] == v[p]);
                    lemma_kvals_src(d, base, k, p);
                    let i = choose|i: int| 0 <= i < d.len() && ekey(d[i], base) == k && #[trigger] evalue(d[i]) == v[p];
                    assert(d[i] == es[i]);
                    assert(es.last() == es[es.len() - 1]);
                }
            }
        }
    }
}

/// Every position below `kstart(ng)` lies in the segment of some key `k < ng`.
pub proof fn lemma_segment_of(es: Seq<u64>, base: int, ng: int, x: int)
    requires 0 <= x < kstart(es, base, ng),
    ensures exists|k: int| 0 <= k < ng && #[trigger] kstart(es, base, k) <= x < kstart(es, base, k) + kcount(es, base, k),
    decreases ng,
{
    if ng <= 0 {
        assert(kstart(es, base, ng) == 0);
    } else if x >= kstart(es, base, ng - 1) {
        assert(kstart(es, base, ng) == kstart(es, base, ng - 1) + kcount(es, base, ng - 1));
    } else {
        lemma_segment_of(es, base, ng - 1, x);
    }
}

/// Segments do not interleave: a position before another lies in the same or an earlier segment.
pub proof fn lemma_segment_order(es: Seq<u64>, base: int, kx: int, ky: int, x: int, y: int)
    requires
        0 <= kx, 0 <= ky, x < y,
        kstart(es, base, kx) <= x < kstart(es, base, kx) + kcount(es, base, kx),
        kstart(es, base, ky) <= y < kstart(es, base, ky) + kcount(es, base, ky),
    ensures kx <= ky,
{
    if ky < kx {
        lemma_start_mono(es, base, ky, kx);
    }
}

} // verus!
