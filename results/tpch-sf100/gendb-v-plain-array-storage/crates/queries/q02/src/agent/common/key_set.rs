//! A read-only set of `i64` keys for membership probes from worker tasks: a bitmap over `[kmin, kmin + span)`
//! when that range is small enough (one bit per key value, bit `o` of the set is bit `o % 64` of word `o / 64`),
//! otherwise the key list itself, probed by a linear scan. Built once on the calling thread; `contains` is
//! `no_unwind` and equals membership in the key list it was built from.
use vstd::prelude::*;

verus! {

/// Largest key range (in bits) for which the bitmap is built: 2^32 bits = 512 MiB.
pub const MAX_SPAN: u64 = 0x1_0000_0000;

/// Bit `o` of a word sequence.
pub open spec fn bit_at(words: Seq<u64>, o: int) -> bool {
    (words[o / 64] >> ((o % 64) as u64)) & 1u64 == 1u64
}

/// `k` lies in `[kmin, kmax]` and its offset's bit is set.
pub open spec fn in_bits(words: Seq<u64>, kmin: i64, kmax: i64, k: i64) -> bool {
    kmin <= k <= kmax && bit_at(words, k - kmin)
}

/// The positions `x` of `[from, to)` whose key is in the bitmap `words` over `[kmin, kmax]`, in increasing order,
/// as `batch[0..k]`. The bitmap fields are parameters so the loop keeps them in registers.
fn collect_dense(words: &Vec<u64>, kmin: i64, kmax: i64, keys: &[i64], n: usize, from: usize, to: usize, batch: &mut Vec<usize>) -> (k: usize)
    requires
        kmin <= kmax,
        kmax - kmin < MAX_SPAN,
        kmax - kmin < words@.len() * 64,
        keys@.len() == n,
        from <= to <= n,
        to - from <= old(batch)@.len(),
    ensures
        final(batch)@.len() == old(batch)@.len(),
        k <= to - from,
        forall|i: int| 0 <= i < k ==> from <= #[trigger] final(batch)@[i] < to && in_bits(words@, kmin, kmax, keys@[final(batch)@[i] as int]),
        forall|i: int, i2: int| 0 <= i < i2 < k ==> final(batch)@[i] < final(batch)@[i2],
        forall|y: int| from <= y < to && #[trigger] in_bits(words@, kmin, kmax, keys@[y]) ==> exists|i: int| 0 <= i < k && final(batch)@[i] == y,
    no_unwind
{
    let ghost len0 = batch@.len();
    let mut k: usize = 0;
    let mut x = from;
    while x < to
        invariant
            batch@.len() == len0,
            kmin <= kmax,
            kmax - kmin < MAX_SPAN,
            kmax - kmin < words@.len() * 64,
            keys@.len() == n,
            from <= x <= to <= n,
            to - from <= batch@.len(),
            k <= x - from,
            forall|i: int| 0 <= i < k ==> from <= #[trigger] batch@[i] < x && in_bits(words@, kmin, kmax, keys@[batch@[i] as int]),
            forall|i: int, i2: int| 0 <= i < i2 < k ==> batch@[i] < batch@[i2],
            forall|y: int| from <= y < x && #[trigger] in_bits(words@, kmin, kmax, keys@[y]) ==> exists|i: int| 0 <= i < k && batch@[i] == y,
        decreases to - x,
    {
        let v = keys[x];
        let ghost old_batch = batch@;
        let ghost old_k = k;
        if kmin <= v && v <= kmax {
            let o = (v - kmin) as u64;
            let w = words[(o / 64) as usize];
            if (w >> (o % 64)) & 1u64 == 1u64 {
                assert(in_bits(words@, kmin, kmax, v));
                batch[k] = x;
                k = k + 1;
            } else {
                assert(!in_bits(words@, kmin, kmax, v));
            }
        }
        proof {
            assert forall|y: int| from <= y < x + 1 && #[trigger] in_bits(words@, kmin, kmax, keys@[y])
                implies exists|i: int| 0 <= i < k && batch@[i] == y by {
                if y < x {
                    let i = choose|i: int| 0 <= i < old_k && old_batch[i] == y;
                    assert(batch@[i] == y);
                } else {
                    assert(batch@[old_k as int] == y);
                }
            }
        }
        x = x + 1;
    }
    k
}

/// Rows per block of `KeySet::collect_members_blocked`: a block whose key range holds no member is skipped after
/// one min/max pass over its keys.
pub const BLOCK: usize = 64;

/// The least and greatest of the `BLOCK` keys `keys[a .. a + BLOCK]`. The block is taken as a sub-slice of
/// constant length, so the loop has no bounds checks and vectorizes.
#[inline(always)]
pub fn block_min_max(keys: &[i64], n: usize, a: usize) -> (r: (i64, i64))
    requires
        keys@.len() == n,
        a + BLOCK <= n,
    ensures
        forall|j: int| a <= j < a + BLOCK ==> r.0 <= #[trigger] keys@[j] <= r.1,
    no_unwind
{
    let (_, tail) = keys.split_at(a);
    let (blk, _) = tail.split_at(BLOCK);
    assert(forall|i: int| 0 <= i < BLOCK ==> #[trigger] blk@[i] == keys@[a + i]);
    let mut mn = blk[0];
    let mut mx = blk[0];
    let mut i: usize = 1;
    while i < BLOCK
        invariant
            blk@.len() == BLOCK,
            1 <= i <= BLOCK,
            forall|q: int| 0 <= q < BLOCK ==> #[trigger] blk@[q] == keys@[a + q],
            forall|q: int| 0 <= q < i ==> mn <= #[trigger] blk@[q] <= mx,
        decreases BLOCK - i,
    {
        let k = blk[i];
        if k < mn {
            mn = k;
        }
        if k > mx {
            mx = k;
        }
        i = i + 1;
    }
    assert forall|j: int| a <= j < a + BLOCK implies mn <= #[trigger] keys@[j] <= mx by {
        assert(blk@[j - a] == keys@[j]);
    }
    (mn, mx)
}



/// Word and bit of an offset `p` within a range `[o, e]` of fewer than 64 offsets.
proof fn lemma_word_pos(o: int, p: int, e: int)
    requires 0 <= o <= p <= e, e - o < 64,
    ensures
        e / 64 == o / 64 || e / 64 == o / 64 + 1,
        p / 64 == o / 64 || p / 64 == e / 64,
        p / 64 == o / 64 ==> o % 64 <= p % 64,
        p / 64 == e / 64 ==> p % 64 <= e % 64,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(o, 64);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p, 64);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(e, 64);
    assert(0 <= o % 64 < 64 && 0 <= p % 64 < 64 && 0 <= e % 64 < 64);
}

/// Offset `o + d` splits into word and bit: within the word of `o` while `o % 64 + d < 64`, else in the next one.
proof fn lemma_offset_split(o: int, d: int)
    requires 0 <= o, 0 <= d < 64,
    ensures
        o % 64 + d < 64 ==> (o + d) / 64 == o / 64 && (o + d) % 64 == o % 64 + d,
        o % 64 + d >= 64 ==> (o + d) / 64 == o / 64 + 1 && (o + d) % 64 == o % 64 + d - 64,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(o, 64);
    if o % 64 + d < 64 {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(o + d, 64, o / 64, o % 64 + d);
    } else {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(o + d, 64, o / 64 + 1, o % 64 + d - 64);
    }
}

/// A word whose low `width + 1` bits are zero has bit `d <= width` clear.
proof fn lemma_mask_zero_bit(m: u64, width: u64, d: u64)
    requires width < 64, d <= width, m & (!0u64 >> ((63u64 - width) as u64)) == 0,
    ensures !((m >> d) & 1u64 == 1u64),
{
    assert(!((m >> d) & 1u64 == 1u64)) by (bit_vector)
        requires width < 64, d <= width, m & (!0u64 >> ((63u64 - width) as u64)) == 0;
}

/// The key set: `keys` as built; `dense` selects the bitmap representation.
pub struct KeySet {
    keys: Vec<i64>,
    words: Vec<u64>,
    kmin: i64,
    kmax: i64,
    span: u64,
    dense: bool,
}

/// Setting bit `s` of `x` sets exactly that bit.
proof fn lemma_or_bit(x: u64, s: u64, t: u64)
    requires s < 64, t < 64,
    ensures ((x | (1u64 << s)) >> t) & 1u64 == 1u64 <==> (s == t || (x >> t) & 1u64 == 1u64),
{
    assert(((x | (1u64 << s)) >> t) & 1u64 == 1u64 <==> (s == t || (x >> t) & 1u64 == 1u64)) by (bit_vector)
        requires s < 64, t < 64;
}

/// Zero has no bit set.
proof fn lemma_zero_bit(t: u64)
    requires t < 64,
    ensures !((0u64 >> t) & 1u64 == 1u64),
{
    assert(!((0u64 >> t) & 1u64 == 1u64)) by (bit_vector) requires t < 64;
}

/// Equal word index and bit position mean equal bit offsets.
proof fn lemma_same_bit(o: int, p: int)
    requires 0 <= o, 0 <= p, o / 64 == p / 64, o % 64 == p % 64,
    ensures o == p,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(o, 64);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p, 64);
}

impl KeySet {
    /// The keys the set was built from.
    pub closed spec fn keys(&self) -> Seq<i64> {
        self.keys@
    }

    /// Representation invariant: in dense mode every key lies in `[kmin, kmin + span)` and bit `k - kmin` is set
    /// exactly for the keys of the list.
    pub closed spec fn wf(&self) -> bool {
        self.dense ==> {
            &&& 1 <= self.span <= MAX_SPAN
            &&& self.kmax == self.kmin + self.span - 1
            &&& self.words@.len() * 64 >= self.span
            &&& forall|o: int| 0 <= o < self.span ==>
                (#[trigger] bit_at(self.words@, o) <==> exists|j: int| 0 <= j < self.keys@.len() && self.keys@[j] - self.kmin == o)
            &&& forall|j: int| 0 <= j < self.keys@.len() ==>
                self.kmin <= #[trigger] self.keys@[j] && self.keys@[j] - self.kmin < self.span
        }
    }

    /// Build the set of `keys` (calling thread; allocates the bitmap when the key range allows it).
    pub fn new(keys: Vec<i64>) -> (s: KeySet)
        ensures s.wf(), s.keys() == keys@,
    {
        let n = keys.len();
        if n == 0 {
            return KeySet { keys, words: Vec::new(), kmin: 0, kmax: 0, span: 0, dense: false };
        }
        let mut kmin: i64 = keys[0];
        let mut kmax: i64 = keys[0];
        let mut i: usize = 1;
        while i < n
            invariant
                n == keys@.len(),
                1 <= i <= n,
                kmin <= kmax,
                forall|j: int| 0 <= j < i ==> kmin <= #[trigger] keys@[j] <= kmax,
            decreases n - i,
        {
            if keys[i] < kmin {
                kmin = keys[i];
            }
            if keys[i] > kmax {
                kmax = keys[i];
            }
            i = i + 1;
        }
        let range: i128 = kmax as i128 - kmin as i128 + 1;
        if range > MAX_SPAN as i128 {
            return KeySet { keys, words: Vec::new(), kmin, kmax, span: 0, dense: false };
        }
        let span = range as u64;
        let nwords = ((span + 63) / 64) as usize;
        let mut words: Vec<u64> = vec![0u64; nwords];
        proof {
            assert forall|w: int| 0 <= w < nwords implies #[trigger] words@[w] == 0u64 by {
                assert(cloned(0u64, words@[w]));
            }
            assert forall|o: int| 0 <= o < span implies !#[trigger] bit_at(words@, o) by {
                assert(words@[o / 64] == 0u64);
                lemma_zero_bit((o % 64) as u64);
            }
        }
        let mut i: usize = 0;
        while i < n
            invariant
                n == keys@.len(),
                i <= n,
                span <= MAX_SPAN,
                kmin <= kmax,
                span == kmax - kmin + 1,
                nwords * 64 >= span,
                words@.len() == nwords,
                forall|j: int| 0 <= j < n ==> kmin <= #[trigger] keys@[j] <= kmax,
                forall|o: int| 0 <= o < span ==>
                    (#[trigger] bit_at(words@, o) <==> exists|j: int| 0 <= j < i && keys@[j] - kmin == o),
            decreases n - i,
        {
            let off: u64 = (keys[i] as i128 - kmin as i128) as u64;
            let w: usize = (off / 64) as usize;
            let s: u64 = off % 64;
            let ghost old_words = words@;
            let old_word = words[w];
            words[w] = old_word | (1u64 << s);
            proof {
                assert forall|o: int| 0 <= o < span implies
                    (#[trigger] bit_at(words@, o) <==> exists|j: int| 0 <= j < i + 1 && keys@[j] - kmin == o) by {
                    let t = (o % 64) as u64;
                    let hit_old = exists|j: int| 0 <= j < i && keys@[j] - kmin == o;
                    if o == off as int {
                        assert(o / 64 == w as int && t == s);
                        lemma_or_bit(old_word, s, t);
                        assert(keys@[i as int] - kmin == o);
                    } else {
                        if o / 64 == w as int {
                            if t == s {
                                lemma_same_bit(o, off as int);
                            }
                            lemma_or_bit(old_word, s, t);
                            assert(bit_at(words@, o) == bit_at(old_words, o));
                        } else {
                            assert(words@[o / 64] == old_words[o / 64]);
                            assert(bit_at(words@, o) == bit_at(old_words, o));
                        }
                        if exists|j: int| 0 <= j < i + 1 && keys@[j] - kmin == o {
                            let j = choose|j: int| 0 <= j < i + 1 && keys@[j] - kmin == o;
                            assert(j != i as int);
                            assert(hit_old);
                        }
                        if hit_old {
                            let j = choose|j: int| 0 <= j < i && keys@[j] - kmin == o;
                            assert(0 <= j < i + 1 && keys@[j] - kmin == o);
                        }
                    }
                }
            }
            i = i + 1;
        }
        assert(i == n);
        let ghost kv = keys@;
        let r = KeySet { keys, words, kmin, kmax, span, dense: true };
        assert(r.keys@ == kv);
        assert forall|o: int| 0 <= o < r.span implies
            (#[trigger] bit_at(r.words@, o) <==> exists|j: int| 0 <= j < r.keys@.len() && r.keys@[j] - r.kmin == o) by {
            if bit_at(r.words@, o) {
                let j = choose|j: int| 0 <= j < i && kv[j] - kmin == o;
                assert(0 <= j < r.keys@.len() && r.keys@[j] - r.kmin == o);
            }
            if exists|j: int| 0 <= j < r.keys@.len() && r.keys@[j] - r.kmin == o {
                let j = choose|j: int| 0 <= j < r.keys@.len() && r.keys@[j] - r.kmin == o;
                assert(0 <= j < i && kv[j] - kmin == o);
            }
        }
        r
    }

    /// `k` is one of the keys.
    pub open spec fn has(&self, k: i64) -> bool {
        exists|j: int| 0 <= j < self.keys().len() && #[trigger] self.keys()[j] == k
    }

    /// The positions `x` of `[from, to)` whose key `keys[x]` is in the set, in increasing order, as `batch[0..k]`.
    pub fn collect_members(&self, keys: &[i64], n: usize, from: usize, to: usize, batch: &mut Vec<usize>) -> (k: usize)
        requires
            self.wf(),
            keys@.len() == n,
            from <= to <= n,
            to - from <= old(batch)@.len(),
        ensures
            final(batch)@.len() == old(batch)@.len(),
            k <= to - from,
            forall|i: int| 0 <= i < k ==> from <= #[trigger] final(batch)@[i] < to && self.has(keys@[final(batch)@[i] as int]),
            forall|i: int, i2: int| 0 <= i < i2 < k ==> final(batch)@[i] < final(batch)@[i2],
            forall|y: int| from <= y < to && #[trigger] self.has(keys@[y]) ==> exists|i: int| 0 <= i < k && final(batch)@[i] == y,
        no_unwind
    {
        if self.dense {
            let k = collect_dense(&self.words, self.kmin, self.kmax, keys, n, from, to, batch);
            proof {
                assert forall|y: int| from <= y < to implies (#[trigger] self.has(keys@[y]) <==> in_bits(self.words@, self.kmin, self.kmax, keys@[y])) by {
                    self.lemma_dense_has(keys@[y]);
                }
            }
            k
        } else {
            let ghost len0 = batch@.len();
            let mut k: usize = 0;
            let mut x = from;
            while x < to
                invariant
                    batch@.len() == len0,
                    self.wf(),
                    keys@.len() == n,
                    from <= x <= to <= n,
                    to - from <= batch@.len(),
                    k <= x - from,
                    forall|i: int| 0 <= i < k ==> from <= #[trigger] batch@[i] < x && self.has(keys@[batch@[i] as int]),
                    forall|i: int, i2: int| 0 <= i < i2 < k ==> batch@[i] < batch@[i2],
                    forall|y: int| from <= y < x && #[trigger] self.has(keys@[y]) ==> exists|i: int| 0 <= i < k && batch@[i] == y,
                decreases to - x,
            {
                let ghost old_batch = batch@;
                let ghost old_k = k;
                if self.contains(keys[x]) {
                    batch[k] = x;
                    k = k + 1;
                }
                proof {
                    assert forall|y: int| from <= y < x + 1 && #[trigger] self.has(keys@[y])
                        implies exists|i: int| 0 <= i < k && batch@[i] == y by {
                        if y < x {
                            let i = choose|i: int| 0 <= i < old_k && old_batch[i] == y;
                            assert(batch@[i] == y);
                        } else {
                            assert(batch@[old_k as int] == y);
                        }
                    }
                }
                x = x + 1;
            }
            k
        }
    }

    /// Appends the positions `x` of `[from, to)` whose key `keys[x]` is in the set, in increasing order, to
    /// `batch[0..k0]`, giving `batch[0..k]`; `batch[0..k0]` is unchanged.
    pub fn collect_into(&self, keys: &[i64], n: usize, from: usize, to: usize, batch: &mut Vec<usize>, k0: usize) -> (k: usize)
        requires
            self.wf(),
            keys@.len() == n,
            from <= to <= n,
            k0 + (to - from) <= old(batch)@.len(),
        ensures
            final(batch)@.len() == old(batch)@.len(),
            k0 <= k <= k0 + (to - from),
            forall|i: int| 0 <= i < k0 ==> #[trigger] final(batch)@[i] == old(batch)@[i],
            forall|i: int| k0 <= i < k ==> from <= #[trigger] final(batch)@[i] < to && self.has(keys@[final(batch)@[i] as int]),
            forall|i: int, i2: int| k0 <= i < i2 < k ==> final(batch)@[i] < final(batch)@[i2],
            forall|y: int| from <= y < to && #[trigger] self.has(keys@[y]) ==> exists|i: int| k0 <= i < k && final(batch)@[i] == y,
        no_unwind
    {
        let ghost b0 = batch@;
        let blen = batch.len();
        let mut k = k0;
        let mut x = from;
        while x < to
            invariant
                self.wf(),
                batch@.len() == b0.len(),
                b0.len() == blen,
                keys@.len() == n,
                from <= x <= to <= n,
                k0 + (to - from) <= b0.len(),
                k0 <= k <= k0 + (x - from),
                forall|i: int| 0 <= i < k0 ==> #[trigger] batch@[i] == b0[i],
                forall|i: int| k0 <= i < k ==> from <= #[trigger] batch@[i] < x && self.has(keys@[batch@[i] as int]),
                forall|i: int, i2: int| k0 <= i < i2 < k ==> batch@[i] < batch@[i2],
                forall|y: int| from <= y < x && #[trigger] self.has(keys@[y]) ==> exists|i: int| k0 <= i < k && batch@[i] == y,
            decreases to - x,
        {
            let ghost old_batch = batch@;
            let ghost old_k = k;
            if self.contains(keys[x]) {
                batch[k] = x;
                k = k + 1;
            }
            proof {
                assert forall|y: int| from <= y < x + 1 && #[trigger] self.has(keys@[y])
                    implies exists|i: int| k0 <= i < k && batch@[i] == y by {
                    if y < x {
                        let i = choose|i: int| k0 <= i < old_k && old_batch[i] == y;
                        assert(batch@[i] == y);
                    } else {
                        assert(batch@[old_k as int] == y);
                    }
                }
            }
            x = x + 1;
        }
        k
    }

    /// The bitmap bits of offsets `o ..= e` (fewer than 64) as one word: bit `d` of the result is the bit of
    /// offset `o + d` (taken from the word of `o` and, past its end, from the next word).
    #[inline(always)]
    fn window_bits(&self, o: u64, e: u64) -> (m: u64)
        requires self.wf(), self.dense, o <= e, e - o < 64, e < self.span,
        ensures forall|d: u64| d <= e - o ==> (((m >> d) & 1u64 == 1u64) == #[trigger] bit_at(self.words@, o + d)),
        no_unwind
    {
        let w0 = (o / 64) as usize;
        let s = o % 64;
        proof { lemma_word_pos(o as int, o as int, e as int); }
        let lo = self.words[w0] >> s;
        if (e / 64) as usize == w0 {
            proof {
                assert forall|d: u64| d <= e - o implies (((lo >> d) & 1u64 == 1u64) == #[trigger] bit_at(self.words@, o + d)) by {
                    lemma_word_pos(o as int, (o + d) as int, e as int);
                    lemma_offset_split(o as int, d as int);
                    let w = self.words@[w0 as int];
                    assert(((w >> s) >> d) & 1u64 == (w >> ((s + d) as u64)) & 1u64) by (bit_vector)
                        requires s + d < 64;
                }
            }
            lo
        } else {
            proof { lemma_word_pos(o as int, e as int, e as int); }
            let hi = self.words[w0 + 1] << (64 - s);
            let m = lo | hi;
            proof {
                assert(s >= 1) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(o as int, 64);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(e as int, 64);
                }
                assert forall|d: u64| d <= e - o implies (((m >> d) & 1u64 == 1u64) == #[trigger] bit_at(self.words@, o + d)) by {
                    lemma_offset_split(o as int, d as int);
                    let w = self.words@[w0 as int];
                    let v = self.words@[w0 + 1];
                    if s + d < 64 {
                        assert((((w >> s) | (v << ((64 - s) as u64))) >> d) & 1u64 == (w >> ((s + d) as u64)) & 1u64) by (bit_vector)
                            requires s + d < 64, 1 <= s < 64;
                    } else {
                        assert((((w >> s) | (v << ((64 - s) as u64))) >> d) & 1u64 == (v >> ((s + d - 64) as u64)) & 1u64) by (bit_vector)
                            requires 64 <= s + d, d < 64, 1 <= s < 64;
                    }
                }
            }
            m
        }
    }

    /// Process block `[x, x + BLOCK)` of a collection over `[from, ..)`: skip it when its key range holds no member,
    /// otherwise append its members to `batch[0..k]`. When the block's keys span fewer than 64 values inside the
    /// bitmap (`block_min_max`), membership is read from one word of bitmap bits (`window_bits`).
    #[inline(always)]
    pub fn block_step(&self, keys: &[i64], n: usize, Ghost(from): Ghost<int>, x: usize, batch: &mut Vec<usize>, k: usize) -> (k2: usize)
        requires
            self.wf(),
            keys@.len() == n,
            from <= x,
            x + BLOCK <= n,
            k + BLOCK <= old(batch)@.len(),
            self.collected(keys@, from, x as int, old(batch)@, k as int),
        ensures
            final(batch)@.len() == old(batch)@.len(),
            k <= k2 <= k + BLOCK,
            self.collected(keys@, from, x + BLOCK, final(batch)@, k2 as int),
        no_unwind
    {
        let ghost old_batch = batch@;
        let (mn, mx) = block_min_max(keys, n, x);
        if self.dense && (mx < self.kmin || mn > self.kmax) {
            // No key of the block lies in the bitmap's range.
            proof {
                assert forall|y: int| x <= y < x + BLOCK implies !#[trigger] self.has(keys@[y]) by {
                    assert(mn <= keys@[y] <= mx);
                    self.lemma_dense_has(keys@[y]);
                }
                assert forall|y: int| from <= y < x + BLOCK && #[trigger] self.has(keys@[y]) implies exists|i: int| 0 <= i < k && batch@[i] == y by {
                    if y >= x { assert(!self.has(keys@[y])); }
                }
            }
            return k;
        }
        if !self.dense || mn < self.kmin || mx > self.kmax || mx as i128 - mn as i128 >= 64 {
            let k2 = self.collect_into(keys, n, x, x + BLOCK, batch, k);
            proof { self.lemma_collected_append(keys@, from, x as int, x + BLOCK, old_batch, batch@, k as int, k2 as int); }
            return k2;
        }
        proof {
            assert(mn <= keys@[x as int] <= mx);
        }
        let o = (mn as i128 - self.kmin as i128) as u64;
        let e = (mx as i128 - self.kmin as i128) as u64;
        let m = self.window_bits(o, e);
        let width = e - o;
        let lenmask = !0u64 >> (63 - width);
        proof {
            assert forall|d: u64| d <= width implies (((m >> d) & 1u64 == 1u64) == self.has((mn + d) as i64)) by {
                assert(bit_at(self.words@, o + d) == ((m >> d) & 1u64 == 1u64));
                self.lemma_dense_has((mn + d) as i64);
            }
        }
        if m & lenmask == 0 {
            proof {
                assert forall|y: int| x <= y < x + BLOCK implies !#[trigger] self.has(keys@[y]) by {
                    assert(mn <= keys@[y] <= mx);
                    let d = (keys@[y] - mn) as u64;
                    lemma_mask_zero_bit(m, width, d);
                }
                assert forall|y: int| from <= y < x + BLOCK && #[trigger] self.has(keys@[y]) implies exists|i: int| 0 <= i < k && batch@[i] == y by {
                    if y >= x { assert(!self.has(keys@[y])); }
                }
            }
            return k;
        }
        let k2 = self.collect_masked(keys, n, x, mn, mx, m, batch, k);
        proof { self.lemma_collected_append(keys@, from, x as int, x + BLOCK, old_batch, batch@, k as int, k2 as int); }
        k2
    }

    /// Appends the positions of block `[x, x + BLOCK)` whose key is a member to `batch[0..k0]`, reading membership
    /// of the block's keys (all in `[mn, mx]`, fewer than 64 values) from bit `key - mn` of `m`.
    #[inline(always)]
    fn collect_masked(&self, keys: &[i64], n: usize, x: usize, mn: i64, mx: i64, m: u64, batch: &mut Vec<usize>, k0: usize) -> (k: usize)
        requires
            self.wf(),
            keys@.len() == n,
            x + BLOCK <= n,
            k0 + BLOCK <= old(batch)@.len(),
            mn <= mx, mx - mn < 64,
            forall|j: int| x <= j < x + BLOCK ==> mn <= #[trigger] keys@[j] <= mx,
            forall|d: u64| d <= mx - mn ==> (((m >> d) & 1u64 == 1u64) == self.has((mn + d) as i64)),
        ensures
            final(batch)@.len() == old(batch)@.len(),
            k0 <= k <= k0 + BLOCK,
            forall|i: int| 0 <= i < k0 ==> #[trigger] final(batch)@[i] == old(batch)@[i],
            forall|i: int| k0 <= i < k ==> x <= #[trigger] final(batch)@[i] < x + BLOCK && self.has(keys@[final(batch)@[i] as int]),
            forall|i: int, i2: int| k0 <= i < i2 < k ==> final(batch)@[i] < final(batch)@[i2],
            forall|y: int| x <= y < x + BLOCK && #[trigger] self.has(keys@[y]) ==> exists|i: int| k0 <= i < k && final(batch)@[i] == y,
        no_unwind
    {
        let (_, tail) = keys.split_at(x);
        let (blk, _) = tail.split_at(BLOCK);
        assert(forall|q: int| 0 <= q < BLOCK ==> #[trigger] blk@[q] == keys@[x + q]);
        let ghost b0 = batch@;
        let blen = batch.len();
        let mut k = k0;
        let mut i: usize = 0;
        while i < BLOCK
            invariant
                blk@.len() == BLOCK,
                forall|q: int| 0 <= q < BLOCK ==> #[trigger] blk@[q] == keys@[x + q],
                forall|j: int| x <= j < x + BLOCK ==> mn <= #[trigger] keys@[j] <= mx,
                forall|d: u64| d <= mx - mn ==> (((m >> d) & 1u64 == 1u64) == self.has((mn + d) as i64)),
                mn <= mx, mx - mn < 64,
                batch@.len() == b0.len(),
                b0.len() == blen,
                k0 + BLOCK <= b0.len(),
                x + BLOCK <= n,
                i <= BLOCK,
                k0 <= k <= k0 + i,
                forall|q: int| 0 <= q < k0 ==> #[trigger] batch@[q] == b0[q],
                forall|q: int| k0 <= q < k ==> x <= #[trigger] batch@[q] < x + i && self.has(keys@[batch@[q] as int]),
                forall|q: int, q2: int| k0 <= q < q2 < k ==> batch@[q] < batch@[q2],
                forall|y: int| x <= y < x + i && #[trigger] self.has(keys@[y]) ==> exists|q: int| k0 <= q < k && batch@[q] == y,
            decreases BLOCK - i,
        {
            let key = blk[i];
            assert(keys@[x + i] == key);
            let d = (key as i128 - mn as i128) as u64;
            let ghost old_batch = batch@;
            let ghost old_k = k;
            if (m >> d) & 1u64 == 1u64 {
                assert(self.has(key));
                batch[k] = x + i;
                k = k + 1;
            } else {
                assert(!self.has(key));
            }
            proof {
                assert forall|y: int| x <= y < x + i + 1 && #[trigger] self.has(keys@[y])
                    implies exists|q: int| k0 <= q < k && batch@[q] == y by {
                    if y < x + i {
                        let q = choose|q: int| k0 <= q < old_k && old_batch[q] == y;
                        assert(batch@[q] == y);
                    } else {
                        assert(batch@[old_k as int] == y);
                    }
                }
            }
            i = i + 1;
        }
        k
    }

    /// Appending the members of `[x, to)` (as `collect_into` ensures) to a collection over `[from, x)` gives one over
    /// `[from, to)`.
    proof fn lemma_collected_append(&self, keys: Seq<i64>, from: int, x: int, to: int, b0: Seq<usize>, b1: Seq<usize>, k: int, k2: int)
        requires
            from <= x <= to,
            self.collected(keys, from, x, b0, k),
            b1.len() == b0.len(),
            k <= k2 <= k + (to - x),
            k2 <= b1.len(),
            forall|i: int| 0 <= i < k ==> #[trigger] b1[i] == b0[i],
            forall|i: int| k <= i < k2 ==> x <= #[trigger] b1[i] < to && self.has(keys[b1[i] as int]),
            forall|i: int, i2: int| k <= i < i2 < k2 ==> b1[i] < b1[i2],
            forall|y: int| x <= y < to && #[trigger] self.has(keys[y]) ==> exists|i: int| k <= i < k2 && b1[i] == y,
        ensures self.collected(keys, from, to, b1, k2),
    {
        assert forall|i: int| 0 <= i < k2 implies from <= #[trigger] b1[i] < to && self.has(keys[b1[i] as int]) by {
            if i < k { assert(b1[i] == b0[i]); }
        }
        assert forall|i: int, i2: int| 0 <= i < i2 < k2 implies b1[i] < b1[i2] by {
            if i2 < k {
                assert(b1[i] == b0[i] && b1[i2] == b0[i2]);
            } else if i < k {
                assert(b1[i] == b0[i]);
            }
        }
        assert forall|y: int| from <= y < to && #[trigger] self.has(keys[y]) implies exists|i: int| 0 <= i < k2 && b1[i] == y by {
            if y < x {
                let i = choose|i: int| 0 <= i < k && b0[i] == y;
                assert(b1[i] == y);
            } else {
                let i = choose|i: int| k <= i < k2 && b1[i] == y;
            }
        }
    }

    /// `batch[0..k]` lists, in increasing order, exactly the positions `y` of `[from, to)` whose key is in the set.
    pub open spec fn collected(&self, keys: Seq<i64>, from: int, to: int, batch: Seq<usize>, k: int) -> bool {
        &&& 0 <= k <= to - from
        &&& k <= batch.len()
        &&& forall|i: int| 0 <= i < k ==> from <= #[trigger] batch[i] < to && self.has(keys[batch[i] as int])
        &&& forall|i: int, i2: int| 0 <= i < i2 < k ==> batch[i] < batch[i2]
        &&& forall|y: int| from <= y < to && #[trigger] self.has(keys[y]) ==> exists|i: int| 0 <= i < k && batch[i] == y
    }

    /// The positions `x` of `[from, to)` whose key `keys[x]` is in the set, in increasing order, as `batch[0..k]`
    /// (as `collect_members`), testing whole blocks of `BLOCK` rows first (`block_step`).
    pub fn collect_members_blocked(&self, keys: &[i64], n: usize, from: usize, to: usize, batch: &mut Vec<usize>) -> (k: usize)
        requires
            self.wf(),
            keys@.len() == n,
            from <= to <= n,
            to - from <= old(batch)@.len(),
        ensures
            final(batch)@.len() == old(batch)@.len(),
            k <= to - from,
            forall|i: int| 0 <= i < k ==> from <= #[trigger] final(batch)@[i] < to && self.has(keys@[final(batch)@[i] as int]),
            forall|i: int, i2: int| 0 <= i < i2 < k ==> final(batch)@[i] < final(batch)@[i2],
            forall|y: int| from <= y < to && #[trigger] self.has(keys@[y]) ==> exists|i: int| 0 <= i < k && final(batch)@[i] == y,
        no_unwind
    {
        let ghost len0 = batch@.len();
        let mut k: usize = 0;
        let mut x = from;
        while to - x >= BLOCK
            invariant
                self.wf(),
                batch@.len() == len0,
                keys@.len() == n,
                from <= x <= to <= n,
                to - from <= len0,
                k <= x - from,
                self.collected(keys@, from as int, x as int, batch@, k as int),
            decreases to - x,
        {
            k = self.block_step(keys, n, Ghost(from as int), x, batch, k);
            x = x + BLOCK;
        }
        let ghost before = batch@;
        let k2 = self.collect_into(keys, n, x, to, batch, k);
        proof {
            assert forall|i: int| 0 <= i < k2 implies from <= #[trigger] batch@[i] < to && self.has(keys@[batch@[i] as int]) by {
                if i < k { assert(batch@[i] == before[i]); }
            }
            assert forall|i: int, i2: int| 0 <= i < i2 < k2 implies batch@[i] < batch@[i2] by {
                if i2 < k {
                    assert(batch@[i] == before[i] && batch@[i2] == before[i2]);
                } else if i < k {
                    assert(batch@[i] == before[i]);
                }
            }
            assert forall|y: int| from <= y < to && #[trigger] self.has(keys@[y]) implies exists|i: int| 0 <= i < k2 && batch@[i] == y by {
                if y < x {
                    let i = choose|i: int| 0 <= i < k && before[i] == y;
                    assert(batch@[i] == y);
                } else {
                    let i = choose|i: int| k <= i < k2 && batch@[i] == y;
                }
            }
        }
        k2
    }

    /// Four collections at once (the 4 lanes of one task): lane `l` collects the members of `[a_l, a_l + len)` into
    /// `b_l` (as `collect_members_blocked`; `len` a multiple of `BLOCK`). The lanes advance one block each in turn,
    /// so a single thread keeps four memory streams in flight.
    pub fn collect4(&self, keys: &[i64], n: usize, a0: usize, a1: usize, a2: usize, a3: usize, len: usize,
        b0: &mut Vec<usize>, b1: &mut Vec<usize>, b2: &mut Vec<usize>, b3: &mut Vec<usize>) -> (r: (usize, usize, usize, usize))
        requires
            self.wf(),
            keys@.len() == n,
            len % BLOCK == 0,
            a0 + len <= n, a1 + len <= n, a2 + len <= n, a3 + len <= n,
            len <= old(b0)@.len(), len <= old(b1)@.len(), len <= old(b2)@.len(), len <= old(b3)@.len(),
        ensures
            final(b0)@.len() == old(b0)@.len(), final(b1)@.len() == old(b1)@.len(),
            final(b2)@.len() == old(b2)@.len(), final(b3)@.len() == old(b3)@.len(),
            self.collected(keys@, a0 as int, a0 + len, final(b0)@, r.0 as int),
            self.collected(keys@, a1 as int, a1 + len, final(b1)@, r.1 as int),
            self.collected(keys@, a2 as int, a2 + len, final(b2)@, r.2 as int),
            self.collected(keys@, a3 as int, a3 + len, final(b3)@, r.3 as int),
        no_unwind
    {
        let ghost (l0, l1, l2, l3) = (b0@.len(), b1@.len(), b2@.len(), b3@.len());
        let mut k0: usize = 0;
        let mut k1: usize = 0;
        let mut k2: usize = 0;
        let mut k3: usize = 0;
        let mut x: usize = 0;
        while x < len
            invariant
                self.wf(),
                keys@.len() == n,
                len % BLOCK == 0,
                x % BLOCK == 0,
                x <= len,
                a0 + len <= n, a1 + len <= n, a2 + len <= n, a3 + len <= n,
                b0@.len() == l0, b1@.len() == l1, b2@.len() == l2, b3@.len() == l3,
                len <= l0, len <= l1, len <= l2, len <= l3,
                self.collected(keys@, a0 as int, a0 + x, b0@, k0 as int),
                self.collected(keys@, a1 as int, a1 + x, b1@, k1 as int),
                self.collected(keys@, a2 as int, a2 + x, b2@, k2 as int),
                self.collected(keys@, a3 as int, a3 + x, b3@, k3 as int),
            decreases len - x,
        {
            assert(x + BLOCK <= len) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, BLOCK as int);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len as int, BLOCK as int);
            }
            k0 = self.block_step(keys, n, Ghost(a0 as int), a0 + x, b0, k0);
            k1 = self.block_step(keys, n, Ghost(a1 as int), a1 + x, b1, k1);
            k2 = self.block_step(keys, n, Ghost(a2 as int), a2 + x, b2, k2);
            k3 = self.block_step(keys, n, Ghost(a3 as int), a3 + x, b3, k3);
            x = x + BLOCK;
        }
        (k0, k1, k2, k3)
    }

    /// In dense mode, membership is the bit of the key's offset.
    proof fn lemma_dense_has(&self, k: i64)
        requires self.wf(), self.dense,
        ensures self.has(k) <==> in_bits(self.words@, self.kmin, self.kmax, k),
    {
        if self.has(k) {
            let j = choose|j: int| 0 <= j < self.keys().len() && #[trigger] self.keys()[j] == k;
            assert(self.kmin <= self.keys@[j] && self.keys@[j] - self.kmin < self.span);
            assert(bit_at(self.words@, k - self.kmin));
        }
        if in_bits(self.words@, self.kmin, self.kmax, k) {
            assert(bit_at(self.words@, k - self.kmin));
            let j = choose|j: int| 0 <= j < self.keys@.len() && self.keys@[j] - self.kmin == k - self.kmin;
            assert(self.keys()[j] == k);
        }
    }

    /// Whether `k` is one of the keys.
    pub fn contains(&self, k: i64) -> (r: bool)
        requires self.wf(),
        ensures r == exists|j: int| 0 <= j < self.keys().len() && self.keys()[j] == k,
        no_unwind
    {
        if self.dense {
            let off: i128 = k as i128 - self.kmin as i128;
            if off < 0 || off >= self.span as i128 {
                proof {
                    if exists|j: int| 0 <= j < self.keys@.len() && self.keys@[j] == k {
                        let j = choose|j: int| 0 <= j < self.keys@.len() && self.keys@[j] == k;
                        assert(self.kmin <= self.keys@[j] && self.keys@[j] - self.kmin < self.span);
                    }
                }
                return false;
            }
            let o = off as u64;
            let wi = (o / 64) as usize;
            let w = self.words[wi];
            let r = (w >> (o % 64)) & 1u64 == 1u64;
            proof {
                assert(wi as int == (o as int) / 64);
                assert(bit_at(self.words@, o as int) == r);
                if r {
                    let j = choose|j: int| 0 <= j < self.keys@.len() && self.keys@[j] - self.kmin == o as int;
                    assert(self.keys()[j] == k);
                }
                if exists|j: int| 0 <= j < self.keys@.len() && self.keys@[j] == k {
                    let j = choose|j: int| 0 <= j < self.keys@.len() && self.keys@[j] == k;
                    assert(self.keys@[j] - self.kmin == o as int);
                    assert(bit_at(self.words@, o as int));
                }
            }
            r
        } else {
            let n = self.keys.len();
            let mut i: usize = 0;
            while i < n
                invariant
                    n == self.keys@.len(),
                    i <= n,
                    forall|j: int| 0 <= j < i ==> self.keys@[j] != k,
                decreases n - i,
            {
                if self.keys[i] == k {
                    assert(self.keys()[i as int] == k);
                    return true;
                }
                i = i + 1;
            }
            false
        }
    }
}

} // verus!
