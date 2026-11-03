//! The key map: what the lineitem scan needs to know about a part key, built on the calling thread from the part
//! pass (`build_keymap`):
//!
//! 1. `concat_keys`: the part tasks' key lists in task order (or `parts::serial_keys`); `keys_ok`: each key with its
//!    branch code, and every key with a branch bit listed;
//! 2. a blocked Bloom filter of their keys (`cb`, `CB_WORDS` words: key `x` sets two bits of one word, the word
//!    from bits 6..22 of `x` and the bits `x & 63` and `(x + (x >> 22) + 21) & 63`, so the probe needs no multiplication;
//!    `hhit(cb, x)`), small enough to stay in a core's L2 cache while the scan streams `l_partkey` past it;
//! 3. a table from their keys to their branch codes (`code`: bit `k` for branch `k`), with open addressing
//!    (`common::key_tags`, home slot from the multiplicative hash `hx`); for more than `2^31` keys (never in practice: the table's
//!    size must fit `usize`) the scan searches the key list instead (`small == false`, `list_get`).
//!
//! `kbit(sv, ps, k, x)`: some part row with key `x` satisfies branch `k`. The part key is a primary key, so for a
//! lineitem row this is "its part satisfies branch `k`" (`scan::lemma_kbit_part`).
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::spec::ast::Literal;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::parts::*;
use crate::agent::common::bits::*;
use crate::agent::common::tz::{tz64, tz_table_array};
use crate::agent::common::selection::*;
use crate::agent::common::key_tags::*;

verus! {

/// Words of the Bloom filter (512 KiB): the hash's top 16 bits pick the word.
pub const CB_WORDS: usize = 65536;

/// The multiplier of the hash (2^64 / golden ratio, odd).
pub const HASH_MUL: u64 = 0x9e37_79b9_7f4a_7c15;

/// The two's-complement bits of a key (only hashed, never compared).
pub open spec fn kbits(x: i64) -> u64 { #[verifier::truncate] (x as u64) }

/// The multiplicative hash of key `x` (bits 20.. pick the table home).
pub open spec fn hx(x: i64) -> u64 { kbits(x).wrapping_mul(HASH_MUL) }

/// The filter word of key `x` (bits 6..22) and its two bits: the second is the first shifted by `21` plus bits 22..
/// (an addition, so two keys of one word do not set each other's bit pair, as an exclusive or would).
pub open spec fn hword(x: i64) -> int { ((kbits(x) >> 6u64) & 65535u64) as int }
pub open spec fn hb1(x: i64) -> u64 { kbits(x) & 63u64 }
pub open spec fn hb2(x: i64) -> u64 { (((kbits(x) & 63u64) + ((kbits(x) >> 22u64) & 63u64) + 21u64) as u64) & 63u64 }

/// Both filter bits of key `x` are set.
pub open spec fn hhit(cb: Seq<u64>, x: i64) -> bool {
    bit(cb[hword(x)], hb1(x)) && bit(cb[hword(x)], hb2(x))
}

/// The table home of key `x` for a table of `mm + 1` home slots.
pub open spec fn thome(mm: u64) -> spec_fn(i64) -> int { |x: i64| ((hx(x) >> 20u64) & mm) as int }

/// The hash of a key, as the scan and the build compute it.
#[inline(always)]
pub fn hx_exec(x: i64) -> (h: u64)
    ensures h == hx(x),
    no_unwind
{
    (#[verifier::truncate] (x as u64)).wrapping_mul(HASH_MUL)
}

/// The two's-complement bits of a key, as the scan and the build compute them.
#[inline(always)]
pub fn kbits_exec(x: i64) -> (b: u64)
    ensures b == kbits(x),
    no_unwind
{
    #[verifier::truncate] (x as u64)
}

/// The filter word and bits of a key are inside the filter and the word.
pub proof fn lemma_hword(x: i64)
    ensures 0 <= hword(x) < CB_WORDS, hb1(x) < 64, hb2(x) < 64,
{
    let k = kbits(x);
    assert((k >> 6u64) & 65535u64 < 65536u64) by (bit_vector);
    assert(k & 63u64 < 64u64) by (bit_vector);
    let t = ((k & 63u64) + ((k >> 22u64) & 63u64) + 21u64) as u64;
    assert(t & 63u64 < 64u64) by (bit_vector);
}

/// The second filter bit of a key's bits `k`, as the scan and the build compute it.
#[inline(always)]
pub fn hb2_exec(k: u64, Ghost(x): Ghost<i64>) -> (b: u64)
    requires k == kbits(x),
    ensures b == hb2(x), b < 64,
    no_unwind
{
    proof {
        assert(k & 63u64 <= 63u64) by (bit_vector);
        assert((k >> 22u64) & 63u64 <= 63u64) by (bit_vector);
        lemma_hword(x);
    }
    ((k & 63u64) + ((k >> 22u64) & 63u64) + 21u64) & 63u64
}

/// A table home is below `mm + 1`.
pub proof fn lemma_thome(mm: u64)
    ensures forall|x: i64| #[trigger] (thome(mm))(x) <= mm as int,
{
    assert forall|x: i64| #[trigger] (thome(mm))(x) <= mm as int by {
        let h = hx(x);
        assert((h >> 20u64) & mm <= mm) by (bit_vector);
    }
}

/// Part row `r` exists and satisfies some branch.
pub open spec fn anyp(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> bool {
    |r: int| r < n_p(sv) && (pcond(sv, ps, 0, r) || pcond(sv, ps, 1, r) || pcond(sv, ps, 2, r))
}

/// Some part row with key `x` satisfies branch `k`.
pub open spec fn kbit(sv: StoresView, ps: Seq<Literal>, k: int, x: int) -> bool {
    exists|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] as int == x && pcond(sv, ps, k, a)
}

/// Some part row with key `x` satisfies some branch.
pub open spec fn qkey(sv: StoresView, ps: Seq<Literal>, x: i64) -> bool {
    kbit(sv, ps, 0, x as int) || kbit(sv, ps, 1, x as int) || kbit(sv, ps, 2, x as int)
}

/// The branch code of three branch bits: bit `k` for branch `k`.
pub open spec fn code3(b0: bool, b1: bool, b2: bool) -> u8 {
    (if b0 { 1u8 } else { 0u8 }) | (if b1 { 2u8 } else { 0u8 }) | (if b2 { 4u8 } else { 0u8 })
}

/// The branch code of key `x`.
pub open spec fn code(sv: StoresView, ps: Seq<Literal>, x: i64) -> u8 {
    code3(kbit(sv, ps, 0, x as int), kbit(sv, ps, 1, x as int), kbit(sv, ps, 2, x as int))
}

/// The bits of a branch code; a code is nonzero exactly when some bit is set.
pub proof fn lemma_code3(b0: bool, b1: bool, b2: bool)
    ensures
        (code3(b0, b1, b2) & 1u8 != 0u8) == b0,
        (code3(b0, b1, b2) & 2u8 != 0u8) == b1,
        (code3(b0, b1, b2) & 4u8 != 0u8) == b2,
        (code3(b0, b1, b2) != 0u8) == (b0 || b1 || b2),
{
    let x0: u8 = if b0 { 1u8 } else { 0u8 };
    let x1: u8 = if b1 { 2u8 } else { 0u8 };
    let x2: u8 = if b2 { 4u8 } else { 0u8 };
    assert((x0 == 0u8 || x0 == 1u8) && (x1 == 0u8 || x1 == 2u8) && (x2 == 0u8 || x2 == 4u8) ==> {
        &&& ((x0 | x1 | x2) & 1u8 != 0u8) == (x0 == 1u8)
        &&& ((x0 | x1 | x2) & 2u8 != 0u8) == (x1 == 2u8)
        &&& ((x0 | x1 | x2) & 4u8 != 0u8) == (x2 == 4u8)
        &&& ((x0 | x1 | x2) != 0u8) == (x0 == 1u8 || x1 == 2u8 || x2 == 4u8)
    }) by (bit_vector);
}

/// The key map.
pub struct KeyMap {
    pub cb: Vec<u64>,
    pub keys: Vec<i64>,
    pub codes: Vec<u8>,
    pub nk: usize,
    pub small: bool,
    pub slots: Vec<(i64, u8)>,
    pub n: usize,
    pub m: usize,
    pub mm: u64,
    pub cap: usize,
}

/// The listed keys and their codes: every key with a branch bit is listed, each with its (nonzero) code.
pub open spec fn keys_ok(keys: Seq<i64>, codes: Seq<u8>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& keys.len() == codes.len()
    &&& forall|i: int| 0 <= i < keys.len() ==> #[trigger] codes[i] == code(sv, ps, keys[i]) && codes[i] != 0u8
    &&& forall|x: i64| #[trigger] qkey(sv, ps, x) ==> exists|i: int| 0 <= i < keys.len() && #[trigger] keys[i] == x
}

/// The filter holds every key with a branch bit; the key list too, and (when `small`) the table, each with its code
/// and nothing else.
pub open spec fn keymap_ok(km: KeyMap, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& km.cb@.len() == CB_WORDS
    &&& forall|x: i64| #[trigger] qkey(sv, ps, x) ==> hhit(km.cb@, x)
    &&& keys_ok(km.keys@, km.codes@, sv, ps) && km.nk == km.keys@.len()
    &&& km.small ==> {
        &&& km.mm as int == km.m - 1 && 1 <= km.m <= 0x4000_0000
        &&& km.n == km.slots@.len()
        &&& tags_wf(km.slots@, km.m as int, km.cap as int, thome(km.mm))
        &&& forall|i: int| 0 <= i < km.slots@.len() && occ(km.slots@, i) ==> #[trigger] km.slots@[i].1 == code(sv, ps, km.slots@[i].0)
        &&& forall|x: i64| #[trigger] qkey(sv, ps, x) ==> tags_key(km.slots@, x)
    }
}

// ------------------------------------------------------------------------------------------------ 1. the keys

/// The key list of the part pass: the tasks' lists in task order, each key with its branch code.
pub fn concat_keys(outs: &Vec<PartOut>, nt: usize, np: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<i64>, Vec<u8>))
    requires ptasks_ok(outs@, nt as int, sv, ps), none_full(outs@), np == n_p(sv),
    ensures keys_ok(r.0@, r.1@, sv, ps),
{
    let ghost p = anyp(sv, ps);
    let nw = np / 64 + if np % 64 != 0 { 1 } else { 0 };
    let q = nw / nt;
    let rm = nw % nt;
    let mut keys: Vec<i64> = Vec::new();
    let mut codes: Vec<u8> = Vec::new();
    let mut wl: usize = 0;
    let mut t: usize = 0;
    proof { lemma_split(nw as int, nt as int, 0); }
    while t < nt
        invariant
            ptasks_ok(outs@, nt as int, sv, ps), none_full(outs@), np == n_p(sv), nw == nwords(np as int), p == anyp(sv, ps),
            q == nw / nt, rm == nw % nt, t <= nt,
            wl == split_at(nw as int, nt as int, t as int),
            keys@.len() == codes@.len(),
            forall|i: int| 0 <= i < keys@.len() ==> #[trigger] codes@[i] == code(sv, ps, keys@[i]) && codes@[i] != 0u8,
            forall|a: int| 0 <= a < 64 * wl && #[trigger] p(a) ==> listed(keys@, keys@.len() as int, p_key(sv)[a]),
        decreases nt - t,
    {
        proof { lemma_split(nw as int, nt as int, t as int); }
        let wh = wl + q + if t < rm { 1 } else { 0 };
        let o = &outs[t];
        proof {
            assert(pout_ok(outs@[t as int], sv, ps, wl as int, wh as int));
            assert(!outs@[t as int].full);
            reveal(plist_ok);
        }
        let on = o.n;
        let base = keys.len();
        let ghost k0 = keys@;
        let mut i: usize = 0;
        while i < on
            invariant
                pout_ok(*o, sv, ps, wl as int, wh as int), !o.full, on == o.n, i <= on, p == anyp(sv, ps),
                on <= o.keys@.len(), o.codes@.len() == o.keys@.len(),
                forall|j: int| 0 <= j < on ==> #[trigger] o.codes@[j] == code(sv, ps, o.keys@[j]) && o.codes@[j] != 0u8,
                keys@.len() == base + i, codes@.len() == base + i, base == k0.len(),
                forall|j: int| 0 <= j < base ==> #[trigger] keys@[j] == k0[j],
                forall|j: int| 0 <= j < i ==> #[trigger] keys@[base + j] == o.keys@[j],
                forall|j: int| 0 <= j < keys@.len() ==> #[trigger] codes@[j] == code(sv, ps, keys@[j]) && codes@[j] != 0u8,
            decreases on - i,
        {
            let ghost (k1, c1) = (keys@, codes@);
            keys.push(o.keys[i]);
            codes.push(o.codes[i]);
            proof {
                assert forall|j: int| 0 <= j < keys@.len() implies #[trigger] codes@[j] == code(sv, ps, keys@[j]) && codes@[j] != 0u8 by {
                    if j < k1.len() { assert(codes@[j] == c1[j] && keys@[j] == k1[j]); }
                }
                assert forall|j: int| 0 <= j < i + 1 implies #[trigger] keys@[base + j] == o.keys@[j] by {
                    if j < i { assert(keys@[base + j] == k1[base + j]); }
                }
                assert forall|j: int| 0 <= j < base implies #[trigger] keys@[j] == k0[j] by {
                    assert(keys@[j] == k1[j]);
                }
            }
            i = i + 1;
        }
        proof {
            reveal(plist_ok);
            assert forall|a: int| 0 <= a < 64 * wh && #[trigger] p(a) implies listed(keys@, keys@.len() as int, p_key(sv)[a]) by {
                if a < 64 * wl {
                    lemma_listed_grow(k0, k0.len() as int, keys@, keys@.len() as int, p_key(sv)[a]);
                } else {
                    let j = choose|j: int| 0 <= j < o.n && #[trigger] o.keys@[j] == p_key(sv)[a];
                    assert(keys@[base + j] == p_key(sv)[a]);
                }
            }
        }
        wl = wh;
        t = t + 1;
    }
    proof {
        lemma_split(nw as int, nt as int, (nt - 1) as int);
        lemma_keys_complete(keys@, codes@, sv, ps, 64 * nw);
    }
    (keys, codes)
}

/// A key list holding the key of every part row below `hi >= np` that satisfies some branch, each key with its
/// branch code, lists every key with a branch bit.
pub proof fn lemma_keys_complete(keys: Seq<i64>, codes: Seq<u8>, sv: StoresView, ps: Seq<Literal>, hi: int)
    requires
        keys.len() == codes.len(), n_p(sv) <= hi,
        forall|i: int| 0 <= i < keys.len() ==> #[trigger] codes[i] == code(sv, ps, keys[i]) && codes[i] != 0u8,
        forall|a: int| 0 <= a < hi && #[trigger] (anyp(sv, ps))(a) ==> listed(keys, keys.len() as int, p_key(sv)[a]),
    ensures keys_ok(keys, codes, sv, ps),
{
    assert forall|x: i64| #[trigger] qkey(sv, ps, x) implies exists|i: int| 0 <= i < keys.len() && #[trigger] keys[i] == x by {
        let k = if kbit(sv, ps, 0, x as int) { 0int } else if kbit(sv, ps, 1, x as int) { 1int } else { 2int };
        let a = choose|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] as int == x as int && pcond(sv, ps, k, a);
        assert((anyp(sv, ps))(a));
        assert(listed(keys, keys.len() as int, p_key(sv)[a]));
    }
}

// ------------------------------------------------------------------------------------------------ 2.-3. filter, table

/// A listed row's key satisfies branch `k` exactly when the row does (the part key is a primary key).
pub proof fn lemma_kbit_row(sv: StoresView, ps: Seq<Literal>, k: int, a: int)
    requires keys_unique(p_key(sv)), 0 <= a < n_p(sv),
    ensures kbit(sv, ps, k, p_key(sv)[a] as int) == pcond(sv, ps, k, a),
{
    if kbit(sv, ps, k, p_key(sv)[a] as int) {
        let b = choose|b: int| 0 <= b < n_p(sv) && #[trigger] p_key(sv)[b] as int == p_key(sv)[a] as int && pcond(sv, ps, k, b);
        if b != a {
            assert(p_key(sv)[b] == p_key(sv)[a]);
        }
    }
}

/// Sets the two filter bits of key `x`: its probe holds, and every probe that held still does.
proof fn lemma_cb_step(cb0: Seq<u64>, cb: Seq<u64>, x: i64)
    requires
        cb0.len() == CB_WORDS,
        cb == cb0.update(hword(x), cb0[hword(x)] | (1u64 << hb1(x)) | (1u64 << hb2(x))),
    ensures
        cb.len() == CB_WORDS,
        hhit(cb, x),
        forall|y: i64| #[trigger] hhit(cb0, y) ==> hhit(cb, y),
{
    lemma_hword(x);
    let w0 = cb0[hword(x)];
    let b1 = hb1(x);
    let b2 = hb2(x);
    assert(cb[hword(x)] == (w0 | (1u64 << b1)) | (1u64 << b2));
    assert forall|u: u64| u < 64 implies #[trigger] bit(cb[hword(x)], u) == (u == b2 || u == b1 || bit(w0, u)) by {
        lemma_bit_or_set(w0 | (1u64 << b1), b2, u);
        lemma_bit_or_set(w0, b1, u);
    }
    assert forall|y: i64| #[trigger] hhit(cb0, y) implies hhit(cb, y) by {
        lemma_hword(y);
        if hword(y) == hword(x) {
            assert(bit(cb[hword(x)], hb1(y)));
            assert(bit(cb[hword(x)], hb2(y)));
        }
    }
}

/// Sets the two filter bits of key `x`.
fn filter_add(cb: &mut Vec<u64>, x: i64)
    requires old(cb)@.len() == CB_WORDS,
    ensures
        final(cb)@.len() == CB_WORDS,
        hhit(final(cb)@, x),
        forall|y: i64| #[trigger] hhit(old(cb)@, y) ==> hhit(final(cb)@, y),
{
    let ghost cb0 = cb@;
    let k = kbits_exec(x);
    proof {
        lemma_hword(x);
        assert((k >> 6u64) & 65535u64 < 65536u64) by (bit_vector);
    }
    let hw = ((k >> 6u64) & 65535u64) as usize;
    let b2 = hb2_exec(k, Ghost(x));
    cb.set(hw, cb[hw] | (1u64 << (k & 63u64)) | (1u64 << b2));
    proof {
        lemma_cb_step(cb0, cb@, x);
    }
}

/// Adds key `x` with its branch code `tag` (nonzero) to the table; what it held before it still holds.
fn table_add(slots: &mut Vec<(i64, u8)>, x: i64, tag: u8, mm: u64,
    Ghost(m): Ghost<int>, Ghost(cap): Ghost<int>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    requires
        tags_wf(old(slots)@, m, cap, thome(mm)), mm as int == m - 1, 1 <= m <= 0x4000_0000,
        occ_count(old(slots)@, 0, old(slots)@.len() as int) < cap,
        tag != 0u8, tag == code(sv, ps, x),
        forall|i: int| 0 <= i < old(slots)@.len() && occ(old(slots)@, i) ==> #[trigger] old(slots)@[i].1 == code(sv, ps, old(slots)@[i].0),
    ensures
        tags_wf(final(slots)@, m, cap, thome(mm)),
        occ_count(final(slots)@, 0, final(slots)@.len() as int) == occ_count(old(slots)@, 0, old(slots)@.len() as int) + 1,
        forall|i: int| 0 <= i < final(slots)@.len() && occ(final(slots)@, i) ==> #[trigger] final(slots)@[i].1 == code(sv, ps, final(slots)@[i].0),
        tags_key(final(slots)@, x),
        forall|y: i64| #[trigger] tags_key(old(slots)@, y) ==> tags_key(final(slots)@, y),
{
    let ghost s0 = slots@;
    let h = hx_exec(x);
    proof {
        lemma_thome(mm);
        assert((h >> 20u64) & mm <= mm) by (bit_vector);
    }
    let hm = ((h >> 20u64) & mm) as usize;
    proof {
        assert(hm as int == (thome(mm))(x));
    }
    tags_put(slots, x, tag, hm, Ghost(m), Ghost(cap), Ghost(thome(mm)));
    proof {
        let s1 = slots@;
        assert forall|i: int| 0 <= i < s1.len() && occ(s1, i) implies #[trigger] s1[i].1 == code(sv, ps, s1[i].0) by {
            if s1[i] != (x, tag) {
                assert(occ(s0, i) && s1[i] == s0[i]);
            }
        }
        let pi = choose|pi: int| 0 <= pi < s1.len() && occ(s1, pi) && #[trigger] s1[pi] == (x, tag);
        assert(s1[pi].0 == x);
        assert forall|y: i64| #[trigger] tags_key(s0, y) implies tags_key(s1, y) by {
            let q = choose|q: int| 0 <= q < s0.len() && occ(s0, q) && #[trigger] s0[q].0 == y;
            assert(s1[q] == s0[q]);
        }
    }
}

/// The filter of the listed keys.
fn build_filter(keys: &Vec<i64>, codes: &Vec<u8>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (cb: Vec<u64>)
    requires keys_ok(keys@, codes@, sv, ps),
    ensures cb@.len() == CB_WORDS, forall|x: i64| #[trigger] qkey(sv, ps, x) ==> hhit(cb@, x),
{
    let n = keys.len();
    let mut cb: Vec<u64> = vec![0u64; CB_WORDS];
    let mut j: usize = 0;
    while j < n
        invariant
            n == keys@.len(), j <= n, cb@.len() == CB_WORDS,
            forall|i: int| 0 <= i < j ==> #[trigger] hhit(cb@, keys@[i]),
        decreases n - j,
    {
        let ghost cb0 = cb@;
        filter_add(&mut cb, keys[j]);
        proof {
            assert forall|i: int| 0 <= i < j + 1 implies #[trigger] hhit(cb@, keys@[i]) by {
                if i < j { assert(hhit(cb0, keys@[i])); }
            }
        }
        j = j + 1;
    }
    proof {
        assert forall|x: i64| #[trigger] qkey(sv, ps, x) implies hhit(cb@, x) by {
            let i = choose|i: int| 0 <= i < keys@.len() && #[trigger] keys@[i] == x;
            assert(hhit(cb@, keys@[i]));
        }
    }
    cb
}

/// The table of the listed keys and codes: `m` home slots (a power of two at least twice the keys, at most `2^30`)
/// and `n` more.
fn build_table(keys: &Vec<i64>, codes: &Vec<u8>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<(i64, u8)>, usize, u64))
    requires keys_ok(keys@, codes@, sv, ps), keys@.len() < 0x8000_0000,
    ensures ({
        let (slots, m, mm) = r;
        &&& mm as int == m - 1 && 1 <= m <= 0x4000_0000
        &&& tags_wf(slots@, m as int, keys@.len() as int, thome(mm))
        &&& forall|i: int| 0 <= i < slots@.len() && occ(slots@, i) ==> #[trigger] slots@[i].1 == code(sv, ps, slots@[i].0)
        &&& forall|x: i64| #[trigger] qkey(sv, ps, x) ==> tags_key(slots@, x)
    }),
{
    let n = keys.len();
    let mut m: usize = 16;
    while m / 2 < n && m < 0x2000_0000
        invariant 16 <= m <= 0x4000_0000,
        decreases 0x4000_0000 - m,
    {
        m = m * 2;
    }
    let mm = (m - 1) as u64;
    let ghost home = thome(mm);
    proof {
        lemma_thome(mm);
        assert forall|x: i64| 0 <= #[trigger] home(x) < m by {}
    }
    let mut slots = tags_new(m, n, Ghost(home));
    proof {
        lemma_count_none(slots@, 0, slots@.len() as int);
    }
    let mut j: usize = 0;
    while j < n
        invariant
            keys_ok(keys@, codes@, sv, ps), n == keys@.len(), j <= n,
            1 <= m <= 0x4000_0000, mm as int == m - 1, home == thome(mm),
            tags_wf(slots@, m as int, n as int, home),
            occ_count(slots@, 0, slots@.len() as int) == j,
            forall|i: int| 0 <= i < slots@.len() && occ(slots@, i) ==> #[trigger] slots@[i].1 == code(sv, ps, slots@[i].0),
            forall|i: int| 0 <= i < j ==> tags_key(slots@, #[trigger] keys@[i]),
        decreases n - j,
    {
        let ghost s0 = slots@;
        let key = keys[j];
        let tag = codes[j];
        table_add(&mut slots, key, tag, mm, Ghost(m as int), Ghost(n as int), Ghost(sv), Ghost(ps));
        proof {
            assert forall|i: int| 0 <= i < j + 1 implies tags_key(slots@, #[trigger] keys@[i]) by {
                if i < j {
                    assert(tags_key(s0, keys@[i]));
                }
            }
        }
        j = j + 1;
    }
    proof {
        assert forall|x: i64| #[trigger] qkey(sv, ps, x) implies tags_key(slots@, x) by {
            let i = choose|i: int| 0 <= i < keys@.len() && #[trigger] keys@[i] == x;
            assert(tags_key(slots@, keys@[i]));
        }
    }
    (slots, m, mm)
}

/// The key map of the listed keys and codes.
pub fn build_keymap(keys: Vec<i64>, codes: Vec<u8>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (km: KeyMap)
    requires keys_ok(keys@, codes@, sv, ps),
    ensures keymap_ok(km, sv, ps),
{
    let cb = build_filter(&keys, &codes, Ghost(sv), Ghost(ps));
    let nk = keys.len();
    if nk < 0x8000_0000 {
        let (slots, m, mm) = build_table(&keys, &codes, Ghost(sv), Ghost(ps));
        let n = slots.len();
        KeyMap { cb, keys, codes, nk, small: true, slots, n, m, mm, cap: nk }
    } else {
        KeyMap { cb, keys, codes, nk, small: false, slots: Vec::new(), n: 0, m: 1, mm: 0, cap: 0 }
    }
}

/// The code of `key` from the key list (0 when it is not listed), by a linear search; `nk` is the list's length.
pub fn list_get(keys: &Vec<i64>, codes: &Vec<u8>, nk: usize, key: i64, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (tag: u8)
    requires keys_ok(keys@, codes@, sv, ps), nk == keys@.len(),
    ensures
        tag != 0u8 ==> tag == code(sv, ps, key),
        tag == 0u8 ==> !qkey(sv, ps, key),
    no_unwind
{
    let mut i: usize = 0;
    while i < nk
        invariant keys_ok(keys@, codes@, sv, ps), nk == keys@.len(), i <= nk,
            forall|j: int| 0 <= j < i ==> #[trigger] keys@[j] != key,
        decreases nk - i,
    {
        if keys[i] == key {
            proof { assert(codes@[i as int] == code(sv, ps, keys@[i as int])); }
            return codes[i];
        }
        i = i + 1;
    }
    0
}

} // verus!
