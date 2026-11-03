//! The per-worker lookup structure of the qualifying subs (`fy = $2`): sub adsh bytes -> rank of the sub among the
//! qualifying subs in row order. Every worker builds its own copy (worker bodies cannot share heap data).
//!
//! Layout: `table` is a linear-probing table without wrap-around (`nslots >= 2^bits + nq + 1` slots, home slot = the
//! top `bits` bits of the key hash); a slot is 0 (empty) or `tag << 32 | (rank + 1)`, where the tag is 24 fingerprint
//! bits of the hash and the key length (when it is 16..24, else 0). `kw[3 rank ..]` holds the key's three words
//! (`common::bytes::key_words_spec`); `qsub[rank]` its sub row; `bloom` has bit `hash >> 44` (the top 20 hash bits) set for every key.
//!
//! Invariants (`keys_inv`): every stored rank's home slot is at or before its slot and every slot in between is
//! occupied, so a probe that meets an empty slot (or the end) has seen every slot that could hold the key.
use vstd::prelude::*;
use crate::link::query::{text_wf, text_at, TextView};
use crate::agent::common::bytes::*;

verus! {

/// The sub columns a worker reads (whole parts) and the parameter `$2`.
#[derive(Clone, Copy)]
pub struct SubCols {
    pub adsh_off: &'static [i64],
    pub adsh_bytes: &'static [u8],
    pub fy: &'static [i32],
    pub fy_valid: &'static [u8],
    /// Number of sub rows.
    pub n: usize,
    /// Number of adsh bytes.
    pub bytes_len: usize,
    pub p1: i32,
}

impl SubCols {
    pub open spec fn text(&self) -> TextView {
        TextView { offsets: self.adsh_off@, bytes: self.adsh_bytes@ }
    }

    /// The adsh bytes of sub row `j`.
    pub open spec fn key(&self, j: int) -> Seq<u8> {
        text_at(self.text(), j)
    }

    /// Sub row `j` has `fy = $2`.
    pub open spec fn qual(&self, j: int) -> bool {
        self.fy_valid@[j] != 0 && self.fy@[j] == self.p1
    }

    /// The qualifying sub rows below `m`, in row order.
    pub open spec fn qlist(&self, m: int) -> Seq<int>
        decreases m,
    {
        if m <= 0 { Seq::empty() } else if self.qual(m - 1) { self.qlist(m - 1).push(m - 1) } else { self.qlist(m - 1) }
    }

    pub open spec fn wf(&self) -> bool {
        &&& text_wf(self.text(), self.n as int)
        &&& self.fy@.len() == self.n && self.fy_valid@.len() == self.n
        &&& self.bytes_len == self.adsh_bytes@.len()
        &&& self.n < 0xffff_fff0
        &&& forall|j1: int, j2: int| 0 <= j1 < self.n && 0 <= j2 < self.n && j1 != j2
            ==> #[trigger] self.key(j1) != #[trigger] self.key(j2)
    }
}

/// The qualifying list's members: distinct, increasing sub rows below `m`, exactly the qualifying ones.
pub proof fn lemma_qlist(sc: &SubCols, m: int)
    requires 0 <= m,
    ensures
        sc.qlist(m).len() <= m,
        forall|a: int| 0 <= a < sc.qlist(m).len() ==> 0 <= #[trigger] sc.qlist(m)[a] < m && sc.qual(sc.qlist(m)[a]),
        forall|a: int, b: int| 0 <= a < b < sc.qlist(m).len() ==> #[trigger] sc.qlist(m)[a] < #[trigger] sc.qlist(m)[b],
        forall|j: int| 0 <= j < m && sc.qual(j) ==> exists|a: int| 0 <= a < sc.qlist(m).len() && #[trigger] sc.qlist(m)[a] == j,
    decreases m,
{
    if m > 0 {
        lemma_qlist(sc, m - 1);
        let q = sc.qlist(m - 1);
        if sc.qual(m - 1) {
            assert(sc.qlist(m) == q.push(m - 1));
            assert forall|j: int| 0 <= j < m && sc.qual(j) implies exists|a: int| 0 <= a < sc.qlist(m).len() && #[trigger] sc.qlist(m)[a] == j by {
                if j == m - 1 {
                    assert(sc.qlist(m)[q.len() as int] == j);
                } else {
                    let a = choose|a: int| 0 <= a < q.len() && #[trigger] q[a] == j;
                    assert(sc.qlist(m)[a] == j);
                }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------- slot encoding

/// The tag of a key: 24 hash bits and the covered length (0 for other lengths).
pub open spec fn tag_of(s: Seq<u8>) -> u64 {
    (((key_hash_spec(s) >> 20u64) & 0xff_ffffu64) << 8u64) | (if fast_len(s.len() as int) { s.len() as u64 } else { 0u64 })
}

pub open spec fn slot_of(tag: u64, id: int) -> u64 {
    (tag << 32u64) | ((id + 1) as u64)
}

pub open spec fn slot_id(slot: u64) -> int {
    (slot & 0xffff_ffffu64) as int - 1
}

pub open spec fn slot_tag(slot: u64) -> u64 {
    slot >> 32u64
}

/// The home slot of a hash.
pub open spec fn home(h: u64, bits: u64) -> int {
    (h >> ((64 - bits) as u64)) as int
}

pub open spec fn bloom_bit(h: u64) -> int {
    (h >> 44u64) as int
}

pub open spec fn bit_set(words: Seq<u64>, b: int) -> bool {
    (words[b / 64] >> ((b % 64) as u64)) & 1u64 == 1u64
}

pub proof fn lemma_tag_bound(s: Seq<u8>)
    ensures tag_of(s) < 0x1_0000_0000,
{
    let h = key_hash_spec(s);
    let l: u64 = if fast_len(s.len() as int) { s.len() as u64 } else { 0u64 };
    assert(l < 256);
    assert((((h >> 20u64) & 0xff_ffffu64) << 8u64) | l < 0x1_0000_0000u64) by (bit_vector) requires l < 256u64;
}

pub proof fn lemma_slot_parts(tag: u64, id: int)
    requires tag < 0x1_0000_0000, 0 <= id < 0xffff_fff0,
    ensures slot_of(tag, id) != 0, slot_id(slot_of(tag, id)) == id, slot_tag(slot_of(tag, id)) == tag,
{
    let x = (id + 1) as u64;
    assert(((tag << 32u64) | x) & 0xffff_ffffu64 == x && ((tag << 32u64) | x) >> 32u64 == tag && ((tag << 32u64) | x) != 0)
        by (bit_vector) requires tag < 0x1_0000_0000u64, 0 < x, x < 0x1_0000_0000u64;
}

pub proof fn lemma_slot_low(slot: u64)
    ensures slot & 0xffff_ffffu64 <= 0xffff_ffffu64,
{
    assert(slot & 0xffff_ffffu64 <= 0xffff_ffffu64) by (bit_vector);
}

pub proof fn lemma_home_bound(h: u64, bits: u64)
    requires 1 <= bits <= 30,
    ensures 0 <= home(h, bits) < pow2i(bits as nat), home(h, bits) < 0x4000_0000,
{
    let sh = (64 - bits) as u64;
    assert(h >> sh < 1u64 << bits) by (bit_vector) requires 1 <= bits <= 30, sh == 64 - bits;
    assert(1u64 << bits <= 0x4000_0000u64) by (bit_vector) requires 1 <= bits <= 30;
    vstd::bits::lemma_u64_pow2_no_overflow(bits as nat);
    vstd::bits::lemma_u64_shl_is_mul(1, bits);
}

pub open spec fn pow2i(n: nat) -> int {
    vstd::arithmetic::power2::pow2(n) as int
}

/// The bloom bit of a hash, its word and its position in the word.
pub proof fn lemma_bloom_idx(h: u64)
    ensures
        0 <= bloom_bit(h) < 0x10_0000,
        ((h >> 44u64) >> 6u64) as int == bloom_bit(h) / 64,
        ((h >> 44u64) & 63u64) as int == bloom_bit(h) % 64,
        (h >> 44u64) >> 6u64 < 0x4000,
        (h >> 44u64) & 63u64 < 64,
{
    let x = h >> 44u64;
    assert(x < 0x10_0000u64) by (bit_vector) requires x == h >> 44u64;
    assert(x >> 6u64 == x / 64u64) by (bit_vector);
    assert(x & 63u64 == x % 64u64) by (bit_vector);
}

/// Setting a bit sets it and keeps the others.
pub proof fn lemma_set_bit(x: u64, b: u64, c: u64)
    requires b < 64, c < 64,
    ensures
        ((x | (1u64 << b)) >> b) & 1u64 == 1u64,
        (x >> c) & 1u64 == 1u64 ==> ((x | (1u64 << b)) >> c) & 1u64 == 1u64,
{
    assert(((x | (1u64 << b)) >> b) & 1u64 == 1u64) by (bit_vector) requires b < 64;
    assert((x >> c) & 1u64 == 1u64 ==> ((x | (1u64 << b)) >> c) & 1u64 == 1u64) by (bit_vector) requires b < 64, c < 64;
}

// --------------------------------------------------------------------------------------------- the key structure

pub struct Keys {
    pub bits: u64,
    pub nslots: usize,
    pub table: Vec<u64>,
    pub bloom: Vec<u64>,
    pub kw: Vec<u64>,
    pub qsub: Vec<u32>,
}

/// The contents of a `Keys`.
pub struct KeysView {
    pub bits: u64,
    pub nslots: int,
    pub table: Seq<u64>,
    pub bloom: Seq<u64>,
    pub kw: Seq<u64>,
    pub qsub: Seq<u32>,
}

impl Keys {
    pub open spec fn view(&self) -> KeysView {
        KeysView { bits: self.bits, nslots: self.nslots as int, table: self.table@, bloom: self.bloom@, kw: self.kw@, qsub: self.qsub@ }
    }
}

/// Number of occupied slots among the first `m`.
pub open spec fn occupied(table: Seq<u64>, m: int) -> int
    decreases m,
{
    if m <= 0 { 0 } else { occupied(table, m - 1) + if table[m - 1] != 0 { 1int } else { 0int } }
}

/// Rank `id` is in some slot.
pub open spec fn stored(v: KeysView, id: int) -> bool {
    exists|s: int| 0 <= s < v.nslots && #[trigger] v.table[s] != 0 && slot_id(v.table[s]) == id
}

/// The key of rank `id`.
pub open spec fn rank_key(sc: &SubCols, id: int) -> Seq<u8> {
    sc.key(sc.qlist(sc.n as int)[id])
}

/// Occupied slot `s`: a rank below `nq` with its tag, at or after its home, every slot from the home on occupied.
pub open spec fn slot_ok(v: KeysView, sc: &SubCols, nq: int, s: int) -> bool {
    let id = slot_id(v.table[s]);
    let key = rank_key(sc, id);
    &&& 0 <= id < nq
    &&& slot_tag(v.table[s]) == tag_of(key)
    &&& home(key_hash_spec(key), v.bits) <= s
    &&& forall|t: int| home(key_hash_spec(key), v.bits) <= t < s ==> #[trigger] v.table[t] != 0
}

/// The shape of the structure for the qualifying subs of `sc`.
pub open spec fn keys_shape(v: KeysView, sc: &SubCols) -> bool {
    &&& 1 <= v.bits <= 30
    &&& v.nslots == v.table.len()
    &&& v.nslots < usize::MAX
    &&& v.bloom.len() == 0x4000
    &&& v.kw.len() >= 3 * sc.qlist(sc.n as int).len()
    &&& v.kw.len() < usize::MAX
    &&& v.qsub.len() >= sc.qlist(sc.n as int).len()
    &&& pow2i(v.bits as nat) + sc.qlist(sc.n as int).len() < v.nslots
}

/// The structure holds the first `nq` qualifying subs.
#[verifier::opaque]
pub open spec fn keys_inv(v: KeysView, sc: &SubCols, nq: int) -> bool {
    &&& keys_shape(v, sc)
    &&& 0 <= nq <= sc.qlist(sc.n as int).len()
    &&& forall|id: int| 0 <= id < nq ==> #[trigger] v.qsub[id] as int == sc.qlist(sc.n as int)[id]
    &&& forall|id: int| 0 <= id < nq ==>
        (#[trigger] v.kw[3 * id], v.kw[3 * id + 1], v.kw[3 * id + 2]) == key_words_spec(rank_key(sc, id))
    &&& forall|id: int| 0 <= id < nq ==> bit_set(v.bloom, bloom_bit(key_hash_spec(#[trigger] rank_key(sc, id))))
    &&& forall|s: int| 0 <= s < v.nslots && #[trigger] v.table[s] != 0 ==> slot_ok(v, sc, nq, s)
    &&& forall|id: int| 0 <= id < nq ==> #[trigger] stored(v, id)
    &&& occupied(v.table, v.nslots) == nq
}

pub proof fn lemma_inv_shape(v: KeysView, sc: &SubCols, nq: int)
    requires keys_inv(v, sc, nq),
    ensures keys_shape(v, sc), 0 <= nq <= sc.qlist(sc.n as int).len(), occupied(v.table, v.nslots) == nq,
{
    reveal(keys_inv);
}

pub proof fn lemma_inv_rank(v: KeysView, sc: &SubCols, nq: int, id: int)
    requires keys_inv(v, sc, nq), 0 <= id < nq,
    ensures
        v.qsub[id] as int == sc.qlist(sc.n as int)[id],
        (v.kw[3 * id], v.kw[3 * id + 1], v.kw[3 * id + 2]) == key_words_spec(rank_key(sc, id)),
        bit_set(v.bloom, bloom_bit(key_hash_spec(rank_key(sc, id)))),
        stored(v, id),
{
    reveal(keys_inv);
}

pub proof fn lemma_inv_slot(v: KeysView, sc: &SubCols, nq: int, s: int)
    requires keys_inv(v, sc, nq), 0 <= s < v.nslots, v.table[s] != 0,
    ensures slot_ok(v, sc, nq, s),
{
    reveal(keys_inv);
}

pub proof fn lemma_occupied_nonneg(table: Seq<u64>, m: int)
    ensures occupied(table, m) >= 0,
    decreases m,
{
    if m > 0 {
        lemma_occupied_nonneg(table, m - 1);
    }
}

pub proof fn lemma_occupied_range(table: Seq<u64>, m: int, a: int, b: int)
    requires 0 <= a <= b <= m <= table.len(), forall|t: int| a <= t < b ==> #[trigger] table[t] != 0,
    ensures occupied(table, m) >= b - a,
    decreases m,
{
    if a == b {
        lemma_occupied_nonneg(table, m);
    } else if m > b {
        lemma_occupied_range(table, m - 1, a, b);
    } else {
        lemma_occupied_range(table, m - 1, a, b - 1);
        assert(table[m - 1] != 0);
    }
}

pub proof fn lemma_occupied_same(a: Seq<u64>, b: Seq<u64>, m: int)
    requires 0 <= m <= a.len(), m <= b.len(), forall|t: int| 0 <= t < m ==> #[trigger] a[t] == b[t],
    ensures occupied(a, m) == occupied(b, m),
    decreases m,
{
    if m > 0 {
        lemma_occupied_same(a, b, m - 1);
    }
}

pub proof fn lemma_occupied_update(table: Seq<u64>, m: int, s: int, v: u64)
    requires 0 <= s < m <= table.len(), table[s] == 0, v != 0,
    ensures occupied(table.update(s, v), m) == occupied(table, m) + 1,
    decreases m,
{
    if m - 1 > s {
        lemma_occupied_update(table, m - 1, s, v);
    } else {
        lemma_occupied_same(table, table.update(s, v), s);
    }
}

pub proof fn lemma_occupied_zero(table: Seq<u64>, m: int)
    requires 0 <= m <= table.len(), forall|t: int| 0 <= t < m ==> #[trigger] table[t] == 0,
    ensures occupied(table, m) == 0,
    decreases m,
{
    if m > 0 {
        lemma_occupied_zero(table, m - 1);
    }
}

/// An empty structure holds no sub.
pub proof fn lemma_inv_init(v: KeysView, sc: &SubCols)
    requires
        keys_shape(v, sc),
        forall|s: int| 0 <= s < v.table.len() ==> #[trigger] v.table[s] == 0,
    ensures keys_inv(v, sc, 0),
{
    reveal(keys_inv);
    lemma_occupied_zero(v.table, v.nslots);
}

/// Inserting rank `id` (sub row `j`) at the empty slot `s` reached from its home.
pub proof fn lemma_inv_insert(v0: KeysView, v1: KeysView, sc: &SubCols, id: int, s: int)
    requires
        keys_inv(v0, sc, id),
        0 <= id < sc.qlist(sc.n as int).len(),
        id < 0xffff_fff0,
        0 <= s < v0.nslots,
        v0.table[s] == 0,
        home(key_hash_spec(rank_key(sc, id)), v0.bits) <= s,
        forall|t: int| home(key_hash_spec(rank_key(sc, id)), v0.bits) <= t < s ==> #[trigger] v0.table[t] != 0,
        v1.bits == v0.bits, v1.nslots == v0.nslots,
        v1.table == v0.table.update(s, slot_of(tag_of(rank_key(sc, id)), id)),
        ({
            let w = key_words_spec(rank_key(sc, id));
            v1.kw == v0.kw.update(3 * id, w.0).update(3 * id + 1, w.1).update(3 * id + 2, w.2)
        }),
        v1.qsub == v0.qsub.update(id, sc.qlist(sc.n as int)[id] as u32),
        0 <= sc.qlist(sc.n as int)[id] < 0x1_0000_0000,
        ({
            let b = bloom_bit(key_hash_spec(rank_key(sc, id)));
            v1.bloom == v0.bloom.update(b / 64, v0.bloom[b / 64] | (1u64 << ((b % 64) as u64)))
        }),
    ensures keys_inv(v1, sc, id + 1),
{
    reveal(keys_inv);
    let key = rank_key(sc, id);
    let tag = tag_of(key);
    lemma_tag_bound(key);
    lemma_slot_parts(tag, id);
    lemma_occupied_update(v0.table, v0.nslots, s, slot_of(tag, id));
    let b = bloom_bit(key_hash_spec(key));
    lemma_bloom_idx(key_hash_spec(key));
    assert forall|i: int| 0 <= i < id + 1 implies bit_set(v1.bloom, bloom_bit(key_hash_spec(#[trigger] rank_key(sc, i)))) by {
        let c = bloom_bit(key_hash_spec(rank_key(sc, i)));
        lemma_bloom_idx(key_hash_spec(rank_key(sc, i)));
        lemma_set_bit(v0.bloom[b / 64], (b % 64) as u64, (c % 64) as u64);
    }
    assert forall|i: int| 0 <= i < id + 1 implies #[trigger] v1.qsub[i] as int == sc.qlist(sc.n as int)[i] by {
        if i < id {
            assert(v1.qsub[i] == v0.qsub[i]);
        }
    }
    assert forall|i: int| 0 <= i < id + 1 implies
        (#[trigger] v1.kw[3 * i], v1.kw[3 * i + 1], v1.kw[3 * i + 2]) == key_words_spec(rank_key(sc, i)) by {
        if i < id {
            assert(v1.kw[3 * i] == v0.kw[3 * i]);
            assert(v1.kw[3 * i + 1] == v0.kw[3 * i + 1]);
            assert(v1.kw[3 * i + 2] == v0.kw[3 * i + 2]);
        }
    }
    assert forall|t: int| 0 <= t < v1.nslots && #[trigger] v1.table[t] != 0 implies slot_ok(v1, sc, id + 1, t) by {
        if t != s {
            assert(v1.table[t] == v0.table[t]);
            assert(slot_ok(v0, sc, id, t));
            let k2 = rank_key(sc, slot_id(v0.table[t]));
            assert forall|u: int| home(key_hash_spec(k2), v1.bits) <= u < t implies #[trigger] v1.table[u] != 0 by {
                if u != s {
                    assert(v1.table[u] == v0.table[u]);
                }
            }
        } else {
            assert forall|u: int| home(key_hash_spec(key), v1.bits) <= u < t implies #[trigger] v1.table[u] != 0 by {
                assert(v1.table[u] == v0.table[u]);
            }
        }
    }
    assert forall|i: int| 0 <= i < id + 1 implies #[trigger] stored(v1, i) by {
        if i == id {
            assert(v1.table[s] != 0 && slot_id(v1.table[s]) == i);
        } else {
            assert(stored(v0, i));
            let t = choose|t: int| 0 <= t < v0.nslots && #[trigger] v0.table[t] != 0 && slot_id(v0.table[t]) == i;
            assert(t != s);
            assert(v1.table[t] == v0.table[t]);
        }
    }
}

/// `qlist(m)` is a prefix of `qlist(m2)` for `m <= m2`.
pub proof fn lemma_qlist_prefix(sc: &SubCols, m: int, m2: int)
    requires 0 <= m <= m2,
    ensures
        sc.qlist(m).len() <= sc.qlist(m2).len(),
        forall|a: int| 0 <= a < sc.qlist(m).len() ==> #[trigger] sc.qlist(m)[a] == sc.qlist(m2)[a],
    decreases m2 - m,
{
    if m < m2 {
        lemma_qlist_prefix(sc, m, m2 - 1);
        lemma_qlist(sc, m2 - 1);
    }
}

/// Insert every qualifying sub (rank order): words, rank -> sub row, bloom bit and slot.
pub fn build_keys(keys: &mut Keys, sc: &SubCols)
    requires
        sc.wf(),
        keys_shape(old(keys).view(), sc),
        forall|s: int| 0 <= s < old(keys).table@.len() ==> #[trigger] old(keys).table@[s] == 0,
    ensures
        keys_inv(final(keys).view(), sc, sc.qlist(sc.n as int).len() as int),
        final(keys).bits == old(keys).bits,
        final(keys).nslots == old(keys).nslots,
    no_unwind
{
    let ghost ql = sc.qlist(sc.n as int);
    proof {
        lemma_qlist(sc, sc.n as int);
        lemma_inv_init(keys.view(), sc);
    }
    let n = sc.n;
    let bits = keys.bits;
    let nslots = keys.nslots;
    let mut j: usize = 0;
    let mut id: usize = 0;
    while j < n
        invariant
            sc.wf(), n == sc.n, bits == keys.bits, nslots == keys.nslots, ql == sc.qlist(sc.n as int),
            j <= n,
            id == sc.qlist(j as int).len(),
            keys_inv(keys.view(), sc, id as int),
        decreases n - j,
    {
        proof {
            lemma_qlist(sc, j as int);
            lemma_qlist(sc, j as int + 1);
            lemma_qlist(sc, sc.n as int);
            lemma_qlist_prefix(sc, j as int + 1, sc.n as int);
            lemma_inv_shape(keys.view(), sc, id as int);
        }
        if sc.fy_valid[j] != 0 && sc.fy[j] == sc.p1 {
            proof {
                // The rank-`id` qualifying sub is `j`.
                assert(sc.qlist(j as int + 1) == sc.qlist(j as int).push(j as int));
                assert(sc.qlist(j as int + 1)[id as int] == j as int);
                assert(ql[id as int] == j as int);
            }
            let ghost vstart = keys.view();
            assert(id < ql.len()) by {
                lemma_qlist_prefix(sc, j as int + 1, sc.n as int);
            }
            assert(3 * id + 2 < keys.kw@.len());
            assert(id < keys.qsub@.len());
            let a = sc.adsh_off[j] as usize;
            let b = sc.adsh_off[j + 1] as usize;
            let x = sub_bytes(sc.adsh_bytes, a, b);
            assert(x@ == rank_key(sc, id as int));
            let w = key_words(x, b - a);
            let h = key_hash(b - a, w);
            proof {
                lemma_bloom_idx(h);
                lemma_home_bound(h, bits);
            }
            let bit = h >> 44u64;
            let wi = (bit >> 6u64) as usize;
            let bi = bit & 63u64;
            let old_word = keys.bloom[wi];
            keys.bloom[wi] = old_word | (1u64 << bi);
            let ghost v0 = keys.view();
            let mut s = (h >> (64 - bits)) as usize;
            let ghost hm = s as int;
            while s < nslots && keys.table[s] != 0
                invariant
                    hm <= s <= nslots, nslots == keys.table@.len(), keys.view() == v0,
                    forall|t: int| hm <= t < s ==> #[trigger] keys.table@[t] != 0,
                decreases nslots - s,
            {
                s = s + 1;
            }
            proof {
                // An empty slot exists before the end: only `id` slots are occupied.
                if s == nslots {
                    lemma_occupied_range(keys.table@, nslots as int, hm, nslots as int);
                    assert(false);
                }
                lemma_tag_bound(x@);
            }
            let len_tag: u64 = if 16 <= b - a && b - a <= 24 { (b - a) as u64 } else { 0 };
            let tag: u64 = (((h >> 20u64) & 0xff_ffffu64) << 8u64) | len_tag;
            assert(tag == tag_of(x@));
            let slot: u64 = (tag << 32u64) | ((id + 1) as u64);
            keys.table[s] = slot;
            keys.kw[3 * id] = w.0;
            keys.kw[3 * id + 1] = w.1;
            keys.kw[3 * id + 2] = w.2;
            keys.qsub[id] = j as u32;
            proof {
                assert(keys.view().bloom == vstart.bloom.update(wi as int, vstart.bloom[wi as int] | (1u64 << bi)));
                assert(keys.view().table == vstart.table.update(s as int, slot));
                lemma_inv_insert(vstart, keys.view(), sc, id as int, s as int);
            }
            id = id + 1;
        }
        j = j + 1;
    }
}

/// A probe that met an empty slot (or the end) at `s`, every slot from the home on occupied by another key: no
/// rank has key `x`.
pub proof fn lemma_probe_absent(v: KeysView, sc: &SubCols, nq: int, x: Seq<u8>, s: int)
    requires
        keys_inv(v, sc, nq),
        home(key_hash_spec(x), v.bits) <= s <= v.nslots,
        s == v.nslots || v.table[s] == 0,
        forall|t: int| home(key_hash_spec(x), v.bits) <= t < s ==> #[trigger] v.table[t] != 0 && rank_key(sc, slot_id(v.table[t])) != x,
    ensures forall|id: int| 0 <= id < nq ==> #[trigger] rank_key(sc, id) != x,
{
    assert forall|id: int| 0 <= id < nq implies #[trigger] rank_key(sc, id) != x by {
        if rank_key(sc, id) == x {
            lemma_inv_rank(v, sc, nq, id);
            let t = choose|t: int| 0 <= t < v.nslots && #[trigger] v.table[t] != 0 && slot_id(v.table[t]) == id;
            lemma_inv_slot(v, sc, nq, t);
            if t > s {
                assert(v.table[s] != 0);
            }
        }
    }
}

/// An occupied slot whose tag differs, or whose rank's words differ (covered keys), holds another key.
pub proof fn lemma_probe_mismatch(v: KeysView, sc: &SubCols, nq: int, x: Seq<u8>, s: int)
    requires
        keys_inv(v, sc, nq),
        0 <= s < v.nslots, v.table[s] != 0,
        slot_tag(v.table[s]) != tag_of(x) || ({
            let id = slot_id(v.table[s]);
            fast_len(x.len() as int) && (v.kw[3 * id], v.kw[3 * id + 1], v.kw[3 * id + 2]) != key_words_spec(x)
        }),
    ensures rank_key(sc, slot_id(v.table[s])) != x,
{
    lemma_inv_slot(v, sc, nq, s);
    let id = slot_id(v.table[s]);
    lemma_inv_rank(v, sc, nq, id);
}

/// The rank of the qualifying sub whose adsh is `x` (`n` bytes; words `w`, hash `h`), or `usize::MAX` when no
/// qualifying sub has that adsh.
pub fn probe(keys: &Keys, sc: &SubCols, x: &'static [u8], n: usize, w: (u64, u64, u64), h: u64) -> (r: usize)
    requires
        sc.wf(),
        keys_inv(keys.view(), sc, sc.qlist(sc.n as int).len() as int),
        x@.len() == n, w == key_words_spec(x@), h == key_hash_spec(x@),
    ensures
        r == usize::MAX ==> forall|id: int| 0 <= id < sc.qlist(sc.n as int).len() ==> #[trigger] rank_key(sc, id) != x@,
        r != usize::MAX ==> r < sc.qlist(sc.n as int).len() && rank_key(sc, r as int) == x@,
    no_unwind
{
    let ghost ql = sc.qlist(sc.n as int);
    let ghost nq = ql.len() as int;
    let ghost v = keys.view();
    proof {
        lemma_inv_shape(v, sc, nq);
        lemma_bloom_idx(h);
        lemma_qlist(sc, sc.n as int);
    }
    let bit = h >> 44u64;
    if (keys.bloom[(bit >> 6u64) as usize] >> (bit & 63u64)) & 1 == 0 {
        proof {
            assert forall|id: int| 0 <= id < nq implies #[trigger] rank_key(sc, id) != x@ by {
                if rank_key(sc, id) == x@ {
                    lemma_inv_rank(v, sc, nq, id);
                }
            }
        }
        return usize::MAX;
    }
    let fast = 16 <= n && n <= 24;
    let tag: u64 = (((h >> 20u64) & 0xff_ffffu64) << 8u64) | (if fast { n as u64 } else { 0 });
    assert(tag == tag_of(x@));
    let bits = keys.bits;
    let mut s = (h >> (64 - bits)) as usize;
    proof {
        lemma_home_bound(h, bits);
    }
    let ghost hm = s as int;
    let nslots = keys.nslots;
    while s < nslots
        invariant
            sc.wf(), keys_inv(v, sc, nq), v == keys.view(), ql == sc.qlist(sc.n as int), nq == ql.len(), nslots == v.nslots,
            hm == home(h, bits), bits == v.bits, hm <= s, x@.len() == n, w == key_words_spec(x@), h == key_hash_spec(x@),
            tag == tag_of(x@), fast == fast_len(n as int),
            v.nslots == v.table.len(), s <= nslots,
            v.kw.len() >= 3 * nq, v.kw.len() < usize::MAX, v.qsub.len() >= nq,
            forall|t: int| hm <= t < s ==> #[trigger] v.table[t] != 0 && rank_key(sc, slot_id(v.table[t])) != x@,
        decreases nslots - s,
    {
        let slot = keys.table[s];
        if slot == 0 {
            proof {
                lemma_probe_absent(v, sc, nq, x@, s as int);
            }
            return usize::MAX;
        }
        proof {
            lemma_inv_slot(v, sc, nq, s as int);
            lemma_slot_low(slot);
        }
        if (slot >> 32u64) == tag {
            let id = ((slot & 0xffff_ffffu64) - 1) as usize;
            proof {
                lemma_inv_rank(v, sc, nq, id as int);
            }
            if fast {
                if keys.kw[3 * id] == w.0 && keys.kw[3 * id + 1] == w.1 && keys.kw[3 * id + 2] == w.2 {
                    proof {
                        // Equal tags give equal covered lengths; equal words of covered keys give equal keys.
                        lemma_tag_len(rank_key(sc, id as int), x@);
                        lemma_key_words_eq(rank_key(sc, id as int), x@);
                    }
                    return id;
                }
                proof {
                    lemma_probe_mismatch(v, sc, nq, x@, s as int);
                }
            } else {
                proof {
                    lemma_qlist(sc, sc.n as int);
                    assert(0 <= ql[id as int] < sc.n);
                }
                let j = keys.qsub[id] as usize;
                let sa = sc.adsh_off[j] as usize;
                let sb = sc.adsh_off[j + 1] as usize;
                if sb - sa == n && eq_n(sub_bytes(sc.adsh_bytes, sa, sb), x, n) {
                    return id;
                }
            }
        } else {
            proof {
                lemma_probe_mismatch(v, sc, nq, x@, s as int);
            }
        }
        s = s + 1;
    }
    proof {
        lemma_probe_absent(v, sc, nq, x@, s as int);
    }
    usize::MAX
}

/// Equal tags: the covered length is the same (a covered key's tag holds its length).
pub proof fn lemma_tag_len(a: Seq<u8>, b: Seq<u8>)
    requires tag_of(a) == tag_of(b), fast_len(b.len() as int),
    ensures a.len() == b.len(), fast_len(a.len() as int),
{
    let ha = key_hash_spec(a);
    let hb = key_hash_spec(b);
    let la: u64 = if fast_len(a.len() as int) { a.len() as u64 } else { 0u64 };
    let lb: u64 = b.len() as u64;
    assert(la < 256 && lb < 256);
    assert(((((ha >> 20u64) & 0xff_ffffu64) << 8u64) | la) & 0xffu64 == la) by (bit_vector) requires la < 256u64;
    assert(((((hb >> 20u64) & 0xff_ffffu64) << 8u64) | lb) & 0xffu64 == lb) by (bit_vector) requires lb < 256u64;
}

} // verus!
