//! Open-addressing index of the `sub` rows whose `fy` equals `$2` (the members), keyed by their `adsh` bytes.
//!
//! Layout: `slots[p]` is a `sub` row or `EMPTY`; a member is placed at the first empty slot at or after the bucket
//! of its key (linear probing, no wrap-around); members that find no slot before the end go to `overflow`.
//! Invariant (`table_wf`): every member is in a slot or in `overflow`, every slot and overflow entry is a member,
//! and every slot between a placed member's bucket and its slot is occupied. So a probe from a key's bucket that
//! reaches an empty slot (or the end) without a match proves the key absent from the slots, and the overflow scan
//! decides the rest. The hash reads two 8-byte words of the key (cheap for the 20-byte adsh); `hashes[p]` keeps
//! the hash of the member at slot `p`, so a probe compares the member's adsh bytes (two cache misses into `sub`)
//! only when the hashes agree. The index is planned (buffers allocated) on the calling thread and built in a
//! worker (`build_planned`, `no_unwind`).
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol, TextView};
use crate::agent::spec::*;
use crate::gendb_entry::work::{filled, put, TaskBuffer};

verus! {

pub const EMPTY: usize = usize::MAX;

/// Extra slots after the last bucket for linear probing.
pub const PROBE_ROOM: usize = 64;

/// Eight bytes of `b` from byte `s` as a little-endian word.
pub open spec fn word8(b: Seq<u8>, s: int) -> u64 {
    (b[s] as u64) | ((b[s + 1] as u64) << 8u64) | ((b[s + 2] as u64) << 16u64) | ((b[s + 3] as u64) << 24u64)
        | ((b[s + 4] as u64) << 32u64) | ((b[s + 5] as u64) << 40u64) | ((b[s + 6] as u64) << 48u64)
        | ((b[s + 7] as u64) << 56u64)
}

/// Hash of a key: the word at byte 2 mixed with the last word (for adsh `CCCCCCCCCC-YY-NNNNNN`: most filer
/// digits, the year and the sequence number); keys shorter than 10 bytes hash to 0.
pub open spec fn hash_spec(b: Seq<u8>) -> u64 {
    if b.len() >= 10 { word8(b, 2) ^ (word8(b, b.len() - 8) << 4u64) } else { 0 }
}

/// Bucket of a key in a table of `cap` buckets.
#[verifier::opaque]
pub open spec fn bucket_spec(b: Seq<u8>, cap: int) -> int {
    (hash_spec(b) as int) % cap
}

/// The word of `key` at byte `s`.
#[inline(always)]
fn word8_at(key: &[u8], s: usize) -> (w: u64)
    requires s + 8 <= key@.len(),
    ensures w == word8(key@, s as int),
    no_unwind
{
    (key[s] as u64) | ((key[s + 1] as u64) << 8u64) | ((key[s + 2] as u64) << 16u64) | ((key[s + 3] as u64) << 24u64)
        | ((key[s + 4] as u64) << 32u64) | ((key[s + 5] as u64) << 40u64) | ((key[s + 6] as u64) << 48u64)
        | ((key[s + 7] as u64) << 56u64)
}

/// The hash of `key` (`klen` bytes).
pub fn hash_key(key: &[u8], klen: usize) -> (h: u64)
    requires klen == key@.len(),
    ensures h == hash_spec(key@),
    no_unwind
{
    if klen >= 10 { word8_at(key, 2) ^ (word8_at(key, klen - 8) << 4u64) } else { 0 }
}

/// The bucket among `cap` buckets of a key whose hash is `h`.
pub fn bucket_of(h: u64, cap: usize, Ghost(key): Ghost<Seq<u8>>) -> (r: usize)
    requires cap > 0, h == hash_spec(key),
    ensures r == bucket_spec(key, cap as int), r < cap,
    no_unwind
{
    proof {
        reveal(bucket_spec);
    }
    (h % (cap as u64)) as usize
}

/// The index: `slots` (`cap + PROBE_ROOM` of them) with the hash of each slot's member, the overflow members, and
/// the `sub` adsh column (`m` rows).
pub struct SubTable {
    pub slots: Vec<usize>,
    pub hashes: Vec<u64>,
    pub cap: usize,
    pub overflow: Vec<usize>,
    pub adsh: TextCol,
    pub m: usize,
}

/// A member at slot `p` was placed at or after its bucket, with every slot in between occupied.
pub open spec fn slot_ok(slots: Seq<usize>, cap: int, c: Ctx, p: int) -> bool {
    let s = slots[p] as int;
    &&& member(c, s)
    &&& bucket_spec(sadsh_text(c, s), cap) <= p
    &&& forall|q: int| bucket_spec(sadsh_text(c, s), cap) <= q < p ==> #[trigger] slots[q] != EMPTY
}

/// Member `s` is in a slot or in the overflow list.
pub open spec fn placed(slots: Seq<usize>, overflow: Seq<usize>, s: int) -> bool {
    (exists|p: int| 0 <= p < slots.len() && (#[trigger] slots[p]) as int == s)
        || (exists|k: int| 0 <= k < overflow.len() && (#[trigger] overflow[k]) as int == s)
}

/// The slots and overflow list index the members `s < upto`.
pub open spec fn index_ok(slots: Seq<usize>, cap: int, overflow: Seq<usize>, c: Ctx, upto: int) -> bool {
    &&& forall|p: int| 0 <= p < slots.len() && #[trigger] slots[p] != EMPTY ==> slot_ok(slots, cap, c, p)
    &&& forall|k: int| 0 <= k < overflow.len() ==> member(c, (#[trigger] overflow[k]) as int)
    &&& forall|s: int| member(c, s) && s < upto ==> #[trigger] placed(slots, overflow, s)
}

/// `hashes[p]` is the hash of the adsh of the member at slot `p`.
pub open spec fn hashes_ok(slots: Seq<usize>, hashes: Seq<u64>, c: Ctx) -> bool {
    &&& hashes.len() == slots.len()
    &&& forall|p: int| 0 <= p < slots.len() && #[trigger] slots[p] != EMPTY
        ==> hashes[p] == hash_spec(sadsh_text(c, slots[p] as int))
}

pub open spec fn table_wf(t: SubTable, c: Ctx) -> bool {
    &&& t.m as int == c.m
    &&& t.adsh@ == sadsh_view(c.sp)
    &&& text_wf(t.adsh@, c.m)
    &&& t.cap > 0
    &&& t.slots@.len() == t.cap + PROBE_ROOM
    &&& index_ok(t.slots@, t.cap as int, t.overflow@, c, c.m)
    &&& hashes_ok(t.slots@, t.hashes@, c)
}

/// The adsh bytes of `sub` row `s`.
fn adsh_of(t: &SubTable, s: usize, Ghost(c): Ghost<Ctx>) -> (r: &'static [u8])
    requires
        t.adsh@ == sadsh_view(c.sp),
        text_wf(t.adsh@, c.m),
        s < c.m,
    ensures r@ == sadsh_text(c, s as int),
{
    proof {
        assert(0 <= t.adsh@.offsets[s as int] <= t.adsh@.offsets[s + 1] <= t.adsh@.bytes.len());
    }
    crate::gendb_entry::work::text_bytes(&t.adsh, s)
}

/// Byte equality of two slices.
pub fn same_bytes(x: &[u8], y: &[u8]) -> (r: bool)
    ensures r == (x@ == y@),
{
    let n = x.len();
    if n != y.len() {
        return false;
    }
    let mut k: usize = 0;
    while k < n
        invariant
            n == x@.len(),
            n == y@.len(),
            k <= n,
            forall|q: int| 0 <= q < k ==> x@[q] == y@[q],
        decreases n - k,
    {
        if x[k] != y[k] {
            proof {
                assert(x@[k as int] != y@[k as int]);
            }
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(x@ =~= y@);
    }
    true
}

/// The member whose adsh equals `key` (of hash `h`), if any.
pub fn lookup(t: &SubTable, key: &[u8], h: u64, Ghost(c): Ghost<Ctx>) -> (r: Option<usize>)
    requires table_wf(*t, c), h == hash_spec(key@),
    ensures
        r matches Some(s) ==> member(c, s as int) && sadsh_text(c, s as int) == key@,
        r is None ==> forall|s: int| member(c, s) ==> sadsh_text(c, s) != key@,
{
    let b = bucket_of(h, t.cap, Ghost(key@));
    let mut pos = b;
    let len = t.slots.len();
    let mut stop = false;
    while pos < len && !stop
        invariant
            table_wf(*t, c),
            len == t.slots@.len(),
            h == hash_spec(key@),
            b == bucket_spec(key@, t.cap as int),
            b <= pos <= len,
            forall|q: int| b <= q < pos ==> #[trigger] t.slots@[q] != EMPTY && sadsh_text(c, t.slots@[q] as int) != key@,
            stop ==> pos < len && t.slots@[pos as int] == EMPTY,
        decreases len - pos + (if stop { 0int } else { 1int }),
    {
        let s = t.slots[pos];
        if s == EMPTY {
            stop = true;
        } else {
            proof {
                assert(slot_ok(t.slots@, t.cap as int, c, pos as int));
                assert(t.hashes@[pos as int] == hash_spec(sadsh_text(c, s as int)));
            }
            // Equal keys have equal hashes: the bytes are compared only when the hashes agree.
            if t.hashes[pos] == h {
                let k2 = adsh_of(t, s, Ghost(c));
                if same_bytes(k2, key) {
                    return Some(s);
                }
            }
            pos = pos + 1;
        }
    }
    proof {
        // No slot holds a member with this key: a member at slot p has every slot from its bucket (= b) up to p
        // occupied, so the probe reached p (the first empty slot comes after p) and found a different key.
        assert forall|p: int| 0 <= p < t.slots@.len() && t.slots@[p] != EMPTY implies
            #[trigger] sadsh_text(c, t.slots@[p] as int) != key@ by {
            assert(slot_ok(t.slots@, t.cap as int, c, p));
            if sadsh_text(c, t.slots@[p] as int) == key@ {
                if p >= pos {
                    assert(stop);
                    assert(t.slots@[pos as int] != EMPTY);
                }
            }
        }
    }
    let n = t.overflow.len();
    let mut k: usize = 0;
    while k < n
        invariant
            table_wf(*t, c),
            n == t.overflow@.len(),
            k <= n,
            forall|q: int| 0 <= q < k ==> sadsh_text(c, #[trigger] t.overflow@[q] as int) != key@,
            forall|p: int| 0 <= p < t.slots@.len() && t.slots@[p] != EMPTY ==> #[trigger] sadsh_text(c, t.slots@[p] as int) != key@,
        decreases n - k,
    {
        let s = t.overflow[k];
        proof {
            assert(member(c, s as int));
        }
        let k2 = adsh_of(t, s, Ghost(c));
        if same_bytes(k2, key) {
            return Some(s);
        }
        k = k + 1;
    }
    proof {
        assert forall|s: int| member(c, s) implies sadsh_text(c, s) != key@ by {
            assert(placed(t.slots@, t.overflow@, s));
            if exists|p: int| 0 <= p < t.slots@.len() && (#[trigger] t.slots@[p]) as int == s {
                let p = choose|p: int| 0 <= p < t.slots@.len() && (#[trigger] t.slots@[p]) as int == s;
                assert(t.slots@[p] != EMPTY) by {
                    assert(s < c.m);
                }
            } else {
                let q = choose|q: int| 0 <= q < t.overflow@.len() && (#[trigger] t.overflow@[q]) as int == s;
            }
        }
    }
    None
}

/// Placing member `s` at the empty slot `pos` (at or after its bucket, every slot in between occupied) keeps the
/// index and places `s`.
proof fn lemma_place_slot(slots: Seq<usize>, cap: int, overflow: Seq<usize>, c: Ctx, s: int, pos: int)
    requires
        index_ok(slots, cap, overflow, c, s),
        member(c, s),
        0 <= pos < slots.len(),
        slots[pos] == EMPTY,
        bucket_spec(sadsh_text(c, s), cap) <= pos,
        forall|q: int| bucket_spec(sadsh_text(c, s), cap) <= q < pos ==> #[trigger] slots[q] != EMPTY,
        0 <= s < c.m,
        c.m <= usize::MAX,
    ensures
        index_ok(slots.update(pos, s as usize), cap, overflow, c, s + 1),
{
    let ns = slots.update(pos, s as usize);
    assert forall|p: int| 0 <= p < ns.len() && #[trigger] ns[p] != EMPTY implies slot_ok(ns, cap, c, p) by {
        if p != pos {
            assert(slots[p] != EMPTY);
            assert(slot_ok(slots, cap, c, p));
            assert forall|q: int| bucket_spec(sadsh_text(c, ns[p] as int), cap) <= q < p implies #[trigger] ns[q] != EMPTY by {
                assert(slots[q] != EMPTY);
            }
        } else {
            assert(ns[p] as int == s);
            assert forall|q: int| bucket_spec(sadsh_text(c, s), cap) <= q < p implies #[trigger] ns[q] != EMPTY by {
                assert(slots[q] != EMPTY);
            }
        }
    }
    assert forall|r: int| member(c, r) && r < s + 1 implies #[trigger] placed(ns, overflow, r) by {
        if r == s {
            assert(ns[pos] as int == r);
        } else {
            assert(placed(slots, overflow, r));
            if exists|p: int| 0 <= p < slots.len() && (#[trigger] slots[p]) as int == r {
                let p = choose|p: int| 0 <= p < slots.len() && (#[trigger] slots[p]) as int == r;
                assert(slots[p] != EMPTY) by { assert(r < c.m); }
                assert(p != pos);
                assert(ns[p] as int == r);
            } else {
                let k = choose|k: int| 0 <= k < overflow.len() && (#[trigger] overflow[k]) as int == r;
            }
        }
    }
}

/// Adding member `s` to the overflow list keeps the index and places `s`.
proof fn lemma_place_overflow(slots: Seq<usize>, cap: int, overflow: Seq<usize>, c: Ctx, s: int)
    requires
        index_ok(slots, cap, overflow, c, s),
        member(c, s),
        0 <= s < c.m,
        c.m <= usize::MAX,
    ensures
        index_ok(slots, cap, overflow.push(s as usize), c, s + 1),
{
    let no = overflow.push(s as usize);
    assert forall|k: int| 0 <= k < no.len() implies member(c, (#[trigger] no[k]) as int) by {
        if k < overflow.len() {
            assert(no[k] == overflow[k]);
        }
    }
    assert forall|r: int| member(c, r) && r < s + 1 implies #[trigger] placed(slots, no, r) by {
        if r == s {
            assert(no[overflow.len() as int] as int == r);
        } else {
            assert(placed(slots, overflow, r));
            if exists|p: int| 0 <= p < slots.len() && (#[trigger] slots[p]) as int == r {
            } else {
                let k = choose|k: int| 0 <= k < overflow.len() && (#[trigger] overflow[k]) as int == r;
                assert(no[k] as int == r);
            }
        }
    }
}

/// The index before it is built: the `sub` columns, the binding `fy`, and the buffers allocated on the calling
/// thread (`slots` all `EMPTY`, an empty overflow buffer with a slot per `sub` row), so a worker can build it.
pub struct TablePlan {
    pub adsh: TextCol,
    pub fy_vals: &'static [i32],
    pub fy_valid: &'static [u8],
    pub m: usize,
    pub fy: i64,
    pub cap: usize,
    pub slots: Vec<usize>,
    pub hashes: Vec<u64>,
    pub overflow: TaskBuffer<usize>,
}

pub open spec fn plan_ok(p: TablePlan, c: Ctx) -> bool {
    &&& c.m == p.m as int
    &&& c.fy == p.fy as int
    &&& p.adsh@ == sadsh_view(c.sp)
    &&& text_wf(p.adsh@, c.m)
    &&& p.fy_vals@ == fy_seq(c.sp)
    &&& p.fy_valid@ == fy_valid_seq(c.sp)
    &&& p.fy_vals@.len() == p.m
    &&& p.fy_valid@.len() == p.m
    &&& p.cap > 0
    &&& p.slots@ == Seq::new((p.cap + PROBE_ROOM) as nat, |_i: int| EMPTY)
    &&& p.hashes@.len() == p.cap + PROBE_ROOM
    &&& p.overflow.wf()
    &&& p.overflow.view() == Seq::<usize>::empty()
    &&& p.overflow.capacity() == p.m
}

/// The built slots, slot hashes and overflow buffer of a plan with `cap` buckets.
pub struct Built {
    pub slots: Vec<usize>,
    pub hashes: Vec<u64>,
    pub overflow: TaskBuffer<usize>,
}

pub open spec fn built_ok(b: Built, cap: usize, c: Ctx) -> bool {
    &&& b.slots@.len() == cap + PROBE_ROOM
    &&& b.overflow.wf()
    &&& index_ok(b.slots@, cap as int, b.overflow.view(), c, c.m)
    &&& hashes_ok(b.slots@, b.hashes@, c)
}

/// Prepare the index (calling thread): count the members to size the table (load factor at most one half) and
/// allocate its buffers.
pub fn plan_table(adsh: TextCol, fy_vals: &'static [i32], fy_valid: &'static [u8], m: usize, fy: i64,
    Ghost(c): Ghost<Ctx>) -> (p: TablePlan)
    requires
        c.m == m as int,
        c.fy == fy as int,
        adsh@ == sadsh_view(c.sp),
        text_wf(adsh@, c.m),
        fy_vals@ == fy_seq(c.sp),
        fy_valid@ == fy_valid_seq(c.sp),
        fy_vals@.len() == m,
        fy_valid@.len() == m,
    ensures
        plan_ok(p, c),
{
    let mut count: usize = 0;
    let mut s: usize = 0;
    while s < m
        invariant s <= m, count <= s, fy_vals@.len() == m, fy_valid@.len() == m,
        decreases m - s,
    {
        if fy_valid[s] != 0 && fy_vals[s] as i64 == fy {
            count = count + 1;
        }
        s = s + 1;
    }
    let cap: usize = if count < 1000000000 { 2 * count + 1 } else { 2000000001 };
    let slots = filled(cap + PROBE_ROOM, EMPTY);
    let hashes = filled(cap + PROBE_ROOM, 0u64);
    let overflow = TaskBuffer::new(m, 0usize);
    TablePlan { adsh, fy_vals, fy_valid, m, fy, cap, slots, hashes, overflow }
}

/// Build the index of a plan (`no_unwind`: runs in a worker).
pub fn build_planned(p: TablePlan, Ghost(c): Ghost<Ctx>) -> (b: Built)
    requires
        plan_ok(p, c),
    ensures
        built_ok(b, p.cap, c),
    no_unwind
{
    let TablePlan { adsh, fy_vals, fy_valid, m, fy, cap, slots, hashes, overflow } = p;
    let mut slots = slots;
    let mut hashes = hashes;
    let mut overflow = overflow;
    proof {
        assert forall|q: int| 0 <= q < slots@.len() implies #[trigger] slots@[q] == EMPTY by {}
        assert(index_ok(slots@, cap as int, overflow.view(), c, 0));
        assert(hashes_ok(slots@, hashes@, c));
    }
    let len = slots.len();
    let mut s: usize = 0;
    while s < m
        invariant
            s <= m,
            c.m == m as int,
            c.fy == fy as int,
            adsh@ == sadsh_view(c.sp),
            text_wf(adsh@, c.m),
            fy_vals@ == fy_seq(c.sp),
            fy_valid@ == fy_valid_seq(c.sp),
            fy_vals@.len() == m, fy_valid@.len() == m,
            cap > 0,
            len == slots@.len(),
            slots@.len() == cap + PROBE_ROOM,
            overflow.wf(),
            overflow.capacity() == m,
            overflow.view().len() <= s,
            index_ok(slots@, cap as int, overflow.view(), c, s as int),
            hashes_ok(slots@, hashes@, c),
        decreases m - s,
    {
        if fy_valid[s] != 0 && fy_vals[s] as i64 == fy {
            proof {
                assert(member(c, s as int));
                assert(0 <= adsh@.offsets[s as int] <= adsh@.offsets[s + 1] <= adsh@.bytes.len());
            }
            let key = crate::gendb_entry::work::text_bytes(&adsh, s);
            // The key length from the offsets (`len()` of a slice is not `no_unwind`).
            let ka = adsh.offsets[s];
            let kb = adsh.offsets[s + 1];
            proof {
                assert(0 <= ka <= kb <= adsh.bytes.len());
            }
            let klen = (kb as usize) - (ka as usize);
            proof {
                assert(key@.len() == klen);
            }
            let h = hash_key(key, klen);
            let bk = bucket_of(h, cap, Ghost(key@));
            let mut pos = bk;
            while pos < len && slots[pos] != EMPTY
                invariant
                    len == slots@.len(),
                    bk <= pos <= len,
                    forall|q: int| bk <= q < pos ==> #[trigger] slots@[q] != EMPTY,
                decreases len - pos,
            {
                pos = pos + 1;
            }
            if pos < len {
                proof {
                    lemma_place_slot(slots@, cap as int, overflow.view(), c, s as int, pos as int);
                }
                let ghost old_slots = slots@;
                let ghost old_hashes = hashes@;
                put(&mut slots, pos, s);
                put(&mut hashes, pos, h);
                proof {
                    assert forall|p: int| 0 <= p < slots@.len() && #[trigger] slots@[p] != EMPTY implies
                        hashes@[p] == hash_spec(sadsh_text(c, slots@[p] as int)) by {
                        if p != pos {
                            assert(old_slots[p] == slots@[p]);
                        }
                    }
                }
            } else {
                proof {
                    lemma_place_overflow(slots@, cap as int, overflow.view(), c, s as int);
                }
                overflow.push(s);
            }
        } else {
            proof {
                assert forall|r: int| member(c, r) && r < s + 1 implies #[trigger] placed(slots@, overflow.view(), r) by {
                    if r == s {
                        assert(member(c, s as int));
                    }
                }
            }
        }
        s = s + 1;
    }
    Built { slots, hashes, overflow }
}

/// The index from a built plan (calling thread, after the join).
pub fn finish_table(b: Built, cap: usize, adsh: TextCol, m: usize, Ghost(c): Ghost<Ctx>) -> (t: SubTable)
    requires
        built_ok(b, cap, c),
        cap > 0,
        c.m == m as int,
        adsh@ == sadsh_view(c.sp),
        text_wf(adsh@, c.m),
    ensures
        table_wf(t, c),
{
    let Built { slots, hashes, overflow } = b;
    let overflow = overflow.into_vec();
    SubTable { slots, hashes, cap, overflow, adsh, m }
}

} // verus!
