//! One worker task of the index build: a run of directory entries `e_lo .. e_lo + ne` (index positions
//! `p0 .. p1` of facts' l_partkey key index). Each position's stored row `s` and quantity key `c` are packed as
//! `c * 2^32 + s` (`pack_run`), each entry's packed values are sorted ascending, so by quantity key (`sort_run`), and
//! unpacked into the task's index rows and quantity keys (`unpack_run`).
//!
//! The facts are stated per entry with single-variable predicates (`entry_keys`, `seg_done`, `entry_out`), each
//! opaque and revealed only in the lemma that needs its body.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::stores::li_pkqty::interface::*;
use super::src::*;
use super::dirscan::lemma_div_lt;
use super::sort64::*;

verus! {

/// `2^32`: packed values are `quantity key * 2^32 + stored row`.
pub open spec fn p32() -> int {
    0x1_0000_0000
}

/// Packed value `x` holds a stored row of key `k` and its quantity key (relative to `qbase`).
#[verifier::opaque]
pub open spec fn good(fp: Seq<PartView>, n: int, qbase: int, k: int, x: u64) -> bool {
    let s = x as int % p32();
    let c = x as int / p32();
    &&& s < n
    &&& c <= 0xffff
    &&& key_at(fp, s) == k
    &&& qbase + c == qty_at(fp, s)
}

/// The entry starts never decrease.
#[verifier::opaque]
pub open spec fn ents_mono(ents: Seq<u32>, ne: int) -> bool {
    forall|j: int| 0 <= j < ne ==> #[trigger] ents[j] <= ents[j + 1]
}

/// Nondecreasing entry starts, between any two entries.
pub proof fn lemma_ents_le(ents: Seq<u32>, ne: int, a: int, b: int)
    requires ents_mono(ents, ne), 0 <= a <= b <= ne,
    ensures ents[a] <= ents[b],
    decreases b - a,
{
    if a < b {
        lemma_ents_le(ents, ne, a, b - 1);
        reveal(ents_mono);
    }
}

/// Every position of entry `j` (positions `ents[j] .. ents[j + 1]` of facts' key index) holds a row of key `k0 + j`.
#[verifier::opaque]
pub open spec fn entry_keys(fp: Seq<PartView>, k0: int, ents: Seq<u32>, j: int) -> bool {
    forall|p: int| ents[j] <= p < ents[j + 1] ==> #[trigger] key_at(fp, kirow(fp, p)) == k0 + j
}

/// Every l_quantity lies in `qbase .. qbase + 0xffff`.
#[verifier::opaque]
pub open spec fn qkeys_in(fp: Seq<PartView>, n: int, qbase: int) -> bool {
    &&& -1_000_000_000_000_000 <= qbase <= 1_000_000_000_000_000
    &&& forall|s: int| 0 <= s < n ==> qbase <= #[trigger] qty_at(fp, s) <= qbase + 0xffff
}

/// The slices a task reads and the source facts about them.
#[verifier::opaque]
pub open spec fn task_src(fp: Seq<PartView>, n: int, bs: int, ic: Seq<u32>, ib: Seq<u64>, qc: Seq<u16>, qb: Seq<i64>) -> bool {
    &&& base_ok(fp, n)
    &&& index_ok(fp, n)
    &&& bs == bsize(fp)
    &&& ic == u32s(fp[LI_KEYIDX_CODES as int])
    &&& ib == u64s(fp[LI_KEYIDX_BASE as int])
    &&& qc == u16s(fp[LI_QUANTITY_CODES as int])
    &&& qb == i64s(fp[LI_QUANTITY_BASE as int])
    &&& n <= u32::MAX
}

/// What the packing step reads: block bases cover the rows, index positions map to stored rows.
pub proof fn lemma_task_src(fp: Seq<PartView>, n: int, bs: int, ic: Seq<u32>, ib: Seq<u64>, qc: Seq<u16>, qb: Seq<i64>)
    requires task_src(fp, n, bs, ic, ib, qc, qb),
    ensures
        bs >= 1, bs == bsize(fp),
        ic.len() == n, ib.len() * bs >= n, qc.len() == n, qb.len() * bs >= n,
        n <= 0xffff_ffff,
        forall|p: int| 0 <= p < n ==> 0 <= #[trigger] kirow(fp, p) < n,
        forall|p: int| #[trigger] kirow(fp, p) == ib[p / bs] + ic[p],
        forall|s: int| #[trigger] qty_at(fp, s) == qb[s / bs] + qc[s],
{
    reveal(task_src);
}

/// Position `p` packed into `value`: its stored row and quantity key.
#[verifier::opaque]
pub open spec fn packed_ok(fp: Seq<PartView>, qbase: int, p: int, value: u64) -> bool {
    value as int == (qty_at(fp, kirow(fp, p)) - qbase) * p32() + kirow(fp, p)
}

/// Entry `j` of the run is done: its packed values (local slots `ents[j] - p0 .. ents[j + 1] - p0`) hold rows of
/// key `k0 + j`, sorted.
#[verifier::opaque]
pub open spec fn seg_done(fp: Seq<PartView>, n: int, qbase: int, k0: int, ents: Seq<u32>, p0: int, v: Seq<u64>, j: int) -> bool {
    &&& forall|x: int| ents[j] - p0 <= x < ents[j + 1] - p0 ==> #[trigger] good(fp, n, qbase, k0 + j, v[x])
    &&& sorted64(seg64(v, ents[j] - p0, ents[j + 1] - p0))
}

/// Entry `j` of the output: its positions hold rows of key `k0 + j` with their quantity keys, in quantity order (positions
/// `p` of the output are at `p - p0`).
#[verifier::opaque]
pub open spec fn entry_out(fp: Seq<PartView>, n: int, qbase: int, k0: int, ents: Seq<u32>, p0: int, rows: Seq<u32>,
    qkeys: Seq<u16>, j: int) -> bool
{
    forall|x: int| ents[j] - p0 <= x < ents[j + 1] - p0 ==> {
        &&& (#[trigger] rows[x]) < n
        &&& key_at(fp, rows[x] as int) == k0 + j
        &&& qbase + qkeys[x] == qty_at(fp, rows[x] as int)
        &&& (x + 1 < ents[j + 1] - p0 ==> qkeys[x] <= qkeys[x + 1])
    }
}

/// One worker's run of entries `e_lo .. e_lo + ne` (positions `p0 .. p1`).
pub struct IdxTask {
    pub ic: &'static [u32],
    pub ib: &'static [u64],
    pub qc: &'static [u16],
    pub qb: &'static [i64],
    pub bs: usize,
    pub n: usize,
    pub qbase: i64,
    /// `offs[e_lo ..= e_lo + ne]`.
    pub ents: Vec<u32>,
    pub ne: usize,
    pub p0: usize,
    pub p1: usize,
    pub packed: Vec<u64>,
    pub tmp: Vec<u64>,
    pub rows: Vec<u32>,
    pub qkeys: Vec<u16>,
    pub fp: Ghost<Seq<PartView>>,
    pub kmin: Ghost<int>,
    pub e_lo: Ghost<int>,
}

/// What a task needs: the source slices, its entries' positions and keys, and the quantity range.
pub open spec fn task_pre(t: IdxTask) -> bool {
    let fp = t.fp@;
    let n = t.n as int;
    let ents = t.ents@;
    let len = t.p1 - t.p0;
    &&& task_src(fp, n, t.bs as int, t.ic@, t.ib@, t.qc@, t.qb@)
    &&& ents.len() == t.ne + 1
    &&& ents[0] == t.p0 && ents[t.ne as int] == t.p1
    &&& t.p0 <= t.p1 <= n
    &&& ents_mono(ents, t.ne as int)
    &&& forall|j: int| 0 <= j < t.ne ==> #[trigger] entry_keys(fp, t.kmin@ + t.e_lo@, ents, j)
    &&& qkeys_in(fp, n, t.qbase as int)
    &&& t.packed@.len() == len && t.tmp@.len() == len && t.rows@.len() == len && t.qkeys@.len() == len
}

/// A task's output: `entry_out` for every entry of its run.
pub open spec fn task_post(t: IdxTask, out: (Vec<u32>, Vec<u16>)) -> bool {
    &&& out.0@.len() == t.p1 - t.p0 && out.1@.len() == t.p1 - t.p0
    &&& forall|j: int| 0 <= j < t.ne ==>
            #[trigger] entry_out(t.fp@, t.n as int, t.qbase as int, t.kmin@ + t.e_lo@, t.ents@, t.p0 as int, out.0@, out.1@, j)
}

/// Unpacking: a packed value's row and quantity key.
proof fn lemma_unpack(x: u64)
    ensures
        x as int % p32() == (x % 0x1_0000_0000) as int,
        x as int / p32() == (x / 0x1_0000_0000) as int,
        (x / 0x1_0000_0000) as int <= 0xffff_ffff,
{
}

/// Packing one position.
proof fn lemma_pack_one(fp: Seq<PartView>, qbase: int, p: int, s: int, d: int, c: int, value: u64)
    requires s == kirow(fp, p), d == qty_at(fp, s), c == d - qbase, value as int == c * p32() + s,
    ensures packed_ok(fp, qbase, p, value),
{
    reveal(packed_ok);
}

/// Step 1 of a task: pack every position's stored row and quantity key.
fn pack_run(ic: &[u32], ib: &[u64], qc: &[u16], qb: &[i64], bs: usize, n: usize, qbase: i64, p0: usize, len: usize,
    packed: &mut Vec<u64>, Ghost(fp): Ghost<Seq<PartView>>)
    requires
        task_src(fp, n as int, bs as int, ic@, ib@, qc@, qb@),
        qkeys_in(fp, n as int, qbase as int),
        p0 + len <= n,
        old(packed)@.len() == len,
    ensures
        final(packed)@.len() == len,
        forall|x: int| 0 <= x < len ==> #[trigger] packed_ok(fp, qbase as int, p0 + x, final(packed)@[x]),
    no_unwind
{
    proof {
        lemma_task_src(fp, n as int, bs as int, ic@, ib@, qc@, qb@);
        reveal(qkeys_in);
    }
    let mut i: usize = 0;
    while i < len
        invariant
            bs >= 1, bs == bsize(fp),
            ic@.len() == n, ib@.len() * bs >= n, qc@.len() == n, qb@.len() * bs >= n,
            n <= 0xffff_ffff,
            forall|p: int| 0 <= p < n ==> 0 <= #[trigger] kirow(fp, p) < n,
            forall|p: int| #[trigger] kirow(fp, p) == ib@[p / (bs as int)] + ic@[p],
            forall|s: int| #[trigger] qty_at(fp, s) == qb@[s / (bs as int)] + qc@[s],
            forall|s: int| 0 <= s < n ==> qbase <= #[trigger] qty_at(fp, s) <= qbase + 0xffff,
            -1_000_000_000_000_000 <= qbase <= 1_000_000_000_000_000,
            p0 + len <= n,
            i <= len,
            packed@.len() == len,
            forall|x: int| 0 <= x < i ==> #[trigger] packed_ok(fp, qbase as int, p0 + x, packed@[x]),
        decreases len - i,
    {
        let p = p0 + i;
        proof {
            lemma_div_lt(p as int, bs as int, ib@.len() as int);
            assert(0 <= kirow(fp, p as int) < n);
        }
        let s = (ib[p / bs] + ic[p] as u64) as usize;
        proof {
            assert(s as int == kirow(fp, p as int));
            lemma_div_lt(s as int, bs as int, qb@.len() as int);
            assert(qbase <= qty_at(fp, s as int) <= qbase + 0xffff);
        }
        let d = qb[s / bs] + qc[s] as i64;
        let c = (d - qbase) as u64;
        proof {
            assert(d as int == qty_at(fp, s as int));
            assert(c <= 0xffff);
        }
        let value = c * 0x1_0000_0000 + s as u64;
        proof {
            lemma_pack_one(fp, qbase as int, p as int, s as int, d as int, c as int, value);
        }
        let ghost old_packed = packed@;
        crate::gendb_entry::work::put(packed, i, value);
        proof {
            assert forall|x: int| 0 <= x < i + 1 implies #[trigger] packed_ok(fp, qbase as int, p0 + x, packed@[x]) by {
                if x < i {
                    assert(packed@[x] == old_packed[x]);
                } else {
                    assert(packed@[x] == value);
                }
            }
        }
        i = i + 1;
    }
}

/// A packed position of entry `j` holds a row of the entry's key and its quantity key.
proof fn lemma_good_init(fp: Seq<PartView>, n: int, qbase: int, k0: int, ents: Seq<u32>, j: int, p: int, value: u64)
    requires
        n <= 0xffff_ffff,
        packed_ok(fp, qbase, p, value),
        entry_keys(fp, k0, ents, j),
        ents[j] <= p < ents[j + 1],
        0 <= kirow(fp, p) < n,
        qkeys_in(fp, n, qbase),
    ensures good(fp, n, qbase, k0 + j, value),
{
    reveal(packed_ok);
    reveal(good);
    reveal(entry_keys);
    reveal(qkeys_in);
    let s = kirow(fp, p);
    assert(key_at(fp, kirow(fp, p)) == k0 + j);
    assert(qbase <= qty_at(fp, s) <= qbase + 0xffff);
    let c = qty_at(fp, s) - qbase;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(value as int, p32(), c, s);
}

/// Entry `j` sorted: `seg_done`.
proof fn lemma_seg_done(fp: Seq<PartView>, n: int, qbase: int, k0: int, ents: Seq<u32>, p0: int, v: Seq<u64>, j: int,
    pr: spec_fn(u64) -> bool)
    requires
        p0 <= ents[j] <= ents[j + 1],
        pr == (|x: u64| good(fp, n, qbase, k0 + j, x)),
        all_in(v, ents[j] - p0, ents[j + 1] - p0, pr),
        sorted64(seg64(v, ents[j] - p0, ents[j + 1] - p0)),
    ensures seg_done(fp, n, qbase, k0, ents, p0, v, j),
{
    reveal(seg_done);
    assert forall|x: int| ents[j] - p0 <= x < ents[j + 1] - p0 implies #[trigger] good(fp, n, qbase, k0 + j, v[x]) by {
        assert(pr(v[x]));
    }
}

/// A done entry stays done while only slots after it change.
proof fn lemma_seg_frame(fp: Seq<PartView>, n: int, qbase: int, k0: int, ents: Seq<u32>, p0: int, v0: Seq<u64>,
    v1: Seq<u64>, j: int, lo: int)
    requires
        seg_done(fp, n, qbase, k0, ents, p0, v0, j),
        p0 <= ents[j] <= ents[j + 1], ents[j + 1] - p0 <= lo,
        v0.len() == v1.len(), ents[j + 1] - p0 <= v0.len(),
        forall|x: int| 0 <= x < lo ==> v1[x] == v0[x],
    ensures seg_done(fp, n, qbase, k0, ents, p0, v1, j),
{
    reveal(seg_done);
    assert forall|x: int| ents[j] - p0 <= x < ents[j + 1] - p0 implies #[trigger] good(fp, n, qbase, k0 + j, v1[x]) by {
        assert(v1[x] == v0[x]);
        assert(good(fp, n, qbase, k0 + j, v0[x]));
    }
    assert(seg64(v1, ents[j] - p0, ents[j + 1] - p0) =~= seg64(v0, ents[j] - p0, ents[j + 1] - p0));
}

/// The facts the sort step needs about its run.
pub open spec fn run_facts(fp: Seq<PartView>, n: int, qbase: int, k0: int, ents: Seq<u32>, ne: int, p0: int, len: int) -> bool {
    &&& ents.len() == ne + 1
    &&& ents[0] == p0 && ents[ne] == p0 + len
    &&& p0 + len <= n
    &&& n <= 0xffff_ffff
    &&& ents_mono(ents, ne)
    &&& forall|j: int| 0 <= j < ne ==> #[trigger] entry_keys(fp, k0, ents, j)
    &&& forall|p: int| 0 <= p < n ==> 0 <= #[trigger] kirow(fp, p) < n
    &&& qkeys_in(fp, n, qbase)
}

/// Step 2 of a task: sort each entry's packed values (so by quantity key).
fn sort_run(packed: &mut Vec<u64>, tmp: &mut Vec<u64>, ents: &Vec<u32>, ne: usize, p0: usize, len: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(n): Ghost<int>, Ghost(qbase): Ghost<int>, Ghost(k0): Ghost<int>)
    requires
        run_facts(fp, n, qbase, k0, ents@, ne as int, p0 as int, len as int),
        old(packed)@.len() == len, old(tmp)@.len() == len,
        forall|x: int| 0 <= x < len ==> #[trigger] packed_ok(fp, qbase, p0 + x, old(packed)@[x]),
    ensures
        final(packed)@.len() == len,
        forall|j: int| 0 <= j < ne ==> #[trigger] seg_done(fp, n, qbase, k0, ents@, p0 as int, final(packed)@, j),
    no_unwind
{
    let ghost ev = ents@;
    let mut j: usize = 0;
    while j < ne
        invariant
            run_facts(fp, n, qbase, k0, ev, ne as int, p0 as int, len as int), ev == ents@,
            j <= ne,
            packed@.len() == len, tmp@.len() == len,
            forall|x: int| ev[j as int] - p0 <= x < len ==> #[trigger] packed_ok(fp, qbase, p0 + x, packed@[x]),
            forall|jj: int| 0 <= jj < j ==> #[trigger] seg_done(fp, n, qbase, k0, ev, p0 as int, packed@, jj),
        decreases ne - j,
    {
        proof {
            lemma_ents_le(ev, ne as int, 0, j as int);
            lemma_ents_le(ev, ne as int, j as int, j as int + 1);
            lemma_ents_le(ev, ne as int, j as int + 1, ne as int);
        }
        let lo = (ents[j] as usize) - p0;
        let hi = (ents[j + 1] as usize) - p0;
        let ghost k = k0 + j;
        let ghost pr = |x: u64| good(fp, n, qbase, k, x);
        proof {
            assert(entry_keys(fp, k0, ev, j as int));
            assert forall|x: int| lo <= x < hi implies #[trigger] pr(packed@[x]) by {
                let p = p0 + x;
                assert(packed_ok(fp, qbase, p0 + x, packed@[x]));
                lemma_good_init(fp, n, qbase, k0, ev, j as int, p, packed@[x]);
            }
        }
        let ghost before = packed@;
        msort64(packed, tmp, lo, hi, Ghost(pr));
        proof {
            lemma_seg_done(fp, n, qbase, k0, ev, p0 as int, packed@, j as int, pr);
            assert forall|x: int| ev[j as int + 1] - p0 <= x < len implies #[trigger] packed_ok(fp, qbase, p0 + x, packed@[x]) by {
                assert(packed@[x] == before[x]);
                assert(packed_ok(fp, qbase, p0 + x, before[x]));
            }
            assert forall|jj: int| 0 <= jj < j + 1 implies #[trigger] seg_done(fp, n, qbase, k0, ev, p0 as int, packed@, jj) by {
                if jj < j {
                    lemma_ents_le(ev, ne as int, 0, jj);
                    lemma_ents_le(ev, ne as int, jj, jj + 1);
                    lemma_ents_le(ev, ne as int, jj + 1, j as int);
                    assert forall|x: int| 0 <= x < lo implies packed@[x] == before[x] by {}
                    lemma_seg_frame(fp, n, qbase, k0, ev, p0 as int, before, packed@, jj, lo as int);
                }
            }
        }
        j = j + 1;
    }
}

/// Step 3 of a task: unpack every packed value into its stored row and quantity key.
fn unpack_run(packed: &Vec<u64>, rows: &mut Vec<u32>, qkeys: &mut Vec<u16>, len: usize)
    requires packed@.len() == len, old(rows)@.len() == len, old(qkeys)@.len() == len,
    ensures
        final(rows)@.len() == len, final(qkeys)@.len() == len,
        forall|x: int| 0 <= x < len ==> (#[trigger] final(rows)@[x]) as int == packed@[x] as int % p32(),
        forall|x: int| 0 <= x < len && packed@[x] as int / p32() <= 0xffff ==> (#[trigger] final(qkeys)@[x]) as int == packed@[x] as int / p32(),
    no_unwind
{
    let mut i: usize = 0;
    while i < len
        invariant
            packed@.len() == len, rows@.len() == len, qkeys@.len() == len,
            i <= len,
            forall|x: int| 0 <= x < i ==> (#[trigger] rows@[x]) as int == packed@[x] as int % p32(),
            forall|x: int| 0 <= x < i && packed@[x] as int / p32() <= 0xffff ==> (#[trigger] qkeys@[x]) as int == packed@[x] as int / p32(),
        decreases len - i,
    {
        let x = packed[i];
        proof { lemma_unpack(x); }
        let c = x / 0x1_0000_0000;
        let ghost (r0, d0) = (rows@, qkeys@);
        crate::gendb_entry::work::put(rows, i, (x % 0x1_0000_0000) as u32);
        crate::gendb_entry::work::put(qkeys, i, (if c <= 0xffff { c } else { 0 }) as u16);
        proof {
            assert forall|y: int| 0 <= y < i + 1 implies (#[trigger] rows@[y]) as int == packed@[y] as int % p32() by {
                if y < i { assert(rows@[y] == r0[y]); }
            }
            assert forall|y: int| 0 <= y < i + 1 && packed@[y] as int / p32() <= 0xffff implies (#[trigger] qkeys@[y]) as int == packed@[y] as int / p32() by {
                if y < i { assert(qkeys@[y] == d0[y]); }
            }
        }
        i = i + 1;
    }
}

/// Packed order: a smaller packed value has a quantity key at most the other's.
proof fn lemma_packed_order(x: u64, y: u64)
    requires x <= y,
    ensures x as int / p32() <= y as int / p32(),
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, y as int, p32());
}

/// Entry `j` of the output from its sorted packed values.
proof fn lemma_entry_unpacked(fp: Seq<PartView>, n: int, qbase: int, k0: int, ents: Seq<u32>, p0: int, len: int,
    packed: Seq<u64>, rows: Seq<u32>, qkeys: Seq<u16>, j: int)
    requires
        seg_done(fp, n, qbase, k0, ents, p0, packed, j),
        p0 <= ents[j] <= ents[j + 1] <= p0 + len,
        packed.len() == len, rows.len() == len, qkeys.len() == len,
        forall|x: int| 0 <= x < len ==> (#[trigger] rows[x]) as int == packed[x] as int % p32(),
        forall|x: int| 0 <= x < len && packed[x] as int / p32() <= 0xffff ==> (#[trigger] qkeys[x]) as int == packed[x] as int / p32(),
    ensures entry_out(fp, n, qbase, k0, ents, p0, rows, qkeys, j),
{
    reveal(seg_done);
    reveal(good);
    reveal(entry_out);
    let lo = ents[j] - p0;
    let hi = ents[j + 1] - p0;
    assert forall|x: int| lo <= x < hi implies {
        &&& (#[trigger] rows[x]) < n
        &&& key_at(fp, rows[x] as int) == k0 + j
        &&& qbase + qkeys[x] == qty_at(fp, rows[x] as int)
        &&& (x + 1 < hi ==> qkeys[x] <= qkeys[x + 1])
    } by {
        assert(good(fp, n, qbase, k0 + j, packed[x]));
        if x + 1 < hi {
            assert(good(fp, n, qbase, k0 + j, packed[x + 1]));
            assert(seg64(packed, lo, hi)[x - lo] == packed[x]);
            assert(seg64(packed, lo, hi)[x + 1 - lo] == packed[x + 1]);
            lemma_packed_order(packed[x], packed[x + 1]);
        }
    }
}

/// A task's precondition gives the facts of its steps.
proof fn lemma_pre_facts(t: IdxTask)
    requires task_pre(t),
    ensures
        run_facts(t.fp@, t.n as int, t.qbase as int, t.kmin@ + t.e_lo@, t.ents@, t.ne as int, t.p0 as int, (t.p1 - t.p0) as int),
        t.n <= 0xffff_ffff,
{
    reveal(task_src);
    assert(index_ok(t.fp@, t.n as int));
}

impl WorkerTask for IdxTask {
    type Output = (Vec<u32>, Vec<u16>);

    open spec fn pre(&self) -> bool {
        task_pre(*self)
    }

    open spec fn post(&self, out: (Vec<u32>, Vec<u16>)) -> bool {
        task_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.p0 as u64, self.p1 as u64)
    }

    fn run(self) -> (out: (Vec<u32>, Vec<u16>)) {
        let ghost fp = self.fp@;
        let ghost k0 = self.kmin@ + self.e_lo@;
        let ghost ev = self.ents@;
        let p0 = self.p0;
        let len = self.p1 - self.p0;
        let ne = self.ne;
        let mut packed = self.packed;
        let mut tmp = self.tmp;
        let mut rows = self.rows;
        let mut qkeys = self.qkeys;
        proof {
            lemma_pre_facts(self);
        }
        pack_run(self.ic, self.ib, self.qc, self.qb, self.bs, self.n, self.qbase, p0, len, &mut packed, Ghost(fp));
        sort_run(&mut packed, &mut tmp, &self.ents, ne, p0, len, Ghost(fp), Ghost(self.n as int), Ghost(self.qbase as int), Ghost(k0));
        unpack_run(&packed, &mut rows, &mut qkeys, len);
        proof {
            assert forall|j: int| 0 <= j < ne implies
                #[trigger] entry_out(fp, self.n as int, self.qbase as int, k0, ev, p0 as int, rows@, qkeys@, j) by {
                lemma_ents_le(ev, ne as int, 0, j);
                lemma_ents_le(ev, ne as int, j, j + 1);
                lemma_ents_le(ev, ne as int, j + 1, ne as int);
                lemma_entry_unpacked(fp, self.n as int, self.qbase as int, k0, ev, p0 as int, len as int, packed@, rows@, qkeys@, j);
            }
        }
        (rows, qkeys)
    }
}

} // verus!
