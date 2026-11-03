//! One worker task of the index build: a run of directory entries `e_lo .. e_lo + ne` (index positions
//! `p0 .. p1` of facts' l_partkey key index). Each position's stored row `s` and date code `c` are packed as
//! `c * 2^32 + s` (`pack_run`), each entry's packed values are sorted ascending, so by date code (`sort_run`), and
//! unpacked into the task's index rows and date codes (`unpack_run`).
//!
//! The facts are stated per entry with single-variable predicates (`entry_keys`, `seg_done`, `entry_out`), each
//! opaque and revealed only in the lemma that needs its body.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::stores::li_pkdate::interface::*;
use super::src::*;
use super::dirscan::lemma_div_lt;
use super::sort64::*;

verus! {

/// `2^32`: packed values are `date code * 2^32 + stored row`.
pub open spec fn p32() -> int {
    0x1_0000_0000
}

/// Packed value `x` holds a stored row of key `k` and its date code (relative to `dbase`).
#[verifier::opaque]
pub open spec fn good(fp: Seq<PartView>, n: int, dbase: int, k: int, x: u64) -> bool {
    let s = x as int % p32();
    let c = x as int / p32();
    &&& s < n
    &&& c <= 0xffff
    &&& key_at(fp, s) == k
    &&& dbase + c == date_at(fp, s)
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

/// Every l_shipdate lies in `dbase .. dbase + 0xffff`.
#[verifier::opaque]
pub open spec fn dates_in(fp: Seq<PartView>, n: int, dbase: int) -> bool {
    &&& -0x8000_0000 <= dbase <= 0x8000_0000
    &&& forall|s: int| 0 <= s < n ==> dbase <= #[trigger] date_at(fp, s) <= dbase + 0xffff
}

/// The slices a task reads and the source facts about them.
#[verifier::opaque]
pub open spec fn task_src(fp: Seq<PartView>, n: int, bs: int, ic: Seq<u32>, ib: Seq<u64>, dc: Seq<u16>, db: Seq<i64>) -> bool {
    &&& base_ok(fp, n)
    &&& index_ok(fp, n)
    &&& bs == bsize(fp)
    &&& ic == u32s(fp[LI_KEYIDX_CODES as int])
    &&& ib == u64s(fp[LI_KEYIDX_BASE as int])
    &&& dc == u16s(fp[LI_SHIPDATE_CODES as int])
    &&& db == i64s(fp[LI_SHIPDATE_BASE as int])
    &&& n <= u32::MAX
}

/// What the packing step reads: block bases cover the rows, index positions map to stored rows.
pub proof fn lemma_task_src(fp: Seq<PartView>, n: int, bs: int, ic: Seq<u32>, ib: Seq<u64>, dc: Seq<u16>, db: Seq<i64>)
    requires task_src(fp, n, bs, ic, ib, dc, db),
    ensures
        bs >= 1, bs == bsize(fp),
        ic.len() == n, ib.len() * bs >= n, dc.len() == n, db.len() * bs >= n,
        n <= 0xffff_ffff,
        forall|p: int| 0 <= p < n ==> 0 <= #[trigger] kirow(fp, p) < n,
        forall|p: int| #[trigger] kirow(fp, p) == ib[p / bs] + ic[p],
        forall|s: int| #[trigger] date_at(fp, s) == db[s / bs] + dc[s],
{
    reveal(task_src);
}

/// Position `p` packed into `value`: its stored row and date code.
#[verifier::opaque]
pub open spec fn packed_ok(fp: Seq<PartView>, dbase: int, p: int, value: u64) -> bool {
    value as int == (date_at(fp, kirow(fp, p)) - dbase) * p32() + kirow(fp, p)
}

/// Entry `j` of the run is done: its packed values (local slots `ents[j] - p0 .. ents[j + 1] - p0`) hold rows of
/// key `k0 + j`, sorted.
#[verifier::opaque]
pub open spec fn seg_done(fp: Seq<PartView>, n: int, dbase: int, k0: int, ents: Seq<u32>, p0: int, v: Seq<u64>, j: int) -> bool {
    &&& forall|x: int| ents[j] - p0 <= x < ents[j + 1] - p0 ==> #[trigger] good(fp, n, dbase, k0 + j, v[x])
    &&& sorted64(seg64(v, ents[j] - p0, ents[j + 1] - p0))
}

/// Entry `j` of the output: its positions hold rows of key `k0 + j` with their date codes, in date order (positions
/// `p` of the output are at `p - p0`).
#[verifier::opaque]
pub open spec fn entry_out(fp: Seq<PartView>, n: int, dbase: int, k0: int, ents: Seq<u32>, p0: int, rows: Seq<u32>,
    dates: Seq<u16>, j: int) -> bool
{
    forall|x: int| ents[j] - p0 <= x < ents[j + 1] - p0 ==> {
        &&& (#[trigger] rows[x]) < n
        &&& key_at(fp, rows[x] as int) == k0 + j
        &&& dbase + dates[x] == date_at(fp, rows[x] as int)
        &&& (x + 1 < ents[j + 1] - p0 ==> dates[x] <= dates[x + 1])
    }
}

/// One worker's run of entries `e_lo .. e_lo + ne` (positions `p0 .. p1`).
pub struct IdxTask {
    pub ic: &'static [u32],
    pub ib: &'static [u64],
    pub dc: &'static [u16],
    pub db: &'static [i64],
    pub bs: usize,
    pub n: usize,
    pub dbase: i64,
    /// `offs[e_lo ..= e_lo + ne]`.
    pub ents: Vec<u32>,
    pub ne: usize,
    pub p0: usize,
    pub p1: usize,
    pub packed: Vec<u64>,
    pub tmp: Vec<u64>,
    pub rows: Vec<u32>,
    pub dates: Vec<u16>,
    pub fp: Ghost<Seq<PartView>>,
    pub kmin: Ghost<int>,
    pub e_lo: Ghost<int>,
}

/// What a task needs: the source slices, its entries' positions and keys, and the date range.
pub open spec fn task_pre(t: IdxTask) -> bool {
    let fp = t.fp@;
    let n = t.n as int;
    let ents = t.ents@;
    let len = t.p1 - t.p0;
    &&& task_src(fp, n, t.bs as int, t.ic@, t.ib@, t.dc@, t.db@)
    &&& ents.len() == t.ne + 1
    &&& ents[0] == t.p0 && ents[t.ne as int] == t.p1
    &&& t.p0 <= t.p1 <= n
    &&& ents_mono(ents, t.ne as int)
    &&& forall|j: int| 0 <= j < t.ne ==> #[trigger] entry_keys(fp, t.kmin@ + t.e_lo@, ents, j)
    &&& dates_in(fp, n, t.dbase as int)
    &&& t.packed@.len() == len && t.tmp@.len() == len && t.rows@.len() == len && t.dates@.len() == len
}

/// A task's output: `entry_out` for every entry of its run.
pub open spec fn task_post(t: IdxTask, out: (Vec<u32>, Vec<u16>)) -> bool {
    &&& out.0@.len() == t.p1 - t.p0 && out.1@.len() == t.p1 - t.p0
    &&& forall|j: int| 0 <= j < t.ne ==>
            #[trigger] entry_out(t.fp@, t.n as int, t.dbase as int, t.kmin@ + t.e_lo@, t.ents@, t.p0 as int, out.0@, out.1@, j)
}

/// Unpacking: a packed value's row and date code.
proof fn lemma_unpack(x: u64)
    ensures
        x as int % p32() == (x % 0x1_0000_0000) as int,
        x as int / p32() == (x / 0x1_0000_0000) as int,
        (x / 0x1_0000_0000) as int <= 0xffff_ffff,
{
}

/// Packing one position.
proof fn lemma_pack_one(fp: Seq<PartView>, dbase: int, p: int, s: int, d: int, c: int, value: u64)
    requires s == kirow(fp, p), d == date_at(fp, s), c == d - dbase, value as int == c * p32() + s,
    ensures packed_ok(fp, dbase, p, value),
{
    reveal(packed_ok);
}

/// Step 1 of a task: pack every position's stored row and date code.
fn pack_run(ic: &[u32], ib: &[u64], dc: &[u16], db: &[i64], bs: usize, n: usize, dbase: i64, p0: usize, len: usize,
    packed: &mut Vec<u64>, Ghost(fp): Ghost<Seq<PartView>>)
    requires
        task_src(fp, n as int, bs as int, ic@, ib@, dc@, db@),
        dates_in(fp, n as int, dbase as int),
        p0 + len <= n,
        old(packed)@.len() == len,
    ensures
        final(packed)@.len() == len,
        forall|x: int| 0 <= x < len ==> #[trigger] packed_ok(fp, dbase as int, p0 + x, final(packed)@[x]),
    no_unwind
{
    proof {
        lemma_task_src(fp, n as int, bs as int, ic@, ib@, dc@, db@);
        reveal(dates_in);
    }
    let mut i: usize = 0;
    while i < len
        invariant
            bs >= 1, bs == bsize(fp),
            ic@.len() == n, ib@.len() * bs >= n, dc@.len() == n, db@.len() * bs >= n,
            n <= 0xffff_ffff,
            forall|p: int| 0 <= p < n ==> 0 <= #[trigger] kirow(fp, p) < n,
            forall|p: int| #[trigger] kirow(fp, p) == ib@[p / (bs as int)] + ic@[p],
            forall|s: int| #[trigger] date_at(fp, s) == db@[s / (bs as int)] + dc@[s],
            forall|s: int| 0 <= s < n ==> dbase <= #[trigger] date_at(fp, s) <= dbase + 0xffff,
            -0x8000_0000 <= dbase <= 0x8000_0000,
            p0 + len <= n,
            i <= len,
            packed@.len() == len,
            forall|x: int| 0 <= x < i ==> #[trigger] packed_ok(fp, dbase as int, p0 + x, packed@[x]),
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
            lemma_div_lt(s as int, bs as int, db@.len() as int);
            assert(dbase <= date_at(fp, s as int) <= dbase + 0xffff);
        }
        let d = db[s / bs] + dc[s] as i64;
        let c = (d - dbase) as u64;
        proof {
            assert(d as int == date_at(fp, s as int));
            assert(c <= 0xffff);
        }
        let value = c * 0x1_0000_0000 + s as u64;
        proof {
            lemma_pack_one(fp, dbase as int, p as int, s as int, d as int, c as int, value);
        }
        let ghost old_packed = packed@;
        crate::gendb_entry::work::put(packed, i, value);
        proof {
            assert forall|x: int| 0 <= x < i + 1 implies #[trigger] packed_ok(fp, dbase as int, p0 + x, packed@[x]) by {
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

/// A packed position of entry `j` holds a row of the entry's key and its date code.
proof fn lemma_good_init(fp: Seq<PartView>, n: int, dbase: int, k0: int, ents: Seq<u32>, j: int, p: int, value: u64)
    requires
        n <= 0xffff_ffff,
        packed_ok(fp, dbase, p, value),
        entry_keys(fp, k0, ents, j),
        ents[j] <= p < ents[j + 1],
        0 <= kirow(fp, p) < n,
        dates_in(fp, n, dbase),
    ensures good(fp, n, dbase, k0 + j, value),
{
    reveal(packed_ok);
    reveal(good);
    reveal(entry_keys);
    reveal(dates_in);
    let s = kirow(fp, p);
    assert(key_at(fp, kirow(fp, p)) == k0 + j);
    assert(dbase <= date_at(fp, s) <= dbase + 0xffff);
    let c = date_at(fp, s) - dbase;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(value as int, p32(), c, s);
}

/// Entry `j` sorted: `seg_done`.
proof fn lemma_seg_done(fp: Seq<PartView>, n: int, dbase: int, k0: int, ents: Seq<u32>, p0: int, v: Seq<u64>, j: int,
    pr: spec_fn(u64) -> bool)
    requires
        p0 <= ents[j] <= ents[j + 1],
        pr == (|x: u64| good(fp, n, dbase, k0 + j, x)),
        all_in(v, ents[j] - p0, ents[j + 1] - p0, pr),
        sorted64(seg64(v, ents[j] - p0, ents[j + 1] - p0)),
    ensures seg_done(fp, n, dbase, k0, ents, p0, v, j),
{
    reveal(seg_done);
    assert forall|x: int| ents[j] - p0 <= x < ents[j + 1] - p0 implies #[trigger] good(fp, n, dbase, k0 + j, v[x]) by {
        assert(pr(v[x]));
    }
}

/// A done entry stays done while only slots after it change.
proof fn lemma_seg_frame(fp: Seq<PartView>, n: int, dbase: int, k0: int, ents: Seq<u32>, p0: int, v0: Seq<u64>,
    v1: Seq<u64>, j: int, lo: int)
    requires
        seg_done(fp, n, dbase, k0, ents, p0, v0, j),
        p0 <= ents[j] <= ents[j + 1], ents[j + 1] - p0 <= lo,
        v0.len() == v1.len(), ents[j + 1] - p0 <= v0.len(),
        forall|x: int| 0 <= x < lo ==> v1[x] == v0[x],
    ensures seg_done(fp, n, dbase, k0, ents, p0, v1, j),
{
    reveal(seg_done);
    assert forall|x: int| ents[j] - p0 <= x < ents[j + 1] - p0 implies #[trigger] good(fp, n, dbase, k0 + j, v1[x]) by {
        assert(v1[x] == v0[x]);
        assert(good(fp, n, dbase, k0 + j, v0[x]));
    }
    assert(seg64(v1, ents[j] - p0, ents[j + 1] - p0) =~= seg64(v0, ents[j] - p0, ents[j + 1] - p0));
}

/// The facts the sort step needs about its run.
pub open spec fn run_facts(fp: Seq<PartView>, n: int, dbase: int, k0: int, ents: Seq<u32>, ne: int, p0: int, len: int) -> bool {
    &&& ents.len() == ne + 1
    &&& ents[0] == p0 && ents[ne] == p0 + len
    &&& p0 + len <= n
    &&& n <= 0xffff_ffff
    &&& ents_mono(ents, ne)
    &&& forall|j: int| 0 <= j < ne ==> #[trigger] entry_keys(fp, k0, ents, j)
    &&& forall|p: int| 0 <= p < n ==> 0 <= #[trigger] kirow(fp, p) < n
    &&& dates_in(fp, n, dbase)
}

/// Step 2 of a task: sort each entry's packed values (so by date code).
fn sort_run(packed: &mut Vec<u64>, tmp: &mut Vec<u64>, ents: &Vec<u32>, ne: usize, p0: usize, len: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(n): Ghost<int>, Ghost(dbase): Ghost<int>, Ghost(k0): Ghost<int>)
    requires
        run_facts(fp, n, dbase, k0, ents@, ne as int, p0 as int, len as int),
        old(packed)@.len() == len, old(tmp)@.len() == len,
        forall|x: int| 0 <= x < len ==> #[trigger] packed_ok(fp, dbase, p0 + x, old(packed)@[x]),
    ensures
        final(packed)@.len() == len,
        forall|j: int| 0 <= j < ne ==> #[trigger] seg_done(fp, n, dbase, k0, ents@, p0 as int, final(packed)@, j),
    no_unwind
{
    let ghost ev = ents@;
    let mut j: usize = 0;
    while j < ne
        invariant
            run_facts(fp, n, dbase, k0, ev, ne as int, p0 as int, len as int), ev == ents@,
            j <= ne,
            packed@.len() == len, tmp@.len() == len,
            forall|x: int| ev[j as int] - p0 <= x < len ==> #[trigger] packed_ok(fp, dbase, p0 + x, packed@[x]),
            forall|jj: int| 0 <= jj < j ==> #[trigger] seg_done(fp, n, dbase, k0, ev, p0 as int, packed@, jj),
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
        let ghost pr = |x: u64| good(fp, n, dbase, k, x);
        proof {
            assert(entry_keys(fp, k0, ev, j as int));
            assert forall|x: int| lo <= x < hi implies #[trigger] pr(packed@[x]) by {
                let p = p0 + x;
                assert(packed_ok(fp, dbase, p0 + x, packed@[x]));
                lemma_good_init(fp, n, dbase, k0, ev, j as int, p, packed@[x]);
            }
        }
        let ghost before = packed@;
        msort64(packed, tmp, lo, hi, Ghost(pr));
        proof {
            lemma_seg_done(fp, n, dbase, k0, ev, p0 as int, packed@, j as int, pr);
            assert forall|x: int| ev[j as int + 1] - p0 <= x < len implies #[trigger] packed_ok(fp, dbase, p0 + x, packed@[x]) by {
                assert(packed@[x] == before[x]);
                assert(packed_ok(fp, dbase, p0 + x, before[x]));
            }
            assert forall|jj: int| 0 <= jj < j + 1 implies #[trigger] seg_done(fp, n, dbase, k0, ev, p0 as int, packed@, jj) by {
                if jj < j {
                    lemma_ents_le(ev, ne as int, 0, jj);
                    lemma_ents_le(ev, ne as int, jj, jj + 1);
                    lemma_ents_le(ev, ne as int, jj + 1, j as int);
                    assert forall|x: int| 0 <= x < lo implies packed@[x] == before[x] by {}
                    lemma_seg_frame(fp, n, dbase, k0, ev, p0 as int, before, packed@, jj, lo as int);
                }
            }
        }
        j = j + 1;
    }
}

/// Step 3 of a task: unpack every packed value into its stored row and date code.
fn unpack_run(packed: &Vec<u64>, rows: &mut Vec<u32>, dates: &mut Vec<u16>, len: usize)
    requires packed@.len() == len, old(rows)@.len() == len, old(dates)@.len() == len,
    ensures
        final(rows)@.len() == len, final(dates)@.len() == len,
        forall|x: int| 0 <= x < len ==> (#[trigger] final(rows)@[x]) as int == packed@[x] as int % p32(),
        forall|x: int| 0 <= x < len && packed@[x] as int / p32() <= 0xffff ==> (#[trigger] final(dates)@[x]) as int == packed@[x] as int / p32(),
    no_unwind
{
    let mut i: usize = 0;
    while i < len
        invariant
            packed@.len() == len, rows@.len() == len, dates@.len() == len,
            i <= len,
            forall|x: int| 0 <= x < i ==> (#[trigger] rows@[x]) as int == packed@[x] as int % p32(),
            forall|x: int| 0 <= x < i && packed@[x] as int / p32() <= 0xffff ==> (#[trigger] dates@[x]) as int == packed@[x] as int / p32(),
        decreases len - i,
    {
        let x = packed[i];
        proof { lemma_unpack(x); }
        let c = x / 0x1_0000_0000;
        let ghost (r0, d0) = (rows@, dates@);
        crate::gendb_entry::work::put(rows, i, (x % 0x1_0000_0000) as u32);
        crate::gendb_entry::work::put(dates, i, (if c <= 0xffff { c } else { 0 }) as u16);
        proof {
            assert forall|y: int| 0 <= y < i + 1 implies (#[trigger] rows@[y]) as int == packed@[y] as int % p32() by {
                if y < i { assert(rows@[y] == r0[y]); }
            }
            assert forall|y: int| 0 <= y < i + 1 && packed@[y] as int / p32() <= 0xffff implies (#[trigger] dates@[y]) as int == packed@[y] as int / p32() by {
                if y < i { assert(dates@[y] == d0[y]); }
            }
        }
        i = i + 1;
    }
}

/// Packed order: a smaller packed value has a date code at most the other's.
proof fn lemma_packed_order(x: u64, y: u64)
    requires x <= y,
    ensures x as int / p32() <= y as int / p32(),
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, y as int, p32());
}

/// Entry `j` of the output from its sorted packed values.
proof fn lemma_entry_unpacked(fp: Seq<PartView>, n: int, dbase: int, k0: int, ents: Seq<u32>, p0: int, len: int,
    packed: Seq<u64>, rows: Seq<u32>, dates: Seq<u16>, j: int)
    requires
        seg_done(fp, n, dbase, k0, ents, p0, packed, j),
        p0 <= ents[j] <= ents[j + 1] <= p0 + len,
        packed.len() == len, rows.len() == len, dates.len() == len,
        forall|x: int| 0 <= x < len ==> (#[trigger] rows[x]) as int == packed[x] as int % p32(),
        forall|x: int| 0 <= x < len && packed[x] as int / p32() <= 0xffff ==> (#[trigger] dates[x]) as int == packed[x] as int / p32(),
    ensures entry_out(fp, n, dbase, k0, ents, p0, rows, dates, j),
{
    reveal(seg_done);
    reveal(good);
    reveal(entry_out);
    let lo = ents[j] - p0;
    let hi = ents[j + 1] - p0;
    assert forall|x: int| lo <= x < hi implies {
        &&& (#[trigger] rows[x]) < n
        &&& key_at(fp, rows[x] as int) == k0 + j
        &&& dbase + dates[x] == date_at(fp, rows[x] as int)
        &&& (x + 1 < hi ==> dates[x] <= dates[x + 1])
    } by {
        assert(good(fp, n, dbase, k0 + j, packed[x]));
        if x + 1 < hi {
            assert(good(fp, n, dbase, k0 + j, packed[x + 1]));
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
        run_facts(t.fp@, t.n as int, t.dbase as int, t.kmin@ + t.e_lo@, t.ents@, t.ne as int, t.p0 as int, (t.p1 - t.p0) as int),
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
        let mut dates = self.dates;
        proof {
            lemma_pre_facts(self);
        }
        pack_run(self.ic, self.ib, self.dc, self.db, self.bs, self.n, self.dbase, p0, len, &mut packed, Ghost(fp));
        sort_run(&mut packed, &mut tmp, &self.ents, ne, p0, len, Ghost(fp), Ghost(self.n as int), Ghost(self.dbase as int), Ghost(k0));
        unpack_run(&packed, &mut rows, &mut dates, len);
        proof {
            assert forall|j: int| 0 <= j < ne implies
                #[trigger] entry_out(fp, self.n as int, self.dbase as int, k0, ev, p0 as int, rows@, dates@, j) by {
                lemma_ents_le(ev, ne as int, 0, j);
                lemma_ents_le(ev, ne as int, j, j + 1);
                lemma_ents_le(ev, ne as int, j + 1, ne as int);
                lemma_entry_unpacked(fp, self.n as int, self.dbase as int, k0, ev, p0 as int, len as int, packed@, rows@, dates@, j);
            }
        }
        (rows, dates)
    }
}

} // verus!
