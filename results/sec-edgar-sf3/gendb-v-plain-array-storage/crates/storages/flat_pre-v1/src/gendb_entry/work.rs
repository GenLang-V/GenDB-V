// FRAMEWORK FILE: verified helpers for candidates (`verification/obligations/gendb_entry/work.rs`).
//
// Copied unchanged into every candidate crate as `crate::gendb_entry::work`. Authors
// cannot edit it; they may call it. Checked by Verus with `--no-cheating` together with the
// candidate; no `assume`, `admit` or `external_body`.
//
// - `text_bytes`: the bytes of one canonical Utf8 value (`link::query::text_at`), `no_unwind`, so
//   worker bodies (`WorkerTask::run`) can read text columns and text parts.
// - `text_eq`: byte equality of two text values (for example group keys), `no_unwind`.
// - `text_offsets_ok`: the verified decision of `link::query::text_wf` (a text column's offsets), used
//   by the generated binder (`binder.rs`) to decide the source declaration's `source_wf` exactly.
// - `filled`: a caller-thread allocation of `n` copies of a value. Worker bodies cannot allocate
//   (`no_unwind`); allocate their output storage with this (or any loop) on the calling thread,
//   move it into the task, fill it there and return it as the task output.
// - `put`: the verified `no_unwind` write of one slot of such a buffer (`v[i] = x`). The pinned
//   vstd's `Vec::set` (`VecAdditionalExecFns`) has NO `no_unwind` specification, so Verus refuses
//   it in a worker body; use `put` or the index assignment `v[i] = x` itself.
// - `TaskBuffer`: a preallocated append-only buffer for a worker whose output count is not known in
//   advance (for example the rows of a range that pass a filter): `TaskBuffer::new(capacity, fill)`
//   on the calling thread, `push` (`no_unwind`, while `len() < capacity()`) in the worker,
//   `into_vec` on the calling thread after the join (its view is exactly the pushed values).
//   Concatenate per-task results on the calling thread, e.g. with `Vec::append`.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol};

verus! {

/// Bytes of value `i` of a text column: `bytes[offsets[i] .. offsets[i + 1]]`.
pub fn text_bytes(c: &TextCol, i: usize) -> (r: &'static [u8])
    requires
        i + 1 < c.offsets@.len(),
        0 <= c.offsets@[i as int],
        c.offsets@[i as int] <= c.offsets@[i + 1],
        c.offsets@[i + 1] <= c.bytes@.len(),
    ensures
        r@ == text_at(c@, i as int),
    no_unwind
{
    let bytes: &'static [u8] = c.bytes;
    let a = c.offsets[i];
    let b = c.offsets[i + 1];
    // Spec-level length (slice `len` has no `no_unwind` spec, so it is not called here).
    assert(0 <= a <= b <= bytes.len());
    let lo = a as usize;
    let hi = b as usize;
    let (_, tail) = bytes.split_at(lo);
    let (mid, _) = tail.split_at(hi - lo);
    proof {
        assert(mid@ =~= c.bytes@.subrange(lo as int, hi as int));
    }
    mid
}

/// Byte equality of values `i` and `j` of text columns `a` and `b` (for example group keys), `no_unwind`.
pub fn text_eq(a: &TextCol, i: usize, b: &TextCol, j: usize) -> (r: bool)
    requires
        i + 1 < a.offsets@.len(),
        0 <= a.offsets@[i as int],
        a.offsets@[i as int] <= a.offsets@[i + 1],
        a.offsets@[i + 1] <= a.bytes@.len(),
        j + 1 < b.offsets@.len(),
        0 <= b.offsets@[j as int],
        b.offsets@[j as int] <= b.offsets@[j + 1],
        b.offsets@[j + 1] <= b.bytes@.len(),
    ensures
        r == (text_at(a@, i as int) == text_at(b@, j as int)),
    no_unwind
{
    let x = text_bytes(a, i);
    let y = text_bytes(b, j);
    let a0 = a.offsets[i];
    let a1 = a.offsets[i + 1];
    let b0 = b.offsets[j];
    let b1 = b.offsets[j + 1];
    assert(x@.len() == a1 - a0 && y@.len() == b1 - b0);
    assert(a1 <= a.bytes.len());
    if a1 - a0 != b1 - b0 {
        proof {
            assert(x@.len() != y@.len());
        }
        return false;
    }
    let n = (a1 - a0) as usize;
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            x@ == text_at(a@, i as int),
            y@ == text_at(b@, j as int),
            x@.len() == n,
            y@.len() == n,
            forall|t: int| 0 <= t < k ==> x@[t] == y@[t],
        decreases n - k,
    {
        if x[k] != y[k] {
            proof {
                assert(x@[k as int] != y@[k as int]);
                assert(x@ != y@);
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

/// Decides `text_wf(c@, n)` in one pass (used by the binder on the build path only).
pub fn text_offsets_ok(c: &TextCol, n: usize) -> (b: bool)
    ensures b == text_wf(c@, n as int),
{
    let offsets: &[i64] = c.offsets;
    let bytes: &[u8] = c.bytes;
    let count = offsets.len();
    if n == usize::MAX || count != n + 1 {
        return false;
    }
    let len = bytes.len();
    let mut i: usize = 0;
    while i < n
        invariant
            offsets@ == c@.offsets,
            bytes@ == c@.bytes,
            offsets.len() == n + 1,
            len == bytes@.len(),
            i <= n,
            forall|k: int| 0 <= k < i ==> 0 <= #[trigger] offsets@[k] && offsets@[k] <= offsets@[k + 1] && offsets@[k + 1] <= bytes@.len(),
        decreases n - i,
    {
        let a = offsets[i];
        let b = offsets[i + 1];
        if a < 0 || a > b || b as i128 > len as i128 {
            proof {
                if text_wf(c@, n as int) {
                    assert(0 <= c@.offsets[i as int] <= c@.offsets[i as int + 1] <= c@.bytes.len());
                }
            }
            return false;
        }
        i = i + 1;
    }
    true
}

/// `n` copies of `x`, allocated on the calling thread (may unwind: never call it in a worker body).
pub fn filled<T: Copy>(n: usize, x: T) -> (v: Vec<T>)
    ensures v@ == Seq::new(n as nat, |_i: int| x),
{
    let mut v: Vec<T> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v@ == Seq::new(i as nat, |_i: int| x),
        decreases n - i,
    {
        v.push(x);
        i = i + 1;
        proof {
            assert(v@ =~= Seq::new(i as nat, |_i: int| x));
        }
    }
    v
}

/// Write slot `i` of a preallocated buffer: `v[i] = x`, `no_unwind` (usable in worker bodies).
pub fn put<T>(v: &mut Vec<T>, i: usize, x: T)
    requires i < old(v)@.len(),
    ensures final(v)@ == old(v)@.update(i as int, x),
    no_unwind
{
    v[i] = x;
}

/// A preallocated append-only output buffer of one worker task. Its view is the pushed values in push order;
/// `capacity()` is the number of slots allocated on the calling thread.
pub struct TaskBuffer<T> {
    slots: Vec<T>,
    used: usize,
}

impl<T: Copy> TaskBuffer<T> {
    /// The pushed values, in push order.
    pub closed spec fn view(&self) -> Seq<T> {
        self.slots@.subrange(0, self.used as int)
    }

    /// The number of preallocated slots.
    pub closed spec fn capacity(&self) -> nat {
        self.slots@.len()
    }

    /// The buffer's representation invariant (kept by every method).
    pub closed spec fn wf(&self) -> bool {
        self.used <= self.slots@.len()
    }

    /// An empty buffer with `capacity` slots, each initialized to `fill` (calling thread; may allocate).
    pub fn new(capacity: usize, fill: T) -> (b: Self)
        ensures b.wf(), b.view() == Seq::<T>::empty(), b.capacity() == capacity,
    {
        TaskBuffer { slots: filled(capacity, fill), used: 0 }
    }

    /// The number of pushed values, `no_unwind`.
    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.view().len(),
        no_unwind
    {
        self.used
    }

    /// The number of slots, `no_unwind`.
    pub fn slots(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.capacity(),
        no_unwind
    {
        self.slots.len()
    }

    /// Append `x` into the next free slot, `no_unwind` (usable in worker bodies; allocates nothing).
    pub fn push(&mut self, x: T)
        requires old(self).wf(), old(self).view().len() < old(self).capacity(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().push(x),
            final(self).capacity() == old(self).capacity(),
        no_unwind
    {
        let i = self.used;
        let n = self.slots.len();
        assert(i < n);
        self.slots[i] = x;
        self.used = i + 1;
        proof {
            assert(self.slots@.subrange(0, self.used as int) =~= old(self).slots@.subrange(0, i as int).push(x));
        }
    }

    /// The pushed values as a vector (calling thread, after the join).
    pub fn into_vec(self) -> (v: Vec<T>)
        requires self.wf(),
        ensures v@ == self.view(),
    {
        let used = self.used;
        let mut slots = self.slots;
        slots.truncate(used);
        proof {
            assert(slots@ =~= self.slots@.subrange(0, used as int));
        }
        slots
    }
}

} // verus!
