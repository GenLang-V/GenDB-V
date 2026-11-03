//! A preallocated append-only buffer for worker tasks, allocated with `vec![fill; capacity]` (for zero fills
//! the allocator hands out lazily zeroed pages, so untouched slots cost nothing) and filled with a `no_unwind`
//! `push` while `len() < capacity()`.
//!
//! Layout: `slots` holds `capacity` values; the first `used` of them are the pushed values in push order (the
//! view); the rest still hold the fill value and are never read.
use vstd::prelude::*;

verus! {

/// Preallocated append-only buffer of one worker task.
pub struct SlotBuffer<T> {
    slots: Vec<T>,
    used: usize,
}

impl<T: Copy> SlotBuffer<T> {
    /// The pushed values, in push order.
    pub closed spec fn view(&self) -> Seq<T> {
        self.slots@.subrange(0, self.used as int)
    }

    /// The number of preallocated slots.
    pub closed spec fn capacity(&self) -> nat {
        self.slots@.len()
    }

    /// Representation invariant: the pushed values fit in the slots.
    pub closed spec fn wf(&self) -> bool {
        self.used <= self.slots@.len()
    }

    /// An empty buffer of `capacity` slots (calling thread; allocates).
    pub fn new(capacity: usize, fill: T) -> (b: Self)
        ensures b.wf(), b.view() == Seq::<T>::empty(), b.capacity() == capacity,
    {
        let slots = vec![fill; capacity];
        SlotBuffer { slots, used: 0 }
    }

    /// The number of pushed values.
    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.view().len(),
        no_unwind
    {
        self.used
    }

    /// Whether another value fits.
    pub fn has_room(&self) -> (r: bool)
        requires self.wf(),
        ensures r == (self.view().len() < self.capacity()),
        no_unwind
    {
        self.used < self.slots.len()
    }

    /// Append `x` (requires room; allocates nothing).
    pub fn push(&mut self, x: T)
        requires old(self).wf(), old(self).view().len() < old(self).capacity(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().push(x),
            final(self).capacity() == old(self).capacity(),
        no_unwind
    {
        let i = self.used;
        let cap = self.slots.len();
        assert(i < cap);
        self.slots[i] = x;
        self.used = i + 1;
        proof {
            assert(self.slots@.subrange(0, self.used as int) =~= old(self).slots@.subrange(0, i as int).push(x));
        }
    }

    /// The pushed values as a vector (calling thread).
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
