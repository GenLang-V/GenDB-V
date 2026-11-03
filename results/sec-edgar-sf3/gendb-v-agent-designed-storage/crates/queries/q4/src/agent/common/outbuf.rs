//! A preallocated append-only output buffer for worker tasks: allocated once on the calling thread with
//! `vec![fill; capacity]` (one bulk fill instead of a push per slot), filled by `push` (`no_unwind`) in a worker body,
//! and handed back as its pushed prefix. The view is the pushed values in push order.
use vstd::prelude::*;

verus! {

pub struct OutBuf<T> {
    slots: Vec<T>,
    used: usize,
}

impl<T: Copy> OutBuf<T> {
    /// The pushed values, in push order.
    pub closed spec fn view(&self) -> Seq<T> {
        self.slots@.subrange(0, self.used as int)
    }

    /// The number of preallocated slots.
    pub closed spec fn capacity(&self) -> nat {
        self.slots@.len()
    }

    /// The representation invariant (kept by every method).
    pub closed spec fn wf(&self) -> bool {
        self.used <= self.slots@.len()
    }

    /// An empty buffer with `capacity` slots (calling thread; allocates).
    pub fn new(capacity: usize, fill: T) -> (b: Self)
        ensures b.wf(), b.view() == Seq::<T>::empty(), b.capacity() == capacity,
    {
        let slots = vec![fill; capacity];
        OutBuf { slots, used: 0 }
    }

    /// The number of pushed values, `no_unwind`.
    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.view().len(),
        no_unwind
    {
        self.used
    }

    /// Append `x` into the next free slot, `no_unwind` (allocates nothing).
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
