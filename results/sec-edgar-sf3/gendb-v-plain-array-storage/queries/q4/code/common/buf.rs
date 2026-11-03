//! A preallocated output buffer usable in `no_unwind` worker bodies (like `gendb_entry::work::TaskBuffer`) that
//! can also be emptied (`clear`) and drained into a vector on the calling thread, so one buffer serves many
//! short runs. `view()` is the pushed values in push order; `push` needs a free slot.
use vstd::prelude::*;

verus! {

pub struct Buf<T> {
    slots: Vec<T>,
    used: usize,
}

impl<T: Copy> Buf<T> {
    /// The pushed values, in push order.
    pub closed spec fn view(&self) -> Seq<T> {
        self.slots@.subrange(0, self.used as int)
    }

    /// The number of preallocated slots.
    pub closed spec fn capacity(&self) -> nat {
        self.slots@.len()
    }

    pub closed spec fn wf(&self) -> bool {
        self.used <= self.slots@.len()
    }

    /// An empty buffer with `capacity` slots (calling thread; allocates).
    pub fn new(capacity: usize, fill: T) -> (b: Self)
        ensures b.wf(), b.view() == Seq::<T>::empty(), b.capacity() == capacity,
    {
        let slots: Vec<T> = vec![fill; capacity];
        let b = Buf { slots, used: 0 };
        proof {
            assert(b.view() =~= Seq::<T>::empty());
        }
        b
    }

    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.view().len(),
        no_unwind
    {
        self.used
    }

    pub fn cap(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.capacity(),
        no_unwind
    {
        self.slots.len()
    }

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

    /// Forget the pushed values (the slots stay allocated).
    pub fn clear(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).view() == Seq::<T>::empty(), final(self).capacity() == old(self).capacity(),
        no_unwind
    {
        self.used = 0;
        proof {
            assert(self.view() =~= Seq::<T>::empty());
        }
    }

    /// Keep the first `n` pushed values.
    pub fn truncate_to(&mut self, n: usize)
        requires old(self).wf(), n <= old(self).view().len(),
        ensures
            final(self).wf(), final(self).view() == old(self).view().subrange(0, n as int),
            final(self).capacity() == old(self).capacity(),
        no_unwind
    {
        self.used = n;
        proof {
            assert(self.view() =~= old(self).view().subrange(0, n as int));
        }
    }

    /// Append the pushed values to `v` (calling thread).
    pub fn drain_into(&self, v: &mut Vec<T>)
        requires self.wf(),
        ensures final(v)@ == old(v)@ + self.view(),
    {
        let n = self.used;
        let mut i: usize = 0;
        while i < n
            invariant
                self.wf(), n == self.used, i <= n,
                v@ == old(v)@ + self.view().subrange(0, i as int),
            decreases n - i,
        {
            v.push(self.slots[i]);
            i = i + 1;
            proof {
                assert(self.view().subrange(0, i as int) =~= self.view().subrange(0, i - 1).push(self.slots@[i - 1]));
            }
        }
        proof {
            assert(self.view().subrange(0, n as int) =~= self.view());
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
