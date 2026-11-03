//! A dense-keyed map `[0, n) -> V` with a default value, as a sparse set: `pos` (n entries, zeroed allocation, never
//! reset) points into the dense `keys`/`vals` lists; key `k` is present when `pos[k] < |keys|` and `keys[pos[k]] == k`
//! (so stale `pos` entries never need clearing). Get and set are O(1); `reset` empties the map in O(1). Memory
//! touched per call is the dense lists plus the `pos` pages of the keys used, instead of an `n`-entry value array.
use vstd::prelude::*;

verus! {

pub struct SlotMap<V> {
    pos: Vec<usize>,
    keys: Vec<usize>,
    vals: Vec<V>,
    dflt: V,
}

impl<V: Copy> SlotMap<V> {
    /// Key `k` has a dense entry.
    pub closed spec fn present(&self, k: int) -> bool {
        &&& 0 <= k < self.pos@.len()
        &&& self.pos@[k] < self.keys@.len()
        &&& self.keys@[self.pos@[k] as int] == k
    }

    /// The map as a sequence of `n` values.
    pub closed spec fn view(&self) -> Seq<V> {
        Seq::new(self.pos@.len(), |k: int| if self.present(k) { self.vals@[self.pos@[k] as int] } else { self.dflt })
    }

    /// The value of absent keys.
    pub closed spec fn default_value(&self) -> V {
        self.dflt
    }

    /// The representation invariant (kept by every method).
    pub closed spec fn wf(&self) -> bool {
        &&& self.vals@.len() == self.keys@.len()
        &&& forall|i: int| 0 <= i < self.keys@.len() ==>
                (#[trigger] self.keys@[i]) < self.pos@.len() && self.pos@[self.keys@[i] as int] == i
    }

    /// The map of `n` keys, all with value `d` (calling thread; one zeroed allocation).
    pub fn new(n: usize, d: V) -> (m: Self)
        ensures m.wf(), m.view() == Seq::new(n as nat, |_k: int| d), m.default_value() == d,
    {
        let m = SlotMap { pos: vec![0usize; n], keys: Vec::new(), vals: Vec::new(), dflt: d };
        proof { assert(m.view() =~= Seq::new(n as nat, |_k: int| d)); }
        m
    }

    /// The number of keys, `no_unwind`.
    pub fn len(&self) -> (n: usize)
        ensures n == self.view().len(),
        no_unwind
    {
        self.pos.len()
    }

    /// The value of key `k`, `no_unwind`.
    pub fn get(&self, k: usize) -> (v: V)
        requires self.wf(), k < self.view().len(),
        ensures v == self.view()[k as int],
        no_unwind
    {
        let p = self.pos[k];
        if p < self.keys.len() && self.keys[p] == k {
            self.vals[p]
        } else {
            self.dflt
        }
    }

    /// Sets key `k` to `v` (calling thread; may grow the dense lists).
    pub fn set(&mut self, k: usize, v: V)
        requires old(self).wf(), k < old(self).view().len(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().update(k as int, v),
            final(self).default_value() == old(self).default_value(),
    {
        let ghost o = *self;
        let p = self.pos[k];
        if p < self.keys.len() && self.keys[p] == k {
            self.vals.set(p, v);
            proof {
                assert(self.view() =~= o.view().update(k as int, v)) by {
                    assert forall|j: int| 0 <= j < o.pos@.len() implies #[trigger] self.view()[j] == o.view().update(k as int, v)[j] by {
                        if j != k && o.present(j) {
                            // Distinct present keys have distinct dense positions.
                            assert(o.pos@[j] != p);
                        }
                    }
                }
            }
        } else {
            let i = self.keys.len();
            self.pos.set(k, i);
            self.keys.push(k);
            self.vals.push(v);
            proof {
                // No old dense entry holds `k` (else `pos[k]` would point at it).
                assert forall|t: int| 0 <= t < o.keys@.len() implies #[trigger] o.keys@[t] != k by {
                    if o.keys@[t] == k { assert(o.pos@[k as int] == t); }
                }
                assert forall|t: int| 0 <= t < self.keys@.len() implies
                    (#[trigger] self.keys@[t]) < self.pos@.len() && self.pos@[self.keys@[t] as int] == t by {
                    if t < i { assert(self.keys@[t] == o.keys@[t]); }
                }
                assert forall|j: int| 0 <= j < o.pos@.len() && j != k implies #[trigger] self.present(j) == o.present(j) by {
                    if o.present(j) { assert(self.keys@[o.pos@[j] as int] == o.keys@[o.pos@[j] as int]); }
                    if self.present(j) && self.pos@[j] < i { assert(self.keys@[self.pos@[j] as int] == o.keys@[self.pos@[j] as int]); }
                }
                assert(self.view() =~= o.view().update(k as int, v)) by {
                    assert forall|j: int| 0 <= j < o.pos@.len() implies #[trigger] self.view()[j] == o.view().update(k as int, v)[j] by {
                        if j != k && o.present(j) {
                            assert(self.vals@[o.pos@[j] as int] == o.vals@[o.pos@[j] as int]);
                        }
                    }
                }
            }
        }
    }

    /// Every key back to the default value, in O(1) (the dense lists are cleared; `pos` is left as is).
    pub fn reset(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == Seq::new(old(self).view().len(), |_k: int| old(self).default_value()),
            final(self).default_value() == old(self).default_value(),
    {
        self.keys.clear();
        self.vals.clear();
        proof { assert(self.view() =~= Seq::new(old(self).view().len(), |_k: int| old(self).default_value())); }
    }
}

} // verus!
