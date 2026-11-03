//! A preallocated append-only buffer of join contributions whose slots are zero-initializable: the executable fields
//! of a `Contrib` are stored as tuples of primitives, so `vec![zero; capacity]` is one zeroed allocation (pages are
//! faulted in by the worker that writes them, not filled on the calling thread); the ghost coordinates live in a
//! ghost sequence beside it. The view is the pushed contributions in push order. `cflat` concatenates the views of a
//! sequence of buffers (the per-task outputs kept in task order).
//!
//! Layout: one 32-byte narrow entry per contribution (`CNar`: sum as i64, mass as u64, filing, slot and count as
//! u32). A contribution whose fields do not fit (or that is not `ok`) is kept whole in the wide list (`CRaw`, 64
//! bytes) and its narrow entry holds its wide index (`kind != 0`). The wide list has the narrow list's capacity but
//! is only written for such contributions, so its pages are normally never touched.
use vstd::prelude::*;
use crate::agent::join::Contrib;

verus! {

/// The executable fields of a contribution: (f, slot, cnt, sum, mass, ok).
pub type CRaw = (usize, u64, u64, i128, u128, bool);

/// A narrow entry: (sum, mass, f, slot, cnt, kind); with `kind != 0` the contribution is wide entry `mass`.
pub type CNar = (i64, u64, u32, u32, u32, u32);

pub open spec fn mk_contrib(r: CRaw, g: (int, int, int)) -> Contrib {
    Contrib { f: r.0, slot: r.1, cnt: r.2, sum: r.3, mass: r.4, ok: r.5, rs: Ghost(g.0), re: Ghost(g.1), nq: Ghost(g.2) }
}

/// The contribution of a narrow entry (`ok`, fields widened), or of the wide entry it points at.
pub open spec fn decode(e: CNar, wide: Seq<CRaw>, g: (int, int, int)) -> Contrib {
    if e.5 == 0 {
        Contrib { f: e.2 as usize, slot: e.3 as u64, cnt: e.4 as u64, sum: e.0 as i128, mass: e.1 as u128, ok: true,
            rs: Ghost(g.0), re: Ghost(g.1), nq: Ghost(g.2) }
    } else if (e.1 as int) < wide.len() {
        mk_contrib(wide[e.1 as int], g)
    } else {
        mk_contrib((0usize, 0u64, 0u64, 0i128, 0u128, false), g)
    }
}

pub struct CBuf {
    nar: Vec<CNar>,
    wide: Vec<CRaw>,
    nwide: usize,
    gh: Ghost<Seq<(int, int, int)>>,
    used: usize,
}

impl CBuf {
    /// The number of pushed contributions (at most the slot count).
    pub closed spec fn n(&self) -> nat {
        if self.used <= self.nar@.len() { self.used as nat } else { self.nar@.len() }
    }

    /// The number of preallocated slots.
    pub closed spec fn capacity(&self) -> nat {
        self.nar@.len()
    }

    /// The representation invariant (kept by every method): every wide index points below `nwide`, and at most one
    /// wide entry per pushed contribution (so a free wide entry exists while a slot is free).
    pub closed spec fn wf(&self) -> bool {
        &&& self.used <= self.nar@.len() && self.gh@.len() == self.used
        &&& self.wide@.len() == self.nar@.len() && self.nwide <= self.used
        &&& forall|i: int| 0 <= i < self.used ==> (#[trigger] self.nar@[i]).5 != 0 ==> self.nar@[i].1 < self.nwide
    }
}

impl CBuf {
    /// The pushed contributions, in push order.
    pub closed spec fn view(&self) -> Seq<Contrib> {
        Seq::new(self.n(), |i: int| decode(self.nar@[i], self.wide@, self.gh@[i]))
    }
}

impl CBuf {
    /// An empty buffer with `capacity` zeroed slots (calling thread; two zeroed allocations).
    pub fn new(capacity: usize) -> (b: Self)
        ensures b.wf(), b.view() == Seq::<Contrib>::empty(), b.capacity() == capacity,
    {
        let nar = vec![(0i64, 0u64, 0u32, 0u32, 0u32, 0u32); capacity];
        let wide = vec![(0usize, 0u64, 0u64, 0i128, 0u128, false); capacity];
        let b = CBuf { nar, wide, nwide: 0, gh: Ghost(Seq::empty()), used: 0 };
        proof { assert(b.view() =~= Seq::<Contrib>::empty()); }
        b
    }

    /// The number of pushed contributions, `no_unwind`.
    pub fn len(&self) -> (n: usize)
        ensures n == self.view().len(),
        no_unwind
    {
        let m = self.nar.len();
        if self.used <= m { self.used } else { m }
    }

    /// Contribution `i`, `no_unwind`.
    pub fn get(&self, i: usize) -> (c: Contrib)
        requires i < self.view().len(),
        ensures c == self.view()[i as int],
        no_unwind
    {
        let e = self.nar[i];
        let ghost g = self.gh@[i as int];
        if e.5 == 0 {
            Contrib { f: e.2 as usize, slot: e.3 as u64, cnt: e.4 as u64, sum: e.0 as i128, mass: e.1 as u128, ok: true,
                rs: Ghost(g.0), re: Ghost(g.1), nq: Ghost(g.2) }
        } else if e.1 < self.wide.len() as u64 {
            let r = self.wide[e.1 as usize];
            Contrib { f: r.0, slot: r.1, cnt: r.2, sum: r.3, mass: r.4, ok: r.5, rs: Ghost(g.0), re: Ghost(g.1), nq: Ghost(g.2) }
        } else {
            // (Not reached in a well-formed buffer.)
            Contrib { f: 0, slot: 0, cnt: 0, sum: 0, mass: 0, ok: false, rs: Ghost(g.0), re: Ghost(g.1), nq: Ghost(g.2) }
        }
    }

    /// Append `c` into the next free slot, `no_unwind` (allocates nothing).
    pub fn push(&mut self, c: Contrib)
        requires old(self).wf(), old(self).view().len() < old(self).capacity(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().push(c),
            final(self).capacity() == old(self).capacity(),
        no_unwind
    {
        let i = self.used;
        let n = self.nar.len();
        assert(i < n);
        let fits = c.ok && c.sum >= i64::MIN as i128 && c.sum <= i64::MAX as i128 && c.mass <= u64::MAX as u128
            && c.f <= u32::MAX as usize && c.slot <= u32::MAX as u64 && c.cnt <= u32::MAX as u64;
        if fits {
            self.nar[i] = (c.sum as i64, c.mass as u64, c.f as u32, c.slot as u32, c.cnt as u32, 0u32);
        } else {
            let w = self.nwide;
            assert(w < n);
            self.wide[w] = (c.f, c.slot, c.cnt, c.sum, c.mass, c.ok);
            self.nar[i] = (0i64, w as u64, 0u32, 0u32, 0u32, 1u32);
            self.nwide = w + 1;
        }
        let ghost g = (c.rs@, c.re@, c.nq@);
        self.gh = Ghost(self.gh@.take(i as int).push(g));
        self.used = i + 1;
        proof {
            assert(decode(self.nar@[i as int], self.wide@, self.gh@[i as int]) == c);
            assert(self.view() =~= old(self).view().push(c)) by {
                assert forall|k: int| 0 <= k < i implies #[trigger] self.view()[k] == old(self).view()[k] by {
                    assert(self.nar@[k] == old(self).nar@[k]);
                    assert(self.gh@[k] == old(self).gh@[k]);
                    if self.nar@[k].5 != 0 {
                        assert(self.wide@[self.nar@[k].1 as int] == old(self).wide@[old(self).nar@[k].1 as int]);
                    }
                }
            }
        }
    }

    /// One buffer holding the contributions of every buffer of `bs`, in order (calling thread; copies, every
    /// contribution kept wide).
    pub fn merge_all(bs: Vec<CBuf>) -> (r: CBuf)
        ensures r.view() == cflat(bs@), r.wf(),
    {
        let mut nar: Vec<CNar> = Vec::new();
        let mut wide: Vec<CRaw> = Vec::new();
        let ghost mut gh: Seq<(int, int, int)> = Seq::empty();
        let nb = bs.len();
        let mut i: usize = 0;
        proof { assert(bs@.take(0) =~= Seq::<CBuf>::empty()); }
        while i < nb
            invariant
                nb == bs@.len(), i <= nb, wide@.len() == gh.len(), nar@.len() == wide@.len(),
                forall|k: int| 0 <= k < nar@.len() ==> #[trigger] nar@[k] == (0i64, k as u64, 0u32, 0u32, 0u32, 1u32),
                forall|k: int| 0 <= k < wide@.len() ==> #[trigger] mk_contrib(wide@[k], gh[k]) == cflat(bs@.take(i as int))[k],
                wide@.len() == cflat(bs@.take(i as int)).len(),
            decreases nb - i,
        {
            let b = &bs[i];
            let m = b.len();
            let ghost base = wide@.len();
            proof { lemma_cflat_take(bs@, i as int); }
            let mut j: usize = 0;
            while j < m
                invariant
                    nb == bs@.len(), i < nb, *b == bs@[i as int], m == b.view().len(), j <= m,
                    wide@.len() == gh.len(), nar@.len() == wide@.len(),
                    wide@.len() == base + j, base == cflat(bs@.take(i as int)).len(),
                    cflat(bs@.take(i + 1)) == cflat(bs@.take(i as int)) + b.view(),
                    forall|k: int| 0 <= k < nar@.len() ==> #[trigger] nar@[k] == (0i64, k as u64, 0u32, 0u32, 0u32, 1u32),
                    forall|k: int| 0 <= k < wide@.len() ==> #[trigger] mk_contrib(wide@[k], gh[k]) == cflat(bs@.take(i + 1))[k],
                decreases m - j,
            {
                let c = b.get(j);
                let w = wide.len();
                wide.push((c.f, c.slot, c.cnt, c.sum, c.mass, c.ok));
                nar.push((0i64, w as u64, 0u32, 0u32, 0u32, 1u32));
                proof {
                    gh = gh.push((c.rs@, c.re@, c.nq@));
                    assert(mk_contrib(wide@[base + j], gh[base + j]) == c);
                }
                j = j + 1;
            }
            i = i + 1;
        }
        proof { lemma_cflat_all(bs@); }
        let n = nar.len();
        let r = CBuf { nar, wide, nwide: n, gh: Ghost(gh), used: n };
        proof {
            assert forall|k: int| 0 <= k < n implies #[trigger] decode(r.nar@[k], r.wide@, r.gh@[k]) == cflat(bs@)[k] by {
                assert(r.nar@[k] == (0i64, k as u64, 0u32, 0u32, 0u32, 1u32));
            }
            assert(r.view() =~= cflat(bs@));
            assert(r.wf());
        }
        r
    }
}

// ------------------------------------------------------------------------------------------------ concatenation

/// The buffers' contributions, in order.
pub open spec fn cflat(bs: Seq<CBuf>) -> Seq<Contrib>
    decreases bs.len(),
{
    if bs.len() == 0 { Seq::empty() } else { cflat(bs.drop_last()) + bs.last().view() }
}

/// Appending a buffer appends its contributions.
pub proof fn lemma_cflat_push(bs: Seq<CBuf>, v: CBuf)
    ensures cflat(bs.push(v)) == cflat(bs) + v.view(),
{
    assert(bs.push(v).drop_last() =~= bs);
}

/// One more buffer of the prefix: `cflat(bs[..i+1]) == cflat(bs[..i]) + bs[i]`.
pub proof fn lemma_cflat_take(bs: Seq<CBuf>, i: int)
    requires 0 <= i < bs.len(),
    ensures cflat(bs.take(i + 1)) == cflat(bs.take(i)) + bs[i].view(),
{
    assert(bs.take(i + 1).drop_last() =~= bs.take(i));
}

/// The concatenation of a prefix is a prefix of the concatenation.
pub proof fn lemma_cflat_prefix(bs: Seq<CBuf>, i: int)
    requires 0 <= i <= bs.len(),
    ensures
        cflat(bs.take(i)).len() <= cflat(bs).len(),
        forall|k: int| 0 <= k < cflat(bs.take(i)).len() ==> #[trigger] cflat(bs.take(i))[k] == cflat(bs)[k],
    decreases bs.len() - i,
{
    if i == bs.len() {
        assert(bs.take(i) =~= bs);
    } else {
        lemma_cflat_prefix(bs, i + 1);
        lemma_cflat_take(bs, i);
        assert forall|k: int| 0 <= k < cflat(bs.take(i)).len() implies #[trigger] cflat(bs.take(i))[k] == cflat(bs)[k] by {
            assert(cflat(bs.take(i + 1))[k] == cflat(bs.take(i))[k]);
        }
    }
}

/// Contribution `j` of buffer `i` sits at `|cflat(bs[..i])| + j`.
pub proof fn lemma_cflat_index(bs: Seq<CBuf>, i: int, j: int)
    requires 0 <= i < bs.len(), 0 <= j < bs[i].view().len(),
    ensures
        cflat(bs.take(i)).len() + j < cflat(bs).len(),
        cflat(bs)[cflat(bs.take(i)).len() + j] == bs[i].view()[j],
{
    lemma_cflat_take(bs, i);
    lemma_cflat_prefix(bs, i + 1);
    let k = cflat(bs.take(i)).len() + j;
    assert(cflat(bs.take(i + 1))[k] == bs[i].view()[j]);
}

/// The whole sequence is its full prefix.
pub proof fn lemma_cflat_all(bs: Seq<CBuf>)
    ensures cflat(bs.take(bs.len() as int)) == cflat(bs),
{
    assert(bs.take(bs.len() as int) =~= bs);
}

} // verus!
