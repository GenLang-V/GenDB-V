//! Concatenation of task outputs in task order (`flatten`, `concat`; a single output is moved, not copied) and the
//! position facts of the outputs of `k` equal cuts of `0..n` (`dictmap::cut`): output `t` covers positions
//! `[cut(n, k, t), cut(n, k, t + 1))`, so position `c` of the concatenation is position `c - cut(n, k, t)` of output `t`.
use vstd::prelude::*;
use super::dictmap::{cut, lemma_cut_mono};

verus! {

/// The elements of the vectors, in order.
pub open spec fn flatten<T>(vs: Seq<Vec<T>>) -> Seq<T>
    decreases vs.len(),
{
    if vs.len() == 0 { Seq::empty() } else { flatten(vs.drop_last()) + vs.last()@ }
}

/// Concatenation of `outs` in order; one vector is returned as it is.
pub fn concat<T>(outs: Vec<Vec<T>>) -> (r: Vec<T>)
    ensures r@ == flatten(outs@),
{
    let ghost orig = outs@;
    let mut outs = outs;
    if outs.len() == 1 {
        proof {
            assert(orig.drop_last() =~= Seq::<Vec<T>>::empty());
            assert(flatten(orig.drop_last()) =~= Seq::<T>::empty());
            assert(flatten(orig) == flatten(orig.drop_last()) + orig.last()@);
            assert(flatten(orig) =~= orig[0]@);
        }
        let o = outs.remove(0);
        return o;
    }
    let mut res: Vec<T> = Vec::new();
    proof {
        assert(orig.subrange(0, 0) =~= Seq::<Vec<T>>::empty());
    }
    let ghost done: int = 0;
    while outs.len() > 0
        invariant
            0 <= done <= orig.len(),
            outs@ == orig.subrange(done, orig.len() as int),
            res@ == flatten(orig.subrange(0, done)),
        decreases outs.len(),
    {
        let mut o = outs.remove(0);
        proof {
            assert(o == orig[done]);
            assert(orig.subrange(0, done + 1).drop_last() =~= orig.subrange(0, done));
            assert(orig.subrange(0, done + 1).last() == orig[done]);
        }
        res.append(&mut o);
        proof {
            done = done + 1;
            assert(outs@ =~= orig.subrange(done, orig.len() as int));
        }
    }
    proof {
        assert(orig.subrange(0, done) =~= orig);
    }
    res
}

/// `flatten` of the outputs of equal cuts that each satisfy `ok` at their positions satisfies `ok` everywhere.
pub proof fn lemma_flatten_cuts<T>(vs: Seq<Vec<T>>, n: int, k: int, ok: spec_fn(int, T) -> bool)
    requires
        n >= 0, k >= 1, vs.len() <= k,
        forall|t: int| 0 <= t < vs.len() ==> (#[trigger] vs[t])@.len() == cut(n, k, t + 1) - cut(n, k, t),
        forall|t: int, c: int| 0 <= t < vs.len() && cut(n, k, t) <= c < cut(n, k, t + 1)
            ==> ok(c, #[trigger] vs[t]@[c - cut(n, k, t)]),
    ensures
        flatten(vs).len() == cut(n, k, vs.len() as int),
        forall|c: int| 0 <= c < flatten(vs).len() ==> ok(c, #[trigger] flatten(vs)[c]),
    decreases vs.len(),
{
    if vs.len() == 0 {
        assert(cut(n, k, 0) == 0) by {
            assert(n * 0 == 0);
        }
    } else {
        let vi = vs.drop_last();
        let t = vs.len() - 1;
        assert forall|u: int| 0 <= u < vi.len() implies (#[trigger] vi[u])@.len() == cut(n, k, u + 1) - cut(n, k, u) by {
            assert(vi[u] == vs[u]);
        }
        assert forall|u: int, c: int| 0 <= u < vi.len() && cut(n, k, u) <= c < cut(n, k, u + 1)
            implies ok(c, #[trigger] vi[u]@[c - cut(n, k, u)]) by {
            assert(vi[u] == vs[u]);
        }
        lemma_flatten_cuts(vi, n, k, ok);
        lemma_cut_mono(n, k, t);
        let f = flatten(vs);
        let fi = flatten(vi);
        assert(f == fi + vs[t]@);
        assert forall|c: int| 0 <= c < f.len() implies ok(c, #[trigger] f[c]) by {
            if c >= fi.len() {
                assert(f[c] == vs[t]@[c - cut(n, k, t)]);
            } else {
                assert(f[c] == fi[c]);
            }
        }
    }
}

} // verus!
