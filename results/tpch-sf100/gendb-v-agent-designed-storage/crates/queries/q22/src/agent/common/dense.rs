//! Dense integer sequences: a strictly increasing integer sequence `f(0) < f(1) < .. < f(n - 1)` whose last
//! element is `f(0) + n - 1` takes every value in between, `f(i) == f(0) + i` (`lemma_dense`). Used to read a
//! sorted unique key column as `first key + row`: then no key needs to be read per row.
use vstd::prelude::*;

verus! {

/// `f` increases strictly over `[0, n)`.
pub open spec fn strictly_increasing(f: spec_fn(int) -> int, n: int) -> bool {
    forall|i: int| 0 <= i < n - 1 ==> #[trigger] f(i) < f(i + 1)
}

/// `f(i) >= f(0) + i`.
proof fn lemma_lower(f: spec_fn(int) -> int, n: int, i: int)
    requires strictly_increasing(f, n), 0 <= i < n,
    ensures f(i) >= f(0) + i,
    decreases i,
{
    if i > 0 {
        lemma_lower(f, n, i - 1);
        assert(f(i - 1) < f(i));
    }
}

/// `f(i) <= f(n - 1) - (n - 1 - i)`.
proof fn lemma_upper(f: spec_fn(int) -> int, n: int, i: int)
    requires strictly_increasing(f, n), 0 <= i < n,
    ensures f(i) <= f(n - 1) - (n - 1 - i),
    decreases n - i,
{
    if i < n - 1 {
        lemma_upper(f, n, i + 1);
        assert(f(i) < f(i + 1));
    }
}

/// A strictly increasing sequence of `n` integers spanning exactly `n - 1` is `f(0), f(0) + 1, ..`.
pub proof fn lemma_dense(f: spec_fn(int) -> int, n: int)
    requires
        n >= 1,
        strictly_increasing(f, n),
        f(n - 1) == f(0) + n - 1,
    ensures
        forall|i: int| 0 <= i < n ==> #[trigger] f(i) == f(0) + i,
{
    assert forall|i: int| 0 <= i < n implies #[trigger] f(i) == f(0) + i by {
        lemma_lower(f, n, i);
        lemma_upper(f, n, i);
    }
}

} // verus!
