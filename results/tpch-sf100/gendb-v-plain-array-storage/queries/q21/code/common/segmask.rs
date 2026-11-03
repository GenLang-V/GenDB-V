//! The first marked bit of every segment of a `u64`, by one carry-propagating addition: segments start at the set
//! bits of `s` (bit 0 must be one of them), `m` marks bits, and `first_marks(s, m, n)` has, below bit `n < 64`, the
//! lowest marked bit of each segment set (`lemma_first_marks`; it may hold other marked bits too, it never holds an
//! unmarked one).
//!
//! How: `z` holds the unmarked bits that start no segment; a carry injected just above every unmarked segment start
//! runs up through `z` and lands on the segment's first marked bit (or on the next start when there is none); a
//! marked start is its own first mark. A carry never leaves a start (bit of `z` clear), so segments never interact.
use vstd::prelude::*;
use vstd::std_specs::bits::u64_trailing_zeros;
use crate::agent::common::bits64::*;

verus! {

/// The mask of the bits `[a, e)` (for `a <= e < 64`; empty when `a == e`).
pub open spec fn span(a: u64, e: u64) -> u64 { sub(1u64 << e, 1u64 << a) }

/// The bits below `n`.
pub open spec fn below(n: u64) -> u64 { sub(1u64 << n, 1u64) }

/// The unmarked bits below `n` that start no segment.
pub open spec fn gaps(s: u64, m: u64, n: u64) -> u64 { !m & !s & below(n) }

/// A carry just above every unmarked segment start below `n`.
pub open spec fn carries(s: u64, m: u64, n: u64) -> u64 { ((s & !m) << 1u64) & below(n) }

/// The first marked bit of every segment below `n` (see the module header).
pub open spec fn first_marks(s: u64, m: u64, n: u64) -> u64 {
    ((add(gaps(s, m, n), carries(s, m, n)) & !gaps(s, m, n)) | s) & m & below(n)
}

/// The first marked bit `f` of the segment starting at `a` (no start in `(a, f]`, no mark in `[a, f)`) is in
/// `first_marks`.
pub proof fn lemma_first_marks(s: u64, m: u64, n: u64, a: u64, f: u64)
    requires
        a <= f, f < n, n < 64,
        bit(s, a),
        s & span(add(a, 1u64), add(f, 1u64)) == 0,
        m & span(a, f) == 0,
        bit(m, f),
    ensures bit(first_marks(s, m, n), f),
{
    let b = below(n);
    let z = gaps(s, m, n);
    let c = carries(s, m, n);
    let fm = first_marks(s, m, n);
    let ea = add(a, 1u64);
    let ef = add(f, 1u64);
    assert((fm >> f) & 1u64 == 1u64) by (bit_vector)
        requires
            a <= f, f < n, n < 64, ea == a + 1, ef == f + 1,
            b == sub(1u64 << n, 1u64),
            z == !m & !s & b,
            c == ((s & !m) << 1u64) & b,
            fm == ((add(z, c) & !z) | s) & m & b,
            (s >> a) & 1u64 == 1u64,
            s & sub(1u64 << ef, 1u64 << ea) == 0,
            m & sub(1u64 << f, 1u64 << a) == 0,
            (m >> f) & 1u64 == 1u64;
}

/// No bit of `x` in `[a, e)`, in closed form.
pub proof fn lemma_span_clear(x: u64, a: u64, e: u64)
    requires a <= e < 64, forall|u: u64| a <= u < e ==> !#[trigger] bit(x, u),
    ensures x & span(a, e) == 0,
{
    let y = x & span(a, e);
    if a == e {
        assert(sub(1u64 << e, 1u64 << e) == 0) by (bit_vector);
        assert(x & 0u64 == 0) by (bit_vector);
    } else if y != 0 {
        lemma_tz(y);
        let t = u64_trailing_zeros(y) as u64;
        lemma_bit_and(x, span(a, e), t);
        lemma_span(a, e, t);
    }
}

/// The start of the segment of bit `u`: the highest set bit of `s` at or below `u` (0 when there is none).
pub open spec fn seg_start(s: u64, u: u64) -> u64
    decreases u,
{
    if u == 0 || bit(s, u) { u } else { seg_start(s, (u - 1) as u64) }
}

pub proof fn lemma_seg_start(s: u64, u: u64)
    requires bit(s, 0),
    ensures
        seg_start(s, u) <= u,
        bit(s, seg_start(s, u)),
        forall|t: u64| seg_start(s, u) < t <= u ==> !#[trigger] bit(s, t),
        forall|x: u64| x <= u && #[trigger] bit(s, x) ==> x <= seg_start(s, u),
    decreases u,
{
    if !(u == 0 || bit(s, u)) {
        lemma_seg_start(s, (u - 1) as u64);
    }
}

/// The lowest set bit of `m` in `[a, u]` (`u` when there is none below it).
pub open spec fn first_from(m: u64, a: u64, u: u64) -> u64
    decreases u - a,
{
    if a >= u || bit(m, a) { a } else { first_from(m, (a + 1) as u64, u) }
}

pub proof fn lemma_first_from(m: u64, a: u64, u: u64)
    requires a <= u,
    ensures
        a <= first_from(m, a, u) <= u,
        first_from(m, a, u) < u || bit(m, u) ==> bit(m, first_from(m, a, u)),
        forall|t: u64| a <= t < first_from(m, a, u) ==> !#[trigger] bit(m, t),
    decreases u - a,
{
    if !(a >= u || bit(m, a)) {
        lemma_first_from(m, (a + 1) as u64, u);
    }
}

/// The first marked bit of the segment of a marked bit `u < n`: it is in `first_marks`, it is marked, and no segment
/// starts in `(f, u]` (`f` and `u` lie in one segment, which starts at or after every start `x <= u`).
pub proof fn lemma_mark_covered(s: u64, m: u64, n: u64, u: u64)
    requires bit(s, 0), n < 64, u < n, bit(m, u),
    ensures ({
        let a = seg_start(s, u);
        let f = first_from(m, a, u);
        &&& a <= f <= u
        &&& bit(first_marks(s, m, n), f)
        &&& bit(m, f)
        &&& forall|t: u64| f < t <= u ==> !#[trigger] bit(s, t)
        &&& forall|x: u64| x <= u && #[trigger] bit(s, x) ==> x <= a
    }),
{
    let a = seg_start(s, u);
    lemma_seg_start(s, u);
    let f = first_from(m, a, u);
    lemma_first_from(m, a, u);
    assert(add(a, 1u64) == a + 1 && add(f, 1u64) == f + 1) by (bit_vector) requires a <= f, f <= u, u < 64;
    lemma_span_clear(s, (a + 1) as u64, (f + 1) as u64);
    lemma_span_clear(m, a, f);
    lemma_first_marks(s, m, n, a, f);
}

/// Clearing every bit below `e` by `x & !(2^e - 1)`.
pub proof fn lemma_clear_below(x: u64, e: u64, u: u64)
    requires e < 64, u < 64,
    ensures (1u64 << e) >= 1, bit(x & !sub(1u64 << e, 1u64), u) == (bit(x, u) && u >= e),
{
    assert((1u64 << e) >= 1 && ((((x & !sub(1u64 << e, 1u64)) >> u) & 1u64 == 1u64) <==> ((x >> u) & 1u64 == 1u64 && u >= e)))
        by (bit_vector) requires e < 64, u < 64;
}

/// Clearing bit `t` by `x & !(1 << t)`.
pub proof fn lemma_clear_bit(x: u64, t: u64, u: u64)
    requires t < 64, u < 64,
    ensures bit(x & !(1u64 << t), u) == (bit(x, u) && u != t),
{
    assert((((x & !(1u64 << t)) >> u) & 1u64 == 1u64) <==> ((x >> u) & 1u64 == 1u64 && u != t))
        by (bit_vector) requires t < 64, u < 64;
}

} // verus!
