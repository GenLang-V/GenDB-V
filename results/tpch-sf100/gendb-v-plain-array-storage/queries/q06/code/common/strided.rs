//! Strided (column-major) visitation of a list: the positions `0..len` of a list `s` read as a grid of `l` columns,
//! column `c` being the positions `c, c + l, c + 2l, ...` (`col`), visited one column after the other (`visit`).
//! A sum over the visited list equals the sum over the list (`lemma_visit_sum`): visiting order is free for sums.
//! Also: a sum over a filtered list is the sum of the guarded terms (`lemma_filter_sum`), and sums over
//! concatenations split (`lemma_sum_concat`).
//!
//! Proof of `lemma_visit_sum`: the column sums `csum(j)` satisfy `csum(j) = h'(j) + csum(j + l)` (`h'` the position
//! terms, zero beyond the list); so `l` consecutive column sums starting at `j` are the `l` terms from `j` plus the
//! next `l` column sums, and by induction they are the position terms from `j` to the end (`lemma_window`).
use vstd::prelude::*;
use crate::agent::common::selection::*;

verus! {

/// The positions `j, j + l, j + 2l, ...` of `s` (below its length), as their elements in order.
pub open spec fn col(s: Seq<int>, l: int, j: int) -> Seq<int>
    decreases if j < s.len() { s.len() - j } else { 0 },
{
    if j < 0 || l < 1 || j >= s.len() {
        Seq::empty()
    } else {
        seq![s[j]] + col(s, l, j + l)
    }
}

/// Columns `0..c` of `s` (column width `l`), concatenated.
pub open spec fn visit(s: Seq<int>, l: int, c: int) -> Seq<int>
    decreases c,
{
    if c <= 0 { Seq::empty() } else { visit(s, l, c - 1) + col(s, l, c - 1) }
}

/// The term of each position of `s`: `g` of its element (0 outside the list).
pub open spec fn pos_term(s: Seq<int>, g: spec_fn(int) -> int) -> spec_fn(int) -> int {
    |x: int| if 0 <= x < s.len() { g(s[x]) } else { 0 }
}

/// Sum of `h` over the positions `j, j + l, ...` below `k`.
pub open spec fn csum(h: spec_fn(int) -> int, k: int, l: int, j: int) -> int
    decreases if j < k { k - j } else { 0 },
{
    if j < 0 || l < 1 || j >= k { 0 } else { h(j) + csum(h, k, l, j + l) }
}

pub open spec fn csum_fn(h: spec_fn(int) -> int, k: int, l: int) -> spec_fn(int) -> int {
    |j: int| csum(h, k, l, j)
}

/// `h` shifted by `d`.
pub open spec fn shifted(h: spec_fn(int) -> int, d: int) -> spec_fn(int) -> int {
    |x: int| h(x + d)
}

/// Pointwise sum of two term functions.
pub open spec fn plus(f: spec_fn(int) -> int, g: spec_fn(int) -> int) -> spec_fn(int) -> int {
    |x: int| f(x) + g(x)
}

/// One more element at the front of a summed list.
pub proof fn lemma_sum_prepend(x: int, t: Seq<int>, g: spec_fn(int) -> int)
    ensures seq_sum(seq![x] + t, g) == g(x) + seq_sum(t, g),
    decreases t.len(),
{
    let u = seq![x] + t;
    if t.len() == 0 {
        assert(u.drop_last() =~= Seq::<int>::empty());
        assert(u.last() == x);
        assert(seq_sum(Seq::<int>::empty(), g) == 0);
        assert(seq_sum(t, g) == 0);
    } else {
        lemma_sum_prepend(x, t.drop_last(), g);
        assert(u.drop_last() =~= seq![x] + t.drop_last());
        assert(u.last() == t.last());
    }
}

/// Sums over a concatenation split.
pub proof fn lemma_sum_concat(a: Seq<int>, b: Seq<int>, g: spec_fn(int) -> int)
    ensures seq_sum(a + b, g) == seq_sum(a, g) + seq_sum(b, g),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_sum_concat(a, b.drop_last(), g);
        assert((a + b).drop_last() =~= a + b.drop_last());
    }
}

/// A sum over a filtered list is the sum of the guarded terms over the list.
pub proof fn lemma_filter_sum(t: Seq<int>, q: spec_fn(int) -> bool, f: spec_fn(int) -> int)
    ensures seq_sum(seq_filter(t, q), f) == seq_sum(t, guard(q, f)),
    decreases t.len(),
{
    if t.len() > 0 {
        lemma_filter_sum(t.drop_last(), q, f);
        let u = seq_filter(t.drop_last(), q);
        if q(t.last()) {
            lemma_seq_sum_push(u, t.last(), f);
        }
    }
}

/// A list sum is the range sum of its position terms.
pub proof fn lemma_seq_sum_positions(s: Seq<int>, g: spec_fn(int) -> int)
    ensures seq_sum(s, g) == range_sum(0, s.len() as int, pos_term(s, g)),
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        lemma_seq_sum_positions(t, g);
        lemma_range_sum_ext(0, t.len() as int, pos_term(t, g), pos_term(s, g));
    }
}

/// The sum over column `j` is the column sum of the position terms.
pub proof fn lemma_col_sum(s: Seq<int>, l: int, j: int, g: spec_fn(int) -> int)
    requires l >= 1, j >= 0,
    ensures seq_sum(col(s, l, j), g) == csum(pos_term(s, g), s.len() as int, l, j),
    decreases if j < s.len() { s.len() - j } else { 0 },
{
    if j < s.len() {
        lemma_col_sum(s, l, j + l, g);
        lemma_sum_prepend(s[j], col(s, l, j + l), g);
    }
}

/// Range sums split at a middle point.
pub proof fn lemma_range_sum_split(a: int, b: int, c: int, f: spec_fn(int) -> int)
    requires a <= b <= c,
    ensures range_sum(a, c, f) == range_sum(a, b, f) + range_sum(b, c, f),
    decreases c - b,
{
    if c > b {
        lemma_range_sum_split(a, b, c - 1, f);
    }
}

/// A range sum of terms that are zero on the range is zero.
pub proof fn lemma_range_sum_zero(a: int, b: int, f: spec_fn(int) -> int)
    requires forall|x: int| a <= x < b ==> #[trigger] f(x) == 0,
    ensures range_sum(a, b, f) == 0,
    decreases b - a,
{
    if b > a {
        lemma_range_sum_zero(a, b - 1, f);
    }
}

/// Range sums are additive in the terms.
pub proof fn lemma_range_sum_plus(a: int, b: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    ensures range_sum(a, b, plus(f, g)) == range_sum(a, b, f) + range_sum(a, b, g),
    decreases b - a,
{
    if b > a {
        lemma_range_sum_plus(a, b - 1, f, g);
    }
}

/// A range sum of shifted terms is the range sum over the shifted range.
pub proof fn lemma_range_sum_shift(a: int, b: int, d: int, f: spec_fn(int) -> int)
    ensures range_sum(a, b, shifted(f, d)) == range_sum(a + d, b + d, f),
    decreases b - a,
{
    if b > a {
        lemma_range_sum_shift(a, b - 1, d, f);
    }
}

/// `l` consecutive column sums from `j` are the position terms from `j` to the end `k`.
pub proof fn lemma_window(h: spec_fn(int) -> int, k: int, l: int, j: int)
    requires l >= 1, j >= 0, forall|x: int| x >= k ==> #[trigger] h(x) == 0,
    ensures range_sum(j, j + l, csum_fn(h, k, l)) == range_sum(j, if j < k { k } else { j }, h),
    decreases if j < k { k - j } else { 0 },
{
    let cs = csum_fn(h, k, l);
    if j >= k {
        assert forall|x: int| j <= x < j + l implies #[trigger] cs(x) == 0 by {}
        lemma_range_sum_zero(j, j + l, cs);
    } else {
        // Every column sum is its first term plus the column sum one row further: csum(x) = h(x) + csum(x + l).
        assert forall|x: int| j <= x < j + l implies #[trigger] cs(x) == plus(h, shifted(cs, l))(x) by {
            if x >= k {
                assert(cs(x + l) == 0);
            }
        }
        lemma_range_sum_ext(j, j + l, cs, plus(h, shifted(cs, l)));
        lemma_range_sum_plus(j, j + l, h, shifted(cs, l));
        lemma_range_sum_shift(j, j + l, l, cs);
        lemma_window(h, k, l, j + l);
        if j + l <= k {
            lemma_range_sum_split(j, j + l, k, h);
        } else {
            lemma_range_sum_split(j, k, j + l, h);
            lemma_range_sum_zero(k, j + l, h);
        }
    }
}

/// The sum over the first `c` visited columns is the range sum of the first `c` column sums.
pub proof fn lemma_visit_prefix_sum(s: Seq<int>, l: int, c: int, g: spec_fn(int) -> int)
    requires l >= 1, c >= 0,
    ensures seq_sum(visit(s, l, c), g) == range_sum(0, c, csum_fn(pos_term(s, g), s.len() as int, l)),
    decreases c,
{
    if c > 0 {
        lemma_visit_prefix_sum(s, l, c - 1, g);
        lemma_sum_concat(visit(s, l, c - 1), col(s, l, c - 1), g);
        lemma_col_sum(s, l, c - 1, g);
    }
}

/// Visiting all `l` columns sums to the sum over the list.
pub proof fn lemma_visit_sum(s: Seq<int>, l: int, g: spec_fn(int) -> int)
    requires l >= 1,
    ensures seq_sum(visit(s, l, l), g) == seq_sum(s, g),
{
    let h = pos_term(s, g);
    let k = s.len() as int;
    lemma_visit_prefix_sum(s, l, l, g);
    lemma_window(h, k, l, 0);
    lemma_seq_sum_positions(s, g);
}

/// The constant term 1 (sums of it count).
pub open spec fn one() -> spec_fn(int) -> int {
    |x: int| 1int
}

/// Summing 1 over a list gives its length.
pub proof fn lemma_sum_one(t: Seq<int>)
    ensures seq_sum(t, one()) == t.len(),
    decreases t.len(),
{
    if t.len() > 0 {
        lemma_sum_one(t.drop_last());
    }
}

/// Visiting all columns lists as many elements as the list has.
pub proof fn lemma_visit_len(s: Seq<int>, l: int)
    requires l >= 1,
    ensures visit(s, l, l).len() == s.len(),
{
    lemma_visit_sum(s, l, one());
    lemma_sum_one(visit(s, l, l));
    lemma_sum_one(s);
}

/// Visiting more columns lists at least as many elements.
pub proof fn lemma_visit_mono(s: Seq<int>, l: int, c: int, d: int)
    requires 0 <= c <= d,
    ensures visit(s, l, c).len() <= visit(s, l, d).len(),
    decreases d - c,
{
    if d > c {
        lemma_visit_mono(s, l, c, d - 1);
    }
}

/// A filter is no longer than its input.
pub proof fn lemma_filter_len(t: Seq<int>, q: spec_fn(int) -> bool)
    ensures seq_filter(t, q).len() <= t.len(),
    decreases t.len(),
{
    if t.len() > 0 {
        lemma_filter_len(t.drop_last(), q);
    }
}

} // verus!
