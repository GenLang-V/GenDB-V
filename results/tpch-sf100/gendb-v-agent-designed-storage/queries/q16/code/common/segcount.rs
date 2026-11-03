//! Distinct count of a segment: the number of distinct values of `s[a .. b)` (each below `n`) that an exclusion
//! bitmap does not mark, with a scratch bitmap that is empty before and after (no allocation; usable in worker bodies).
//!
//! The value of an element is its low bits `s[k] & mask` (`mask = u32::MAX` for the element itself; a field mask for
//! packed entries). The first pass marks every kept value in the scratch bitmap (`common::marks::mark_new`) and counts first sightings;
//! the second pass clears the word of every value of the segment, which empties the scratch again.
use vstd::prelude::*;
use super::marks::*;

verus! {

/// The value of element `v`.
pub open spec fn mval(v: u32, mask: u32) -> int {
    (v & mask) as int
}

/// Some position of `s[a .. b)` holds value `x`.
pub open spec fn has_val(s: Seq<u32>, a: int, b: int, mask: u32, x: int) -> bool {
    exists|k: int| a <= k < b && #[trigger] mval(s[k], mask) == x
}

/// The distinct values of `s[a .. b)` below `n` that `ex` does not mark.
pub open spec fn kept(s: Seq<u32>, a: int, b: int, mask: u32, ex: Seq<u64>, n: int) -> Set<int> {
    Set::range(0, n).filter(|x: int| has_val(s, a, b, mask, x) && !bit_at(ex, x))
}

/// A set of values below `n` has at most `n` elements.
proof fn lemma_kept_bound(st: Set<int>, n: int)
    requires n >= 0, forall|x: int| #[trigger] st.contains(x) ==> 0 <= x < n,
    ensures st.len() <= n,
{
    vstd::set_lib::lemma_int_range(0, n);
    assert(st.subset_of(Set::range(0int, n)));
    vstd::set_lib::lemma_len_subset(st, Set::range(0int, n));
}

/// Position `k` adds value `s[k]` (when kept) to the kept values of `s[a .. k)`.
proof fn lemma_kept_step(s: Seq<u32>, a: int, k: int, mask: u32, ex: Seq<u64>, n: int)
    requires a <= k < s.len(), mval(s[k], mask) < n,
    ensures
        kept(s, a, k + 1, mask, ex, n) == if bit_at(ex, mval(s[k], mask)) { kept(s, a, k, mask, ex, n) }
            else { kept(s, a, k, mask, ex, n).insert(mval(s[k], mask)) },
{
    let x = mval(s[k], mask);
    let k1 = kept(s, a, k + 1, mask, ex, n);
    let k0 = kept(s, a, k, mask, ex, n);
    let want = if bit_at(ex, x) { k0 } else { k0.insert(x) };
    assert forall|y: int| #[trigger] k1.contains(y) == want.contains(y) by {
        if has_val(s, a, k + 1, mask, y) && !has_val(s, a, k, mask, y) {
            let p = choose|p: int| a <= p < k + 1 && #[trigger] mval(s[p], mask) == y;
            assert(p == k);
        }
        if has_val(s, a, k, mask, y) {
            let p = choose|p: int| a <= p < k && #[trigger] mval(s[p], mask) == y;
            assert(a <= p < k + 1);
        }
        if y == x {
            assert(has_val(s, a, k + 1, mask, y));
        }
    }
    assert(k1 =~= want);
}

/// The number of distinct values of `s[a .. b)` that `ex` does not mark; `marks` is empty before and after.
pub fn count_seg(s: &Vec<u32>, a: usize, b: usize, mask: u32, ex: &Vec<u64>, marks: &mut Vec<u64>, n: usize) -> (c: u64)
    requires
        a <= b <= s@.len(),
        forall|k: int| a <= k < b ==> mval(#[trigger] s@[k], mask) < n,
        n <= 64 * ex@.len(),
        n <= 64 * old(marks)@.len(),
        holds(old(marks)@, Set::empty()),
    ensures
        c as int == kept(s@, a as int, b as int, mask, ex@, n as int).len(),
        final(marks)@.len() == old(marks)@.len(),
        holds(final(marks)@, Set::empty()),
    no_unwind
{
    let ghost sv = s@;
    let ghost mut seen: Set<int> = Set::empty();
    let mut c: u64 = 0;
    proof {
        assert(seen =~= kept(sv, a as int, a as int, mask, ex@, n as int));
    }
    let mut k = a;
    while k < b
        invariant
            sv == s@,
            a <= k <= b <= s@.len(),
            forall|k2: int| a <= k2 < b ==> mval(#[trigger] s@[k2], mask) < n,
            n <= 64 * ex@.len(),
            n <= 64 * marks@.len(),
            marks@.len() == old(marks)@.len(),
            seen == kept(sv, a as int, k as int, mask, ex@, n as int),
            holds(marks@, seen),
            c as int == seen.len(),
            seen.len() <= n,
        decreases b - k,
    {
        let x = (s[k] & mask) as usize;
        proof {
            lemma_kept_step(sv, a as int, k as int, mask, ex@, n as int);
        }
        if !get_bit(ex, x) {
            let fresh = mark_new(marks, x, Ghost(seen));
            proof {
                vstd::set::lemma_set_insert_len(seen, x as int);
                lemma_kept_bound(seen.insert(x as int), n as int);
                seen = seen.insert(x as int);
            }
            if fresh {
                c = c + 1;
            }
        }
        k = k + 1;
    }
    // Clear the word of every value of the segment: every marked value is one of them.
    let ghost all = seen;
    let ghost mut left: Set<int> = seen;
    let mut k = a;
    while k < b
        invariant
            sv == s@,
            a <= k <= b <= s@.len(),
            forall|k2: int| a <= k2 < b ==> mval(#[trigger] s@[k2], mask) < n,
            n <= 64 * marks@.len(),
            marks@.len() == old(marks)@.len(),
            all == kept(sv, a as int, b as int, mask, ex@, n as int),
            holds(marks@, left),
            forall|x: int| #[trigger] left.contains(x) ==> all.contains(x) && !has_val(sv, a as int, k as int, mask, x),
        decreases b - k,
    {
        let x = (s[k] & mask) as usize;
        clear_word(marks, x, Ghost(left));
        proof {
            let l2 = left.filter(|y: int| y / 64 != (x as int) / 64);
            assert forall|y: int| #[trigger] l2.contains(y) implies all.contains(y) && !has_val(sv, a as int, k + 1, mask, y) by {
                assert(left.contains(y));
                assert(y != x as int);
                if has_val(sv, a as int, k + 1, mask, y) {
                    let p = choose|p: int| a <= p < k + 1 && #[trigger] mval(sv[p], mask) == y;
                    assert(p != k as int);
                    assert(has_val(sv, a as int, k as int, mask, y));
                }
            }
            left = l2;
        }
        k = k + 1;
    }
    proof {
        assert(left =~= Set::<int>::empty()) by {
            assert forall|x: int| !left.contains(x) by {
                if left.contains(x) {
                    assert(all.contains(x));
                    assert(has_val(sv, a as int, b as int, mask, x));
                }
            }
        }
    }
    c
}

} // verus!
