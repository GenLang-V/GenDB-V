//! A table of distinct non-zero `u64` hashes, each with a representative row of two text columns `(a, b)`, used to
//! check that a hash separates the values `(a[row], b[row])` of a set of rows: `add(h, row)` either finds `h` with a
//! representative of the same value, stores `h` with `row`, or reports a collision (`false`: two different values
//! share the hash). `no_unwind`, usable in worker tasks.
//!
//! Layout: slot `s` holds `(hs[s], rows[s])`, empty when `hs[s] == 0`, `mask + 1 + ROOM` slots, linear probing
//! from `h & mask` without wrap-around. Invariant (`dt_wf`): as `pairset`, plus the stored hashes are distinct and
//! the rows are below the row count. Consequence (`lemma_rep_same`): two rows added under the same hash have equal
//! values.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol, TextView};
use crate::agent::common::pairset::ROOM;

verus! {

pub struct DistinctTable {
    pub hs: Vec<u64>,
    pub rows: Vec<u64>,
    pub mask: u64,
}

pub open spec fn bucket1(h: u64, mask: u64) -> int {
    (h & mask) as int
}

pub open spec fn occ(t: DistinctTable, s: int) -> bool {
    0 <= s < t.hs@.len() && t.hs@[s] != 0
}

pub open spec fn dt_wf(t: DistinctTable, n: int) -> bool {
    &&& t.hs@.len() == t.rows@.len()
    &&& t.hs@.len() == t.mask + 1 + ROOM
    &&& forall|s: int| #[trigger] occ(t, s) ==> {
            &&& bucket1(t.hs@[s], t.mask) <= s
            &&& (t.rows@[s] as int) < n
            &&& forall|q: int| bucket1(t.hs@[s], t.mask) <= q < s ==> #[trigger] occ(t, q) && t.hs@[q] != t.hs@[s]
        }
}

/// Stored hashes are distinct: two slots of one hash both sit in its probe run, and the later one sees the earlier.
pub proof fn lemma_distinct(t: DistinctTable, n: int, s1: int, s2: int)
    requires dt_wf(t, n), occ(t, s1), occ(t, s2), t.hs@[s1] == t.hs@[s2],
    ensures s1 == s2,
{
    if s1 < s2 {
        assert(occ(t, s1) && t.hs@[s1] != t.hs@[s2]);
    } else if s2 < s1 {
        assert(occ(t, s2) && t.hs@[s2] != t.hs@[s1]);
    }
}

/// Rows `r1` and `r2` have the same value `(a[r], b[r])`.
pub open spec fn val_eq(a: TextView, b: TextView, r1: int, r2: int) -> bool {
    text_at(a, r1) == text_at(a, r2) && text_at(b, r1) == text_at(b, r2)
}

/// The table holds hash `h` with a representative of row `r`'s value.
pub open spec fn rep(t: DistinctTable, h: u64, a: TextView, b: TextView, r: int) -> bool {
    exists|s: int| #[trigger] occ(t, s) && t.hs@[s] == h && val_eq(a, b, t.rows@[s] as int, r)
}

/// Two rows represented under the same hash have the same value.
pub proof fn lemma_rep_same(t: DistinctTable, n: int, h: u64, a: TextView, b: TextView, r1: int, r2: int)
    requires dt_wf(t, n), rep(t, h, a, b, r1), rep(t, h, a, b, r2),
    ensures val_eq(a, b, r1, r2),
{
    let s1 = choose|s: int| #[trigger] occ(t, s) && t.hs@[s] == h && val_eq(a, b, t.rows@[s] as int, r1);
    let s2 = choose|s: int| #[trigger] occ(t, s) && t.hs@[s] == h && val_eq(a, b, t.rows@[s] as int, r2);
    lemma_distinct(t, n, s1, s2);
}

/// An empty table of `mask + 1 + ROOM` slots (calling thread; allocates).
pub fn new_table(mask: u64, Ghost(n): Ghost<int>) -> (t: DistinctTable)
    requires mask as int + 1 + ROOM <= usize::MAX,
    ensures dt_wf(t, n), t.mask == mask,
{
    let len = mask as usize + 1 + ROOM;
    let t = DistinctTable { hs: vec![0u64; len], rows: vec![0u64; len], mask };
    proof {
        assert forall|s: int| !(#[trigger] occ(t, s)) by {
            if 0 <= s < t.hs@.len() {
                assert(t.hs@[s] == 0);
            }
        }
    }
    t
}

/// Add row `row` under hash `h` (`false`: a different value is stored under `h`, or the probe ran past the last
/// slot). On success the table represents `row` under `h` and keeps every earlier representative.
pub fn add(t: &mut DistinctTable, h: u64, row: u64, a: &TextCol, b: &TextCol, Ghost(n): Ghost<int>) -> (good: bool)
    requires
        dt_wf(*old(t), n), h != 0, (row as int) < n, n <= usize::MAX,
        text_wf(a@, n), text_wf(b@, n),
    ensures
        dt_wf(*final(t), n), final(t).mask == old(t).mask,
        good ==> rep(*final(t), h, a@, b@, row as int),
        good ==> forall|h2: u64, r2: int| #[trigger] rep(*old(t), h2, a@, b@, r2) ==> rep(*final(t), h2, a@, b@, r2),
    no_unwind
{
    let len = t.hs.len();
    assert(t.mask < usize::MAX);
    let mask = t.mask;
    assert(h & mask <= mask) by (bit_vector);
    let bk = (h & mask) as usize;
    let mut pos = bk;
    while pos < len && t.hs[pos] != 0
        invariant
            dt_wf(*t, n), len == t.hs@.len(), mask == t.mask, bk == bucket1(h, mask), bk <= pos <= len,
            text_wf(a@, n), text_wf(b@, n), (row as int) < n, h != 0, n <= usize::MAX,
            forall|q: int| bk <= q < pos ==> #[trigger] occ(*t, q) && t.hs@[q] != h,
        decreases len - pos,
    {
        if t.hs[pos] == h {
            let r = t.rows[pos];
            proof {
                assert(occ(*t, pos as int));
                assert(0 <= a@.offsets[row as int] <= a@.offsets[row + 1] <= a@.bytes.len());
                assert(0 <= a@.offsets[r as int] <= a@.offsets[r + 1] <= a@.bytes.len());
                assert(0 <= b@.offsets[row as int] <= b@.offsets[row + 1] <= b@.bytes.len());
                assert(0 <= b@.offsets[r as int] <= b@.offsets[r + 1] <= b@.bytes.len());
            }
            let same = crate::gendb_entry::work::text_eq(a, r as usize, a, row as usize)
                && crate::gendb_entry::work::text_eq(b, r as usize, b, row as usize);
            proof {
                if same {
                    assert(val_eq(a@, b@, t.rows@[pos as int] as int, row as int));
                }
            }
            return same;
        }
        proof {
            assert(occ(*t, pos as int));
            assert(t.hs@[pos as int] != h);
            assert forall|q: int| bk <= q < pos + 1 implies #[trigger] occ(*t, q) && t.hs@[q] != h by {
                if q < pos as int {
                    assert(occ(*t, q) && t.hs@[q] != h);
                }
            }
        }
        pos = pos + 1;
    }
    if pos == len {
        return false;
    }
    let ghost old_t = *t;
    proof {
        // No stored slot holds `h`: it would sit at or after `bk` with every slot up to it occupied.
        assert forall|s: int| #[trigger] occ(old_t, s) implies old_t.hs@[s] != h by {
            if old_t.hs@[s] == h {
                assert(bk <= s);
                if s >= pos as int {
                    assert(occ(old_t, pos as int));
                }
            }
        }
    }
    t.hs[pos] = h;
    t.rows[pos] = row;
    proof {
        assert(!occ(old_t, pos as int));
        assert forall|s: int| #[trigger] occ(*t, s) implies {
            &&& bucket1(t.hs@[s], t.mask) <= s
            &&& (t.rows@[s] as int) < n
            &&& forall|q: int| bucket1(t.hs@[s], t.mask) <= q < s ==> #[trigger] occ(*t, q) && t.hs@[q] != t.hs@[s]
        } by {
            if s != pos as int {
                assert(occ(old_t, s));
                assert(t.hs@[s] == old_t.hs@[s]);
                assert(t.rows@[s] == old_t.rows@[s]);
                assert(bucket1(t.hs@[s], t.mask) <= s);
                assert((t.rows@[s] as int) < n);
            } else {
                assert(t.hs@[s] == h);
                assert(bucket1(h, t.mask) == bk as int);
                assert(bucket1(t.hs@[s], t.mask) <= s);
                assert(t.rows@[s] == row);
                assert((t.rows@[s] as int) < n);
            }
            assert forall|q: int| bucket1(t.hs@[s], t.mask) <= q < s implies #[trigger] occ(*t, q) && t.hs@[q] != t.hs@[s] by {
                if s == pos as int {
                    assert(bk <= q < pos);
                    assert(occ(old_t, q) && old_t.hs@[q] != h);
                    assert(q != pos as int);
                    assert(t.hs@[q] == old_t.hs@[q]);
                } else {
                    assert(occ(old_t, s));
                    assert(occ(old_t, q) && old_t.hs@[q] != old_t.hs@[s]);
                    assert(q != pos as int);
                    assert(t.hs@[q] == old_t.hs@[q]);
                }
            }
        }
        assert(occ(*t, pos as int));
        assert(val_eq(a@, b@, t.rows@[pos as int] as int, row as int));
        assert forall|h2: u64, r2: int| #[trigger] rep(old_t, h2, a@, b@, r2) implies rep(*t, h2, a@, b@, r2) by {
            let s = choose|s: int| #[trigger] occ(old_t, s) && old_t.hs@[s] == h2 && val_eq(a@, b@, old_t.rows@[s] as int, r2);
            assert(s != pos as int);
            assert(occ(*t, s));
        }
    }
    true
}

} // verus!
