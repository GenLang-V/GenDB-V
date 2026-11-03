//! The NOT IN subquery's supplier rows: those whose `s_comment LIKE '%Customer%Complaints%'`.
//!
//! The pattern's words are ASCII, so a comment matches exactly when its bytes hold `Customer` and, after it,
//! `Complaints`, each followed by no UTF-8 continuation byte (else the word's last character would be longer):
//! `common::likebytes::lemma_two_words_fwd` and `lemma_two_words_back`, here `lemma_cc_exact`. Parallel tasks
//! (`SuppTask`, run inside the pair tasks of `kernel`) decide this byte test for supplier row ranges (a branch-free
//! scan for an upper-case `C`, then `byte_hit`) and list the matching rows; `round::excl_of` turns the lists into a
//! bitmap.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::gendb_entry::parallel::WorkerTask;
use super::tables::*;
use super::sqlq::{cc_bytes, esc, cc_true, like_res, like_true, lemma_like_shape};
use super::common::likebytes::*;

verus! {

/// `Customer`.
pub open spec fn cust() -> Seq<u8> {
    seq![67u8, 117u8, 115u8, 116u8, 111u8, 109u8, 101u8, 114u8]
}

/// `Complaints`.
pub open spec fn comp() -> Seq<u8> {
    seq![67u8, 111u8, 109u8, 112u8, 108u8, 97u8, 105u8, 110u8, 116u8, 115u8]
}

/// The comment of supplier row `r`.
pub open spec fn comment(s: SCols, r: int) -> Seq<u8> {
    txt(s.comm_o@, s.comm_y@, r)
}

/// Supplier row `r`'s comment matches the subquery's pattern.
pub open spec fn cc_row(s: SCols, r: int) -> bool {
    cc_true(Val::Text(comment(s, r)))
}

/// The comment parts of the supplier rows are well formed.
pub open spec fn comm_ok(s: SCols) -> bool {
    &&& txt_ok(s.comm_o@, s.comm_y@, s.n as int)
    &&& s.comm_len == s.comm_y@.len()
}

/// `Customer` at `p`, followed by no continuation byte.
pub open spec fn cust_at(y: Seq<u8>, p: int) -> bool {
    occurs_at(y, cust(), p) && p + 8 < y.len() && !is_cont(y[p + 8])
}

/// `Complaints` at `p`, followed by the end `b` or by no continuation byte.
pub open spec fn comp_at(y: Seq<u8>, b: int, p: int) -> bool {
    occurs_at(y, comp(), p) && (p + 10 == b || !is_cont(y[p + 10]))
}

/// `y[a .. b]` holds `Customer` at `p1` and `Complaints` at `p2 >= p1 + 8`, each ending a character.
pub open spec fn hit_in(y: Seq<u8>, a: int, b: int) -> bool {
    exists|p1: int, p2: int| a <= p1 && p1 + 8 <= p2 && p2 + 10 <= b
        && #[trigger] cust_at(y, p1) && #[trigger] comp_at(y, b, p2)
}

/// The subquery's pattern is `%Customer%Complaints%`.
proof fn lemma_cc_words()
    ensures
        cc_bytes() == two_words(cust(), comp()),
        word_ok(cust(), 92u8), word_ok(comp(), 92u8),
{
    assert(cc_bytes() =~= two_words(cust(), comp()));
    assert(word_ok(cust(), 92u8)) by {
        assert forall|i: int| 0 <= i < cust().len() implies (#[trigger] cust()[i]) < 0x80u8 by {}
        assert forall|i: int| 0 <= i < cust().len() implies #[trigger] cust()[i] != 0x25u8 && cust()[i] != 0x5Fu8
            && cust()[i] != 92u8 by {}
    }
    assert(word_ok(comp(), 92u8)) by {
        assert forall|i: int| 0 <= i < comp().len() implies (#[trigger] comp()[i]) < 0x80u8 by {}
        assert forall|i: int| 0 <= i < comp().len() implies #[trigger] comp()[i] != 0x25u8 && comp()[i] != 0x5Fu8
            && comp()[i] != 92u8 by {}
    }
}

/// A comment matches exactly when its bytes pass the byte test.
pub proof fn lemma_cc_exact(s: SCols, r: int)
    requires comm_ok(s), 0 <= r < s.n,
    ensures cc_row(s, r) == hit_in(s.comm_y@, s.comm_o@[r] as int, s.comm_o@[r + 1] as int),
{
    let (a, b) = (s.comm_o@[r] as int, s.comm_o@[r + 1] as int);
    assert(a <= b && b <= s.comm_y@.len());
    let y = s.comm_y@;
    let sb = comment(s, r);
    assert(sb == y.subrange(a, b));
    lemma_like_shape(sb, cc_bytes());
    lemma_cc_words();
    assert(esc() == seq![92u8]);
    if cc_row(s, r) {
        lemma_two_words_fwd(sb, cust(), comp(), 92u8);
        let (q1, q2) = choose|q1: int, q2: int| q1 + cust().len() <= q2 && #[trigger] proper_at(sb, cust(), q1)
            && #[trigger] proper_at(sb, comp(), q2);
        assert(cust_at(y, a + q1)) by {
            assert forall|m: int| 0 <= m < cust().len() implies #[trigger] y[(a + q1) + m] == cust()[m] by {
                assert(sb[q1 + m] == y[a + (q1 + m)]);
            }
            assert(sb[q1 + 8] == y[a + q1 + 8]);
        }
        assert(comp_at(y, b, a + q2)) by {
            assert forall|m: int| 0 <= m < comp().len() implies #[trigger] y[(a + q2) + m] == comp()[m] by {
                assert(sb[q2 + m] == y[a + (q2 + m)]);
            }
            if q2 + 10 < sb.len() {
                assert(sb[q2 + 10] == y[a + q2 + 10]);
            }
        }
        assert(hit_in(y, a, b));
    }
    if hit_in(y, a, b) {
        let (p1, p2) = choose|p1: int, p2: int| a <= p1 && p1 + 8 <= p2 && p2 + 10 <= b
            && #[trigger] cust_at(y, p1) && #[trigger] comp_at(y, b, p2);
        assert(proper_at(sb, cust(), p1 - a)) by {
            assert forall|m: int| 0 <= m < cust().len() implies #[trigger] sb[(p1 - a) + m] == cust()[m] by {
                assert(y[p1 + m] == cust()[m]);
            }
            assert(sb[p1 - a + 8] == y[p1 + 8]);
        }
        assert(proper_at(sb, comp(), p2 - a)) by {
            assert forall|m: int| 0 <= m < comp().len() implies #[trigger] sb[(p2 - a) + m] == comp()[m] by {
                assert(y[p2 + m] == comp()[m]);
            }
            if p2 + 10 < b {
                assert(sb[p2 - a + 10] == y[p2 + 10]);
            }
        }
        assert(proper_two(sb, cust(), comp()));
        lemma_two_words_back(sb, cust(), comp(), 92u8);
    }
}

/// `y[p .. p + 8] == "Customer"`.
fn at_customer(y: &[u8], p: usize, Ghost(n): Ghost<int>) -> (r: bool)
    requires p + 8 <= n, n <= y@.len(),
    ensures r == occurs_at(y@, cust(), p as int),
    no_unwind
{
    let r = y[p] == 67u8 && y[p + 1] == 117u8 && y[p + 2] == 115u8 && y[p + 3] == 116u8 && y[p + 4] == 111u8
        && y[p + 5] == 109u8 && y[p + 6] == 101u8 && y[p + 7] == 114u8;
    proof {
        if r {
            assert forall|m: int| 0 <= m < cust().len() implies #[trigger] y@[p + m] == cust()[m] by {}
        }
        if occurs_at(y@, cust(), p as int) {
            assert(y@[p + 0] == cust()[0] && y@[p + 1] == cust()[1] && y@[p + 2] == cust()[2] && y@[p + 3] == cust()[3]);
            assert(y@[p + 4] == cust()[4] && y@[p + 5] == cust()[5] && y@[p + 6] == cust()[6] && y@[p + 7] == cust()[7]);
        }
    }
    r
}

/// `y[p .. p + 10] == "Complaints"`.
fn at_complaints(y: &[u8], p: usize, Ghost(n): Ghost<int>) -> (r: bool)
    requires p + 10 <= n, n <= y@.len(),
    ensures r == occurs_at(y@, comp(), p as int),
    no_unwind
{
    let r = y[p] == 67u8 && y[p + 1] == 111u8 && y[p + 2] == 109u8 && y[p + 3] == 112u8 && y[p + 4] == 108u8
        && y[p + 5] == 97u8 && y[p + 6] == 105u8 && y[p + 7] == 110u8 && y[p + 8] == 116u8 && y[p + 9] == 115u8;
    proof {
        if r {
            assert forall|m: int| 0 <= m < comp().len() implies #[trigger] y@[p + m] == comp()[m] by {}
        }
        if occurs_at(y@, comp(), p as int) {
            assert(y@[p + 0] == comp()[0] && y@[p + 1] == comp()[1] && y@[p + 2] == comp()[2] && y@[p + 3] == comp()[3]);
            assert(y@[p + 4] == comp()[4] && y@[p + 5] == comp()[5] && y@[p + 6] == comp()[6] && y@[p + 7] == comp()[7]);
            assert(y@[p + 8] == comp()[8] && y@[p + 9] == comp()[9]);
        }
    }
    r
}

/// Whether `y[a .. b]` holds `Customer` and, after it, `Complaints`, each ending a character (`hit_in`).
pub fn byte_hit(y: &[u8], a: usize, b: usize, Ghost(n): Ghost<int>) -> (r: bool)
    requires a <= b, b <= n, n <= y@.len(),
    ensures r == hit_in(y@, a as int, b as int),
    no_unwind
{
    if b - a < 18 {
        proof {
            if hit_in(y@, a as int, b as int) {
                let (p1, p2) = choose|p1: int, p2: int| a <= p1 && p1 + 8 <= p2 && p2 + 10 <= b
                    && #[trigger] cust_at(y@, p1) && #[trigger] comp_at(y@, b as int, p2);
            }
        }
        return false;
    }
    // The first `Customer` ending a character, with room for `Complaints` after it.
    let mut p = a;
    let mut found = false;
    while !found && b - p >= 18
        invariant
            a <= p, b <= n, n <= y@.len(), b - a >= 18,
            p <= b,
            found ==> b - p >= 18 && cust_at(y@, p as int),
            forall|p1: int| a <= p1 < p ==> !#[trigger] cust_at(y@, p1),
        decreases b - p, if found { 0int } else { 1int },
    {
        if y[p] == 67u8 && at_customer(y, p, Ghost(n)) && !(0x80u8 <= y[p + 8] && y[p + 8] < 0xC0u8) {
            found = true;
        } else {
            proof {
                if y@[p as int] != 67u8 {
                    assert(!cust_at(y@, p as int)) by {
                        if occurs_at(y@, cust(), p as int) { assert(y@[p + 0] == cust()[0]); }
                    }
                }
            }
            p = p + 1;
        }
    }
    if !found {
        proof {
            if hit_in(y@, a as int, b as int) {
                let (p1, p2) = choose|p1: int, p2: int| a <= p1 && p1 + 8 <= p2 && p2 + 10 <= b
                    && #[trigger] cust_at(y@, p1) && #[trigger] comp_at(y@, b as int, p2);
                assert(p1 < p);
            }
        }
        return false;
    }
    let mut q = p + 8;
    while b - q >= 10
        invariant
            a <= p, p + 18 <= b, b <= n, n <= y@.len(),
            cust_at(y@, p as int),
            p + 8 <= q, q <= b,
            forall|p1: int| a <= p1 < p ==> !#[trigger] cust_at(y@, p1),
            forall|p2: int| p + 8 <= p2 < q ==> !#[trigger] comp_at(y@, b as int, p2),
        decreases b - q,
    {
        if y[q] == 67u8 && at_complaints(y, q, Ghost(n)) && (q + 10 == b || !(0x80u8 <= y[q + 10] && y[q + 10] < 0xC0u8)) {
            proof {
                assert(comp_at(y@, b as int, q as int));
                assert(hit_in(y@, a as int, b as int));
            }
            return true;
        }
        proof {
            if y@[q as int] != 67u8 {
                assert(!comp_at(y@, b as int, q as int)) by {
                    if occurs_at(y@, comp(), q as int) { assert(y@[q + 0] == comp()[0]); }
                }
            }
        }
        q = q + 1;
    }
    proof {
        if hit_in(y@, a as int, b as int) {
            let (p1, p2) = choose|p1: int, p2: int| a <= p1 && p1 + 8 <= p2 && p2 + 10 <= b
                && #[trigger] cust_at(y@, p1) && #[trigger] comp_at(y@, b as int, p2);
            assert(p <= p1);
            assert(p2 < q);
        }
    }
    false
}

/// The bytes `y[a .. b]` as a slice.
fn byte_range(y: &'static [u8], a: usize, b: usize, Ghost(n): Ghost<int>) -> (r: &'static [u8])
    requires a <= b, b <= n, n <= y@.len(),
    ensures r@ == y@.subrange(a as int, b as int),
    no_unwind
{
    let (_, tail) = y.split_at(a);
    let (mid, _) = tail.split_at(b - a);
    proof {
        assert(mid@ =~= y@.subrange(a as int, b as int));
    }
    mid
}

/// `x | y` is zero exactly when both are.
proof fn lemma_or_zero(x: u8, y: u8)
    by (bit_vector)
    ensures ((x | y) == 0u8) == (x == 0u8 && y == 0u8),
{
}

/// Whether `r` holds an upper-case `C` (branch-free, so the loop vectorizes).
fn has_c(r: &[u8], m: usize) -> (h: bool)
    requires m == r@.len(),
    ensures (exists|k: int| 0 <= k < m && #[trigger] r@[k] == 67u8) ==> h,
    no_unwind
{
    let mut any: u8 = 0;
    let mut k: usize = 0;
    while k < m
        invariant
            m == r@.len(), k <= m,
            any == 0 ==> forall|k2: int| 0 <= k2 < k ==> #[trigger] r@[k2] != 67u8,
        decreases m - k,
    {
        let hit: u8 = if r[k] == 67u8 { 1 } else { 0 };
        proof {
            lemma_or_zero(any, hit);
        }
        any = any | hit;
        k = k + 1;
    }
    any != 0
}

/// Rows per chunk of the supplier scan (`SuppTask::run`).
pub const CHUNK: usize = 16;

/// Comment offsets are nondecreasing: `o[a] <= o[b]` for `a <= b <= n`.
pub proof fn lemma_offs_mono(s: SCols, a: int, b: int)
    requires comm_ok(s), 0 <= a <= b <= s.n,
    ensures s.comm_o@[a] <= s.comm_o@[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(s, a, b - 1);
        assert(s.comm_o@[b - 1] <= s.comm_o@[(b - 1) + 1]);
    }
}

/// Supplier rows `[lo, hi)`: the rows whose comment matches (at most `cap`).
pub struct SuppTask {
    pub s: SCols,
    pub lo: usize,
    pub hi: usize,
    pub cap: usize,
    pub out: Vec<usize>,
}

pub struct SuppOut {
    pub rows: Vec<usize>,
    pub len: usize,
    /// False when more than `cap` rows matched (the task stopped).
    pub done: bool,
}

/// A finished output over rows `[lo, hi)`: the listed rows are exactly the matching rows there.
pub open spec fn supp_out_ok(s: SCols, lo: int, hi: int, o: SuppOut) -> bool {
    &&& o.len <= o.rows@.len()
    &&& forall|q: int| 0 <= q < o.len ==> lo <= #[trigger] o.rows@[q] < hi && cc_row(s, o.rows@[q] as int)
    &&& forall|r: int| lo <= r < hi && #[trigger] cc_row(s, r) ==> exists|q: int| 0 <= q < o.len && o.rows@[q] == r
}

impl WorkerTask for SuppTask {
    type Output = SuppOut;

    open spec fn pre(&self) -> bool {
        &&& comm_ok(self.s)
        &&& self.lo <= self.hi <= self.s.n
        &&& self.out@.len() == self.cap
    }

    open spec fn post(&self, out: SuppOut) -> bool {
        &&& out.done ==> supp_out_ok(self.s, self.lo as int, self.hi as int, out)
        &&& self.cap >= self.hi - self.lo ==> out.done
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: SuppOut) {
        let SuppTask { s, lo, hi, cap, out } = self;
        let mut out = out;
        let mut len: usize = 0;
        let ghost n = s.comm_y@.len() as int;
        let mut j = lo;
        while j < hi
            invariant
                comm_ok(s), s == self.s, lo == self.lo, hi == self.hi, cap == self.cap,
                lo <= j <= hi <= s.n,
                n == s.comm_y@.len(),
                out@.len() == cap, len <= cap, len <= j - lo,
                forall|q: int| 0 <= q < len ==> lo <= #[trigger] out@[q] < j && cc_row(s, out@[q] as int),
                forall|r: int| lo <= r < j && #[trigger] cc_row(s, r) ==> exists|q: int| 0 <= q < len && out@[q] == r,
            decreases hi - j,
        {
            // A chunk of up to `CHUNK` rows: one branch-free scan of their bytes for an upper-case `C` decides that
            // no row of the chunk matches; only a chunk holding one is tested row by row.
            let e = if hi - j > CHUNK { j + CHUNK } else { hi };
            proof {
                lemma_offs_mono(s, j as int, e as int);
                assert(s.comm_o@[(e - 1) as int] <= s.comm_o@[e as int] && s.comm_o@[e as int] <= s.comm_y@.len());
            }
            let ca = s.comm_o[j] as usize;
            let cb = s.comm_o[e] as usize;
            let chunk = byte_range(s.comm_y, ca, cb, Ghost(n));
            if has_c(chunk, cb - ca) {
                while j < e
                    invariant
                        comm_ok(s), s == self.s, lo == self.lo, hi == self.hi, cap == self.cap,
                        lo <= j <= e <= hi <= s.n,
                        n == s.comm_y@.len(),
                        out@.len() == cap, len <= cap, len <= j - lo,
                        forall|q: int| 0 <= q < len ==> lo <= #[trigger] out@[q] < j && cc_row(s, out@[q] as int),
                        forall|r: int| lo <= r < j && #[trigger] cc_row(s, r) ==> exists|q: int| 0 <= q < len && out@[q] == r,
                    decreases e - j,
                {
                    proof {
                        assert(s.comm_o@[j as int] <= s.comm_o@[j + 1] && s.comm_o@[j + 1] <= s.comm_y@.len());
                        assert(s.comm_len == s.comm_y@.len());
                    }
                    let a = s.comm_o[j] as usize;
                    let b = s.comm_o[j + 1] as usize;
                    let pass = byte_hit(s.comm_y, a, b, Ghost(n));
                    proof {
                        lemma_cc_exact(s, j as int);
                        assert(pass == cc_row(s, j as int));
                    }
                    if pass {
                        if len >= cap {
                            return SuppOut { rows: out, len, done: false };
                        }
                        let ghost out0 = out@;
                        out[len] = j;
                        len = len + 1;
                        proof {
                            assert forall|q: int| 0 <= q < len implies lo <= #[trigger] out@[q] < j + 1 && cc_row(s, out@[q] as int) by {
                                if q < len - 1 {
                                    assert(out@[q] == out0[q]);
                                }
                            }
                            assert forall|r: int| lo <= r < j + 1 && #[trigger] cc_row(s, r) implies
                                exists|q: int| 0 <= q < len && out@[q] == r by {
                                if r < j {
                                    let q = choose|q: int| 0 <= q < len - 1 && out0[q] == r;
                                    assert(out@[q] == out0[q]);
                                } else {
                                    assert(out@[len - 1] == r);
                                }
                            }
                        }
                    }
                    j = j + 1;
                }
            } else {
                proof {
                    assert forall|r: int| j <= r < e implies !#[trigger] cc_row(s, r) by {
                        lemma_cc_exact(s, r);
                        lemma_offs_mono(s, j as int, r);
                        lemma_offs_mono(s, r + 1, e as int);
                        if hit_in(s.comm_y@, s.comm_o@[r] as int, s.comm_o@[r + 1] as int) {
                            let (p1, p2) = choose|p1: int, p2: int| s.comm_o@[r] <= p1 && p1 + 8 <= p2
                                && p2 + 10 <= s.comm_o@[r + 1]
                                && #[trigger] cust_at(s.comm_y@, p1) && #[trigger] comp_at(s.comm_y@, s.comm_o@[r + 1] as int, p2);
                            assert(s.comm_y@[p1 + 0] == cust()[0]);
                            assert(chunk@[p1 - ca] == 67u8);
                        }
                    }
                    assert forall|r: int| lo <= r < e && #[trigger] cc_row(s, r) implies
                        exists|q: int| 0 <= q < len && out@[q] == r by {}
                }
                j = e;
            }
        }
        SuppOut { rows: out, len, done: true }
    }
}

} // verus!
