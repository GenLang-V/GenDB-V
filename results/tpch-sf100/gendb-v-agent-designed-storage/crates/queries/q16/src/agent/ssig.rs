//! The NOT IN subquery through storage `supp_trisig`: the 128-bit trigram signature of every supplier row's s_comment
//! (two U64 words per row) decides most rows without reading the comment.
//!
//! A comment matching `%Customer%Complaints%` holds the six probe trigrams `Cus`, `tom`, `mer` (of `Customer`) and
//! `Com`, `pla`, `nts` (of `Complaints`), so its signature holds every bit of `probe_mask` (`lemma_cc_sig`). A row whose
//! signature misses one of those bits is not excluded; every other row (a candidate, about 0.3% of rows) gets the exact
//! byte test of `supp::byte_hit`. `SigTask` lists the matching rows of a supplier row range like `supp::SuppTask`, and
//! `excl_bitmap_sig` merges the lists into the exclusion bitmap with `ixcnt::excl_merge`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::stores::supp_trisig::interface as sti;
use crate::stores::supp_trisig::interface::trisig::{sig_of, tri_bit, tri_bits_exec, lemma_sig_has};
use crate::stores::suppliers::interface::common::colfmt::u64s;
use super::tables::*;
use super::supp::{cc_row, comment, comm_ok, cust_at, comp_at, cust, comp, byte_hit, lemma_cc_exact, SuppOut,
    supp_out_ok};
use super::common::likebytes::occurs_at;
use super::common::marks::bit_at;
use super::split::{cuts, split_range};
use super::ixcnt::excl_merge;

verus! {

/// Word `w` of the OR of the signature bits of the six probe trigrams: `Cus`, `tom`, `mer`, `Com`, `pla`, `nts`
/// (opaque: its hash arithmetic is revealed only in `probe_masks` and `lemma_cc_sig`).
#[verifier::opaque]
pub open spec fn probe_mask(w: int) -> u64 {
    tri_bit(67u8, 117u8, 115u8, w) | tri_bit(116u8, 111u8, 109u8, w) | tri_bit(109u8, 101u8, 114u8, w)
        | tri_bit(67u8, 111u8, 109u8, w) | tri_bit(112u8, 108u8, 97u8, w) | tri_bit(110u8, 116u8, 115u8, w)
}

/// Both words of `probe_mask`, computed.
fn probe_masks() -> (r: (u64, u64))
    ensures r.0 == probe_mask(0), r.1 == probe_mask(1),
{
    reveal(probe_mask);
    let (a0, a1) = tri_bits_exec(67u8, 117u8, 115u8);
    let (b0, b1) = tri_bits_exec(116u8, 111u8, 109u8);
    let (c0, c1) = tri_bits_exec(109u8, 101u8, 114u8);
    let (d0, d1) = tri_bits_exec(67u8, 111u8, 109u8);
    let (e0, e1) = tri_bits_exec(112u8, 108u8, 97u8);
    let (f0, f1) = tri_bits_exec(110u8, 116u8, 115u8);
    (a0 | b0 | c0 | d0 | e0 | f0, a1 | b1 | c1 | d1 | e1 | f1)
}

/// A word holding six bit sets holds their union.
proof fn lemma_and6(x: u64, b1: u64, b2: u64, b3: u64, b4: u64, b5: u64, b6: u64)
    by (bit_vector)
    requires x & b1 == b1, x & b2 == b2, x & b3 == b3, x & b4 == b4, x & b5 == b5, x & b6 == b6,
    ensures x & (b1 | b2 | b3 | b4 | b5 | b6) == (b1 | b2 | b3 | b4 | b5 | b6),
{
}

/// The signature of `t` holds the bit of the trigram `a, b, c` found at `q`.
proof fn lemma_tri_at(t: Seq<u8>, q: int, w: int, a: u8, b: u8, c: u8)
    requires 0 <= q, q + 2 < t.len(), t[q] == a, t[q + 1] == b, t[q + 2] == c,
    ensures sig_of(t, w) & tri_bit(a, b, c, w) == tri_bit(a, b, c, w),
{
    lemma_sig_has(t, q, w);
}

/// A matching comment's signature holds every probe bit.
pub proof fn lemma_cc_sig(s: SCols, r: int, w: int)
    requires comm_ok(s), 0 <= r < s.n, cc_row(s, r),
    ensures sig_of(comment(s, r), w) & probe_mask(w) == probe_mask(w),
{
    reveal(probe_mask);
    lemma_cc_exact(s, r);
    let y = s.comm_y@;
    let (a, b) = (s.comm_o@[r] as int, s.comm_o@[r + 1] as int);
    assert(a <= b && b <= y.len());
    let (p1, p2) = choose|p1: int, p2: int| a <= p1 && p1 + 8 <= p2 && p2 + 10 <= b
        && #[trigger] cust_at(y, p1) && #[trigger] comp_at(y, b, p2);
    let t = comment(s, r);
    assert(t == y.subrange(a, b));
    assert(occurs_at(y, cust(), p1));
    assert(occurs_at(y, comp(), p2));
    // The bytes of both words in `t` (`t[i] == y[a + i]`).
    let (q1, q2) = (p1 - a, p2 - a);
    assert forall|m: int| 0 <= m < 8 implies #[trigger] t[q1 + m] == cust()[m] by {
        assert(y[p1 + m] == cust()[m]);
    }
    assert forall|m: int| 0 <= m < 10 implies #[trigger] t[q2 + m] == comp()[m] by {
        assert(y[p2 + m] == comp()[m]);
    }
    assert(t[q1 + 0] == 67u8 && t[q1 + 1] == 117u8 && t[q1 + 2] == 115u8);
    assert(t[q1 + 3] == 116u8 && t[q1 + 4] == 111u8 && t[q1 + 5] == 109u8);
    assert(t[q1 + 6] == 101u8 && t[q1 + 7] == 114u8);
    assert(t[q2 + 0] == 67u8 && t[q2 + 1] == 111u8 && t[q2 + 2] == 109u8);
    assert(t[q2 + 3] == 112u8 && t[q2 + 4] == 108u8 && t[q2 + 5] == 97u8);
    assert(t[q2 + 7] == 110u8 && t[q2 + 8] == 116u8 && t[q2 + 9] == 115u8);
    lemma_tri_at(t, q1, w, 67u8, 117u8, 115u8);
    lemma_tri_at(t, q1 + 3, w, 116u8, 111u8, 109u8);
    lemma_tri_at(t, q1 + 5, w, 109u8, 101u8, 114u8);
    lemma_tri_at(t, q2, w, 67u8, 111u8, 109u8);
    lemma_tri_at(t, q2 + 3, w, 112u8, 108u8, 97u8);
    lemma_tri_at(t, q2 + 7, w, 110u8, 116u8, 115u8);
    lemma_and6(sig_of(t, w), tri_bit(67u8, 117u8, 115u8, w), tri_bit(116u8, 111u8, 109u8, w),
        tri_bit(109u8, 101u8, 114u8, w), tri_bit(67u8, 111u8, 109u8, w), tri_bit(112u8, 108u8, 97u8, w),
        tri_bit(110u8, 116u8, 115u8, w));
}

// ------------------------------------------------------------------------------------------------ the signatures

/// The signature words of the supplier rows, two per row.
#[derive(Clone, Copy)]
pub struct SSig {
    pub sig: &'static [u64],
    /// The number of words (`sig`'s length).
    pub len: usize,
}

/// Words `2 r` and `2 r + 1` are the signature of supplier row `r`'s comment.
pub open spec fn ssig_ok(s: SCols, g: SSig) -> bool {
    &&& g.sig@.len() == 2 * s.n
    &&& g.len == g.sig@.len()
    &&& forall|r: int| 0 <= r < s.n ==> {
            &&& #[trigger] g.sig@[2 * r] == sig_of(comment(s, r), 0)
            &&& g.sig@[2 * r + 1] == sig_of(comment(s, r), 1)
        }
}

/// The signature part of storage `supp_trisig`, over the supplier relation whose comments are `s`'s.
pub fn open_ssig(st: &mut StoredParts, s: &SCols, Ghost(sr): Ghost<Seq<Seq<Row>>>) -> (g: SSig)
    requires
        sti::represents(old(st)@, sr),
        comm_ok(*s),
        sr[1].len() == s.n,
        forall|j: int| 0 <= j < s.n ==> #[trigger] sr[1][j][6] == Val::Text(comment(*s, j)),
    ensures
        final(st)@ == old(st)@,
        ssig_ok(*s, g),
{
    let ghost parts = st@;
    let n = st.part_len(sti::SUPP_SIG);
    let sig = st.extent_u64(sti::SUPP_SIG, 0, n);
    proof {
        assert(sig@ =~= u64s(parts[sti::SUPP_SIG as int]));
        assert forall|r: int| 0 <= r < s.n implies {
            &&& #[trigger] sig@[2 * r] == sig_of(comment(*s, r), 0)
            &&& sig@[2 * r + 1] == sig_of(comment(*s, r), 1)
        } by {
            sti::lemma_comment_sig(parts, sr, r);
            assert(Val::Text(sti::comment_at(parts, r)) == Val::Text(comment(*s, r)));
        }
    }
    SSig { sig, len: n }
}

// ------------------------------------------------------------------------------------------------ the scan

/// Whether the subquery excludes supplier row `j`: the signature rules out a row missing a probe bit; a candidate gets
/// the exact byte test.
#[inline(always)]
fn row_excluded(s: &SCols, g: SSig, m0: u64, m1: u64, j: usize) -> (pass: bool)
    requires comm_ok(*s), ssig_ok(*s, g), m0 == probe_mask(0), m1 == probe_mask(1), j < s.n,
    ensures pass == cc_row(*s, j as int),
    no_unwind
{
    proof {
        assert(2 * (j as int) + 1 < g.len);
        assert(g.sig@[2 * (j as int)] == sig_of(comment(*s, j as int), 0));
    }
    let w0 = g.sig[2 * j];
    let w1 = g.sig[2 * j + 1];
    if (w0 & m0) == m0 && (w1 & m1) == m1 {
        proof {
            assert(s.comm_o@[j as int] <= s.comm_o@[j + 1] && s.comm_o@[j + 1] <= s.comm_y@.len());
            assert(s.comm_len == s.comm_y@.len());
            lemma_cc_exact(*s, j as int);
        }
        let a = s.comm_o[j] as usize;
        let b = s.comm_o[j + 1] as usize;
        byte_hit(s.comm_y, a, b, Ghost(s.comm_y@.len() as int))
    } else {
        proof {
            if cc_row(*s, j as int) {
                lemma_cc_sig(*s, j as int, 0);
                lemma_cc_sig(*s, j as int, 1);
            }
        }
        false
    }
}

/// The supplier rows `[lo, hi)`: list the rows the subquery excludes (room for `cap`).
pub struct SigTask {
    pub s: SCols,
    pub g: SSig,
    /// `probe_mask(0)` and `probe_mask(1)`.
    pub m0: u64,
    pub m1: u64,
    pub lo: usize,
    pub hi: usize,
    pub cap: usize,
    pub out: Vec<usize>,
}

impl WorkerTask for SigTask {
    type Output = SuppOut;

    open spec fn pre(&self) -> bool {
        &&& comm_ok(self.s)
        &&& ssig_ok(self.s, self.g)
        &&& self.m0 == probe_mask(0) && self.m1 == probe_mask(1)
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
        let SigTask { s, g, m0, m1, lo, hi, cap, out } = self;
        let mut out = out;
        let mut len: usize = 0;
        let ghost n = s.comm_y@.len() as int;
        let mut j = lo;
        while j < hi
            invariant
                comm_ok(s), ssig_ok(s, g), m0 == probe_mask(0), m1 == probe_mask(1),
                s == self.s, lo == self.lo, hi == self.hi, cap == self.cap,
                lo <= j <= hi <= s.n,
                n == s.comm_y@.len(),
                out@.len() == cap, len <= cap, len <= j - lo,
                forall|q: int| 0 <= q < len ==> lo <= #[trigger] out@[q] < j && cc_row(s, out@[q] as int),
                forall|r: int| lo <= r < j && #[trigger] cc_row(s, r) ==> exists|q: int| 0 <= q < len && out@[q] == r,
            decreases hi - j,
        {
            let pass = row_excluded(&s, g, m0, m1, j);
            assert(pass == cc_row(s, j as int));
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
        SuppOut { rows: out, len, done: true }
    }
}

/// The supplier rows `[lo, hi)` task, with room for all of them.
fn sig_task(s: &SCols, g: SSig, m0: u64, m1: u64, lo: usize, hi: usize) -> (st: SigTask)
    requires comm_ok(*s), ssig_ok(*s, g), m0 == probe_mask(0), m1 == probe_mask(1), lo <= hi <= s.n,
    ensures st.pre(), st.s == *s, st.lo == lo, st.hi == hi, st.cap >= hi - lo,
{
    let cap = hi - lo;
    SigTask { s: *s, g, m0, m1, lo, hi, cap, out: vec![0usize; cap] }
}

/// The bitmap of the supplier rows the subquery excludes, decided through the signatures by at most `workers` tasks
/// over consecutive supplier ranges.
pub fn excl_bitmap_sig(s: &SCols, g: SSig, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<u64>, QueryError>)
    requires comm_ok(*s), ssig_ok(*s, g), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(m) ==> s.n <= 64 * m@.len() && forall|j: int| 0 <= j < s.n ==> #[trigger] bit_at(m@, j) == cc_row(*s, j),
{
    let (m0, m1) = probe_masks();
    let sb = split_range(s.n, workers, 1);
    let nk = sb.len() - 1;
    let mut tasks: Vec<SigTask> = Vec::new();
    let mut k: usize = 0;
    while k < nk
        invariant
            comm_ok(*s), ssig_ok(*s, g), m0 == probe_mask(0), m1 == probe_mask(1),
            cuts(sb@, s.n as int), nk == sb@.len() - 1, k <= nk, tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].s == *s
                && tasks@[i].lo == sb@[i] && tasks@[i].hi == sb@[i + 1] && tasks@[i].cap >= tasks@[i].hi - tasks@[i].lo,
        decreases nk - k,
    {
        proof {
            assert(sb@[k as int] <= sb@[k + 1]);
            super::round::lemma_cuts_mono(sb@, s.n as int, k as int + 1, nk as int);
        }
        let st = sig_task(s, g, m0, m1, sb[k], sb[k + 1]);
        tasks.push(st);
        k = k + 1;
    }
    let ghost ts = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(QueryError::WorkerFailed(e));
        },
    };
    proof {
        assert forall|i: int| 0 <= i < nk implies supp_out_ok(*s, sb@[i] as int, sb@[i + 1] as int, #[trigger] outs@[i]) by {
            assert(ts[i].post(outs@[i]));
        }
    }
    Ok(excl_merge(s, &sb, &outs))
}

} // verus!
