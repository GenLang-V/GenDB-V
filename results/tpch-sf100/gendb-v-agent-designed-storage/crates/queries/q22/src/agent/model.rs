//! The scan model: what the query computes per customer row `i` from the views of the parts it reads (`Cv`), and
//! the per-range accumulators of its two passes.
//! - `rtext(v, i)`: c_phone (custpart text offsets + bytes); `rgid(v, i)`: the group of `SUBSTRING(c_phone, 1, 2)`,
//!   the first parameter slot holding that text (0..7), or `NG` (7) when none does;
//! - `racct(v, i)`: the c_acctbal coefficient (scale 2, FOR codes + group bases); `rkey(v, i)`: c_custkey;
//! - `rnoord(v, i)`: no orders row has o_custkey `rkey(v, i)` (orders_custidx: the directory entry of the key is
//!   empty or the key is outside the directory; fallback mode: no stored key equals it);
//! - pass A (`qa`, `cnta`, `suma`): rows of a listed country code with a positive balance (the AVG subquery);
//! - pass B (`qb`, `cntb`, `sumb`): rows of group `k` above the average without orders (the outer query).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::*;
use crate::stores::custpart::interface::common::colfmt::text_of;
use super::common::sub2::*;

verus! {

/// Number of parameter slots of the IN list; group `NG` means "not listed".
pub const NG: usize = 7;

/// Exclusive bound of a c_acctbal coefficient (numeric(15, 2)).
pub open spec fn acct_bound() -> int { 1_000_000_000_000_000 }

/// Text of parameter slot `k`.
pub open spec fn ptext(ps: Seq<Literal>, k: int) -> Seq<u8> {
    match ps[k] {
        Literal::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// The first slot `j >= k` whose parameter text is `t`, or `NG`.
pub open spec fn gid_from(ps: Seq<Literal>, k: int, t: Seq<u8>) -> int
    decreases 7 - k,
{
    if k >= 7 {
        7
    } else if ptext(ps, k) == t {
        k
    } else {
        gid_from(ps, k + 1, t)
    }
}

/// The group of country code `t`: the first slot holding it, or `NG`.
pub open spec fn gid(ps: Seq<Literal>, t: Seq<u8>) -> int {
    gid_from(ps, 0, t)
}

/// The views of the parts the scan reads.
pub struct Cv {
    pub poffs: Seq<u64>,
    pub pbytes: Seq<u8>,
    pub ac: Seq<u32>,
    pub ab: Seq<i64>,
    pub kc: Seq<u32>,
    pub kb: Seq<i64>,
    pub bs: int,
    pub n: int,
    pub dir: bool,
    pub kmin: int,
    pub offs: Seq<u32>,
    pub nk: int,
    pub keys: Seq<i64>,
    pub n_o: int,
    pub ps: Seq<Literal>,
}

/// c_phone of row `i`.
pub open spec fn rtext(v: Cv, i: int) -> Seq<u8> {
    text_of(v.poffs, v.pbytes, i)
}

/// The group of row `i`'s country code.
pub open spec fn rgid(v: Cv, i: int) -> int {
    gid(v.ps, sub2(rtext(v, i)))
}

/// c_acctbal coefficient of row `i`.
pub open spec fn racct(v: Cv, i: int) -> int {
    v.ab[i / v.bs] + v.ac[i]
}

/// c_custkey of row `i`.
pub open spec fn rkey(v: Cv, i: int) -> int {
    v.kb[i / v.bs] + v.kc[i]
}

/// No orders row has o_custkey `k`, by the index.
pub open spec fn noord_key(v: Cv, k: int) -> bool {
    if v.dir {
        !(v.kmin <= k < v.kmin + v.nk) || v.offs[k - v.kmin + 1] == v.offs[k - v.kmin]
    } else {
        forall|r: int| 0 <= r < v.n_o ==> #[trigger] v.keys[r] != k
    }
}

/// No orders row has row `i`'s key.
pub open spec fn rnoord(v: Cv, i: int) -> bool {
    noord_key(v, rkey(v, i))
}

/// What the readers need of the views.
pub open spec fn cv_ok(v: Cv) -> bool {
    &&& v.bs >= 1
    &&& 0 <= v.n < 0x1_0000_0000_0000_0000
    &&& v.pbytes.len() <= usize::MAX
    &&& v.poffs.len() == v.n + 1
    &&& forall|i: int| 0 <= i < v.n ==> #[trigger] v.poffs[i] <= v.poffs[i + 1] && v.poffs[i + 1] <= v.pbytes.len()
    &&& v.ac.len() == v.n
    &&& v.kc.len() == v.n
    &&& forall|i: int| 0 <= i < v.n ==> #[trigger] (i / v.bs) < v.ab.len() && i / v.bs < v.kb.len()
    &&& forall|i: int| 0 <= i < v.n ==> -acct_bound() < #[trigger] racct(v, i) < acct_bound()
    &&& forall|i: int| 0 <= i < v.n ==> i64::MIN <= #[trigger] rkey(v, i) <= i64::MAX
    &&& v.dir ==> v.offs.len() == v.nk + 1 && 0 <= v.nk
    &&& !v.dir ==> v.keys.len() == v.n_o && 0 <= v.n_o
    &&& v.ps.len() == 7
}

// ------------------------------------------------------------------------------------------------ pass A

/// Row `i` enters the AVG subquery.
pub open spec fn qa(v: Cv, i: int) -> bool {
    rgid(v, i) < 7 && racct(v, i) > 0
}

/// Rows of `[lo, hi)` entering the subquery.
pub open spec fn cnta(v: Cv, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { cnta(v, lo, hi - 1) + if qa(v, hi - 1) { 1nat } else { 0nat } }
}

/// Sum of their balances.
pub open spec fn suma(v: Cv, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { suma(v, lo, hi - 1) + if qa(v, hi - 1) { racct(v, hi - 1) } else { 0 } }
}

/// The accumulators split at `mid`.
pub proof fn lemma_a_split(v: Cv, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        cnta(v, lo, hi) == cnta(v, lo, mid) + cnta(v, mid, hi),
        suma(v, lo, hi) == suma(v, lo, mid) + suma(v, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_a_split(v, lo, mid, hi - 1);
    }
}

/// Bounds of the pass A accumulators.
pub proof fn lemma_a_bound(v: Cv, lo: int, hi: int)
    requires cv_ok(v), 0 <= lo <= hi <= v.n,
    ensures
        cnta(v, lo, hi) <= hi - lo,
        abs(suma(v, lo, hi)) <= cnta(v, lo, hi) * acct_bound(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_a_bound(v, lo, hi - 1);
        assert(-acct_bound() < racct(v, hi - 1) < acct_bound());
    }
}

// ------------------------------------------------------------------------------------------------ pass B

/// `a > avg` for a coefficient `a` at scale 2 (false against NULL).
pub open spec fn gt_avg(a: int, avg: Val) -> bool {
    match avg {
        Val::Num { coeff, scale } => num_cmp(a, 2, coeff, scale) > 0,
        _ => false,
    }
}

/// Row `i` is in the outer query's result.
pub open spec fn qb(v: Cv, avg: Val, i: int) -> bool {
    rgid(v, i) < 7 && gt_avg(racct(v, i), avg) && rnoord(v, i)
}

/// Result rows of group `k` in `[lo, hi)`.
pub open spec fn cntb(v: Cv, avg: Val, k: int, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { cntb(v, avg, k, lo, hi - 1) + if qb(v, avg, hi - 1) && rgid(v, hi - 1) == k { 1nat } else { 0nat } }
}

/// Sum of their balances.
pub open spec fn sumb(v: Cv, avg: Val, k: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { sumb(v, avg, k, lo, hi - 1) + if qb(v, avg, hi - 1) && rgid(v, hi - 1) == k { racct(v, hi - 1) } else { 0 } }
}

/// The accumulators split at `mid`.
pub proof fn lemma_b_split(v: Cv, avg: Val, k: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        cntb(v, avg, k, lo, hi) == cntb(v, avg, k, lo, mid) + cntb(v, avg, k, mid, hi),
        sumb(v, avg, k, lo, hi) == sumb(v, avg, k, lo, mid) + sumb(v, avg, k, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_b_split(v, avg, k, lo, mid, hi - 1);
    }
}

/// Bounds of the pass B accumulators.
pub proof fn lemma_b_bound(v: Cv, avg: Val, k: int, lo: int, hi: int)
    requires cv_ok(v), 0 <= lo <= hi <= v.n,
    ensures
        cntb(v, avg, k, lo, hi) <= hi - lo,
        abs(sumb(v, avg, k, lo, hi)) <= cntb(v, avg, k, lo, hi) * acct_bound(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_b_bound(v, avg, k, lo, hi - 1);
        assert(-acct_bound() < racct(v, hi - 1) < acct_bound());
    }
}

} // verus!
