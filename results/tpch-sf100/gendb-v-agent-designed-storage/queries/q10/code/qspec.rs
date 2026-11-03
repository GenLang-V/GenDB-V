//! The Q10 result over the model (`model`). The date window is `[lo, hi]` in days (`$1` and the last day before
//! `$1 + 3 months`). Per order (stored position `q`): `lhit(q, j)` says lineitem row `j` belongs to the order and is
//! returned (`l_returnflag = 'R'`); `lcnt(q)`, `lsum(q)`, `labs(q)` are the count, the exact revenue sum
//! (`l_extendedprice * (1 - l_discount)`, coefficients at scale 4) and the absolute revenue sum of those rows. Per
//! customer (stored row `c`): `ohit(c, q)` says order `q` is the customer's and dated in the window; `ccnt(c)`,
//! `csum(c)`, `cabs(c)` sum the order values over those orders. Customer `c` is a group exactly when `good(c)`:
//! its nation exists (`nat_ok`) and it has a returned lineitem in the window (`ccnt(c) > 0`); its row is `grow(c)`.
//! `gseq(lo, hi)` lists the rows of the groups at customer rows `[lo, hi)`. The SQL link proves that the
//! statement's groups are exactly `gseq(0, c_n)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::OrderKey;
use crate::link::expr::i128_max;
use super::common::isum::*;
use super::model::*;

verus! {

/// The date window `[lo, hi]` (days since 2000-01-01).
pub struct QP {
    pub lo: int,
    pub hi: int,
}

/// The text `'R'`.
pub open spec fn r_text() -> Seq<u8> { seq![82u8] }

// ------------------------------------------------------------------------------------------------ orders

/// Lineitem row `j` belongs to the order at position `q` and is returned.
pub open spec fn lhit(m: M, q: int, j: int) -> bool {
    lkey(m, j) == okey(m, q) && lflag(m, j) == r_text()
}

pub open spec fn lcnt_f(m: M, q: int) -> spec_fn(int) -> int {
    |j: int| if lhit(m, q, j) { 1int } else { 0int }
}

pub open spec fn lsum_f(m: M, q: int) -> spec_fn(int) -> int {
    |j: int| if lhit(m, q, j) { larg(m, j) } else { 0int }
}

pub open spec fn labs_f(m: M, q: int) -> spec_fn(int) -> int {
    |j: int| if lhit(m, q, j) { abs(larg(m, j)) } else { 0int }
}

/// Number, revenue sum and absolute revenue sum of the returned lineitems of the order at `q`.
pub open spec fn lcnt(m: M, q: int) -> int { isum(m.l_n, lcnt_f(m, q)) }
pub open spec fn lsum(m: M, q: int) -> int { isum(m.l_n, lsum_f(m, q)) }
pub open spec fn labs(m: M, q: int) -> int { isum(m.l_n, labs_f(m, q)) }

/// The order at `q` is dated in the window.
pub open spec fn odok(m: M, p: QP, q: int) -> bool {
    p.lo <= odate(m, q) <= p.hi
}

// ------------------------------------------------------------------------------------------------ customers

/// The order at `q` belongs to customer row `c` and is dated in the window.
pub open spec fn ohit(m: M, p: QP, c: int, q: int) -> bool {
    ocust(m, q) == ckey(m, c) && odok(m, p, q)
}

pub open spec fn ccnt_f(m: M, p: QP, c: int) -> spec_fn(int) -> int {
    |q: int| if ohit(m, p, c, q) { lcnt(m, q) } else { 0int }
}

pub open spec fn csum_f(m: M, p: QP, c: int) -> spec_fn(int) -> int {
    |q: int| if ohit(m, p, c, q) { lsum(m, q) } else { 0int }
}

pub open spec fn cabs_f(m: M, p: QP, c: int) -> spec_fn(int) -> int {
    |q: int| if ohit(m, p, c, q) { labs(m, q) } else { 0int }
}

/// Number, revenue and absolute revenue of the returned lineitems of customer `c`'s orders in the window.
pub open spec fn ccnt(m: M, p: QP, c: int) -> int { isum(m.o_n, ccnt_f(m, p, c)) }
pub open spec fn csum(m: M, p: QP, c: int) -> int { isum(m.o_n, csum_f(m, p, c)) }
pub open spec fn cabs(m: M, p: QP, c: int) -> int { isum(m.o_n, cabs_f(m, p, c)) }

/// The nation row of customer `c` exists.
pub open spec fn nat_ok(m: M, c: int) -> bool {
    npos(m, cnat(m, c)) < m.n_n
}

/// The nation name of customer `c`.
pub open spec fn cnname(m: M, c: int) -> Seq<u8> {
    nname(m, npos(m, cnat(m, c)))
}

// ------------------------------------------------------------------------------------------------ groups

/// Customer row `c` is a group of the result.
pub open spec fn good(m: M, p: QP, c: int) -> bool {
    nat_ok(m, c) && ccnt(m, p, c) > 0
}

/// The result row of customer `c` with revenue coefficient `rev` (scale 4).
pub open spec fn crow_rev(m: M, c: int, rev: int) -> Row {
    seq![Val::Int(ckey(m, c)), Val::Text(cname(m, c)), Val::Num { coeff: rev, scale: 4 },
        Val::Num { coeff: cbal(m, c), scale: 2 }, Val::Text(cnname(m, c)), Val::Text(caddr(m, c)),
        Val::Text(cphone(m, c)), Val::Text(ccmt(m, c))]
}

/// The result row of the group of customer `c`.
pub open spec fn grow(m: M, p: QP, c: int) -> Row {
    crow_rev(m, c, csum(m, p, c))
}

/// The rows of the groups at customer rows `[lo, hi)`, in row order.
pub open spec fn gseq(m: M, p: QP, lo: int, hi: int) -> Seq<Row>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else {
        let s = gseq(m, p, lo, hi - 1);
        if good(m, p, hi - 1) { s.push(grow(m, p, hi - 1)) } else { s }
    }
}

/// Every group's revenue has absolute coefficient mass inside `i128` (the SUM capacity condition).
pub open spec fn caps_ok(m: M, p: QP) -> bool {
    forall|c: int| 0 <= c < m.c_n && #[trigger] good(m, p, c) ==> cabs(m, p, c) <= i128_max()
}

/// ORDER BY revenue DESC.
pub open spec fn q10_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 2, desc: true, nulls_first: true }]
}

/// Family of the ORDER BY key: numeric (1).
pub open spec fn q10_fams() -> Seq<int> {
    seq![1int]
}

// ------------------------------------------------------------------------------------------------ laws

/// One more position.
pub proof fn lemma_gseq_step(m: M, p: QP, lo: int, hi: int)
    requires lo <= hi,
    ensures gseq(m, p, lo, hi + 1) == if good(m, p, hi) { gseq(m, p, lo, hi).push(grow(m, p, hi)) } else { gseq(m, p, lo, hi) },
{
}

/// The empty range.
pub proof fn lemma_gseq_empty(m: M, p: QP, lo: int)
    ensures gseq(m, p, lo, lo) == Seq::<Row>::empty(),
{
}

/// Adjacent ranges concatenate.
pub proof fn lemma_gseq_split(m: M, p: QP, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures gseq(m, p, lo, hi) == gseq(m, p, lo, mid) + gseq(m, p, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_gseq_split(m, p, lo, mid, hi - 1);
        if good(m, p, hi - 1) {
            assert(gseq(m, p, lo, mid) + gseq(m, p, mid, hi - 1).push(grow(m, p, hi - 1))
                =~= (gseq(m, p, lo, mid) + gseq(m, p, mid, hi - 1)).push(grow(m, p, hi - 1)));
        }
    } else {
        assert(gseq(m, p, lo, mid) + Seq::<Row>::empty() =~= gseq(m, p, lo, mid));
    }
}

/// A range without groups has no rows.
pub proof fn lemma_gseq_none(m: M, p: QP, lo: int, hi: int)
    requires forall|c: int| lo <= c < hi ==> !#[trigger] good(m, p, c),
    ensures gseq(m, p, lo, hi) == Seq::<Row>::empty(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_gseq_none(m, p, lo, hi - 1);
    }
}

/// The rows of `gseq` are the rows of the groups in the range.
pub proof fn lemma_gseq_contains(m: M, p: QP, lo: int, hi: int)
    ensures
        forall|r: Row| #[trigger] gseq(m, p, lo, hi).contains(r) <==> exists|c: int| lo <= c < hi && good(m, p, c) && r == grow(m, p, c),
    decreases hi - lo,
{
    if hi > lo {
        lemma_gseq_contains(m, p, lo, hi - 1);
        let s = gseq(m, p, lo, hi - 1);
        assert forall|r: Row| #[trigger] gseq(m, p, lo, hi).contains(r) <==> exists|c: int| lo <= c < hi && good(m, p, c) && r == grow(m, p, c) by {
            if good(m, p, hi - 1) {
                let t = s.push(grow(m, p, hi - 1));
                assert(t[s.len() as int] == grow(m, p, hi - 1));
                if t.contains(r) {
                    let i = choose|i: int| 0 <= i < t.len() && t[i] == r;
                    if i < s.len() {
                        assert(s[i] == r);
                        assert(s.contains(r));
                    } else {
                        assert(r == grow(m, p, hi - 1));
                    }
                }
                if exists|c: int| lo <= c < hi && good(m, p, c) && r == grow(m, p, c) {
                    let c = choose|c: int| lo <= c < hi && good(m, p, c) && r == grow(m, p, c);
                    if c < hi - 1 {
                        assert(s.contains(r));
                        let i = choose|i: int| 0 <= i < s.len() && s[i] == r;
                        assert(t[i] == r);
                    }
                }
            } else {
                if exists|c: int| lo <= c < hi && good(m, p, c) && r == grow(m, p, c) {
                    let c = choose|c: int| lo <= c < hi && good(m, p, c) && r == grow(m, p, c);
                    assert(c < hi - 1);
                }
            }
        }
    }
}

/// Under the customer primary key the group rows are distinct.
pub proof fn lemma_gseq_nodup(m: M, p: QP, lo: int, hi: int)
    requires
        0 <= lo,
        hi <= m.c_n,
        forall|a: int, b: int| 0 <= a < m.c_n && 0 <= b < m.c_n && a != b ==> #[trigger] ckey(m, a) != #[trigger] ckey(m, b),
    ensures gseq(m, p, lo, hi).no_duplicates(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_gseq_nodup(m, p, lo, hi - 1);
        let s = gseq(m, p, lo, hi - 1);
        if good(m, p, hi - 1) {
            lemma_gseq_contains(m, p, lo, hi - 1);
            let x = grow(m, p, hi - 1);
            assert(!s.contains(x)) by {
                if s.contains(x) {
                    let c = choose|c: int| lo <= c < hi - 1 && good(m, p, c) && x == grow(m, p, c);
                    assert(grow(m, p, c)[0] == Val::Int(ckey(m, c)));
                    assert(x[0] == Val::Int(ckey(m, hi - 1)));
                    assert(ckey(m, c) != ckey(m, hi - 1));
                }
            }
            let t = s.push(x);
            assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i] != t[j] by {
                if i == s.len() {
                    assert(s.contains(t[j]));
                } else if j == s.len() {
                    assert(s.contains(t[i]));
                }
            }
        }
    }
}

} // verus!
