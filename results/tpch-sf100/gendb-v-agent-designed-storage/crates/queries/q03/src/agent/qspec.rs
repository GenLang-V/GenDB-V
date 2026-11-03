//! The Q3 result over the model (`model`): for the market segment `seg` ($1) and the date `day` ($2), the order at
//! stored position `q` is a group exactly when `good(q)`: its date is before `day`, its customer has the segment, and
//! some lineitem of it ships after `day`. Its row is `grow(q)` = (l_orderkey, revenue, o_orderdate,
//! o_shippriority), the revenue being `lsum(q)`, the exact sum of `l_extendedprice * (1 - l_discount)` (coefficients
//! at scale 4) over those lineitems. `gseq(lo, hi)` lists the rows of the groups at positions `[lo, hi)`. The SQL
//! link (`bridge`) proves that the statement's groups are exactly `gseq(0, o_n)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::{OrderKey, Literal};
use crate::spec::datetime::date_from_civil;
use crate::link::expr::i128_max;
use super::common::isum::*;
use super::model::*;

verus! {

/// The statement's parameters as values: `$1` (text) and `$2` (days since 2000-01-01).
pub struct QP {
    pub seg: Seq<u8>,
    pub day: int,
}

/// The parameter values of a binding `ps` (`$1` text, `$2` date).
pub open spec fn qp_of(ps: Seq<Literal>) -> QP {
    QP {
        seg: match ps[0] { Literal::Text(b) => b, _ => Seq::empty() },
        day: match ps[1] { Literal::Date { y, m, d } => date_from_civil(y, m, d), _ => 0 },
    }
}

// ------------------------------------------------------------------------------------------------ customers

/// Customer row `c` has key `ck` and the segment.
pub open spec fn cmatch(m: M, p: QP, c: int, ck: int) -> bool {
    ckey(m, c) == ck && segtext(m, c) == p.seg
}

pub open spec fn cmatch_f(m: M, p: QP, ck: int) -> spec_fn(int) -> int {
    |c: int| if cmatch(m, p, c, ck) { 1int } else { 0int }
}

/// Number of customer rows with key `ck` and the segment (0 or 1 under the primary key).
pub open spec fn ccnt(m: M, p: QP, ck: int) -> int {
    isum(m.c_n, cmatch_f(m, p, ck))
}

// ------------------------------------------------------------------------------------------------ lineitems of an order

/// Lineitem row `j` belongs to the order at position `q` and ships after the date.
pub open spec fn lhit(m: M, p: QP, q: int, j: int) -> bool {
    lkey(m, j) == okey(m, q) && lship(m, j) > p.day
}

pub open spec fn lcnt_f(m: M, p: QP, q: int) -> spec_fn(int) -> int {
    |j: int| if lhit(m, p, q, j) { 1int } else { 0int }
}

pub open spec fn lsum_f(m: M, p: QP, q: int) -> spec_fn(int) -> int {
    |j: int| if lhit(m, p, q, j) { larg(m, j) } else { 0int }
}

pub open spec fn labs_f(m: M, p: QP, q: int) -> spec_fn(int) -> int {
    |j: int| if lhit(m, p, q, j) { abs(larg(m, j)) } else { 0int }
}

/// Number, revenue sum and absolute revenue sum of the shipped-later lineitems of the order at `q`.
pub open spec fn lcnt(m: M, p: QP, q: int) -> int { isum(m.l_n, lcnt_f(m, p, q)) }
pub open spec fn lsum(m: M, p: QP, q: int) -> int { isum(m.l_n, lsum_f(m, p, q)) }
pub open spec fn labs(m: M, p: QP, q: int) -> int { isum(m.l_n, labs_f(m, p, q)) }

// ------------------------------------------------------------------------------------------------ groups

/// The order at stored position `q` is a group of the result.
pub open spec fn good(m: M, p: QP, q: int) -> bool {
    odate(m, q) < p.day && ccnt(m, p, ocust(m, q)) > 0 && lcnt(m, p, q) > 0
}

/// The result row of the group of the order at `q`.
pub open spec fn grow(m: M, p: QP, q: int) -> Row {
    seq![Val::Int(okey(m, q)), Val::Num { coeff: lsum(m, p, q), scale: 4 }, Val::Date(odate(m, q)), Val::Int(osp(m, q))]
}

/// The rows of the groups at positions `[lo, hi)`, in position order.
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
    forall|q: int| 0 <= q < m.o_n && #[trigger] good(m, p, q) ==> labs(m, p, q) <= i128_max()
}

/// ORDER BY revenue DESC, o_orderdate.
pub open spec fn q3_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }, OrderKey { col: 2, desc: false, nulls_first: false }]
}

/// Families of the ORDER BY keys: numeric (1), date (2).
pub open spec fn q3_fams() -> Seq<int> {
    seq![1int, 2int]
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
    requires forall|q: int| lo <= q < hi ==> !#[trigger] good(m, p, q),
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
        forall|r: Row| #[trigger] gseq(m, p, lo, hi).contains(r) <==> exists|q: int| lo <= q < hi && good(m, p, q) && r == grow(m, p, q),
    decreases hi - lo,
{
    if hi > lo {
        lemma_gseq_contains(m, p, lo, hi - 1);
        let s = gseq(m, p, lo, hi - 1);
        assert forall|r: Row| #[trigger] gseq(m, p, lo, hi).contains(r) <==> exists|q: int| lo <= q < hi && good(m, p, q) && r == grow(m, p, q) by {
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
                if exists|q: int| lo <= q < hi && good(m, p, q) && r == grow(m, p, q) {
                    let q = choose|q: int| lo <= q < hi && good(m, p, q) && r == grow(m, p, q);
                    if q < hi - 1 {
                        assert(s.contains(r));
                        let i = choose|i: int| 0 <= i < s.len() && s[i] == r;
                        assert(t[i] == r);
                    }
                }
            } else {
                if exists|q: int| lo <= q < hi && good(m, p, q) && r == grow(m, p, q) {
                    let q = choose|q: int| lo <= q < hi && good(m, p, q) && r == grow(m, p, q);
                    assert(q < hi - 1);
                }
            }
        }
    }
}

/// Under the orders primary key the group rows are distinct.
pub proof fn lemma_gseq_nodup(m: M, p: QP, lo: int, hi: int)
    requires
        0 <= lo,
        hi <= m.o_n,
        forall|a: int, b: int| 0 <= a < m.o_n && 0 <= b < m.o_n && a != b ==> #[trigger] okey(m, a) != #[trigger] okey(m, b),
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
                    let q = choose|q: int| lo <= q < hi - 1 && good(m, p, q) && x == grow(m, p, q);
                    assert(grow(m, p, q)[0] == Val::Int(okey(m, q)));
                    assert(x[0] == Val::Int(okey(m, hi - 1)));
                    assert(okey(m, q) != okey(m, hi - 1));
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
