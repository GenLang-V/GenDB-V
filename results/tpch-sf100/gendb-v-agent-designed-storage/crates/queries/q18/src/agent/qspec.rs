//! The Q18 result over the model (`model`). For an order key `k`, `kcnt(k)` / `ksum(k)` are the number of lineitem
//! rows with `l_orderkey = k` and the exact sum of their l_quantity coefficients (scale 2); the IN subquery keeps `k`
//! exactly when `big(k)`: it has a lineitem and that sum is above `$1` (`ksum > 100 * $1`, `$1` at scale 0). The
//! order at stored position `q` is a group exactly when `good(q)`: its key is big and its customer exists. Its row is
//! `grow(q)` = (c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice, SUM(l_quantity)). `gseq(lo, hi)` lists
//! the rows of the groups at positions `[lo, hi)`. The SQL link (`sqllink`, `answer`) proves that the statement's
//! groups are exactly `gseq(0, o_n)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::{OrderKey, Literal};
use super::common::isum::*;
use super::model::*;

verus! {

/// The statement's parameter as a value: `$1` (an int4, compared with numeric sums at scale 0).
pub struct QP {
    pub lim: int,
}

/// The parameter value of a binding `ps`.
pub open spec fn qp_of(ps: Seq<Literal>) -> QP {
    QP { lim: match ps[0] { Literal::Int { v, .. } => v, _ => 0 } }
}

/// The HAVING bound as a coefficient at scale 2.
pub open spec fn thr(p: QP) -> int { 100 * p.lim }

// ------------------------------------------------------------------------------------------------ lineitems of a key

pub open spec fn kcnt_f(m: M, k: int) -> spec_fn(int) -> int {
    |j: int| if lkey(m, j) == k { 1int } else { 0int }
}

pub open spec fn ksum_f(m: M, k: int) -> spec_fn(int) -> int {
    |j: int| if lkey(m, j) == k { lqty(m, j) } else { 0int }
}

pub open spec fn kabs_f(m: M, k: int) -> spec_fn(int) -> int {
    |j: int| if lkey(m, j) == k { abs(lqty(m, j)) } else { 0int }
}

/// Number, quantity sum and absolute quantity sum of the lineitem rows of order key `k`.
pub open spec fn kcnt(m: M, k: int) -> int { isum(m.l_n, kcnt_f(m, k)) }
pub open spec fn ksum(m: M, k: int) -> int { isum(m.l_n, ksum_f(m, k)) }
pub open spec fn kabs(m: M, k: int) -> int { isum(m.l_n, kabs_f(m, k)) }

/// The IN subquery's set: keys with a lineitem whose quantity sum is above `$1`.
pub open spec fn big(m: M, p: QP, k: int) -> bool {
    kcnt(m, k) > 0 && ksum(m, k) > thr(p)
}

// ------------------------------------------------------------------------------------------------ customers

pub open spec fn cmatch_f(m: M, ck: int) -> spec_fn(int) -> int {
    |c: int| if ckey(m, c) == ck { 1int } else { 0int }
}

/// Number of customer rows with key `ck` (0 or 1 under the primary key).
pub open spec fn ccnt(m: M, ck: int) -> int { isum(m.c_n, cmatch_f(m, ck)) }

/// The customer row with key `ck` (when there is one).
pub open spec fn cpos(m: M, ck: int) -> int {
    choose|c: int| 0 <= c < m.c_n && #[trigger] ckey(m, c) == ck
}

// ------------------------------------------------------------------------------------------------ groups

/// The order at stored position `q` is a group of the result.
pub open spec fn good(m: M, p: QP, q: int) -> bool {
    big(m, p, okey(m, q)) && ccnt(m, ocust(m, q)) > 0
}

/// The result row of the group of the order at `q`.
pub open spec fn grow(m: M, p: QP, q: int) -> Row {
    seq![
        Val::Text(cname(m, cpos(m, ocust(m, q)))),
        Val::Int(ocust(m, q)),
        Val::Int(okey(m, q)),
        Val::Date(odate(m, q)),
        Val::Num { coeff: otp(m, q), scale: 2 },
        Val::Num { coeff: ksum(m, okey(m, q)), scale: 2 },
    ]
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

/// ORDER BY o_totalprice DESC, o_orderdate.
pub open spec fn q18_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 4, desc: true, nulls_first: true }, OrderKey { col: 3, desc: false, nulls_first: false }]
}

/// Families of the ORDER BY keys: numeric (1), date (2).
pub open spec fn q18_fams() -> Seq<int> {
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

/// Under the orders primary key the group rows are distinct (column 2 is the order key).
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
                    assert(grow(m, p, q)[2] == Val::Int(okey(m, q)));
                    assert(x[2] == Val::Int(okey(m, hi - 1)));
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

/// Under the customer primary key a customer key has at most one row, and `cpos` is it.
pub proof fn lemma_ccnt(m: M, ck: int)
    requires
        forall|a: int, b: int| 0 <= a < m.c_n && 0 <= b < m.c_n && a != b ==> #[trigger] ckey(m, a) != #[trigger] ckey(m, b),
    ensures
        0 <= ccnt(m, ck) <= 1,
        ccnt(m, ck) > 0 <==> exists|c: int| 0 <= c < m.c_n && #[trigger] ckey(m, c) == ck,
        ccnt(m, ck) > 0 ==> 0 <= cpos(m, ck) < m.c_n && ckey(m, cpos(m, ck)) == ck,
        forall|c: int| 0 <= c < m.c_n && #[trigger] ckey(m, c) == ck ==> c == cpos(m, ck),
{
    let f = cmatch_f(m, ck);
    if exists|c: int| 0 <= c < m.c_n && #[trigger] ckey(m, c) == ck {
        let c0 = cpos(m, ck);
        assert(0 <= c0 < m.c_n && ckey(m, c0) == ck);
        assert forall|c: int| 0 <= c < m.c_n && c != c0 implies #[trigger] f(c) == 0 by {
            assert(ckey(m, c) != ckey(m, c0));
        }
        lemma_isum_single(m.c_n, f, c0);
        assert forall|c: int| 0 <= c < m.c_n && #[trigger] ckey(m, c) == ck implies c == cpos(m, ck) by {
            if c != c0 {
                assert(ckey(m, c) != ckey(m, c0));
            }
        }
    } else {
        assert forall|c: int| 0 <= c < m.c_n implies #[trigger] f(c) == 0 by {}
        lemma_isum_zero(m.c_n, f);
    }
}

} // verus!
