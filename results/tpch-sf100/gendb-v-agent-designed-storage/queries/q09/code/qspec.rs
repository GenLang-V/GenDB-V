//! The Q9 result over the model (`model`). For the pattern `pat` ($1), part row `c` matches when
//! `p_name LIKE pat ESCAPE '\'` is true (`pmatch`). A stored lineitem row `j` joins (`jok`) when the part of its
//! `l_partkey` matches and its supplier, the supplier's nation, the partsupp row of `(l_partkey, l_suppkey)` and the
//! order of `l_orderkey` exist (the rows holding those keys, `model::*pos`); it then contributes `jamt(j)` (scale 4) to
//! the group of its supplier's nation row `jn(j)` and its order's year `jyear(j)`. Per (nation row, year) the count,
//! sum and absolute sum over a row range `[a, b)` are `dsum`s of the per-row terms (`cnt_f`, `sum_f`, `abs_f`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::Literal;
use crate::spec::fns::like::like_value;
use super::common::isum::*;
use super::model::*;
use super::year::year_of;

verus! {

/// The statement's parameter as a value: the LIKE pattern `$1`.
pub struct QP {
    pub pat: Seq<u8>,
}

pub open spec fn qp_of(ps: Seq<Literal>) -> QP {
    QP { pat: match ps[0] { Literal::Text(b) => b, _ => Seq::empty() } }
}

/// The escape string of `LIKE $1` (the frontend supplies `\`).
pub open spec fn esc() -> Seq<u8> {
    seq![92u8]
}

/// `p_name LIKE $1` on part row `c`.
pub open spec fn plike(m: M, p: QP, c: int) -> Result<Val, SqlError> {
    like_value(Val::Text(pname(m, c)), Val::Text(p.pat), Val::Text(esc()))
}

/// Part row `c` matches the pattern.
pub open spec fn pmatch(m: M, p: QP, c: int) -> bool {
    plike(m, p, c) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// No part name makes `LIKE` raise.
pub open spec fn like_total(m: M, p: QP) -> bool {
    forall|c: int| 0 <= c < m.p_n ==> #[trigger] plike(m, p, c) is Ok
}

// ------------------------------------------------------------------------------------------------ joined rows

/// The part, supplier, partsupp row and order of lineitem row `j` (`*_n` when there is none).
pub open spec fn lc(m: M, j: int) -> int { ppos(m, lpk(m, j)) }
pub open spec fn ls(m: M, j: int) -> int { spos(m, lsk(m, j)) }
pub open spec fn lt(m: M, j: int) -> int { tpos(m, lpk(m, j), lsk(m, j)) }
pub open spec fn lq(m: M, j: int) -> int { opos(m, lok(m, j)) }

/// The nation row of supplier row `s` (`n_n` when there is none).
pub open spec fn sn(m: M, s: int) -> int { npos(m, snk(m, s)) }

/// The nation row of lineitem row `j`'s supplier.
pub open spec fn jn(m: M, j: int) -> int { sn(m, ls(m, j)) }

/// Lineitem row `j` joins a matching part, its supplier and nation, its partsupp row and its order.
pub open spec fn jok(m: M, p: QP, j: int) -> bool {
    &&& lc(m, j) < m.p_n && pmatch(m, p, lc(m, j))
    &&& ls(m, j) < m.s_n && jn(m, j) < m.n_n
    &&& lt(m, j) < m.t_n
    &&& lq(m, j) < m.o_n
}

/// The order year of lineitem row `j`.
pub open spec fn jyear(m: M, j: int) -> int { year_of(odate(m, lq(m, j))) }

/// `l_extendedprice * (1 - l_discount) - ps_supplycost * l_quantity` of lineitem row `j` (coefficient, scale 4).
pub open spec fn jamt(m: M, j: int) -> int {
    lprice(m, j) * (100 - ldisc(m, j)) - tcost(m, lt(m, j)) * lqty(m, j)
}

/// Row `j` contributes to the cell (nation row `n`, year `y`).
pub open spec fn jhit(m: M, p: QP, j: int, n: int, y: int) -> bool {
    jok(m, p, j) && jn(m, j) == n && jyear(m, j) == y
}

pub open spec fn cnt_f(m: M, p: QP, n: int, y: int) -> spec_fn(int) -> int {
    |j: int| if jhit(m, p, j, n, y) { 1int } else { 0int }
}

pub open spec fn sum_f(m: M, p: QP, n: int, y: int) -> spec_fn(int) -> int {
    |j: int| if jhit(m, p, j, n, y) { jamt(m, j) } else { 0int }
}

pub open spec fn abs_f(m: M, p: QP, n: int, y: int) -> spec_fn(int) -> int {
    |j: int| if jhit(m, p, j, n, y) { abs(jamt(m, j)) } else { 0int }
}

/// The sum of `f` over the rows `[a, b)`.
pub open spec fn dsum(f: spec_fn(int) -> int, a: int, b: int) -> int {
    isum(b, f) - isum(a, f)
}

/// The terms of a cell at one row.
pub proof fn lemma_terms_at(m: M, p: QP, n: int, y: int, j: int)
    ensures
        cnt_f(m, p, n, y)(j) == if jhit(m, p, j, n, y) { 1int } else { 0int },
        sum_f(m, p, n, y)(j) == if jhit(m, p, j, n, y) { jamt(m, j) } else { 0int },
        abs_f(m, p, n, y)(j) == if jhit(m, p, j, n, y) { abs(jamt(m, j)) } else { 0int },
{
}

/// One more row.
pub proof fn lemma_dsum_step(f: spec_fn(int) -> int, a: int, b: int)
    requires 0 <= b,
    ensures dsum(f, a, b + 1) == dsum(f, a, b) + f(b),
{
    lemma_isum_step(b, f);
}

/// Adjacent ranges add.
pub proof fn lemma_dsum_split(f: spec_fn(int) -> int, a: int, b: int, c: int)
    ensures dsum(f, a, c) == dsum(f, a, b) + dsum(f, b, c),
{
}

/// The empty range.
pub proof fn lemma_dsum_empty(f: spec_fn(int) -> int, a: int)
    ensures dsum(f, a, a) == 0,
{
}

} // verus!
