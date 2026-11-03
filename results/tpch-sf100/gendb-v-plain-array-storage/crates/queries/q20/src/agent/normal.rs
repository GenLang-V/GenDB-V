//! The statement's normal form over the stored columns, for a date window `[lo, hi)` of stored days:
//!
//! - part row `p` matches when `p_name LIKE $1` is true (`pmatch`); `in_part(v)`: some matching part has key `v`;
//! - `lcnt(a, b)` / `lsum(a, b)`: the number of lineitem rows with part key `a`, supplier key `b` and shipdate in the
//!   window, and the sum of their quantity coefficients (scale 2);
//! - partsupp row `q` qualifies (`ps_ok`) when its part is in `in_part`, it has such lineitem rows and
//!   `ps_availqty > 0.5 * SUM(l_quantity)`, i.e. `200 * ps_availqty > lsum` in coefficients;
//! - `in_supp(v)`: some qualifying partsupp row has supplier key `v`;
//! - the body's rows (`out_rows`): per supplier row, per nation row (the product's order), when the supplier is in
//!   `in_supp`, the nation keys agree and the nation's name is `$3`, the row `[s_name, s_address]`.
//!
//! Row-level forms (`ps_f`, `out_f`) state the same conditions on the rows the evaluator sees.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::fns::like::like_value;
use crate::spec::relation::product_rows;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::keep;
use crate::link::expr::ival;
use crate::agent::tables::*;
use crate::agent::params::{pat_of, nat_of};
use crate::agent::common::selection::range_sum;

verus! {

// ------------------------------------------------------------------------------------------ LIKE on part names

/// The escape string of `LIKE` (one backslash).
pub open spec fn esc() -> Seq<u8> { seq![92u8] }

/// `name LIKE pat` (escape backslash) on text values.
pub open spec fn like_res(name: Seq<u8>, pat: Seq<u8>) -> Result<Val, SqlError> {
    like_value(Val::Text(name), Val::Text(pat), Val::Text(esc()))
}

pub open spec fn like_ok(name: Seq<u8>, pat: Seq<u8>) -> bool { like_res(name, pat) is Ok }

pub open spec fn like_true(name: Seq<u8>, pat: Seq<u8>) -> bool { like_res(name, pat) == Ok::<Val, SqlError>(Val::Bool(true)) }

/// No part name's `LIKE` raises.
pub open spec fn likes_ok(sv: StoresView, ps: Seq<Literal>) -> bool {
    forall|p: int| 0 <= p < n_p(sv) ==> like_ok(#[trigger] pname(sv, p), pat_of(ps))
}

/// Part row `p` matches `$1`.
pub open spec fn pmatch(sv: StoresView, ps: Seq<Literal>, p: int) -> bool { like_true(pname(sv, p), pat_of(ps)) }

/// Some matching part row has key `v`.
pub open spec fn in_part(sv: StoresView, ps: Seq<Literal>, v: int) -> bool {
    exists|p: int| 0 <= p < n_p(sv) && #[trigger] pk(sv)[p] as int == v && pmatch(sv, ps, p)
}

// ------------------------------------------------------------------------------------------ lineitem sums

/// Lineitem row `l` has part key `a`, supplier key `b` and its shipdate in `[lo, hi)`.
pub open spec fn lhit(sv: StoresView, lo: int, hi: int, a: int, b: int, l: int) -> bool {
    lpk(sv)[l] as int == a && lsk(sv)[l] as int == b && lo <= lsd(sv)[l] && lsd(sv)[l] < hi
}

pub open spec fn lcnt_term(sv: StoresView, lo: int, hi: int, a: int, b: int) -> spec_fn(int) -> int {
    |l: int| if lhit(sv, lo, hi, a, b, l) { 1int } else { 0int }
}

pub open spec fn lsum_term(sv: StoresView, lo: int, hi: int, a: int, b: int) -> spec_fn(int) -> int {
    |l: int| if lhit(sv, lo, hi, a, b, l) { lqt(sv)[l] as int } else { 0int }
}

/// The number of hits of `(a, b)` and the sum of their quantity coefficients (scale 2).
pub open spec fn lcnt(sv: StoresView, lo: int, hi: int, a: int, b: int) -> int { range_sum(0, n_l(sv) as int, lcnt_term(sv, lo, hi, a, b)) }
pub open spec fn lsum(sv: StoresView, lo: int, hi: int, a: int, b: int) -> int { range_sum(0, n_l(sv) as int, lsum_term(sv, lo, hi, a, b)) }

// ------------------------------------------------------------------------------------------ partsupp and suppliers

/// A partsupp key pair and availability qualify.
pub open spec fn ps_cond(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, a: int, b: int, aq: int) -> bool {
    in_part(sv, ps, a) && lcnt(sv, lo, hi, a, b) > 0 && 200 * aq > lsum(sv, lo, hi, a, b)
}

/// Partsupp row `q` qualifies.
pub open spec fn ps_ok(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, q: int) -> bool {
    ps_cond(sv, ps, lo, hi, pspk(sv)[q] as int, pssk(sv)[q] as int, psaq(sv)[q] as int)
}

/// Some qualifying partsupp row has supplier key `v`.
pub open spec fn in_supp(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, v: int) -> bool {
    exists|q: int| 0 <= q < n_ps(sv) && #[trigger] ps_ok(sv, ps, lo, hi, q) && pssk(sv)[q] as int == v
}

/// `ps_ok` on a partsupp row as the evaluator sees it.
pub open spec fn ps_f(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> spec_fn(Row) -> bool {
    |r: Row| ps_cond(sv, ps, lo, hi, ival(r[0]), ival(r[1]), ival(r[2]))
}

/// The outer condition on a joined `supplier ++ nation` row.
pub open spec fn out_f(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> spec_fn(Row) -> bool {
    |x: Row| in_supp(sv, ps, lo, hi, ival(x[0])) && x[3] == x[7] && x[8] == Val::Text(nat_of(ps))
}

/// The output columns `s_name, s_address` of a joined row.
pub open spec fn out_proj(x: Row) -> Row { seq![x[1], x[2]] }

/// The body's rows.
pub open spec fn out_rows(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> Seq<Row> {
    keep(product_rows(supp_rows(sv), nat_rows(sv)), out_f(sv, ps, lo, hi)).map_values(|x: Row| out_proj(x))
}

} // verus!
