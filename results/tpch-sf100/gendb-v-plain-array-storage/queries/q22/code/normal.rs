//! The statement's normal form over the stored columns and the binding `ps` (the seven country-code texts).
//!
//! - `code_of(i)`: `SUBSTRING(c_phone, 1, 2)` of customer row `i`; `code_hit` says whether a code is one of the
//!   seven parameters, and `grp` gives the first parameter slot equal to it (7 when none): the group id the scans
//!   compute. Two codes that hit have the same group id exactly when they are equal (`lemma_grp_eq`).
//! - The AVG population: the rows whose code hits and whose balance is positive; `avg_n` of them with balance sum
//!   `avg_s` (coefficients at scale 2). AVG exceeds a balance exactly when the balance exceeds `thr`
//!   (`common::avg_threshold`).
//! - `qual(i)`: the outer WHERE condition (code hits, the AVG population is non-empty, balance above AVG, and no
//!   orders row with the row's key); per group id `g`, the qualifying rows' count `gcnt` and balance sum `gsm`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::link::expr::{ival, tval};
use crate::agent::common::rsum::*;
use crate::agent::common::prefix2::prefix2;
use crate::agent::common::avg_threshold::avg_thr;
use crate::agent::tables::*;

verus! {

/// The text of parameter slot `k`.
pub open spec fn pt(ps: Seq<Literal>, k: int) -> Seq<u8> { ps[k]->Text_0 }

/// The binding has seven text parameters.
pub open spec fn ps_ok(ps: Seq<Literal>) -> bool {
    &&& ps.len() == 7
    &&& forall|k: int| 0 <= k < 7 ==> #[trigger] ps[k] is Text
}

/// The code `t` is one of the seven parameters (the OR chain of the IN list).
pub open spec fn code_hit(ps: Seq<Literal>, t: Seq<u8>) -> bool {
    (((((t == pt(ps, 0) || t == pt(ps, 1)) || t == pt(ps, 2)) || t == pt(ps, 3)) || t == pt(ps, 4)) || t == pt(ps, 5))
        || t == pt(ps, 6)
}

/// The first parameter slot equal to `t`, or 7.
pub open spec fn grp(ps: Seq<Literal>, t: Seq<u8>) -> int {
    if t == pt(ps, 0) { 0 } else if t == pt(ps, 1) { 1 } else if t == pt(ps, 2) { 2 } else if t == pt(ps, 3) { 3 }
    else if t == pt(ps, 4) { 4 } else if t == pt(ps, 5) { 5 } else if t == pt(ps, 6) { 6 } else { 7 }
}

/// A code hits exactly when it has a group id below 7, and then it is that slot's text.
#[verifier::spinoff_prover]
pub proof fn lemma_grp(ps: Seq<Literal>, t: Seq<u8>)
    ensures
        0 <= grp(ps, t) <= 7,
        code_hit(ps, t) == (grp(ps, t) < 7),
        grp(ps, t) < 7 ==> t == pt(ps, grp(ps, t)),
        forall|k: int| 0 <= k < grp(ps, t) ==> t != #[trigger] pt(ps, k),
{
}

/// Hitting codes with the same group id are equal.
#[verifier::spinoff_prover]
pub proof fn lemma_grp_eq(ps: Seq<Literal>, t: Seq<u8>, u: Seq<u8>)
    requires code_hit(ps, t), code_hit(ps, u),
    ensures (grp(ps, t) == grp(ps, u)) == (t == u),
{
    lemma_grp(ps, t);
    lemma_grp(ps, u);
}

/// The country code of customer row `i`.
pub open spec fn code_of(sv: StoresView, i: int) -> Seq<u8> { prefix2(phone(sv, i)) }

// ------------------------------------------------------------------------------------------ the AVG population

/// Row `i` is in the AVG subquery's population: its code hits and its balance is positive.
pub open spec fn avg_in(sv: StoresView, ps: Seq<Literal>, i: int) -> bool {
    code_hit(ps, code_of(sv, i)) && bal(sv)[i] > 0
}

pub open spec fn avg_cnt_term(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> int {
    |i: int| if avg_in(sv, ps, i) { 1int } else { 0int }
}

pub open spec fn avg_sum_term(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> int {
    |i: int| if avg_in(sv, ps, i) { bal(sv)[i] as int } else { 0int }
}

/// The AVG population's size and balance sum (scale 2).
pub open spec fn avg_n(sv: StoresView, ps: Seq<Literal>) -> int { range_sum(0, n_c(sv) as int, avg_cnt_term(sv, ps)) }
pub open spec fn avg_s(sv: StoresView, ps: Seq<Literal>) -> int { range_sum(0, n_c(sv) as int, avg_sum_term(sv, ps)) }

/// The integer threshold: a balance exceeds the AVG exactly when it exceeds `thr`.
pub open spec fn thr(sv: StoresView, ps: Seq<Literal>) -> int { avg_thr(avg_s(sv, ps), 2, avg_n(sv, ps)) }

// ------------------------------------------------------------------------------------------ the outer condition

/// Some orders row has customer key `k`.
pub open spec fn has_ord(sv: StoresView, k: int) -> bool {
    exists|j: int| 0 <= j < n_o(sv) && #[trigger] ock(sv)[j] as int == k
}

/// Customer row `i` satisfies the outer WHERE condition.
pub open spec fn qual(sv: StoresView, ps: Seq<Literal>, i: int) -> bool {
    &&& code_hit(ps, code_of(sv, i))
    &&& avg_n(sv, ps) > 0
    &&& bal(sv)[i] > thr(sv, ps)
    &&& !has_ord(sv, cck(sv)[i] as int)
}

/// The same condition on a customer row value (as the statement's filter sees it).
pub open spec fn qrow(sv: StoresView, ps: Seq<Literal>) -> spec_fn(Row) -> bool {
    |r: Row| code_hit(ps, prefix2(tval(r[4]))) && avg_n(sv, ps) > 0 && ival(r[5]) > thr(sv, ps)
        && !has_ord(sv, ival(r[0]))
}

/// Per group id: the qualifying rows of that group, counted and their balances summed.
pub open spec fn gcnt_term(sv: StoresView, ps: Seq<Literal>, g: int) -> spec_fn(int) -> int {
    |i: int| if qual(sv, ps, i) && grp(ps, code_of(sv, i)) == g { 1int } else { 0int }
}

pub open spec fn gsum_term(sv: StoresView, ps: Seq<Literal>, g: int) -> spec_fn(int) -> int {
    |i: int| if qual(sv, ps, i) && grp(ps, code_of(sv, i)) == g { bal(sv)[i] as int } else { 0int }
}

pub open spec fn gcnt(sv: StoresView, ps: Seq<Literal>, g: int) -> int { range_sum(0, n_c(sv) as int, gcnt_term(sv, ps, g)) }
pub open spec fn gsm(sv: StoresView, ps: Seq<Literal>, g: int) -> int { range_sum(0, n_c(sv) as int, gsum_term(sv, ps, g)) }

/// The row value of customer row `i` satisfies `qrow` exactly when the row qualifies.
#[verifier::spinoff_prover]
pub proof fn lemma_qrow(sv: StoresView, ps: Seq<Literal>, i: int)
    requires 0 <= i < n_c(sv),
    ensures qrow(sv, ps)(cust_rows(sv)[i]) == qual(sv, ps, i),
{
    lemma_cust_row(sv, i);
}

} // verus!
