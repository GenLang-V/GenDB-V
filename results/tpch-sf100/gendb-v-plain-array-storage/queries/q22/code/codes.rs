//! Country-code group ids of customer rows (`normal::grp` of `SUBSTRING(c_phone, 1, 2)` as a byte: the first
//! parameter slot equal to the code, `NONE` = 7 when none).
//!
//! - `fast_code` (worker-safe): a phone starting with two ASCII bytes followed by the end or a character start
//!   has those two bytes as its code (`common::prefix2`); their group id is read from a 16384-entry table indexed
//!   by `128 * b0 + b1` (`lut_ok`, built by `build_lut`). Any other phone gives `SLOW`.
//! - `slow_code` (calling thread, allocates): the general `SUBSTRING` of the verified evaluator, then the slots
//!   compared byte by byte.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::{Literal, ScalarFn};
use crate::spec::fns::substring::*;
use crate::exec::value::*;
use crate::exec::fns::substring::exec_substring;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_params::Params;
use crate::agent::common::prefix2::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::cols::*;

verus! {

/// Group id of a row whose code matches no parameter.
pub const NONE: u8 = 7;
/// Group id of a row whose code the fast test cannot decide.
pub const SLOW: u8 = 8;

/// The group id of customer row `i` as a byte.
pub open spec fn gid(sv: StoresView, ps: Seq<Literal>, i: int) -> u8 { grp(ps, code_of(sv, i)) as u8 }

/// The two bytes of table index `k`.
pub open spec fn key_text(k: int) -> Seq<u8> { seq![(k / 128) as u8, (k % 128) as u8] }

/// Entry `128 * b0 + b1` is the group id of the code `b0 b1` (both ASCII).
pub open spec fn lut_ok(lut: Seq<u8>, ps: Seq<Literal>) -> bool {
    &&& lut.len() == 16384
    &&& forall|k: int| 0 <= k < 16384 ==> #[trigger] lut[k] == grp(ps, key_text(k)) as u8
}

/// The text of parameter slot `k`.
#[verifier::spinoff_prover]
pub fn param_at(params: &Params, k: usize) -> (p: &'static [u8])
    requires k < 7,
    ensures p@ == pt(params@, k as int),
{
    if k == 0 { params.p0 } else if k == 1 { params.p1 } else if k == 2 { params.p2 } else if k == 3 { params.p3 }
    else if k == 4 { params.p4 } else if k == 5 { params.p5 } else { params.p6 }
}

/// Whether the text `p` is exactly the two bytes `b0 b1`.
#[verifier::spinoff_prover]
fn pair_eq(p: &[u8], b0: u8, b1: u8) -> (r: bool)
    ensures r == (p@ == seq![b0, b1]),
{
    if p.len() != 2 {
        return false;
    }
    let r = p[0] == b0 && p[1] == b1;
    proof {
        if r { assert(p@ =~= seq![b0, b1]); }
        if p@ == seq![b0, b1] { assert(p@[0] == b0 && p@[1] == b1); }
    }
    r
}

/// The group id of the code `b0 b1`.
#[verifier::spinoff_prover]
fn grp_pair(params: &Params, b0: u8, b1: u8) -> (g: u8)
    ensures g == grp(params@, seq![b0, b1]) as u8,
{
    let ghost t = seq![b0, b1];
    if pair_eq(param_at(params, 0), b0, b1) { 0 }
    else if pair_eq(param_at(params, 1), b0, b1) { 1 }
    else if pair_eq(param_at(params, 2), b0, b1) { 2 }
    else if pair_eq(param_at(params, 3), b0, b1) { 3 }
    else if pair_eq(param_at(params, 4), b0, b1) { 4 }
    else if pair_eq(param_at(params, 5), b0, b1) { 5 }
    else if pair_eq(param_at(params, 6), b0, b1) { 6 }
    else { NONE }
}

/// The group-id table of all two-byte ASCII codes.
#[verifier::spinoff_prover]
pub fn build_lut(params: &Params) -> (lut: Vec<u8>)
    ensures lut_ok(lut@, params@),
{
    let mut lut: Vec<u8> = Vec::with_capacity(16384);
    let mut k: usize = 0;
    while k < 16384
        invariant
            k <= 16384,
            lut@.len() == k,
            forall|j: int| 0 <= j < k ==> #[trigger] lut@[j] == grp(params@, key_text(j)) as u8,
        decreases 16384 - k,
    {
        let b0 = (k / 128) as u8;
        let b1 = (k % 128) as u8;
        let g = grp_pair(params, b0, b1);
        proof { assert(key_text(k as int) == seq![b0, b1]); }
        lut.push(g);
        k = k + 1;
    }
    lut
}

/// The group id of customer row `i` by the fast test, or `SLOW`.
#[verifier::spinoff_prover]
pub fn fast_code(c: &Cols, lut: &Vec<u8>, i: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (g: u8)
    requires cols_ok(*c, sv), lut_ok(lut@, ps), i < c.nc,
    ensures g == SLOW || g == gid(sv, ps, i as int),
    no_unwind
{
    proof { lemma_phone_range(*c, sv, i as int); }
    let a = c.poffs[i];
    let b = c.poffs[i + 1];
    if b - a < 2 {
        return SLOW;
    }
    let au = a as usize;
    let bu = b as usize;
    let b0 = c.pbytes[au];
    let b1 = c.pbytes[au + 1];
    if b0 >= 0x80 || b1 >= 0x80 {
        return SLOW;
    }
    let ghost ph = phone(sv, i as int);
    proof {
        assert(ph.len() == bu - au);
        assert(ph[0] == b0 && ph[1] == b1);
    }
    if bu - au > 2 {
        let b2 = c.pbytes[au + 2];
        if 0x80 <= b2 && b2 < 0xC0 {
            return SLOW;
        }
        proof { assert(ph[2] == b2); assert(!crate::spec::chars::is_cont(ph[2])); }
    }
    proof {
        lemma_prefix2_ascii(ph);
        assert(ph.subrange(0, 2) =~= seq![b0, b1]);
    }
    let key = (b0 as usize) * 128 + (b1 as usize);
    proof {
        assert(key / 128 == b0 as usize && key % 128 == b1 as usize);
        assert(key_text(key as int) =~= seq![b0, b1]);
    }
    lut[key]
}

/// Whether two byte strings are equal.
#[verifier::spinoff_prover]
fn vec_slice_eq(a: &Vec<u8>, b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut j: usize = 0;
    while j < a.len()
        invariant j <= a@.len(), a@.len() == b@.len(), forall|m: int| 0 <= m < j ==> a@[m] == b@[m],
        decreases a@.len() - j,
    {
        if a[j] != b[j] {
            return false;
        }
        j = j + 1;
    }
    proof { assert(a@ =~= b@); }
    true
}

/// The group id of a code `t`.
#[verifier::spinoff_prover]
fn grp_vec(params: &Params, t: &Vec<u8>) -> (g: u8)
    ensures g == grp(params@, t@) as u8,
{
    if vec_slice_eq(t, param_at(params, 0)) { 0 }
    else if vec_slice_eq(t, param_at(params, 1)) { 1 }
    else if vec_slice_eq(t, param_at(params, 2)) { 2 }
    else if vec_slice_eq(t, param_at(params, 3)) { 3 }
    else if vec_slice_eq(t, param_at(params, 4)) { 4 }
    else if vec_slice_eq(t, param_at(params, 5)) { 5 }
    else if vec_slice_eq(t, param_at(params, 6)) { 6 }
    else { NONE }
}

/// `SUBSTRING(b, 1, 2)` on its evaluated arguments is the two-character prefix.
#[verifier::spinoff_prover]
proof fn lemma_substring12(b: Seq<u8>)
    ensures apply_substring(ScalarFn::Substring3, seq![Val::Text(b), Val::Int(1), Val::Int(2)]) == Ok::<Val, SqlError>(Val::Text(prefix2(b))),
{
    reveal(prefix2);
    let vs = seq![Val::Text(b), Val::Int(1), Val::Int(2)];
    assert(!(exists|k: int| 0 <= k < vs.len() && #[trigger] vs[k] is Null)) by {
        assert forall|k: int| 0 <= k < vs.len() implies !(#[trigger] vs[k] is Null) by {
            if k == 0 {} else if k == 1 {} else {}
        }
    }
}

/// The group id of customer row `i` by the general `SUBSTRING` (allocates; calling thread only).
#[verifier::spinoff_prover]
pub fn slow_code(c: &Cols, params: &Params, i: usize, Ghost(sv): Ghost<StoresView>) -> (g: u8)
    requires cols_ok(*c, sv), i < c.nc,
    ensures g == gid(sv, params@, i as int),
{
    proof { lemma_phone_range(*c, sv, i as int); }
    let a = c.poffs[i] as usize;
    let b = c.poffs[i + 1] as usize;
    let ghost ph = phone(sv, i as int);
    let mut v: Vec<u8> = Vec::new();
    let mut j = a;
    while j < b
        invariant a <= j <= b, b <= c.nbytes, c.nbytes == c.pbytes@.len(), v@ == c.pbytes@.subrange(a as int, j as int),
        decreases b - j,
    {
        v.push(c.pbytes[j]);
        j = j + 1;
        proof { assert(v@ =~= c.pbytes@.subrange(a as int, j as int)); }
    }
    assert(v@ == ph);
    let mut args: Vec<EVal> = Vec::new();
    args.push(EVal::Text(v));
    args.push(EVal::Int(1));
    args.push(EVal::Int(2));
    proof {
        assert(view_row(args@) =~= seq![Val::Text(ph), Val::Int(1), Val::Int(2)]);
        assert(crate::exec::domain::row_ts_ok(view_row(args@)));
        lemma_substring12(ph);
    }
    let r = exec_substring(ScalarFn::Substring3, &args);
    match r {
        Ok(Ok(EVal::Text(t))) => {
            assert(t@ == prefix2(ph));
            grp_vec(params, &t)
        },
        _ => {
            proof {
                assert(fits_substring(ScalarFn::Substring3, view_row(args@)));
            }
            NONE
        },
    }
}

} // verus!
