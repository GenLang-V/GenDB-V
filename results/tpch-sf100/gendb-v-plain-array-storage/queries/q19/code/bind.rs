//! The parameters as the scan uses them (`Bind`): per branch `k`, the brand bytes `pb(ps, k)` with their length, and
//! the quantity window `[100 pv, 100 (pv + 10)]` on scale-2 coefficients. `pv + 10` is int4 arithmetic in the
//! statement: when it leaves int4 for some branch (`!adds_ok`), `make_bind` reports it, and the WHERE condition
//! fails with `NumericValueOutOfRange` on every joined row. Brand parameters of 8 bytes (TPC-H's `Brand#MN`) are
//! also kept as little-endian words (`pack8_spec`), so the part pass compares a stored brand of 8 bytes with one
//! word comparison (`load8`, `lemma_pack8_eq`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::agent::line::*;

verus! {

/// The bound parameters.
#[derive(Clone, Copy)]
pub struct Bind {
    pub b0: &'static [u8],
    pub n0: usize,
    pub b1: &'static [u8],
    pub n1: usize,
    pub b2: &'static [u8],
    pub n2: usize,
    pub lo0: i128,
    pub hi0: i128,
    pub lo1: i128,
    pub hi1: i128,
    pub lo2: i128,
    pub hi2: i128,
    /// The brand parameters of length 8 as little-endian words (`pack8`), with `e_k`: brand `k` has length 8.
    pub k0: u64,
    pub k1: u64,
    pub k2: u64,
    pub e0: bool,
    pub e1: bool,
    pub e2: bool,
}

/// `pv + 10` stays inside int4 for every branch.
pub open spec fn adds_ok(ps: Seq<Literal>) -> bool {
    pv(ps, 0) + 10 <= 0x7fff_ffff && pv(ps, 1) + 10 <= 0x7fff_ffff && pv(ps, 2) + 10 <= 0x7fff_ffff
}

/// The bound parameters are the statement's.
pub open spec fn bind_ok(x: Bind, ps: Seq<Literal>) -> bool {
    &&& x.b0@ == pb(ps, 0) && x.n0 == x.b0@.len()
    &&& x.b1@ == pb(ps, 1) && x.n1 == x.b1@.len()
    &&& x.b2@ == pb(ps, 2) && x.n2 == x.b2@.len()
    &&& x.lo0 as int == 100 * pv(ps, 0) && x.hi0 as int == 100 * (pv(ps, 0) + 10)
    &&& x.lo1 as int == 100 * pv(ps, 1) && x.hi1 as int == 100 * (pv(ps, 1) + 10)
    &&& x.lo2 as int == 100 * pv(ps, 2) && x.hi2 as int == 100 * (pv(ps, 2) + 10)
    &&& x.e0 == (pb(ps, 0).len() == 8) && (x.e0 ==> x.k0 == pack8_spec(pb(ps, 0)))
    &&& x.e1 == (pb(ps, 1).len() == 8) && (x.e1 ==> x.k1 == pack8_spec(pb(ps, 1)))
    &&& x.e2 == (pb(ps, 2).len() == 8) && (x.e2 ==> x.k2 == pack8_spec(pb(ps, 2)))
}

/// Eight bytes as a little-endian word.
pub open spec fn pack8_spec(b: Seq<u8>) -> u64 {
    (b[0] as u64) | ((b[1] as u64) << 8u64) | ((b[2] as u64) << 16u64) | ((b[3] as u64) << 24u64)
        | ((b[4] as u64) << 32u64) | ((b[5] as u64) << 40u64) | ((b[6] as u64) << 48u64) | ((b[7] as u64) << 56u64)
}

/// The eight bytes `b[s..s + 8]` as a little-endian word (one bounds check: the bytes are read from an 8-byte
/// subslice, so the compiler can merge them into one load).
#[inline(always)]
pub fn load8(b: &[u8], s: usize) -> (v: u64)
    requires s + 8 <= b@.len(),
    ensures v == pack8_spec(b@.subrange(s as int, s + 8)),
    no_unwind
{
    let (_, tail) = b.split_at(s);
    let (w, _) = tail.split_at(8);
    proof {
        assert(w@ =~= b@.subrange(s as int, s + 8));
    }
    (w[0] as u64) | ((w[1] as u64) << 8u64) | ((w[2] as u64) << 16u64) | ((w[3] as u64) << 24u64)
        | ((w[4] as u64) << 32u64) | ((w[5] as u64) << 40u64) | ((w[6] as u64) << 48u64)
        | ((w[7] as u64) << 56u64)
}

/// Words of eight bytes are equal exactly when the bytes are.
pub proof fn lemma_pack8_eq(a: Seq<u8>, b: Seq<u8>)
    requires a.len() == 8, b.len() == 8,
    ensures (pack8_spec(a) == pack8_spec(b)) == (a == b),
{
    let (a0, a1, a2, a3, a4, a5, a6, a7) = (a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
    let (b0, b1, b2, b3, b4, b5, b6, b7) = (b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
    assert(((a0 as u64) | ((a1 as u64) << 8u64) | ((a2 as u64) << 16u64) | ((a3 as u64) << 24u64)
        | ((a4 as u64) << 32u64) | ((a5 as u64) << 40u64) | ((a6 as u64) << 48u64) | ((a7 as u64) << 56u64)
        == (b0 as u64) | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64) | ((b3 as u64) << 24u64)
        | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64) | ((b6 as u64) << 48u64) | ((b7 as u64) << 56u64))
        == (a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7))
        by (bit_vector);
    if a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7 {
        assert(a =~= b);
    }
}

/// The parameters of the domain: three texts and three int4 values.
pub proof fn lemma_params(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps.len() == 6,
        ps[0] == Literal::Text(pb(ps, 0)), ps[2] == Literal::Text(pb(ps, 1)), ps[4] == Literal::Text(pb(ps, 2)),
        ps[1] == (Literal::Int { v: pv(ps, 0), kind: IntKind::Int4 }),
        ps[3] == (Literal::Int { v: pv(ps, 1), kind: IntKind::Int4 }),
        ps[5] == (Literal::Int { v: pv(ps, 2), kind: IntKind::Int4 }),
        -0x8000_0000 <= pv(ps, 0) <= 0x7fff_ffff,
        -0x8000_0000 <= pv(ps, 1) <= 0x7fff_ffff,
        -0x8000_0000 <= pv(ps, 2) <= 0x7fff_ffff,
{
    assert(2 * 0 == 0 && 2 * 0 + 1 == 1 && 2 * 1 == 2 && 2 * 1 + 1 == 3 && 2 * 2 == 4 && 2 * 2 + 1 == 5);
}

/// A brand parameter as a word (0 unless it has 8 bytes) and whether it has 8 bytes.
fn pack_param(b: &[u8]) -> (r: (u64, bool))
    ensures r.1 == (b@.len() == 8), r.1 ==> r.0 == pack8_spec(b@),
{
    if b.len() != 8 {
        return (0, false);
    }
    let v = load8(b, 0);
    proof {
        assert(b@.subrange(0, 8) =~= b@);
    }
    (v, true)
}

/// The bound parameters, or `None` when some `pv + 10` leaves int4.
pub fn make_bind(params: &Params) -> (r: Option<Bind>)
    requires param_domain(params@),
    ensures
        r matches Some(x) ==> adds_ok(params@) && bind_ok(x, params@),
        r is None ==> !adds_ok(params@),
{
    let ghost ps = params@;
    proof { lemma_params(ps); }
    if params.p1 > 0x7fff_fff5 || params.p3 > 0x7fff_fff5 || params.p5 > 0x7fff_fff5 {
        return None;
    }
    let x = Bind {
        b0: params.p0, n0: params.p0.len(),
        b1: params.p2, n1: params.p2.len(),
        b2: params.p4, n2: params.p4.len(),
        lo0: params.p1 as i128 * 100, hi0: (params.p1 as i128 + 10) * 100,
        lo1: params.p3 as i128 * 100, hi1: (params.p3 as i128 + 10) * 100,
        lo2: params.p5 as i128 * 100, hi2: (params.p5 as i128 + 10) * 100,
        k0: 0, k1: 0, k2: 0, e0: false, e1: false, e2: false,
    };
    let (k0, e0) = pack_param(params.p0);
    let (k1, e1) = pack_param(params.p2);
    let (k2, e2) = pack_param(params.p4);
    let x = Bind { k0, k1, k2, e0, e1, e2, ..x };
    Some(x)
}

} // verus!
