//! The stored columns the query reads, as whole-column slices (one extent per part; the host maps the parts, so
//! only the pages a pass touches are read), and their relation to the model (`cols_ok`).
//!
//! A text column is its offsets (`n + 1`, non-decreasing, the first not necessarily 0) and the bytes they address:
//! value `a` is `bytes[off[a] - off[0] .. off[a + 1] - off[0]]` (`tval`, `trange`).
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::{TextView, text_at};
use crate::agent::model::*;
use crate::agent::model;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;

verus! {

/// A text column of rows `0..n` (see the module comment).
#[derive(Clone, Copy)]
pub struct TextCol {
    pub off: &'static [i64],
    pub bytes: &'static [u8],
}

/// The offsets of a text column of `n` rows are well formed.
pub open spec fn tcol_wf(t: TextCol, n: int) -> bool {
    &&& t.off@.len() == n + 1
    &&& 0 <= t.off@[0]
    &&& forall|a: int, b: int| 0 <= a <= b <= n ==> t.off@[a] <= t.off@[b]
    &&& t.bytes@.len() == t.off@[n] - t.off@[0]
    &&& t.bytes@.len() <= usize::MAX
}

/// Value `a` of a text column.
pub open spec fn tval(t: TextCol, a: int) -> Seq<u8> {
    t.bytes@.subrange(t.off@[a] - t.off@[0], t.off@[a + 1] - t.off@[0])
}

/// `t` holds the `n` values of the stored text column `view`.
pub open spec fn tcol_is(t: TextCol, view: TextView, n: int) -> bool {
    &&& tcol_wf(t, n)
    &&& forall|a: int| 0 <= a < n ==> #[trigger] tval(t, a) == text_at(view, a)
}

/// The byte range of value `a` in `t.bytes`.
pub fn trange(t: &TextCol, a: usize, Ghost(n): Ghost<int>) -> (r: (usize, usize))
    requires tcol_wf(*t, n), a < n,
    ensures r.0 <= r.1 <= t.bytes@.len(), t.bytes@.subrange(r.0 as int, r.1 as int) == tval(*t, a as int),
    no_unwind
{
    let base = t.off[0];
    let x = t.off[a];
    let y = t.off[a + 1];
    proof {
        assert(t.off@[0] <= t.off@[a as int] <= t.off@[a + 1] <= t.off@[n]);
    }
    ((x - base) as usize, (y - base) as usize)
}

/// The columns the query reads.
#[derive(Clone, Copy)]
pub struct Cols {
    pub np: usize,
    pub nq: usize,
    pub ns: usize,
    pub p_key: &'static [i64],
    pub p_size: &'static [i64],
    pub brand: TextCol,
    pub ptype: TextCol,
    pub ps_pk: &'static [i64],
    pub ps_sk: &'static [i64],
    pub s_key: &'static [i64],
    pub comment: TextCol,
}

/// The slices are the stored columns of `sv`.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.np == part_n(sv) && c.nq == ps_n(sv) && c.ns == supp_n(sv)
    &&& c.p_key@.len() == c.np && c.p_size@.len() == c.np
    &&& c.ps_pk@.len() == c.nq && c.ps_sk@.len() == c.nq && c.s_key@.len() == c.ns
    &&& c.p_key@ == p_keys(sv) && c.p_size@ == p_sizes(sv)
    &&& c.ps_pk@ == ps_pkeys(sv) && c.ps_sk@ == ps_skeys(sv)
    &&& c.s_key@ == s_keys(sv)
    &&& tcol_is(c.brand, brand_view(sv), c.np as int)
    &&& tcol_is(c.ptype, type_view(sv), c.np as int)
    &&& tcol_is(c.comment, comment_view(sv), c.ns as int)
}

/// Turns the reader output `(offsets, bytes)` of rows `0..n` into a `TextCol`.
fn tcol_of(r: (&'static [i64], &'static [u8]), n: usize, Ghost(view): Ghost<TextView>) -> (t: TextCol)
    requires
        n >= 1,
        r.0@.len() == n + 1,
        0 <= r.0@[0],
        forall|a: int, b: int| 0 <= a <= b <= n ==> r.0@[a] <= r.0@[b],
        r.1@.len() == r.0@[n as int] - r.0@[0],
        forall|j: int| 0 <= j < n ==> #[trigger] r.1@.subrange(r.0@[j] - r.0@[0], r.0@[j + 1] - r.0@[0]) == text_at(view, j),
    ensures tcol_is(t, view, n as int),
{
    let t = TextCol { off: r.0, bytes: r.1 };
    let _blen = r.1.len();
    proof {
        assert forall|a: int| 0 <= a < n implies #[trigger] tval(t, a) == text_at(view, a) by {
            assert(r.1@.subrange(r.0@[a] - r.0@[0], r.0@[a + 1] - r.0@[0]) == text_at(view, a));
        }
    }
    t
}

/// Read every column the query reads (every table non-empty).
pub fn read_cols(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (c: Cols)
    requires
        old(stores)@ == sv,
        stores_wf(sv),
        part_n(sv) >= 1, ps_n(sv) >= 1, supp_n(sv) >= 1,
    ensures
        final(stores)@ == sv,
        cols_ok(c, sv),
{
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let p_key = stores.flat_part.extent_i64(pi::P_PARTKEY, 0, np);
    let p_size = stores.flat_part.extent_i64(pi::P_SIZE, 0, np);
    assert(p_key@ =~= model::p_keys(sv));
    assert(p_size@ =~= model::p_sizes(sv));
    let r = pi::text_rows(&mut stores.flat_part, pi::P_BRAND_OFFSETS, pi::P_BRAND_BYTES, 0, np, Ghost(np as int));
    let brand = tcol_of(r, np, Ghost(brand_view(sv)));
    let r = pi::text_rows(&mut stores.flat_part, pi::P_TYPE_OFFSETS, pi::P_TYPE_BYTES, 0, np, Ghost(np as int));
    let ptype = tcol_of(r, np, Ghost(type_view(sv)));
    let nq = stores.flat_partsupp.part_len(psi::PS_PARTKEY);
    let ps_pk = stores.flat_partsupp.extent_i64(psi::PS_PARTKEY, 0, nq);
    let ps_sk = stores.flat_partsupp.extent_i64(psi::PS_SUPPKEY, 0, nq);
    assert(ps_pk@ =~= model::ps_pkeys(sv));
    assert(ps_sk@ =~= model::ps_skeys(sv));
    let ns = stores.flat_supplier.part_len(si::S_SUPPKEY);
    let s_key = stores.flat_supplier.extent_i64(si::S_SUPPKEY, 0, ns);
    assert(s_key@ =~= model::s_keys(sv));
    let r = si::text_rows(&mut stores.flat_supplier, si::S_COMMENT_OFFSETS, si::S_COMMENT_BYTES, 0, ns, Ghost(ns as int));
    let comment = tcol_of(r, ns, Ghost(comment_view(sv)));
    Cols { np, nq, ns, p_key, p_size, brand, ptype, ps_pk, ps_sk, s_key, comment }
}

} // verus!
