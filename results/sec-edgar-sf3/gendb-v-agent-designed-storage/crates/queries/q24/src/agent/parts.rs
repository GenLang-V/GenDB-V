//! Whole stored parts as `'static` slices (one counted extent request each) and the stored dictionaries as `Dict`.
use vstd::prelude::*;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::layout::PartView;
use crate::stores::num_tvg::interface as N;
use crate::stores::pre::interface as P;
use super::common::dictmap::Dict;
use super::stored::{ndict_is, pdict_is, lemma_ndict_wf, lemma_pdict_wf};

verus! {

pub fn read_u64(st: &mut StoredParts, p: usize) -> (r: &'static [u64])
    requires p < old(st)@.len(), old(st)@[p as int] is U64,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->U64_0,
{
    let n = st.part_len(p);
    let r = st.extent_u64(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->U64_0);
    }
    r
}

pub fn read_u32(st: &mut StoredParts, p: usize) -> (r: &'static [u32])
    requires p < old(st)@.len(), old(st)@[p as int] is U32,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->U32_0,
{
    let n = st.part_len(p);
    let r = st.extent_u32(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->U32_0);
    }
    r
}

pub fn read_u8(st: &mut StoredParts, p: usize) -> (r: &'static [u8])
    requires p < old(st)@.len(), old(st)@[p as int] is U8,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->U8_0,
{
    let n = st.part_len(p);
    let r = st.extent_u8(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->U8_0);
    }
    r
}

pub fn read_i32(st: &mut StoredParts, p: usize) -> (r: &'static [i32])
    requires p < old(st)@.len(), old(st)@[p as int] is I32,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->I32_0,
{
    let n = st.part_len(p);
    let r = st.extent_i32(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->I32_0);
    }
    r
}

pub fn read_i128(st: &mut StoredParts, p: usize) -> (r: &'static [i128])
    requires p < old(st)@.len(), old(st)@[p as int] is I128,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->I128_0,
{
    let n = st.part_len(p);
    let r = st.extent_i128(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->I128_0);
    }
    r
}

/// The num dictionary in parts `po`, `po + 1`.
pub fn num_dict(st: &mut StoredParts, po: usize) -> (d: Dict)
    requires
        po < 64, po + 1 < old(st)@.len(), N::dict_ok(old(st)@, po),
    ensures final(st)@ == old(st)@, ndict_is(d, old(st)@, po), d.wf(),
{
    let off = read_u64(st, po);
    let bytes = read_u8(st, po + 1);
    let n = off.len();
    let d = Dict { off, bytes, count: n - 1 };
    proof {
        lemma_ndict_wf(d, st@, po);
    }
    d
}

/// The pre dictionary in parts `po`, `po + 1`.
pub fn pre_dict(st: &mut StoredParts, po: usize) -> (d: Dict)
    requires
        po < 64, po + 1 < old(st)@.len(), P::common::cols::sorted_list_ok(old(st)@, po),
    ensures final(st)@ == old(st)@, pdict_is(d, old(st)@, po), d.wf(),
{
    let off = read_u64(st, po);
    let bytes = read_u8(st, po + 1);
    let n = off.len();
    let d = Dict { off, bytes, count: n - 1 };
    proof {
        lemma_pdict_wf(d, st@, po);
    }
    d
}

/// A bound on the length of a stored `i128` part: its bytes fit `isize`.
pub fn len_bound(s: &'static [i128]) -> (n: usize)
    ensures n == s@.len(), n <= 0x0800_0000_0000_0000, n < usize::MAX,
{
    vstd::layout::layout_for_val_is_valid::<[i128]>(Tracked(s));
    proof {
        broadcast use vstd::layout::layout_of_slices, vstd::layout::layout_of_primitives;
        assert(vstd::layout::spec_size_of_val::<[i128]>(s) == s@.len() * 16);
        assert(isize::MAX <= 0x7fff_ffff_ffff_ffff);
        assert(isize::MAX < usize::MAX);
    }
    s.len()
}

/// A bound on the length of a stored `u64` part: its bytes fit `isize`.
pub fn len_bound_u64(s: &'static [u64]) -> (n: usize)
    ensures n == s@.len(), n <= 0x1000_0000_0000_0000, n < usize::MAX,
{
    vstd::layout::layout_for_val_is_valid::<[u64]>(Tracked(s));
    proof {
        broadcast use vstd::layout::layout_of_slices, vstd::layout::layout_of_primitives;
        assert(vstd::layout::spec_size_of_val::<[u64]>(s) == s@.len() * 8);
        assert(isize::MAX <= 0x7fff_ffff_ffff_ffff);
        assert(isize::MAX < usize::MAX);
    }
    s.len()
}

} // verus!
