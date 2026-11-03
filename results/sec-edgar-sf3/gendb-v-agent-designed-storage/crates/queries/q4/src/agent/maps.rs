//! Sorted dictionaries held as slices (`Dict`): the text lists the lookups search.
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;

use crate::stores::num::interface::common::text::{text_entry, text_parts_wf, text_strictly_sorted, u64_part, u8_part, lemma_dict_codes};

verus! {

// ------------------------------------------------------------------------------------------------ dictionaries

/// A sorted dictionary held as slices.
#[derive(Clone, Copy)]
pub struct Dict {
    pub off: &'static [u64],
    pub bytes: &'static [u8],
    pub n: usize,
}

pub open spec fn dict_wf(d: Dict) -> bool {
    text_parts_wf(d.off@, d.bytes@, d.n as int) && text_strictly_sorted(d.off@, d.bytes@, d.n as int)
}

pub open spec fn dentry(d: Dict, k: int) -> Seq<u8> { text_entry(d.off@, d.bytes@, k) }

/// The dictionary of parts `po` (offsets) and `po + 1` (bytes), read whole.
pub fn read_dict(st: &mut StoredParts, po: usize, pb: usize) -> (d: Dict)
    requires
        pb == po + 1, pb < old(st)@.len(), old(st)@[po as int] is U64, old(st)@[po + 1] is U8,
        u64_part(old(st)@[po as int]).len() >= 1,
    ensures
        final(st)@ == old(st)@,
        d.off@ == u64_part(old(st)@[po as int]), d.bytes@ == u8_part(old(st)@[po + 1]),
        d.n == u64_part(old(st)@[po as int]).len() - 1,
{
    let no = st.part_len(po);
    let off = st.extent_u64(po, 0, no);
    let nb = st.part_len(pb);
    let bytes = st.extent_u8(pb, 0, nb);
    proof {
        assert(off@ =~= u64_part(old(st)@[po as int]));
        assert(bytes@ =~= u8_part(old(st)@[po + 1]));
    }
    Dict { off, bytes, n: no - 1 }
}

} // verus!
