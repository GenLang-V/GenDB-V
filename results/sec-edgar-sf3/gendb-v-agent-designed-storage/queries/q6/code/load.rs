//! The stored parts the query reads, each as one whole slice (one request each), and what they are.
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::stored::StoredParts;
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::sub::interface as si;
use crate::stores::num::interface::common::text as ntext;
use crate::stores::pre::interface::common::text as ptext;
use crate::stores::sub::interface::common::text as stext;
use crate::stores::num::interface::common::cols::{i32_part, i128_part};
use crate::stores::pre::interface::common::cols::u64s as pu64s;
use crate::agent::views::*;
use crate::agent::fspec::layouts;
use crate::agent::pairs::{PairDicts, pd_ok};

verus! {

fn all_u64(st: &mut StoredParts, p: usize) -> (r: &'static [u64])
    requires p < old(st)@.len(), old(st)@[p as int] is U64,
    ensures final(st)@ == old(st)@, r@ == ntext::u64_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_u64(p, 0, n);
    proof { assert(r@ =~= ntext::u64_part(st@[p as int])); }
    r
}

fn all_u8(st: &mut StoredParts, p: usize) -> (r: &'static [u8])
    requires p < old(st)@.len(), old(st)@[p as int] is U8,
    ensures final(st)@ == old(st)@, r@ == ntext::u8_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_u8(p, 0, n);
    proof { assert(r@ =~= ntext::u8_part(st@[p as int])); }
    r
}

fn all_i32(st: &mut StoredParts, p: usize) -> (r: &'static [i32])
    requires p < old(st)@.len(), old(st)@[p as int] is I32,
    ensures final(st)@ == old(st)@, r@ == i32_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_i32(p, 0, n);
    proof { assert(r@ =~= i32_part(st@[p as int])); }
    r
}

fn all_i128(st: &mut StoredParts, p: usize) -> (r: &'static [i128])
    requires p < old(st)@.len(), old(st)@[p as int] is I128,
    ensures final(st)@ == old(st)@, r@ == i128_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_i128(p, 0, n);
    proof { assert(r@ =~= i128_part(st@[p as int])); }
    r
}

/// The whole parts the query reads (independent of the parameters).
#[derive(Clone, Copy)]
pub struct Inputs {
    pub nadsh_off: &'static [u64],
    pub nadsh_bytes: &'static [u8],
    pub nadsh_count: usize,
    pub uom_runs: &'static [u64],
    pub nruns_all: usize,
    pub num_tv: &'static [u64],
    pub num_val: &'static [i128],
    pub nrows: usize,
    pub padsh_off: &'static [u64],
    pub padsh_bytes: &'static [u8],
    pub padsh_count: usize,
    pub adsh_subs: &'static [u64],
    pub sub_start: &'static [u64],
    pub sub_group: &'static [u64],
    pub nsubs: usize,
    pub group_stmt: &'static [u64],
    pub ngroups: usize,
    pub pre_tv: &'static [u64],
    pub npre: usize,
    pub plabel_codes: &'static [u64],
    pub plabel_valid: &'static [u8],
    pub plabel_off: &'static [u64],
    pub plabel_bytes: &'static [u8],
    pub nplabel: usize,
    pub fy: &'static [i32],
    pub fy_valid: &'static [u8],
    pub name_codes: &'static [u64],
    pub sadsh_off: &'static [u64],
    pub sadsh_bytes: &'static [u8],
    pub ns: usize,
    /// `sub` rows in adsh order (`P_ADSH_ORDER`); only a search hint, so no facts are kept but its length.
    pub sadsh_order: &'static [u64],
    pub norder: usize,
    pub name_off: &'static [u64],
    pub name_bytes: &'static [u8],
    pub name_count: usize,
    pub dicts: PairDicts,
}

/// The slices are the storages' parts.
pub open spec fn loaded(t: Inputs, sv: StoresView) -> bool {
    let np = sv.num;
    let pp = sv.pre;
    let sp = sv.sub;
    &&& layouts(sv)
    &&& t.nadsh_off@ == ntext::u64_part(np[ni::P_ADSH_OFF as int])
    &&& t.nadsh_bytes@ == ntext::u8_part(np[ni::P_ADSH_BYTES as int])
    &&& t.nadsh_count == ni::adsh_count(np)
    &&& t.uom_runs@ == ni::u64s(np, ni::P_UOM_RUNS)
    &&& t.nruns_all == ni::run_count(np)
    &&& t.num_tv@ == ni::u64s(np, ni::P_TV)
    &&& t.num_val@ == i128_part(np[ni::P_VALUE as int])
    &&& t.nrows == n_count(sv)
    &&& t.padsh_off@ == ptext::u64_part(pp[pi::P_ADSH_OFF as int])
    &&& t.padsh_bytes@ == ptext::u8_part(pp[pi::P_ADSH_BYTES as int])
    &&& t.padsh_count == pi::adsh_count(pp)
    &&& t.adsh_subs@ == pu64s(pp, pi::P_ADSH_SUBS)
    &&& t.sub_start@ == p_start(sv)
    &&& t.sub_group@ == pu64s(pp, pi::P_SUB_GROUP)
    &&& t.nsubs == pi::sub_count(pp)
    &&& t.group_stmt@ == pu64s(pp, pi::P_GROUP_STMT)
    &&& t.ngroups == pi::group_count(pp)
    &&& t.pre_tv@ == pu64s(pp, pi::P_TV)
    &&& t.npre == p_count(sv)
    &&& t.plabel_codes@ == pu64s(pp, pi::P_PLABEL_CODES)
    &&& t.plabel_valid@ == ptext::u8_part(pp[pi::P_PLABEL_VALID as int])
    &&& t.plabel_off@ == ptext::u64_part(pp[pi::P_PLABEL_OFF as int])
    &&& t.plabel_bytes@ == ptext::u8_part(pp[pi::P_PLABEL_BYTES as int])
    &&& t.nplabel as int == crate::stores::pre::interface::common::cols::text_count(pp, pi::P_PLABEL_OFF as int)
    &&& t.fy@ == crate::stores::sub::interface::common::cols::i32_part(sp[si::P_FY as int])
    &&& t.fy_valid@ == stext::u8_part(sp[si::P_FY_VALID as int])
    &&& t.name_codes@ == stext::u64_part(sp[si::P_NAME_CODES as int])
    &&& t.sadsh_off@ == stext::u64_part(sp[si::P_ADSH_OFF as int])
    &&& t.sadsh_bytes@ == stext::u8_part(sp[si::P_ADSH_BYTES as int])
    &&& t.ns == s_count(sv)
    &&& t.sadsh_order@.len() == t.norder
    &&& t.name_off@ == stext::u64_part(sp[si::P_NAME_DICT_OFF as int])
    &&& t.name_bytes@ == stext::u8_part(sp[si::P_NAME_DICT_BYTES as int])
    &&& t.name_count as int == crate::stores::sub::interface::common::cols::text_count(sp, si::P_NAME_DICT_OFF as int)
    &&& pd_ok(t.dicts, sv)
}

/// Read the whole parts.
pub fn load(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (t: Inputs)
    requires old(stores)@ == sv, layouts(sv),
    ensures final(stores)@ == sv, loaded(t, sv),
{
    let ghost np = sv.num;
    let ghost pp = sv.pre;
    let ghost sp = sv.sub;
    proof {
        assert(ni::num_layout_ok(np));
        assert(pi::pre_layout_ok(pp));
        assert(si::sub_layout_ok(sp));
        assert(pi::P_PLABEL_OFF + 1 == pi::P_PLABEL_BYTES);
    }
    // num
    let nadsh_off = all_u64(&mut stores.num, ni::P_ADSH_OFF);
    let nadsh_bytes = all_u8(&mut stores.num, ni::P_ADSH_BYTES);
    let uom_runs = all_u64(&mut stores.num, ni::P_UOM_RUNS);
    let run_uom_n = stores.num.part_len(ni::P_RUN_UOM);
    let num_tv = all_u64(&mut stores.num, ni::P_TV);
    let num_val = all_i128(&mut stores.num, ni::P_VALUE);
    let nrows = stores.num.part_len(ni::P_ORIG);
    let npair_tag = all_u64(&mut stores.num, ni::P_PAIR_TAG);
    let npair_ver = all_u64(&mut stores.num, ni::P_PAIR_VERSION);
    let ntag_off = all_u64(&mut stores.num, ni::P_TAG_OFF);
    let ntag_bytes = all_u8(&mut stores.num, ni::P_TAG_BYTES);
    let nver_off = all_u64(&mut stores.num, ni::P_VERSION_OFF);
    let nver_bytes = all_u8(&mut stores.num, ni::P_VERSION_BYTES);
    // pre
    let padsh_off = all_u64(&mut stores.pre, pi::P_ADSH_OFF);
    let padsh_bytes = all_u8(&mut stores.pre, pi::P_ADSH_BYTES);
    let adsh_subs = all_u64(&mut stores.pre, pi::P_ADSH_SUBS);
    let sub_start = all_u64(&mut stores.pre, pi::P_SUB_START);
    let sub_group = all_u64(&mut stores.pre, pi::P_SUB_GROUP);
    let nsubs = stores.pre.part_len(pi::P_SUB_ADSH);
    let group_stmt = all_u64(&mut stores.pre, pi::P_GROUP_STMT);
    let pre_tv = all_u64(&mut stores.pre, pi::P_TV);
    let npre = stores.pre.part_len(pi::P_ORIG);
    let ppair_tag = all_u64(&mut stores.pre, pi::P_PAIR_TAG);
    let ppair_ver = all_u64(&mut stores.pre, pi::P_PAIR_VERSION);
    let ptag_off = all_u64(&mut stores.pre, pi::P_TAG_OFF);
    let ptag_bytes = all_u8(&mut stores.pre, pi::P_TAG_BYTES);
    let pver_off = all_u64(&mut stores.pre, pi::P_VERSION_OFF);
    let pver_bytes = all_u8(&mut stores.pre, pi::P_VERSION_BYTES);
    let plabel_codes = all_u64(&mut stores.pre, pi::P_PLABEL_CODES);
    let plabel_valid = all_u8(&mut stores.pre, pi::P_PLABEL_VALID);
    let plabel_off = all_u64(&mut stores.pre, pi::P_PLABEL_OFF);
    let plabel_bytes = all_u8(&mut stores.pre, pi::P_PLABEL_BYTES);
    // sub
    let fy = all_i32(&mut stores.sub, si::P_FY);
    let fy_valid = all_u8(&mut stores.sub, si::P_FY_VALID);
    let name_codes = all_u64(&mut stores.sub, si::P_NAME_CODES);
    let sadsh_off = all_u64(&mut stores.sub, si::P_ADSH_OFF);
    let sadsh_bytes = all_u8(&mut stores.sub, si::P_ADSH_BYTES);
    let sadsh_order = all_u64(&mut stores.sub, si::P_ADSH_ORDER);
    let name_off = all_u64(&mut stores.sub, si::P_NAME_DICT_OFF);
    let name_bytes = all_u8(&mut stores.sub, si::P_NAME_DICT_BYTES);
    let ns = name_codes.len();
    let dicts = PairDicts {
        ppair_tag, ppair_ver, npp: ppair_tag.len(),
        ptag_off, ptag_bytes, ptag_count: ptag_off.len() - 1,
        pver_off, pver_bytes, pver_count: pver_off.len() - 1,
        ntag_off, ntag_bytes, ntag_count: ntag_off.len() - 1,
        nver_off, nver_bytes, nver_count: nver_off.len() - 1,
        npair_tag, npair_ver, nnpairs: npair_tag.len(),
    };
    Inputs {
        nadsh_off, nadsh_bytes, nadsh_count: nadsh_off.len() - 1, uom_runs, nruns_all: run_uom_n, num_tv, num_val, nrows,
        padsh_off, padsh_bytes, padsh_count: padsh_off.len() - 1, adsh_subs, sub_start, sub_group, nsubs, group_stmt,
        ngroups: group_stmt.len(), pre_tv, npre, plabel_codes, plabel_valid, plabel_off, plabel_bytes,
        nplabel: plabel_off.len() - 1, fy, fy_valid, name_codes, sadsh_off, sadsh_bytes, ns, sadsh_order,
        norder: sadsh_order.len(), name_off, name_bytes,
        name_count: name_off.len() - 1, dicts,
    }
}

} // verus!
