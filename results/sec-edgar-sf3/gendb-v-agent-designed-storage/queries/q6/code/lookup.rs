//! The parameters as dictionary codes: `$1` in the num uom dictionary, `$2` in the pre stmt dictionary. A value
//! missing from its dictionary qualifies no row (`lemma_no_uom`, `lemma_no_stmt`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::num::interface::common::text as ntext;
use crate::stores::pre::interface::common::text as ptext;
use crate::stores::num::interface::common::text::find_in_stored_dict;
use crate::stores::num::interface::common::runs as nruns;
use crate::stores::pre::interface::common::runs as pruns;
use crate::stores::pre::interface::common::cols::{u64s as pu64s, list_entry};
use crate::agent::meaning::{p_uom, p_stmt};
use crate::agent::views::*;
use crate::agent::fspec::{layouts, zero_j};
use crate::agent::filings::{stmt_key_ok, lemma_ptext};

verus! {

/// The uom code of `$1`, if the dictionary has it.
pub fn find_uom(stores: &mut Stores, key: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<usize>)
    requires old(stores)@ == sv, layouts(sv), key@ == p_uom(ps),
    ensures
        final(stores)@ == sv,
        r matches Some(u) ==> u < ni::uom_count(sv.num) && ni::dict_entry(sv.num, ni::P_UOM_OFF, u as int) == p_uom(ps),
        r is None ==> forall|k: int| 0 <= k < ni::uom_count(sv.num) ==> #[trigger] ni::dict_entry(sv.num, ni::P_UOM_OFF, k) != p_uom(ps),
{
    proof { assert(ni::num_layout_ok(sv.num)); }
    let n = stores.num.part_len(ni::P_UOM_OFF);
    find_in_stored_dict(&mut stores.num, ni::P_UOM_OFF, ni::P_UOM_BYTES, n - 1, key)
}

/// The stmt key of `$2` (dictionary code + 1), if the dictionary has it.
pub fn find_stmt(stores: &mut Stores, key: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<u64>)
    requires old(stores)@ == sv, layouts(sv), key@ == p_stmt(ps),
    ensures
        final(stores)@ == sv,
        r matches Some(k) ==> stmt_key_ok(sv, ps, k),
        r is None ==> forall|g: int| 0 <= g < pi::group_count(sv.pre) ==> #[trigger] pi::group_stmt_of(sv.pre, g) != Val::Text(p_stmt(ps)),
{
    let ghost pp = sv.pre;
    proof { assert(pi::pre_layout_ok(pp)); }
    let n = stores.pre.part_len(pi::P_STMT_OFF);
    let ghost off = ptext::u64_part(pp[pi::P_STMT_OFF as int]);
    let ghost bytes = ptext::u8_part(pp[pi::P_STMT_BYTES as int]);
    let ghost cnt = (n - 1) as int;
    proof {
        assert(pi::P_STMT_OFF + 1 == pi::P_STMT_BYTES);
        lemma_ptext(off, bytes, cnt);
    }
    let r = find_in_stored_dict(&mut stores.pre, pi::P_STMT_OFF, pi::P_STMT_BYTES, n - 1, key);
    match r {
        Some(c) => {
            proof {
                assert forall|g: int| 0 <= g < pi::group_count(pp)
                    implies ((#[trigger] pu64s(pp, pi::P_GROUP_STMT)[g] == c + 1) == (pi::group_stmt_of(pp, g) == Val::Text(p_stmt(ps)))) by {
                    let k = pu64s(pp, pi::P_GROUP_STMT)[g];
                    if k != 0 && k != c + 1 {
                        ptext::lemma_dict_codes(off, bytes, cnt, k - 1, c as int);
                    }
                }
            }
            Some(c as u64 + 1)
        },
        None => {
            proof {
                assert forall|g: int| 0 <= g < pi::group_count(pp) implies #[trigger] pi::group_stmt_of(pp, g) != Val::Text(p_stmt(ps)) by {
                    let k = pu64s(pp, pi::P_GROUP_STMT)[g];
                    if k != 0 {
                        assert(ntext::text_entry(off, bytes, k - 1) != key@);
                    }
                }
            }
            None
        },
    }
}

/// No uom value is `$1`: no triple qualifies.
pub proof fn lemma_no_uom(sv: StoresView, ps: Seq<Literal>)
    requires
        layouts(sv),
        forall|k: int| 0 <= k < ni::uom_count(sv.num) ==> #[trigger] ni::dict_entry(sv.num, ni::P_UOM_OFF, k) != p_uom(ps),
    ensures forall|j: int| 0 <= j < s_count(sv) ==> #[trigger] zero_j(sv, ps, j),
{
    let np = sv.num;
    assert(ni::num_layout_ok(np));
    assert forall|j: int| 0 <= j < s_count(sv) implies #[trigger] zero_j(sv, ps, j) by {
        assert forall|i: int, l: int| 0 <= i < n_count(sv) && 0 <= l < p_count(sv) implies !#[trigger] pq(sv, ps, i, j, l) by {
            nruns::lemma_run_of(n_start(sv), ni::run_count(np), n_count(sv), i);
            let r = n_run(sv, i);
            assert(ni::u64s(np, ni::P_RUN_UOM)[r] < ni::uom_count(np));
            assert(ni::dict_entry(np, ni::P_UOM_OFF, ni::u64s(np, ni::P_RUN_UOM)[r] as int) != p_uom(ps));
        }
    }
}

/// No (stmt, rfile) group has stmt `$2`: no triple qualifies.
pub proof fn lemma_no_stmt(sv: StoresView, ps: Seq<Literal>)
    requires
        layouts(sv),
        forall|g: int| 0 <= g < pi::group_count(sv.pre) ==> #[trigger] pi::group_stmt_of(sv.pre, g) != Val::Text(p_stmt(ps)),
    ensures forall|j: int| 0 <= j < s_count(sv) ==> #[trigger] zero_j(sv, ps, j),
{
    let pp = sv.pre;
    assert(pi::pre_layout_ok(pp));
    assert forall|j: int| 0 <= j < s_count(sv) implies #[trigger] zero_j(sv, ps, j) by {
        assert forall|i: int, l: int| 0 <= i < n_count(sv) && 0 <= l < p_count(sv) implies !#[trigger] pq(sv, ps, i, j, l) by {
            pruns::lemma_run_of(p_start(sv), pi::sub_count(pp), p_count(sv), l);
            let s = p_sub(sv, l);
            assert(pu64s(pp, pi::P_SUB_ADSH)[s] < pi::adsh_count(pp));
            assert(pu64s(pp, pi::P_SUB_GROUP)[s] < pi::group_count(pp));
            assert(pi::group_stmt_of(pp, pu64s(pp, pi::P_SUB_GROUP)[s] as int) != Val::Text(p_stmt(ps)));
        }
    }
}

} // verus!
