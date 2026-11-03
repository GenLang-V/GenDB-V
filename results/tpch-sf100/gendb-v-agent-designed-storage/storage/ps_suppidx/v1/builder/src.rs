//! What the builder reads from storage `suppliers` (partsupp in canonical row order: stored row `s` is canonical row
//! `s`): for a database bound to the source, the ps_suppkey of row `s` is `key_at(s)`, a frame-of-reference value over
//! uniform groups of `bsize` rows (`base[s / bsize] + code[s]`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::spec::value::{Database, Row, Val};
use crate::spec::int::{int_in_range, IntKind};
use crate::link::source::lemma_proj_all_index;
use crate::stores::suppliers::interface as F;
use crate::stores::suppliers::interface::common::colfmt as FC;
use crate::stores::suppliers::interface::common::read as FR;
use crate::stores::ps_suppidx::declaration as D;

verus! {

/// Part indices of the partsupp columns of `suppliers` the builder reads.
pub const P_LAYOUT: usize = 0;
pub const P_GROUPS: usize = 1;
pub const P_SUPP_CODES: usize = 4;
pub const P_SUPP_BASE: usize = 5;

/// ps_suppkey of row `s`.
pub open spec fn key_at(kc: Seq<u32>, kb: Seq<i64>, bsize: int, s: int) -> int {
    kb[s / bsize] + kc[s]
}

/// The source facts the builder uses, over the parts `p` of `suppliers` and the indexed relation `rel`.
pub open spec fn src_ok(p: Seq<PartView>, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    let bsize = FC::u64s(p[P_LAYOUT as int])[1] as int;
    let (kc, kb) = (FC::u32s(p[P_SUPP_CODES as int]), FC::i64s(p[P_SUPP_BASE as int]));
    &&& p.len() == F::SUPPLIERS_PARTS
    &&& p[P_LAYOUT as int] is U64 && FC::u64s(p[P_LAYOUT as int]).len() == 2
    &&& bsize >= 1
    &&& p[P_SUPP_CODES as int] is U32 && p[P_SUPP_BASE as int] is I64
    &&& kc.len() == n
    &&& forall|s: int| 0 <= s < n ==> #[trigger] (s / bsize) < kb.len()
    &&& forall|s: int| 0 <= s < n ==> {
            &&& i64::MIN <= #[trigger] key_at(kc, kb, bsize, s) <= i64::MAX
            &&& rel[s][0] == Val::Int(key_at(kc, kb, bsize, s))
        }
    &&& forall|r: int| 0 <= r < n ==> (#[trigger] rel[r]).len() == 1
}

/// For a database bound to `suppliers`, its parts and this storage's relation meet `src_ok`.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.suppliers, D::stored_relations(db)[0]),
{
    let p = sv.suppliers;
    let srels = crate::stores::suppliers::declaration::stored_relations(db);
    let rel = D::stored_relations(db)[0];
    assert(F::represents(p, srels));
    let tp = p.subrange(F::PARTSUPP_FIRST as int, (F::PARTSUPP_FIRST + F::PS_PARTS) as int);
    let prel = srels[0];
    assert(F::partsupp_ok(tp, prel));
    let t4 = db.tables[4];
    lemma_proj_all_index(t4, crate::stores::suppliers::declaration::stored_cols_t0());
    lemma_proj_all_index(t4, D::stored_cols_t0());
    D::lemma_stored_relations(db);
    let n = rel.len() as int;
    assert(prel.len() == n);
    let bsize = FC::u64s(tp[F::PS_LAYOUT as int])[1] as int;
    assert(tp[F::PS_LAYOUT as int] == p[P_LAYOUT as int]);
    assert(tp[F::PS_GROUPS as int] == p[P_GROUPS as int]);
    assert(tp[F::PS_SUPPKEY_CODES as int] == p[P_SUPP_CODES as int]);
    assert(tp[F::PS_SUPPKEY_BASE as int] == p[P_SUPP_BASE as int]);
    let gp = p[P_GROUPS as int];
    let gs = FC::u64s(gp);
    let (kcp, kbp) = (p[P_SUPP_CODES as int], p[P_SUPP_BASE as int]);
    let (kc, kb) = (FC::u32s(kcp), FC::i64s(kbp));
    assert(F::table_layout_ok(tp, n));
    assert(FC::groups_part_ok(gp, n, bsize));
    FC::lemma_uniform_groups(gp, n, bsize);
    FC::lemma_nblocks(n, bsize);
    assert(FC::int_col_at(tp, F::PS_GROUPS as int, F::PS_SUPPKEY_CODES as int, F::PS_SUPPKEY_BASE as int, prel, 1));
    assert(FC::int_col(prel, 1, gs, kbp, kcp));
    assert forall|s: int| 0 <= s < n implies #[trigger] (s / bsize) < kb.len() by {
        assert(s / bsize < FC::nblocks_of(n, bsize)) by {
            assert(s / bsize <= (n - 1) / bsize) by (nonlinear_arith) requires 0 <= s <= n - 1, bsize >= 1;
            assert(((n - 1) / bsize) * bsize <= n - 1) by (nonlinear_arith) requires n >= 1, bsize >= 1;
            assert((n - 1) / bsize < (n + bsize - 1) / bsize) by (nonlinear_arith) requires n >= 1, bsize >= 1;
        }
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] key_at(kc, kb, bsize, s) == FC::for_at(gs, kbp, kcp, s) by {
        FR::lemma_for_row(gp, n, bsize, kbp, kcp, s);
    }
    assert forall|s: int| 0 <= s < n implies {
        &&& i64::MIN <= #[trigger] key_at(kc, kb, bsize, s) <= i64::MAX
        &&& rel[s][0] == Val::Int(key_at(kc, kb, bsize, s))
    } by {
        assert(key_at(kc, kb, bsize, s) == FC::for_at(gs, kbp, kcp, s));
        assert(prel[s][1] == Val::Int(FC::for_at(gs, kbp, kcp, s)));
        assert(prel[s][1] == t4[s][1]);
        assert(rel[s][0] == t4[s][1]);
        assert(crate::spec::typing::value_in_column(rel[s][0], D::stored_columns_t0()[0]));
        assert(int_in_range(IntKind::Int8, key_at(kc, kb, bsize, s)));
    }
}

} // verus!
