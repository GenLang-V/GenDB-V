//! What the builder reads from storage `facts` (orders, stored by date with a row map): for a database bound to the
//! source, stored row `s` is canonical row `map_at(s)` (a bijection of `0 .. n`), and its o_custkey is `key_at(s)`;
//! both are frame-of-reference values over uniform groups of `bsize` rows (`base[s / bsize] + code[s]`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::spec::value::{Database, Row, Val};
use crate::spec::int::{int_in_range, IntKind};
use crate::link::source::lemma_proj_all_index;
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::facts::interface::common::read as FR;
use crate::stores::orders_custidx::declaration as D;

verus! {

/// Part indices of the orders columns of `facts` the builder reads.
pub const P_LAYOUT: usize = 48;
pub const P_GROUPS: usize = 49;
pub const P_PERM_CODES: usize = 50;
pub const P_PERM_BASE: usize = 51;
pub const P_CUST_CODES: usize = 54;
pub const P_CUST_BASE: usize = 55;

/// Canonical row of stored row `s`.
pub open spec fn map_at(pc: Seq<u32>, pb: Seq<u64>, bsize: int, s: int) -> int {
    pb[s / bsize] + pc[s]
}

/// o_custkey of stored row `s`.
pub open spec fn key_at(kc: Seq<u32>, kb: Seq<i64>, bsize: int, s: int) -> int {
    kb[s / bsize] + kc[s]
}

/// Canonical row `r` is the image of some stored row (`pc.len()` stored rows).
pub open spec fn mapped(pc: Seq<u32>, pb: Seq<u64>, bsize: int, r: int) -> bool {
    exists|s: int| 0 <= s < pc.len() && #[trigger] map_at(pc, pb, bsize, s) == r
}

/// The source facts the builder uses, over the orders parts `p` of `facts` and the indexed relation `rel`.
pub open spec fn src_ok(p: Seq<PartView>, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    let bsize = FC::u64s(p[P_LAYOUT as int])[1] as int;
    let (pc, pb) = (FC::u32s(p[P_PERM_CODES as int]), FC::u64s(p[P_PERM_BASE as int]));
    let (kc, kb) = (FC::u32s(p[P_CUST_CODES as int]), FC::i64s(p[P_CUST_BASE as int]));
    &&& p.len() == F::FACTS_PARTS
    &&& p[P_LAYOUT as int] is U64 && FC::u64s(p[P_LAYOUT as int]).len() == 2
    &&& bsize >= 1
    &&& p[P_PERM_CODES as int] is U32 && p[P_PERM_BASE as int] is U64
    &&& p[P_CUST_CODES as int] is U32 && p[P_CUST_BASE as int] is I64
    &&& pc.len() == n && kc.len() == n
    &&& forall|s: int| 0 <= s < n ==> #[trigger] (s / bsize) < pb.len() && s / bsize < kb.len()
    &&& forall|s: int| 0 <= s < n ==> 0 <= #[trigger] map_at(pc, pb, bsize, s) < n
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==>
            #[trigger] map_at(pc, pb, bsize, a) != #[trigger] map_at(pc, pb, bsize, b)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] mapped(pc, pb, bsize, r)
    &&& forall|s: int| 0 <= s < n ==> {
            &&& i64::MIN <= #[trigger] key_at(kc, kb, bsize, s) <= i64::MAX
            &&& rel[map_at(pc, pb, bsize, s)][0] == Val::Int(key_at(kc, kb, bsize, s))
        }
    &&& forall|r: int| 0 <= r < n ==> (#[trigger] rel[r]).len() == 1
}

/// For a database bound to `facts`, its parts and this storage's relation meet `src_ok`.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.facts, D::stored_relations(db)[0]),
{
    let p = sv.facts;
    let frels = crate::stores::facts::declaration::stored_relations(db);
    let rel = D::stored_relations(db)[0];
    assert(F::represents(p, frels));
    let tp = p.subrange(F::ORDERS_FIRST as int, (F::ORDERS_FIRST + F::OR_PARTS) as int);
    let orel = frels[1];
    assert(F::orders_ok(tp, orel));
    let t1 = db.tables[1];
    lemma_proj_all_index(t1, crate::stores::facts::declaration::stored_cols_t1());
    lemma_proj_all_index(t1, D::stored_cols_t0());
    D::lemma_stored_relations(db);
    let n = rel.len() as int;
    assert(orel.len() == n);
    let bsize = FC::u64s(tp[F::OR_LAYOUT as int])[1] as int;
    assert(tp[F::OR_LAYOUT as int] == p[P_LAYOUT as int]);
    assert(tp[F::OR_GROUPS as int] == p[P_GROUPS as int]);
    assert(tp[F::OR_PERM_CODES as int] == p[P_PERM_CODES as int]);
    assert(tp[F::OR_PERM_BASE as int] == p[P_PERM_BASE as int]);
    assert(tp[F::OR_CUSTKEY_CODES as int] == p[P_CUST_CODES as int]);
    assert(tp[F::OR_CUSTKEY_BASE as int] == p[P_CUST_BASE as int]);
    let gp = p[P_GROUPS as int];
    let gs = FC::u64s(gp);
    let (pcp, pbp) = (p[P_PERM_CODES as int], p[P_PERM_BASE as int]);
    let (kcp, kbp) = (p[P_CUST_CODES as int], p[P_CUST_BASE as int]);
    let (pc, pb) = (FC::u32s(pcp), FC::u64s(pbp));
    let (kc, kb) = (FC::u32s(kcp), FC::i64s(kbp));
    assert(FC::groups_part_ok(gp, n, bsize));
    FC::lemma_uniform_groups(gp, n, bsize);
    FC::lemma_nblocks(n, bsize);
    let rmap = FC::for_map(gs, pbp, pcp, n);
    assert(FC::is_perm(rmap, n));
    let rows = F::orders_rows(tp, orel);
    assert(F::orders_cols_ok(tp, rows));
    assert(FC::int_col(rows, 1, gs, kbp, kcp));
    assert forall|s: int| 0 <= s < n implies #[trigger] (s / bsize) < pb.len() && s / bsize < kb.len() by {
        assert(s / bsize < FC::nblocks_of(n, bsize)) by {
            assert(s / bsize <= (n - 1) / bsize) by (nonlinear_arith) requires 0 <= s <= n - 1, bsize >= 1;
            assert(((n - 1) / bsize) * bsize <= n - 1) by (nonlinear_arith) requires n >= 1, bsize >= 1;
            assert((n - 1) / bsize < (n + bsize - 1) / bsize) by (nonlinear_arith) requires n >= 1, bsize >= 1;
        }
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] map_at(pc, pb, bsize, s) == rmap[s] by {
        FR::lemma_for_row(gp, n, bsize, pbp, pcp, s);
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] key_at(kc, kb, bsize, s) == FC::for_at(gs, kbp, kcp, s) by {
        FR::lemma_for_row(gp, n, bsize, kbp, kcp, s);
    }
    assert forall|s: int| 0 <= s < n implies 0 <= #[trigger] map_at(pc, pb, bsize, s) < n by {
        assert(map_at(pc, pb, bsize, s) == rmap[s]);
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies
        #[trigger] map_at(pc, pb, bsize, a) != #[trigger] map_at(pc, pb, bsize, b) by {
        assert(map_at(pc, pb, bsize, a) == rmap[a]);
        assert(map_at(pc, pb, bsize, b) == rmap[b]);
    }
    assert forall|r: int| 0 <= r < n implies #[trigger] mapped(pc, pb, bsize, r) by {
        assert(FC::covered(rmap, r));
        let s = choose|s: int| 0 <= s < rmap.len() && rmap[s] == r;
        assert(map_at(pc, pb, bsize, s) == rmap[s]);
    }
    assert forall|s: int| 0 <= s < n implies {
        &&& i64::MIN <= #[trigger] key_at(kc, kb, bsize, s) <= i64::MAX
        &&& rel[map_at(pc, pb, bsize, s)][0] == Val::Int(key_at(kc, kb, bsize, s))
    } by {
        let r = map_at(pc, pb, bsize, s);
        assert(r == rmap[s]);
        assert(rows[s] == orel[r]);
        assert(rows[s][1] == Val::Int(FC::for_at(gs, kbp, kcp, s)));
        assert(orel[r][1] == t1[r][1]);
        assert(rel[r][0] == t1[r][1]);
        assert(crate::spec::typing::value_in_column(rel[r][0], D::stored_columns_t0()[0]));
        assert(int_in_range(IntKind::Int8, key_at(kc, kb, bsize, s)));
    }
}

} // verus!
