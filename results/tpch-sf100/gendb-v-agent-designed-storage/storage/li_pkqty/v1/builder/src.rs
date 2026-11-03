//! What the builder reads from storage `facts` (lineitem: stored by order with a row map, and a key index on
//! l_partkey), stated with this storage's interface definitions over the source parts `fp`: for a database bound to
//! the source, the layout and column shapes (`base_ok`), the row map and the stored values of
//! `[l_partkey, l_quantity, l_extendedprice]` (`row_map_ok`, `rows_ok`), keys inside `i64`, quantities inside
//! numeric(15, 2) (`|coefficient| < 10^15`), and, when the key index has kind 2, its positions as a bijection of the stored rows with
//! nondecreasing keys (`index_ok`; `kirow(p)` is the stored row at position `p` of facts' key index).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::spec::value::{Database, Row, Val};
use crate::spec::int::{int_in_range, IntKind};
use crate::spec::numeric::{abs, pow10};
use crate::link::source::lemma_proj_all_index;
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::facts::interface::common::keyidx as FK;
use crate::stores::facts::interface::common::read as FR;
use crate::stores::facts::declaration as FD;
use crate::stores::li_pkqty::declaration as D;
use crate::stores::li_pkqty::interface::*;

verus! {

/// Quantity coefficients lie strictly inside `(-QMAX, QMAX)` (numeric(15, 2): `10^15`).
pub const QMAX: i64 = 1_000_000_000_000_000;

/// lineitem: U32 codes of facts' l_partkey key index (stored row at each index position).
pub const LI_KEYIDX_CODES: usize = 45;
/// lineitem: U64 block bases of facts' l_partkey key index.
pub const LI_KEYIDX_BASE: usize = 46;
/// lineitem: U64 `[kind]` of facts' l_partkey key index.
pub const LI_KEYIDX_KIND: usize = 47;

/// The key index kind of the source.
pub open spec fn kind_of(fp: Seq<PartView>) -> u64 {
    u64s(fp[LI_KEYIDX_KIND as int])[0]
}

/// Stored row at position `p` of facts' key index.
pub open spec fn kirow(fp: Seq<PartView>, p: int) -> int {
    u64s(fp[LI_KEYIDX_BASE as int])[p / bsize(fp)] + u32s(fp[LI_KEYIDX_CODES as int])[p]
}

/// Stored row `s` is at some position of facts' key index.
pub open spec fn kindexed(fp: Seq<PartView>, n: int, s: int) -> bool {
    exists|p: int| 0 <= p < n && #[trigger] kirow(fp, p) == s
}

/// Layout and column shapes over the source parts (as `li_shape`, without the part count of this storage).
pub open spec fn base_ok(fp: Seq<PartView>, n: int) -> bool {
    let bs = bsize(fp);
    &&& fp.len() == FACTS_PARTS
    &&& fp[LI_LAYOUT as int] is U64 && u64s(fp[LI_LAYOUT as int]).len() == 2
    &&& n_rows(fp) == n
    &&& bs >= 1
    &&& n + bs <= u64::MAX
    &&& fp[LI_PERM_CODES as int] is U32 && fp[LI_PERM_BASE as int] is U64
    &&& for_len_ok(u32s(fp[LI_PERM_CODES as int]).len() as int, u64s(fp[LI_PERM_BASE as int]).len() as int, n, bs)
    &&& fp[LI_PARTKEY_CODES as int] is U32 && fp[LI_PARTKEY_BASE as int] is I64
    &&& for_len_ok(u32s(fp[LI_PARTKEY_CODES as int]).len() as int, i64s(fp[LI_PARTKEY_BASE as int]).len() as int, n, bs)
    &&& fp[LI_QUANTITY_CODES as int] is U16 && fp[LI_QUANTITY_BASE as int] is I64
    &&& for_len_ok(u16s(fp[LI_QUANTITY_CODES as int]).len() as int, i64s(fp[LI_QUANTITY_BASE as int]).len() as int, n, bs)
    &&& fp[LI_EXTENDEDPRICE_CODES as int] is U32 && fp[LI_EXTENDEDPRICE_BASE as int] is I64
    &&& for_len_ok(u32s(fp[LI_EXTENDEDPRICE_CODES as int]).len() as int,
            i64s(fp[LI_EXTENDEDPRICE_BASE as int]).len() as int, n, bs)
    &&& fp[LI_KEYIDX_KIND as int] is U64 && u64s(fp[LI_KEYIDX_KIND as int]).len() == 1
    &&& forall|s: int| 0 <= s < n ==> i64::MIN <= #[trigger] key_at(fp, s) <= i64::MAX
    &&& forall|s: int| 0 <= s < n ==> -QMAX < #[trigger] qty_at(fp, s) < QMAX
}

/// Keys do not decrease from key index position `p` to `p + 1`.
pub open spec fn ksorted_at(fp: Seq<PartView>, p: int) -> bool {
    key_at(fp, kirow(fp, p)) <= key_at(fp, kirow(fp, p + 1))
}

/// Under kind 2, the key index: positions are a bijection of the stored rows, in nondecreasing key order.
pub open spec fn index_ok(fp: Seq<PartView>, n: int) -> bool {
    &&& fp[LI_KEYIDX_CODES as int] is U32 && fp[LI_KEYIDX_BASE as int] is U64
    &&& for_len_ok(u32s(fp[LI_KEYIDX_CODES as int]).len() as int, u64s(fp[LI_KEYIDX_BASE as int]).len() as int, n, bsize(fp))
    &&& forall|p: int| 0 <= p < n ==> 0 <= #[trigger] kirow(fp, p) < n
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] kirow(fp, a) != #[trigger] kirow(fp, b)
    &&& forall|s: int| 0 <= s < n ==> #[trigger] kindexed(fp, n, s)
    &&& forall|p: int| 0 <= p < n - 1 ==> #[trigger] ksorted_at(fp, p)
}

/// Everything the builder uses about the source.
pub open spec fn src_ok(fp: Seq<PartView>, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    &&& base_ok(fp, n)
    &&& row_map_ok(fp, n)
    &&& rows_ok(fp, rel)
    &&& kind_of(fp) == 2 ==> index_ok(fp, n)
}

/// The FOR value of `colfmt` is the block base plus the code (`bsize` rows per block).
proof fn lemma_for_value(gp: PartView, n: int, bs: int, base: PartView, codes: PartView, s: int)
    requires
        FC::groups_part_ok(gp, n, bs),
        0 <= s < n,
    ensures
        FC::for_at(FC::u64s(gp), base, codes, s) == FC::base_at(base, s / bs) + FC::code_at(codes, s),
{
    FR::lemma_for_row(gp, n, bs, base, codes, s);
}

/// One base per block: the bases cover the rows.
proof fn lemma_bases_cover(gp: PartView, n: int, bs: int, nb: int)
    requires
        FC::groups_part_ok(gp, n, bs),
        nb == FC::u64s(gp).len() - 1,
    ensures
        nb * bs >= n,
{
    FC::lemma_uniform_groups(gp, n, bs);
    FC::lemma_nblocks(n, bs);
}

/// The lineitem parts of facts.
pub open spec fn li_tp(fp: Seq<PartView>) -> Seq<PartView> {
    fp.subrange(F::LINEITEM_FIRST as int, (F::LINEITEM_FIRST + F::LI_PARTS) as int)
}

/// The conjuncts of facts' `represents` about lineitem that the builder reads.
pub open spec fn li_conj(fp: Seq<PartView>, rel15: Seq<Row>) -> bool {
    let tp = li_tp(fp);
    let n = rel15.len() as int;
    let srows = F::lineitem_rows(tp, rel15);
    let bs = FC::u64s(tp[F::LI_LAYOUT as int])[1] as int;
    &&& fp.len() == FACTS_PARTS
    &&& F::table_layout_ok(tp, n)
    &&& tp[F::LI_PERM_CODES as int] is U32
    &&& FC::perm_col_at(tp, F::LI_GROUPS as int, F::LI_PERM_CODES as int, F::LI_PERM_BASE as int, n)
    &&& tp[F::LI_PARTKEY_CODES as int] is U32
    &&& FC::int_col_at(tp, F::LI_GROUPS as int, F::LI_PARTKEY_CODES as int, F::LI_PARTKEY_BASE as int, srows, 1)
    &&& tp[F::LI_QUANTITY_CODES as int] is U16
    &&& FC::num_col_at(tp, F::LI_GROUPS as int, F::LI_QUANTITY_CODES as int, F::LI_QUANTITY_BASE as int, srows, 4, 2)
    &&& tp[F::LI_EXTENDEDPRICE_CODES as int] is U32
    &&& FC::num_col_at(tp, F::LI_GROUPS as int, F::LI_EXTENDEDPRICE_CODES as int, F::LI_EXTENDEDPRICE_BASE as int, srows, 5, 2)
    &&& tp[F::LI_KEYIDX_CODES as int] is U32 && tp[F::LI_KEYIDX_BASE as int] is U64
    &&& tp[F::LI_KEYIDX_KIND as int] is U64 && FC::u64s(tp[F::LI_KEYIDX_KIND as int]).len() == 1
    &&& FK::keyidx_ok(FC::u32s(tp[F::LI_PARTKEY_CODES as int]), FC::i64s(tp[F::LI_PARTKEY_BASE as int]),
            FC::u32s(tp[F::LI_KEYIDX_CODES as int]), FC::u64s(tp[F::LI_KEYIDX_BASE as int]), bs,
            FC::u64s(tp[F::LI_KEYIDX_KIND as int])[0], n)
}

/// facts' `represents` gives `li_conj` (conjuncts only).
proof fn lemma_li_conj(fp: Seq<PartView>, frels: Seq<Seq<Row>>)
    requires F::represents(fp, frels),
    ensures li_conj(fp, frels[0]),
{
    let tp = li_tp(fp);
    assert(F::lineitem_ok(tp, frels[0]));
    assert(F::lineitem_cols_ok(tp, F::lineitem_rows(tp, frels[0])));
}

/// The lineitem parts are the first parts of facts.
proof fn lemma_tp(fp: Seq<PartView>)
    requires fp.len() == FACTS_PARTS,
    ensures forall|k: int| 0 <= k < 48 ==> #[trigger] li_tp(fp)[k] == fp[k],
{
}

/// Layout and column shapes.
proof fn lemma_src_shape(fp: Seq<PartView>, rel15: Seq<Row>)
    requires li_conj(fp, rel15),
    ensures ({
        let n = rel15.len() as int;
        let bs = bsize(fp);
        &&& fp.len() == FACTS_PARTS
        &&& fp[LI_LAYOUT as int] is U64 && u64s(fp[LI_LAYOUT as int]).len() == 2
        &&& n_rows(fp) == n
        &&& bs >= 1
        &&& n + bs <= u64::MAX
        &&& FC::groups_part_ok(fp[F::LI_GROUPS as int], n, bs)
        &&& fp[LI_PERM_CODES as int] is U32 && fp[LI_PERM_BASE as int] is U64
        &&& for_len_ok(u32s(fp[LI_PERM_CODES as int]).len() as int, u64s(fp[LI_PERM_BASE as int]).len() as int, n, bs)
        &&& fp[LI_PARTKEY_CODES as int] is U32 && fp[LI_PARTKEY_BASE as int] is I64
        &&& for_len_ok(u32s(fp[LI_PARTKEY_CODES as int]).len() as int, i64s(fp[LI_PARTKEY_BASE as int]).len() as int, n, bs)
        &&& fp[LI_QUANTITY_CODES as int] is U16 && fp[LI_QUANTITY_BASE as int] is I64
        &&& for_len_ok(u16s(fp[LI_QUANTITY_CODES as int]).len() as int, i64s(fp[LI_QUANTITY_BASE as int]).len() as int, n, bs)
        &&& fp[LI_EXTENDEDPRICE_CODES as int] is U32 && fp[LI_EXTENDEDPRICE_BASE as int] is I64
        &&& for_len_ok(u32s(fp[LI_EXTENDEDPRICE_CODES as int]).len() as int,
                i64s(fp[LI_EXTENDEDPRICE_BASE as int]).len() as int, n, bs)
        &&& fp[LI_KEYIDX_KIND as int] is U64 && u64s(fp[LI_KEYIDX_KIND as int]).len() == 1
    }),
{
    hide(FC::perm_col_at);
    hide(FK::keyidx_ok);
    hide(F::lineitem_rows);
    let tp = li_tp(fp);
    lemma_tp(fp);
    let n = rel15.len() as int;
    let gp = tp[F::LI_GROUPS as int];
    let bs = FC::u64s(tp[F::LI_LAYOUT as int])[1] as int;
    assert(FC::groups_part_ok(gp, n, bs));
    let nb = FC::u64s(gp).len() - 1;
    lemma_bases_cover(gp, n, bs, nb);
    reveal(FC::perm_col_at);
    assert(FC::for_u64_shape(tp, F::LI_GROUPS as int, F::LI_PERM_CODES as int, F::LI_PERM_BASE as int, n));
    assert(F::lineitem_rows(tp, rel15).len() == n) by {
        reveal(F::lineitem_rows);
    }
    assert(FC::for_i64_shape(tp, F::LI_GROUPS as int, F::LI_PARTKEY_CODES as int, F::LI_PARTKEY_BASE as int, n));
    assert(FC::for_i64_shape(tp, F::LI_GROUPS as int, F::LI_QUANTITY_CODES as int, F::LI_QUANTITY_BASE as int, n));
    assert(FC::for_i64_shape(tp, F::LI_GROUPS as int, F::LI_EXTENDEDPRICE_CODES as int, F::LI_EXTENDEDPRICE_BASE as int, n));
}

/// The row map is a bijection.
proof fn lemma_src_map(fp: Seq<PartView>, rel15: Seq<Row>)
    requires li_conj(fp, rel15),
    ensures row_map_ok(fp, rel15.len() as int),
        forall|s: int| 0 <= s < rel15.len() ==> #[trigger] map_at(fp, s)
            == FC::for_map(FC::u64s(fp[F::LI_GROUPS as int]), fp[LI_PERM_BASE as int], fp[LI_PERM_CODES as int], rel15.len() as int)[s],
{
    hide(FC::int_col_at);
    hide(FC::num_col_at);
    hide(FK::keyidx_ok);
    let tp = li_tp(fp);
    lemma_tp(fp);
    let n = rel15.len() as int;
    let gp = tp[F::LI_GROUPS as int];
    let gs = FC::u64s(gp);
    let bs = FC::u64s(tp[F::LI_LAYOUT as int])[1] as int;
    assert(bs == bsize(fp));
    assert(FC::groups_part_ok(gp, n, bs));
    let (pcp, pbp) = (tp[F::LI_PERM_CODES as int], tp[F::LI_PERM_BASE as int]);
    let rmap = FC::for_map(gs, pbp, pcp, n);
    assert(FC::is_perm(rmap, n));
    assert forall|s: int| 0 <= s < n implies #[trigger] map_at(fp, s) == rmap[s] by {
        lemma_for_value(gp, n, bs, pbp, pcp, s);
    }
    assert forall|s: int| 0 <= s < n implies 0 <= #[trigger] map_at(fp, s) < n by {
        assert(map_at(fp, s) == rmap[s]);
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies
        #[trigger] map_at(fp, a) != #[trigger] map_at(fp, b) by {
        assert(map_at(fp, a) == rmap[a]);
        assert(map_at(fp, b) == rmap[b]);
    }
    assert forall|r: int| 0 <= r < n implies #[trigger] mapped(fp, n, r) by {
        assert(FC::covered(rmap, r));
        let s = choose|s: int| 0 <= s < rmap.len() && rmap[s] == r;
        assert(map_at(fp, s) == rmap[s]);
    }
}

/// The stored values of `[l_partkey, l_quantity, l_extendedprice]`.
proof fn lemma_src_rows(fp: Seq<PartView>, rel15: Seq<Row>, rel: Seq<Row>, t0: Seq<Row>)
    requires
        li_conj(fp, rel15),
        rel15 == crate::link::query::proj_all(t0, FD::stored_cols_t0()),
        rel == crate::link::query::proj_all(t0, D::stored_cols_t0()),
        crate::link::source::rows_in_columns(rel, D::stored_columns_t0()),
    ensures
        rows_ok(fp, rel),
        forall|s: int| 0 <= s < rel.len() ==> i64::MIN <= #[trigger] key_at(fp, s) <= i64::MAX,
        forall|s: int| 0 <= s < rel.len() ==> -QMAX < #[trigger] qty_at(fp, s) < QMAX,
{
    hide(FC::perm_col_at);
    hide(FK::keyidx_ok);
    let tp = li_tp(fp);
    lemma_tp(fp);
    lemma_proj_all_index(t0, FD::stored_cols_t0());
    lemma_proj_all_index(t0, D::stored_cols_t0());
    let n = rel15.len() as int;
    let gp = tp[F::LI_GROUPS as int];
    let gs = FC::u64s(gp);
    let bs = FC::u64s(tp[F::LI_LAYOUT as int])[1] as int;
    assert(bs == bsize(fp));
    let (pcp, pbp) = (tp[F::LI_PERM_CODES as int], tp[F::LI_PERM_BASE as int]);
    let rmap = FC::for_map(gs, pbp, pcp, n);
    lemma_src_map(fp, rel15);
    let srows = F::lineitem_rows(tp, rel15);
    assert(srows == FC::stored_rows(rel15, rmap));
    let (kcp, kbp) = (tp[F::LI_PARTKEY_CODES as int], tp[F::LI_PARTKEY_BASE as int]);
    let (qcp, qbp) = (tp[F::LI_QUANTITY_CODES as int], tp[F::LI_QUANTITY_BASE as int]);
    let (xcp, xbp) = (tp[F::LI_EXTENDEDPRICE_CODES as int], tp[F::LI_EXTENDEDPRICE_BASE as int]);
    assert(FC::int_col(srows, 1, gs, kbp, kcp));
    assert(FC::num_col(srows, 4, 2, gs, qbp, qcp));
    assert(FC::num_col(srows, 5, 2, gs, xbp, xcp));
    assert(pow10(15) == QMAX) by (compute);
    assert forall|s: int| 0 <= s < n implies
        rel[#[trigger] map_at(fp, s)] == li_row(key_at(fp, s), qty_at(fp, s), price_at(fp, s))
        && i64::MIN <= key_at(fp, s) <= i64::MAX && -QMAX < qty_at(fp, s) < QMAX by {
        let r = map_at(fp, s);
        assert(r == rmap[s]);
        lemma_for_value(gp, n, bs, kbp, kcp, s);
        lemma_for_value(gp, n, bs, qbp, qcp, s);
        lemma_for_value(gp, n, bs, xbp, xcp, s);
        assert(srows[s] == rel15[r]);
        assert(srows[s][1] == Val::Int(key_at(fp, s)));
        assert(srows[s][4] == (Val::Num { coeff: qty_at(fp, s), scale: 2 }));
        assert(srows[s][5] == (Val::Num { coeff: price_at(fp, s), scale: 2 }));
        assert(rel15[r][1] == t0[r][1]);
        assert(rel15[r][4] == t0[r][4]);
        assert(rel15[r][5] == t0[r][5]);
        assert(rel[r][0] == t0[r][1]);
        assert(rel[r][1] == t0[r][4]);
        assert(rel[r][2] == t0[r][5]);
        assert(rel[r].len() == 3);
        assert(rel[r] =~= li_row(key_at(fp, s), qty_at(fp, s), price_at(fp, s)));
        assert(crate::spec::typing::value_in_column(rel[r][0], D::stored_columns_t0()[0]));
        assert(int_in_range(IntKind::Int8, key_at(fp, s)));
        assert(crate::spec::typing::value_in_column(rel[r][1], D::stored_columns_t0()[1]));
        assert(abs(qty_at(fp, s)) < pow10(15));
    }
    assert forall|s: int| 0 <= s < n implies i64::MIN <= #[trigger] key_at(fp, s) <= i64::MAX by {
        assert(rel[map_at(fp, s)] == li_row(key_at(fp, s), qty_at(fp, s), price_at(fp, s)));
    }
    assert forall|s: int| 0 <= s < n implies -QMAX < #[trigger] qty_at(fp, s) < QMAX by {
        assert(rel[map_at(fp, s)] == li_row(key_at(fp, s), qty_at(fp, s), price_at(fp, s)));
    }
}

/// Under kind 2, the key index.
proof fn lemma_src_index(fp: Seq<PartView>, rel15: Seq<Row>)
    requires li_conj(fp, rel15), kind_of(fp) == 2,
    ensures index_ok(fp, rel15.len() as int),
{
    hide(FC::perm_col_at);
    hide(FC::int_col_at);
    hide(FC::num_col_at);
    hide(F::table_layout_ok);
    let tp = li_tp(fp);
    lemma_tp(fp);
    let n = rel15.len() as int;
    let bs = FC::u64s(tp[F::LI_LAYOUT as int])[1] as int;
    assert(bs == bsize(fp));
    let kind = kind_of(fp);
    let (kcp, kbp) = (tp[F::LI_PARTKEY_CODES as int], tp[F::LI_PARTKEY_BASE as int]);
    let (icp, ibp) = (tp[F::LI_KEYIDX_CODES as int], tp[F::LI_KEYIDX_BASE as int]);
    let (kc, kb, ic, ib) = (FC::u32s(kcp), FC::i64s(kbp), FC::u32s(icp), FC::u64s(ibp));
    assert(FK::keyidx_ok(kc, kb, ic, ib, bs, kind, n));
    let im = FK::idx_map(ic, ib, bs, n);
    assert(FC::is_perm(im, n));
    assert forall|p: int| 0 <= p < n implies #[trigger] kirow(fp, p) == im[p] by {}
    assert forall|p: int| 0 <= p < n implies 0 <= #[trigger] kirow(fp, p) < n by {
        assert(kirow(fp, p) == im[p]);
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies
        #[trigger] kirow(fp, a) != #[trigger] kirow(fp, b) by {
        assert(kirow(fp, a) == im[a]);
        assert(kirow(fp, b) == im[b]);
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] kindexed(fp, n, s) by {
        assert(FC::covered(im, s));
        let p = choose|p: int| 0 <= p < im.len() && im[p] == s;
        assert(kirow(fp, p) == im[p]);
    }
    assert forall|p: int| 0 <= p < n - 1 implies #[trigger] ksorted_at(fp, p) by {
        assert(FK::sorted_at(kc, kb, ic, ib, bs, kind, p));
        assert(FK::irow(kind, ic, ib, bs, p) == kirow(fp, p));
        assert(FK::irow(kind, ic, ib, bs, p + 1) == kirow(fp, p + 1));
    }
}

/// For a database bound to `facts`, its parts and this storage's relation meet `src_ok`.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.facts, D::stored_relations(db)[0]),
{
    hide(li_conj);
    let fp = sv.facts;
    let frels = FD::stored_relations(db);
    let rel = D::stored_relations(db)[0];
    assert(F::represents(fp, frels));
    lemma_li_conj(fp, frels);
    let rel15 = frels[0];
    let t0 = db.tables[0];
    D::lemma_stored_relations(db);
    FD::lemma_stored_relations(db);
    lemma_proj_all_index(t0, FD::stored_cols_t0());
    lemma_proj_all_index(t0, D::stored_cols_t0());
    assert(rel15.len() == rel.len());
    lemma_src_shape(fp, rel15);
    lemma_src_map(fp, rel15);
    lemma_src_rows(fp, rel15, rel, t0);
    if kind_of(fp) == 2 {
        lemma_src_index(fp, rel15);
    }
}

} // verus!
