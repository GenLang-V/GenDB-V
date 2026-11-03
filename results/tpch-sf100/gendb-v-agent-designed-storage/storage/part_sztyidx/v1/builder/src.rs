//! What the builder reads from storage `custpart` (table part, canonical row order: stored row `r` is canonical row
//! `r`): the p_size of row `r` is the frame-of-reference value `key_at(r) = base[r / bsize] + code[r]` (U8 codes,
//! I64 bases) and its p_type is entry `tent_at(r) = tbase[r / bsize] + tcode[r]` (U8 codes, U64 bases) of the
//! p_type dictionary (U64 offsets, U8 bytes), over uniform groups of `bsize` rows.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::spec::value::{Database, Row, Val};
use crate::spec::int::{int_in_range, IntKind};
use crate::link::source::lemma_proj_all_index;
use crate::stores::custpart::interface as C;
use crate::stores::custpart::interface::common::colfmt as CF;
use crate::stores::custpart::interface::common::read as CR;
use crate::stores::part_sztyidx::declaration as D;
use crate::stores::part_sztyidx::interface::{key_text, texts_ok};

verus! {

/// Part indices of the part columns of `custpart` the builder reads.
pub const P_LAYOUT: usize = 21;
pub const P_GROUPS: usize = 22;
pub const P_TYPE_CODES: usize = 35;
pub const P_TYPE_BASE: usize = 36;
pub const P_TYPE_DOFFS: usize = 37;
pub const P_TYPE_DBYTES: usize = 38;
pub const P_SIZE_CODES: usize = 39;
pub const P_SIZE_BASE: usize = 40;

/// p_size of row `r`.
pub open spec fn key_at(sc: Seq<u8>, sb: Seq<i64>, bsize: int, r: int) -> int {
    sb[r / bsize] + sc[r]
}

/// p_type dictionary entry of row `r`.
pub open spec fn tent_at(tc: Seq<u8>, tb: Seq<u64>, bsize: int, r: int) -> int {
    tb[r / bsize] + tc[r]
}

/// The source facts the builder uses, over the parts `p` of `custpart` and the indexed relation `rel`.
pub open spec fn src_ok(p: Seq<PartView>, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    let bsize = CF::u64s(p[P_LAYOUT as int])[1] as int;
    let (sc, sb) = (CF::u8s(p[P_SIZE_CODES as int]), CF::i64s(p[P_SIZE_BASE as int]));
    let (tc, tb) = (CF::u8s(p[P_TYPE_CODES as int]), CF::u64s(p[P_TYPE_BASE as int]));
    let (doffs, dbytes) = (CF::u64s(p[P_TYPE_DOFFS as int]), CF::u8s(p[P_TYPE_DBYTES as int]));
    &&& p.len() == C::CUSTPART_PARTS
    &&& p[P_LAYOUT as int] is U64 && CF::u64s(p[P_LAYOUT as int]).len() == 2
    &&& bsize >= 1
    &&& p[P_SIZE_CODES as int] is U8 && p[P_SIZE_BASE as int] is I64
    &&& p[P_TYPE_CODES as int] is U8 && p[P_TYPE_BASE as int] is U64
    &&& p[P_TYPE_DOFFS as int] is U64 && p[P_TYPE_DBYTES as int] is U8
    &&& sc.len() == n && tc.len() == n
    &&& texts_ok(doffs, dbytes)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] (r / bsize) < sb.len() && (r / bsize) < tb.len()
    &&& forall|r: int| 0 <= r < n ==> {
            &&& i64::MIN <= #[trigger] key_at(sc, sb, bsize, r) <= i64::MAX
            &&& rel[r][1] == Val::Int(key_at(sc, sb, bsize, r))
            &&& 0 <= tent_at(tc, tb, bsize, r) < doffs.len() - 1
            &&& rel[r][0] == Val::Text(key_text(doffs, dbytes, tent_at(tc, tb, bsize, r)))
        }
    &&& forall|r: int| 0 <= r < n ==> (#[trigger] rel[r]).len() == 2
}

/// The per-row facts of `src_ok` from the column predicates of custpart's part relation `prel`.
proof fn lemma_src_rows(p: Seq<PartView>, prel: Seq<Row>, rel: Seq<Row>, bsize: int)
    requires
        p.len() == C::CUSTPART_PARTS,
        bsize == CF::u64s(p[P_LAYOUT as int])[1] as int,
        CF::groups_part_ok(p[P_GROUPS as int], rel.len() as int, bsize),
        prel.len() == rel.len(),
        forall|r: int| 0 <= r < rel.len() ==> (#[trigger] rel[r]).len() == 2 && rel[r][0] == prel[r][4] && rel[r][1] == prel[r][5],
        crate::link::source::rows_in_columns(rel, D::stored_columns_t0()),
        CF::int_col(prel, 5, CF::u64s(p[P_GROUPS as int]), p[P_SIZE_BASE as int], p[P_SIZE_CODES as int]),
        CF::dict_col(prel, 4, CF::u64s(p[P_GROUPS as int]), p[P_TYPE_BASE as int], p[P_TYPE_CODES as int],
            CF::u64s(p[P_TYPE_DOFFS as int]), CF::u8s(p[P_TYPE_DBYTES as int])),
        p[P_SIZE_CODES as int] is U8 && p[P_SIZE_BASE as int] is I64,
        p[P_TYPE_CODES as int] is U8 && p[P_TYPE_BASE as int] is U64,
    ensures
        forall|r: int| 0 <= r < rel.len() ==> {
            &&& i64::MIN <= #[trigger] key_at(CF::u8s(p[P_SIZE_CODES as int]), CF::i64s(p[P_SIZE_BASE as int]), bsize, r) <= i64::MAX
            &&& rel[r][1] == Val::Int(key_at(CF::u8s(p[P_SIZE_CODES as int]), CF::i64s(p[P_SIZE_BASE as int]), bsize, r))
            &&& 0 <= tent_at(CF::u8s(p[P_TYPE_CODES as int]), CF::u64s(p[P_TYPE_BASE as int]), bsize, r) < CF::u64s(p[P_TYPE_DOFFS as int]).len() - 1
            &&& rel[r][0] == Val::Text(key_text(CF::u64s(p[P_TYPE_DOFFS as int]), CF::u8s(p[P_TYPE_DBYTES as int]),
                    tent_at(CF::u8s(p[P_TYPE_CODES as int]), CF::u64s(p[P_TYPE_BASE as int]), bsize, r)))
        },
{
    let n = rel.len() as int;
    let gp = p[P_GROUPS as int];
    let (scp, sbp) = (p[P_SIZE_CODES as int], p[P_SIZE_BASE as int]);
    let (tcp, tbp) = (p[P_TYPE_CODES as int], p[P_TYPE_BASE as int]);
    let (sc, sb) = (CF::u8s(scp), CF::i64s(sbp));
    let (tc, tb) = (CF::u8s(tcp), CF::u64s(tbp));
    let (doffs, dbytes) = (CF::u64s(p[P_TYPE_DOFFS as int]), CF::u8s(p[P_TYPE_DBYTES as int]));
    assert forall|r: int| 0 <= r < n implies {
        &&& i64::MIN <= #[trigger] key_at(sc, sb, bsize, r) <= i64::MAX
        &&& rel[r][1] == Val::Int(key_at(sc, sb, bsize, r))
        &&& 0 <= tent_at(tc, tb, bsize, r) < doffs.len() - 1
        &&& rel[r][0] == Val::Text(key_text(doffs, dbytes, tent_at(tc, tb, bsize, r)))
    } by {
        CR::lemma_for_row(gp, n, bsize, sbp, scp, r);
        CR::lemma_for_row(gp, n, bsize, tbp, tcp, r);
        assert(prel[r][5] == Val::Int(CF::for_at(CF::u64s(gp), sbp, scp, r)));
        assert(rel[r].len() == 2);
        assert(crate::spec::typing::value_in_column(rel[r][1], D::stored_columns_t0()[1]));
        assert(int_in_range(IntKind::Int8, key_at(sc, sb, bsize, r)));
        assert(prel[r][4] == Val::Text(CF::text_of(doffs, dbytes, CF::for_at(CF::u64s(gp), tbp, tcp, r))));
    }
}

/// The column predicates of custpart's part relation `prel` (parts `p[PART_FIRST ..]`) the builder reads.
proof fn lemma_src_cols(p: Seq<PartView>, prel: Seq<Row>)
    requires
        p.len() == C::CUSTPART_PARTS,
        C::part_ok(p.subrange(C::PART_FIRST as int, (C::PART_FIRST + C::PA_PARTS) as int), prel),
    ensures
        p[P_LAYOUT as int] is U64 && CF::u64s(p[P_LAYOUT as int]).len() == 2,
        CF::u64s(p[P_LAYOUT as int])[1] >= 1,
        CF::groups_part_ok(p[P_GROUPS as int], prel.len() as int, CF::u64s(p[P_LAYOUT as int])[1] as int),
        CF::int_col(prel, 5, CF::u64s(p[P_GROUPS as int]), p[P_SIZE_BASE as int], p[P_SIZE_CODES as int]),
        CF::for_i64_shape(p, P_GROUPS as int, P_SIZE_CODES as int, P_SIZE_BASE as int, prel.len() as int),
        CF::dict_col(prel, 4, CF::u64s(p[P_GROUPS as int]), p[P_TYPE_BASE as int], p[P_TYPE_CODES as int],
            CF::u64s(p[P_TYPE_DOFFS as int]), CF::u8s(p[P_TYPE_DBYTES as int])),
        CF::for_u64_shape(p, P_GROUPS as int, P_TYPE_CODES as int, P_TYPE_BASE as int, prel.len() as int),
        p[P_SIZE_CODES as int] is U8 && p[P_SIZE_BASE as int] is I64,
        p[P_TYPE_CODES as int] is U8 && p[P_TYPE_BASE as int] is U64,
        p[P_TYPE_DOFFS as int] is U64 && p[P_TYPE_DBYTES as int] is U8,
        CF::u64s(p[P_TYPE_DOFFS as int]).len() >= 1,
        CF::text_parts_wf(CF::u64s(p[P_TYPE_DOFFS as int]), CF::u8s(p[P_TYPE_DBYTES as int]), CF::u64s(p[P_TYPE_DOFFS as int]).len() - 1),
{
    let tp = p.subrange(C::PART_FIRST as int, (C::PART_FIRST + C::PA_PARTS) as int);
    assert(tp[C::PA_LAYOUT as int] == p[P_LAYOUT as int]);
    assert(tp[C::PA_GROUPS as int] == p[P_GROUPS as int]);
    assert(tp[C::PA_SIZE_CODES as int] == p[P_SIZE_CODES as int]);
    assert(tp[C::PA_SIZE_BASE as int] == p[P_SIZE_BASE as int]);
    assert(tp[C::PA_TYPE_CODES as int] == p[P_TYPE_CODES as int]);
    assert(tp[C::PA_TYPE_BASE as int] == p[P_TYPE_BASE as int]);
    assert(tp[C::PA_TYPE_DICT_OFFS as int] == p[P_TYPE_DOFFS as int]);
    assert(tp[C::PA_TYPE_DICT_BYTES as int] == p[P_TYPE_DBYTES as int]);
    assert(C::table_layout_ok(tp, prel.len() as int));
    assert(CF::int_col_at(tp, C::PA_GROUPS as int, C::PA_SIZE_CODES as int, C::PA_SIZE_BASE as int, prel, 5));
    assert(CF::dict_col_at(tp, C::PA_GROUPS as int, C::PA_TYPE_CODES as int, C::PA_TYPE_BASE as int, C::PA_TYPE_DICT_OFFS as int, C::PA_TYPE_DICT_BYTES as int, prel, 4));
}

/// The facts of `src_ok` from custpart's part relation `prel` (parts `p[PART_FIRST ..]`), of which `rel` holds the
/// columns p_type and p_size.
proof fn lemma_src_part(p: Seq<PartView>, prel: Seq<Row>, rel: Seq<Row>)
    requires
        p.len() == C::CUSTPART_PARTS,
        C::part_ok(p.subrange(C::PART_FIRST as int, (C::PART_FIRST + C::PA_PARTS) as int), prel),
        prel.len() == rel.len(),
        forall|r: int| 0 <= r < rel.len() ==> (#[trigger] rel[r]).len() == 2 && rel[r][0] == prel[r][4] && rel[r][1] == prel[r][5],
        crate::link::source::rows_in_columns(rel, D::stored_columns_t0()),
    ensures src_ok(p, rel),
{
    lemma_src_cols(p, prel);
    lemma_src_frame(p, prel, rel);
}

/// `src_ok` from the column predicates (`lemma_src_cols`).
proof fn lemma_src_frame(p: Seq<PartView>, prel: Seq<Row>, rel: Seq<Row>)
    requires
        p.len() == C::CUSTPART_PARTS,
        p[P_LAYOUT as int] is U64 && CF::u64s(p[P_LAYOUT as int]).len() == 2,
        CF::u64s(p[P_LAYOUT as int])[1] >= 1,
        CF::groups_part_ok(p[P_GROUPS as int], prel.len() as int, CF::u64s(p[P_LAYOUT as int])[1] as int),
        CF::int_col(prel, 5, CF::u64s(p[P_GROUPS as int]), p[P_SIZE_BASE as int], p[P_SIZE_CODES as int]),
        CF::for_i64_shape(p, P_GROUPS as int, P_SIZE_CODES as int, P_SIZE_BASE as int, prel.len() as int),
        CF::dict_col(prel, 4, CF::u64s(p[P_GROUPS as int]), p[P_TYPE_BASE as int], p[P_TYPE_CODES as int],
            CF::u64s(p[P_TYPE_DOFFS as int]), CF::u8s(p[P_TYPE_DBYTES as int])),
        CF::for_u64_shape(p, P_GROUPS as int, P_TYPE_CODES as int, P_TYPE_BASE as int, prel.len() as int),
        p[P_SIZE_CODES as int] is U8 && p[P_SIZE_BASE as int] is I64,
        p[P_TYPE_CODES as int] is U8 && p[P_TYPE_BASE as int] is U64,
        p[P_TYPE_DOFFS as int] is U64 && p[P_TYPE_DBYTES as int] is U8,
        CF::u64s(p[P_TYPE_DOFFS as int]).len() >= 1,
        CF::text_parts_wf(CF::u64s(p[P_TYPE_DOFFS as int]), CF::u8s(p[P_TYPE_DBYTES as int]), CF::u64s(p[P_TYPE_DOFFS as int]).len() - 1),
        prel.len() == rel.len(),
        forall|r: int| 0 <= r < rel.len() ==> (#[trigger] rel[r]).len() == 2 && rel[r][0] == prel[r][4] && rel[r][1] == prel[r][5],
        crate::link::source::rows_in_columns(rel, D::stored_columns_t0()),
    ensures src_ok(p, rel),
{
    let n = rel.len() as int;
    let bsize = CF::u64s(p[P_LAYOUT as int])[1] as int;
    let gp = p[P_GROUPS as int];
    let (sb, tb) = (CF::i64s(p[P_SIZE_BASE as int]), CF::u64s(p[P_TYPE_BASE as int]));
    let (doffs, dbytes) = (CF::u64s(p[P_TYPE_DOFFS as int]), CF::u8s(p[P_TYPE_DBYTES as int]));
    CF::lemma_uniform_groups(gp, n, bsize);
    CF::lemma_nblocks(n, bsize);
    assert forall|t: int| 0 <= t < doffs.len() - 1 implies #[trigger] doffs[t] <= doffs[t + 1] && doffs[t + 1] <= dbytes.len() by {
        assert(CF::text_range_ok(doffs, dbytes, t));
    }
    assert forall|r: int| 0 <= r < n implies #[trigger] (r / bsize) < sb.len() && (r / bsize) < tb.len() by {
        assert(r / bsize < CF::nblocks_of(n, bsize)) by {
            assert(r / bsize <= (n - 1) / bsize) by (nonlinear_arith) requires 0 <= r <= n - 1, bsize >= 1;
            assert(((n - 1) / bsize) * bsize <= n - 1) by (nonlinear_arith) requires n >= 1, bsize >= 1;
            assert((n - 1) / bsize < (n + bsize - 1) / bsize) by (nonlinear_arith) requires n >= 1, bsize >= 1;
        }
    }
    lemma_src_rows(p, prel, rel, bsize);
}

/// For a database bound to `custpart`, its parts and this storage's relation meet `src_ok`.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.custpart, D::stored_relations(db)[0]),
{
    let p = sv.custpart;
    let crels = crate::stores::custpart::declaration::stored_relations(db);
    let rel = D::stored_relations(db)[0];
    assert(C::represents(p, crels));
    let prel = crels[1];
    let t3 = db.tables[3];
    lemma_proj_all_index(t3, crate::stores::custpart::declaration::stored_cols_t1());
    lemma_proj_all_index(t3, D::stored_cols_t0());
    D::lemma_stored_relations(db);
    assert(prel.len() == rel.len());
    assert forall|r: int| 0 <= r < rel.len() implies (#[trigger] rel[r]).len() == 2 && rel[r][0] == prel[r][4] && rel[r][1] == prel[r][5] by {
        assert(prel[r][5] == t3[r][5]);
        assert(prel[r][4] == t3[r][4]);
    }
    lemma_src_part(p, prel, rel);
}

} // verus!
