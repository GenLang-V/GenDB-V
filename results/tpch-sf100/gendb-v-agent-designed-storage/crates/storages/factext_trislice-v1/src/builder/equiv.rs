//! The inherited parts: `factext_trisig`'s `represents` (the source's interface, `S`) gives this storage's
//! restatement of it (`D::base_represents` and `D::sigs_ok`, the same definitions in this storage's interface). Each
//! lemma unfolds one definition of both copies; the non-syntactic steps are the group of a row (`group_of`, a
//! `choose`), which both copies pin to the unique group containing the row (`lemma_for_at_same`), and the recursive
//! signature (`lemma_sig_upto_same`, by induction).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::spec::value::{Database, Row, Val};
use crate::stores::factext_trisig::interface as S;
use crate::stores::factext_trislice::interface as D;
use crate::stores::factext_trisig::interface::common::colfmt as SC;
use crate::stores::factext_trislice::interface::common::colfmt as DC;
use crate::stores::factext_trisig::interface::trisig as ST;
use crate::stores::factext_trislice::interface::trisig as DT;

verus! {

/// The part views of both copies agree.
proof fn lemma_views_same(p: PartView)
    ensures
        SC::u64s(p) == DC::u64s(p),
        SC::u8s(p) == DC::u8s(p),
        SC::u32s(p) == DC::u32s(p),
        SC::i64s(p) == DC::i64s(p),
        SC::is_code_part(p) == DC::is_code_part(p),
        forall|i: int| #[trigger] SC::code_at(p, i) == DC::code_at(p, i),
        forall|g: int| #[trigger] SC::base_at(p, g) == DC::base_at(p, g),
{
}

/// Uniform groups: the same sequence in both copies.
proof fn lemma_groups_part_same(p: PartView, n: int, bsize: int)
    requires SC::groups_part_ok(p, n, bsize),
    ensures
        DC::groups_part_ok(p, n, bsize),
        SC::groups_wf(SC::u64s(p), n),
        DC::groups_wf(DC::u64s(p), n),
{
    lemma_views_same(p);
    assert(SC::uniform_gs(n, bsize) =~= DC::uniform_gs(n, bsize));
    SC::lemma_uniform_groups(p, n, bsize);
    DC::lemma_uniform_groups(p, n, bsize);
}

/// A table frame.
proof fn lemma_layout_same(tp: Seq<PartView>, n: int)
    requires S::table_layout_ok(tp, n),
    ensures
        D::table_layout_ok(tp, n),
        SC::groups_wf(SC::u64s(tp[1]), n),
{
    lemma_views_same(tp[0]);
    lemma_groups_part_same(tp[1], n, SC::u64s(tp[0])[1] as int);
}

/// A plain text column.
proof fn lemma_text_col_same(parts: Seq<PartView>, op: int, yp: int, rows: Seq<Row>, c: int)
    requires SC::text_col_at(parts, op, yp, rows, c),
    ensures DC::text_col_at(parts, op, yp, rows, c),
{
    lemma_views_same(parts[op]);
    lemma_views_same(parts[yp]);
    let (offs, bytes) = (SC::u64s(parts[op]), SC::u8s(parts[yp]));
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] DC::text_range_ok(offs, bytes, j) by {
        assert(SC::text_range_ok(offs, bytes, j));
    }
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j][c] == Val::Text(DC::text_of(offs, bytes, j)) by {
        assert(rows[j][c] == Val::Text(SC::text_of(offs, bytes, j)));
    }
}

/// A frame-of-reference value: both copies pick the unique group of the row.
proof fn lemma_for_at_same(gs: Seq<u64>, n: int, base: PartView, codes: PartView, j: int)
    requires
        SC::groups_wf(gs, n),
        0 <= j < n,
    ensures
        SC::for_at(gs, base, codes, j) == DC::for_at(gs, base, codes, j),
{
    SC::lemma_group_of(gs, n, j);
    let g = SC::group_of(gs, j);
    assert(DC::groups_wf(gs, n));
    assert(DC::in_group(gs, g, j));
    DC::lemma_group_of_unique(gs, n, g, j);
    lemma_views_same(base);
    lemma_views_same(codes);
}

/// A dictionary column over the groups `gp`.
proof fn lemma_dict_col_same(parts: Seq<PartView>, gp: int, cp: int, bp: int, op: int, yp: int, rows: Seq<Row>, c: int)
    requires
        SC::dict_col_at(parts, gp, cp, bp, op, yp, rows, c),
        SC::groups_wf(SC::gs_at(parts, gp), rows.len() as int),
    ensures
        DC::dict_col_at(parts, gp, cp, bp, op, yp, rows, c),
{
    lemma_views_same(parts[gp]);
    lemma_views_same(parts[cp]);
    lemma_views_same(parts[bp]);
    lemma_views_same(parts[op]);
    lemma_views_same(parts[yp]);
    let gs = SC::gs_at(parts, gp);
    let (doffs, dbytes) = (SC::u64s(parts[op]), SC::u8s(parts[yp]));
    let k = doffs.len() - 1;
    assert forall|j: int| 0 <= j < k implies #[trigger] DC::text_range_ok(doffs, dbytes, j) by {
        assert(SC::text_range_ok(doffs, dbytes, j));
    }
    assert forall|a: int| 0 <= a < k - 1 implies
        #[trigger] crate::spec::text::lex_cmp(DC::text_of(doffs, dbytes, a), DC::text_of(doffs, dbytes, a + 1)) < 0 by {
        assert(crate::spec::text::lex_cmp(SC::text_of(doffs, dbytes, a), SC::text_of(doffs, dbytes, a + 1)) < 0);
    }
    assert forall|j: int| 0 <= j < rows.len() implies {
        &&& 0 <= DC::for_at(gs, parts[bp], parts[cp], j) < doffs.len() - 1
        &&& #[trigger] rows[j][c] == Val::Text(DC::text_of(doffs, dbytes, DC::for_at(gs, parts[bp], parts[cp], j)))
    } by {
        lemma_for_at_same(gs, rows.len() as int, parts[bp], parts[cp], j);
        assert(rows[j][c] == Val::Text(SC::text_of(doffs, dbytes, SC::for_at(gs, parts[bp], parts[cp], j))));
    }
}

/// Table lineitem (l_comment).
proof fn lemma_lineitem_same(tp: Seq<PartView>, rel: Seq<Row>)
    requires S::lineitem_ok(tp, rel),
    ensures D::lineitem_ok(tp, rel),
{
    lemma_layout_same(tp, rel.len() as int);
    lemma_text_col_same(tp, S::LT_COMMENT_OFFS as int, S::LT_COMMENT_BYTES as int, rel, 0);
}

/// Table orders (o_clerk, o_comment).
proof fn lemma_orders_same(tp: Seq<PartView>, rel: Seq<Row>)
    requires S::orders_ok(tp, rel),
    ensures D::orders_ok(tp, rel),
{
    lemma_layout_same(tp, rel.len() as int);
    lemma_dict_col_same(tp, S::OT_GROUPS as int, S::OT_CLERK_CODES as int, S::OT_CLERK_BASE as int,
        S::OT_CLERK_DICT_OFFS as int, S::OT_CLERK_DICT_BYTES as int, rel, 0);
    lemma_text_col_same(tp, S::OT_COMMENT_OFFS as int, S::OT_COMMENT_BYTES as int, rel, 1);
}

/// The stored relations of both declarations are the same.
pub proof fn lemma_relations_same(db: Database)
    ensures
        crate::stores::factext_trisig::declaration::stored_relations(db)
            == crate::stores::factext_trislice::declaration::stored_relations(db),
{
}

/// The signature prefixes of both copies agree.
proof fn lemma_sig_upto_same(t: Seq<u8>, k: int, w: int)
    ensures ST::sig_upto(t, k, w) == DT::sig_upto(t, k, w),
    decreases k,
{
    if k > 0 {
        lemma_sig_upto_same(t, k - 1, w);
    }
}

/// The signatures of both copies agree.
pub proof fn lemma_sig_same(t: Seq<u8>, w: int)
    ensures ST::sig_of(t, w) == DT::sig_of(t, w),
{
    lemma_sig_upto_same(t, ST::tri_count(t), w);
}

/// For a database bound to the source: the inherited parts are `factext_trisig`'s, described by `base_represents`
/// (the parts of `factext`) and `sigs_ok` (the signatures) of this storage's interface.
pub proof fn lemma_base_copy(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        sv.factext_trisig.len() == D::FACTEXT_TRISIG_PARTS,
        D::base_represents(sv.factext_trisig.subrange(0, D::FACTEXT_PARTS as int),
            crate::stores::factext_trislice::declaration::stored_relations(db)),
        D::sigs_ok(sv.factext_trisig, crate::stores::factext_trislice::declaration::stored_relations(db)[1].len() as int),
{
    lemma_relations_same(db);
    let rels = crate::stores::factext_trisig::declaration::stored_relations(db);
    let parts = sv.factext_trisig;
    assert(S::represents(parts, rels));
    let base = parts.subrange(0, S::FACTEXT_PARTS as int);
    lemma_lineitem_same(base.subrange(S::LINEITEM_FIRST as int, (S::LINEITEM_FIRST + S::LT_PARTS) as int), rels[0]);
    lemma_orders_same(base.subrange(S::ORDERS_FIRST as int, (S::ORDERS_FIRST + S::OT_PARTS) as int), rels[1]);
    let n = rels[1].len() as int;
    lemma_views_same(parts[D::ORDERS_SIG as int]);
    lemma_views_same(parts[D::O_COMMENT_OFFS_PART as int]);
    lemma_views_same(parts[D::O_COMMENT_BYTES_PART as int]);
    assert forall|r: int| 0 <= r < n implies {
        &&& #[trigger] DC::u64s(parts[D::ORDERS_SIG as int])[2 * r] == DT::sig_of(D::comment_at(parts, r), 0)
        &&& DC::u64s(parts[D::ORDERS_SIG as int])[2 * r + 1] == DT::sig_of(D::comment_at(parts, r), 1)
    } by {
        assert(D::comment_at(parts, r) == S::comment_at(parts, r));
        lemma_sig_same(S::comment_at(parts, r), 0);
        lemma_sig_same(S::comment_at(parts, r), 1);
        assert(SC::u64s(parts[S::ORDERS_SIG as int])[2 * r] == ST::sig_of(S::comment_at(parts, r), 0));
        assert(SC::u64s(parts[S::ORDERS_SIG as int])[2 * r + 1] == ST::sig_of(S::comment_at(parts, r), 1));
    }
}

} // verus!
