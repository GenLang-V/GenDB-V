//! Builder of storage `factext`: per table, sorted dictionaries of its low-cardinality text columns,
//! frame-of-reference encoding of its integer, numeric, date and dictionary-index columns over blocks of
//! `BLOCK_ROWS` stored rows (one-row blocks if some block does not fit a code width), and copies of its other text
//! columns, in stored order; then its parts in the interface's order, with the proof of `<table>_ok`.
use vstd::prelude::*;
use std::sync::Arc;
pub mod common;
pub use crate::stores::factext::interface as iface;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{owned_part_view, owned_parts_view, PartView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_source::*;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::spec::value::{Row, Val};
use crate::builder::iface::*;
use crate::builder::iface::common::colfmt::*;
use crate::builder::common::codes::Code;
use crate::builder::common::colsrc::*;
use crate::builder::common::dict::*;
use crate::builder::common::forenc::*;
use crate::builder::common::perm::*;
use crate::builder::common::textcopy::*;
use crate::builder::common::assemble::*;
use crate::builder::common::keyed::*;
use crate::builder::common::cluster::invert_perm;
use crate::builder::iface::common::keyidx::*;

verus! {

/// Block size of a table of `n` rows: `BLOCK_ROWS`, kept below `usize::MAX - n`.
fn block_rows_for(n: usize) -> (b: usize)
    requires n < usize::MAX,
    ensures 1 <= b, n + b <= usize::MAX,
{
    if n <= usize::MAX - BLOCK_ROWS { BLOCK_ROWS } else { usize::MAX - n }
}

/// The identity row map is a bijection.
proof fn lemma_identity_rm(n: int)
    requires n >= 0,
    ensures rm_perm(RowMap::Identity, n),
{
    lemma_identity_perm(n);
    assert(rm_seq(RowMap::Identity, n) =~= identity_map(n));
}

/// Numeric(15, 2) coefficients delivered in the declared domain are below 10^15 in magnitude.
proof fn lemma_num15(rel: Seq<Row>, cs: Seq<crate::spec::types::Column>, k: int, col: Seq<i128>)
    requires
        crate::link::source::rows_in_columns(rel, cs),
        0 <= k < cs.len(),
        cs[k] == (crate::spec::types::Column { ty: crate::spec::types::SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        rel.len() == col.len(),
        forall|i: int| 0 <= i < rel.len() ==> #[trigger] rel[i][k] == (Val::Num { coeff: col[i] as int, scale: 2 }),
    ensures
        forall|i: int| 0 <= i < col.len() ==> -num15_bound() < #[trigger] col[i] < num15_bound(),
{
    assert(crate::spec::numeric::pow10(15) == num15_bound()) by (compute);
    assert forall|i: int| 0 <= i < col.len() implies -num15_bound() < #[trigger] col[i] < num15_bound() by {
        assert(rel[i][k] == (Val::Num { coeff: col[i] as int, scale: 2 }));
        assert(rel[i].len() == cs.len());
        assert(crate::spec::typing::value_in_column(rel[i][k], cs[k]));
    }
}

/// The delivered source is well formed and in the declared domain. Opaque: its text-column quantifiers
/// (`text_wf`) instantiate themselves, so each table's builder sees only the facts `lemma_src_<table>` extracts.
#[verifier::opaque]
pub open spec fn src_ok(v: SourceView) -> bool {
    source_wf(v) && in_domain(tables(v))
}


// ---------------------------------------------------------------------------------------------- lineitem

/// The facts the builder of table lineitem uses about the delivered source.
proof fn lemma_src_lineitem(v: SourceView)
    requires src_ok(v),
    ensures
        source_rows_t0(v) >= 0,
        table_t0(v).len() == source_rows_t0(v),
        tables(v)[0] == table_t0(v),
        v.t0_f0.offsets.len() == source_rows_t0(v) + 1,
        twf(v.t0_f0, source_rows_t0(v)),
{
    reveal(src_ok);
    reveal(twf);
}

/// The parts of table lineitem (canonical row order).
fn build_lineitem(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> lineitem_ok(owned_parts_view(v@), table_t0(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t0(src@);
    proof {
        lemma_src_lineitem(src@);
        vstd::slice::axiom_spec_len(src.t0_f0.offsets);
    }
    let n = src.t0_f0.offsets.len() - 1;
    proof {
        lemma_identity_rm(n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Identity;
    let bsize = bsize0;
    let (o_comment, y_comment) = match copy_text(&src.t0_f0, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let pp_2 = OwnedPart::U64(o_comment);
    let pp_3 = OwnedPart::U8(y_comment);
    let parts = assemble_lineitem(pp_0, pp_1, pp_2, pp_3);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == LT_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 1));
        lemma_text_col(tp, LT_COMMENT_OFFS as int, LT_COMMENT_BYTES as int, rel, 0, o_comment@, y_comment@, src@.t0_f0, rm);
    }
    Ok(parts)
}

// ---------------------------------------------------------------------------------------------- orders

/// The facts the builder of table orders uses about the delivered source.
proof fn lemma_src_orders(v: SourceView)
    requires src_ok(v),
    ensures
        source_rows_t1(v) >= 0,
        table_t1(v).len() == source_rows_t1(v),
        tables(v)[1] == table_t1(v),
        v.t1_f0.offsets.len() == source_rows_t1(v) + 1,
        twf(v.t1_f0, source_rows_t1(v)),
        twf(v.t1_f1, source_rows_t1(v)),
{
    reveal(src_ok);
    reveal(twf);
}

/// The FOR columns of table orders, encoded over blocks of `bsize` stored rows (`None`: some block does not fit).
fn encode_orders(src_clerk: &ValSrc, rm: &RowMap, n: usize, bsize: usize, zb_clerk: bool, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<(ForCol<u32>,)>, QueryError>)
    requires
        src_wf(*src_clerk, n as int),
        zb_clerk ==> fits_zero_base::<u32>(*src_clerk, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> for_col_ok(t.0, *src_clerk, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
        r matches Err(e) ==> e is WorkerFailed,
{
    let c_clerk = match encode_column::<u32>(src_clerk, rm, n, bsize, zb_clerk, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(Some((c_clerk,)))
}

/// The parts of table orders (canonical row order).
fn build_orders(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> orders_ok(owned_parts_view(v@), table_t1(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t1(src@);
    proof {
        lemma_src_orders(src@);
        vstd::slice::axiom_spec_len(src.t1_f0.offsets);
    }
    let n = src.t1_f0.offsets.len() - 1;
    proof {
        lemma_identity_rm(n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Identity;
    let d_clerk = Arc::new(build_dict(&src.t1_f0, n));
    let zb_clerk = d_clerk.offs.len() - 1 <= 4294967295;
    let src_clerk = ValSrc::Dict(TextCol { offsets: src.t1_f0.offsets, bytes: src.t1_f0.bytes }, d_clerk.clone());
    proof {
        if zb_clerk {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_clerk, i) <= u32::cap() by {
                lemma_dict_src_bound(src_clerk, n as int, i);
            }
        }
    }
    let (bsize, (c_clerk,)) = match encode_orders(&src_clerk, &rm, n, bsize0, zb_clerk, workers, dispatch) {
        Ok(Some(cols)) => (bsize0, cols),
        Ok(None) => match encode_orders(&src_clerk, &rm, n, 1, zb_clerk, workers, dispatch) {
            Ok(Some(cols)) => (1, cols),
            Ok(None) => { proof { assert(false); } return Err(QueryError::Malformed); }
            Err(e) => return Err(e),
        },
        Err(e) => return Err(e),
    };
    let (o_comment, y_comment) = match copy_text(&src.t1_f1, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_col_ranges(c_clerk, src_clerk, rm, n as int, bsize as int);
    }
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let b_clerk = bases_u64(&c_clerk.bases);
    let ghost cc_clerk = c_clerk.codes@;
    let pp_2 = u32::into_part(c_clerk.codes);
    let pp_3 = OwnedPart::U64(b_clerk);
    let pp_4 = OwnedPart::U64(copy_u64s(&d_clerk.offs));
    let pp_5 = OwnedPart::U8(copy_u8s(&d_clerk.bytes));
    let pp_6 = OwnedPart::U64(o_comment);
    let pp_7 = OwnedPart::U8(y_comment);
    let parts = assemble_orders(pp_0, pp_1, pp_2, pp_3, pp_4, pp_5, pp_6, pp_7);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == OT_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 2));
        assert(tp[OT_CLERK_CODES as int] == u32::part_of(cc_clerk));
        lemma_for_decode(tp, OT_GROUPS as int, OT_CLERK_CODES as int, OT_CLERK_BASE as int, c_clerk, src_clerk, rm, n as int, bsize as int);
        lemma_dict_col(tp, OT_GROUPS as int, OT_CLERK_CODES as int, OT_CLERK_BASE as int, OT_CLERK_DICT_OFFS as int, OT_CLERK_DICT_BYTES as int, rel, 0, src@.t1_f0, &d_clerk, rm, n as int);
        lemma_text_col(tp, OT_COMMENT_OFFS as int, OT_COMMENT_BYTES as int, rel, 1, o_comment@, y_comment@, src@.t1_f1, rm);
    }
    Ok(parts)
}

/// Parts 0 .. 3 of table lineitem, in order.
fn assemble_lineitem_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 4,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(4);
    v.push(p0);
    v.push(p1);
    v.push(p2);
    v.push(p3);
    v
}

/// The 4 parts of table lineitem, in order (each named by index in the postcondition).
fn assemble_lineitem(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 4,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
{
    let mut c0 = assemble_lineitem_0(p0, p1, p2, p3);
    let mut v: Vec<OwnedPart> = Vec::new();
    let ghost before_0 = v@;
    v.append(&mut c0);
    assert(v@.len() == 4);
    proof {
        assert(v@[0] == p0);
        assert(v@[1] == p1);
        assert(v@[2] == p2);
        assert(v@[3] == p3);
    }
    v
}

/// Parts 0 .. 7 of table orders, in order.
fn assemble_orders_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 8,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
        v@[4] == p4,
        v@[5] == p5,
        v@[6] == p6,
        v@[7] == p7,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(8);
    v.push(p0);
    v.push(p1);
    v.push(p2);
    v.push(p3);
    v.push(p4);
    v.push(p5);
    v.push(p6);
    v.push(p7);
    v
}

/// The 8 parts of table orders, in order (each named by index in the postcondition).
fn assemble_orders(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 8,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
        v@[4] == p4,
        v@[5] == p5,
        v@[6] == p6,
        v@[7] == p7,
{
    let mut c0 = assemble_orders_0(p0, p1, p2, p3, p4, p5, p6, p7);
    let mut v: Vec<OwnedPart> = Vec::new();
    let ghost before_0 = v@;
    v.append(&mut c0);
    assert(v@.len() == 8);
    proof {
        assert(v@[0] == p0);
        assert(v@[1] == p1);
        assert(v@[2] == p2);
        assert(v@[3] == p3);
        assert(v@[4] == p4);
        assert(v@[5] == p5);
        assert(v@[6] == p6);
        assert(v@[7] == p7);
    }
    v
}

/// Builds every table's parts and concatenates them in the interface's order.
pub fn build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        source_wf(src@),
        in_domain(tables(src@)),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> crate::stores::factext::interface::represents(owned_parts_view(p@), tables(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    proof {
        reveal(src_ok);
    }
    let mut parts: Vec<OwnedPart> = Vec::new();
    let mut p_lineitem = match build_lineitem(src, workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_lineitem = p_lineitem@;
    assert(owned_parts_view(v_lineitem).len() == LT_PARTS);
    parts.append(&mut p_lineitem);
    let mut p_orders = match build_orders(src, workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_orders = p_orders@;
    assert(owned_parts_view(v_orders).len() == OT_PARTS);
    parts.append(&mut p_orders);
    proof {
        let pv = owned_parts_view(parts@);
        let ts = tables(src@);
        assert(pv.subrange(LINEITEM_FIRST as int, LINEITEM_FIRST as int + LT_PARTS as int) =~= owned_parts_view(v_lineitem));
        assert(ts[0] == table_t0(src@));
        assert(pv.subrange(ORDERS_FIRST as int, ORDERS_FIRST as int + OT_PARTS as int) =~= owned_parts_view(v_orders));
        assert(ts[1] == table_t1(src@));
    }
    Ok(parts)
}

} // verus!
