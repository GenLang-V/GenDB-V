//! Builder of storage `suppliers`: per table, sorted dictionaries of its low-cardinality text columns,
//! frame-of-reference encoding of its integer, numeric, date and dictionary-index columns over blocks of
//! `BLOCK_ROWS` stored rows (one-row blocks if some block does not fit a code width), and copies of its other text
//! columns, in stored order; then its parts in the interface's order, with the proof of `<table>_ok`.
use vstd::prelude::*;
use std::sync::Arc;
pub mod common;
pub use crate::stores::suppliers::interface as iface;
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


// ---------------------------------------------------------------------------------------------- partsupp

/// The facts the builder of table partsupp uses about the delivered source.
proof fn lemma_src_partsupp(v: SourceView)
    requires src_ok(v),
    ensures
        source_rows_t0(v) >= 0,
        table_t0(v).len() == source_rows_t0(v),
        tables(v)[0] == table_t0(v),
        v.t0_f4.offsets.len() == source_rows_t0(v) + 1,
        v.t0_f0.len() == source_rows_t0(v),
        v.t0_f1.len() == source_rows_t0(v),
        v.t0_f2.len() == source_rows_t0(v),
        v.t0_f3.len() == source_rows_t0(v),
        twf(v.t0_f4, source_rows_t0(v)),
        forall|i: int| 0 <= i < v.t0_f3.len() ==> -num15_bound() < #[trigger] v.t0_f3[i] < num15_bound(),
{
    reveal(src_ok);
    reveal(twf);
    lemma_num15(table_t0(v), source_columns_t0(), 3, v.t0_f3);
}

/// The FOR columns of table partsupp, encoded over blocks of `bsize` stored rows (`None`: some block does not fit).
fn encode_partsupp(src_partkey: &ValSrc, src_suppkey: &ValSrc, src_availqty: &ValSrc, src_supplycost: &ValSrc, rm: &RowMap, n: usize, bsize: usize, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<(ForCol<u32>, ForCol<u32>, ForCol<u16>, ForCol<u32>,)>, QueryError>)
    requires
        src_wf(*src_partkey, n as int),
        src_wf(*src_suppkey, n as int),
        src_wf(*src_availqty, n as int),
        src_wf(*src_supplycost, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> for_col_ok(t.0, *src_partkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.1, *src_suppkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.2, *src_availqty, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.3, *src_supplycost, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
        r matches Err(e) ==> e is WorkerFailed,
{
    let c_partkey = match encode_column::<u32>(src_partkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_suppkey = match encode_column::<u32>(src_suppkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_availqty = match encode_column::<u16>(src_availqty, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_supplycost = match encode_column::<u32>(src_supplycost, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(Some((c_partkey, c_suppkey, c_availqty, c_supplycost,)))
}

/// The parts of table partsupp (canonical row order).
fn build_partsupp(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> partsupp_ok(owned_parts_view(v@), table_t0(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t0(src@);
    proof {
        lemma_src_partsupp(src@);
        vstd::slice::axiom_spec_len(src.t0_f4.offsets);
    }
    let n = src.t0_f0.len();
    proof {
        lemma_identity_rm(n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Identity;
    let src_partkey = ValSrc::Int(src.t0_f0);
    let src_suppkey = ValSrc::Int(src.t0_f1);
    let src_availqty = ValSrc::Int(src.t0_f2);
    let src_supplycost = ValSrc::Num(src.t0_f3);
    let (bsize, (c_partkey, c_suppkey, c_availqty, c_supplycost,)) = match encode_partsupp(&src_partkey, &src_suppkey, &src_availqty, &src_supplycost, &rm, n, bsize0, workers, dispatch) {
        Ok(Some(cols)) => (bsize0, cols),
        Ok(None) => match encode_partsupp(&src_partkey, &src_suppkey, &src_availqty, &src_supplycost, &rm, n, 1, workers, dispatch) {
            Ok(Some(cols)) => (1, cols),
            Ok(None) => { proof { assert(false); } return Err(QueryError::Malformed); }
            Err(e) => return Err(e),
        },
        Err(e) => return Err(e),
    };
    let (o_comment, y_comment) = match copy_text(&src.t0_f4, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_col_ranges(c_partkey, src_partkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_suppkey, src_suppkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_availqty, src_availqty, rm, n as int, bsize as int);
        lemma_col_ranges(c_supplycost, src_supplycost, rm, n as int, bsize as int);
    }
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let b_partkey = bases_i64(&c_partkey.bases);
    let ghost bb_partkey = b_partkey@;
    let ghost cc_partkey = c_partkey.codes@;
    let pp_2 = u32::into_part(c_partkey.codes);
    let pp_3 = OwnedPart::I64(b_partkey);
    let b_suppkey = bases_i64(&c_suppkey.bases);
    let ghost bb_suppkey = b_suppkey@;
    let ghost cc_suppkey = c_suppkey.codes@;
    let pp_4 = u32::into_part(c_suppkey.codes);
    let pp_5 = OwnedPart::I64(b_suppkey);
    let b_availqty = bases_i64(&c_availqty.bases);
    let ghost bb_availqty = b_availqty@;
    let ghost cc_availqty = c_availqty.codes@;
    let pp_6 = u16::into_part(c_availqty.codes);
    let pp_7 = OwnedPart::I64(b_availqty);
    let b_supplycost = bases_i64(&c_supplycost.bases);
    let ghost bb_supplycost = b_supplycost@;
    let ghost cc_supplycost = c_supplycost.codes@;
    let pp_8 = u32::into_part(c_supplycost.codes);
    let pp_9 = OwnedPart::I64(b_supplycost);
    let pp_10 = OwnedPart::U64(o_comment);
    let pp_11 = OwnedPart::U8(y_comment);
    let ghost kcs = cc_partkey;
    let ghost kbs = bb_partkey;
    proof {
        lemma_fkey_col(c_partkey, src_partkey, rm, kbs, n as int, bsize as int);
    }
    let key_kind = build_keyidx_sorted(src.t0_f0, n, bsize, Ghost(kcs), Ghost(kbs));
    let pp_12 = OwnedPart::U64(vec![key_kind]);
    let parts = assemble_partsupp(pp_0, pp_1, pp_2, pp_3, pp_4, pp_5, pp_6, pp_7, pp_8, pp_9, pp_10, pp_11, pp_12);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == PS_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 5));
        assert(tp[PS_PARTKEY_CODES as int] == u32::part_of(cc_partkey));
        lemma_for_decode(tp, PS_GROUPS as int, PS_PARTKEY_CODES as int, PS_PARTKEY_BASE as int, c_partkey, src_partkey, rm, n as int, bsize as int);
        lemma_int_col(tp, PS_GROUPS as int, PS_PARTKEY_CODES as int, PS_PARTKEY_BASE as int, rel, 0, src_partkey, rm);
        assert(tp[PS_SUPPKEY_CODES as int] == u32::part_of(cc_suppkey));
        lemma_for_decode(tp, PS_GROUPS as int, PS_SUPPKEY_CODES as int, PS_SUPPKEY_BASE as int, c_suppkey, src_suppkey, rm, n as int, bsize as int);
        lemma_int_col(tp, PS_GROUPS as int, PS_SUPPKEY_CODES as int, PS_SUPPKEY_BASE as int, rel, 1, src_suppkey, rm);
        assert(tp[PS_AVAILQTY_CODES as int] == u16::part_of(cc_availqty));
        lemma_for_decode(tp, PS_GROUPS as int, PS_AVAILQTY_CODES as int, PS_AVAILQTY_BASE as int, c_availqty, src_availqty, rm, n as int, bsize as int);
        lemma_int_col(tp, PS_GROUPS as int, PS_AVAILQTY_CODES as int, PS_AVAILQTY_BASE as int, rel, 2, src_availqty, rm);
        assert(tp[PS_SUPPLYCOST_CODES as int] == u32::part_of(cc_supplycost));
        lemma_for_decode(tp, PS_GROUPS as int, PS_SUPPLYCOST_CODES as int, PS_SUPPLYCOST_BASE as int, c_supplycost, src_supplycost, rm, n as int, bsize as int);
        lemma_num_col(tp, PS_GROUPS as int, PS_SUPPLYCOST_CODES as int, PS_SUPPLYCOST_BASE as int, rel, 3, 2, src_supplycost, rm);
        lemma_text_col(tp, PS_COMMENT_OFFS as int, PS_COMMENT_BYTES as int, rel, 4, o_comment@, y_comment@, src@.t0_f4, rm);
        assert(u64s(tp[PS_KEYIDX_KIND as int]) =~= seq![key_kind]);
        assert(u32s(tp[PS_PARTKEY_CODES as int]) == kcs);
        assert(i64s(tp[PS_PARTKEY_BASE as int]) == kbs);
    }
    Ok(parts)
}

// ---------------------------------------------------------------------------------------------- supplier

/// The facts the builder of table supplier uses about the delivered source.
proof fn lemma_src_supplier(v: SourceView)
    requires src_ok(v),
    ensures
        source_rows_t1(v) >= 0,
        table_t1(v).len() == source_rows_t1(v),
        tables(v)[1] == table_t1(v),
        v.t1_f1.offsets.len() == source_rows_t1(v) + 1,
        v.t1_f0.len() == source_rows_t1(v),
        twf(v.t1_f1, source_rows_t1(v)),
        twf(v.t1_f2, source_rows_t1(v)),
        v.t1_f3.len() == source_rows_t1(v),
        twf(v.t1_f4, source_rows_t1(v)),
        v.t1_f5.len() == source_rows_t1(v),
        twf(v.t1_f6, source_rows_t1(v)),
        forall|i: int| 0 <= i < v.t1_f5.len() ==> -num15_bound() < #[trigger] v.t1_f5[i] < num15_bound(),
{
    reveal(src_ok);
    reveal(twf);
    lemma_num15(table_t1(v), source_columns_t1(), 5, v.t1_f5);
}

/// The FOR columns of table supplier, encoded over blocks of `bsize` stored rows (`None`: some block does not fit).
fn encode_supplier(src_suppkey: &ValSrc, src_nationkey: &ValSrc, src_acctbal: &ValSrc, rm: &RowMap, n: usize, bsize: usize, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<(ForCol<u32>, ForCol<u8>, ForCol<u32>,)>, QueryError>)
    requires
        src_wf(*src_suppkey, n as int),
        src_wf(*src_nationkey, n as int),
        src_wf(*src_acctbal, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> for_col_ok(t.0, *src_suppkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.1, *src_nationkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.2, *src_acctbal, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
        r matches Err(e) ==> e is WorkerFailed,
{
    let c_suppkey = match encode_column::<u32>(src_suppkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_nationkey = match encode_column::<u8>(src_nationkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_acctbal = match encode_column::<u32>(src_acctbal, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(Some((c_suppkey, c_nationkey, c_acctbal,)))
}

/// The parts of table supplier (canonical row order).
fn build_supplier(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> supplier_ok(owned_parts_view(v@), table_t1(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t1(src@);
    proof {
        lemma_src_supplier(src@);
        vstd::slice::axiom_spec_len(src.t1_f1.offsets);
    }
    let n = src.t1_f0.len();
    proof {
        lemma_identity_rm(n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Identity;
    let src_suppkey = ValSrc::Int(src.t1_f0);
    let src_nationkey = ValSrc::Int(src.t1_f3);
    let src_acctbal = ValSrc::Num(src.t1_f5);
    let (bsize, (c_suppkey, c_nationkey, c_acctbal,)) = match encode_supplier(&src_suppkey, &src_nationkey, &src_acctbal, &rm, n, bsize0, workers, dispatch) {
        Ok(Some(cols)) => (bsize0, cols),
        Ok(None) => match encode_supplier(&src_suppkey, &src_nationkey, &src_acctbal, &rm, n, 1, workers, dispatch) {
            Ok(Some(cols)) => (1, cols),
            Ok(None) => { proof { assert(false); } return Err(QueryError::Malformed); }
            Err(e) => return Err(e),
        },
        Err(e) => return Err(e),
    };
    let (o_name, y_name) = match copy_text(&src.t1_f1, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let (o_address, y_address) = match copy_text(&src.t1_f2, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let (o_phone, y_phone) = match copy_text(&src.t1_f4, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let (o_comment, y_comment) = match copy_text(&src.t1_f6, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_col_ranges(c_suppkey, src_suppkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_nationkey, src_nationkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_acctbal, src_acctbal, rm, n as int, bsize as int);
    }
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let b_suppkey = bases_i64(&c_suppkey.bases);
    let ghost bb_suppkey = b_suppkey@;
    let ghost cc_suppkey = c_suppkey.codes@;
    let pp_2 = u32::into_part(c_suppkey.codes);
    let pp_3 = OwnedPart::I64(b_suppkey);
    let pp_4 = OwnedPart::U64(o_name);
    let pp_5 = OwnedPart::U8(y_name);
    let pp_6 = OwnedPart::U64(o_address);
    let pp_7 = OwnedPart::U8(y_address);
    let b_nationkey = bases_i64(&c_nationkey.bases);
    let ghost bb_nationkey = b_nationkey@;
    let ghost cc_nationkey = c_nationkey.codes@;
    let pp_8 = u8::into_part(c_nationkey.codes);
    let pp_9 = OwnedPart::I64(b_nationkey);
    let pp_10 = OwnedPart::U64(o_phone);
    let pp_11 = OwnedPart::U8(y_phone);
    let b_acctbal = bases_i64(&c_acctbal.bases);
    let ghost bb_acctbal = b_acctbal@;
    let ghost cc_acctbal = c_acctbal.codes@;
    let pp_12 = u32::into_part(c_acctbal.codes);
    let pp_13 = OwnedPart::I64(b_acctbal);
    let pp_14 = OwnedPart::U64(o_comment);
    let pp_15 = OwnedPart::U8(y_comment);
    let ghost kcs = cc_suppkey;
    let ghost kbs = bb_suppkey;
    proof {
        lemma_fkey_col(c_suppkey, src_suppkey, rm, kbs, n as int, bsize as int);
    }
    let key_kind = build_keyidx_sorted(src.t1_f0, n, bsize, Ghost(kcs), Ghost(kbs));
    let pp_16 = OwnedPart::U64(vec![key_kind]);
    let parts = assemble_supplier(pp_0, pp_1, pp_2, pp_3, pp_4, pp_5, pp_6, pp_7, pp_8, pp_9, pp_10, pp_11, pp_12, pp_13, pp_14, pp_15, pp_16);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == SU_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 7));
        assert(tp[SU_SUPPKEY_CODES as int] == u32::part_of(cc_suppkey));
        lemma_for_decode(tp, SU_GROUPS as int, SU_SUPPKEY_CODES as int, SU_SUPPKEY_BASE as int, c_suppkey, src_suppkey, rm, n as int, bsize as int);
        lemma_int_col(tp, SU_GROUPS as int, SU_SUPPKEY_CODES as int, SU_SUPPKEY_BASE as int, rel, 0, src_suppkey, rm);
        lemma_text_col(tp, SU_NAME_OFFS as int, SU_NAME_BYTES as int, rel, 1, o_name@, y_name@, src@.t1_f1, rm);
        lemma_text_col(tp, SU_ADDRESS_OFFS as int, SU_ADDRESS_BYTES as int, rel, 2, o_address@, y_address@, src@.t1_f2, rm);
        assert(tp[SU_NATIONKEY_CODES as int] == u8::part_of(cc_nationkey));
        lemma_for_decode(tp, SU_GROUPS as int, SU_NATIONKEY_CODES as int, SU_NATIONKEY_BASE as int, c_nationkey, src_nationkey, rm, n as int, bsize as int);
        lemma_int_col(tp, SU_GROUPS as int, SU_NATIONKEY_CODES as int, SU_NATIONKEY_BASE as int, rel, 3, src_nationkey, rm);
        lemma_text_col(tp, SU_PHONE_OFFS as int, SU_PHONE_BYTES as int, rel, 4, o_phone@, y_phone@, src@.t1_f4, rm);
        assert(tp[SU_ACCTBAL_CODES as int] == u32::part_of(cc_acctbal));
        lemma_for_decode(tp, SU_GROUPS as int, SU_ACCTBAL_CODES as int, SU_ACCTBAL_BASE as int, c_acctbal, src_acctbal, rm, n as int, bsize as int);
        lemma_num_col(tp, SU_GROUPS as int, SU_ACCTBAL_CODES as int, SU_ACCTBAL_BASE as int, rel, 5, 2, src_acctbal, rm);
        lemma_text_col(tp, SU_COMMENT_OFFS as int, SU_COMMENT_BYTES as int, rel, 6, o_comment@, y_comment@, src@.t1_f6, rm);
        assert(u64s(tp[SU_KEYIDX_KIND as int]) =~= seq![key_kind]);
        assert(u32s(tp[SU_SUPPKEY_CODES as int]) == kcs);
        assert(i64s(tp[SU_SUPPKEY_BASE as int]) == kbs);
    }
    Ok(parts)
}

// ---------------------------------------------------------------------------------------------- nation

/// The facts the builder of table nation uses about the delivered source.
proof fn lemma_src_nation(v: SourceView)
    requires src_ok(v),
    ensures
        source_rows_t2(v) >= 0,
        table_t2(v).len() == source_rows_t2(v),
        tables(v)[2] == table_t2(v),
        v.t2_f1.offsets.len() == source_rows_t2(v) + 1,
        v.t2_f0.len() == source_rows_t2(v),
        twf(v.t2_f1, source_rows_t2(v)),
        v.t2_f2.len() == source_rows_t2(v),
        twf(v.t2_f3, source_rows_t2(v)),
{
    reveal(src_ok);
    reveal(twf);
}

/// The FOR columns of table nation, encoded over blocks of `bsize` stored rows (`None`: some block does not fit).
fn encode_nation(src_nationkey: &ValSrc, src_regionkey: &ValSrc, rm: &RowMap, n: usize, bsize: usize, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<(ForCol<u8>, ForCol<u8>,)>, QueryError>)
    requires
        src_wf(*src_nationkey, n as int),
        src_wf(*src_regionkey, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> for_col_ok(t.0, *src_nationkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.1, *src_regionkey, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
        r matches Err(e) ==> e is WorkerFailed,
{
    let c_nationkey = match encode_column::<u8>(src_nationkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_regionkey = match encode_column::<u8>(src_regionkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(Some((c_nationkey, c_regionkey,)))
}

/// The parts of table nation (canonical row order).
fn build_nation(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> nation_ok(owned_parts_view(v@), table_t2(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t2(src@);
    proof {
        lemma_src_nation(src@);
        vstd::slice::axiom_spec_len(src.t2_f1.offsets);
    }
    let n = src.t2_f0.len();
    proof {
        lemma_identity_rm(n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Identity;
    let src_nationkey = ValSrc::Int(src.t2_f0);
    let src_regionkey = ValSrc::Int(src.t2_f2);
    let (bsize, (c_nationkey, c_regionkey,)) = match encode_nation(&src_nationkey, &src_regionkey, &rm, n, bsize0, workers, dispatch) {
        Ok(Some(cols)) => (bsize0, cols),
        Ok(None) => match encode_nation(&src_nationkey, &src_regionkey, &rm, n, 1, workers, dispatch) {
            Ok(Some(cols)) => (1, cols),
            Ok(None) => { proof { assert(false); } return Err(QueryError::Malformed); }
            Err(e) => return Err(e),
        },
        Err(e) => return Err(e),
    };
    let (o_name, y_name) = match copy_text(&src.t2_f1, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let (o_comment, y_comment) = match copy_text(&src.t2_f3, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_col_ranges(c_nationkey, src_nationkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_regionkey, src_regionkey, rm, n as int, bsize as int);
    }
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let b_nationkey = bases_i64(&c_nationkey.bases);
    let ghost bb_nationkey = b_nationkey@;
    let ghost cc_nationkey = c_nationkey.codes@;
    let pp_2 = u8::into_part(c_nationkey.codes);
    let pp_3 = OwnedPart::I64(b_nationkey);
    let pp_4 = OwnedPart::U64(o_name);
    let pp_5 = OwnedPart::U8(y_name);
    let b_regionkey = bases_i64(&c_regionkey.bases);
    let ghost bb_regionkey = b_regionkey@;
    let ghost cc_regionkey = c_regionkey.codes@;
    let pp_6 = u8::into_part(c_regionkey.codes);
    let pp_7 = OwnedPart::I64(b_regionkey);
    let pp_8 = OwnedPart::U64(o_comment);
    let pp_9 = OwnedPart::U8(y_comment);
    let parts = assemble_nation(pp_0, pp_1, pp_2, pp_3, pp_4, pp_5, pp_6, pp_7, pp_8, pp_9);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == NA_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 4));
        assert(tp[NA_NATIONKEY_CODES as int] == u8::part_of(cc_nationkey));
        lemma_for_decode(tp, NA_GROUPS as int, NA_NATIONKEY_CODES as int, NA_NATIONKEY_BASE as int, c_nationkey, src_nationkey, rm, n as int, bsize as int);
        lemma_int_col(tp, NA_GROUPS as int, NA_NATIONKEY_CODES as int, NA_NATIONKEY_BASE as int, rel, 0, src_nationkey, rm);
        lemma_text_col(tp, NA_NAME_OFFS as int, NA_NAME_BYTES as int, rel, 1, o_name@, y_name@, src@.t2_f1, rm);
        assert(tp[NA_REGIONKEY_CODES as int] == u8::part_of(cc_regionkey));
        lemma_for_decode(tp, NA_GROUPS as int, NA_REGIONKEY_CODES as int, NA_REGIONKEY_BASE as int, c_regionkey, src_regionkey, rm, n as int, bsize as int);
        lemma_int_col(tp, NA_GROUPS as int, NA_REGIONKEY_CODES as int, NA_REGIONKEY_BASE as int, rel, 2, src_regionkey, rm);
        lemma_text_col(tp, NA_COMMENT_OFFS as int, NA_COMMENT_BYTES as int, rel, 3, o_comment@, y_comment@, src@.t2_f3, rm);
    }
    Ok(parts)
}

// ---------------------------------------------------------------------------------------------- region

/// The facts the builder of table region uses about the delivered source.
proof fn lemma_src_region(v: SourceView)
    requires src_ok(v),
    ensures
        source_rows_t3(v) >= 0,
        table_t3(v).len() == source_rows_t3(v),
        tables(v)[3] == table_t3(v),
        v.t3_f1.offsets.len() == source_rows_t3(v) + 1,
        v.t3_f0.len() == source_rows_t3(v),
        twf(v.t3_f1, source_rows_t3(v)),
        twf(v.t3_f2, source_rows_t3(v)),
{
    reveal(src_ok);
    reveal(twf);
}

/// The FOR columns of table region, encoded over blocks of `bsize` stored rows (`None`: some block does not fit).
fn encode_region(src_regionkey: &ValSrc, rm: &RowMap, n: usize, bsize: usize, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<(ForCol<u8>,)>, QueryError>)
    requires
        src_wf(*src_regionkey, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> for_col_ok(t.0, *src_regionkey, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
        r matches Err(e) ==> e is WorkerFailed,
{
    let c_regionkey = match encode_column::<u8>(src_regionkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(Some((c_regionkey,)))
}

/// The parts of table region (canonical row order).
fn build_region(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> region_ok(owned_parts_view(v@), table_t3(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t3(src@);
    proof {
        lemma_src_region(src@);
        vstd::slice::axiom_spec_len(src.t3_f1.offsets);
    }
    let n = src.t3_f0.len();
    proof {
        lemma_identity_rm(n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Identity;
    let src_regionkey = ValSrc::Int(src.t3_f0);
    let (bsize, (c_regionkey,)) = match encode_region(&src_regionkey, &rm, n, bsize0, workers, dispatch) {
        Ok(Some(cols)) => (bsize0, cols),
        Ok(None) => match encode_region(&src_regionkey, &rm, n, 1, workers, dispatch) {
            Ok(Some(cols)) => (1, cols),
            Ok(None) => { proof { assert(false); } return Err(QueryError::Malformed); }
            Err(e) => return Err(e),
        },
        Err(e) => return Err(e),
    };
    let (o_name, y_name) = match copy_text(&src.t3_f1, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let (o_comment, y_comment) = match copy_text(&src.t3_f2, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_col_ranges(c_regionkey, src_regionkey, rm, n as int, bsize as int);
    }
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let b_regionkey = bases_i64(&c_regionkey.bases);
    let ghost bb_regionkey = b_regionkey@;
    let ghost cc_regionkey = c_regionkey.codes@;
    let pp_2 = u8::into_part(c_regionkey.codes);
    let pp_3 = OwnedPart::I64(b_regionkey);
    let pp_4 = OwnedPart::U64(o_name);
    let pp_5 = OwnedPart::U8(y_name);
    let pp_6 = OwnedPart::U64(o_comment);
    let pp_7 = OwnedPart::U8(y_comment);
    let parts = assemble_region(pp_0, pp_1, pp_2, pp_3, pp_4, pp_5, pp_6, pp_7);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == RE_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 3));
        assert(tp[RE_REGIONKEY_CODES as int] == u8::part_of(cc_regionkey));
        lemma_for_decode(tp, RE_GROUPS as int, RE_REGIONKEY_CODES as int, RE_REGIONKEY_BASE as int, c_regionkey, src_regionkey, rm, n as int, bsize as int);
        lemma_int_col(tp, RE_GROUPS as int, RE_REGIONKEY_CODES as int, RE_REGIONKEY_BASE as int, rel, 0, src_regionkey, rm);
        lemma_text_col(tp, RE_NAME_OFFS as int, RE_NAME_BYTES as int, rel, 1, o_name@, y_name@, src@.t3_f1, rm);
        lemma_text_col(tp, RE_COMMENT_OFFS as int, RE_COMMENT_BYTES as int, rel, 2, o_comment@, y_comment@, src@.t3_f2, rm);
    }
    Ok(parts)
}

/// Parts 0 .. 11 of table partsupp, in order.
fn assemble_partsupp_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 12,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
        v@[4] == p4,
        v@[5] == p5,
        v@[6] == p6,
        v@[7] == p7,
        v@[8] == p8,
        v@[9] == p9,
        v@[10] == p10,
        v@[11] == p11,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(12);
    v.push(p0);
    v.push(p1);
    v.push(p2);
    v.push(p3);
    v.push(p4);
    v.push(p5);
    v.push(p6);
    v.push(p7);
    v.push(p8);
    v.push(p9);
    v.push(p10);
    v.push(p11);
    v
}

/// Parts 12 .. 12 of table partsupp, in order.
fn assemble_partsupp_1(p12: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 1,
        v@[0] == p12,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(1);
    v.push(p12);
    v
}

/// The 13 parts of table partsupp, in order (each named by index in the postcondition).
fn assemble_partsupp(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart, p12: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 13,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
        v@[4] == p4,
        v@[5] == p5,
        v@[6] == p6,
        v@[7] == p7,
        v@[8] == p8,
        v@[9] == p9,
        v@[10] == p10,
        v@[11] == p11,
        v@[12] == p12,
{
    let mut c0 = assemble_partsupp_0(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11);
    let mut c1 = assemble_partsupp_1(p12);
    let mut v: Vec<OwnedPart> = Vec::new();
    let ghost before_0 = v@;
    v.append(&mut c0);
    assert(v@.len() == 12);
    proof {
        assert(v@[0] == p0);
        assert(v@[1] == p1);
        assert(v@[2] == p2);
        assert(v@[3] == p3);
        assert(v@[4] == p4);
        assert(v@[5] == p5);
        assert(v@[6] == p6);
        assert(v@[7] == p7);
        assert(v@[8] == p8);
        assert(v@[9] == p9);
        assert(v@[10] == p10);
        assert(v@[11] == p11);
    }
    let ghost before_1 = v@;
    v.append(&mut c1);
    assert(v@.len() == 13);
    proof {
        assert(v@[12] == p12);
        assert(v@[0] == before_1[0]);
        assert(v@[1] == before_1[1]);
        assert(v@[2] == before_1[2]);
        assert(v@[3] == before_1[3]);
        assert(v@[4] == before_1[4]);
        assert(v@[5] == before_1[5]);
        assert(v@[6] == before_1[6]);
        assert(v@[7] == before_1[7]);
        assert(v@[8] == before_1[8]);
        assert(v@[9] == before_1[9]);
        assert(v@[10] == before_1[10]);
        assert(v@[11] == before_1[11]);
    }
    v
}

/// Parts 0 .. 11 of table supplier, in order.
fn assemble_supplier_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 12,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
        v@[4] == p4,
        v@[5] == p5,
        v@[6] == p6,
        v@[7] == p7,
        v@[8] == p8,
        v@[9] == p9,
        v@[10] == p10,
        v@[11] == p11,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(12);
    v.push(p0);
    v.push(p1);
    v.push(p2);
    v.push(p3);
    v.push(p4);
    v.push(p5);
    v.push(p6);
    v.push(p7);
    v.push(p8);
    v.push(p9);
    v.push(p10);
    v.push(p11);
    v
}

/// Parts 12 .. 16 of table supplier, in order.
fn assemble_supplier_1(p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 5,
        v@[0] == p12,
        v@[1] == p13,
        v@[2] == p14,
        v@[3] == p15,
        v@[4] == p16,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(5);
    v.push(p12);
    v.push(p13);
    v.push(p14);
    v.push(p15);
    v.push(p16);
    v
}

/// The 17 parts of table supplier, in order (each named by index in the postcondition).
fn assemble_supplier(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart, p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 17,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
        v@[4] == p4,
        v@[5] == p5,
        v@[6] == p6,
        v@[7] == p7,
        v@[8] == p8,
        v@[9] == p9,
        v@[10] == p10,
        v@[11] == p11,
        v@[12] == p12,
        v@[13] == p13,
        v@[14] == p14,
        v@[15] == p15,
        v@[16] == p16,
{
    let mut c0 = assemble_supplier_0(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11);
    let mut c1 = assemble_supplier_1(p12, p13, p14, p15, p16);
    let mut v: Vec<OwnedPart> = Vec::new();
    let ghost before_0 = v@;
    v.append(&mut c0);
    assert(v@.len() == 12);
    proof {
        assert(v@[0] == p0);
        assert(v@[1] == p1);
        assert(v@[2] == p2);
        assert(v@[3] == p3);
        assert(v@[4] == p4);
        assert(v@[5] == p5);
        assert(v@[6] == p6);
        assert(v@[7] == p7);
        assert(v@[8] == p8);
        assert(v@[9] == p9);
        assert(v@[10] == p10);
        assert(v@[11] == p11);
    }
    let ghost before_1 = v@;
    v.append(&mut c1);
    assert(v@.len() == 17);
    proof {
        assert(v@[12] == p12);
        assert(v@[13] == p13);
        assert(v@[14] == p14);
        assert(v@[15] == p15);
        assert(v@[16] == p16);
        assert(v@[0] == before_1[0]);
        assert(v@[1] == before_1[1]);
        assert(v@[2] == before_1[2]);
        assert(v@[3] == before_1[3]);
        assert(v@[4] == before_1[4]);
        assert(v@[5] == before_1[5]);
        assert(v@[6] == before_1[6]);
        assert(v@[7] == before_1[7]);
        assert(v@[8] == before_1[8]);
        assert(v@[9] == before_1[9]);
        assert(v@[10] == before_1[10]);
        assert(v@[11] == before_1[11]);
    }
    v
}

/// Parts 0 .. 9 of table nation, in order.
fn assemble_nation_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 10,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
        v@[4] == p4,
        v@[5] == p5,
        v@[6] == p6,
        v@[7] == p7,
        v@[8] == p8,
        v@[9] == p9,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(10);
    v.push(p0);
    v.push(p1);
    v.push(p2);
    v.push(p3);
    v.push(p4);
    v.push(p5);
    v.push(p6);
    v.push(p7);
    v.push(p8);
    v.push(p9);
    v
}

/// The 10 parts of table nation, in order (each named by index in the postcondition).
fn assemble_nation(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 10,
        v@[0] == p0,
        v@[1] == p1,
        v@[2] == p2,
        v@[3] == p3,
        v@[4] == p4,
        v@[5] == p5,
        v@[6] == p6,
        v@[7] == p7,
        v@[8] == p8,
        v@[9] == p9,
{
    let mut c0 = assemble_nation_0(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9);
    let mut v: Vec<OwnedPart> = Vec::new();
    let ghost before_0 = v@;
    v.append(&mut c0);
    assert(v@.len() == 10);
    proof {
        assert(v@[0] == p0);
        assert(v@[1] == p1);
        assert(v@[2] == p2);
        assert(v@[3] == p3);
        assert(v@[4] == p4);
        assert(v@[5] == p5);
        assert(v@[6] == p6);
        assert(v@[7] == p7);
        assert(v@[8] == p8);
        assert(v@[9] == p9);
    }
    v
}

/// Parts 0 .. 7 of table region, in order.
fn assemble_region_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart) -> (v: Vec<OwnedPart>)
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

/// The 8 parts of table region, in order (each named by index in the postcondition).
fn assemble_region(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart) -> (v: Vec<OwnedPart>)
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
    let mut c0 = assemble_region_0(p0, p1, p2, p3, p4, p5, p6, p7);
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
        r matches Ok(p) ==> crate::stores::suppliers::interface::represents(owned_parts_view(p@), tables(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    proof {
        reveal(src_ok);
    }
    let mut parts: Vec<OwnedPart> = Vec::new();
    let mut p_partsupp = match build_partsupp(src, workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_partsupp = p_partsupp@;
    assert(owned_parts_view(v_partsupp).len() == PS_PARTS);
    parts.append(&mut p_partsupp);
    let mut p_supplier = match build_supplier(src, workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_supplier = p_supplier@;
    assert(owned_parts_view(v_supplier).len() == SU_PARTS);
    parts.append(&mut p_supplier);
    let mut p_nation = match build_nation(src, workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_nation = p_nation@;
    assert(owned_parts_view(v_nation).len() == NA_PARTS);
    parts.append(&mut p_nation);
    let mut p_region = match build_region(src, workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_region = p_region@;
    assert(owned_parts_view(v_region).len() == RE_PARTS);
    parts.append(&mut p_region);
    proof {
        let pv = owned_parts_view(parts@);
        let ts = tables(src@);
        assert(pv.subrange(PARTSUPP_FIRST as int, PARTSUPP_FIRST as int + PS_PARTS as int) =~= owned_parts_view(v_partsupp));
        assert(ts[0] == table_t0(src@));
        assert(pv.subrange(SUPPLIER_FIRST as int, SUPPLIER_FIRST as int + SU_PARTS as int) =~= owned_parts_view(v_supplier));
        assert(ts[1] == table_t1(src@));
        assert(pv.subrange(NATION_FIRST as int, NATION_FIRST as int + NA_PARTS as int) =~= owned_parts_view(v_nation));
        assert(ts[2] == table_t2(src@));
        assert(pv.subrange(REGION_FIRST as int, REGION_FIRST as int + RE_PARTS as int) =~= owned_parts_view(v_region));
        assert(ts[3] == table_t3(src@));
    }
    Ok(parts)
}

} // verus!
