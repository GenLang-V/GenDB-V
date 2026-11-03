//! Builder of storage `custpart`: per table, sorted dictionaries of its low-cardinality text columns,
//! frame-of-reference encoding of its integer, numeric, date and dictionary-index columns over blocks of
//! `BLOCK_ROWS` stored rows (one-row blocks if some block does not fit a code width), and copies of its other text
//! columns, in stored order; then its parts in the interface's order, with the proof of `<table>_ok`.
use vstd::prelude::*;
use std::sync::Arc;
pub mod common;
pub use crate::stores::custpart::interface as iface;
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


// ---------------------------------------------------------------------------------------------- customer

/// The facts the builder of table customer uses about the delivered source.
proof fn lemma_src_customer(v: SourceView)
    requires src_ok(v),
    ensures
        source_rows_t0(v) >= 0,
        table_t0(v).len() == source_rows_t0(v),
        tables(v)[0] == table_t0(v),
        v.t0_f1.offsets.len() == source_rows_t0(v) + 1,
        v.t0_f0.len() == source_rows_t0(v),
        twf(v.t0_f1, source_rows_t0(v)),
        twf(v.t0_f2, source_rows_t0(v)),
        v.t0_f3.len() == source_rows_t0(v),
        twf(v.t0_f4, source_rows_t0(v)),
        v.t0_f5.len() == source_rows_t0(v),
        twf(v.t0_f6, source_rows_t0(v)),
        twf(v.t0_f7, source_rows_t0(v)),
        forall|i: int| 0 <= i < v.t0_f5.len() ==> -num15_bound() < #[trigger] v.t0_f5[i] < num15_bound(),
{
    reveal(src_ok);
    reveal(twf);
    lemma_num15(table_t0(v), source_columns_t0(), 5, v.t0_f5);
}

/// The FOR columns of table customer, encoded over blocks of `bsize` stored rows (`None`: some block does not fit).
fn encode_customer(src_custkey: &ValSrc, src_nationkey: &ValSrc, src_acctbal: &ValSrc, src_mktsegment: &ValSrc, rm: &RowMap, n: usize, bsize: usize, zb_mktsegment: bool, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<(ForCol<u32>, ForCol<u8>, ForCol<u32>, ForCol<u8>,)>, QueryError>)
    requires
        src_wf(*src_custkey, n as int),
        src_wf(*src_nationkey, n as int),
        src_wf(*src_acctbal, n as int),
        src_wf(*src_mktsegment, n as int),
        zb_mktsegment ==> fits_zero_base::<u8>(*src_mktsegment, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> for_col_ok(t.0, *src_custkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.1, *src_nationkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.2, *src_acctbal, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.3, *src_mktsegment, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
        r matches Err(e) ==> e is WorkerFailed,
{
    let c_custkey = match encode_column::<u32>(src_custkey, rm, n, bsize, false, workers, dispatch) {
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
    let c_mktsegment = match encode_column::<u8>(src_mktsegment, rm, n, bsize, zb_mktsegment, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(Some((c_custkey, c_nationkey, c_acctbal, c_mktsegment,)))
}

/// The parts of table customer (canonical row order).
fn build_customer(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> customer_ok(owned_parts_view(v@), table_t0(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t0(src@);
    proof {
        lemma_src_customer(src@);
        vstd::slice::axiom_spec_len(src.t0_f1.offsets);
    }
    let n = src.t0_f0.len();
    proof {
        lemma_identity_rm(n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Identity;
    let d_mktsegment = Arc::new(build_dict(&src.t0_f6, n));
    let zb_mktsegment = d_mktsegment.offs.len() - 1 <= 255;
    let src_custkey = ValSrc::Int(src.t0_f0);
    let src_nationkey = ValSrc::Int(src.t0_f3);
    let src_acctbal = ValSrc::Num(src.t0_f5);
    let src_mktsegment = ValSrc::Dict(TextCol { offsets: src.t0_f6.offsets, bytes: src.t0_f6.bytes }, d_mktsegment.clone());
    proof {
        if zb_mktsegment {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_mktsegment, i) <= u8::cap() by {
                lemma_dict_src_bound(src_mktsegment, n as int, i);
            }
        }
    }
    let (bsize, (c_custkey, c_nationkey, c_acctbal, c_mktsegment,)) = match encode_customer(&src_custkey, &src_nationkey, &src_acctbal, &src_mktsegment, &rm, n, bsize0, zb_mktsegment, workers, dispatch) {
        Ok(Some(cols)) => (bsize0, cols),
        Ok(None) => match encode_customer(&src_custkey, &src_nationkey, &src_acctbal, &src_mktsegment, &rm, n, 1, zb_mktsegment, workers, dispatch) {
            Ok(Some(cols)) => (1, cols),
            Ok(None) => { proof { assert(false); } return Err(QueryError::Malformed); }
            Err(e) => return Err(e),
        },
        Err(e) => return Err(e),
    };
    let (o_name, y_name) = match copy_text(&src.t0_f1, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let (o_address, y_address) = match copy_text(&src.t0_f2, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let (o_phone, y_phone) = match copy_text(&src.t0_f4, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let (o_comment, y_comment) = match copy_text(&src.t0_f7, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_col_ranges(c_custkey, src_custkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_nationkey, src_nationkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_acctbal, src_acctbal, rm, n as int, bsize as int);
        lemma_col_ranges(c_mktsegment, src_mktsegment, rm, n as int, bsize as int);
    }
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let b_custkey = bases_i64(&c_custkey.bases);
    let ghost bb_custkey = b_custkey@;
    let ghost cc_custkey = c_custkey.codes@;
    let pp_2 = u32::into_part(c_custkey.codes);
    let pp_3 = OwnedPart::I64(b_custkey);
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
    let b_mktsegment = bases_u64(&c_mktsegment.bases);
    let ghost cc_mktsegment = c_mktsegment.codes@;
    let pp_14 = u8::into_part(c_mktsegment.codes);
    let pp_15 = OwnedPart::U64(b_mktsegment);
    let pp_16 = OwnedPart::U64(copy_u64s(&d_mktsegment.offs));
    let pp_17 = OwnedPart::U8(copy_u8s(&d_mktsegment.bytes));
    let pp_18 = OwnedPart::U64(o_comment);
    let pp_19 = OwnedPart::U8(y_comment);
    let ghost kcs = cc_custkey;
    let ghost kbs = bb_custkey;
    proof {
        lemma_fkey_col(c_custkey, src_custkey, rm, kbs, n as int, bsize as int);
    }
    let key_kind = build_keyidx_sorted(src.t0_f0, n, bsize, Ghost(kcs), Ghost(kbs));
    let pp_20 = OwnedPart::U64(vec![key_kind]);
    let parts = assemble_customer(pp_0, pp_1, pp_2, pp_3, pp_4, pp_5, pp_6, pp_7, pp_8, pp_9, pp_10, pp_11, pp_12, pp_13, pp_14, pp_15, pp_16, pp_17, pp_18, pp_19, pp_20);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == CU_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 8));
        assert(tp[CU_CUSTKEY_CODES as int] == u32::part_of(cc_custkey));
        lemma_for_decode(tp, CU_GROUPS as int, CU_CUSTKEY_CODES as int, CU_CUSTKEY_BASE as int, c_custkey, src_custkey, rm, n as int, bsize as int);
        lemma_int_col(tp, CU_GROUPS as int, CU_CUSTKEY_CODES as int, CU_CUSTKEY_BASE as int, rel, 0, src_custkey, rm);
        lemma_text_col(tp, CU_NAME_OFFS as int, CU_NAME_BYTES as int, rel, 1, o_name@, y_name@, src@.t0_f1, rm);
        lemma_text_col(tp, CU_ADDRESS_OFFS as int, CU_ADDRESS_BYTES as int, rel, 2, o_address@, y_address@, src@.t0_f2, rm);
        assert(tp[CU_NATIONKEY_CODES as int] == u8::part_of(cc_nationkey));
        lemma_for_decode(tp, CU_GROUPS as int, CU_NATIONKEY_CODES as int, CU_NATIONKEY_BASE as int, c_nationkey, src_nationkey, rm, n as int, bsize as int);
        lemma_int_col(tp, CU_GROUPS as int, CU_NATIONKEY_CODES as int, CU_NATIONKEY_BASE as int, rel, 3, src_nationkey, rm);
        lemma_text_col(tp, CU_PHONE_OFFS as int, CU_PHONE_BYTES as int, rel, 4, o_phone@, y_phone@, src@.t0_f4, rm);
        assert(tp[CU_ACCTBAL_CODES as int] == u32::part_of(cc_acctbal));
        lemma_for_decode(tp, CU_GROUPS as int, CU_ACCTBAL_CODES as int, CU_ACCTBAL_BASE as int, c_acctbal, src_acctbal, rm, n as int, bsize as int);
        lemma_num_col(tp, CU_GROUPS as int, CU_ACCTBAL_CODES as int, CU_ACCTBAL_BASE as int, rel, 5, 2, src_acctbal, rm);
        assert(tp[CU_MKTSEGMENT_CODES as int] == u8::part_of(cc_mktsegment));
        lemma_for_decode(tp, CU_GROUPS as int, CU_MKTSEGMENT_CODES as int, CU_MKTSEGMENT_BASE as int, c_mktsegment, src_mktsegment, rm, n as int, bsize as int);
        lemma_dict_col(tp, CU_GROUPS as int, CU_MKTSEGMENT_CODES as int, CU_MKTSEGMENT_BASE as int, CU_MKTSEGMENT_DICT_OFFS as int, CU_MKTSEGMENT_DICT_BYTES as int, rel, 6, src@.t0_f6, &d_mktsegment, rm, n as int);
        lemma_text_col(tp, CU_COMMENT_OFFS as int, CU_COMMENT_BYTES as int, rel, 7, o_comment@, y_comment@, src@.t0_f7, rm);
        assert(u64s(tp[CU_KEYIDX_KIND as int]) =~= seq![key_kind]);
        assert(u32s(tp[CU_CUSTKEY_CODES as int]) == kcs);
        assert(i64s(tp[CU_CUSTKEY_BASE as int]) == kbs);
    }
    Ok(parts)
}

// ---------------------------------------------------------------------------------------------- part

/// The facts the builder of table part uses about the delivered source.
proof fn lemma_src_part(v: SourceView)
    requires src_ok(v),
    ensures
        source_rows_t1(v) >= 0,
        table_t1(v).len() == source_rows_t1(v),
        tables(v)[1] == table_t1(v),
        v.t1_f1.offsets.len() == source_rows_t1(v) + 1,
        v.t1_f0.len() == source_rows_t1(v),
        twf(v.t1_f1, source_rows_t1(v)),
        twf(v.t1_f2, source_rows_t1(v)),
        twf(v.t1_f3, source_rows_t1(v)),
        twf(v.t1_f4, source_rows_t1(v)),
        v.t1_f5.len() == source_rows_t1(v),
        twf(v.t1_f6, source_rows_t1(v)),
        v.t1_f7.len() == source_rows_t1(v),
        twf(v.t1_f8, source_rows_t1(v)),
        forall|i: int| 0 <= i < v.t1_f7.len() ==> -num15_bound() < #[trigger] v.t1_f7[i] < num15_bound(),
{
    reveal(src_ok);
    reveal(twf);
    lemma_num15(table_t1(v), source_columns_t1(), 7, v.t1_f7);
}

/// The FOR columns of table part, encoded over blocks of `bsize` stored rows (`None`: some block does not fit).
fn encode_part(src_partkey: &ValSrc, src_mfgr: &ValSrc, src_brand: &ValSrc, src_type: &ValSrc, src_size: &ValSrc, src_container: &ValSrc, src_retailprice: &ValSrc, rm: &RowMap, n: usize, bsize: usize, zb_mfgr: bool, zb_brand: bool, zb_type: bool, zb_container: bool, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<(ForCol<u32>, ForCol<u8>, ForCol<u8>, ForCol<u8>, ForCol<u8>, ForCol<u8>, ForCol<u32>,)>, QueryError>)
    requires
        src_wf(*src_partkey, n as int),
        src_wf(*src_mfgr, n as int),
        src_wf(*src_brand, n as int),
        src_wf(*src_type, n as int),
        src_wf(*src_size, n as int),
        src_wf(*src_container, n as int),
        src_wf(*src_retailprice, n as int),
        zb_mfgr ==> fits_zero_base::<u8>(*src_mfgr, n as int),
        zb_brand ==> fits_zero_base::<u8>(*src_brand, n as int),
        zb_type ==> fits_zero_base::<u8>(*src_type, n as int),
        zb_container ==> fits_zero_base::<u8>(*src_container, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> for_col_ok(t.0, *src_partkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.1, *src_mfgr, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.2, *src_brand, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.3, *src_type, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.4, *src_size, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.5, *src_container, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.6, *src_retailprice, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
        r matches Err(e) ==> e is WorkerFailed,
{
    let c_partkey = match encode_column::<u32>(src_partkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_mfgr = match encode_column::<u8>(src_mfgr, rm, n, bsize, zb_mfgr, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_brand = match encode_column::<u8>(src_brand, rm, n, bsize, zb_brand, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_type = match encode_column::<u8>(src_type, rm, n, bsize, zb_type, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_size = match encode_column::<u8>(src_size, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_container = match encode_column::<u8>(src_container, rm, n, bsize, zb_container, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_retailprice = match encode_column::<u32>(src_retailprice, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(Some((c_partkey, c_mfgr, c_brand, c_type, c_size, c_container, c_retailprice,)))
}

/// The parts of table part (canonical row order).
fn build_part(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> part_ok(owned_parts_view(v@), table_t1(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t1(src@);
    proof {
        lemma_src_part(src@);
        vstd::slice::axiom_spec_len(src.t1_f1.offsets);
    }
    let n = src.t1_f0.len();
    proof {
        lemma_identity_rm(n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Identity;
    let d_mfgr = Arc::new(build_dict(&src.t1_f2, n));
    let zb_mfgr = d_mfgr.offs.len() - 1 <= 255;
    let d_brand = Arc::new(build_dict(&src.t1_f3, n));
    let zb_brand = d_brand.offs.len() - 1 <= 255;
    let d_type = Arc::new(build_dict(&src.t1_f4, n));
    let zb_type = d_type.offs.len() - 1 <= 255;
    let d_container = Arc::new(build_dict(&src.t1_f6, n));
    let zb_container = d_container.offs.len() - 1 <= 255;
    let src_partkey = ValSrc::Int(src.t1_f0);
    let src_mfgr = ValSrc::Dict(TextCol { offsets: src.t1_f2.offsets, bytes: src.t1_f2.bytes }, d_mfgr.clone());
    let src_brand = ValSrc::Dict(TextCol { offsets: src.t1_f3.offsets, bytes: src.t1_f3.bytes }, d_brand.clone());
    let src_type = ValSrc::Dict(TextCol { offsets: src.t1_f4.offsets, bytes: src.t1_f4.bytes }, d_type.clone());
    let src_size = ValSrc::Int(src.t1_f5);
    let src_container = ValSrc::Dict(TextCol { offsets: src.t1_f6.offsets, bytes: src.t1_f6.bytes }, d_container.clone());
    let src_retailprice = ValSrc::Num(src.t1_f7);
    proof {
        if zb_mfgr {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_mfgr, i) <= u8::cap() by {
                lemma_dict_src_bound(src_mfgr, n as int, i);
            }
        }
        if zb_brand {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_brand, i) <= u8::cap() by {
                lemma_dict_src_bound(src_brand, n as int, i);
            }
        }
        if zb_type {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_type, i) <= u8::cap() by {
                lemma_dict_src_bound(src_type, n as int, i);
            }
        }
        if zb_container {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_container, i) <= u8::cap() by {
                lemma_dict_src_bound(src_container, n as int, i);
            }
        }
    }
    let (bsize, (c_partkey, c_mfgr, c_brand, c_type, c_size, c_container, c_retailprice,)) = match encode_part(&src_partkey, &src_mfgr, &src_brand, &src_type, &src_size, &src_container, &src_retailprice, &rm, n, bsize0, zb_mfgr, zb_brand, zb_type, zb_container, workers, dispatch) {
        Ok(Some(cols)) => (bsize0, cols),
        Ok(None) => match encode_part(&src_partkey, &src_mfgr, &src_brand, &src_type, &src_size, &src_container, &src_retailprice, &rm, n, 1, zb_mfgr, zb_brand, zb_type, zb_container, workers, dispatch) {
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
    let (o_comment, y_comment) = match copy_text(&src.t1_f8, n, &rm, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_col_ranges(c_partkey, src_partkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_mfgr, src_mfgr, rm, n as int, bsize as int);
        lemma_col_ranges(c_brand, src_brand, rm, n as int, bsize as int);
        lemma_col_ranges(c_type, src_type, rm, n as int, bsize as int);
        lemma_col_ranges(c_size, src_size, rm, n as int, bsize as int);
        lemma_col_ranges(c_container, src_container, rm, n as int, bsize as int);
        lemma_col_ranges(c_retailprice, src_retailprice, rm, n as int, bsize as int);
    }
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let b_partkey = bases_i64(&c_partkey.bases);
    let ghost bb_partkey = b_partkey@;
    let ghost cc_partkey = c_partkey.codes@;
    let pp_2 = u32::into_part(c_partkey.codes);
    let pp_3 = OwnedPart::I64(b_partkey);
    let pp_4 = OwnedPart::U64(o_name);
    let pp_5 = OwnedPart::U8(y_name);
    let b_mfgr = bases_u64(&c_mfgr.bases);
    let ghost cc_mfgr = c_mfgr.codes@;
    let pp_6 = u8::into_part(c_mfgr.codes);
    let pp_7 = OwnedPart::U64(b_mfgr);
    let pp_8 = OwnedPart::U64(copy_u64s(&d_mfgr.offs));
    let pp_9 = OwnedPart::U8(copy_u8s(&d_mfgr.bytes));
    let b_brand = bases_u64(&c_brand.bases);
    let ghost cc_brand = c_brand.codes@;
    let pp_10 = u8::into_part(c_brand.codes);
    let pp_11 = OwnedPart::U64(b_brand);
    let pp_12 = OwnedPart::U64(copy_u64s(&d_brand.offs));
    let pp_13 = OwnedPart::U8(copy_u8s(&d_brand.bytes));
    let b_type = bases_u64(&c_type.bases);
    let ghost cc_type = c_type.codes@;
    let pp_14 = u8::into_part(c_type.codes);
    let pp_15 = OwnedPart::U64(b_type);
    let pp_16 = OwnedPart::U64(copy_u64s(&d_type.offs));
    let pp_17 = OwnedPart::U8(copy_u8s(&d_type.bytes));
    let b_size = bases_i64(&c_size.bases);
    let ghost bb_size = b_size@;
    let ghost cc_size = c_size.codes@;
    let pp_18 = u8::into_part(c_size.codes);
    let pp_19 = OwnedPart::I64(b_size);
    let b_container = bases_u64(&c_container.bases);
    let ghost cc_container = c_container.codes@;
    let pp_20 = u8::into_part(c_container.codes);
    let pp_21 = OwnedPart::U64(b_container);
    let pp_22 = OwnedPart::U64(copy_u64s(&d_container.offs));
    let pp_23 = OwnedPart::U8(copy_u8s(&d_container.bytes));
    let b_retailprice = bases_i64(&c_retailprice.bases);
    let ghost bb_retailprice = b_retailprice@;
    let ghost cc_retailprice = c_retailprice.codes@;
    let pp_24 = u32::into_part(c_retailprice.codes);
    let pp_25 = OwnedPart::I64(b_retailprice);
    let pp_26 = OwnedPart::U64(o_comment);
    let pp_27 = OwnedPart::U8(y_comment);
    let ghost kcs = cc_partkey;
    let ghost kbs = bb_partkey;
    proof {
        lemma_fkey_col(c_partkey, src_partkey, rm, kbs, n as int, bsize as int);
    }
    let key_kind = build_keyidx_sorted(src.t1_f0, n, bsize, Ghost(kcs), Ghost(kbs));
    let pp_28 = OwnedPart::U64(vec![key_kind]);
    let parts = assemble_part(pp_0, pp_1, pp_2, pp_3, pp_4, pp_5, pp_6, pp_7, pp_8, pp_9, pp_10, pp_11, pp_12, pp_13, pp_14, pp_15, pp_16, pp_17, pp_18, pp_19, pp_20, pp_21, pp_22, pp_23, pp_24, pp_25, pp_26, pp_27, pp_28);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == PA_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 9));
        assert(tp[PA_PARTKEY_CODES as int] == u32::part_of(cc_partkey));
        lemma_for_decode(tp, PA_GROUPS as int, PA_PARTKEY_CODES as int, PA_PARTKEY_BASE as int, c_partkey, src_partkey, rm, n as int, bsize as int);
        lemma_int_col(tp, PA_GROUPS as int, PA_PARTKEY_CODES as int, PA_PARTKEY_BASE as int, rel, 0, src_partkey, rm);
        lemma_text_col(tp, PA_NAME_OFFS as int, PA_NAME_BYTES as int, rel, 1, o_name@, y_name@, src@.t1_f1, rm);
        assert(tp[PA_MFGR_CODES as int] == u8::part_of(cc_mfgr));
        lemma_for_decode(tp, PA_GROUPS as int, PA_MFGR_CODES as int, PA_MFGR_BASE as int, c_mfgr, src_mfgr, rm, n as int, bsize as int);
        lemma_dict_col(tp, PA_GROUPS as int, PA_MFGR_CODES as int, PA_MFGR_BASE as int, PA_MFGR_DICT_OFFS as int, PA_MFGR_DICT_BYTES as int, rel, 2, src@.t1_f2, &d_mfgr, rm, n as int);
        assert(tp[PA_BRAND_CODES as int] == u8::part_of(cc_brand));
        lemma_for_decode(tp, PA_GROUPS as int, PA_BRAND_CODES as int, PA_BRAND_BASE as int, c_brand, src_brand, rm, n as int, bsize as int);
        lemma_dict_col(tp, PA_GROUPS as int, PA_BRAND_CODES as int, PA_BRAND_BASE as int, PA_BRAND_DICT_OFFS as int, PA_BRAND_DICT_BYTES as int, rel, 3, src@.t1_f3, &d_brand, rm, n as int);
        assert(tp[PA_TYPE_CODES as int] == u8::part_of(cc_type));
        lemma_for_decode(tp, PA_GROUPS as int, PA_TYPE_CODES as int, PA_TYPE_BASE as int, c_type, src_type, rm, n as int, bsize as int);
        lemma_dict_col(tp, PA_GROUPS as int, PA_TYPE_CODES as int, PA_TYPE_BASE as int, PA_TYPE_DICT_OFFS as int, PA_TYPE_DICT_BYTES as int, rel, 4, src@.t1_f4, &d_type, rm, n as int);
        assert(tp[PA_SIZE_CODES as int] == u8::part_of(cc_size));
        lemma_for_decode(tp, PA_GROUPS as int, PA_SIZE_CODES as int, PA_SIZE_BASE as int, c_size, src_size, rm, n as int, bsize as int);
        lemma_int_col(tp, PA_GROUPS as int, PA_SIZE_CODES as int, PA_SIZE_BASE as int, rel, 5, src_size, rm);
        assert(tp[PA_CONTAINER_CODES as int] == u8::part_of(cc_container));
        lemma_for_decode(tp, PA_GROUPS as int, PA_CONTAINER_CODES as int, PA_CONTAINER_BASE as int, c_container, src_container, rm, n as int, bsize as int);
        lemma_dict_col(tp, PA_GROUPS as int, PA_CONTAINER_CODES as int, PA_CONTAINER_BASE as int, PA_CONTAINER_DICT_OFFS as int, PA_CONTAINER_DICT_BYTES as int, rel, 6, src@.t1_f6, &d_container, rm, n as int);
        assert(tp[PA_RETAILPRICE_CODES as int] == u32::part_of(cc_retailprice));
        lemma_for_decode(tp, PA_GROUPS as int, PA_RETAILPRICE_CODES as int, PA_RETAILPRICE_BASE as int, c_retailprice, src_retailprice, rm, n as int, bsize as int);
        lemma_num_col(tp, PA_GROUPS as int, PA_RETAILPRICE_CODES as int, PA_RETAILPRICE_BASE as int, rel, 7, 2, src_retailprice, rm);
        lemma_text_col(tp, PA_COMMENT_OFFS as int, PA_COMMENT_BYTES as int, rel, 8, o_comment@, y_comment@, src@.t1_f8, rm);
        assert(u64s(tp[PA_KEYIDX_KIND as int]) =~= seq![key_kind]);
        assert(u32s(tp[PA_PARTKEY_CODES as int]) == kcs);
        assert(i64s(tp[PA_PARTKEY_BASE as int]) == kbs);
    }
    Ok(parts)
}

/// Parts 0 .. 11 of table customer, in order.
fn assemble_customer_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart) -> (v: Vec<OwnedPart>)
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

/// Parts 12 .. 20 of table customer, in order.
fn assemble_customer_1(p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart, p17: OwnedPart, p18: OwnedPart, p19: OwnedPart, p20: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 9,
        v@[0] == p12,
        v@[1] == p13,
        v@[2] == p14,
        v@[3] == p15,
        v@[4] == p16,
        v@[5] == p17,
        v@[6] == p18,
        v@[7] == p19,
        v@[8] == p20,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(9);
    v.push(p12);
    v.push(p13);
    v.push(p14);
    v.push(p15);
    v.push(p16);
    v.push(p17);
    v.push(p18);
    v.push(p19);
    v.push(p20);
    v
}

/// The 21 parts of table customer, in order (each named by index in the postcondition).
fn assemble_customer(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart, p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart, p17: OwnedPart, p18: OwnedPart, p19: OwnedPart, p20: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 21,
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
        v@[17] == p17,
        v@[18] == p18,
        v@[19] == p19,
        v@[20] == p20,
{
    let mut c0 = assemble_customer_0(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11);
    let mut c1 = assemble_customer_1(p12, p13, p14, p15, p16, p17, p18, p19, p20);
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
    assert(v@.len() == 21);
    proof {
        assert(v@[12] == p12);
        assert(v@[13] == p13);
        assert(v@[14] == p14);
        assert(v@[15] == p15);
        assert(v@[16] == p16);
        assert(v@[17] == p17);
        assert(v@[18] == p18);
        assert(v@[19] == p19);
        assert(v@[20] == p20);
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

/// Parts 0 .. 11 of table part, in order.
fn assemble_part_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart) -> (v: Vec<OwnedPart>)
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

/// Parts 12 .. 23 of table part, in order.
fn assemble_part_1(p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart, p17: OwnedPart, p18: OwnedPart, p19: OwnedPart, p20: OwnedPart, p21: OwnedPart, p22: OwnedPart, p23: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 12,
        v@[0] == p12,
        v@[1] == p13,
        v@[2] == p14,
        v@[3] == p15,
        v@[4] == p16,
        v@[5] == p17,
        v@[6] == p18,
        v@[7] == p19,
        v@[8] == p20,
        v@[9] == p21,
        v@[10] == p22,
        v@[11] == p23,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(12);
    v.push(p12);
    v.push(p13);
    v.push(p14);
    v.push(p15);
    v.push(p16);
    v.push(p17);
    v.push(p18);
    v.push(p19);
    v.push(p20);
    v.push(p21);
    v.push(p22);
    v.push(p23);
    v
}

/// Parts 24 .. 28 of table part, in order.
fn assemble_part_2(p24: OwnedPart, p25: OwnedPart, p26: OwnedPart, p27: OwnedPart, p28: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 5,
        v@[0] == p24,
        v@[1] == p25,
        v@[2] == p26,
        v@[3] == p27,
        v@[4] == p28,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(5);
    v.push(p24);
    v.push(p25);
    v.push(p26);
    v.push(p27);
    v.push(p28);
    v
}

/// The 29 parts of table part, in order (each named by index in the postcondition).
fn assemble_part(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart, p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart, p17: OwnedPart, p18: OwnedPart, p19: OwnedPart, p20: OwnedPart, p21: OwnedPart, p22: OwnedPart, p23: OwnedPart, p24: OwnedPart, p25: OwnedPart, p26: OwnedPart, p27: OwnedPart, p28: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 29,
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
        v@[17] == p17,
        v@[18] == p18,
        v@[19] == p19,
        v@[20] == p20,
        v@[21] == p21,
        v@[22] == p22,
        v@[23] == p23,
        v@[24] == p24,
        v@[25] == p25,
        v@[26] == p26,
        v@[27] == p27,
        v@[28] == p28,
{
    let mut c0 = assemble_part_0(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11);
    let mut c1 = assemble_part_1(p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23);
    let mut c2 = assemble_part_2(p24, p25, p26, p27, p28);
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
    assert(v@.len() == 24);
    proof {
        assert(v@[12] == p12);
        assert(v@[13] == p13);
        assert(v@[14] == p14);
        assert(v@[15] == p15);
        assert(v@[16] == p16);
        assert(v@[17] == p17);
        assert(v@[18] == p18);
        assert(v@[19] == p19);
        assert(v@[20] == p20);
        assert(v@[21] == p21);
        assert(v@[22] == p22);
        assert(v@[23] == p23);
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
    let ghost before_2 = v@;
    v.append(&mut c2);
    assert(v@.len() == 29);
    proof {
        assert(v@[24] == p24);
        assert(v@[25] == p25);
        assert(v@[26] == p26);
        assert(v@[27] == p27);
        assert(v@[28] == p28);
        assert(v@[0] == before_2[0]);
        assert(v@[1] == before_2[1]);
        assert(v@[2] == before_2[2]);
        assert(v@[3] == before_2[3]);
        assert(v@[4] == before_2[4]);
        assert(v@[5] == before_2[5]);
        assert(v@[6] == before_2[6]);
        assert(v@[7] == before_2[7]);
        assert(v@[8] == before_2[8]);
        assert(v@[9] == before_2[9]);
        assert(v@[10] == before_2[10]);
        assert(v@[11] == before_2[11]);
        assert(v@[12] == before_2[12]);
        assert(v@[13] == before_2[13]);
        assert(v@[14] == before_2[14]);
        assert(v@[15] == before_2[15]);
        assert(v@[16] == before_2[16]);
        assert(v@[17] == before_2[17]);
        assert(v@[18] == before_2[18]);
        assert(v@[19] == before_2[19]);
        assert(v@[20] == before_2[20]);
        assert(v@[21] == before_2[21]);
        assert(v@[22] == before_2[22]);
        assert(v@[23] == before_2[23]);
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
        r matches Ok(p) ==> crate::stores::custpart::interface::represents(owned_parts_view(p@), tables(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    proof {
        reveal(src_ok);
    }
    let mut parts: Vec<OwnedPart> = Vec::new();
    let mut p_customer = match build_customer(src, workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_customer = p_customer@;
    assert(owned_parts_view(v_customer).len() == CU_PARTS);
    parts.append(&mut p_customer);
    let mut p_part = match build_part(src, workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_part = p_part@;
    assert(owned_parts_view(v_part).len() == PA_PARTS);
    parts.append(&mut p_part);
    proof {
        let pv = owned_parts_view(parts@);
        let ts = tables(src@);
        assert(pv.subrange(CUSTOMER_FIRST as int, CUSTOMER_FIRST as int + CU_PARTS as int) =~= owned_parts_view(v_customer));
        assert(ts[0] == table_t0(src@));
        assert(pv.subrange(PART_FIRST as int, PART_FIRST as int + PA_PARTS as int) =~= owned_parts_view(v_part));
        assert(ts[1] == table_t1(src@));
    }
    Ok(parts)
}

} // verus!
