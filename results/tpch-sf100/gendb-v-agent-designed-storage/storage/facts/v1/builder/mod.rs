//! Builder of storage `facts`: per table, sorted dictionaries of its low-cardinality text columns,
//! frame-of-reference encoding of its integer, numeric, date and dictionary-index columns over blocks of
//! `BLOCK_ROWS` stored rows (one-row blocks if some block does not fit a code width), and copies of its other text
//! columns, in stored order; then its parts in the interface's order, with the proof of `<table>_ok`.
//! Clustered tables are stored in the order `order` computes (a checked bijection, else canonical order).
use vstd::prelude::*;
use std::sync::Arc;
pub mod common;
pub mod order;
pub mod clustercheck;
pub use crate::stores::facts::interface as iface;
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
        v.t0_f8.offsets.len() == source_rows_t0(v) + 1,
        v.t0_f0.len() == source_rows_t0(v),
        v.t0_f1.len() == source_rows_t0(v),
        v.t0_f2.len() == source_rows_t0(v),
        v.t0_f3.len() == source_rows_t0(v),
        v.t0_f4.len() == source_rows_t0(v),
        v.t0_f5.len() == source_rows_t0(v),
        v.t0_f6.len() == source_rows_t0(v),
        v.t0_f7.len() == source_rows_t0(v),
        twf(v.t0_f8, source_rows_t0(v)),
        twf(v.t0_f9, source_rows_t0(v)),
        v.t0_f10.len() == source_rows_t0(v),
        v.t0_f11.len() == source_rows_t0(v),
        v.t0_f12.len() == source_rows_t0(v),
        twf(v.t0_f13, source_rows_t0(v)),
        twf(v.t0_f14, source_rows_t0(v)),
        forall|i: int| 0 <= i < v.t0_f4.len() ==> -num15_bound() < #[trigger] v.t0_f4[i] < num15_bound(),
        forall|i: int| 0 <= i < v.t0_f5.len() ==> -num15_bound() < #[trigger] v.t0_f5[i] < num15_bound(),
        forall|i: int| 0 <= i < v.t0_f6.len() ==> -num15_bound() < #[trigger] v.t0_f6[i] < num15_bound(),
        forall|i: int| 0 <= i < v.t0_f7.len() ==> -num15_bound() < #[trigger] v.t0_f7[i] < num15_bound(),
{
    reveal(src_ok);
    reveal(twf);
    lemma_num15(table_t0(v), source_columns_t0(), 4, v.t0_f4);
    lemma_num15(table_t0(v), source_columns_t0(), 5, v.t0_f5);
    lemma_num15(table_t0(v), source_columns_t0(), 6, v.t0_f6);
    lemma_num15(table_t0(v), source_columns_t0(), 7, v.t0_f7);
}

/// The FOR columns of table lineitem, encoded over blocks of `bsize` stored rows (`None`: some block does not fit).
fn encode_lineitem(src_perm: &ValSrc, src_orderkey: &ValSrc, src_partkey: &ValSrc, src_suppkey: &ValSrc, src_linenumber: &ValSrc, src_quantity: &ValSrc, src_extendedprice: &ValSrc, src_discount: &ValSrc, src_tax: &ValSrc, src_returnflag: &ValSrc, src_linestatus: &ValSrc, src_shipdate: &ValSrc, src_commitdate: &ValSrc, src_receiptdate: &ValSrc, src_shipinstruct: &ValSrc, src_shipmode: &ValSrc, rm: &RowMap, n: usize, bsize: usize, zb_returnflag: bool, zb_linestatus: bool, zb_shipinstruct: bool, zb_shipmode: bool, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<(ForCol<u32>, ForCol<u32>, ForCol<u32>, ForCol<u32>, ForCol<u8>, ForCol<u16>, ForCol<u32>, ForCol<u8>, ForCol<u8>, ForCol<u8>, ForCol<u8>, ForCol<u16>, ForCol<u16>, ForCol<u16>, ForCol<u8>, ForCol<u8>,)>, QueryError>)
    requires
        src_wf(*src_perm, n as int),
        src_wf(*src_orderkey, n as int),
        src_wf(*src_partkey, n as int),
        src_wf(*src_suppkey, n as int),
        src_wf(*src_linenumber, n as int),
        src_wf(*src_quantity, n as int),
        src_wf(*src_extendedprice, n as int),
        src_wf(*src_discount, n as int),
        src_wf(*src_tax, n as int),
        src_wf(*src_returnflag, n as int),
        src_wf(*src_linestatus, n as int),
        src_wf(*src_shipdate, n as int),
        src_wf(*src_commitdate, n as int),
        src_wf(*src_receiptdate, n as int),
        src_wf(*src_shipinstruct, n as int),
        src_wf(*src_shipmode, n as int),
        zb_returnflag ==> fits_zero_base::<u8>(*src_returnflag, n as int),
        zb_linestatus ==> fits_zero_base::<u8>(*src_linestatus, n as int),
        zb_shipinstruct ==> fits_zero_base::<u8>(*src_shipinstruct, n as int),
        zb_shipmode ==> fits_zero_base::<u8>(*src_shipmode, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> for_col_ok(t.0, *src_perm, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.1, *src_orderkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.2, *src_partkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.3, *src_suppkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.4, *src_linenumber, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.5, *src_quantity, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.6, *src_extendedprice, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.7, *src_discount, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.8, *src_tax, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.9, *src_returnflag, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.10, *src_linestatus, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.11, *src_shipdate, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.12, *src_commitdate, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.13, *src_receiptdate, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.14, *src_shipinstruct, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.15, *src_shipmode, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
        r matches Err(e) ==> e is WorkerFailed,
{
    let c_perm = match encode_column::<u32>(src_perm, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_orderkey = match encode_column::<u32>(src_orderkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
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
    let c_linenumber = match encode_column::<u8>(src_linenumber, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_quantity = match encode_column::<u16>(src_quantity, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_extendedprice = match encode_column::<u32>(src_extendedprice, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_discount = match encode_column::<u8>(src_discount, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_tax = match encode_column::<u8>(src_tax, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_returnflag = match encode_column::<u8>(src_returnflag, rm, n, bsize, zb_returnflag, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_linestatus = match encode_column::<u8>(src_linestatus, rm, n, bsize, zb_linestatus, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_shipdate = match encode_column::<u16>(src_shipdate, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_commitdate = match encode_column::<u16>(src_commitdate, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_receiptdate = match encode_column::<u16>(src_receiptdate, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_shipinstruct = match encode_column::<u8>(src_shipinstruct, rm, n, bsize, zb_shipinstruct, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_shipmode = match encode_column::<u8>(src_shipmode, rm, n, bsize, zb_shipmode, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(Some((c_perm, c_orderkey, c_partkey, c_suppkey, c_linenumber, c_quantity, c_extendedprice, c_discount, c_tax, c_returnflag, c_linestatus, c_shipdate, c_commitdate, c_receiptdate, c_shipinstruct, c_shipmode,)))
}

/// The parts of table lineitem (clustered order `rmv` (stored row -> canonical row)).
fn build_lineitem(src: &SourceRef, rmv: Arc<Vec<u64>>, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
        rmv@.len() == table_t0(src@).len(),
        is_perm(map_view(rmv@), table_t0(src@).len() as int),
    ensures
        r matches Ok(v) ==> lineitem_ok(owned_parts_view(v@), table_t0(src@)),
        r matches Ok(v) ==> lineitem_map(owned_parts_view(v@), table_t0(src@).len() as int) == map_view(rmv@),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t0(src@);
    proof {
        lemma_src_lineitem(src@);
        vstd::slice::axiom_spec_len(src.t0_f8.offsets);
    }
    let n = src.t0_f0.len();
    proof {
        lemma_map_rm(rmv, n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Map(rmv.clone());
    let ghost rows = stored_rows(rel, map_view(rmv@));
    let d_returnflag = Arc::new(build_dict(&src.t0_f8, n));
    let zb_returnflag = d_returnflag.offs.len() - 1 <= 255;
    let d_linestatus = Arc::new(build_dict(&src.t0_f9, n));
    let zb_linestatus = d_linestatus.offs.len() - 1 <= 255;
    let d_shipinstruct = Arc::new(build_dict(&src.t0_f13, n));
    let zb_shipinstruct = d_shipinstruct.offs.len() - 1 <= 255;
    let d_shipmode = Arc::new(build_dict(&src.t0_f14, n));
    let zb_shipmode = d_shipmode.offs.len() - 1 <= 255;
    let src_perm = ValSrc::Pos;
    let src_orderkey = ValSrc::Int(src.t0_f0);
    let src_partkey = ValSrc::Int(src.t0_f1);
    let src_suppkey = ValSrc::Int(src.t0_f2);
    let src_linenumber = ValSrc::Int(src.t0_f3);
    let src_quantity = ValSrc::Num(src.t0_f4);
    let src_extendedprice = ValSrc::Num(src.t0_f5);
    let src_discount = ValSrc::Num(src.t0_f6);
    let src_tax = ValSrc::Num(src.t0_f7);
    let src_returnflag = ValSrc::Dict(TextCol { offsets: src.t0_f8.offsets, bytes: src.t0_f8.bytes }, d_returnflag.clone());
    let src_linestatus = ValSrc::Dict(TextCol { offsets: src.t0_f9.offsets, bytes: src.t0_f9.bytes }, d_linestatus.clone());
    let src_shipdate = ValSrc::Date(src.t0_f10);
    let src_commitdate = ValSrc::Date(src.t0_f11);
    let src_receiptdate = ValSrc::Date(src.t0_f12);
    let src_shipinstruct = ValSrc::Dict(TextCol { offsets: src.t0_f13.offsets, bytes: src.t0_f13.bytes }, d_shipinstruct.clone());
    let src_shipmode = ValSrc::Dict(TextCol { offsets: src.t0_f14.offsets, bytes: src.t0_f14.bytes }, d_shipmode.clone());
    proof {
        if zb_returnflag {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_returnflag, i) <= u8::cap() by {
                lemma_dict_src_bound(src_returnflag, n as int, i);
            }
        }
        if zb_linestatus {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_linestatus, i) <= u8::cap() by {
                lemma_dict_src_bound(src_linestatus, n as int, i);
            }
        }
        if zb_shipinstruct {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_shipinstruct, i) <= u8::cap() by {
                lemma_dict_src_bound(src_shipinstruct, n as int, i);
            }
        }
        if zb_shipmode {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_shipmode, i) <= u8::cap() by {
                lemma_dict_src_bound(src_shipmode, n as int, i);
            }
        }
    }
    let (bsize, (c_perm, c_orderkey, c_partkey, c_suppkey, c_linenumber, c_quantity, c_extendedprice, c_discount, c_tax, c_returnflag, c_linestatus, c_shipdate, c_commitdate, c_receiptdate, c_shipinstruct, c_shipmode,)) = match encode_lineitem(&src_perm, &src_orderkey, &src_partkey, &src_suppkey, &src_linenumber, &src_quantity, &src_extendedprice, &src_discount, &src_tax, &src_returnflag, &src_linestatus, &src_shipdate, &src_commitdate, &src_receiptdate, &src_shipinstruct, &src_shipmode, &rm, n, bsize0, zb_returnflag, zb_linestatus, zb_shipinstruct, zb_shipmode, workers, dispatch) {
        Ok(Some(cols)) => (bsize0, cols),
        Ok(None) => match encode_lineitem(&src_perm, &src_orderkey, &src_partkey, &src_suppkey, &src_linenumber, &src_quantity, &src_extendedprice, &src_discount, &src_tax, &src_returnflag, &src_linestatus, &src_shipdate, &src_commitdate, &src_receiptdate, &src_shipinstruct, &src_shipmode, &rm, n, 1, zb_returnflag, zb_linestatus, zb_shipinstruct, zb_shipmode, workers, dispatch) {
            Ok(Some(cols)) => (1, cols),
            Ok(None) => { proof { assert(false); } return Err(QueryError::Malformed); }
            Err(e) => return Err(e),
        },
        Err(e) => return Err(e),
    };
    proof {
        lemma_col_ranges(c_perm, src_perm, rm, n as int, bsize as int);
        lemma_col_ranges(c_orderkey, src_orderkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_partkey, src_partkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_suppkey, src_suppkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_linenumber, src_linenumber, rm, n as int, bsize as int);
        lemma_col_ranges(c_quantity, src_quantity, rm, n as int, bsize as int);
        lemma_col_ranges(c_extendedprice, src_extendedprice, rm, n as int, bsize as int);
        lemma_col_ranges(c_discount, src_discount, rm, n as int, bsize as int);
        lemma_col_ranges(c_tax, src_tax, rm, n as int, bsize as int);
        lemma_col_ranges(c_returnflag, src_returnflag, rm, n as int, bsize as int);
        lemma_col_ranges(c_linestatus, src_linestatus, rm, n as int, bsize as int);
        lemma_col_ranges(c_shipdate, src_shipdate, rm, n as int, bsize as int);
        lemma_col_ranges(c_commitdate, src_commitdate, rm, n as int, bsize as int);
        lemma_col_ranges(c_receiptdate, src_receiptdate, rm, n as int, bsize as int);
        lemma_col_ranges(c_shipinstruct, src_shipinstruct, rm, n as int, bsize as int);
        lemma_col_ranges(c_shipmode, src_shipmode, rm, n as int, bsize as int);
    }
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let b_perm = bases_u64(&c_perm.bases);
    let ghost cc_perm = c_perm.codes@;
    let pp_2 = u32::into_part(c_perm.codes);
    let pp_3 = OwnedPart::U64(b_perm);
    let b_orderkey = bases_i64(&c_orderkey.bases);
    let ghost bb_orderkey = b_orderkey@;
    let ghost cc_orderkey = c_orderkey.codes@;
    let pp_4 = u32::into_part(c_orderkey.codes);
    let pp_5 = OwnedPart::I64(b_orderkey);
    let b_partkey = bases_i64(&c_partkey.bases);
    let ghost bb_partkey = b_partkey@;
    let ghost cc_partkey = c_partkey.codes@;
    let pp_6 = u32::into_part(c_partkey.codes);
    let pp_7 = OwnedPart::I64(b_partkey);
    let b_suppkey = bases_i64(&c_suppkey.bases);
    let ghost bb_suppkey = b_suppkey@;
    let ghost cc_suppkey = c_suppkey.codes@;
    let pp_8 = u32::into_part(c_suppkey.codes);
    let pp_9 = OwnedPart::I64(b_suppkey);
    let b_linenumber = bases_i64(&c_linenumber.bases);
    let ghost bb_linenumber = b_linenumber@;
    let ghost cc_linenumber = c_linenumber.codes@;
    let pp_10 = u8::into_part(c_linenumber.codes);
    let pp_11 = OwnedPart::I64(b_linenumber);
    let b_quantity = bases_i64(&c_quantity.bases);
    let ghost bb_quantity = b_quantity@;
    let ghost cc_quantity = c_quantity.codes@;
    let pp_12 = u16::into_part(c_quantity.codes);
    let pp_13 = OwnedPart::I64(b_quantity);
    let b_extendedprice = bases_i64(&c_extendedprice.bases);
    let ghost bb_extendedprice = b_extendedprice@;
    let ghost cc_extendedprice = c_extendedprice.codes@;
    let pp_14 = u32::into_part(c_extendedprice.codes);
    let pp_15 = OwnedPart::I64(b_extendedprice);
    let b_discount = bases_i64(&c_discount.bases);
    let ghost bb_discount = b_discount@;
    let ghost cc_discount = c_discount.codes@;
    let pp_16 = u8::into_part(c_discount.codes);
    let pp_17 = OwnedPart::I64(b_discount);
    let b_tax = bases_i64(&c_tax.bases);
    let ghost bb_tax = b_tax@;
    let ghost cc_tax = c_tax.codes@;
    let pp_18 = u8::into_part(c_tax.codes);
    let pp_19 = OwnedPart::I64(b_tax);
    let b_returnflag = bases_u64(&c_returnflag.bases);
    let ghost cc_returnflag = c_returnflag.codes@;
    let pp_20 = u8::into_part(c_returnflag.codes);
    let pp_21 = OwnedPart::U64(b_returnflag);
    let pp_22 = OwnedPart::U64(copy_u64s(&d_returnflag.offs));
    let pp_23 = OwnedPart::U8(copy_u8s(&d_returnflag.bytes));
    let b_linestatus = bases_u64(&c_linestatus.bases);
    let ghost cc_linestatus = c_linestatus.codes@;
    let pp_24 = u8::into_part(c_linestatus.codes);
    let pp_25 = OwnedPart::U64(b_linestatus);
    let pp_26 = OwnedPart::U64(copy_u64s(&d_linestatus.offs));
    let pp_27 = OwnedPart::U8(copy_u8s(&d_linestatus.bytes));
    let b_shipdate = bases_i64(&c_shipdate.bases);
    let ghost bb_shipdate = b_shipdate@;
    let z_shipdate = bases_i64(&c_shipdate.zmax);
    let ghost cc_shipdate = c_shipdate.codes@;
    let pp_28 = u16::into_part(c_shipdate.codes);
    let pp_29 = OwnedPart::I64(b_shipdate);
    let ghost zz_shipdate = z_shipdate@;
    let pp_30 = OwnedPart::I64(z_shipdate);
    let b_commitdate = bases_i64(&c_commitdate.bases);
    let ghost bb_commitdate = b_commitdate@;
    let z_commitdate = bases_i64(&c_commitdate.zmax);
    let ghost cc_commitdate = c_commitdate.codes@;
    let pp_31 = u16::into_part(c_commitdate.codes);
    let pp_32 = OwnedPart::I64(b_commitdate);
    let ghost zz_commitdate = z_commitdate@;
    let pp_33 = OwnedPart::I64(z_commitdate);
    let b_receiptdate = bases_i64(&c_receiptdate.bases);
    let ghost bb_receiptdate = b_receiptdate@;
    let z_receiptdate = bases_i64(&c_receiptdate.zmax);
    let ghost cc_receiptdate = c_receiptdate.codes@;
    let pp_34 = u16::into_part(c_receiptdate.codes);
    let pp_35 = OwnedPart::I64(b_receiptdate);
    let ghost zz_receiptdate = z_receiptdate@;
    let pp_36 = OwnedPart::I64(z_receiptdate);
    let b_shipinstruct = bases_u64(&c_shipinstruct.bases);
    let ghost cc_shipinstruct = c_shipinstruct.codes@;
    let pp_37 = u8::into_part(c_shipinstruct.codes);
    let pp_38 = OwnedPart::U64(b_shipinstruct);
    let pp_39 = OwnedPart::U64(copy_u64s(&d_shipinstruct.offs));
    let pp_40 = OwnedPart::U8(copy_u8s(&d_shipinstruct.bytes));
    let b_shipmode = bases_u64(&c_shipmode.bases);
    let ghost cc_shipmode = c_shipmode.codes@;
    let pp_41 = u8::into_part(c_shipmode.codes);
    let pp_42 = OwnedPart::U64(b_shipmode);
    let pp_43 = OwnedPart::U64(copy_u64s(&d_shipmode.offs));
    let pp_44 = OwnedPart::U8(copy_u8s(&d_shipmode.bytes));
    let ghost kcs = cc_partkey;
    let ghost kbs = bb_partkey;
    proof {
        lemma_fkey_col(c_partkey, src_partkey, rm, kbs, n as int, bsize as int);
    }
    let (kic, kib, key_kind) = match build_keyidx_sortperm(src.t0_f1, &rmv, n, bsize, Ghost(kcs), Ghost(kbs), workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    let ghost kic_v = kic@;
    let ghost kib_v = kib@;
    let pp_45 = OwnedPart::U32(kic);
    let pp_46 = OwnedPart::U64(kib);
    let pp_47 = OwnedPart::U64(vec![key_kind]);
    let parts = assemble_lineitem(pp_0, pp_1, pp_2, pp_3, pp_4, pp_5, pp_6, pp_7, pp_8, pp_9, pp_10, pp_11, pp_12, pp_13, pp_14, pp_15, pp_16, pp_17, pp_18, pp_19, pp_20, pp_21, pp_22, pp_23, pp_24, pp_25, pp_26, pp_27, pp_28, pp_29, pp_30, pp_31, pp_32, pp_33, pp_34, pp_35, pp_36, pp_37, pp_38, pp_39, pp_40, pp_41, pp_42, pp_43, pp_44, pp_45, pp_46, pp_47);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == LI_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 15));
        assert(tp[LI_PERM_CODES as int] == u32::part_of(cc_perm));
        lemma_for_decode(tp, LI_GROUPS as int, LI_PERM_CODES as int, LI_PERM_BASE as int, c_perm, src_perm, rm, n as int, bsize as int);
        lemma_perm_col(tp, LI_GROUPS as int, LI_PERM_CODES as int, LI_PERM_BASE as int, n as int, rmv@);
        assert(lineitem_map(tp, n as int) == map_view(rmv@));
        assert(lineitem_rows(tp, rel) == rows);
        assert(tp[LI_ORDERKEY_CODES as int] == u32::part_of(cc_orderkey));
        lemma_for_decode(tp, LI_GROUPS as int, LI_ORDERKEY_CODES as int, LI_ORDERKEY_BASE as int, c_orderkey, src_orderkey, rm, n as int, bsize as int);
        lemma_int_col(tp, LI_GROUPS as int, LI_ORDERKEY_CODES as int, LI_ORDERKEY_BASE as int, rows, 0, src_orderkey, rm);
        assert(tp[LI_PARTKEY_CODES as int] == u32::part_of(cc_partkey));
        lemma_for_decode(tp, LI_GROUPS as int, LI_PARTKEY_CODES as int, LI_PARTKEY_BASE as int, c_partkey, src_partkey, rm, n as int, bsize as int);
        lemma_int_col(tp, LI_GROUPS as int, LI_PARTKEY_CODES as int, LI_PARTKEY_BASE as int, rows, 1, src_partkey, rm);
        assert(tp[LI_SUPPKEY_CODES as int] == u32::part_of(cc_suppkey));
        lemma_for_decode(tp, LI_GROUPS as int, LI_SUPPKEY_CODES as int, LI_SUPPKEY_BASE as int, c_suppkey, src_suppkey, rm, n as int, bsize as int);
        lemma_int_col(tp, LI_GROUPS as int, LI_SUPPKEY_CODES as int, LI_SUPPKEY_BASE as int, rows, 2, src_suppkey, rm);
        assert(tp[LI_LINENUMBER_CODES as int] == u8::part_of(cc_linenumber));
        lemma_for_decode(tp, LI_GROUPS as int, LI_LINENUMBER_CODES as int, LI_LINENUMBER_BASE as int, c_linenumber, src_linenumber, rm, n as int, bsize as int);
        lemma_int_col(tp, LI_GROUPS as int, LI_LINENUMBER_CODES as int, LI_LINENUMBER_BASE as int, rows, 3, src_linenumber, rm);
        assert(tp[LI_QUANTITY_CODES as int] == u16::part_of(cc_quantity));
        lemma_for_decode(tp, LI_GROUPS as int, LI_QUANTITY_CODES as int, LI_QUANTITY_BASE as int, c_quantity, src_quantity, rm, n as int, bsize as int);
        lemma_num_col(tp, LI_GROUPS as int, LI_QUANTITY_CODES as int, LI_QUANTITY_BASE as int, rows, 4, 2, src_quantity, rm);
        assert(tp[LI_EXTENDEDPRICE_CODES as int] == u32::part_of(cc_extendedprice));
        lemma_for_decode(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, c_extendedprice, src_extendedprice, rm, n as int, bsize as int);
        lemma_num_col(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, rows, 5, 2, src_extendedprice, rm);
        assert(tp[LI_DISCOUNT_CODES as int] == u8::part_of(cc_discount));
        lemma_for_decode(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, c_discount, src_discount, rm, n as int, bsize as int);
        lemma_num_col(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, rows, 6, 2, src_discount, rm);
        assert(tp[LI_TAX_CODES as int] == u8::part_of(cc_tax));
        lemma_for_decode(tp, LI_GROUPS as int, LI_TAX_CODES as int, LI_TAX_BASE as int, c_tax, src_tax, rm, n as int, bsize as int);
        lemma_num_col(tp, LI_GROUPS as int, LI_TAX_CODES as int, LI_TAX_BASE as int, rows, 7, 2, src_tax, rm);
        assert(tp[LI_RETURNFLAG_CODES as int] == u8::part_of(cc_returnflag));
        lemma_for_decode(tp, LI_GROUPS as int, LI_RETURNFLAG_CODES as int, LI_RETURNFLAG_BASE as int, c_returnflag, src_returnflag, rm, n as int, bsize as int);
        lemma_dict_col(tp, LI_GROUPS as int, LI_RETURNFLAG_CODES as int, LI_RETURNFLAG_BASE as int, LI_RETURNFLAG_DICT_OFFS as int, LI_RETURNFLAG_DICT_BYTES as int, rows, 8, src@.t0_f8, &d_returnflag, rm, n as int);
        assert(tp[LI_LINESTATUS_CODES as int] == u8::part_of(cc_linestatus));
        lemma_for_decode(tp, LI_GROUPS as int, LI_LINESTATUS_CODES as int, LI_LINESTATUS_BASE as int, c_linestatus, src_linestatus, rm, n as int, bsize as int);
        lemma_dict_col(tp, LI_GROUPS as int, LI_LINESTATUS_CODES as int, LI_LINESTATUS_BASE as int, LI_LINESTATUS_DICT_OFFS as int, LI_LINESTATUS_DICT_BYTES as int, rows, 9, src@.t0_f9, &d_linestatus, rm, n as int);
        assert(tp[LI_SHIPDATE_CODES as int] == u16::part_of(cc_shipdate));
        lemma_for_decode(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, c_shipdate, src_shipdate, rm, n as int, bsize as int);
        lemma_date_col(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, rows, 10, src_shipdate, rm);
        lemma_zone(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, LI_SHIPDATE_ZMAX as int, c_shipdate, src_shipdate, rm, n as int, bsize as int, zz_shipdate);
        assert(tp[LI_COMMITDATE_CODES as int] == u16::part_of(cc_commitdate));
        lemma_for_decode(tp, LI_GROUPS as int, LI_COMMITDATE_CODES as int, LI_COMMITDATE_BASE as int, c_commitdate, src_commitdate, rm, n as int, bsize as int);
        lemma_date_col(tp, LI_GROUPS as int, LI_COMMITDATE_CODES as int, LI_COMMITDATE_BASE as int, rows, 11, src_commitdate, rm);
        lemma_zone(tp, LI_GROUPS as int, LI_COMMITDATE_CODES as int, LI_COMMITDATE_BASE as int, LI_COMMITDATE_ZMAX as int, c_commitdate, src_commitdate, rm, n as int, bsize as int, zz_commitdate);
        assert(tp[LI_RECEIPTDATE_CODES as int] == u16::part_of(cc_receiptdate));
        lemma_for_decode(tp, LI_GROUPS as int, LI_RECEIPTDATE_CODES as int, LI_RECEIPTDATE_BASE as int, c_receiptdate, src_receiptdate, rm, n as int, bsize as int);
        lemma_date_col(tp, LI_GROUPS as int, LI_RECEIPTDATE_CODES as int, LI_RECEIPTDATE_BASE as int, rows, 12, src_receiptdate, rm);
        lemma_zone(tp, LI_GROUPS as int, LI_RECEIPTDATE_CODES as int, LI_RECEIPTDATE_BASE as int, LI_RECEIPTDATE_ZMAX as int, c_receiptdate, src_receiptdate, rm, n as int, bsize as int, zz_receiptdate);
        assert(tp[LI_SHIPINSTRUCT_CODES as int] == u8::part_of(cc_shipinstruct));
        lemma_for_decode(tp, LI_GROUPS as int, LI_SHIPINSTRUCT_CODES as int, LI_SHIPINSTRUCT_BASE as int, c_shipinstruct, src_shipinstruct, rm, n as int, bsize as int);
        lemma_dict_col(tp, LI_GROUPS as int, LI_SHIPINSTRUCT_CODES as int, LI_SHIPINSTRUCT_BASE as int, LI_SHIPINSTRUCT_DICT_OFFS as int, LI_SHIPINSTRUCT_DICT_BYTES as int, rows, 13, src@.t0_f13, &d_shipinstruct, rm, n as int);
        assert(tp[LI_SHIPMODE_CODES as int] == u8::part_of(cc_shipmode));
        lemma_for_decode(tp, LI_GROUPS as int, LI_SHIPMODE_CODES as int, LI_SHIPMODE_BASE as int, c_shipmode, src_shipmode, rm, n as int, bsize as int);
        lemma_dict_col(tp, LI_GROUPS as int, LI_SHIPMODE_CODES as int, LI_SHIPMODE_BASE as int, LI_SHIPMODE_DICT_OFFS as int, LI_SHIPMODE_DICT_BYTES as int, rows, 14, src@.t0_f14, &d_shipmode, rm, n as int);
        assert(u64s(tp[LI_KEYIDX_KIND as int]) =~= seq![key_kind]);
        assert(u32s(tp[LI_PARTKEY_CODES as int]) == kcs);
        assert(i64s(tp[LI_PARTKEY_BASE as int]) == kbs);
        assert(tp[LI_KEYIDX_CODES as int] == PartView::U32(kic_v));
        assert(tp[LI_KEYIDX_BASE as int] == PartView::U64(kib_v));
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
        v.t1_f2.offsets.len() == source_rows_t1(v) + 1,
        v.t1_f0.len() == source_rows_t1(v),
        v.t1_f1.len() == source_rows_t1(v),
        twf(v.t1_f2, source_rows_t1(v)),
        v.t1_f3.len() == source_rows_t1(v),
        v.t1_f4.len() == source_rows_t1(v),
        twf(v.t1_f5, source_rows_t1(v)),
        v.t1_f6.len() == source_rows_t1(v),
        forall|i: int| 0 <= i < v.t1_f3.len() ==> -num15_bound() < #[trigger] v.t1_f3[i] < num15_bound(),
{
    reveal(src_ok);
    reveal(twf);
    lemma_num15(table_t1(v), source_columns_t1(), 3, v.t1_f3);
}

/// The FOR columns of table orders, encoded over blocks of `bsize` stored rows (`None`: some block does not fit).
fn encode_orders(src_perm: &ValSrc, src_orderkey: &ValSrc, src_custkey: &ValSrc, src_orderstatus: &ValSrc, src_totalprice: &ValSrc, src_orderdate: &ValSrc, src_orderpriority: &ValSrc, src_shippriority: &ValSrc, rm: &RowMap, n: usize, bsize: usize, zb_orderstatus: bool, zb_orderpriority: bool, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<(ForCol<u32>, ForCol<u32>, ForCol<u32>, ForCol<u8>, ForCol<u32>, ForCol<u16>, ForCol<u8>, ForCol<u8>,)>, QueryError>)
    requires
        src_wf(*src_perm, n as int),
        src_wf(*src_orderkey, n as int),
        src_wf(*src_custkey, n as int),
        src_wf(*src_orderstatus, n as int),
        src_wf(*src_totalprice, n as int),
        src_wf(*src_orderdate, n as int),
        src_wf(*src_orderpriority, n as int),
        src_wf(*src_shippriority, n as int),
        zb_orderstatus ==> fits_zero_base::<u8>(*src_orderstatus, n as int),
        zb_orderpriority ==> fits_zero_base::<u8>(*src_orderpriority, n as int),
        rm_wf(*rm, n as int),
        1 <= bsize,
        n + bsize <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> for_col_ok(t.0, *src_perm, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.1, *src_orderkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.2, *src_custkey, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.3, *src_orderstatus, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.4, *src_totalprice, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.5, *src_orderdate, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.6, *src_orderpriority, *rm, n as int, bsize as int),
        r matches Ok(Some(t)) ==> for_col_ok(t.7, *src_shippriority, *rm, n as int, bsize as int),
        r matches Ok(None) ==> bsize != 1,
        r matches Err(e) ==> e is WorkerFailed,
{
    let c_perm = match encode_column::<u32>(src_perm, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_orderkey = match encode_column::<u32>(src_orderkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_custkey = match encode_column::<u32>(src_custkey, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_orderstatus = match encode_column::<u8>(src_orderstatus, rm, n, bsize, zb_orderstatus, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_totalprice = match encode_column::<u32>(src_totalprice, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_orderdate = match encode_column::<u16>(src_orderdate, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_orderpriority = match encode_column::<u8>(src_orderpriority, rm, n, bsize, zb_orderpriority, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let c_shippriority = match encode_column::<u8>(src_shippriority, rm, n, bsize, false, workers, dispatch) {
        Ok(Some(c)) => c,
        Ok(None) => return Ok(None),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(Some((c_perm, c_orderkey, c_custkey, c_orderstatus, c_totalprice, c_orderdate, c_orderpriority, c_shippriority,)))
}

/// The parts of table orders (clustered order `rmv` (stored row -> canonical row)).
fn build_orders(src: &SourceRef, rmv: Arc<Vec<u64>>, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        src_ok(src@),
        1 <= workers <= MAX_WORKERS,
        rmv@.len() == table_t1(src@).len(),
        is_perm(map_view(rmv@), table_t1(src@).len() as int),
    ensures
        r matches Ok(v) ==> orders_ok(owned_parts_view(v@), table_t1(src@)),
        r matches Ok(v) ==> orders_map(owned_parts_view(v@), table_t1(src@).len() as int) == map_view(rmv@),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost rel = table_t1(src@);
    proof {
        lemma_src_orders(src@);
        vstd::slice::axiom_spec_len(src.t1_f2.offsets);
    }
    let n = src.t1_f0.len();
    proof {
        lemma_map_rm(rmv, n as int);
    }
    let bsize0 = block_rows_for(n);
    let rm = RowMap::Map(rmv.clone());
    let ghost rows = stored_rows(rel, map_view(rmv@));
    let d_orderstatus = Arc::new(build_dict(&src.t1_f2, n));
    let zb_orderstatus = d_orderstatus.offs.len() - 1 <= 255;
    let d_orderpriority = Arc::new(build_dict(&src.t1_f5, n));
    let zb_orderpriority = d_orderpriority.offs.len() - 1 <= 255;
    let src_perm = ValSrc::Pos;
    let src_orderkey = ValSrc::Int(src.t1_f0);
    let src_custkey = ValSrc::Int(src.t1_f1);
    let src_orderstatus = ValSrc::Dict(TextCol { offsets: src.t1_f2.offsets, bytes: src.t1_f2.bytes }, d_orderstatus.clone());
    let src_totalprice = ValSrc::Num(src.t1_f3);
    let src_orderdate = ValSrc::Date(src.t1_f4);
    let src_orderpriority = ValSrc::Dict(TextCol { offsets: src.t1_f5.offsets, bytes: src.t1_f5.bytes }, d_orderpriority.clone());
    let src_shippriority = ValSrc::Int(src.t1_f6);
    proof {
        if zb_orderstatus {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_orderstatus, i) <= u8::cap() by {
                lemma_dict_src_bound(src_orderstatus, n as int, i);
            }
        }
        if zb_orderpriority {
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] src_val(src_orderpriority, i) <= u8::cap() by {
                lemma_dict_src_bound(src_orderpriority, n as int, i);
            }
        }
    }
    let (bsize, (c_perm, c_orderkey, c_custkey, c_orderstatus, c_totalprice, c_orderdate, c_orderpriority, c_shippriority,)) = match encode_orders(&src_perm, &src_orderkey, &src_custkey, &src_orderstatus, &src_totalprice, &src_orderdate, &src_orderpriority, &src_shippriority, &rm, n, bsize0, zb_orderstatus, zb_orderpriority, workers, dispatch) {
        Ok(Some(cols)) => (bsize0, cols),
        Ok(None) => match encode_orders(&src_perm, &src_orderkey, &src_custkey, &src_orderstatus, &src_totalprice, &src_orderdate, &src_orderpriority, &src_shippriority, &rm, n, 1, zb_orderstatus, zb_orderpriority, workers, dispatch) {
            Ok(Some(cols)) => (1, cols),
            Ok(None) => { proof { assert(false); } return Err(QueryError::Malformed); }
            Err(e) => return Err(e),
        },
        Err(e) => return Err(e),
    };
    proof {
        lemma_col_ranges(c_perm, src_perm, rm, n as int, bsize as int);
        lemma_col_ranges(c_orderkey, src_orderkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_custkey, src_custkey, rm, n as int, bsize as int);
        lemma_col_ranges(c_orderstatus, src_orderstatus, rm, n as int, bsize as int);
        lemma_col_ranges(c_totalprice, src_totalprice, rm, n as int, bsize as int);
        lemma_col_ranges(c_orderdate, src_orderdate, rm, n as int, bsize as int);
        lemma_col_ranges(c_orderpriority, src_orderpriority, rm, n as int, bsize as int);
        lemma_col_ranges(c_shippriority, src_shippriority, rm, n as int, bsize as int);
    }
    let pp_0 = OwnedPart::U64(vec![n as u64, bsize as u64]);
    let pp_1 = groups_part(n, bsize);
    let b_perm = bases_u64(&c_perm.bases);
    let ghost cc_perm = c_perm.codes@;
    let pp_2 = u32::into_part(c_perm.codes);
    let pp_3 = OwnedPart::U64(b_perm);
    let b_orderkey = bases_i64(&c_orderkey.bases);
    let ghost bb_orderkey = b_orderkey@;
    let ghost cc_orderkey = c_orderkey.codes@;
    let pp_4 = u32::into_part(c_orderkey.codes);
    let pp_5 = OwnedPart::I64(b_orderkey);
    let b_custkey = bases_i64(&c_custkey.bases);
    let ghost bb_custkey = b_custkey@;
    let ghost cc_custkey = c_custkey.codes@;
    let pp_6 = u32::into_part(c_custkey.codes);
    let pp_7 = OwnedPart::I64(b_custkey);
    let b_orderstatus = bases_u64(&c_orderstatus.bases);
    let ghost cc_orderstatus = c_orderstatus.codes@;
    let pp_8 = u8::into_part(c_orderstatus.codes);
    let pp_9 = OwnedPart::U64(b_orderstatus);
    let pp_10 = OwnedPart::U64(copy_u64s(&d_orderstatus.offs));
    let pp_11 = OwnedPart::U8(copy_u8s(&d_orderstatus.bytes));
    let b_totalprice = bases_i64(&c_totalprice.bases);
    let ghost bb_totalprice = b_totalprice@;
    let ghost cc_totalprice = c_totalprice.codes@;
    let pp_12 = u32::into_part(c_totalprice.codes);
    let pp_13 = OwnedPart::I64(b_totalprice);
    let b_orderdate = bases_i64(&c_orderdate.bases);
    let ghost bb_orderdate = b_orderdate@;
    let z_orderdate = bases_i64(&c_orderdate.zmax);
    let ghost cc_orderdate = c_orderdate.codes@;
    let pp_14 = u16::into_part(c_orderdate.codes);
    let pp_15 = OwnedPart::I64(b_orderdate);
    let ghost zz_orderdate = z_orderdate@;
    let pp_16 = OwnedPart::I64(z_orderdate);
    let b_orderpriority = bases_u64(&c_orderpriority.bases);
    let ghost cc_orderpriority = c_orderpriority.codes@;
    let pp_17 = u8::into_part(c_orderpriority.codes);
    let pp_18 = OwnedPart::U64(b_orderpriority);
    let pp_19 = OwnedPart::U64(copy_u64s(&d_orderpriority.offs));
    let pp_20 = OwnedPart::U8(copy_u8s(&d_orderpriority.bytes));
    let b_shippriority = bases_i64(&c_shippriority.bases);
    let ghost bb_shippriority = b_shippriority@;
    let ghost cc_shippriority = c_shippriority.codes@;
    let pp_21 = u8::into_part(c_shippriority.codes);
    let pp_22 = OwnedPart::I64(b_shippriority);
    let ghost kcs = cc_orderkey;
    let ghost kbs = bb_orderkey;
    proof {
        lemma_fkey_col(c_orderkey, src_orderkey, rm, kbs, n as int, bsize as int);
    }
    let (kic, kib, key_kind) = match build_keyidx_perm(src.t1_f0, &rmv, n, bsize, Ghost(kcs), Ghost(kbs), workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    let ghost kic_v = kic@;
    let ghost kib_v = kib@;
    let pp_23 = OwnedPart::U32(kic);
    let pp_24 = OwnedPart::U64(kib);
    let pp_25 = OwnedPart::U64(vec![key_kind]);
    let parts = assemble_orders(pp_0, pp_1, pp_2, pp_3, pp_4, pp_5, pp_6, pp_7, pp_8, pp_9, pp_10, pp_11, pp_12, pp_13, pp_14, pp_15, pp_16, pp_17, pp_18, pp_19, pp_20, pp_21, pp_22, pp_23, pp_24, pp_25);
    proof {
        let tp = owned_parts_view(parts@);
        assert(tp.len() == OR_PARTS);
        assert(rel.len() == n);
        assert(tp[0] == PartView::U64(seq![n as u64, bsize as u64]));
        assert(u64s(tp[0]) =~= seq![n as u64, bsize as u64]);
        assert(table_layout_ok(tp, n as int));
        assert(rows_width(rel, 7));
        assert(tp[OR_PERM_CODES as int] == u32::part_of(cc_perm));
        lemma_for_decode(tp, OR_GROUPS as int, OR_PERM_CODES as int, OR_PERM_BASE as int, c_perm, src_perm, rm, n as int, bsize as int);
        lemma_perm_col(tp, OR_GROUPS as int, OR_PERM_CODES as int, OR_PERM_BASE as int, n as int, rmv@);
        assert(orders_map(tp, n as int) == map_view(rmv@));
        assert(orders_rows(tp, rel) == rows);
        assert(tp[OR_ORDERKEY_CODES as int] == u32::part_of(cc_orderkey));
        lemma_for_decode(tp, OR_GROUPS as int, OR_ORDERKEY_CODES as int, OR_ORDERKEY_BASE as int, c_orderkey, src_orderkey, rm, n as int, bsize as int);
        lemma_int_col(tp, OR_GROUPS as int, OR_ORDERKEY_CODES as int, OR_ORDERKEY_BASE as int, rows, 0, src_orderkey, rm);
        assert(tp[OR_CUSTKEY_CODES as int] == u32::part_of(cc_custkey));
        lemma_for_decode(tp, OR_GROUPS as int, OR_CUSTKEY_CODES as int, OR_CUSTKEY_BASE as int, c_custkey, src_custkey, rm, n as int, bsize as int);
        lemma_int_col(tp, OR_GROUPS as int, OR_CUSTKEY_CODES as int, OR_CUSTKEY_BASE as int, rows, 1, src_custkey, rm);
        assert(tp[OR_ORDERSTATUS_CODES as int] == u8::part_of(cc_orderstatus));
        lemma_for_decode(tp, OR_GROUPS as int, OR_ORDERSTATUS_CODES as int, OR_ORDERSTATUS_BASE as int, c_orderstatus, src_orderstatus, rm, n as int, bsize as int);
        lemma_dict_col(tp, OR_GROUPS as int, OR_ORDERSTATUS_CODES as int, OR_ORDERSTATUS_BASE as int, OR_ORDERSTATUS_DICT_OFFS as int, OR_ORDERSTATUS_DICT_BYTES as int, rows, 2, src@.t1_f2, &d_orderstatus, rm, n as int);
        assert(tp[OR_TOTALPRICE_CODES as int] == u32::part_of(cc_totalprice));
        lemma_for_decode(tp, OR_GROUPS as int, OR_TOTALPRICE_CODES as int, OR_TOTALPRICE_BASE as int, c_totalprice, src_totalprice, rm, n as int, bsize as int);
        lemma_num_col(tp, OR_GROUPS as int, OR_TOTALPRICE_CODES as int, OR_TOTALPRICE_BASE as int, rows, 3, 2, src_totalprice, rm);
        assert(tp[OR_ORDERDATE_CODES as int] == u16::part_of(cc_orderdate));
        lemma_for_decode(tp, OR_GROUPS as int, OR_ORDERDATE_CODES as int, OR_ORDERDATE_BASE as int, c_orderdate, src_orderdate, rm, n as int, bsize as int);
        lemma_date_col(tp, OR_GROUPS as int, OR_ORDERDATE_CODES as int, OR_ORDERDATE_BASE as int, rows, 4, src_orderdate, rm);
        lemma_zone(tp, OR_GROUPS as int, OR_ORDERDATE_CODES as int, OR_ORDERDATE_BASE as int, OR_ORDERDATE_ZMAX as int, c_orderdate, src_orderdate, rm, n as int, bsize as int, zz_orderdate);
        assert(tp[OR_ORDERPRIORITY_CODES as int] == u8::part_of(cc_orderpriority));
        lemma_for_decode(tp, OR_GROUPS as int, OR_ORDERPRIORITY_CODES as int, OR_ORDERPRIORITY_BASE as int, c_orderpriority, src_orderpriority, rm, n as int, bsize as int);
        lemma_dict_col(tp, OR_GROUPS as int, OR_ORDERPRIORITY_CODES as int, OR_ORDERPRIORITY_BASE as int, OR_ORDERPRIORITY_DICT_OFFS as int, OR_ORDERPRIORITY_DICT_BYTES as int, rows, 5, src@.t1_f5, &d_orderpriority, rm, n as int);
        assert(tp[OR_SHIPPRIORITY_CODES as int] == u8::part_of(cc_shippriority));
        lemma_for_decode(tp, OR_GROUPS as int, OR_SHIPPRIORITY_CODES as int, OR_SHIPPRIORITY_BASE as int, c_shippriority, src_shippriority, rm, n as int, bsize as int);
        lemma_int_col(tp, OR_GROUPS as int, OR_SHIPPRIORITY_CODES as int, OR_SHIPPRIORITY_BASE as int, rows, 6, src_shippriority, rm);
        assert(u64s(tp[OR_KEYIDX_KIND as int]) =~= seq![key_kind]);
        assert(u32s(tp[OR_ORDERKEY_CODES as int]) == kcs);
        assert(i64s(tp[OR_ORDERKEY_BASE as int]) == kbs);
        assert(tp[OR_KEYIDX_CODES as int] == PartView::U32(kic_v));
        assert(tp[OR_KEYIDX_BASE as int] == PartView::U64(kib_v));
        if key_kind == 2 {
            assert forall|r: int| 0 <= r < n implies #[trigger] orders_map(tp, n as int)[fidx(kic_v, kib_v, bsize as int, r)] == r by {
                assert(idx_map(kic_v, kib_v, bsize as int, n as int)[r] == fidx(kic_v, kib_v, bsize as int, r));
                assert(0 <= idx_map(kic_v, kib_v, bsize as int, n as int)[r] < n);
                assert(map_view(rmv@)[fidx(kic_v, kib_v, bsize as int, r)] == rmv@[fidx(kic_v, kib_v, bsize as int, r)] as int);
            }
        }
    }
    Ok(parts)
}

/// Parts 0 .. 11 of table lineitem, in order.
fn assemble_lineitem_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart) -> (v: Vec<OwnedPart>)
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

/// Parts 12 .. 23 of table lineitem, in order.
fn assemble_lineitem_1(p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart, p17: OwnedPart, p18: OwnedPart, p19: OwnedPart, p20: OwnedPart, p21: OwnedPart, p22: OwnedPart, p23: OwnedPart) -> (v: Vec<OwnedPart>)
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

/// Parts 24 .. 35 of table lineitem, in order.
fn assemble_lineitem_2(p24: OwnedPart, p25: OwnedPart, p26: OwnedPart, p27: OwnedPart, p28: OwnedPart, p29: OwnedPart, p30: OwnedPart, p31: OwnedPart, p32: OwnedPart, p33: OwnedPart, p34: OwnedPart, p35: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 12,
        v@[0] == p24,
        v@[1] == p25,
        v@[2] == p26,
        v@[3] == p27,
        v@[4] == p28,
        v@[5] == p29,
        v@[6] == p30,
        v@[7] == p31,
        v@[8] == p32,
        v@[9] == p33,
        v@[10] == p34,
        v@[11] == p35,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(12);
    v.push(p24);
    v.push(p25);
    v.push(p26);
    v.push(p27);
    v.push(p28);
    v.push(p29);
    v.push(p30);
    v.push(p31);
    v.push(p32);
    v.push(p33);
    v.push(p34);
    v.push(p35);
    v
}

/// Parts 36 .. 47 of table lineitem, in order.
fn assemble_lineitem_3(p36: OwnedPart, p37: OwnedPart, p38: OwnedPart, p39: OwnedPart, p40: OwnedPart, p41: OwnedPart, p42: OwnedPart, p43: OwnedPart, p44: OwnedPart, p45: OwnedPart, p46: OwnedPart, p47: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 12,
        v@[0] == p36,
        v@[1] == p37,
        v@[2] == p38,
        v@[3] == p39,
        v@[4] == p40,
        v@[5] == p41,
        v@[6] == p42,
        v@[7] == p43,
        v@[8] == p44,
        v@[9] == p45,
        v@[10] == p46,
        v@[11] == p47,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(12);
    v.push(p36);
    v.push(p37);
    v.push(p38);
    v.push(p39);
    v.push(p40);
    v.push(p41);
    v.push(p42);
    v.push(p43);
    v.push(p44);
    v.push(p45);
    v.push(p46);
    v.push(p47);
    v
}

/// The 48 parts of table lineitem, in order (each named by index in the postcondition).
fn assemble_lineitem(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart, p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart, p17: OwnedPart, p18: OwnedPart, p19: OwnedPart, p20: OwnedPart, p21: OwnedPart, p22: OwnedPart, p23: OwnedPart, p24: OwnedPart, p25: OwnedPart, p26: OwnedPart, p27: OwnedPart, p28: OwnedPart, p29: OwnedPart, p30: OwnedPart, p31: OwnedPart, p32: OwnedPart, p33: OwnedPart, p34: OwnedPart, p35: OwnedPart, p36: OwnedPart, p37: OwnedPart, p38: OwnedPart, p39: OwnedPart, p40: OwnedPart, p41: OwnedPart, p42: OwnedPart, p43: OwnedPart, p44: OwnedPart, p45: OwnedPart, p46: OwnedPart, p47: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 48,
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
        v@[29] == p29,
        v@[30] == p30,
        v@[31] == p31,
        v@[32] == p32,
        v@[33] == p33,
        v@[34] == p34,
        v@[35] == p35,
        v@[36] == p36,
        v@[37] == p37,
        v@[38] == p38,
        v@[39] == p39,
        v@[40] == p40,
        v@[41] == p41,
        v@[42] == p42,
        v@[43] == p43,
        v@[44] == p44,
        v@[45] == p45,
        v@[46] == p46,
        v@[47] == p47,
{
    let mut c0 = assemble_lineitem_0(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11);
    let mut c1 = assemble_lineitem_1(p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23);
    let mut c2 = assemble_lineitem_2(p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35);
    let mut c3 = assemble_lineitem_3(p36, p37, p38, p39, p40, p41, p42, p43, p44, p45, p46, p47);
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
    assert(v@.len() == 36);
    proof {
        assert(v@[24] == p24);
        assert(v@[25] == p25);
        assert(v@[26] == p26);
        assert(v@[27] == p27);
        assert(v@[28] == p28);
        assert(v@[29] == p29);
        assert(v@[30] == p30);
        assert(v@[31] == p31);
        assert(v@[32] == p32);
        assert(v@[33] == p33);
        assert(v@[34] == p34);
        assert(v@[35] == p35);
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
    let ghost before_3 = v@;
    v.append(&mut c3);
    assert(v@.len() == 48);
    proof {
        assert(v@[36] == p36);
        assert(v@[37] == p37);
        assert(v@[38] == p38);
        assert(v@[39] == p39);
        assert(v@[40] == p40);
        assert(v@[41] == p41);
        assert(v@[42] == p42);
        assert(v@[43] == p43);
        assert(v@[44] == p44);
        assert(v@[45] == p45);
        assert(v@[46] == p46);
        assert(v@[47] == p47);
        assert(v@[0] == before_3[0]);
        assert(v@[1] == before_3[1]);
        assert(v@[2] == before_3[2]);
        assert(v@[3] == before_3[3]);
        assert(v@[4] == before_3[4]);
        assert(v@[5] == before_3[5]);
        assert(v@[6] == before_3[6]);
        assert(v@[7] == before_3[7]);
        assert(v@[8] == before_3[8]);
        assert(v@[9] == before_3[9]);
        assert(v@[10] == before_3[10]);
        assert(v@[11] == before_3[11]);
        assert(v@[12] == before_3[12]);
        assert(v@[13] == before_3[13]);
        assert(v@[14] == before_3[14]);
        assert(v@[15] == before_3[15]);
        assert(v@[16] == before_3[16]);
        assert(v@[17] == before_3[17]);
        assert(v@[18] == before_3[18]);
        assert(v@[19] == before_3[19]);
        assert(v@[20] == before_3[20]);
        assert(v@[21] == before_3[21]);
        assert(v@[22] == before_3[22]);
        assert(v@[23] == before_3[23]);
        assert(v@[24] == before_3[24]);
        assert(v@[25] == before_3[25]);
        assert(v@[26] == before_3[26]);
        assert(v@[27] == before_3[27]);
        assert(v@[28] == before_3[28]);
        assert(v@[29] == before_3[29]);
        assert(v@[30] == before_3[30]);
        assert(v@[31] == before_3[31]);
        assert(v@[32] == before_3[32]);
        assert(v@[33] == before_3[33]);
        assert(v@[34] == before_3[34]);
        assert(v@[35] == before_3[35]);
    }
    v
}

/// Parts 0 .. 11 of table orders, in order.
fn assemble_orders_0(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart) -> (v: Vec<OwnedPart>)
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

/// Parts 12 .. 23 of table orders, in order.
fn assemble_orders_1(p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart, p17: OwnedPart, p18: OwnedPart, p19: OwnedPart, p20: OwnedPart, p21: OwnedPart, p22: OwnedPart, p23: OwnedPart) -> (v: Vec<OwnedPart>)
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

/// Parts 24 .. 25 of table orders, in order.
fn assemble_orders_2(p24: OwnedPart, p25: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 2,
        v@[0] == p24,
        v@[1] == p25,
{
    let mut v: Vec<OwnedPart> = Vec::with_capacity(2);
    v.push(p24);
    v.push(p25);
    v
}

/// The 26 parts of table orders, in order (each named by index in the postcondition).
fn assemble_orders(p0: OwnedPart, p1: OwnedPart, p2: OwnedPart, p3: OwnedPart, p4: OwnedPart, p5: OwnedPart, p6: OwnedPart, p7: OwnedPart, p8: OwnedPart, p9: OwnedPart, p10: OwnedPart, p11: OwnedPart, p12: OwnedPart, p13: OwnedPart, p14: OwnedPart, p15: OwnedPart, p16: OwnedPart, p17: OwnedPart, p18: OwnedPart, p19: OwnedPart, p20: OwnedPart, p21: OwnedPart, p22: OwnedPart, p23: OwnedPart, p24: OwnedPart, p25: OwnedPart) -> (v: Vec<OwnedPart>)
    ensures
        v@.len() == 26,
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
{
    let mut c0 = assemble_orders_0(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11);
    let mut c1 = assemble_orders_1(p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23);
    let mut c2 = assemble_orders_2(p24, p25);
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
    assert(v@.len() == 26);
    proof {
        assert(v@[24] == p24);
        assert(v@[25] == p25);
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
        r matches Ok(p) ==> crate::stores::facts::interface::represents(owned_parts_view(p@), tables(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    proof {
        reveal(src_ok);
    }
    let (map_lineitem, map_orders,) = order::row_maps(src);
    let mut parts: Vec<OwnedPart> = Vec::new();
    let rmv_lineitem = Arc::new(map_lineitem);
    let mut p_lineitem = match build_lineitem(src, rmv_lineitem.clone(), workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_lineitem = p_lineitem@;
    assert(owned_parts_view(v_lineitem).len() == LI_PARTS);
    parts.append(&mut p_lineitem);
    let rmv_orders = Arc::new(map_orders);
    let mut p_orders = match build_orders(src, rmv_orders.clone(), workers, dispatch) { Ok(p) => p, Err(e) => return Err(e) };
    let ghost v_orders = p_orders@;
    assert(owned_parts_view(v_orders).len() == OR_PARTS);
    parts.append(&mut p_orders);
    proof {
        assert forall|j: int| 0 <= j < rmv_lineitem@.len() implies #[trigger] rmv_lineitem@[j] < src@.t0_f0.len() by {
            assert(0 <= map_view(rmv_lineitem@)[j] < table_t0(src@).len());
        }
        assert forall|i: int| 0 <= i < rmv_orders@.len() implies #[trigger] rmv_orders@[i] < src@.t1_f0.len() by {
            assert(0 <= map_view(rmv_orders@)[i] < table_t1(src@).len());
        }
    }
    let flag = clustercheck::cluster_flag(src.t0_f0, &*rmv_lineitem, src.t1_f0, &*rmv_orders);
    assert(parts@.len() == FACTS_CLUSTER);
    let flag_part = OwnedPart::U64(vec![if flag { 1u64 } else { 0u64 }]);
    parts.push(flag_part);
    assert(parts@[FACTS_CLUSTER as int] == flag_part);
    proof {
        let pv = owned_parts_view(parts@);
        let ts = tables(src@);
        assert(pv.subrange(LINEITEM_FIRST as int, LINEITEM_FIRST as int + LI_PARTS as int) =~= owned_parts_view(v_lineitem));
        assert(ts[0] == table_t0(src@));
        assert(pv.subrange(ORDERS_FIRST as int, ORDERS_FIRST as int + OR_PARTS as int) =~= owned_parts_view(v_orders));
        assert(ts[1] == table_t1(src@));
        let cf = FACTS_CLUSTER as int;
        assert(pv[cf] == owned_part_view(flag_part));
        assert(u64s(pv[cf]) =~= seq![if flag { 1u64 } else { 0u64 }]);
        if flag {
            let lsub = pv.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int);
            let osub = pv.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OR_PARTS) as int);
            let (lrel, orel) = (table_t0(src@), table_t1(src@));
            assert(lineitem_map(lsub, lrel.len() as int) == map_view(rmv_lineitem@));
            assert(orders_map(osub, orel.len() as int) == map_view(rmv_orders@));
            let lrows = lineitem_rows(lsub, lrel);
            let orows = orders_rows(osub, orel);
            let lk = clustercheck::lkst(src@.t0_f0, rmv_lineitem@);
            let ok = clustercheck::okst(src@.t1_f0, rmv_orders@);
            assert forall|j: int| 0 <= j < lk.len() implies #[trigger] lrows[j][0] == Val::Int(lk[j]) by {
                assert(0 <= map_view(rmv_lineitem@)[j] < lrel.len());
            }
            assert forall|q: int| 0 <= q < ok.len() implies #[trigger] orows[q][0] == Val::Int(ok[q]) by {
                assert(0 <= map_view(rmv_orders@)[q] < orel.len());
            }
            clustercheck::lemma_cluster_rows(lrows, orows, lk, ok);
        }
    }
    Ok(parts)
}

} // verus!
