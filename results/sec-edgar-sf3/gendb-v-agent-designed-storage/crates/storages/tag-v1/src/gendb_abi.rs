// FRAMEWORK FILE: data types of the GenDB Verus C ABI v3 (gendb-runtime, `runtime/verus/gendb_abi.rs`).
//
// Copied unchanged into every Verus candidate crate as `crate::gendb_abi`. Authors cannot edit it.
// Types only: no specifications, proofs, `assume`, `admit` or `external_body`. The trusted
// `gendb_shim` builds these values from host memory and calls the verified
// `crate::gendb_entry::{abi_query, abi_build}`; the host side is `gendb_runtime::abi`.
//
// Query inputs: stored representation parts (`Part`) and statement arguments (`ParamArg`, one per
// free parameter in slot order). Query statuses include `SqlError(e)` (the exact trusted SQL error of
// the statement) and `ParamRefused` (arguments outside the declared parameter domain, decided by
// verified code before any author code runs).
//
// The build input is one column list: the delivered columns of every source table, table by table
// (`t0_f0, t0_f1, .., t1_f0, ..`); each table has its own row count.
use vstd::prelude::*;
use crate::exec::value::EVal;
use crate::spec::value::SqlError;

verus! {

/// One canonical source column, NOT NULL, in canonical source row order.
/// Decimal columns are coefficients at the declared scale; Date32 is days since 1970-01-01.
/// `Utf8`: absolute Arrow offsets (row count + 1 entries, the first may be > 0) into `bytes`.
pub enum Column {
    I32(&'static [i32]),
    I64(&'static [i64]),
    I128(&'static [i128]),
    Utf8 { offsets: &'static [i64], bytes: &'static [u8] },
}

/// One read-only part of a stored data representation, as written by its builder.
pub enum Part {
    I8(&'static [i8]),
    I16(&'static [i16]),
    I32(&'static [i32]),
    I64(&'static [i64]),
    I128(&'static [i128]),
    U8(&'static [u8]),
    U16(&'static [u16]),
    U32(&'static [u32]),
    U64(&'static [u64]),
}

/// One owned part returned by a representation builder; the host stores it.
pub enum OwnedPart {
    I8(Vec<i8>),
    I16(Vec<i16>),
    I32(Vec<i32>),
    I64(Vec<i64>),
    I128(Vec<i128>),
    U8(Vec<u8>),
    U16(Vec<u16>),
    U32(Vec<u32>),
    U64(Vec<u64>),
}

/// Civil date components of a `date` argument (no range check here; the verified parameter binder decides).
#[derive(Clone, Copy)]
pub struct CivilDate {
    pub y: i32,
    pub m: i32,
    pub d: i32,
}

/// One statement argument, for one free parameter (slot order = ascending placeholder index).
/// `Int`: `integer`/`bigint` value; `Num`: `numeric(p, s)` coefficient at the declared scale `s`;
/// `Date`: civil date.
#[derive(Clone, Copy)]
pub enum ParamArg {
    Int(i64),
    Num(i128),
    Date(CivilDate),
}

/// Call outcome.
/// - `Refused`: worker count outside 1..=MAX_WORKERS, or the verified binder did not accept the column shapes.
/// - `ParamRefused`: the arguments are not a binding of the declared parameter domain (count, kinds, types,
///   bounds); decided by verified entry code before any author code runs.
/// - `SqlError(e)`: the statement's meaning on the database is exactly the SQL error `e`.
/// - `Capacity`: the database is outside the fixed generic capacity domain (never a SQL result).
/// - `InvalidInput` (build only): the delivered columns are outside the declared column domains.
/// - `WorkerFailed`: a joined worker thread failed (only from the runtime's private token).
/// - `Malformed`: never produced by a verified entry (kept for the status table).
pub enum AbiStatus {
    Ok,
    InvalidInput,
    Malformed,
    WorkerFailed,
    Refused,
    Capacity,
    SqlError(SqlError),
    ParamRefused,
}

/// Observed dispatch of one call: workers spawned and joined, and the row range
/// `[lo, hi)` declared for each spawn. Descriptive evidence only.
pub struct DispatchEvidence {
    pub spawned: u64,
    pub joined: u64,
    pub ranges: Vec<(u64, u64)>,
}

/// Query result: with `Ok`, the result rows as VERUS_SQL executable values; otherwise empty.
pub struct QueryReturn {
    pub status: AbiStatus,
    pub rows: Vec<Vec<EVal>>,
    pub dispatch: DispatchEvidence,
}

pub struct BuildReturn {
    pub status: AbiStatus,
    pub parts: Vec<OwnedPart>,
    pub dispatch: DispatchEvidence,
}

} // verus!
