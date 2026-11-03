// FRAMEWORK FILE: trusted C ABI shim of a reference evaluator crate (`gendb_sqlspec::evaluator`).
//
// Copied unchanged into every evaluator crate as `crate::shim`, outside `verus!{}`. NOT VERIFIED; it is a
// listed trusted component and the only file of the crate the refusal scanner does not read. It contains no
// SQL logic. It only
//   1. copies the host's input bytes and decodes the database wire format into owned executable rows
//      (`EVal`), refusing malformed bytes before any verified code runs (a *wire* check: typing, NULL and
//      range rules of the data are decided by the verified `check_db` inside `crate::abi::abi_run`);
//   2. calls the verified entry points `crate::abi::{abi_run, abi_echo}`;
//   3. encodes the verified outcome (result wire) and the executable AST (echo text) into a host sink.
// The codec *definition* (bytes <-> `EVal`, `EOrderedQuery` -> echo text) is trusted and mirrored by the
// host (`gendb_sqlspec::codec`, `gendb_sqlspec::evaluator::echo_text`). Nothing borrows host memory after a
// call returns. A panic reaching this shim aborts the process.
use crate::abi::{abi_echo, abi_run};
use crate::exec::ast::*;
use crate::exec::value::*;
use crate::exec::relational::entry::EvalResult;
use crate::spec::int::IntKind;
use crate::spec::ast::ScalarFn;
use crate::spec::scalar::{ArithOp, CastOp, CmpOp, NumKind};
use crate::spec::types::ScalarTy;
use crate::spec::value::SqlError;
use std::ffi::c_void;
use std::fmt::Write as _;

/// Version of the wire formats and C symbols below.
const ABI_VERSION: u64 = 1;
const DB_MAGIC: &[u8; 8] = b"GSQLDB1\0";
const RESULT_MAGIC: &[u8; 8] = b"GSQLRS1\0";

const STATUS_ROWS: u8 = 0;
const STATUS_SQL_ERROR: u8 = 1;
const STATUS_CAPACITY: u8 = 2;
const STATUS_BAD_DATABASE: u8 = 3;
const STATUS_ILL_TYPED: u8 = 4;
const STATUS_WIRE_REFUSED: u8 = 5;
const STATUS_CONSTRAINT_VIOLATION: u8 = 6;

/// Host-provided output sink: called once with the complete output bytes; non-zero = failure.
#[repr(C)]
pub struct SqlSinkV1 {
    ctx: *mut c_void,
    put: Option<unsafe extern "C" fn(*mut c_void, *const u8, u64) -> i32>,
}

struct Reader<'a> {
    b: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(n)?;
        let s = self.b.get(self.at..end)?;
        self.at = end;
        Some(s)
    }
    fn u8(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }
    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?))
    }
    fn i32(&mut self) -> Option<i32> {
        Some(i32::from_le_bytes(self.take(4)?.try_into().ok()?))
    }
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }
    fn i64(&mut self) -> Option<i64> {
        Some(i64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }
    fn i128(&mut self) -> Option<i128> {
        Some(i128::from_le_bytes(self.take(16)?.try_into().ok()?))
    }
    /// A count that cannot exceed the remaining input (every counted item takes at least one byte).
    fn count(&mut self) -> Option<usize> {
        let n = usize::try_from(self.u64()?).ok()?;
        if n > self.b.len() - self.at { None } else { Some(n) }
    }
}

fn decode_value(r: &mut Reader) -> Option<EVal> {
    Some(match r.u8()? {
        0 => EVal::Null,
        1 => match r.u8()? {
            0 => EVal::Bool(false),
            1 => EVal::Bool(true),
            _ => return None,
        },
        2 => EVal::Int(r.i64()?),
        3 => {
            let coeff = r.i128()?;
            EVal::Num { coeff, scale: r.u32()? }
        }
        4 => EVal::Date(r.i32()?),
        5 => EVal::Ts(r.i64()?),
        6 => {
            let n = r.count()?;
            EVal::Text(r.take(n)?.to_vec())
        }
        _ => return None,
    })
}

/// Database wire -> rows per table (table id = position). `None` = malformed bytes.
fn decode_tables(bytes: &[u8]) -> Option<Vec<Vec<ERow>>> {
    let mut r = Reader { b: bytes, at: 0 };
    if r.take(8)? != DB_MAGIC {
        return None;
    }
    let mut tables = Vec::new();
    for _ in 0..r.count()? {
        let mut rows = Vec::new();
        for _ in 0..r.count()? {
            let mut row = Vec::new();
            for _ in 0..r.count()? {
                row.push(decode_value(&mut r)?);
            }
            rows.push(row);
        }
        tables.push(rows);
    }
    if r.at != bytes.len() {
        return None;
    }
    Some(tables)
}

fn encode_value(out: &mut Vec<u8>, v: &EVal) {
    match v {
        EVal::Null => out.push(0),
        EVal::Bool(b) => out.extend([1, *b as u8]),
        EVal::Int(x) => {
            out.push(2);
            out.extend(x.to_le_bytes());
        }
        EVal::Num { coeff, scale } => {
            out.push(3);
            out.extend(coeff.to_le_bytes());
            out.extend(scale.to_le_bytes());
        }
        EVal::Date(d) => {
            out.push(4);
            out.extend(d.to_le_bytes());
        }
        EVal::Ts(t) => {
            out.push(5);
            out.extend(t.to_le_bytes());
        }
        EVal::Text(b) => {
            out.push(6);
            out.extend((b.len() as u64).to_le_bytes());
            out.extend(b);
        }
    }
}

fn sql_error_code(e: &SqlError) -> u8 {
    match e {
        SqlError::NumericValueOutOfRange => 1,
        SqlError::DatetimeFieldOverflow => 2,
        SqlError::TypeError => 3,
        SqlError::DivisionByZero => 4,
        SqlError::CardinalityViolation => 5,
        SqlError::SubstringError => 6,
        SqlError::InvalidEscapeSequence => 7,
        SqlError::InvalidEscapeCharacter => 8,
    }
}

fn encode_result(r: Option<&EvalResult>) -> Vec<u8> {
    let mut out = RESULT_MAGIC.to_vec();
    match r {
        None => out.push(STATUS_WIRE_REFUSED),
        Some(EvalResult::BadDatabase) => out.push(STATUS_BAD_DATABASE),
        Some(EvalResult::IllTyped) => out.push(STATUS_ILL_TYPED),
        Some(EvalResult::Capacity) => out.push(STATUS_CAPACITY),
        Some(EvalResult::ConstraintViolation) => out.push(STATUS_CONSTRAINT_VIOLATION),
        Some(EvalResult::Done(Err(e))) => out.extend([STATUS_SQL_ERROR, sql_error_code(e)]),
        Some(EvalResult::Done(Ok(rows))) => {
            out.push(STATUS_ROWS);
            out.extend((rows.len() as u64).to_le_bytes());
            for row in rows {
                out.extend((row.len() as u64).to_le_bytes());
                for v in row {
                    encode_value(&mut out, v);
                }
            }
        }
    }
    out
}

// ---- echo: canonical s-expression of the executable AST (grammar in `gendb_sqlspec::evaluator::echo_text`).

fn int_kind(k: &IntKind) -> &'static str {
    match k {
        IntKind::Int4 => "Int4",
        IntKind::Int8 => "Int8",
    }
}

fn num_kind(k: &NumKind) -> &'static str {
    match k {
        NumKind::Int4 => "Int4",
        NumKind::Int8 => "Int8",
        NumKind::Numeric => "Numeric",
    }
}

fn arith_op(o: &ArithOp) -> &'static str {
    match o {
        ArithOp::Add => "Add",
        ArithOp::Sub => "Sub",
        ArithOp::Mul => "Mul",
    }
}

fn cmp_op(o: &CmpOp) -> &'static str {
    match o {
        CmpOp::Eq => "Eq",
        CmpOp::Ne => "Ne",
        CmpOp::Lt => "Lt",
        CmpOp::Le => "Le",
        CmpOp::Gt => "Gt",
        CmpOp::Ge => "Ge",
    }
}

fn cast_op(o: &CastOp) -> &'static str {
    match o {
        CastOp::Int4ToInt8 => "Int4ToInt8",
        CastOp::IntToNumeric => "IntToNumeric",
        CastOp::DateToTimestamp => "DateToTimestamp",
    }
}

fn scalar_fn(f: &ScalarFn) -> &'static str {
    match f {
        ScalarFn::DivInt4 => "DivInt4",
        ScalarFn::DivInt8 => "DivInt8",
        ScalarFn::DivNumeric => "DivNumeric",
        ScalarFn::Like => "Like",
        ScalarFn::Substring2 => "Substring2",
        ScalarFn::Substring3 => "Substring3",
        ScalarFn::ExtractYear => "ExtractYear",
        ScalarFn::ExtractMonth => "ExtractMonth",
        ScalarFn::ExtractDay => "ExtractDay",
        ScalarFn::PadBpchar => "PadBpchar",
    }
}

fn scalar_ty(o: &mut String, t: &ScalarTy) {
    match t {
        ScalarTy::Bool => o.push_str("(Bool)"),
        ScalarTy::Int4 => o.push_str("(Int4)"),
        ScalarTy::Int8 => o.push_str("(Int8)"),
        ScalarTy::Numeric { scale } => {
            let _ = write!(o, "(Numeric {scale})");
        }
        ScalarTy::Date => o.push_str("(Date)"),
        ScalarTy::Timestamp => o.push_str("(Timestamp)"),
        ScalarTy::Text => o.push_str("(Text)"),
    }
}

fn lit(o: &mut String, l: &ELiteral) {
    match l {
        ELiteral::Null { ty } => {
            o.push_str("(Null ");
            scalar_ty(o, ty);
            o.push(')');
        }
        ELiteral::Bool(b) => {
            let _ = write!(o, "(Bool {b})");
        }
        ELiteral::Int { v, kind } => {
            let _ = write!(o, "(Int {v} {})", int_kind(kind));
        }
        ELiteral::Num { coeff, scale } => {
            let _ = write!(o, "(Num {coeff} {scale})");
        }
        ELiteral::Date { y, m, d } => {
            let _ = write!(o, "(Date {y} {m} {d})");
        }
        ELiteral::Text(b) => {
            o.push_str("(Text 0x");
            for x in b {
                let _ = write!(o, "{x:02x}");
            }
            o.push(')');
        }
    }
}

fn expr(o: &mut String, e: &EExpr) {
    match e {
        EExpr::Col(i) => {
            let _ = write!(o, "(Col {i})");
        }
        EExpr::Lit(l) => {
            o.push_str("(Lit ");
            lit(o, l);
            o.push(')');
        }
        EExpr::Neg { kind, arg } => {
            let _ = write!(o, "(Neg {} ", num_kind(kind));
            expr(o, arg);
            o.push(')');
        }
        EExpr::Arith { op, kind, a, b } => {
            let _ = write!(o, "(Arith {} {} ", arith_op(op), num_kind(kind));
            expr(o, a);
            o.push(' ');
            expr(o, b);
            o.push(')');
        }
        EExpr::Cast { cast, arg } => {
            let _ = write!(o, "(Cast {} ", cast_op(cast));
            expr(o, arg);
            o.push(')');
        }
        EExpr::AddInterval { arg, months, days, micros } => {
            o.push_str("(AddInterval ");
            expr(o, arg);
            let _ = write!(o, " {months} {days} {micros})");
        }
        EExpr::Call { f, args } => {
            let _ = write!(o, "(Call {} ", scalar_fn(f));
            list(o, args, expr);
            o.push(')');
        }
        EExpr::If { cond, then_e, else_e } => {
            o.push_str("(If ");
            pred(o, cond);
            o.push(' ');
            expr(o, then_e);
            o.push(' ');
            expr(o, else_e);
            o.push(')');
        }
        EExpr::Subquery(q) => {
            o.push_str("(Subquery ");
            query(o, q);
            o.push(')');
        }
    }
}

fn pred(o: &mut String, p: &EPred) {
    match p {
        EPred::Cmp { op, a, b } => {
            let _ = write!(o, "(Cmp {} ", cmp_op(op));
            expr(o, a);
            o.push(' ');
            expr(o, b);
            o.push(')');
        }
        EPred::And(a, b) | EPred::Or(a, b) => {
            o.push_str(if matches!(p, EPred::And(..)) { "(And " } else { "(Or " });
            pred(o, a);
            o.push(' ');
            pred(o, b);
            o.push(')');
        }
        EPred::Not(a) => {
            o.push_str("(Not ");
            pred(o, a);
            o.push(')');
        }
        EPred::IsNull(e) | EPred::OfBool(e) => {
            o.push_str(if matches!(p, EPred::IsNull(_)) { "(IsNull " } else { "(OfBool " });
            expr(o, e);
            o.push(')');
        }
        EPred::Exists(q) => {
            o.push_str("(Exists ");
            query(o, q);
            o.push(')');
        }
        EPred::AnyCmp { op, e, q } => {
            let _ = write!(o, "(AnyCmp {} ", cmp_op(op));
            expr(o, e);
            o.push(' ');
            query(o, q);
            o.push(')');
        }
    }
}

fn agg(o: &mut String, a: &EAgg) {
    match a {
        EAgg::CountStar => o.push_str("(CountStar)"),
        EAgg::Count(e) => {
            o.push_str("(Count ");
            expr(o, e);
            o.push(')');
        }
        EAgg::Sum { kind, arg } => {
            let _ = write!(o, "(Sum {} ", num_kind(kind));
            expr(o, arg);
            o.push(')');
        }
        EAgg::Min(e) | EAgg::Max(e) => {
            o.push_str(if matches!(a, EAgg::Min(_)) { "(Min " } else { "(Max " });
            expr(o, e);
            o.push(')');
        }
        EAgg::Avg { kind, arg } => {
            let _ = write!(o, "(Avg {} ", num_kind(kind));
            expr(o, arg);
            o.push(')');
        }
        EAgg::DistinctAgg(inner) => {
            o.push_str("(DistinctAgg ");
            agg(o, inner);
            o.push(')');
        }
    }
}

fn list<T>(o: &mut String, xs: &[T], f: fn(&mut String, &T)) {
    o.push('[');
    for (i, x) in xs.iter().enumerate() {
        if i > 0 {
            o.push(' ');
        }
        f(o, x);
    }
    o.push(']');
}

fn query(o: &mut String, q: &EQuery) {
    match q {
        EQuery::Table(t) => {
            let _ = write!(o, "(Table {t})");
        }
        EQuery::Filter { pred: p, input } => {
            o.push_str("(Filter ");
            pred(o, p);
            o.push(' ');
            query(o, input);
            o.push(')');
        }
        EQuery::Project { exprs, input } => {
            o.push_str("(Project ");
            list(o, exprs, expr);
            o.push(' ');
            query(o, input);
            o.push(')');
        }
        EQuery::Product { left, right } => {
            o.push_str("(Product ");
            query(o, left);
            o.push(' ');
            query(o, right);
            o.push(')');
        }
        EQuery::LeftJoin { left, right, on } => {
            o.push_str("(LeftJoin ");
            query(o, left);
            o.push(' ');
            query(o, right);
            o.push(' ');
            pred(o, on);
            o.push(')');
        }
        EQuery::Aggregate { aggs, input } => {
            o.push_str("(Aggregate ");
            list(o, aggs, agg);
            o.push(' ');
            query(o, input);
            o.push(')');
        }
        EQuery::GroupBy { keys, aggs, input } => {
            o.push_str("(GroupBy ");
            list(o, keys, expr);
            o.push(' ');
            list(o, aggs, agg);
            o.push(' ');
            query(o, input);
            o.push(')');
        }
        EQuery::Distinct(input) => {
            o.push_str("(Distinct ");
            query(o, input);
            o.push(')');
        }
    }
}

fn order_key(o: &mut String, k: &EOrderKey) {
    let _ = write!(o, "(OrderKey {} {} {})", k.col, k.desc, k.nulls_first);
}

fn echo_text(q: &EOrderedQuery) -> String {
    let mut o = String::from("(OrderedQuery ");
    query(&mut o, &q.body);
    o.push(' ');
    list(&mut o, &q.keys, order_key);
    match q.limit {
        None => o.push_str(" none"),
        Some(n) => {
            let _ = write!(o, " (some {n})");
        }
    }
    let _ = write!(o, " {})", q.offset);
    o
}

// ---- C symbols

fn guarded(f: impl FnOnce() -> i32) -> i32 {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(r) => r,
        Err(_) => std::process::abort(),
    }
}

unsafe fn deliver(sink: *const SqlSinkV1, bytes: &[u8]) -> i32 {
    let Some(sink) = (unsafe { sink.as_ref() }) else { return -1 };
    let Some(put) = sink.put else { return -1 };
    if unsafe { put(sink.ctx, bytes.as_ptr(), bytes.len() as u64) } != 0 { -2 } else { 0 }
}

#[no_mangle]
pub extern "C" fn gendb_sql_abi_version_v1() -> u64 {
    ABI_VERSION
}

/// Evaluate the crate's query on the database in `data[..len]`; the result wire goes to `sink`.
/// Returns 0 when the sink received the result, negative for a bad sink.
#[no_mangle]
pub unsafe extern "C" fn gendb_sql_run_v1(data: *const u8, len: u64, sink: *const SqlSinkV1) -> i32 {
    guarded(|| {
        let bytes: Vec<u8> = match usize::try_from(len) {
            Ok(0) => Vec::new(),
            Ok(n) if !data.is_null() => unsafe { std::slice::from_raw_parts(data, n) }.to_vec(),
            _ => return unsafe { deliver(sink, &encode_result(None)) },
        };
        let out = match decode_tables(&bytes) {
            None => encode_result(None),
            Some(tables) => encode_result(Some(&abi_run(tables))),
        };
        unsafe { deliver(sink, &out) }
    })
}

/// The executable AST of the crate's query as echo text (UTF-8) to `sink`.
#[no_mangle]
pub unsafe extern "C" fn gendb_sql_echo_v1(sink: *const SqlSinkV1) -> i32 {
    guarded(|| {
        let text = echo_text(&abi_echo());
        unsafe { deliver(sink, text.as_bytes()) }
    })
}
