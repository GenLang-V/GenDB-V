//! L3, executable checker: the non-recursive operators (engine toolkit; nothing here names a query, a table or a
//! column).
//!
//! One executable function per operator analysis of `engine_link::classes`, each proved equal to it
//! (`ensures r == <spec function>(..)`): error sets, value classes of constants and columns, unary and binary
//! arithmetic, casts, intervals, scalar functions (with the LIKE pattern check), comparisons, CASE branches,
//! scalar subqueries and aggregate values. The analysis types (`VClass`, `Errs`, `ExprInfo`, `PredInfo`) are
//! machine data, so these functions return them directly; lists use `EListInfo` / `EQueryInfo` with a view.
//! The recursive analysis is `engine_link::classes_exec`.
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::domain::*;
use crate::exec::datetime::{date_valid_exec, ts_valid_exec};
use crate::exec::chars::*;
use crate::exec::fns::like::*;
use crate::exec::expr::exec_expr;
use crate::exec::relational::schema::*;
use crate::link::expr::{closed_expr, closed_db};
use crate::engine_link::classes::*;

verus! {

// ------------------------------------------------------------------------------------- list analyses

/// `ListInfo` with a vector of classes.
pub struct EListInfo {
    pub classes: Vec<VClass>,
    pub errs: Errs,
    pub fits: bool,
}

pub open spec fn view_list_info(l: EListInfo) -> ListInfo {
    ListInfo { classes: l.classes@, errs: l.errs, fits: l.fits }
}

pub open spec fn view_list_opt(l: Option<EListInfo>) -> Option<ListInfo> {
    match l {
        Some(x) => Some(view_list_info(x)),
        None => None,
    }
}

/// `QueryInfo` with a vector of classes.
pub struct EQueryInfo {
    pub cols: Vec<VClass>,
    pub errs: Errs,
    pub fits: bool,
    pub one_row: bool,
}

pub open spec fn view_query_info(q: EQueryInfo) -> QueryInfo {
    QueryInfo { cols: q.cols@, errs: q.errs, fits: q.fits, one_row: q.one_row }
}

pub open spec fn view_query_opt(q: Option<EQueryInfo>) -> Option<QueryInfo> {
    match q {
        Some(x) => Some(view_query_info(x)),
        None => None,
    }
}

/// `a ++ b`.
pub fn concat_classes(a: &Vec<VClass>, b: &Vec<VClass>) -> (r: Vec<VClass>)
    ensures r@ == a@ + b@,
{
    let mut r: Vec<VClass> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len(), r@ == a@.take(i as int),
        decreases a.len() - i,
    {
        r.push(a[i]);
        proof { assert(r@ =~= a@.take(i as int + 1)); }
        i = i + 1;
    }
    let mut j: usize = 0;
    proof { assert(a@.take(a.len() as int) =~= a@); }
    while j < b.len()
        invariant j <= b.len(), r@ == a@ + b@.take(j as int),
        decreases b.len() - j,
    {
        r.push(b[j]);
        proof { assert(r@ =~= a@ + b@.take(j as int + 1)); }
        j = j + 1;
    }
    proof { assert(b@.take(b.len() as int) =~= b@); }
    r
}

/// `nullable_classes`.
pub fn nullable_classes_exec(a: &Vec<VClass>) -> (r: Vec<VClass>)
    ensures r@ == nullable_classes(a@),
{
    let mut r: Vec<VClass> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len(), r@ == nullable_classes(a@.take(i as int)),
        decreases a.len() - i,
    {
        r.push(VClass { kind: a[i].kind, nullable: true });
        proof { assert(r@ =~= nullable_classes(a@.take(i as int + 1))); }
        i = i + 1;
    }
    proof { assert(a@.take(a.len() as int) =~= a@); }
    r
}

// ------------------------------------------------------------------------------------- errors

/// SQL error equality.
pub fn same_error(a: SqlError, b: SqlError) -> (r: bool)
    ensures r == (a == b),
{
    match (a, b) {
        (SqlError::NumericValueOutOfRange, SqlError::NumericValueOutOfRange) => true,
        (SqlError::DatetimeFieldOverflow, SqlError::DatetimeFieldOverflow) => true,
        (SqlError::DivisionByZero, SqlError::DivisionByZero) => true,
        (SqlError::CardinalityViolation, SqlError::CardinalityViolation) => true,
        (SqlError::SubstringError, SqlError::SubstringError) => true,
        (SqlError::InvalidEscapeSequence, SqlError::InvalidEscapeSequence) => true,
        (SqlError::InvalidEscapeCharacter, SqlError::InvalidEscapeCharacter) => true,
        (SqlError::TypeError, SqlError::TypeError) => true,
        _ => false,
    }
}

/// Executable `errs_join` (proved equal).
pub fn errs_join_exec(a: Errs, b: Errs) -> (r: Option<Errs>)
    ensures r == errs_join(a, b),
{
    match (a, b) {
        (Errs::Never, _) => Some(b),
        (_, Errs::Never) => Some(a),
        (Errs::Only(x), Errs::Only(y)) => if same_error(x, y) { Some(a) } else { None },
    }
}

/// Executable `errs_join3` (proved equal).
pub fn errs_join3_exec(a: Errs, b: Errs, c: Errs) -> (r: Option<Errs>)
    ensures r == errs_join3(a, b, c),
{
    match errs_join_exec(a, b) {
        Some(x) => errs_join_exec(x, c),
        None => None,
    }
}

// ------------------------------------------------------------------------------------- classes of values

/// Executable `column_class` (proved equal).
pub fn column_class_exec(c: Column) -> (r: VClass)
    ensures r == column_class(c),
{
    VClass {
        kind: match c.ty {
            SqlType::Bool => VKind::Bool,
            SqlType::Int4 => VKind::Int { mag: 0x8000_0000 },
            SqlType::Int8 => VKind::Int { mag: 0x8000_0000_0000_0000 },
            SqlType::Numeric { precision, scale } => VKind::Num { scale, digits: Some(precision) },
            SqlType::Date => VKind::Date,
            SqlType::Timestamp => VKind::Ts,
            SqlType::Text => VKind::Text,
            SqlType::Varchar { .. } => VKind::Text,
            SqlType::Bpchar { .. } => VKind::Text,
        },
        nullable: c.nullable,
    }
}

/// Executable `table_classes` (proved equal).
pub fn table_classes_exec(t: &ETableSchema) -> (r: Vec<VClass>)
    ensures r@ == table_classes(view_table_schema(*t)),
{
    let mut r: Vec<VClass> = Vec::new();
    let mut i: usize = 0;
    while i < t.columns.len()
        invariant i <= t.columns.len(), r@ == table_classes(view_table_schema(*t)).take(i as int),
        decreases t.columns.len() - i,
    {
        r.push(column_class_exec(t.columns[i]));
        proof { assert(r@ =~= table_classes(view_table_schema(*t)).take(i as int + 1)); }
        i = i + 1;
    }
    proof { assert(table_classes(view_table_schema(*t)).take(t.columns.len() as int) =~= table_classes(view_table_schema(*t))); }
    r
}

/// `|c|` of an `i128`, exactly.
pub fn abs_i128(c: i128) -> (r: u128)
    ensures r as int == abs(c as int),
{
    if c >= 0 {
        c as u128
    } else if c == i128::MIN {
        0x8000_0000_0000_0000_0000_0000_0000_0000u128
    } else {
        (-c) as u128
    }
}

/// Every `u128` has at most 39 decimal digits.
proof fn lemma_u128_digits(n: u128)
    ensures decimal_digits(n as int) <= 39,
{
    assert(pow10(39) == 1000000000000000000000000000000000000000) by (compute);
    lemma_decimal_digits_bound(n as int, 39);
}

/// `spec::numeric::decimal_digits`.
pub fn decimal_digits_exec(n: u128) -> (r: u32)
    ensures r as nat == decimal_digits(n as int),
{
    proof { lemma_u128_digits(n); }
    let mut x = n;
    let mut d: u32 = 0;
    while x > 0
        invariant d as nat + decimal_digits(x as int) == decimal_digits(n as int), decimal_digits(n as int) <= 39,
        decreases x,
    {
        assert(decimal_digits(x as int) == 1 + decimal_digits(x as int / 10));
        x = x / 10;
        d = d + 1;
    }
    d
}

/// Executable `const_class` (proved equal).
pub fn const_class_exec(v: &EVal) -> (r: Option<VClass>)
    ensures r == const_class(v@),
{
    match v {
        EVal::Null => Some(VClass { kind: VKind::NoValue, nullable: true }),
        EVal::Bool(_) => Some(VClass { kind: VKind::Bool, nullable: false }),
        EVal::Int(x) => {
            let m = abs_i128(*x as i128);
            Some(VClass { kind: VKind::Int { mag: m }, nullable: false })
        },
        EVal::Num { coeff, scale } => {
            let m = abs_i128(*coeff);
            let d = decimal_digits_exec(m);
            Some(VClass { kind: VKind::Num { scale: *scale, digits: Some(d) }, nullable: false })
        },
        EVal::Date(d) => if date_valid_exec(*d as i64) { Some(VClass { kind: VKind::Date, nullable: false }) } else { None },
        EVal::Ts(t) => if ts_valid_exec(*t as i128) { Some(VClass { kind: VKind::Ts, nullable: false }) } else { None },
        EVal::Text(_) => Some(VClass { kind: VKind::Text, nullable: false }),
    }
}

/// `link::expr::closed_expr`.
pub fn closed_expr_exec(e: &EExpr) -> (r: bool)
    ensures r == closed_expr(view_expr(*e)),
    decreases e,
{
    match e {
        EExpr::Col(_) => false,
        EExpr::Lit(_) => true,
        EExpr::Neg { arg, .. } => closed_expr_exec(arg),
        EExpr::Arith { a, b, .. } => closed_expr_exec(a) && closed_expr_exec(b),
        EExpr::Cast { arg, .. } => closed_expr_exec(arg),
        EExpr::AddInterval { arg, .. } => closed_expr_exec(arg),
        _ => false,
    }
}

/// `closed_value`: evaluated once by the verified interpreter in the empty database and environment.
pub fn closed_value_exec(e: &EExpr) -> (r: Option<EVal>)
    ensures
        match r {
            Some(v) => closed_value(view_expr(*e)) == Some(v@),
            None => closed_value(view_expr(*e)) is None,
        },
{
    if !closed_expr_exec(e) {
        return None;
    }
    let db = EDatabase { schema: Vec::new(), tables: Vec::new() };
    let env: Vec<EVal> = Vec::new();
    proof {
        assert(db@.schema =~= Seq::<TableSchema>::empty());
        assert(db@.tables =~= Seq::<Relation>::empty());
        assert(db@ == closed_db());
        assert(view_row(env@) =~= Seq::<Val>::empty());
        assert(db_ts_ok(db@));
        assert(row_ts_ok(view_row(env@)));
    }
    match exec_expr(&db, &env, e) {
        Ok(Ok(v)) => Some(v),
        _ => None,
    }
}

/// Executable `closed_info` (proved equal).
pub fn closed_info_exec(e: &EExpr) -> (r: Option<ExprInfo>)
    ensures r == closed_info(view_expr(*e)),
{
    match closed_value_exec(e) {
        Some(v) => match const_class_exec(&v) {
            Some(c) => Some(ExprInfo { cls: c, errs: Errs::Never, fits: true }),
            None => None,
        },
        None => None,
    }
}

// ------------------------------------------------------------------------------------- operators

/// Executable `int_ok` (proved equal).
pub fn int_ok_exec(k: VKind) -> (r: bool)
    ensures r == int_ok(k),
{
    match k {
        VKind::Int { mag } => mag <= 0x8000_0000_0000_0000,
        _ => false,
    }
}

/// Executable `num_ok` (proved equal).
pub fn num_ok_exec(k: VKind) -> (r: bool)
    ensures r == num_ok(k),
{
    match k {
        VKind::Num { scale, digits } => scale <= 16383 && match digits {
            Some(d) => d <= 147455,
            None => true,
        },
        _ => false,
    }
}

/// Executable `kind_mag` (proved equal).
pub fn kind_mag_exec(k: IntKind) -> (r: u128)
    ensures r as int == kind_mag(k),
{
    match k {
        IntKind::Int4 => 0x8000_0000,
        IntKind::Int8 => 0x8000_0000_0000_0000,
    }
}

/// Executable `int_result_info` (proved equal).
pub fn int_result_info_exec(k: IntKind, m: u128, nullable: bool) -> (r: ExprInfo)
    ensures r == int_result_info(k, m as int, nullable),
{
    let km = kind_mag_exec(k);
    if m <= km - 1 {
        ExprInfo { cls: VClass { kind: VKind::Int { mag: m }, nullable }, errs: Errs::Never, fits: true }
    } else {
        ExprInfo {
            cls: VClass { kind: VKind::Int { mag: km }, nullable },
            errs: Errs::Only(SqlError::NumericValueOutOfRange),
            fits: true,
        }
    }
}

/// Executable `num_result_info` (proved equal).
pub fn num_result_info_exec(s: u32, d: u64, nullable: bool) -> (r: ExprInfo)
    requires s <= 16383,
    ensures r == num_result_info(s, d as int, nullable),
{
    let limit: u64 = 131072 + s as u64;
    if d <= limit {
        ExprInfo {
            cls: VClass { kind: VKind::Num { scale: s, digits: Some(d as u32) }, nullable },
            errs: Errs::Never,
            fits: d <= 38,
        }
    } else {
        ExprInfo {
            cls: VClass { kind: VKind::Num { scale: s, digits: Some(limit as u32) }, nullable },
            errs: Errs::Only(SqlError::NumericValueOutOfRange),
            fits: false,
        }
    }
}

/// Executable `num_unbounded_info` (proved equal).
pub fn num_unbounded_info_exec(s: u32, nullable: bool) -> (r: ExprInfo)
    requires s <= 16383,
    ensures r == num_unbounded_info(s, nullable),
{
    ExprInfo {
        cls: VClass { kind: VKind::Num { scale: s, digits: Some((131072 + s as u64) as u32) }, nullable },
        errs: Errs::Only(SqlError::NumericValueOutOfRange),
        fits: false,
    }
}

/// Executable `num_any_info` (proved equal).
pub fn num_any_info_exec(nullable: bool) -> (r: ExprInfo)
    ensures r == num_any_info(nullable),
{
    ExprInfo { cls: VClass { kind: VKind::NumAny, nullable }, errs: Errs::Only(SqlError::NumericValueOutOfRange), fits: false }
}

/// Executable `null_info` (proved equal).
pub fn null_info_exec() -> (r: ExprInfo)
    ensures r == null_info(),
{
    ExprInfo { cls: VClass { kind: VKind::NoValue, nullable: true }, errs: Errs::Never, fits: true }
}

/// Executable `neg_op` (proved equal).
pub fn neg_op_exec(k: NumKind, a: VClass) -> (r: Option<ExprInfo>)
    ensures r == neg_op(k, a),
{
    match (k, a.kind) {
        (_, VKind::NoValue) => Some(null_info_exec()),
        (NumKind::Int4, VKind::Int { mag }) | (NumKind::Int8, VKind::Int { mag }) =>
            if int_ok_exec(a.kind) {
                let ik = match k { NumKind::Int8 => IntKind::Int8, _ => IntKind::Int4 };
                Some(int_result_info_exec(ik, mag, a.nullable))
            } else {
                None
            },
        (NumKind::Numeric, VKind::Num { scale, digits }) =>
            if num_ok_exec(a.kind) {
                match digits {
                    Some(d) => Some(num_result_info_exec(scale, d as u64, a.nullable)),
                    None => Some(num_unbounded_info_exec(scale, a.nullable)),
                }
            } else {
                None
            },
        (NumKind::Numeric, VKind::NumAny) => Some(num_any_info_exec(a.nullable)),
        _ => None,
    }
}

/// Executable `arith_op` (proved equal).
pub fn arith_op_exec(op: ArithOp, k: NumKind, a: VClass, b: VClass) -> (r: Option<ExprInfo>)
    ensures r == arith_op(op, k, a, b),
{
    let nullable = a.nullable || b.nullable;
    match (k, a.kind, b.kind) {
        (NumKind::Int4, VKind::NoValue, VKind::Int { .. }) | (NumKind::Int4, VKind::Int { .. }, VKind::NoValue)
        | (NumKind::Int4, VKind::NoValue, VKind::NoValue) | (NumKind::Int8, VKind::NoValue, VKind::Int { .. })
        | (NumKind::Int8, VKind::Int { .. }, VKind::NoValue) | (NumKind::Int8, VKind::NoValue, VKind::NoValue)
        | (NumKind::Numeric, VKind::NoValue, VKind::Num { .. }) | (NumKind::Numeric, VKind::Num { .. }, VKind::NoValue)
        | (NumKind::Numeric, VKind::NoValue, VKind::NumAny) | (NumKind::Numeric, VKind::NumAny, VKind::NoValue)
        | (NumKind::Numeric, VKind::NoValue, VKind::NoValue) => Some(null_info_exec()),
        (NumKind::Int4, VKind::Int { mag: x }, VKind::Int { mag: y }) | (NumKind::Int8, VKind::Int { mag: x }, VKind::Int { mag: y }) =>
            if int_ok_exec(a.kind) && int_ok_exec(b.kind) {
                let m: u128 = match op {
                    ArithOp::Mul => {
                        proof {
                            assert(x as int * y as int <= 0x8000_0000_0000_0000 * 0x8000_0000_0000_0000) by (nonlinear_arith)
                                requires 0 <= x <= 0x8000_0000_0000_0000, 0 <= y <= 0x8000_0000_0000_0000;
                        }
                        x * y
                    },
                    _ => x + y,
                };
                let ik = match k { NumKind::Int8 => IntKind::Int8, _ => IntKind::Int4 };
                Some(int_result_info_exec(ik, m, nullable))
            } else {
                None
            },
        (NumKind::Numeric, VKind::Num { scale: s1, digits: d1 }, VKind::Num { scale: s2, digits: d2 }) =>
            if num_ok_exec(a.kind) && num_ok_exec(b.kind) {
                match op {
                    ArithOp::Mul => {
                        let s: u32 = s1 + s2;
                        if s > 16383 {
                            None
                        } else {
                            match (d1, d2) {
                                (Some(x), Some(y)) => Some(num_result_info_exec(s, x as u64 + y as u64, nullable)),
                                _ => Some(num_unbounded_info_exec(s, nullable)),
                            }
                        }
                    },
                    _ => {
                        let s = if s1 >= s2 { s1 } else { s2 };
                        match (d1, d2) {
                            (Some(x), Some(y)) => {
                                let da: u64 = x as u64 + (s - s1) as u64;
                                let db: u64 = y as u64 + (s - s2) as u64;
                                Some(num_result_info_exec(s, (if da >= db { da } else { db }) + 1, nullable))
                            },
                            _ => Some(num_unbounded_info_exec(s, nullable)),
                        }
                    },
                }
            } else {
                None
            },
        (NumKind::Numeric, VKind::Num { .. }, VKind::NumAny) | (NumKind::Numeric, VKind::NumAny, VKind::Num { .. })
        | (NumKind::Numeric, VKind::NumAny, VKind::NumAny) => Some(num_any_info_exec(nullable)),
        _ => None,
    }
}

/// Executable `cast_op` (proved equal).
pub fn cast_op_exec(cast: CastOp, a: VClass) -> (r: Option<ExprInfo>)
    ensures r == cast_op(cast, a),
{
    match (cast, a.kind) {
        (_, VKind::NoValue) => Some(null_info_exec()),
        (CastOp::Int4ToInt8, VKind::Int { .. }) => Some(ExprInfo { cls: a, errs: Errs::Never, fits: true }),
        (CastOp::IntToNumeric, VKind::Int { mag }) =>
            if int_ok_exec(a.kind) {
                let d = decimal_digits_exec(mag);
                Some(ExprInfo {
                    cls: VClass { kind: VKind::Num { scale: 0, digits: Some(d) }, nullable: a.nullable },
                    errs: Errs::Never,
                    fits: true,
                })
            } else {
                None
            },
        (CastOp::DateToTimestamp, VKind::Date) => Some(ExprInfo {
            cls: VClass { kind: VKind::Ts, nullable: a.nullable },
            errs: Errs::Only(SqlError::DatetimeFieldOverflow),
            fits: true,
        }),
        _ => None,
    }
}

/// Executable `interval_op` (proved equal).
pub fn interval_op_exec(months: i32, days: i32, micros: i64, a: VClass) -> (r: Option<ExprInfo>)
    ensures r == interval_op(months, days, micros, a),
{
    match a.kind {
        VKind::NoValue => Some(null_info_exec()),
        VKind::Ts => Some(ExprInfo {
            cls: a,
            errs: if months == 0 && days == 0 && micros == 0 { Errs::Never } else { Errs::Only(SqlError::DatetimeFieldOverflow) },
            fits: true,
        }),
        _ => None,
    }
}

/// Executable `text_like` (proved equal).
pub fn text_like_exec(k: VKind) -> (r: bool)
    ensures r == text_like(k),
{
    match k {
        VKind::Text | VKind::NoValue => true,
        _ => false,
    }
}

/// Executable `int_like` (proved equal).
pub fn int_like_exec(k: VKind) -> (r: bool)
    ensures r == int_like(k),
{
    match k {
        VKind::Int { .. } | VKind::NoValue => true,
        _ => false,
    }
}

/// Executable `any_nullable` (proved equal).
pub fn any_nullable_exec(cs: &Vec<VClass>) -> (r: bool)
    ensures r == any_nullable(cs@),
{
    let mut found = false;
    let mut i: usize = 0;
    proof { assert(cs@.take(0) =~= Seq::<VClass>::empty()); }
    while i < cs.len()
        invariant i <= cs.len(), found == any_nullable(cs@.take(i as int)),
        decreases cs.len() - i,
    {
        proof {
            let t = cs@.take(i as int + 1);
            assert(t.drop_last() =~= cs@.take(i as int));
            assert(t.last() == cs@[i as int]);
        }
        found = found || cs[i].nullable;
        i = i + 1;
    }
    proof { assert(cs@.take(cs.len() as int) =~= cs@); }
    found
}

/// `like_safe`: an escape of at most one character and no dangling escape at the end of the pattern.
pub fn like_safe_exec(pattern: &Vec<u8>, escape: &Vec<u8>) -> (r: bool)
    ensures r == like_safe(pattern@, escape@),
{
    let ec = chars_exec(escape);
    if ec.len() > 1 {
        return false;
    }
    let pc = chars_exec(pattern);
    let esc: Option<Vec<u8>> = if ec.len() == 0 { None } else { Some(ec[0].clone()) };
    proof {
        let ecv = chars(escape@);
        assert(ecv == view_chars(ec@));
        if ec.len() > 0 {
            assert(ecv[0] == ec@[0]@);
        }
        assert(escape_of(ecv) == match esc { Some(x) => Some(x@), None => None::<Seq<u8>> });
    }
    let toks = like_tokens_exec(&pc, &esc);
    let ghost gt = view_toks(toks@);
    proof {
        assert(view_chars(pc@) == chars(pattern@));
        assert(gt == like_tokens(chars(pattern@), escape_of(chars(escape@)), 0));
    }
    let mut i: usize = 0;
    proof { assert(gt.take(0) =~= Seq::<LikeTok>::empty()); }
    while i < toks.len()
        invariant
            i <= toks.len(), gt == view_toks(toks@), none_dangling(gt.take(i as int)),
            gt == like_tokens(chars(pattern@), escape_of(chars(escape@)), 0), chars(escape@).len() <= 1,
        decreases toks.len() - i,
    {
        proof {
            let t = gt.take(i as int + 1);
            assert(t.drop_last() =~= gt.take(i as int));
            assert(t.last() == view_tok(toks@[i as int]));
        }
        let dangling = match toks[i] { ETok::Dangling => true, _ => false };
        if dangling {
            proof {
                let t = gt.take(i as int + 1);
                assert(toks@[i as int] is Dangling);
                assert(t.last() is Dangling);
                assert(!none_dangling(t));
                lemma_none_dangling_prefix(gt, i as int + 1);
                assert(!like_safe(pattern@, escape@));
            }
            return false;
        }
        proof {
            let t = gt.take(i as int + 1);
            assert(!(toks@[i as int] is Dangling));
            assert(!(t.last() is Dangling));
        }
        i = i + 1;
    }
    proof { assert(gt.take(toks.len() as int) =~= gt); }
    true
}

/// A dangling token in a prefix is one in the whole sequence.
proof fn lemma_none_dangling_prefix(ts: Seq<LikeTok>, k: int)
    requires 0 <= k <= ts.len(), !none_dangling(ts.take(k)),
    ensures !none_dangling(ts),
    decreases ts.len(),
{
    if k < ts.len() {
        let d = ts.drop_last();
        assert(d.take(k) =~= ts.take(k));
        lemma_none_dangling_prefix(d, k);
    } else {
        assert(ts.take(k) =~= ts);
    }
}

/// Executable `call_op` (proved equal).
pub fn call_op_exec(f: ScalarFn, args: &Vec<EExpr>, cs: &Vec<VClass>) -> (r: Option<ExprInfo>)
    ensures r == call_op(f, view_exprs(args@), cs@),
{
    proof { lemma_view_exprs_index(args@); }
    let nullable = any_nullable_exec(cs);
    match f {
        ScalarFn::Like =>
            if args.len() == 3 && cs.len() == 3 && text_like_exec(cs[0].kind) && text_like_exec(cs[1].kind) && text_like_exec(cs[2].kind) {
                let safe = match (closed_value_exec(&args[1]), closed_value_exec(&args[2])) {
                    (Some(EVal::Text(p)), Some(EVal::Text(e))) => like_safe_exec(&p, &e),
                    _ => false,
                };
                if safe { Some(ExprInfo { cls: VClass { kind: VKind::Bool, nullable }, errs: Errs::Never, fits: true }) } else { None }
            } else {
                None
            },
        ScalarFn::Substring2 =>
            if args.len() == 2 && cs.len() == 2 && text_like_exec(cs[0].kind) && int_like_exec(cs[1].kind) {
                Some(ExprInfo { cls: VClass { kind: VKind::Text, nullable }, errs: Errs::Never, fits: true })
            } else {
                None
            },
        ScalarFn::Substring3 =>
            if args.len() == 3 && cs.len() == 3 && text_like_exec(cs[0].kind) && int_like_exec(cs[1].kind) && int_like_exec(cs[2].kind) {
                let safe = match closed_value_exec(&args[2]) {
                    Some(EVal::Int(n)) => n >= 0,
                    _ => false,
                };
                Some(ExprInfo {
                    cls: VClass { kind: VKind::Text, nullable },
                    errs: if safe { Errs::Never } else { Errs::Only(SqlError::SubstringError) },
                    fits: true,
                })
            } else {
                None
            },
        ScalarFn::ExtractYear | ScalarFn::ExtractMonth | ScalarFn::ExtractDay =>
            if args.len() == 1 && cs.len() == 1 && match cs[0].kind { VKind::Date | VKind::Ts | VKind::NoValue => true, _ => false } {
                Some(ExprInfo { cls: VClass { kind: VKind::Num { scale: 0, digits: None }, nullable }, errs: Errs::Never, fits: true })
            } else {
                None
            },
        ScalarFn::PadBpchar =>
            if args.len() == 2 && cs.len() == 2 && text_like_exec(cs[0].kind) && int_like_exec(cs[1].kind) {
                Some(ExprInfo { cls: VClass { kind: VKind::Text, nullable }, errs: Errs::Never, fits: true })
            } else {
                None
            },
        _ => None,
    }
}

/// Executable `class_join` (proved equal).
pub fn class_join_exec(a: VClass, b: VClass) -> (r: Option<VClass>)
    ensures r == class_join(a, b),
{
    let nullable = a.nullable || b.nullable;
    let kind = match (a.kind, b.kind) {
        (VKind::NoValue, k) => Some(k),
        (k, VKind::NoValue) => Some(k),
        (VKind::Bool, VKind::Bool) => Some(VKind::Bool),
        (VKind::Int { mag: x }, VKind::Int { mag: y }) => Some(VKind::Int { mag: if x >= y { x } else { y } }),
        (VKind::Num { scale: s1, digits: d1 }, VKind::Num { scale: s2, digits: d2 }) =>
            if s1 == s2 {
                Some(VKind::Num {
                    scale: s1,
                    digits: match (d1, d2) {
                        (Some(x), Some(y)) => Some(if x >= y { x } else { y }),
                        _ => None,
                    },
                })
            } else {
                Some(VKind::NumAny)
            },
        (VKind::Num { .. }, VKind::NumAny) | (VKind::NumAny, VKind::Num { .. }) | (VKind::NumAny, VKind::NumAny) => Some(VKind::NumAny),
        (VKind::Date, VKind::Date) => Some(VKind::Date),
        (VKind::Ts, VKind::Ts) => Some(VKind::Ts),
        (VKind::Text, VKind::Text) => Some(VKind::Text),
        _ => None,
    };
    match kind {
        Some(k) => Some(VClass { kind: k, nullable }),
        None => None,
    }
}

/// Executable `comparable` (proved equal).
pub fn comparable_exec(a: VKind, b: VKind) -> (r: bool)
    ensures r == comparable(a, b),
{
    match (a, b) {
        (VKind::NoValue, _) => true,
        (_, VKind::NoValue) => true,
        (VKind::Bool, VKind::Bool) => true,
        (VKind::Int { .. }, VKind::Int { .. }) | (VKind::Int { .. }, VKind::Num { .. }) | (VKind::Int { .. }, VKind::NumAny) => true,
        (VKind::Num { .. }, VKind::Int { .. }) | (VKind::Num { .. }, VKind::Num { .. }) | (VKind::Num { .. }, VKind::NumAny) => true,
        (VKind::NumAny, VKind::Int { .. }) | (VKind::NumAny, VKind::Num { .. }) | (VKind::NumAny, VKind::NumAny) => true,
        (VKind::Date, VKind::Date) | (VKind::Date, VKind::Ts) | (VKind::Ts, VKind::Date) | (VKind::Ts, VKind::Ts) => true,
        (VKind::Text, VKind::Text) => true,
        _ => false,
    }
}

/// Executable `after1` (proved equal).
pub fn after1_exec(a: ExprInfo, op: Option<ExprInfo>) -> (r: Option<ExprInfo>)
    ensures r == after1(a, op),
{
    match op {
        Some(o) => match errs_join_exec(a.errs, o.errs) {
            Some(e) => Some(ExprInfo { cls: o.cls, errs: e, fits: a.fits && o.fits }),
            None => None,
        },
        None => None,
    }
}

/// Executable `after2` (proved equal).
pub fn after2_exec(a: ExprInfo, b: ExprInfo, op: Option<ExprInfo>) -> (r: Option<ExprInfo>)
    ensures r == after2(a, b, op),
{
    match errs_join_exec(a.errs, b.errs) {
        Some(e) => after1_exec(ExprInfo { cls: a.cls, errs: e, fits: a.fits && b.fits }, op),
        None => None,
    }
}

/// Executable `pred_after2` (proved equal).
pub fn pred_after2_exec(a: Errs, b: Errs, fits: bool) -> (r: Option<PredInfo>)
    ensures r == pred_after2(a, b, fits),
{
    match errs_join_exec(a, b) {
        Some(e) => Some(PredInfo { errs: e, fits }),
        None => None,
    }
}

/// Executable `if_info` (proved equal).
pub fn if_info_exec(c: PredInfo, t: ExprInfo, f: ExprInfo) -> (r: Option<ExprInfo>)
    ensures r == if_info(c, t, f),
{
    match (class_join_exec(t.cls, f.cls), errs_join_exec(c.errs, t.errs)) {
        (Some(cls), Some(e1)) => match errs_join_exec(e1, f.errs) {
            Some(e) => Some(ExprInfo { cls, errs: e, fits: c.fits && t.fits && f.fits }),
            None => None,
        },
        _ => None,
    }
}

/// Executable `subquery_info` (proved equal).
pub fn subquery_info_exec(q: &EQueryInfo) -> (r: Option<ExprInfo>)
    ensures r == subquery_info(view_query_info(*q)),
{
    if q.cols.len() == 1 {
        let card = if q.one_row { Errs::Never } else { Errs::Only(SqlError::CardinalityViolation) };
        match errs_join_exec(q.errs, card) {
            Some(e) => Some(ExprInfo { cls: VClass { kind: q.cols[0].kind, nullable: true }, errs: e, fits: q.fits }),
            None => None,
        }
    } else {
        None
    }
}

// ------------------------------------------------------------------------------------- aggregate values

/// Executable `agg_value_info` (proved equal).
pub fn agg_value_info_exec(a: &EAgg, c: VClass) -> (r: Option<ExprInfo>)
    ensures r == agg_value_info(view_agg(*a), c),
    decreases a,
{
    match a {
        EAgg::CountStar | EAgg::Count(_) => Some(ExprInfo {
            cls: VClass { kind: VKind::Int { mag: 0x7fff_ffff_ffff_ffff }, nullable: false },
            errs: Errs::Only(SqlError::NumericValueOutOfRange),
            fits: true,
        }),
        EAgg::Sum { kind, .. } => match (kind, c.kind) {
            (_, VKind::NoValue) => Some(null_info_exec()),
            (NumKind::Int4, VKind::Int { .. }) => Some(ExprInfo {
                cls: VClass { kind: VKind::Int { mag: 0x8000_0000_0000_0000 }, nullable: true },
                errs: Errs::Only(SqlError::NumericValueOutOfRange),
                fits: false,
            }),
            (NumKind::Int8, VKind::Int { .. }) => Some(num_unbounded_info_exec(0, true)),
            (NumKind::Numeric, VKind::Num { scale, .. }) =>
                if scale <= 16383 { Some(num_unbounded_info_exec(scale, true)) } else { None },
            (NumKind::Numeric, VKind::NumAny) => Some(num_any_info_exec(true)),
            _ => None,
        },
        EAgg::Avg { kind, .. } => match (kind, c.kind) {
            (_, VKind::NoValue) => Some(null_info_exec()),
            (NumKind::Int4, VKind::Int { .. }) | (NumKind::Int8, VKind::Int { .. })
            | (NumKind::Numeric, VKind::Num { .. }) | (NumKind::Numeric, VKind::NumAny) => Some(num_any_info_exec(true)),
            _ => None,
        },
        EAgg::Min(_) | EAgg::Max(_) => match c.kind {
            VKind::Bool => None,
            _ => Some(ExprInfo { cls: VClass { kind: c.kind, nullable: true }, errs: Errs::Never, fits: true }),
        },
        EAgg::DistinctAgg(inner) => agg_value_info_exec(inner, c),
    }
}

/// Executable `aggs_value_info` (proved equal).
pub fn aggs_value_info_exec(aggs: &Vec<EAgg>, cs: &Vec<VClass>) -> (r: Option<EListInfo>)
    ensures view_list_opt(r) == aggs_value_info(view_aggs(aggs@), cs@),
{
    let ghost ga = view_aggs(aggs@);
    proof { lemma_view_aggs_index(aggs@); }
    if aggs.len() != cs.len() {
        return None;
    }
    let mut classes: Vec<VClass> = Vec::new();
    let mut errs = Errs::Never;
    let mut fits = true;
    let mut i: usize = 0;
    proof {
        assert(ga.take(0) =~= Seq::<Agg>::empty());
        assert(cs@.take(0) =~= Seq::<VClass>::empty());
        assert(classes@ =~= Seq::<VClass>::empty());
    }
    while i < aggs.len()
        invariant
            i <= aggs.len(), aggs.len() == cs.len(), ga == view_aggs(aggs@), ga.len() == aggs.len(),
            forall|j: int| 0 <= j < aggs.len() ==> #[trigger] ga[j] == view_agg(aggs@[j]),
            aggs_value_info(ga.take(i as int), cs@.take(i as int)) == Some(ListInfo { classes: classes@, errs, fits }),
        decreases aggs.len() - i,
    {
        proof {
            let (t, tc) = (ga.take(i as int + 1), cs@.take(i as int + 1));
            assert(t.drop_last() =~= ga.take(i as int));
            assert(tc.drop_last() =~= cs@.take(i as int));
            assert(t.last() == view_agg(aggs@[i as int]));
            assert(tc.last() == cs@[i as int]);
        }
        let x = match agg_value_info_exec(&aggs[i], cs[i]) {
            Some(x) => x,
            None => {
                proof { lemma_aggs_value_prefix_none(ga, cs@, i as int + 1); }
                return None;
            },
        };
        match errs_join_exec(errs, x.errs) {
            Some(e) => {
                classes.push(x.cls);
                errs = e;
                fits = fits && x.fits;
            },
            None => {
                proof { lemma_aggs_value_prefix_none(ga, cs@, i as int + 1); }
                return None;
            },
        }
        i = i + 1;
    }
    proof {
        assert(ga.take(aggs.len() as int) =~= ga);
        assert(cs@.take(cs.len() as int) =~= cs@);
    }
    Some(EListInfo { classes, errs, fits })
}

/// An unclassified prefix leaves the whole list unclassified.
proof fn lemma_aggs_value_prefix_none(aggs: Seq<Agg>, cs: Seq<VClass>, k: int)
    requires 0 <= k <= aggs.len(), aggs.len() == cs.len(), aggs_value_info(aggs.take(k), cs.take(k)) is None,
    ensures aggs_value_info(aggs, cs) is None,
    decreases aggs.len(),
{
    if k < aggs.len() {
        let (d, dc) = (aggs.drop_last(), cs.drop_last());
        assert(d.take(k) =~= aggs.take(k));
        assert(dc.take(k) =~= cs.take(k));
        lemma_aggs_value_prefix_none(d, dc, k);
    } else {
        assert(aggs.take(k) =~= aggs);
        assert(cs.take(k) =~= cs);
    }
}

} // verus!
