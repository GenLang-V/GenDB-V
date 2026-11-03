//! L3, static classes: the spec checker (engine toolkit; nothing here names a query, a table or a column).
//!
//! One static analysis over the AST decides three classes a planner needs:
//! - **totality** (hazard H1): a node never raises an SQL error and always stays inside the executable domain
//!   (`fits_*`), on every environment whose values lie in given classes, so a plan may skip it on some rows or
//!   evaluate it on more rows (`expr_total`, `pred_total`, `query_total`);
//! - **uniformity** (H1): every SQL error the node can raise is one code, so a plan may reorder rows
//!   (`expr_uniform`, `pred_uniform`, `query_uniform`; totality is the error-free case);
//! - **scale-exactness** (H2): all values of a node have one exact type (numerics one scale), so SQL "not
//!   distinct" is structural equality and representatives do not depend on order (`expr_exact`, `query_exact`).
//!
//! The analysis (`expr_info`, `pred_info`, `query_info`, with the list and aggregate forms) computes for every
//! node a value class (`VClass`: a kind with magnitude or digit bounds, and NULL-ability; for queries one class
//! per output column), the errors it may raise (`Errs`: none, or one code) and whether it always fits the
//! executable domain. Closed (literal-only, `link::expr::closed_expr`) subexpressions are hoisted: they are
//! evaluated once (`closed_value`) and treated as a constant of their value's class, so `$1 + INTERVAL '1' YEAR`
//! is a constant timestamp. A closed subexpression that raises (or leaves the domain) leaves the node
//! unclassified (`None`): its error must be raised only if a row reaches it (`engine_link::decorrelate`).
//!
//! Unclassified (`None`) means the analysis does not decide the node; it is never a claim about the node.
//! Unsupported on purpose: division (`DivInt4`, `DivInt8`, `DivNumeric`), LIKE whose pattern or escape is not a
//! constant that can never raise (`like_safe`), operands whose classes exceed the analysis bounds (integer
//! magnitudes above `2^63`, numeric scales above 16383 or digit bounds above 147455), and ill-typed combinations
//! (`TypeError`).
//!
//! Soundness: `engine_link::classes_sound`. Executable checker proved equal to this one:
//! `engine_link::classes_exec`.
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
use crate::exec::domain::*;
use crate::link::expr::{closed_expr, closed_db};

verus! {

// ------------------------------------------------------------------------------------- value classes

/// The kind of the non-NULL values of a class.
#[derive(Clone, Copy)]
pub enum VKind {
    Bool,
    /// Integers `x` with `|x| <= mag`.
    Int { mag: u128 },
    /// Numerics of exactly this scale; with `digits == Some(d)`, coefficients `|c| < 10^d`.
    Num { scale: u32, digits: Option<u32> },
    /// Numerics of any scale (results of AVG; not scale-exact).
    NumAny,
    /// Valid dates (`date_valid`).
    Date,
    /// Valid timestamps (`ts_valid`).
    Ts,
    Text,
    /// No non-NULL value: the class is `{NULL}` when nullable, empty otherwise.
    NoValue,
}

/// A set of values: a kind, and whether NULL is in it.
#[derive(Clone, Copy)]
pub struct VClass {
    pub kind: VKind,
    pub nullable: bool,
}

/// The SQL errors a node may raise: none, or the one code `Only(e)`.
#[derive(Clone, Copy)]
pub enum Errs {
    Never,
    Only(SqlError),
}

/// Analysis of an expression (or a condition's operand): the class of its values, its errors, and whether it
/// always fits the executable domain.
#[derive(Clone, Copy)]
pub struct ExprInfo {
    pub cls: VClass,
    pub errs: Errs,
    pub fits: bool,
}

/// Analysis of a condition: its errors and whether it always fits the executable domain.
#[derive(Clone, Copy)]
pub struct PredInfo {
    pub errs: Errs,
    pub fits: bool,
}

/// Analysis of a list of expressions or aggregate arguments: one class per element.
pub struct ListInfo {
    pub classes: Seq<VClass>,
    pub errs: Errs,
    pub fits: bool,
}

/// Analysis of a query: one class per output column, its errors, whether it always fits the executable domain,
/// and whether it yields at most one row.
pub struct QueryInfo {
    pub cols: Seq<VClass>,
    pub errs: Errs,
    pub fits: bool,
    pub one_row: bool,
}

/// `v` is in class `c`.
pub open spec fn in_class(v: Val, c: VClass) -> bool {
    match v {
        Val::Null => c.nullable,
        Val::Bool(_) => c.kind is Bool,
        Val::Int(x) => match c.kind {
            VKind::Int { mag } => abs(x) <= mag as int,
            _ => false,
        },
        Val::Num { coeff, scale } => match c.kind {
            VKind::Num { scale: s, digits } => scale == s as nat && match digits {
                Some(d) => abs(coeff) < pow10(d as nat),
                None => true,
            },
            VKind::NumAny => true,
            _ => false,
        },
        Val::Date(d) => c.kind is Date && date_valid(d),
        Val::Ts(t) => c.kind is Ts && ts_valid(t),
        Val::Text(_) => c.kind is Text,
    }
}

/// A row of one value per class, each in its class.
pub open spec fn row_in(r: Row, cs: Seq<VClass>) -> bool {
    r.len() == cs.len() && forall|i: int| 0 <= i < r.len() ==> in_class(#[trigger] r[i], cs[i])
}

/// Every row is `row_in`.
pub open spec fn rows_in(rows: Seq<Row>, cs: Seq<VClass>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> row_in(#[trigger] rows[i], cs)
}

/// An outcome raises only errors that `e` allows.
pub open spec fn errs_allow<T>(r: Result<T, SqlError>, e: Errs) -> bool {
    match e {
        Errs::Never => r is Ok,
        Errs::Only(c) => r is Ok || r == Err::<T, SqlError>(c),
    }
}

/// Both error sets in one, if they have at most one code together.
pub open spec fn errs_join(a: Errs, b: Errs) -> Option<Errs> {
    match (a, b) {
        (Errs::Never, _) => Some(b),
        (_, Errs::Never) => Some(a),
        (Errs::Only(x), Errs::Only(y)) => if x == y { Some(a) } else { None },
    }
}

/// A non-NULL class of kind `k`.
pub open spec fn not_null(k: VKind) -> VClass {
    VClass { kind: k, nullable: false }
}

/// Classes made nullable (the right side of a LEFT JOIN).
pub open spec fn nullable_classes(cs: Seq<VClass>) -> Seq<VClass> {
    cs.map_values(|c: VClass| VClass { kind: c.kind, nullable: true })
}

/// Values of class `c` have one exact type (`bridge::equality::same_exact_type`): every kind but `NumAny`.
pub open spec fn class_exact(c: VClass) -> bool {
    !(c.kind is NumAny)
}

/// Every class of the list is exact (recursive, so `by (compute)` decides it).
pub open spec fn classes_exact(cs: Seq<VClass>) -> bool
    decreases cs.len(),
{
    cs.len() == 0 || (class_exact(cs.last()) && classes_exact(cs.drop_last()))
}

// ------------------------------------------------------------------------------------- bounds

/// Largest integer magnitude the analysis accepts (`2^63`: every int8 value).
pub open spec fn int_mag_cap() -> int { 0x8000_0000_0000_0000 }

/// Largest numeric scale the analysis accepts (`spec::limits::numeric_dscale_max`).
pub open spec fn scale_cap() -> int { 16383 }

/// Largest digit bound the analysis accepts (`numeric_int_digits_max() + scale_cap()`).
pub open spec fn digits_cap() -> int { 147455 }

/// Digits of an `i128`-representable coefficient: `|c| < 10^38` fits `i128` (`lemma_pow10_i128_boundary`).
pub open spec fn i128_digits() -> int { 38 }

/// Largest magnitude of a value of integer kind `k` (`2^31` or `2^63`).
pub open spec fn kind_mag(k: IntKind) -> int {
    match k {
        IntKind::Int4 => 0x8000_0000,
        IntKind::Int8 => 0x8000_0000_0000_0000,
    }
}

/// The class's integer magnitude is within the analysis bound.
pub open spec fn int_ok(k: VKind) -> bool {
    match k {
        VKind::Int { mag } => mag as int <= int_mag_cap(),
        _ => false,
    }
}

/// The class's numeric scale and digit bound are within the analysis bounds.
pub open spec fn num_ok(k: VKind) -> bool {
    match k {
        VKind::Num { scale, digits } => scale as int <= scale_cap() && match digits {
            Some(d) => d as int <= digits_cap(),
            None => true,
        },
        _ => false,
    }
}

// ------------------------------------------------------------------------------------- classes of values

/// Class of the values of a declared column (`spec::typing::value_in_column`).
pub open spec fn column_class(c: Column) -> VClass {
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

/// Classes of a table's columns.
pub open spec fn table_classes(t: TableSchema) -> Seq<VClass> {
    t.columns.map_values(|c: Column| column_class(c))
}

/// Class of one constant value (a hoisted closed expression); `None` outside the analysis bounds.
pub open spec fn const_class(v: Val) -> Option<VClass> {
    match v {
        Val::Null => Some(VClass { kind: VKind::NoValue, nullable: true }),
        Val::Bool(_) => Some(not_null(VKind::Bool)),
        Val::Int(x) => if abs(x) <= int_mag_cap() { Some(not_null(VKind::Int { mag: abs(x) as u128 })) } else { None },
        Val::Num { coeff, scale } =>
            if scale <= u32::MAX && decimal_digits(abs(coeff)) <= u32::MAX {
                Some(not_null(VKind::Num { scale: scale as u32, digits: Some(decimal_digits(abs(coeff)) as u32) }))
            } else {
                None
            },
        Val::Date(d) => if date_valid(d) { Some(not_null(VKind::Date)) } else { None },
        Val::Ts(t) => if ts_valid(t) { Some(not_null(VKind::Ts)) } else { None },
        Val::Text(_) => Some(not_null(VKind::Text)),
    }
}

/// The value of a closed expression, evaluated once (empty database and environment), when it succeeds inside
/// the executable domain.
pub open spec fn closed_value(e: Expr) -> Option<Val> {
    if closed_expr(e) && fits_expr(closed_db(), Seq::empty(), e) {
        match eval_expr(closed_db(), Seq::empty(), e) {
            Ok(v) => Some(v),
            Err(_) => None,
        }
    } else {
        None
    }
}

/// A hoisted closed expression: the class of its value, no error, inside the domain.
pub open spec fn closed_info(e: Expr) -> Option<ExprInfo> {
    match closed_value(e) {
        Some(v) => match const_class(v) {
            Some(c) => Some(ExprInfo { cls: c, errs: Errs::Never, fits: true }),
            None => None,
        },
        None => None,
    }
}

// ------------------------------------------------------------------------------------- operators

/// Two kinds can be compared without a type error (`spec::scalar::compare` is `Some` on their values).
pub open spec fn comparable(a: VKind, b: VKind) -> bool {
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

/// An integer result of kind `k` whose exact value has magnitude at most `m`: its class and errors.
pub open spec fn int_result_info(k: IntKind, m: int, nullable: bool) -> ExprInfo {
    if m <= kind_mag(k) - 1 {
        ExprInfo { cls: VClass { kind: VKind::Int { mag: m as u128 }, nullable }, errs: Errs::Never, fits: true }
    } else {
        ExprInfo {
            cls: VClass { kind: VKind::Int { mag: kind_mag(k) as u128 }, nullable },
            errs: Errs::Only(SqlError::NumericValueOutOfRange),
            fits: true,
        }
    }
}

/// A numeric result at scale `s` whose exact coefficient has fewer than `d` digits: its class and errors (the
/// format limit `num_in_range` is `|c| < 10^(131072 + s)`). `fits`: the coefficient fits `i128`.
pub open spec fn num_result_info(s: u32, d: int, nullable: bool) -> ExprInfo {
    let limit = numeric_int_digits_max() + s;
    if d <= limit {
        ExprInfo {
            cls: VClass { kind: VKind::Num { scale: s, digits: Some(d as u32) }, nullable },
            errs: Errs::Never,
            fits: d <= i128_digits(),
        }
    } else {
        ExprInfo {
            cls: VClass { kind: VKind::Num { scale: s, digits: Some(limit as u32) }, nullable },
            errs: Errs::Only(SqlError::NumericValueOutOfRange),
            fits: false,
        }
    }
}

/// A numeric result at scale `s` with no digit bound: in range or 22003.
pub open spec fn num_unbounded_info(s: u32, nullable: bool) -> ExprInfo {
    ExprInfo {
        cls: VClass { kind: VKind::Num { scale: s, digits: Some((numeric_int_digits_max() + s) as u32) }, nullable },
        errs: Errs::Only(SqlError::NumericValueOutOfRange),
        fits: false,
    }
}

/// A numeric result of any scale: 22003 possible, domain unknown.
pub open spec fn num_any_info(nullable: bool) -> ExprInfo {
    ExprInfo {
        cls: VClass { kind: VKind::NumAny, nullable },
        errs: Errs::Only(SqlError::NumericValueOutOfRange),
        fits: false,
    }
}

/// Always NULL.
pub open spec fn null_info() -> ExprInfo {
    ExprInfo { cls: VClass { kind: VKind::NoValue, nullable: true }, errs: Errs::Never, fits: true }
}

/// The operator `-a` at kind `k` on values of class `a` (its own result class, errors and domain).
pub open spec fn neg_op(k: NumKind, a: VClass) -> Option<ExprInfo> {
    match (k, a.kind) {
        (_, VKind::NoValue) => Some(null_info()),
        (NumKind::Int4, VKind::Int { mag }) | (NumKind::Int8, VKind::Int { mag }) =>
            if int_ok(a.kind) { Some(int_result_info(int_kind_of(k), mag as int, a.nullable)) } else { None },
        (NumKind::Numeric, VKind::Num { scale, digits }) =>
            if num_ok(a.kind) {
                match digits {
                    Some(d) => Some(num_result_info(scale, d as int, a.nullable)),
                    None => Some(num_unbounded_info(scale, a.nullable)),
                }
            } else {
                None
            },
        (NumKind::Numeric, VKind::NumAny) => Some(num_any_info(a.nullable)),
        _ => None,
    }
}

/// The operator `a op b` at kind `k` on values of classes `a`, `b`.
pub open spec fn arith_op(op: ArithOp, k: NumKind, a: VClass, b: VClass) -> Option<ExprInfo> {
    let nullable = a.nullable || b.nullable;
    match (k, a.kind, b.kind) {
        (NumKind::Int4, VKind::NoValue, VKind::Int { .. }) | (NumKind::Int4, VKind::Int { .. }, VKind::NoValue)
        | (NumKind::Int4, VKind::NoValue, VKind::NoValue) | (NumKind::Int8, VKind::NoValue, VKind::Int { .. })
        | (NumKind::Int8, VKind::Int { .. }, VKind::NoValue) | (NumKind::Int8, VKind::NoValue, VKind::NoValue)
        | (NumKind::Numeric, VKind::NoValue, VKind::Num { .. }) | (NumKind::Numeric, VKind::Num { .. }, VKind::NoValue)
        | (NumKind::Numeric, VKind::NoValue, VKind::NumAny) | (NumKind::Numeric, VKind::NumAny, VKind::NoValue)
        | (NumKind::Numeric, VKind::NoValue, VKind::NoValue) => Some(null_info()),
        (NumKind::Int4, VKind::Int { mag: x }, VKind::Int { mag: y }) | (NumKind::Int8, VKind::Int { mag: x }, VKind::Int { mag: y }) =>
            if int_ok(a.kind) && int_ok(b.kind) {
                let m = match op { ArithOp::Mul => x as int * y as int, _ => x as int + y as int };
                Some(int_result_info(int_kind_of(k), m, nullable))
            } else {
                None
            },
        (NumKind::Numeric, VKind::Num { scale: s1, digits: d1 }, VKind::Num { scale: s2, digits: d2 }) =>
            if num_ok(a.kind) && num_ok(b.kind) {
                match op {
                    ArithOp::Mul => {
                        let s = s1 as int + s2 as int;
                        if s > scale_cap() {
                            None
                        } else {
                            match (d1, d2) {
                                (Some(x), Some(y)) => Some(num_result_info(s as u32, x as int + y as int, nullable)),
                                _ => Some(num_unbounded_info(s as u32, nullable)),
                            }
                        }
                    },
                    _ => {
                        let s = if s1 >= s2 { s1 } else { s2 };
                        match (d1, d2) {
                            (Some(x), Some(y)) => {
                                let da = x as int + (s as int - s1 as int);
                                let db = y as int + (s as int - s2 as int);
                                Some(num_result_info(s, (if da >= db { da } else { db }) + 1, nullable))
                            },
                            _ => Some(num_unbounded_info(s, nullable)),
                        }
                    },
                }
            } else {
                None
            },
        (NumKind::Numeric, VKind::Num { .. }, VKind::NumAny) | (NumKind::Numeric, VKind::NumAny, VKind::Num { .. })
        | (NumKind::Numeric, VKind::NumAny, VKind::NumAny) => Some(num_any_info(nullable)),
        _ => None,
    }
}

/// Decimal digits of a magnitude (`spec::numeric::decimal_digits`).
pub open spec fn mag_digits(m: u128) -> nat {
    decimal_digits(m as int)
}

/// The cast operator on values of class `a`.
pub open spec fn cast_op(cast: CastOp, a: VClass) -> Option<ExprInfo> {
    match (cast, a.kind) {
        (_, VKind::NoValue) => Some(null_info()),
        (CastOp::Int4ToInt8, VKind::Int { .. }) => Some(ExprInfo { cls: a, errs: Errs::Never, fits: true }),
        (CastOp::IntToNumeric, VKind::Int { mag }) =>
            if int_ok(a.kind) {
                Some(ExprInfo {
                    cls: VClass { kind: VKind::Num { scale: 0, digits: Some(mag_digits(mag) as u32) }, nullable: a.nullable },
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

/// `timestamp + interval` on values of class `a`.
pub open spec fn interval_op(months: i32, days: i32, micros: i64, a: VClass) -> Option<ExprInfo> {
    match a.kind {
        VKind::NoValue => Some(null_info()),
        VKind::Ts => Some(ExprInfo {
            cls: a,
            errs: if months == 0 && days == 0 && micros == 0 { Errs::Never } else { Errs::Only(SqlError::DatetimeFieldOverflow) },
            fits: true,
        }),
        _ => None,
    }
}

/// Text or always NULL.
pub open spec fn text_like(k: VKind) -> bool {
    k is Text || k is NoValue
}

/// Integer or always NULL.
pub open spec fn int_like(k: VKind) -> bool {
    k is Int || k is NoValue
}

/// `none_dangling(ts)` is `bridge::fns::like::no_dangling`, decided by recursion.
pub open spec fn none_dangling(ts: Seq<LikeTok>) -> bool
    decreases ts.len(),
{
    ts.len() == 0 || (!(ts.last() is Dangling) && none_dangling(ts.drop_last()))
}

/// A constant LIKE pattern and escape that can never raise: an escape of at most one character, and no
/// dangling escape at the end of the pattern.
pub open spec fn like_safe(pattern: Seq<u8>, escape: Seq<u8>) -> bool {
    chars(escape).len() <= 1 && none_dangling(like_tokens(chars(pattern), escape_of(chars(escape)), 0))
}

/// The scalar function `f` on arguments `args` of classes `cs` (constant pattern, escape and length arguments
/// are read from their hoisted values). LIKE is classified only with a constant pattern and escape that can
/// never raise (`like_safe`).
/// Some class of the list contains NULL (recursive, so `by (compute)` decides it).
pub open spec fn any_nullable(cs: Seq<VClass>) -> bool
    decreases cs.len(),
{
    cs.len() > 0 && (cs.last().nullable || any_nullable(cs.drop_last()))
}

pub open spec fn call_op(f: ScalarFn, args: Seq<Expr>, cs: Seq<VClass>) -> Option<ExprInfo> {
    let nullable = any_nullable(cs);
    match f {
        ScalarFn::Like =>
            if args.len() == 3 && cs.len() == 3 && text_like(cs[0].kind) && text_like(cs[1].kind) && text_like(cs[2].kind) {
                let safe = match (closed_value(args[1]), closed_value(args[2])) {
                    (Some(Val::Text(p)), Some(Val::Text(e))) => like_safe(p, e),
                    _ => false,
                };
                if safe { Some(ExprInfo { cls: VClass { kind: VKind::Bool, nullable }, errs: Errs::Never, fits: true }) } else { None }
            } else {
                None
            },
        ScalarFn::Substring2 =>
            if args.len() == 2 && cs.len() == 2 && text_like(cs[0].kind) && int_like(cs[1].kind) {
                Some(ExprInfo { cls: VClass { kind: VKind::Text, nullable }, errs: Errs::Never, fits: true })
            } else {
                None
            },
        ScalarFn::Substring3 =>
            if args.len() == 3 && cs.len() == 3 && text_like(cs[0].kind) && int_like(cs[1].kind) && int_like(cs[2].kind) {
                let safe = match closed_value(args[2]) {
                    Some(Val::Int(n)) => n >= 0,
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
            if args.len() == 1 && cs.len() == 1 && (cs[0].kind is Date || cs[0].kind is Ts || cs[0].kind is NoValue) {
                Some(ExprInfo { cls: VClass { kind: VKind::Num { scale: 0, digits: None }, nullable }, errs: Errs::Never, fits: true })
            } else {
                None
            },
        ScalarFn::PadBpchar =>
            if args.len() == 2 && cs.len() == 2 && text_like(cs[0].kind) && int_like(cs[1].kind) {
                Some(ExprInfo { cls: VClass { kind: VKind::Text, nullable }, errs: Errs::Never, fits: true })
            } else {
                None
            },
        _ => None,
    }
}

/// The class of a value of either class (CASE branches), if the kinds are compatible.
pub open spec fn class_join(a: VClass, b: VClass) -> Option<VClass> {
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

/// A node whose child (analysis `a`) is evaluated first, then the operator (analysis `op`).
pub open spec fn after1(a: ExprInfo, op: Option<ExprInfo>) -> Option<ExprInfo> {
    match op {
        Some(o) => match errs_join(a.errs, o.errs) {
            Some(e) => Some(ExprInfo { cls: o.cls, errs: e, fits: a.fits && o.fits }),
            None => None,
        },
        None => None,
    }
}

/// A node whose two children are evaluated first, then the operator.
pub open spec fn after2(a: ExprInfo, b: ExprInfo, op: Option<ExprInfo>) -> Option<ExprInfo> {
    match errs_join(a.errs, b.errs) {
        Some(e) => after1(ExprInfo { cls: a.cls, errs: e, fits: a.fits && b.fits }, op),
        None => None,
    }
}

/// A condition built from two parts evaluated in turn.
pub open spec fn pred_after2(a: Errs, b: Errs, fits: bool) -> Option<PredInfo> {
    match errs_join(a, b) {
        Some(e) => Some(PredInfo { errs: e, fits }),
        None => None,
    }
}

/// CASE: the condition, then one branch.
pub open spec fn if_info(c: PredInfo, t: ExprInfo, f: ExprInfo) -> Option<ExprInfo> {
    match (class_join(t.cls, f.cls), errs_join(c.errs, t.errs)) {
        (Some(cls), Some(e1)) => match errs_join(e1, f.errs) {
            Some(e) => Some(ExprInfo { cls, errs: e, fits: c.fits && t.fits && f.fits }),
            None => None,
        },
        _ => None,
    }
}

/// A scalar subquery over a query of one column: NULL on no row, 21000 on more than one.
pub open spec fn subquery_info(q: QueryInfo) -> Option<ExprInfo> {
    if q.cols.len() == 1 {
        let card = if q.one_row { Errs::Never } else { Errs::Only(SqlError::CardinalityViolation) };
        match errs_join(q.errs, card) {
            Some(e) => Some(ExprInfo { cls: VClass { kind: q.cols[0].kind, nullable: true }, errs: e, fits: q.fits }),
            None => None,
        }
    } else {
        None
    }
}

// ------------------------------------------------------------------------------------- aggregate values

/// The value of aggregate `a` over argument values of class `c` (any number of them): its class, its errors
/// (COUNT, SUM and AVG raise 22003 beyond their ranges) and whether it always fits the executable domain (SUM and
/// AVG need the absolute-mass condition, so they do not).
pub open spec fn agg_value_info(a: Agg, c: VClass) -> Option<ExprInfo>
    decreases a,
{
    match a {
        Agg::CountStar | Agg::Count(_) => Some(ExprInfo {
            cls: not_null(VKind::Int { mag: 0x7fff_ffff_ffff_ffff }),
            errs: Errs::Only(SqlError::NumericValueOutOfRange),
            fits: true,
        }),
        Agg::Sum { kind, arg } => match (kind, c.kind) {
            (_, VKind::NoValue) => Some(null_info()),
            (NumKind::Int4, VKind::Int { .. }) => Some(ExprInfo {
                cls: VClass { kind: VKind::Int { mag: 0x8000_0000_0000_0000 }, nullable: true },
                errs: Errs::Only(SqlError::NumericValueOutOfRange),
                fits: false,
            }),
            (NumKind::Int8, VKind::Int { .. }) => Some(num_unbounded_info(0, true)),
            (NumKind::Numeric, VKind::Num { scale, .. }) =>
                if scale as int <= scale_cap() { Some(num_unbounded_info(scale, true)) } else { None },
            (NumKind::Numeric, VKind::NumAny) => Some(num_any_info(true)),
            _ => None,
        },
        Agg::Avg { kind, arg } => match (kind, c.kind) {
            (_, VKind::NoValue) => Some(null_info()),
            (NumKind::Int4, VKind::Int { .. }) | (NumKind::Int8, VKind::Int { .. })
            | (NumKind::Numeric, VKind::Num { .. }) | (NumKind::Numeric, VKind::NumAny) => Some(num_any_info(true)),
            _ => None,
        },
        Agg::Min(_) | Agg::Max(_) => if c.kind is Bool {
            None
        } else {
            Some(ExprInfo { cls: VClass { kind: c.kind, nullable: true }, errs: Errs::Never, fits: true })
        },
        Agg::DistinctAgg(inner) => agg_value_info(*inner, c),
    }
}

/// `agg_value_info` of every aggregate, over the argument classes `cs` (one per aggregate).
pub open spec fn aggs_value_info(aggs: Seq<Agg>, cs: Seq<VClass>) -> Option<ListInfo>
    decreases aggs.len(),
{
    if aggs.len() != cs.len() {
        None
    } else if aggs.len() == 0 {
        Some(ListInfo { classes: Seq::empty(), errs: Errs::Never, fits: true })
    } else {
        match (aggs_value_info(aggs.drop_last(), cs.drop_last()), agg_value_info(aggs.last(), cs.last())) {
            (Some(l), Some(x)) => match errs_join(l.errs, x.errs) {
                Some(e) => Some(ListInfo { classes: l.classes.push(x.cls), errs: e, fits: l.fits && x.fits }),
                None => None,
            },
            _ => None,
        }
    }
}

// ------------------------------------------------------------------------------------- the analysis

/// Analysis of an expression under environment classes `env` (`ctx ++ row`).
pub open spec fn expr_info(schema: Schema, env: Seq<VClass>, e: Expr) -> Option<ExprInfo>
    decreases e,
{
    if closed_expr(e) {
        closed_info(e)
    } else {
        match e {
            Expr::Col(i) => if i < env.len() { Some(ExprInfo { cls: env[i as int], errs: Errs::Never, fits: true }) } else { None },
            Expr::Lit(_) => None,
            Expr::Neg { kind, arg } => match expr_info(schema, env, *arg) {
                Some(a) => after1(a, neg_op(kind, a.cls)),
                None => None,
            },
            Expr::Arith { op, kind, a, b } => match (expr_info(schema, env, *a), expr_info(schema, env, *b)) {
                (Some(x), Some(y)) => after2(x, y, arith_op(op, kind, x.cls, y.cls)),
                _ => None,
            },
            Expr::Cast { cast, arg } => match expr_info(schema, env, *arg) {
                Some(a) => after1(a, cast_op(cast, a.cls)),
                None => None,
            },
            Expr::AddInterval { arg, months, days, micros } => match expr_info(schema, env, *arg) {
                Some(a) => after1(a, interval_op(months, days, micros, a.cls)),
                None => None,
            },
            Expr::Call { f, args } => match exprs_info(schema, env, args) {
                Some(l) => after1(ExprInfo { cls: not_null(VKind::NoValue), errs: l.errs, fits: l.fits }, call_op(f, args, l.classes)),
                None => None,
            },
            Expr::If { cond, then_e, else_e } =>
                match (pred_info(schema, env, *cond), expr_info(schema, env, *then_e), expr_info(schema, env, *else_e)) {
                    (Some(c), Some(t), Some(f)) => if_info(c, t, f),
                    _ => None,
                },
            Expr::Subquery(q) => match query_info(schema, env, *q) {
                Some(qi) => subquery_info(qi),
                None => None,
            },
        }
    }
}

/// Analysis of a list of expressions (left to right).
pub open spec fn exprs_info(schema: Schema, env: Seq<VClass>, es: Seq<Expr>) -> Option<ListInfo>
    decreases es,
{
    if es.len() == 0 {
        Some(ListInfo { classes: Seq::empty(), errs: Errs::Never, fits: true })
    } else {
        match (exprs_info(schema, env, es.drop_last()), expr_info(schema, env, es.last())) {
            (Some(l), Some(x)) => match errs_join(l.errs, x.errs) {
                Some(e) => Some(ListInfo { classes: l.classes.push(x.cls), errs: e, fits: l.fits && x.fits }),
                None => None,
            },
            _ => None,
        }
    }
}

/// Analysis of a condition under environment classes `env`.
pub open spec fn pred_info(schema: Schema, env: Seq<VClass>, p: Pred) -> Option<PredInfo>
    decreases p,
{
    match p {
        Pred::Cmp { op, a, b } => match (expr_info(schema, env, a), expr_info(schema, env, b)) {
            (Some(x), Some(y)) =>
                if comparable(x.cls.kind, y.cls.kind) { pred_after2(x.errs, y.errs, x.fits && y.fits) } else { None },
            _ => None,
        },
        Pred::And(a, b) => match (pred_info(schema, env, *a), pred_info(schema, env, *b)) {
            (Some(x), Some(y)) => pred_after2(x.errs, y.errs, x.fits && y.fits),
            _ => None,
        },
        Pred::Or(a, b) => match (pred_info(schema, env, *a), pred_info(schema, env, *b)) {
            (Some(x), Some(y)) => pred_after2(x.errs, y.errs, x.fits && y.fits),
            _ => None,
        },
        Pred::Not(a) => pred_info(schema, env, *a),
        Pred::IsNull(e) => match expr_info(schema, env, e) {
            Some(x) => Some(PredInfo { errs: x.errs, fits: x.fits }),
            None => None,
        },
        Pred::OfBool(e) => match expr_info(schema, env, e) {
            Some(x) => if x.cls.kind is Bool || x.cls.kind is NoValue { Some(PredInfo { errs: x.errs, fits: x.fits }) } else { None },
            None => None,
        },
        Pred::Exists(q) => match query_info(schema, env, *q) {
            Some(qi) => Some(PredInfo { errs: qi.errs, fits: qi.fits }),
            None => None,
        },
        Pred::AnyCmp { op, e, q } => match (expr_info(schema, env, e), query_info(schema, env, *q)) {
            (Some(x), Some(qi)) =>
                if qi.cols.len() == 1 && comparable(x.cls.kind, qi.cols[0].kind) {
                    pred_after2(x.errs, qi.errs, x.fits && qi.fits)
                } else {
                    None
                },
            _ => None,
        },
    }
}

/// Analysis of one aggregate's argument (COUNT(*) has none; its NULL stand-in is always NULL).
pub open spec fn agg_arg_info(schema: Schema, env: Seq<VClass>, a: Agg) -> Option<ExprInfo>
    decreases a,
{
    match a {
        Agg::CountStar => Some(null_info()),
        Agg::Count(e) => expr_info(schema, env, e),
        Agg::Sum { kind, arg } => expr_info(schema, env, arg),
        Agg::Min(e) => expr_info(schema, env, e),
        Agg::Max(e) => expr_info(schema, env, e),
        Agg::Avg { kind, arg } => expr_info(schema, env, arg),
        Agg::DistinctAgg(inner) => agg_arg_info(schema, env, *inner),
    }
}

/// Analysis of the arguments of a list of aggregates (left to right).
pub open spec fn aggs_arg_info(schema: Schema, env: Seq<VClass>, aggs: Seq<Agg>) -> Option<ListInfo>
    decreases aggs,
{
    if aggs.len() == 0 {
        Some(ListInfo { classes: Seq::empty(), errs: Errs::Never, fits: true })
    } else {
        match (aggs_arg_info(schema, env, aggs.drop_last()), agg_arg_info(schema, env, aggs.last())) {
            (Some(l), Some(x)) => match errs_join(l.errs, x.errs) {
                Some(e) => Some(ListInfo { classes: l.classes.push(x.cls), errs: e, fits: l.fits && x.fits }),
                None => None,
            },
            _ => None,
        }
    }
}

/// Errors of three parts evaluated in turn.
pub open spec fn errs_join3(a: Errs, b: Errs, c: Errs) -> Option<Errs> {
    match errs_join(a, b) {
        Some(x) => errs_join(x, c),
        None => None,
    }
}

/// Analysis of a query under context classes `ctx`.
pub open spec fn query_info(schema: Schema, ctx: Seq<VClass>, q: Query) -> Option<QueryInfo>
    decreases q,
{
    match q {
        Query::Table(t) =>
            if t < schema.len() {
                Some(QueryInfo { cols: table_classes(schema[t as int]), errs: Errs::Never, fits: true, one_row: false })
            } else {
                None
            },
        Query::Filter { pred, input } => match query_info(schema, ctx, *input) {
            Some(i) => match pred_info(schema, ctx + i.cols, pred) {
                Some(p) => match errs_join(i.errs, p.errs) {
                    Some(e) => Some(QueryInfo { cols: i.cols, errs: e, fits: i.fits && p.fits, one_row: i.one_row }),
                    None => None,
                },
                None => None,
            },
            None => None,
        },
        Query::Project { exprs, input } => match query_info(schema, ctx, *input) {
            Some(i) => match exprs_info(schema, ctx + i.cols, exprs) {
                Some(l) => match errs_join(i.errs, l.errs) {
                    Some(e) => Some(QueryInfo { cols: l.classes, errs: e, fits: i.fits && l.fits, one_row: i.one_row }),
                    None => None,
                },
                None => None,
            },
            None => None,
        },
        Query::Product { left, right } => match (query_info(schema, ctx, *left), query_info(schema, ctx, *right)) {
            (Some(l), Some(r)) => match errs_join(l.errs, r.errs) {
                Some(e) => Some(QueryInfo { cols: l.cols + r.cols, errs: e, fits: l.fits && r.fits, one_row: l.one_row && r.one_row }),
                None => None,
            },
            _ => None,
        },
        Query::LeftJoin { left, right, on } => match (query_info(schema, ctx, *left), query_info(schema, ctx, *right)) {
            (Some(l), Some(r)) => match pred_info(schema, ctx + l.cols + r.cols, on) {
                Some(p) => match errs_join3(l.errs, r.errs, p.errs) {
                    Some(e) => Some(QueryInfo {
                        cols: l.cols + nullable_classes(r.cols),
                        errs: e,
                        fits: l.fits && r.fits && p.fits && r.cols.len() <= usize::MAX,
                        one_row: false,
                    }),
                    None => None,
                },
                None => None,
            },
            _ => None,
        },
        Query::Aggregate { aggs, input } => match query_info(schema, ctx, *input) {
            Some(i) => match aggs_arg_info(schema, ctx + i.cols, aggs) {
                Some(a) => match aggs_value_info(aggs, a.classes) {
                    Some(v) => match errs_join3(i.errs, a.errs, v.errs) {
                        Some(e) => Some(QueryInfo { cols: v.classes, errs: e, fits: i.fits && a.fits && v.fits, one_row: true }),
                        None => None,
                    },
                    None => None,
                },
                None => None,
            },
            None => None,
        },
        Query::GroupBy { keys, aggs, input } => match query_info(schema, ctx, *input) {
            Some(i) => match (exprs_info(schema, ctx + i.cols, keys), aggs_arg_info(schema, ctx + i.cols, aggs)) {
                (Some(k), Some(a)) => match aggs_value_info(aggs, a.classes) {
                    Some(v) => match errs_join3(i.errs, k.errs, a.errs) {
                        Some(e1) => match errs_join(e1, v.errs) {
                            Some(e) => Some(QueryInfo {
                                cols: k.classes + v.classes,
                                errs: e,
                                fits: i.fits && k.fits && a.fits && v.fits,
                                one_row: false,
                            }),
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                },
                _ => None,
            },
            None => None,
        },
        Query::Distinct(input) => query_info(schema, ctx, *input),
    }
}

// ------------------------------------------------------------------------------------- the three classes

/// Totality (H1): never an SQL error, always inside the executable domain.
pub open spec fn expr_total(schema: Schema, env: Seq<VClass>, e: Expr) -> bool {
    expr_info(schema, env, e) matches Some(i) && i.errs is Never && i.fits
}

pub open spec fn pred_total(schema: Schema, env: Seq<VClass>, p: Pred) -> bool {
    pred_info(schema, env, p) matches Some(i) && i.errs is Never && i.fits
}

pub open spec fn query_total(schema: Schema, ctx: Seq<VClass>, q: Query) -> bool {
    query_info(schema, ctx, q) matches Some(i) && i.errs is Never && i.fits
}

/// The errors allow only `code` (or none).
pub open spec fn errs_only(e: Errs, code: SqlError) -> bool {
    e is Never || e == Errs::Only(code)
}

/// Uniformity (H1): every SQL error is `code`.
pub open spec fn expr_uniform(schema: Schema, env: Seq<VClass>, e: Expr, code: SqlError) -> bool {
    expr_info(schema, env, e) matches Some(i) && errs_only(i.errs, code)
}

pub open spec fn pred_uniform(schema: Schema, env: Seq<VClass>, p: Pred, code: SqlError) -> bool {
    pred_info(schema, env, p) matches Some(i) && errs_only(i.errs, code)
}

pub open spec fn query_uniform(schema: Schema, ctx: Seq<VClass>, q: Query, code: SqlError) -> bool {
    query_info(schema, ctx, q) matches Some(i) && errs_only(i.errs, code)
}

/// Scale-exactness (H2): every value has one exact type.
pub open spec fn expr_exact(schema: Schema, env: Seq<VClass>, e: Expr) -> bool {
    expr_info(schema, env, e) matches Some(i) && class_exact(i.cls)
}

pub open spec fn exprs_exact(schema: Schema, env: Seq<VClass>, es: Seq<Expr>) -> bool {
    exprs_info(schema, env, es) matches Some(l) && classes_exact(l.classes)
}

pub open spec fn query_exact(schema: Schema, ctx: Seq<VClass>, q: Query) -> bool {
    query_info(schema, ctx, q) matches Some(i) && classes_exact(i.cols)
}

} // verus!
