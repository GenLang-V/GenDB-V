// FRAMEWORK FILE: the AST byte codec of every GenDB engine crate (`runtime/verus/engine_codec.rs`, assembled as
// `crate::gendb_ast_codec` by `gendb_verification::obligations::engine_crate_files`). Engine crates only: it is in no
// storage's dependency closure, so admitted storages are unaffected by it.
//
// An engine call receives its statement as bytes (the host encoder `gendb_frontend::engine_encode` writes them from
// the translated, bound AST document). This file fixes what the bytes mean and how they are read and echoed:
//
// - `decode_spec(b)`: the meaning of the bytes, a TRUSTED DEFINITION (like the SQLSpec `spec` definitions; trusted
//   item `ast_decode_definition`). It is a total, deterministic prefix decoding of the constructors of
//   `gendb-sql-ast-v1` (SQLSpec `spec::ast`), returning `None` for every byte string that is not exactly one encoded
//   `OrderedQuery`. The engine entry's claim is stated for `decode_spec(ast)`.
// - `decode_query(b)`: the executable decoder, VERIFIED to return `Some(q)` with `view_ordered(q) == decode_spec(b)`
//   exactly when `decode_spec(b)` is `Some`.
// - `render_spec(q)` / `render_query(q)`: the echo text of a decoded statement, the canonical s-expression of the
//   evaluator's echo grammar (`gendb_sqlspec::evaluator::echo_text`, mirrored by the evaluator shim
//   `sqlspec/interpreter/host/shim.rs`). `render_query` is VERIFIED equal to `render_spec`. The host renders its own
//   AST document in the same grammar and compares (translation validation of the host encoder; trusted item
//   `engine_echo`).
//
// Byte format `gendb-engine-ast-v1` (all integers little-endian; signed ones two's complement):
//
//   ast      := "GSQLAST1" ordered                       (the whole input; nothing may follow)
//   ordered  := query  u32:n key*n  limit  u64:offset    (OrderedQuery fields in schema order)
//   key      := u32:col  bool:desc  bool:nulls_first
//   limit    := 0x00 | 0x01 u64
//   query    := 0 u32:table | 1 pred query | 2 u32:n expr*n query | 3 query query | 4 query query pred
//             | 5 u32:n agg*n query | 6 u32:n expr*n u32:m agg*m query | 7 query
//               (Table, Filter, Project, Product, LeftJoin, Aggregate, GroupBy, Distinct)
//   expr     := 0 u32:col | 1 lit | 2 numkind expr | 3 arithop numkind expr expr | 4 castop expr
//             | 5 expr i32:months i32:days i64:micros | 6 scalarfn u32:n expr*n | 7 pred expr expr | 8 query
//               (Col, Lit, Neg, Arith, Cast, AddInterval, Call, If, Subquery)
//   pred     := 0 cmpop expr expr | 1 pred pred | 2 pred pred | 3 pred | 4 expr | 5 expr | 6 query
//             | 7 cmpop expr query
//               (Cmp, And, Or, Not, IsNull, OfBool, Exists, AnyCmp)
//   agg      := 0 | 1 expr | 2 numkind expr | 3 expr | 4 expr | 5 numkind expr | 6 agg
//               (CountStar, Count, Sum, Min, Max, Avg, DistinctAgg)
//   lit      := 0 scalarty | 1 bool | 2 i64 intkind | 3 i128:coeff u32:scale | 4 i32:y i32:m i32:d | 5 u32:n byte*n
//               (Null, Bool, Int, Num, Date, Text)
//   scalarty := 0 | 1 | 2 | 3 u32:scale | 4 | 5 | 6    (Bool, Int4, Int8, Numeric, Date, Timestamp, Text)
//   bool     := 0x00 | 0x01
//   enums    := one byte, the position in the AST schema's enum list (IntKind, NumKind, ArithOp, CmpOp, CastOp,
//               ScalarFn of `frontend/ast/ast_schema.json`); any other byte is undecodable.
//
// Fields follow the AST schema's field order. Column, table and ORDER BY positions are u32 (the host encoder refuses
// larger ones). No `assume`, `admit` or `external_body`; checked by Verus with `--no-cheating` in the engine crate.
use vstd::prelude::*;
use crate::spec::types::ScalarTy;
use crate::spec::int::IntKind;
use crate::spec::scalar::{ArithOp, CastOp, CmpOp, NumKind};
use crate::spec::ast::{Agg, Expr, Literal, OrderKey, OrderedQuery, Pred, Query, ScalarFn};
use crate::exec::ast::{
    lemma_view_aggs_index, lemma_view_exprs_index, view_agg, view_aggs, view_expr, view_exprs, view_lit, view_ordered, view_order_key,
    view_order_keys, view_pred, view_query, EAgg, EExpr, ELiteral, EOrderKey, EOrderedQuery, EPred, EQuery,
};

verus! {

// ================================================================================================= byte format

/// The 8-byte magic every AST starts with (`GSQLAST1`).
pub open spec fn ast_magic() -> Seq<u8> {
    seq![b'G', b'S', b'Q', b'L', b'A', b'S', b'T', b'1']
}

/// The bytes left after position `pos` (0 outside `0..=b.len()`): the termination measure of the decoders.
pub open spec fn rest(b: Seq<u8>, pos: int) -> int {
    if 0 <= pos <= b.len() { b.len() - pos } else { 0 }
}

/// `n` bytes start at `pos`.
pub open spec fn in_bounds(b: Seq<u8>, pos: int, n: int) -> bool {
    0 <= pos && 0 <= n && pos + n <= b.len()
}

/// A decoder that started at `pos` (inside the bytes) and ended at `end` consumed at least one byte.
pub open spec fn advances(b: Seq<u8>, pos: int, end: int) -> bool {
    0 <= pos < b.len() && pos < end
}

/// Unsigned value of the 4 bytes at `pos`.
pub open spec fn le4(b: Seq<u8>, pos: int) -> int {
    b[pos] as int + 0x100 * b[pos + 1] as int + 0x1_0000 * b[pos + 2] as int + 0x100_0000 * b[pos + 3] as int
}

/// Unsigned value of the 8 bytes at `pos`.
pub open spec fn le8(b: Seq<u8>, pos: int) -> int {
    le4(b, pos) + 0x1_0000_0000 * le4(b, pos + 4)
}

/// Unsigned value of the 16 bytes at `pos`.
pub open spec fn le16(b: Seq<u8>, pos: int) -> int {
    le8(b, pos) + 0x1_0000_0000_0000_0000 * le8(b, pos + 8)
}

/// Two's complement value of a 32-bit unsigned value.
pub open spec fn s32(u: int) -> int {
    if u < 0x8000_0000 { u } else { u - 0x1_0000_0000 }
}

/// Two's complement value of a 64-bit unsigned value.
pub open spec fn s64(u: int) -> int {
    if u < 0x8000_0000_0000_0000 { u } else { u - 0x1_0000_0000_0000_0000 }
}

/// Two's complement value of a 128-bit unsigned value.
pub open spec fn s128(u: int) -> int {
    if u < 0x8000_0000_0000_0000_0000_0000_0000_0000 { u } else { u - 0x1_0000_0000_0000_0000_0000_0000_0000_0000 }
}

pub open spec fn dec_int_kind(x: u8) -> Option<IntKind> {
    if x == 0 { Some(IntKind::Int4) } else if x == 1 { Some(IntKind::Int8) } else { None }
}

pub open spec fn dec_num_kind(x: u8) -> Option<NumKind> {
    if x == 0 { Some(NumKind::Int4) } else if x == 1 { Some(NumKind::Int8) } else if x == 2 { Some(NumKind::Numeric) } else { None }
}

pub open spec fn dec_arith_op(x: u8) -> Option<ArithOp> {
    if x == 0 { Some(ArithOp::Add) } else if x == 1 { Some(ArithOp::Sub) } else if x == 2 { Some(ArithOp::Mul) } else { None }
}

pub open spec fn dec_cmp_op(x: u8) -> Option<CmpOp> {
    if x == 0 {
        Some(CmpOp::Eq)
    } else if x == 1 {
        Some(CmpOp::Ne)
    } else if x == 2 {
        Some(CmpOp::Lt)
    } else if x == 3 {
        Some(CmpOp::Le)
    } else if x == 4 {
        Some(CmpOp::Gt)
    } else if x == 5 {
        Some(CmpOp::Ge)
    } else {
        None
    }
}

pub open spec fn dec_cast_op(x: u8) -> Option<CastOp> {
    if x == 0 {
        Some(CastOp::Int4ToInt8)
    } else if x == 1 {
        Some(CastOp::IntToNumeric)
    } else if x == 2 {
        Some(CastOp::DateToTimestamp)
    } else {
        None
    }
}

pub open spec fn dec_scalar_fn(x: u8) -> Option<ScalarFn> {
    if x == 0 {
        Some(ScalarFn::DivInt4)
    } else if x == 1 {
        Some(ScalarFn::DivInt8)
    } else if x == 2 {
        Some(ScalarFn::DivNumeric)
    } else if x == 3 {
        Some(ScalarFn::Like)
    } else if x == 4 {
        Some(ScalarFn::Substring2)
    } else if x == 5 {
        Some(ScalarFn::Substring3)
    } else if x == 6 {
        Some(ScalarFn::ExtractYear)
    } else if x == 7 {
        Some(ScalarFn::ExtractMonth)
    } else if x == 8 {
        Some(ScalarFn::ExtractDay)
    } else if x == 9 {
        Some(ScalarFn::PadBpchar)
    } else {
        None
    }
}

/// A `bool` byte.
pub open spec fn dec_bool(x: u8) -> Option<bool> {
    if x == 0 { Some(false) } else if x == 1 { Some(true) } else { None }
}

/// `scalarty` at `pos`, and the position after it.
pub open spec fn dec_scalar_ty(b: Seq<u8>, pos: int) -> Option<(ScalarTy, int)> {
    if !in_bounds(b, pos, 1) {
        None
    } else {
        let (t, p) = (b[pos], pos + 1);
        if t == 0 {
            Some((ScalarTy::Bool, p))
        } else if t == 1 {
            Some((ScalarTy::Int4, p))
        } else if t == 2 {
            Some((ScalarTy::Int8, p))
        } else if t == 3 {
            if in_bounds(b, p, 4) { Some((ScalarTy::Numeric { scale: le4(b, p) as u32 }, p + 4)) } else { None }
        } else if t == 4 {
            Some((ScalarTy::Date, p))
        } else if t == 5 {
            Some((ScalarTy::Timestamp, p))
        } else if t == 6 {
            Some((ScalarTy::Text, p))
        } else {
            None
        }
    }
}

/// `lit` at `pos`, and the position after it.
pub open spec fn dec_lit(b: Seq<u8>, pos: int) -> Option<(Literal, int)> {
    if !in_bounds(b, pos, 1) {
        None
    } else {
        let (t, p) = (b[pos], pos + 1);
        if t == 0 {
            match dec_scalar_ty(b, p) {
                Some((ty, q)) => Some((Literal::Null { ty }, q)),
                None => None,
            }
        } else if t == 1 {
            if in_bounds(b, p, 1) && dec_bool(b[p]) is Some { Some((Literal::Bool(dec_bool(b[p])->Some_0), p + 1)) } else { None }
        } else if t == 2 {
            if in_bounds(b, p, 9) && dec_int_kind(b[p + 8]) is Some {
                Some((Literal::Int { v: s64(le8(b, p)), kind: dec_int_kind(b[p + 8])->Some_0 }, p + 9))
            } else {
                None
            }
        } else if t == 3 {
            if in_bounds(b, p, 20) { Some((Literal::Num { coeff: s128(le16(b, p)), scale: le4(b, p + 16) as nat }, p + 20)) } else { None }
        } else if t == 4 {
            if in_bounds(b, p, 12) {
                Some((Literal::Date { y: s32(le4(b, p)), m: s32(le4(b, p + 4)), d: s32(le4(b, p + 8)) }, p + 12))
            } else {
                None
            }
        } else if t == 5 {
            if in_bounds(b, p, 4) && in_bounds(b, p + 4, le4(b, p)) {
                Some((Literal::Text(b.subrange(p + 4, p + 4 + le4(b, p))), p + 4 + le4(b, p)))
            } else {
                None
            }
        } else {
            None
        }
    }
}

/// `expr` at `pos`, and the position after it.
pub open spec fn dec_expr(b: Seq<u8>, pos: int) -> Option<(Expr, int)>
    decreases rest(b, pos), 0int,
{
    if !in_bounds(b, pos, 1) {
        None
    } else {
        let (t, p) = (b[pos], pos + 1);
        if t == 0 {
            if in_bounds(b, p, 4) { Some((Expr::Col(le4(b, p) as nat), p + 4)) } else { None }
        } else if t == 1 {
            match dec_lit(b, p) {
                Some((l, q)) => Some((Expr::Lit(l), q)),
                None => None,
            }
        } else if t == 2 {
            if in_bounds(b, p, 1) && dec_num_kind(b[p]) is Some {
                match dec_expr(b, p + 1) {
                    Some((arg, q)) => Some((Expr::Neg { kind: dec_num_kind(b[p])->Some_0, arg: Box::new(arg) }, q)),
                    None => None,
                }
            } else {
                None
            }
        } else if t == 3 {
            if in_bounds(b, p, 2) && dec_arith_op(b[p]) is Some && dec_num_kind(b[p + 1]) is Some {
                match dec_expr(b, p + 2) {
                    Some((a, q1)) => if advances(b, pos, q1) {
                        match dec_expr(b, q1) {
                            Some((c, q2)) => Some((
                                Expr::Arith {
                                    op: dec_arith_op(b[p])->Some_0,
                                    kind: dec_num_kind(b[p + 1])->Some_0,
                                    a: Box::new(a),
                                    b: Box::new(c),
                                },
                                q2,
                            )),
                            None => None,
                        }
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            }
        } else if t == 4 {
            if in_bounds(b, p, 1) && dec_cast_op(b[p]) is Some {
                match dec_expr(b, p + 1) {
                    Some((arg, q)) => Some((Expr::Cast { cast: dec_cast_op(b[p])->Some_0, arg: Box::new(arg) }, q)),
                    None => None,
                }
            } else {
                None
            }
        } else if t == 5 {
            match dec_expr(b, p) {
                Some((arg, q)) => if in_bounds(b, q, 16) {
                    Some((
                        Expr::AddInterval {
                            arg: Box::new(arg),
                            months: s32(le4(b, q)) as i32,
                            days: s32(le4(b, q + 4)) as i32,
                            micros: s64(le8(b, q + 8)) as i64,
                        },
                        q + 16,
                    ))
                } else {
                    None
                },
                None => None,
            }
        } else if t == 6 {
            if in_bounds(b, p, 5) && dec_scalar_fn(b[p]) is Some {
                match dec_exprs(b, p + 5, le4(b, p + 1) as nat) {
                    Some((args, q)) => Some((Expr::Call { f: dec_scalar_fn(b[p])->Some_0, args }, q)),
                    None => None,
                }
            } else {
                None
            }
        } else if t == 7 {
            match dec_pred(b, p) {
                Some((cond, q1)) => if advances(b, pos, q1) {
                    match dec_expr(b, q1) {
                        Some((then_e, q2)) => if advances(b, pos, q2) {
                            match dec_expr(b, q2) {
                                Some((else_e, q3)) => Some((
                                    Expr::If { cond: Box::new(cond), then_e: Box::new(then_e), else_e: Box::new(else_e) },
                                    q3,
                                )),
                                None => None,
                            }
                        } else {
                            None
                        },
                        None => None,
                    }
                } else {
                    None
                },
                None => None,
            }
        } else if t == 8 {
            match dec_query(b, p) {
                Some((q, end)) => Some((Expr::Subquery(Box::new(q)), end)),
                None => None,
            }
        } else {
            None
        }
    }
}

/// `n` consecutive `expr`s at `pos`, and the position after them.
pub open spec fn dec_exprs(b: Seq<u8>, pos: int, n: nat) -> Option<(Seq<Expr>, int)>
    decreases rest(b, pos), 1int,
{
    if n == 0 {
        Some((Seq::empty(), pos))
    } else {
        match dec_expr(b, pos) {
            Some((e, q)) => if advances(b, pos, q) {
                match dec_exprs(b, q, (n - 1) as nat) {
                    Some((es, end)) => Some((seq![e] + es, end)),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    }
}

/// `pred` at `pos`, and the position after it.
pub open spec fn dec_pred(b: Seq<u8>, pos: int) -> Option<(Pred, int)>
    decreases rest(b, pos), 0int,
{
    if !in_bounds(b, pos, 1) {
        None
    } else {
        let (t, p) = (b[pos], pos + 1);
        if t == 0 {
            if in_bounds(b, p, 1) && dec_cmp_op(b[p]) is Some {
                match dec_expr(b, p + 1) {
                    Some((a, q1)) => if advances(b, pos, q1) {
                        match dec_expr(b, q1) {
                            Some((c, q2)) => Some((Pred::Cmp { op: dec_cmp_op(b[p])->Some_0, a, b: c }, q2)),
                            None => None,
                        }
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            }
        } else if t == 1 || t == 2 {
            match dec_pred(b, p) {
                Some((x, q1)) => if advances(b, pos, q1) {
                    match dec_pred(b, q1) {
                        Some((y, q2)) => Some((if t == 1 { Pred::And(Box::new(x), Box::new(y)) } else { Pred::Or(Box::new(x), Box::new(y)) }, q2)),
                        None => None,
                    }
                } else {
                    None
                },
                None => None,
            }
        } else if t == 3 {
            match dec_pred(b, p) {
                Some((x, q)) => Some((Pred::Not(Box::new(x)), q)),
                None => None,
            }
        } else if t == 4 || t == 5 {
            match dec_expr(b, p) {
                Some((e, q)) => Some((if t == 4 { Pred::IsNull(e) } else { Pred::OfBool(e) }, q)),
                None => None,
            }
        } else if t == 6 {
            match dec_query(b, p) {
                Some((q, end)) => Some((Pred::Exists(Box::new(q)), end)),
                None => None,
            }
        } else if t == 7 {
            if in_bounds(b, p, 1) && dec_cmp_op(b[p]) is Some {
                match dec_expr(b, p + 1) {
                    Some((e, q1)) => if advances(b, pos, q1) {
                        match dec_query(b, q1) {
                            Some((q, q2)) => Some((Pred::AnyCmp { op: dec_cmp_op(b[p])->Some_0, e, q: Box::new(q) }, q2)),
                            None => None,
                        }
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}

/// `agg` at `pos`, and the position after it.
pub open spec fn dec_agg(b: Seq<u8>, pos: int) -> Option<(Agg, int)>
    decreases rest(b, pos), 0int,
{
    if !in_bounds(b, pos, 1) {
        None
    } else {
        let (t, p) = (b[pos], pos + 1);
        if t == 0 {
            Some((Agg::CountStar, p))
        } else if t == 1 || t == 3 || t == 4 {
            match dec_expr(b, p) {
                Some((e, q)) => Some((if t == 1 { Agg::Count(e) } else if t == 3 { Agg::Min(e) } else { Agg::Max(e) }, q)),
                None => None,
            }
        } else if t == 2 || t == 5 {
            if in_bounds(b, p, 1) && dec_num_kind(b[p]) is Some {
                match dec_expr(b, p + 1) {
                    Some((e, q)) => {
                        let kind = dec_num_kind(b[p])->Some_0;
                        Some((if t == 2 { Agg::Sum { kind, arg: e } } else { Agg::Avg { kind, arg: e } }, q))
                    },
                    None => None,
                }
            } else {
                None
            }
        } else if t == 6 {
            match dec_agg(b, p) {
                Some((a, q)) => Some((Agg::DistinctAgg(Box::new(a)), q)),
                None => None,
            }
        } else {
            None
        }
    }
}

/// `n` consecutive `agg`s at `pos`, and the position after them.
pub open spec fn dec_aggs(b: Seq<u8>, pos: int, n: nat) -> Option<(Seq<Agg>, int)>
    decreases rest(b, pos), 1int,
{
    if n == 0 {
        Some((Seq::empty(), pos))
    } else {
        match dec_agg(b, pos) {
            Some((a, q)) => if advances(b, pos, q) {
                match dec_aggs(b, q, (n - 1) as nat) {
                    Some((aggs, end)) => Some((seq![a] + aggs, end)),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    }
}

/// `query` at `pos`, and the position after it.
pub open spec fn dec_query(b: Seq<u8>, pos: int) -> Option<(Query, int)>
    decreases rest(b, pos), 0int,
{
    if !in_bounds(b, pos, 1) {
        None
    } else {
        let (t, p) = (b[pos], pos + 1);
        if t == 0 {
            if in_bounds(b, p, 4) { Some((Query::Table(le4(b, p) as nat), p + 4)) } else { None }
        } else if t == 1 {
            match dec_pred(b, p) {
                Some((pred, q1)) => if advances(b, pos, q1) {
                    match dec_query(b, q1) {
                        Some((input, q2)) => Some((Query::Filter { pred, input: Box::new(input) }, q2)),
                        None => None,
                    }
                } else {
                    None
                },
                None => None,
            }
        } else if t == 2 {
            if in_bounds(b, p, 4) {
                match dec_exprs(b, p + 4, le4(b, p) as nat) {
                    Some((exprs, q1)) => if advances(b, pos, q1) {
                        match dec_query(b, q1) {
                            Some((input, q2)) => Some((Query::Project { exprs, input: Box::new(input) }, q2)),
                            None => None,
                        }
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            }
        } else if t == 5 {
            if in_bounds(b, p, 4) {
                match dec_aggs(b, p + 4, le4(b, p) as nat) {
                    Some((aggs, q1)) => if advances(b, pos, q1) {
                        match dec_query(b, q1) {
                            Some((input, q2)) => Some((Query::Aggregate { aggs, input: Box::new(input) }, q2)),
                            None => None,
                        }
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            }
        } else if t == 3 || t == 4 {
            match dec_query(b, p) {
                Some((left, q1)) => if advances(b, pos, q1) {
                    match dec_query(b, q1) {
                        Some((right, q2)) => if t == 3 {
                            Some((Query::Product { left: Box::new(left), right: Box::new(right) }, q2))
                        } else if advances(b, pos, q2) {
                            match dec_pred(b, q2) {
                                Some((on, q3)) => Some((Query::LeftJoin { left: Box::new(left), right: Box::new(right), on }, q3)),
                                None => None,
                            }
                        } else {
                            None
                        },
                        None => None,
                    }
                } else {
                    None
                },
                None => None,
            }
        } else if t == 6 {
            if in_bounds(b, p, 4) {
                match dec_exprs(b, p + 4, le4(b, p) as nat) {
                    Some((keys, q1)) => if advances(b, pos, q1) && in_bounds(b, q1, 4) {
                        match dec_aggs(b, q1 + 4, le4(b, q1) as nat) {
                            Some((aggs, q2)) => if advances(b, pos, q2) {
                                match dec_query(b, q2) {
                                    Some((input, q3)) => Some((Query::GroupBy { keys, aggs, input: Box::new(input) }, q3)),
                                    None => None,
                                }
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            }
        } else if t == 7 {
            match dec_query(b, p) {
                Some((input, q)) => Some((Query::Distinct(Box::new(input)), q)),
                None => None,
            }
        } else {
            None
        }
    }
}

/// `n` consecutive ORDER BY keys at `pos`, and the position after them.
pub open spec fn dec_keys(b: Seq<u8>, pos: int, n: nat) -> Option<(Seq<OrderKey>, int)>
    decreases n,
{
    if n == 0 {
        Some((Seq::empty(), pos))
    } else if in_bounds(b, pos, 6) && dec_bool(b[pos + 4]) is Some && dec_bool(b[pos + 5]) is Some {
        match dec_keys(b, pos + 6, (n - 1) as nat) {
            Some((keys, end)) => Some((
                seq![OrderKey { col: le4(b, pos) as nat, desc: dec_bool(b[pos + 4])->Some_0, nulls_first: dec_bool(b[pos + 5])->Some_0 }] + keys,
                end,
            )),
            None => None,
        }
    } else {
        None
    }
}

/// `limit` at `pos`, and the position after it.
pub open spec fn dec_limit(b: Seq<u8>, pos: int) -> Option<(Option<nat>, int)> {
    if in_bounds(b, pos, 1) && b[pos] == 0 {
        Some((None, pos + 1))
    } else if in_bounds(b, pos, 9) && b[pos] == 1 {
        Some((Some(le8(b, pos + 1) as nat), pos + 9))
    } else {
        None
    }
}

/// `ordered` at `pos`, and the position after it.
pub open spec fn dec_ordered(b: Seq<u8>, pos: int) -> Option<(OrderedQuery, int)> {
    match dec_query(b, pos) {
        Some((body, q1)) => if in_bounds(b, q1, 4) {
            match dec_keys(b, q1 + 4, le4(b, q1) as nat) {
                Some((keys, q2)) => match dec_limit(b, q2) {
                    Some((limit, q3)) => if in_bounds(b, q3, 8) {
                        Some((OrderedQuery { body, keys, limit, offset: le8(b, q3) as nat }, q3 + 8))
                    } else {
                        None
                    },
                    None => None,
                },
                None => None,
            }
        } else {
            None
        },
        None => None,
    }
}

/// THE MEANING OF AN ENGINE CALL'S AST BYTES (trusted definition, `ast_decode_definition`): the statement the bytes
/// encode, or `None` when they are not exactly the magic followed by one encoded `OrderedQuery`.
pub open spec fn decode_spec(b: Seq<u8>) -> Option<OrderedQuery> {
    if in_bounds(b, 0, 8) && b.subrange(0, 8) == ast_magic() {
        match dec_ordered(b, 8) {
            Some((q, end)) => if end == b.len() { Some(q) } else { None },
            None => None,
        }
    } else {
        None
    }
}

// ============================================================================================ executable decoder

/// What an executable decoder of one item at `pos` returns: the item's view and the position after it exactly when
/// the spec decoder decodes one.
pub open spec fn decoded<T, V>(spec: Option<(V, int)>, r: Option<(T, usize)>, view: spec_fn(T) -> V) -> bool {
    match r {
        Some((x, q)) => spec == Some((view(x), q as int)),
        None => spec is None,
    }
}

fn in_bounds_exec(b: &[u8], pos: usize, n: usize) -> (r: bool)
    ensures
        r == in_bounds(b@, pos as int, n as int),
{
    pos <= b.len() && b.len() - pos >= n
}

fn le4_exec(b: &[u8], pos: usize) -> (r: u32)
    requires
        in_bounds(b@, pos as int, 4),
    ensures
        r as int == le4(b@, pos as int),
{
    b[pos] as u32 + 0x100 * (b[pos + 1] as u32) + 0x1_0000 * (b[pos + 2] as u32) + 0x100_0000 * (b[pos + 3] as u32)
}

fn le8_exec(b: &[u8], pos: usize) -> (r: u64)
    requires
        in_bounds(b@, pos as int, 8),
    ensures
        r as int == le8(b@, pos as int),
{
    let _len = b.len();
    let (lo, hi) = (le4_exec(b, pos) as u64, le4_exec(b, pos + 4) as u64);
    assert(hi * 0x1_0000_0000 <= 0xffff_ffff_0000_0000) by (nonlinear_arith) requires hi <= 0xffff_ffff;
    lo + hi * 0x1_0000_0000
}

fn le16_exec(b: &[u8], pos: usize) -> (r: u128)
    requires
        in_bounds(b@, pos as int, 16),
    ensures
        r as int == le16(b@, pos as int),
{
    let _len = b.len();
    let (lo, hi) = (le8_exec(b, pos) as u128, le8_exec(b, pos + 8) as u128);
    assert(hi * 0x1_0000_0000_0000_0000 <= 0xffff_ffff_ffff_ffff_0000_0000_0000_0000) by (nonlinear_arith) requires hi <= 0xffff_ffff_ffff_ffff;
    lo + hi * 0x1_0000_0000_0000_0000
}

fn s32_exec(u: u32) -> (r: i32)
    ensures
        r as int == s32(u as int),
{
    if u < 0x8000_0000 { u as i32 } else { ((u - 0x8000_0000) as i32) - 0x7fff_ffff - 1 }
}

fn s64_exec(u: u64) -> (r: i64)
    ensures
        r as int == s64(u as int),
{
    if u < 0x8000_0000_0000_0000 { u as i64 } else { ((u - 0x8000_0000_0000_0000) as i64) - 0x7fff_ffff_ffff_ffff - 1 }
}

fn s128_exec(u: u128) -> (r: i128)
    ensures
        r as int == s128(u as int),
{
    if u < 0x8000_0000_0000_0000_0000_0000_0000_0000 {
        u as i128
    } else {
        ((u - 0x8000_0000_0000_0000_0000_0000_0000_0000) as i128) - 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff - 1
    }
}

fn int_kind_exec(x: u8) -> (r: Option<IntKind>)
    ensures
        r == dec_int_kind(x),
{
    if x == 0 { Some(IntKind::Int4) } else if x == 1 { Some(IntKind::Int8) } else { None }
}

fn num_kind_exec(x: u8) -> (r: Option<NumKind>)
    ensures
        r == dec_num_kind(x),
{
    if x == 0 { Some(NumKind::Int4) } else if x == 1 { Some(NumKind::Int8) } else if x == 2 { Some(NumKind::Numeric) } else { None }
}

fn arith_op_exec(x: u8) -> (r: Option<ArithOp>)
    ensures
        r == dec_arith_op(x),
{
    if x == 0 { Some(ArithOp::Add) } else if x == 1 { Some(ArithOp::Sub) } else if x == 2 { Some(ArithOp::Mul) } else { None }
}

fn cmp_op_exec(x: u8) -> (r: Option<CmpOp>)
    ensures
        r == dec_cmp_op(x),
{
    if x == 0 {
        Some(CmpOp::Eq)
    } else if x == 1 {
        Some(CmpOp::Ne)
    } else if x == 2 {
        Some(CmpOp::Lt)
    } else if x == 3 {
        Some(CmpOp::Le)
    } else if x == 4 {
        Some(CmpOp::Gt)
    } else if x == 5 {
        Some(CmpOp::Ge)
    } else {
        None
    }
}

fn cast_op_exec(x: u8) -> (r: Option<CastOp>)
    ensures
        r == dec_cast_op(x),
{
    if x == 0 {
        Some(CastOp::Int4ToInt8)
    } else if x == 1 {
        Some(CastOp::IntToNumeric)
    } else if x == 2 {
        Some(CastOp::DateToTimestamp)
    } else {
        None
    }
}

fn scalar_fn_exec(x: u8) -> (r: Option<ScalarFn>)
    ensures
        r == dec_scalar_fn(x),
{
    if x == 0 {
        Some(ScalarFn::DivInt4)
    } else if x == 1 {
        Some(ScalarFn::DivInt8)
    } else if x == 2 {
        Some(ScalarFn::DivNumeric)
    } else if x == 3 {
        Some(ScalarFn::Like)
    } else if x == 4 {
        Some(ScalarFn::Substring2)
    } else if x == 5 {
        Some(ScalarFn::Substring3)
    } else if x == 6 {
        Some(ScalarFn::ExtractYear)
    } else if x == 7 {
        Some(ScalarFn::ExtractMonth)
    } else if x == 8 {
        Some(ScalarFn::ExtractDay)
    } else if x == 9 {
        Some(ScalarFn::PadBpchar)
    } else {
        None
    }
}

fn bool_exec(x: u8) -> (r: Option<bool>)
    ensures
        r == dec_bool(x),
{
    if x == 0 { Some(false) } else if x == 1 { Some(true) } else { None }
}

fn scalar_ty_exec(b: &[u8], pos: usize) -> (r: Option<(ScalarTy, usize)>)
    ensures
        decoded(dec_scalar_ty(b@, pos as int), r, |t: ScalarTy| t),
{
    if !in_bounds_exec(b, pos, 1) {
        return None;
    }
    let (t, p) = (b[pos], pos + 1);
    if t == 0 {
        Some((ScalarTy::Bool, p))
    } else if t == 1 {
        Some((ScalarTy::Int4, p))
    } else if t == 2 {
        Some((ScalarTy::Int8, p))
    } else if t == 3 {
        if in_bounds_exec(b, p, 4) { Some((ScalarTy::Numeric { scale: le4_exec(b, p) }, p + 4)) } else { None }
    } else if t == 4 {
        Some((ScalarTy::Date, p))
    } else if t == 5 {
        Some((ScalarTy::Timestamp, p))
    } else if t == 6 {
        Some((ScalarTy::Text, p))
    } else {
        None
    }
}

/// The bytes `b[lo..hi]` as a new vector.
fn copy_bytes(b: &[u8], lo: usize, hi: usize) -> (r: Vec<u8>)
    requires
        lo <= hi <= b@.len(),
    ensures
        r@ == b@.subrange(lo as int, hi as int),
{
    let mut r: Vec<u8> = Vec::with_capacity(hi - lo);
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi <= b@.len(),
            r@ == b@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        r.push(b[i]);
        i += 1;
        assert(r@ =~= b@.subrange(lo as int, i as int));
    }
    r
}

fn lit_exec(b: &[u8], pos: usize) -> (r: Option<(ELiteral, usize)>)
    ensures
        decoded(dec_lit(b@, pos as int), r, |l: ELiteral| view_lit(l)),
{
    if !in_bounds_exec(b, pos, 1) {
        return None;
    }
    let (t, p) = (b[pos], pos + 1);
    if t == 0 {
        match scalar_ty_exec(b, p) {
            Some((ty, q)) => Some((ELiteral::Null { ty }, q)),
            None => None,
        }
    } else if t == 1 {
        if !in_bounds_exec(b, p, 1) {
            return None;
        }
        match bool_exec(b[p]) {
            Some(v) => Some((ELiteral::Bool(v), p + 1)),
            None => None,
        }
    } else if t == 2 {
        if !in_bounds_exec(b, p, 9) {
            return None;
        }
        match int_kind_exec(b[p + 8]) {
            Some(kind) => Some((ELiteral::Int { v: s64_exec(le8_exec(b, p)), kind }, p + 9)),
            None => None,
        }
    } else if t == 3 {
        if !in_bounds_exec(b, p, 20) {
            return None;
        }
        Some((ELiteral::Num { coeff: s128_exec(le16_exec(b, p)), scale: le4_exec(b, p + 16) }, p + 20))
    } else if t == 4 {
        if !in_bounds_exec(b, p, 12) {
            return None;
        }
        Some((ELiteral::Date { y: s32_exec(le4_exec(b, p)), m: s32_exec(le4_exec(b, p + 4)), d: s32_exec(le4_exec(b, p + 8)) }, p + 12))
    } else if t == 5 {
        if !in_bounds_exec(b, p, 4) {
            return None;
        }
        let n = le4_exec(b, p) as usize;
        if !in_bounds_exec(b, p + 4, n) {
            return None;
        }
        Some((ELiteral::Text(copy_bytes(b, p + 4, p + 4 + n)), p + 4 + n))
    } else {
        None
    }
}

/// Executable `dec_expr`.
fn expr_exec(b: &[u8], pos: usize) -> (r: Option<(EExpr, usize)>)
    ensures
        decoded(dec_expr(b@, pos as int), r, |e: EExpr| view_expr(e)),
    decreases rest(b@, pos as int), 1int,
{
    if !in_bounds_exec(b, pos, 1) {
        return None;
    }
    let (t, p) = (b[pos], pos + 1);
    if t == 0 {
        if in_bounds_exec(b, p, 4) { Some((EExpr::Col(le4_exec(b, p) as usize), p + 4)) } else { None }
    } else if t == 1 {
        match lit_exec(b, p) {
            Some((l, q)) => Some((EExpr::Lit(l), q)),
            None => None,
        }
    } else if t == 2 {
        if !in_bounds_exec(b, p, 1) {
            return None;
        }
        let kind = match num_kind_exec(b[p]) {
            Some(k) => k,
            None => return None,
        };
        match expr_exec(b, p + 1) {
            Some((arg, q)) => Some((EExpr::Neg { kind, arg: Box::new(arg) }, q)),
            None => None,
        }
    } else if t == 4 {
        if !in_bounds_exec(b, p, 1) {
            return None;
        }
        let cast = match cast_op_exec(b[p]) {
            Some(c) => c,
            None => return None,
        };
        match expr_exec(b, p + 1) {
            Some((arg, q)) => Some((EExpr::Cast { cast, arg: Box::new(arg) }, q)),
            None => None,
        }
    } else if t == 8 {
        match query_exec(b, p) {
            Some((q, end)) => Some((EExpr::Subquery(Box::new(q)), end)),
            None => None,
        }
    } else if t == 3 || t == 5 || t == 6 || t == 7 {
        expr_compound_exec(b, pos)
    } else {
        None
    }
}

/// `expr_exec` of the expressions with several subterms (tags 3 `Arith`, 5 `AddInterval`, 6 `Call`, 7 `If`).
fn expr_compound_exec(b: &[u8], pos: usize) -> (r: Option<(EExpr, usize)>)
    requires
        in_bounds(b@, pos as int, 1),
        b@[pos as int] == 3 || b@[pos as int] == 5 || b@[pos as int] == 6 || b@[pos as int] == 7,
    ensures
        decoded(dec_expr(b@, pos as int), r, |e: EExpr| view_expr(e)),
    decreases rest(b@, pos as int), 0int,
{
    let (t, p) = (b[pos], pos + 1);
    if t == 3 {
        if !in_bounds_exec(b, p, 2) {
            return None;
        }
        let (op, kind) = match (arith_op_exec(b[p]), num_kind_exec(b[p + 1])) {
            (Some(op), Some(kind)) => (op, kind),
            _ => return None,
        };
        let (a, q1) = match expr_exec(b, p + 2) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q1) {
            return None;
        }
        match expr_exec(b, q1) {
            Some((c, q2)) => Some((EExpr::Arith { op, kind, a: Box::new(a), b: Box::new(c) }, q2)),
            None => None,
        }
    } else if t == 5 {
        let (arg, q) = match expr_exec(b, p) {
            Some(x) => x,
            None => return None,
        };
        if !in_bounds_exec(b, q, 16) {
            return None;
        }
        let months = s32_exec(le4_exec(b, q));
        let days = s32_exec(le4_exec(b, q + 4));
        let micros = s64_exec(le8_exec(b, q + 8));
        Some((EExpr::AddInterval { arg: Box::new(arg), months, days, micros }, q + 16))
    } else if t == 6 {
        if !in_bounds_exec(b, p, 5) {
            return None;
        }
        let f = match scalar_fn_exec(b[p]) {
            Some(f) => f,
            None => return None,
        };
        match exprs_exec(b, p + 5, le4_exec(b, p + 1)) {
            Some((args, q)) => Some((EExpr::Call { f, args }, q)),
            None => None,
        }
    } else {
        let (cond, q1) = match pred_exec(b, p) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q1) {
            return None;
        }
        let (then_e, q2) = match expr_exec(b, q1) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q2) {
            return None;
        }
        match expr_exec(b, q2) {
            Some((else_e, q3)) => Some((EExpr::If { cond: Box::new(cond), then_e: Box::new(then_e), else_e: Box::new(else_e) }, q3)),
            None => None,
        }
    }
}

/// `dec_exprs` from the position `at` reached after decoding the items `done` (in order) from `pos`: the whole list's
/// decoding is `done` followed by the decoding of the rest.
pub open spec fn exprs_continue(done: Seq<Expr>, tail: Option<(Seq<Expr>, int)>) -> Option<(Seq<Expr>, int)> {
    match tail {
        Some((es, end)) => Some((done + es, end)),
        None => None,
    }
}

/// Executable `dec_exprs`.
fn exprs_exec(b: &[u8], pos: usize, n: u32) -> (r: Option<(Vec<EExpr>, usize)>)
    ensures
        decoded(dec_exprs(b@, pos as int, n as nat), r, |v: Vec<EExpr>| view_exprs(v@)),
    decreases rest(b@, pos as int), 2int,
{
    let mut out: Vec<EExpr> = Vec::new();
    let mut at = pos;
    let mut i: u32 = 0;
    proof {
        assert(view_exprs(out@) =~= Seq::<Expr>::empty());
        assert(Seq::<Expr>::empty() + Seq::<Expr>::empty() =~= Seq::<Expr>::empty());
        match dec_exprs(b@, pos as int, n as nat) {
            Some((es, end)) => assert(Seq::<Expr>::empty() + es =~= es),
            None => {},
        }
    }
    while i < n
        invariant
            i <= n,
            i == 0 ==> at == pos,
            i > 0 ==> pos < b@.len() && pos < at,
            dec_exprs(b@, pos as int, n as nat) == exprs_continue(view_exprs(out@), dec_exprs(b@, at as int, (n - i) as nat)),
        decreases n - i,
    {
        let ghost done = view_exprs(out@);
        let (e, q) = match expr_exec(b, at) {
            Some(x) => x,
            None => return None,
        };
        if !(at < b.len() && at < q) {
            return None;
        }
        proof {
            let tail = dec_exprs(b@, q as int, (n - i - 1) as nat);
            assert(dec_exprs(b@, at as int, (n - i) as nat) == exprs_continue(seq![view_expr(e)], tail));
            lemma_view_exprs_index(out@);
            lemma_view_exprs_index(out@.push(e));
            assert(view_exprs(out@.push(e)) =~= done.push(view_expr(e)));
            match tail {
                Some((es, end)) => assert(done + (seq![view_expr(e)] + es) =~= done.push(view_expr(e)) + es),
                None => {},
            }
        }
        out.push(e);
        at = q;
        i = i + 1;
    }
    proof {
        assert(view_exprs(out@) + Seq::<Expr>::empty() =~= view_exprs(out@));
    }
    Some((out, at))
}

/// Executable `dec_pred`.
fn pred_exec(b: &[u8], pos: usize) -> (r: Option<(EPred, usize)>)
    ensures
        decoded(dec_pred(b@, pos as int), r, |p: EPred| view_pred(p)),
    decreases rest(b@, pos as int), 0int,
{
    if !in_bounds_exec(b, pos, 1) {
        return None;
    }
    let (t, p) = (b[pos], pos + 1);
    if t == 0 || t == 7 {
        if !in_bounds_exec(b, p, 1) {
            return None;
        }
        let op = match cmp_op_exec(b[p]) {
            Some(op) => op,
            None => return None,
        };
        let (a, q1) = match expr_exec(b, p + 1) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q1) {
            return None;
        }
        if t == 0 {
            match expr_exec(b, q1) {
                Some((c, q2)) => Some((EPred::Cmp { op, a, b: c }, q2)),
                None => None,
            }
        } else {
            match query_exec(b, q1) {
                Some((q, q2)) => Some((EPred::AnyCmp { op, e: a, q: Box::new(q) }, q2)),
                None => None,
            }
        }
    } else if t == 1 || t == 2 {
        let (x, q1) = match pred_exec(b, p) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q1) {
            return None;
        }
        match pred_exec(b, q1) {
            Some((y, q2)) => Some((if t == 1 { EPred::And(Box::new(x), Box::new(y)) } else { EPred::Or(Box::new(x), Box::new(y)) }, q2)),
            None => None,
        }
    } else if t == 3 {
        match pred_exec(b, p) {
            Some((x, q)) => Some((EPred::Not(Box::new(x)), q)),
            None => None,
        }
    } else if t == 4 || t == 5 {
        match expr_exec(b, p) {
            Some((e, q)) => Some((if t == 4 { EPred::IsNull(e) } else { EPred::OfBool(e) }, q)),
            None => None,
        }
    } else if t == 6 {
        match query_exec(b, p) {
            Some((q, end)) => Some((EPred::Exists(Box::new(q)), end)),
            None => None,
        }
    } else {
        None
    }
}

/// Executable `dec_agg`.
fn agg_exec(b: &[u8], pos: usize) -> (r: Option<(EAgg, usize)>)
    ensures
        decoded(dec_agg(b@, pos as int), r, |a: EAgg| view_agg(a)),
    decreases rest(b@, pos as int), 0int,
{
    if !in_bounds_exec(b, pos, 1) {
        return None;
    }
    let (t, p) = (b[pos], pos + 1);
    if t == 0 {
        Some((EAgg::CountStar, p))
    } else if t == 1 || t == 3 || t == 4 {
        match expr_exec(b, p) {
            Some((e, q)) => Some((if t == 1 { EAgg::Count(e) } else if t == 3 { EAgg::Min(e) } else { EAgg::Max(e) }, q)),
            None => None,
        }
    } else if t == 2 || t == 5 {
        if !in_bounds_exec(b, p, 1) {
            return None;
        }
        let kind = match num_kind_exec(b[p]) {
            Some(k) => k,
            None => return None,
        };
        match expr_exec(b, p + 1) {
            Some((e, q)) => Some((if t == 2 { EAgg::Sum { kind, arg: e } } else { EAgg::Avg { kind, arg: e } }, q)),
            None => None,
        }
    } else if t == 6 {
        match agg_exec(b, p) {
            Some((a, q)) => Some((EAgg::DistinctAgg(Box::new(a)), q)),
            None => None,
        }
    } else {
        None
    }
}

/// `dec_aggs` continued after the decoded items `done` (see `exprs_continue`).
pub open spec fn aggs_continue(done: Seq<Agg>, tail: Option<(Seq<Agg>, int)>) -> Option<(Seq<Agg>, int)> {
    match tail {
        Some((aggs, end)) => Some((done + aggs, end)),
        None => None,
    }
}

/// Executable `dec_aggs`.
fn aggs_exec(b: &[u8], pos: usize, n: u32) -> (r: Option<(Vec<EAgg>, usize)>)
    ensures
        decoded(dec_aggs(b@, pos as int, n as nat), r, |v: Vec<EAgg>| view_aggs(v@)),
    decreases rest(b@, pos as int), 1int,
{
    let mut out: Vec<EAgg> = Vec::new();
    let mut at = pos;
    let mut i: u32 = 0;
    proof {
        assert(view_aggs(out@) =~= Seq::<Agg>::empty());
        match dec_aggs(b@, pos as int, n as nat) {
            Some((aggs, end)) => assert(Seq::<Agg>::empty() + aggs =~= aggs),
            None => {},
        }
    }
    while i < n
        invariant
            i <= n,
            i == 0 ==> at == pos,
            i > 0 ==> pos < b@.len() && pos < at,
            dec_aggs(b@, pos as int, n as nat) == aggs_continue(view_aggs(out@), dec_aggs(b@, at as int, (n - i) as nat)),
        decreases n - i,
    {
        let ghost done = view_aggs(out@);
        let (a, q) = match agg_exec(b, at) {
            Some(x) => x,
            None => return None,
        };
        if !(at < b.len() && at < q) {
            return None;
        }
        proof {
            let tail = dec_aggs(b@, q as int, (n - i - 1) as nat);
            assert(dec_aggs(b@, at as int, (n - i) as nat) == aggs_continue(seq![view_agg(a)], tail));
            lemma_view_aggs_index(out@);
            lemma_view_aggs_index(out@.push(a));
            assert(view_aggs(out@.push(a)) =~= done.push(view_agg(a)));
            match tail {
                Some((aggs, end)) => assert(done + (seq![view_agg(a)] + aggs) =~= done.push(view_agg(a)) + aggs),
                None => {},
            }
        }
        out.push(a);
        at = q;
        i = i + 1;
    }
    proof {
        assert(view_aggs(out@) + Seq::<Agg>::empty() =~= view_aggs(out@));
    }
    Some((out, at))
}

/// Executable `dec_query`.
fn query_exec(b: &[u8], pos: usize) -> (r: Option<(EQuery, usize)>)
    ensures
        decoded(dec_query(b@, pos as int), r, |q: EQuery| view_query(q)),
    decreases rest(b@, pos as int), 0int,
{
    if !in_bounds_exec(b, pos, 1) {
        return None;
    }
    let (t, p) = (b[pos], pos + 1);
    if t == 0 {
        if in_bounds_exec(b, p, 4) { Some((EQuery::Table(le4_exec(b, p) as usize), p + 4)) } else { None }
    } else if t == 1 {
        let (pred, q1) = match pred_exec(b, p) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q1) {
            return None;
        }
        match query_exec(b, q1) {
            Some((input, q2)) => Some((EQuery::Filter { pred, input: Box::new(input) }, q2)),
            None => None,
        }
    } else if t == 2 {
        if !in_bounds_exec(b, p, 4) {
            return None;
        }
        let (exprs, q1) = match exprs_exec(b, p + 4, le4_exec(b, p)) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q1) {
            return None;
        }
        match query_exec(b, q1) {
            Some((input, q2)) => Some((EQuery::Project { exprs, input: Box::new(input) }, q2)),
            None => None,
        }
    } else if t == 5 {
        if !in_bounds_exec(b, p, 4) {
            return None;
        }
        let (aggs, q1) = match aggs_exec(b, p + 4, le4_exec(b, p)) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q1) {
            return None;
        }
        match query_exec(b, q1) {
            Some((input, q2)) => Some((EQuery::Aggregate { aggs, input: Box::new(input) }, q2)),
            None => None,
        }
    } else if t == 3 || t == 4 {
        let (left, q1) = match query_exec(b, p) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q1) {
            return None;
        }
        let (right, q2) = match query_exec(b, q1) {
            Some(x) => x,
            None => return None,
        };
        if t == 3 {
            return Some((EQuery::Product { left: Box::new(left), right: Box::new(right) }, q2));
        }
        if !(pos < b.len() && pos < q2) {
            return None;
        }
        match pred_exec(b, q2) {
            Some((on, q3)) => Some((EQuery::LeftJoin { left: Box::new(left), right: Box::new(right), on }, q3)),
            None => None,
        }
    } else if t == 6 {
        if !in_bounds_exec(b, p, 4) {
            return None;
        }
        let (keys, q1) = match exprs_exec(b, p + 4, le4_exec(b, p)) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q1 && in_bounds_exec(b, q1, 4)) {
            return None;
        }
        let (aggs, q2) = match aggs_exec(b, q1 + 4, le4_exec(b, q1)) {
            Some(x) => x,
            None => return None,
        };
        if !(pos < b.len() && pos < q2) {
            return None;
        }
        match query_exec(b, q2) {
            Some((input, q3)) => Some((EQuery::GroupBy { keys, aggs, input: Box::new(input) }, q3)),
            None => None,
        }
    } else if t == 7 {
        match query_exec(b, p) {
            Some((input, q)) => Some((EQuery::Distinct(Box::new(input)), q)),
            None => None,
        }
    } else {
        None
    }
}

/// `dec_keys` continued after the decoded keys `done` (see `exprs_continue`).
pub open spec fn keys_continue(done: Seq<OrderKey>, tail: Option<(Seq<OrderKey>, int)>) -> Option<(Seq<OrderKey>, int)> {
    match tail {
        Some((keys, end)) => Some((done + keys, end)),
        None => None,
    }
}

/// Executable `dec_keys`.
fn keys_exec(b: &[u8], pos: usize, n: u32) -> (r: Option<(Vec<EOrderKey>, usize)>)
    ensures
        decoded(dec_keys(b@, pos as int, n as nat), r, |v: Vec<EOrderKey>| view_order_keys(v@)),
{
    let mut out: Vec<EOrderKey> = Vec::new();
    let mut at = pos;
    let mut i: u32 = 0;
    proof {
        assert(view_order_keys(out@) =~= Seq::<OrderKey>::empty());
        match dec_keys(b@, pos as int, n as nat) {
            Some((keys, end)) => assert(Seq::<OrderKey>::empty() + keys =~= keys),
            None => {},
        }
    }
    while i < n
        invariant
            i <= n,
            dec_keys(b@, pos as int, n as nat) == keys_continue(view_order_keys(out@), dec_keys(b@, at as int, (n - i) as nat)),
        decreases n - i,
    {
        let len = b.len();
        if !(at <= len && len - at >= 6) {
            return None;
        }
        let (desc, nulls_first) = match (bool_exec(b[at + 4]), bool_exec(b[at + 5])) {
            (Some(desc), Some(nulls_first)) => (desc, nulls_first),
            _ => return None,
        };
        let key = EOrderKey { col: le4_exec(b, at) as usize, desc, nulls_first };
        proof {
            let done = view_order_keys(out@);
            let tail = dec_keys(b@, at + 6, (n - i - 1) as nat);
            assert(view_order_keys(out@.push(key)) =~= done.push(view_order_key(key)));
            match tail {
                Some((keys, end)) => assert(done + (seq![view_order_key(key)] + keys) =~= done.push(view_order_key(key)) + keys),
                None => {},
            }
        }
        out.push(key);
        at = at + 6;
        i = i + 1;
    }
    proof {
        assert(view_order_keys(out@) + Seq::<OrderKey>::empty() =~= view_order_keys(out@));
    }
    Some((out, at))
}

/// THE EXECUTABLE DECODER: `Some(q)` with `view_ordered(q) == decode_spec(b)` exactly when `decode_spec(b)` is `Some`.
pub fn decode_query(b: &[u8]) -> (r: Option<EOrderedQuery>)
    ensures
        match r {
            Some(q) => decode_spec(b@) == Some(view_ordered(q)),
            None => decode_spec(b@) is None,
        },
{
    if !in_bounds_exec(b, 0, 8) {
        return None;
    }
    if !(b[0] == b'G' && b[1] == b'S' && b[2] == b'Q' && b[3] == b'L' && b[4] == b'A' && b[5] == b'S' && b[6] == b'T' && b[7] == b'1') {
        proof {
            assert(b@.subrange(0, 8) != ast_magic()) by {
                if b@.subrange(0, 8) == ast_magic() {
                    assert(b@.subrange(0, 8)[0] == b@[0]);
                    assert(b@.subrange(0, 8)[1] == b@[1]);
                    assert(b@.subrange(0, 8)[2] == b@[2]);
                    assert(b@.subrange(0, 8)[3] == b@[3]);
                    assert(b@.subrange(0, 8)[4] == b@[4]);
                    assert(b@.subrange(0, 8)[5] == b@[5]);
                    assert(b@.subrange(0, 8)[6] == b@[6]);
                    assert(b@.subrange(0, 8)[7] == b@[7]);
                }
            }
        }
        return None;
    }
    proof {
        assert(b@.subrange(0, 8) =~= ast_magic());
    }
    let (body, q1) = match query_exec(b, 8) {
        Some(x) => x,
        None => return None,
    };
    if !in_bounds_exec(b, q1, 4) {
        return None;
    }
    let (keys, q2) = match keys_exec(b, q1 + 4, le4_exec(b, q1)) {
        Some(x) => x,
        None => return None,
    };
    let (limit, q3) = if in_bounds_exec(b, q2, 1) && b[q2] == 0 {
        (None, q2 + 1)
    } else if in_bounds_exec(b, q2, 9) && b[q2] == 1 {
        (Some(le8_exec(b, q2 + 1)), q2 + 9)
    } else {
        return None;
    };
    if !in_bounds_exec(b, q3, 8) {
        return None;
    }
    let offset = le8_exec(b, q3);
    if q3 + 8 != b.len() {
        return None;
    }
    let q = EOrderedQuery { body, keys, limit, offset };
    proof {
        assert(dec_limit(b@, q2 as int) == Some((view_ordered(q).limit, q3 as int)));
    }
    Some(q)
}


// ============================================================================================ echo text (spec)
//
// The canonical s-expression of the evaluator's echo grammar (`gendb_sqlspec::evaluator::echo_text`): `(Tag field
// ...)` per node in schema field order, children inline, lists `[a b]`, `none` / `(some n)`, scalar types `(Numeric s)`
// or `(Date)`, integers in decimal, text bytes as `0x` and two lowercase hex digits per byte, booleans `true`/`false`.
// An undecodable input renders as `(Malformed)`.

/// Every identifier of the echo grammar: node tags, operator and type names and the fixed tokens `none`, `some`,
/// `true`, `false` and `Malformed`.
pub enum Word {
    OrderedQuery,
    OrderKey,
    Table,
    Filter,
    Project,
    Product,
    LeftJoin,
    Aggregate,
    GroupBy,
    Distinct,
    Col,
    Lit,
    Neg,
    Arith,
    Cast,
    AddInterval,
    Call,
    If,
    Subquery,
    Cmp,
    And,
    Or,
    Not,
    IsNull,
    OfBool,
    Exists,
    AnyCmp,
    CountStar,
    Count,
    Sum,
    Min,
    Max,
    Avg,
    DistinctAgg,
    Null,
    Bool,
    Int,
    Num,
    Date,
    Text,
    Int4,
    Int8,
    Numeric,
    Timestamp,
    Add,
    Sub,
    Mul,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Int4ToInt8,
    IntToNumeric,
    DateToTimestamp,
    DivInt4,
    DivInt8,
    DivNumeric,
    Like,
    Substring2,
    Substring3,
    ExtractYear,
    ExtractMonth,
    ExtractDay,
    PadBpchar,
    NoneWord,
    SomeWord,
    TrueWord,
    FalseWord,
    Malformed,
}

/// The bytes of a word (ASCII).
pub open spec fn word(w: Word) -> Seq<u8> {
    match w {
        Word::OrderedQuery => seq![b'O', b'r', b'd', b'e', b'r', b'e', b'd', b'Q', b'u', b'e', b'r', b'y'],
        Word::OrderKey => seq![b'O', b'r', b'd', b'e', b'r', b'K', b'e', b'y'],
        Word::Table => seq![b'T', b'a', b'b', b'l', b'e'],
        Word::Filter => seq![b'F', b'i', b'l', b't', b'e', b'r'],
        Word::Project => seq![b'P', b'r', b'o', b'j', b'e', b'c', b't'],
        Word::Product => seq![b'P', b'r', b'o', b'd', b'u', b'c', b't'],
        Word::LeftJoin => seq![b'L', b'e', b'f', b't', b'J', b'o', b'i', b'n'],
        Word::Aggregate => seq![b'A', b'g', b'g', b'r', b'e', b'g', b'a', b't', b'e'],
        Word::GroupBy => seq![b'G', b'r', b'o', b'u', b'p', b'B', b'y'],
        Word::Distinct => seq![b'D', b'i', b's', b't', b'i', b'n', b'c', b't'],
        Word::Col => seq![b'C', b'o', b'l'],
        Word::Lit => seq![b'L', b'i', b't'],
        Word::Neg => seq![b'N', b'e', b'g'],
        Word::Arith => seq![b'A', b'r', b'i', b't', b'h'],
        Word::Cast => seq![b'C', b'a', b's', b't'],
        Word::AddInterval => seq![b'A', b'd', b'd', b'I', b'n', b't', b'e', b'r', b'v', b'a', b'l'],
        Word::Call => seq![b'C', b'a', b'l', b'l'],
        Word::If => seq![b'I', b'f'],
        Word::Subquery => seq![b'S', b'u', b'b', b'q', b'u', b'e', b'r', b'y'],
        Word::Cmp => seq![b'C', b'm', b'p'],
        Word::And => seq![b'A', b'n', b'd'],
        Word::Or => seq![b'O', b'r'],
        Word::Not => seq![b'N', b'o', b't'],
        Word::IsNull => seq![b'I', b's', b'N', b'u', b'l', b'l'],
        Word::OfBool => seq![b'O', b'f', b'B', b'o', b'o', b'l'],
        Word::Exists => seq![b'E', b'x', b'i', b's', b't', b's'],
        Word::AnyCmp => seq![b'A', b'n', b'y', b'C', b'm', b'p'],
        Word::CountStar => seq![b'C', b'o', b'u', b'n', b't', b'S', b't', b'a', b'r'],
        Word::Count => seq![b'C', b'o', b'u', b'n', b't'],
        Word::Sum => seq![b'S', b'u', b'm'],
        Word::Min => seq![b'M', b'i', b'n'],
        Word::Max => seq![b'M', b'a', b'x'],
        Word::Avg => seq![b'A', b'v', b'g'],
        Word::DistinctAgg => seq![b'D', b'i', b's', b't', b'i', b'n', b'c', b't', b'A', b'g', b'g'],
        Word::Null => seq![b'N', b'u', b'l', b'l'],
        Word::Bool => seq![b'B', b'o', b'o', b'l'],
        Word::Int => seq![b'I', b'n', b't'],
        Word::Num => seq![b'N', b'u', b'm'],
        Word::Date => seq![b'D', b'a', b't', b'e'],
        Word::Text => seq![b'T', b'e', b'x', b't'],
        Word::Int4 => seq![b'I', b'n', b't', b'4'],
        Word::Int8 => seq![b'I', b'n', b't', b'8'],
        Word::Numeric => seq![b'N', b'u', b'm', b'e', b'r', b'i', b'c'],
        Word::Timestamp => seq![b'T', b'i', b'm', b'e', b's', b't', b'a', b'm', b'p'],
        Word::Add => seq![b'A', b'd', b'd'],
        Word::Sub => seq![b'S', b'u', b'b'],
        Word::Mul => seq![b'M', b'u', b'l'],
        Word::Eq => seq![b'E', b'q'],
        Word::Ne => seq![b'N', b'e'],
        Word::Lt => seq![b'L', b't'],
        Word::Le => seq![b'L', b'e'],
        Word::Gt => seq![b'G', b't'],
        Word::Ge => seq![b'G', b'e'],
        Word::Int4ToInt8 => seq![b'I', b'n', b't', b'4', b'T', b'o', b'I', b'n', b't', b'8'],
        Word::IntToNumeric => seq![b'I', b'n', b't', b'T', b'o', b'N', b'u', b'm', b'e', b'r', b'i', b'c'],
        Word::DateToTimestamp => seq![b'D', b'a', b't', b'e', b'T', b'o', b'T', b'i', b'm', b'e', b's', b't', b'a', b'm', b'p'],
        Word::DivInt4 => seq![b'D', b'i', b'v', b'I', b'n', b't', b'4'],
        Word::DivInt8 => seq![b'D', b'i', b'v', b'I', b'n', b't', b'8'],
        Word::DivNumeric => seq![b'D', b'i', b'v', b'N', b'u', b'm', b'e', b'r', b'i', b'c'],
        Word::Like => seq![b'L', b'i', b'k', b'e'],
        Word::Substring2 => seq![b'S', b'u', b'b', b's', b't', b'r', b'i', b'n', b'g', b'2'],
        Word::Substring3 => seq![b'S', b'u', b'b', b's', b't', b'r', b'i', b'n', b'g', b'3'],
        Word::ExtractYear => seq![b'E', b'x', b't', b'r', b'a', b'c', b't', b'Y', b'e', b'a', b'r'],
        Word::ExtractMonth => seq![b'E', b'x', b't', b'r', b'a', b'c', b't', b'M', b'o', b'n', b't', b'h'],
        Word::ExtractDay => seq![b'E', b'x', b't', b'r', b'a', b'c', b't', b'D', b'a', b'y'],
        Word::PadBpchar => seq![b'P', b'a', b'd', b'B', b'p', b'c', b'h', b'a', b'r'],
        Word::NoneWord => seq![b'n', b'o', b'n', b'e'],
        Word::SomeWord => seq![b's', b'o', b'm', b'e'],
        Word::TrueWord => seq![b't', b'r', b'u', b'e'],
        Word::FalseWord => seq![b'f', b'a', b'l', b's', b'e'],
        Word::Malformed => seq![b'M', b'a', b'l', b'f', b'o', b'r', b'm', b'e', b'd'],
    }
}

/// `word(w)` as a static byte slice.
fn word_bytes(w: Word) -> (r: &'static [u8])
    ensures
        r@ == word(w),
{
    match w {
        Word::OrderedQuery => &[b'O', b'r', b'd', b'e', b'r', b'e', b'd', b'Q', b'u', b'e', b'r', b'y'],
        Word::OrderKey => &[b'O', b'r', b'd', b'e', b'r', b'K', b'e', b'y'],
        Word::Table => &[b'T', b'a', b'b', b'l', b'e'],
        Word::Filter => &[b'F', b'i', b'l', b't', b'e', b'r'],
        Word::Project => &[b'P', b'r', b'o', b'j', b'e', b'c', b't'],
        Word::Product => &[b'P', b'r', b'o', b'd', b'u', b'c', b't'],
        Word::LeftJoin => &[b'L', b'e', b'f', b't', b'J', b'o', b'i', b'n'],
        Word::Aggregate => &[b'A', b'g', b'g', b'r', b'e', b'g', b'a', b't', b'e'],
        Word::GroupBy => &[b'G', b'r', b'o', b'u', b'p', b'B', b'y'],
        Word::Distinct => &[b'D', b'i', b's', b't', b'i', b'n', b'c', b't'],
        Word::Col => &[b'C', b'o', b'l'],
        Word::Lit => &[b'L', b'i', b't'],
        Word::Neg => &[b'N', b'e', b'g'],
        Word::Arith => &[b'A', b'r', b'i', b't', b'h'],
        Word::Cast => &[b'C', b'a', b's', b't'],
        Word::AddInterval => &[b'A', b'd', b'd', b'I', b'n', b't', b'e', b'r', b'v', b'a', b'l'],
        Word::Call => &[b'C', b'a', b'l', b'l'],
        Word::If => &[b'I', b'f'],
        Word::Subquery => &[b'S', b'u', b'b', b'q', b'u', b'e', b'r', b'y'],
        Word::Cmp => &[b'C', b'm', b'p'],
        Word::And => &[b'A', b'n', b'd'],
        Word::Or => &[b'O', b'r'],
        Word::Not => &[b'N', b'o', b't'],
        Word::IsNull => &[b'I', b's', b'N', b'u', b'l', b'l'],
        Word::OfBool => &[b'O', b'f', b'B', b'o', b'o', b'l'],
        Word::Exists => &[b'E', b'x', b'i', b's', b't', b's'],
        Word::AnyCmp => &[b'A', b'n', b'y', b'C', b'm', b'p'],
        Word::CountStar => &[b'C', b'o', b'u', b'n', b't', b'S', b't', b'a', b'r'],
        Word::Count => &[b'C', b'o', b'u', b'n', b't'],
        Word::Sum => &[b'S', b'u', b'm'],
        Word::Min => &[b'M', b'i', b'n'],
        Word::Max => &[b'M', b'a', b'x'],
        Word::Avg => &[b'A', b'v', b'g'],
        Word::DistinctAgg => &[b'D', b'i', b's', b't', b'i', b'n', b'c', b't', b'A', b'g', b'g'],
        Word::Null => &[b'N', b'u', b'l', b'l'],
        Word::Bool => &[b'B', b'o', b'o', b'l'],
        Word::Int => &[b'I', b'n', b't'],
        Word::Num => &[b'N', b'u', b'm'],
        Word::Date => &[b'D', b'a', b't', b'e'],
        Word::Text => &[b'T', b'e', b'x', b't'],
        Word::Int4 => &[b'I', b'n', b't', b'4'],
        Word::Int8 => &[b'I', b'n', b't', b'8'],
        Word::Numeric => &[b'N', b'u', b'm', b'e', b'r', b'i', b'c'],
        Word::Timestamp => &[b'T', b'i', b'm', b'e', b's', b't', b'a', b'm', b'p'],
        Word::Add => &[b'A', b'd', b'd'],
        Word::Sub => &[b'S', b'u', b'b'],
        Word::Mul => &[b'M', b'u', b'l'],
        Word::Eq => &[b'E', b'q'],
        Word::Ne => &[b'N', b'e'],
        Word::Lt => &[b'L', b't'],
        Word::Le => &[b'L', b'e'],
        Word::Gt => &[b'G', b't'],
        Word::Ge => &[b'G', b'e'],
        Word::Int4ToInt8 => &[b'I', b'n', b't', b'4', b'T', b'o', b'I', b'n', b't', b'8'],
        Word::IntToNumeric => &[b'I', b'n', b't', b'T', b'o', b'N', b'u', b'm', b'e', b'r', b'i', b'c'],
        Word::DateToTimestamp => &[b'D', b'a', b't', b'e', b'T', b'o', b'T', b'i', b'm', b'e', b's', b't', b'a', b'm', b'p'],
        Word::DivInt4 => &[b'D', b'i', b'v', b'I', b'n', b't', b'4'],
        Word::DivInt8 => &[b'D', b'i', b'v', b'I', b'n', b't', b'8'],
        Word::DivNumeric => &[b'D', b'i', b'v', b'N', b'u', b'm', b'e', b'r', b'i', b'c'],
        Word::Like => &[b'L', b'i', b'k', b'e'],
        Word::Substring2 => &[b'S', b'u', b'b', b's', b't', b'r', b'i', b'n', b'g', b'2'],
        Word::Substring3 => &[b'S', b'u', b'b', b's', b't', b'r', b'i', b'n', b'g', b'3'],
        Word::ExtractYear => &[b'E', b'x', b't', b'r', b'a', b'c', b't', b'Y', b'e', b'a', b'r'],
        Word::ExtractMonth => &[b'E', b'x', b't', b'r', b'a', b'c', b't', b'M', b'o', b'n', b't', b'h'],
        Word::ExtractDay => &[b'E', b'x', b't', b'r', b'a', b'c', b't', b'D', b'a', b'y'],
        Word::PadBpchar => &[b'P', b'a', b'd', b'B', b'p', b'c', b'h', b'a', b'r'],
        Word::NoneWord => &[b'n', b'o', b'n', b'e'],
        Word::SomeWord => &[b's', b'o', b'm', b'e'],
        Word::TrueWord => &[b't', b'r', b'u', b'e'],
        Word::FalseWord => &[b'f', b'a', b'l', b's', b'e'],
        Word::Malformed => &[b'M', b'a', b'l', b'f', b'o', b'r', b'm', b'e', b'd'],
    }
}


pub open spec fn lp() -> Seq<u8> {
    seq![b'(']
}

pub open spec fn rp() -> Seq<u8> {
    seq![b')']
}

pub open spec fn sp() -> Seq<u8> {
    seq![b' ']
}

/// `(w)`.
pub open spec fn node0(w: Word) -> Seq<u8> {
    lp() + word(w) + rp()
}

/// `(w a)`.
pub open spec fn node1(w: Word, a: Seq<u8>) -> Seq<u8> {
    lp() + word(w) + sp() + a + rp()
}

/// `(w a b)`.
pub open spec fn node2(w: Word, a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    lp() + word(w) + sp() + a + sp() + b + rp()
}

/// `(w a b c)`.
pub open spec fn node3(w: Word, a: Seq<u8>, b: Seq<u8>, c: Seq<u8>) -> Seq<u8> {
    lp() + word(w) + sp() + a + sp() + b + sp() + c + rp()
}

/// `(w a b c d)`.
pub open spec fn node4(w: Word, a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, d: Seq<u8>) -> Seq<u8> {
    lp() + word(w) + sp() + a + sp() + b + sp() + c + sp() + d + rp()
}

/// The parts separated by single spaces.
pub open spec fn joined(parts: Seq<Seq<u8>>) -> Seq<u8>
    decreases parts.len(),
{
    if parts.len() == 0 {
        Seq::empty()
    } else if parts.len() == 1 {
        parts[0]
    } else {
        joined(parts.drop_last()) + sp() + parts.last()
    }
}

/// `[a b c]`.
pub open spec fn bracketed(parts: Seq<Seq<u8>>) -> Seq<u8> {
    seq![b'['] + joined(parts) + seq![b']']
}

/// Decimal digits of `n` (no sign, no leading zero).
pub open spec fn digits(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 { seq![(48 + n) as u8] } else { digits(n / 10).push((48 + n % 10) as u8) }
}

/// Decimal text of `i` (`-` before a negative value).
pub open spec fn decimal(i: int) -> Seq<u8> {
    if i < 0 { seq![b'-'] + digits((-i) as nat) } else { digits(i as nat) }
}

/// The lowercase hex digit of `x` (`x < 16`).
pub open spec fn hex_digit(x: nat) -> u8 {
    if x < 10 { (48 + x) as u8 } else { (87 + x) as u8 }
}

/// Two lowercase hex digits per byte.
pub open spec fn hex(bs: Seq<u8>) -> Seq<u8>
    decreases bs.len(),
{
    if bs.len() == 0 {
        Seq::empty()
    } else {
        hex(bs.drop_last()) + seq![hex_digit(bs.last() as nat / 16), hex_digit(bs.last() as nat % 16)]
    }
}

pub open spec fn bool_word(v: bool) -> Word {
    if v { Word::TrueWord } else { Word::FalseWord }
}

pub open spec fn int_kind_word(k: IntKind) -> Word {
    match k {
        IntKind::Int4 => Word::Int4,
        IntKind::Int8 => Word::Int8,
    }
}

pub open spec fn num_kind_word(k: NumKind) -> Word {
    match k {
        NumKind::Int4 => Word::Int4,
        NumKind::Int8 => Word::Int8,
        NumKind::Numeric => Word::Numeric,
    }
}

pub open spec fn arith_op_word(o: ArithOp) -> Word {
    match o {
        ArithOp::Add => Word::Add,
        ArithOp::Sub => Word::Sub,
        ArithOp::Mul => Word::Mul,
    }
}

pub open spec fn cmp_op_word(o: CmpOp) -> Word {
    match o {
        CmpOp::Eq => Word::Eq,
        CmpOp::Ne => Word::Ne,
        CmpOp::Lt => Word::Lt,
        CmpOp::Le => Word::Le,
        CmpOp::Gt => Word::Gt,
        CmpOp::Ge => Word::Ge,
    }
}

pub open spec fn cast_op_word(o: CastOp) -> Word {
    match o {
        CastOp::Int4ToInt8 => Word::Int4ToInt8,
        CastOp::IntToNumeric => Word::IntToNumeric,
        CastOp::DateToTimestamp => Word::DateToTimestamp,
    }
}

pub open spec fn scalar_fn_word(f: ScalarFn) -> Word {
    match f {
        ScalarFn::DivInt4 => Word::DivInt4,
        ScalarFn::DivInt8 => Word::DivInt8,
        ScalarFn::DivNumeric => Word::DivNumeric,
        ScalarFn::Like => Word::Like,
        ScalarFn::Substring2 => Word::Substring2,
        ScalarFn::Substring3 => Word::Substring3,
        ScalarFn::ExtractYear => Word::ExtractYear,
        ScalarFn::ExtractMonth => Word::ExtractMonth,
        ScalarFn::ExtractDay => Word::ExtractDay,
        ScalarFn::PadBpchar => Word::PadBpchar,
    }
}

pub open spec fn sx_scalar_ty(t: ScalarTy) -> Seq<u8> {
    match t {
        ScalarTy::Bool => node0(Word::Bool),
        ScalarTy::Int4 => node0(Word::Int4),
        ScalarTy::Int8 => node0(Word::Int8),
        ScalarTy::Numeric { scale } => node1(Word::Numeric, decimal(scale as int)),
        ScalarTy::Date => node0(Word::Date),
        ScalarTy::Timestamp => node0(Word::Timestamp),
        ScalarTy::Text => node0(Word::Text),
    }
}

pub open spec fn sx_lit(l: Literal) -> Seq<u8> {
    match l {
        Literal::Null { ty } => node1(Word::Null, sx_scalar_ty(ty)),
        Literal::Bool(v) => node1(Word::Bool, word(bool_word(v))),
        Literal::Int { v, kind } => node2(Word::Int, decimal(v), word(int_kind_word(kind))),
        Literal::Num { coeff, scale } => node2(Word::Num, decimal(coeff), decimal(scale as int)),
        Literal::Date { y, m, d } => node3(Word::Date, decimal(y), decimal(m), decimal(d)),
        Literal::Text(bs) => node1(Word::Text, seq![b'0', b'x'] + hex(bs)),
    }
}

pub open spec fn sx_expr(e: Expr) -> Seq<u8>
    decreases e, 0nat,
{
    match e {
        Expr::Col(i) => node1(Word::Col, decimal(i as int)),
        Expr::Lit(l) => node1(Word::Lit, sx_lit(l)),
        Expr::Neg { kind, arg } => node2(Word::Neg, word(num_kind_word(kind)), sx_expr(*arg)),
        Expr::Arith { op, kind, a, b } => node4(Word::Arith, word(arith_op_word(op)), word(num_kind_word(kind)), sx_expr(*a), sx_expr(*b)),
        Expr::Cast { cast, arg } => node2(Word::Cast, word(cast_op_word(cast)), sx_expr(*arg)),
        Expr::AddInterval { arg, months, days, micros } =>
            node4(Word::AddInterval, sx_expr(*arg), decimal(months as int), decimal(days as int), decimal(micros as int)),
        Expr::Call { f, args } => node2(Word::Call, word(scalar_fn_word(f)), sx_exprs(args)),
        Expr::If { cond, then_e, else_e } => node3(Word::If, sx_pred(*cond), sx_expr(*then_e), sx_expr(*else_e)),
        Expr::Subquery(q) => node1(Word::Subquery, sx_query(*q)),
    }
}

/// The text of every expression of a list.
pub open spec fn expr_texts(es: Seq<Expr>) -> Seq<Seq<u8>>
    decreases es, 0nat,
{
    Seq::new(es.len(), |i: int| if 0 <= i < es.len() { sx_expr(es[i]) } else { Seq::empty() })
}

pub open spec fn sx_exprs(es: Seq<Expr>) -> Seq<u8>
    decreases es, 1nat,
{
    bracketed(expr_texts(es))
}

pub open spec fn sx_pred(p: Pred) -> Seq<u8>
    decreases p, 0nat,
{
    match p {
        Pred::Cmp { op, a, b } => node3(Word::Cmp, word(cmp_op_word(op)), sx_expr(a), sx_expr(b)),
        Pred::And(a, b) => node2(Word::And, sx_pred(*a), sx_pred(*b)),
        Pred::Or(a, b) => node2(Word::Or, sx_pred(*a), sx_pred(*b)),
        Pred::Not(a) => node1(Word::Not, sx_pred(*a)),
        Pred::IsNull(e) => node1(Word::IsNull, sx_expr(e)),
        Pred::OfBool(e) => node1(Word::OfBool, sx_expr(e)),
        Pred::Exists(q) => node1(Word::Exists, sx_query(*q)),
        Pred::AnyCmp { op, e, q } => node3(Word::AnyCmp, word(cmp_op_word(op)), sx_expr(e), sx_query(*q)),
    }
}

pub open spec fn sx_agg(a: Agg) -> Seq<u8>
    decreases a, 0nat,
{
    match a {
        Agg::CountStar => node0(Word::CountStar),
        Agg::Count(e) => node1(Word::Count, sx_expr(e)),
        Agg::Sum { kind, arg } => node2(Word::Sum, word(num_kind_word(kind)), sx_expr(arg)),
        Agg::Min(e) => node1(Word::Min, sx_expr(e)),
        Agg::Max(e) => node1(Word::Max, sx_expr(e)),
        Agg::Avg { kind, arg } => node2(Word::Avg, word(num_kind_word(kind)), sx_expr(arg)),
        Agg::DistinctAgg(inner) => node1(Word::DistinctAgg, sx_agg(*inner)),
    }
}

/// The text of every aggregate of a list.
pub open spec fn agg_texts(aggs: Seq<Agg>) -> Seq<Seq<u8>>
    decreases aggs, 0nat,
{
    Seq::new(aggs.len(), |j: int| if 0 <= j < aggs.len() { sx_agg(aggs[j]) } else { Seq::empty() })
}

pub open spec fn sx_aggs(aggs: Seq<Agg>) -> Seq<u8>
    decreases aggs, 1nat,
{
    bracketed(agg_texts(aggs))
}

pub open spec fn sx_query(q: Query) -> Seq<u8>
    decreases q, 0nat,
{
    match q {
        Query::Table(t) => node1(Word::Table, decimal(t as int)),
        Query::Filter { pred, input } => node2(Word::Filter, sx_pred(pred), sx_query(*input)),
        Query::Project { exprs, input } => node2(Word::Project, sx_exprs(exprs), sx_query(*input)),
        Query::Product { left, right } => node2(Word::Product, sx_query(*left), sx_query(*right)),
        Query::LeftJoin { left, right, on } => node3(Word::LeftJoin, sx_query(*left), sx_query(*right), sx_pred(on)),
        Query::Aggregate { aggs, input } => node2(Word::Aggregate, sx_aggs(aggs), sx_query(*input)),
        Query::GroupBy { keys, aggs, input } => node3(Word::GroupBy, sx_exprs(keys), sx_aggs(aggs), sx_query(*input)),
        Query::Distinct(input) => node1(Word::Distinct, sx_query(*input)),
    }
}

pub open spec fn sx_key(k: OrderKey) -> Seq<u8> {
    node3(Word::OrderKey, decimal(k.col as int), word(bool_word(k.desc)), word(bool_word(k.nulls_first)))
}

pub open spec fn sx_keys(ks: Seq<OrderKey>) -> Seq<u8> {
    bracketed(Seq::new(ks.len(), |i: int| sx_key(ks[i])))
}

pub open spec fn sx_limit(limit: Option<nat>) -> Seq<u8> {
    match limit {
        None => word(Word::NoneWord),
        Some(n) => node1(Word::SomeWord, decimal(n as int)),
    }
}

pub open spec fn sx_ordered(q: OrderedQuery) -> Seq<u8> {
    node4(Word::OrderedQuery, sx_query(q.body), sx_keys(q.keys), sx_limit(q.limit), decimal(q.offset as int))
}

/// THE ECHO TEXT of a decoded statement (`(Malformed)` for undecodable bytes).
pub open spec fn render_spec(q: Option<OrderedQuery>) -> Seq<u8> {
    match q {
        Some(q) => sx_ordered(q),
        None => node0(Word::Malformed),
    }
}

// ======================================================================================= echo text (executable)

/// Append `s`.
fn put_bytes(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            out@ == old(out)@ + s@.subrange(0, i as int),
        decreases s@.len() - i,
    {
        out.push(s[i]);
        i += 1;
        assert(out@ =~= old(out)@ + s@.subrange(0, i as int));
    }
    assert(s@.subrange(0, s@.len() as int) =~= s@);
}

fn put_word(out: &mut Vec<u8>, w: Word)
    ensures
        final(out)@ == old(out)@ + word(w),
{
    put_bytes(out, word_bytes(w));
}

/// Append `(w`.
fn put_open(out: &mut Vec<u8>, w: Word)
    ensures
        final(out)@ == old(out)@ + lp() + word(w),
{
    out.push(b'(');
    put_word(out, w);
    assert(out@ =~= old(out)@ + lp() + word(w));
}

fn put_space(out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + sp(),
{
    out.push(b' ');
    assert(out@ =~= old(out)@ + sp());
}

fn put_close(out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + rp(),
{
    out.push(b')');
    assert(out@ =~= old(out)@ + rp());
}

/// Append ` (w)` pieces: the space, then the word (a node field that is a word).
fn put_field_word(out: &mut Vec<u8>, w: Word)
    ensures
        final(out)@ == old(out)@ + sp() + word(w),
{
    put_space(out);
    put_word(out, w);
}

fn put_digits(out: &mut Vec<u8>, n: u128)
    ensures
        final(out)@ == old(out)@ + digits(n as nat),
    decreases n,
{
    if n >= 10 {
        put_digits(out, n / 10);
    }
    let d = (n % 10) as u8;
    out.push(48 + d);
    proof {
        if n >= 10 {
            assert(digits(n as nat) == digits((n / 10) as nat).push((48 + n % 10) as u8));
        } else {
            assert(digits(n as nat) == seq![(48 + n) as u8]);
        }
        assert(out@ =~= old(out)@ + digits(n as nat));
    }
}

fn put_decimal(out: &mut Vec<u8>, v: i128)
    ensures
        final(out)@ == old(out)@ + decimal(v as int),
{
    if v < 0 {
        out.push(b'-');
        let magnitude: u128 = ((-(v + 1)) as u128) + 1;
        put_digits(out, magnitude);
        assert(out@ =~= old(out)@ + decimal(v as int));
    } else {
        put_digits(out, v as u128);
    }
}

fn hex_digit_exec(x: u8) -> (r: u8)
    requires
        x < 16,
    ensures
        r == hex_digit(x as nat),
{
    if x < 10 { 48 + x } else { 87 + x }
}

/// Append `hex(bs)`.
fn put_hex(out: &mut Vec<u8>, bs: &Vec<u8>)
    ensures
        final(out)@ == old(out)@ + hex(bs@),
{
    let mut i: usize = 0;
    assert(bs@.take(0) =~= Seq::<u8>::empty());
    assert(old(out)@ + hex(Seq::<u8>::empty()) =~= old(out)@);
    while i < bs.len()
        invariant
            i <= bs@.len(),
            out@ == old(out)@ + hex(bs@.take(i as int)),
        decreases bs@.len() - i,
    {
        let x = bs[i];
        out.push(hex_digit_exec(x / 16));
        out.push(hex_digit_exec(x % 16));
        proof {
            let next = bs@.take(i as int + 1);
            assert(next.drop_last() =~= bs@.take(i as int));
            assert(next.last() == x);
            assert(hex(next) == hex(bs@.take(i as int)) + seq![hex_digit(x as nat / 16), hex_digit(x as nat % 16)]);
        }
        i += 1;
        assert(out@ =~= old(out)@ + hex(bs@.take(i as int)));
    }
    assert(bs@.take(bs@.len() as int) =~= bs@);
}

fn bool_word_exec(v: bool) -> (w: Word)
    ensures
        w == bool_word(v),
{
    if v { Word::TrueWord } else { Word::FalseWord }
}

fn int_kind_word_exec(k: &IntKind) -> (w: Word)
    ensures
        w == int_kind_word(*k),
{
    match k {
        IntKind::Int4 => Word::Int4,
        IntKind::Int8 => Word::Int8,
    }
}

fn num_kind_word_exec(k: &NumKind) -> (w: Word)
    ensures
        w == num_kind_word(*k),
{
    match k {
        NumKind::Int4 => Word::Int4,
        NumKind::Int8 => Word::Int8,
        NumKind::Numeric => Word::Numeric,
    }
}

fn arith_op_word_exec(o: &ArithOp) -> (w: Word)
    ensures
        w == arith_op_word(*o),
{
    match o {
        ArithOp::Add => Word::Add,
        ArithOp::Sub => Word::Sub,
        ArithOp::Mul => Word::Mul,
    }
}

fn cmp_op_word_exec(o: &CmpOp) -> (w: Word)
    ensures
        w == cmp_op_word(*o),
{
    match o {
        CmpOp::Eq => Word::Eq,
        CmpOp::Ne => Word::Ne,
        CmpOp::Lt => Word::Lt,
        CmpOp::Le => Word::Le,
        CmpOp::Gt => Word::Gt,
        CmpOp::Ge => Word::Ge,
    }
}

fn cast_op_word_exec(o: &CastOp) -> (w: Word)
    ensures
        w == cast_op_word(*o),
{
    match o {
        CastOp::Int4ToInt8 => Word::Int4ToInt8,
        CastOp::IntToNumeric => Word::IntToNumeric,
        CastOp::DateToTimestamp => Word::DateToTimestamp,
    }
}

fn scalar_fn_word_exec(f: &ScalarFn) -> (w: Word)
    ensures
        w == scalar_fn_word(*f),
{
    match f {
        ScalarFn::DivInt4 => Word::DivInt4,
        ScalarFn::DivInt8 => Word::DivInt8,
        ScalarFn::DivNumeric => Word::DivNumeric,
        ScalarFn::Like => Word::Like,
        ScalarFn::Substring2 => Word::Substring2,
        ScalarFn::Substring3 => Word::Substring3,
        ScalarFn::ExtractYear => Word::ExtractYear,
        ScalarFn::ExtractMonth => Word::ExtractMonth,
        ScalarFn::ExtractDay => Word::ExtractDay,
        ScalarFn::PadBpchar => Word::PadBpchar,
    }
}

// The executable renderer appends each node's pieces to one buffer, so the buffer after a node is the left-nested
// chain `acc + lp() + word(w) + sp() + a + ... + rp()`. These lemmas fold such a chain into `acc + node_k(w, ..)`
// (associativity of `+`), so each step's proof is one equality.

proof fn lemma_node0(acc: Seq<u8>, w: Word)
    ensures
        acc + lp() + word(w) + rp() == acc + node0(w),
{
    assert(acc + lp() + word(w) + rp() =~= acc + node0(w));
}

proof fn lemma_node1(acc: Seq<u8>, w: Word, a: Seq<u8>)
    ensures
        acc + lp() + word(w) + sp() + a + rp() == acc + node1(w, a),
{
    assert(acc + lp() + word(w) + sp() + a + rp() =~= acc + node1(w, a));
}

proof fn lemma_node2(acc: Seq<u8>, w: Word, a: Seq<u8>, b: Seq<u8>)
    ensures
        acc + lp() + word(w) + sp() + a + sp() + b + rp() == acc + node2(w, a, b),
{
    assert(acc + lp() + word(w) + sp() + a + sp() + b + rp() =~= acc + node2(w, a, b));
}

proof fn lemma_node3(acc: Seq<u8>, w: Word, a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    ensures
        acc + lp() + word(w) + sp() + a + sp() + b + sp() + c + rp() == acc + node3(w, a, b, c),
{
    assert(acc + lp() + word(w) + sp() + a + sp() + b + sp() + c + rp() =~= acc + node3(w, a, b, c));
}

proof fn lemma_node4(acc: Seq<u8>, w: Word, a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, d: Seq<u8>)
    ensures
        acc + lp() + word(w) + sp() + a + sp() + b + sp() + c + sp() + d + rp() == acc + node4(w, a, b, c, d),
{
    assert(acc + lp() + word(w) + sp() + a + sp() + b + sp() + c + sp() + d + rp() =~= acc + node4(w, a, b, c, d));
}

/// A list's text so far after `[`: before item `i` (`take(i)`), and after appending item `i` (with a space unless it is
/// the first).
proof fn lemma_list_step(prefix: Seq<u8>, parts: Seq<Seq<u8>>, i: int)
    requires
        0 <= i < parts.len(),
    ensures
        i == 0 ==> prefix + joined(parts.take(i)) + parts[i] == prefix + joined(parts.take(i + 1)),
        i > 0 ==> prefix + joined(parts.take(i)) + sp() + parts[i] == prefix + joined(parts.take(i + 1)),
{
    let next = parts.take(i + 1);
    if i == 0 {
        assert(next.len() == 1 && next[0] == parts[0]);
        assert(parts.take(0) =~= Seq::<Seq<u8>>::empty());
        assert(prefix + joined(parts.take(i)) + parts[i] =~= prefix + joined(next));
    } else {
        assert(next.drop_last() =~= parts.take(i));
        assert(next.last() == parts[i]);
        assert(prefix + joined(parts.take(i)) + sp() + parts[i] =~= prefix + joined(next));
    }
}

/// `acc` followed by `[`, the list's items and `]` is `acc + bracketed(parts)`.
proof fn lemma_list_open(acc: Seq<u8>, parts: Seq<Seq<u8>>)
    ensures
        acc.push(b'[') == acc + seq![b'['] + joined(parts.take(0)),
{
    assert(parts.take(0) =~= Seq::<Seq<u8>>::empty());
    assert(acc.push(b'[') =~= acc + seq![b'['] + joined(parts.take(0)));
}

proof fn lemma_list_close(acc: Seq<u8>, parts: Seq<Seq<u8>>)
    ensures
        (acc + seq![b'['] + joined(parts.take(parts.len() as int))).push(b']') == acc + bracketed(parts),
{
    assert(parts.take(parts.len() as int) =~= parts);
    assert((acc + seq![b'['] + joined(parts)).push(b']') =~= acc + bracketed(parts));
}

fn put_scalar_ty(out: &mut Vec<u8>, t: &ScalarTy)
    ensures
        final(out)@ == old(out)@ + sx_scalar_ty(*t),
{
    let ghost acc = out@;
    match t {
        ScalarTy::Numeric { scale } => {
            put_open(out, Word::Numeric);
            put_space(out);
            put_decimal(out, *scale as i128);
            put_close(out);
            proof { lemma_node1(acc, Word::Numeric, decimal(*scale as int)); }
        },
        _ => {
            let w = match t {
                ScalarTy::Bool => Word::Bool,
                ScalarTy::Int4 => Word::Int4,
                ScalarTy::Int8 => Word::Int8,
                ScalarTy::Date => Word::Date,
                ScalarTy::Timestamp => Word::Timestamp,
                _ => Word::Text,
            };
            put_open(out, w);
            put_close(out);
            proof { lemma_node0(acc, w); }
        },
    }
}

fn put_lit(out: &mut Vec<u8>, l: &ELiteral)
    ensures
        final(out)@ == old(out)@ + sx_lit(view_lit(*l)),
{
    let ghost acc = out@;
    match l {
        ELiteral::Null { ty } => {
            put_open(out, Word::Null);
            put_space(out);
            put_scalar_ty(out, ty);
            put_close(out);
            proof { lemma_node1(acc, Word::Null, sx_scalar_ty(*ty)); }
        },
        ELiteral::Bool(v) => {
            put_open(out, Word::Bool);
            put_field_word(out, bool_word_exec(*v));
            put_close(out);
            proof { lemma_node1(acc, Word::Bool, word(bool_word(*v))); }
        },
        ELiteral::Int { v, kind } => {
            put_open(out, Word::Int);
            put_space(out);
            put_decimal(out, *v as i128);
            put_field_word(out, int_kind_word_exec(kind));
            put_close(out);
            proof { lemma_node2(acc, Word::Int, decimal(*v as int), word(int_kind_word(*kind))); }
        },
        ELiteral::Num { coeff, scale } => {
            put_open(out, Word::Num);
            put_space(out);
            put_decimal(out, *coeff);
            put_space(out);
            put_decimal(out, *scale as i128);
            put_close(out);
            proof { lemma_node2(acc, Word::Num, decimal(*coeff as int), decimal(*scale as int)); }
        },
        ELiteral::Date { y, m, d } => {
            put_open(out, Word::Date);
            put_space(out);
            put_decimal(out, *y as i128);
            put_space(out);
            put_decimal(out, *m as i128);
            put_space(out);
            put_decimal(out, *d as i128);
            put_close(out);
            proof { lemma_node3(acc, Word::Date, decimal(*y as int), decimal(*m as int), decimal(*d as int)); }
        },
        ELiteral::Text(bs) => {
            put_open(out, Word::Text);
            put_space(out);
            let ghost before_hex = out@;
            out.push(b'0');
            out.push(b'x');
            put_hex(out, bs);
            put_close(out);
            proof {
                assert(before_hex.push(b'0').push(b'x') + hex(bs@) =~= before_hex + (seq![b'0', b'x'] + hex(bs@)));
                lemma_node1(acc, Word::Text, seq![b'0', b'x'] + hex(bs@));
            }
        },
    }
}

fn put_expr(out: &mut Vec<u8>, e: &EExpr)
    ensures
        final(out)@ == old(out)@ + sx_expr(view_expr(*e)),
    decreases e, 1nat,
{
    let ghost acc = out@;
    match e {
        EExpr::Col(i) => {
            put_open(out, Word::Col);
            put_space(out);
            put_decimal(out, *i as i128);
            put_close(out);
            proof { lemma_node1(acc, Word::Col, decimal(*i as int)); }
        },
        EExpr::Lit(l) => {
            put_open(out, Word::Lit);
            put_space(out);
            put_lit(out, l);
            put_close(out);
            proof { lemma_node1(acc, Word::Lit, sx_lit(view_lit(*l))); }
        },
        EExpr::Neg { kind, arg } => {
            put_open(out, Word::Neg);
            put_field_word(out, num_kind_word_exec(kind));
            put_space(out);
            put_expr(out, arg);
            put_close(out);
            proof { lemma_node2(acc, Word::Neg, word(num_kind_word(*kind)), sx_expr(view_expr(**arg))); }
        },
        EExpr::Cast { cast, arg } => {
            put_open(out, Word::Cast);
            put_field_word(out, cast_op_word_exec(cast));
            put_space(out);
            put_expr(out, arg);
            put_close(out);
            proof { lemma_node2(acc, Word::Cast, word(cast_op_word(*cast)), sx_expr(view_expr(**arg))); }
        },
        EExpr::Subquery(q) => {
            put_open(out, Word::Subquery);
            put_space(out);
            put_query(out, q);
            put_close(out);
            proof { lemma_node1(acc, Word::Subquery, sx_query(view_query(**q))); }
        },
        _ => put_expr_compound(out, e),
    }
}

/// `put_expr` of the expressions with several subterms (`Arith`, `AddInterval`, `Call`, `If`).
fn put_expr_compound(out: &mut Vec<u8>, e: &EExpr)
    requires
        e is Arith || e is AddInterval || e is Call || e is If,
    ensures
        final(out)@ == old(out)@ + sx_expr(view_expr(*e)),
    decreases e, 0nat,
{
    let ghost acc = out@;
    match e {
        EExpr::Arith { op, kind, a, b } => {
            put_open(out, Word::Arith);
            put_field_word(out, arith_op_word_exec(op));
            put_field_word(out, num_kind_word_exec(kind));
            put_space(out);
            put_expr(out, a);
            put_space(out);
            put_expr(out, b);
            put_close(out);
            proof {
                lemma_node4(acc, Word::Arith, word(arith_op_word(*op)), word(num_kind_word(*kind)), sx_expr(view_expr(**a)), sx_expr(view_expr(**b)));
            }
        },
        EExpr::AddInterval { arg, months, days, micros } => {
            put_open(out, Word::AddInterval);
            put_space(out);
            put_expr(out, arg);
            put_space(out);
            put_decimal(out, *months as i128);
            put_space(out);
            put_decimal(out, *days as i128);
            put_space(out);
            put_decimal(out, *micros as i128);
            put_close(out);
            proof {
                lemma_node4(acc, Word::AddInterval, sx_expr(view_expr(**arg)), decimal(*months as int), decimal(*days as int), decimal(*micros as int));
            }
        },
        EExpr::Call { f, args } => {
            put_open(out, Word::Call);
            put_field_word(out, scalar_fn_word_exec(f));
            put_space(out);
            put_exprs(out, args);
            put_close(out);
            proof { lemma_node2(acc, Word::Call, word(scalar_fn_word(*f)), sx_exprs(view_exprs(args@))); }
        },
        EExpr::If { cond, then_e, else_e } => {
            put_open(out, Word::If);
            put_space(out);
            put_pred(out, cond);
            put_space(out);
            put_expr(out, then_e);
            put_space(out);
            put_expr(out, else_e);
            put_close(out);
            proof {
                lemma_node3(acc, Word::If, sx_pred(view_pred(**cond)), sx_expr(view_expr(**then_e)), sx_expr(view_expr(**else_e)));
            }
        },
        _ => {},
    }
}

fn put_exprs(out: &mut Vec<u8>, es: &Vec<EExpr>)
    ensures
        final(out)@ == old(out)@ + sx_exprs(view_exprs(es@)),
    decreases es, 2nat,
{
    let ghost parts = expr_texts(view_exprs(es@));
    let ghost prefix = old(out)@ + seq![b'['];
    proof {
        lemma_view_exprs_index(es@);
        lemma_list_open(old(out)@, parts);
    }
    out.push(b'[');
    let mut i: usize = 0;
    while i < es.len()
        invariant
            i <= es@.len(),
            parts.len() == es@.len(),
            forall|k: int| 0 <= k < es@.len() ==> #[trigger] parts[k] == sx_expr(view_expr(es@[k])),
            prefix == old(out)@ + seq![b'['],
            out@ == prefix + joined(parts.take(i as int)),
        decreases es@.len() - i,
    {
        if i > 0 {
            put_space(out);
        }
        put_expr(out, &es[i]);
        proof { lemma_list_step(prefix, parts, i as int); }
        i += 1;
    }
    out.push(b']');
    proof { lemma_list_close(old(out)@, parts); }
}

fn put_pred(out: &mut Vec<u8>, p: &EPred)
    ensures
        final(out)@ == old(out)@ + sx_pred(view_pred(*p)),
    decreases p, 1nat,
{
    let ghost acc = out@;
    match p {
        EPred::Not(a) => {
            put_open(out, Word::Not);
            put_space(out);
            put_pred(out, a);
            put_close(out);
            proof { lemma_node1(acc, Word::Not, sx_pred(view_pred(**a))); }
        },
        EPred::IsNull(e) => {
            put_open(out, Word::IsNull);
            put_space(out);
            put_expr(out, e);
            put_close(out);
            proof { lemma_node1(acc, Word::IsNull, sx_expr(view_expr(*e))); }
        },
        EPred::OfBool(e) => {
            put_open(out, Word::OfBool);
            put_space(out);
            put_expr(out, e);
            put_close(out);
            proof { lemma_node1(acc, Word::OfBool, sx_expr(view_expr(*e))); }
        },
        EPred::Exists(q) => {
            put_open(out, Word::Exists);
            put_space(out);
            put_query(out, q);
            put_close(out);
            proof { lemma_node1(acc, Word::Exists, sx_query(view_query(**q))); }
        },
        _ => put_pred_compound(out, p),
    }
}

/// `put_pred` of the conditions with two subterms (`Cmp`, `And`, `Or`, `AnyCmp`).
fn put_pred_compound(out: &mut Vec<u8>, p: &EPred)
    requires
        p is Cmp || p is And || p is Or || p is AnyCmp,
    ensures
        final(out)@ == old(out)@ + sx_pred(view_pred(*p)),
    decreases p, 0nat,
{
    let ghost acc = out@;
    match p {
        EPred::Cmp { op, a, b } => {
            put_open(out, Word::Cmp);
            put_field_word(out, cmp_op_word_exec(op));
            put_space(out);
            put_expr(out, a);
            put_space(out);
            put_expr(out, b);
            put_close(out);
            proof { lemma_node3(acc, Word::Cmp, word(cmp_op_word(*op)), sx_expr(view_expr(*a)), sx_expr(view_expr(*b))); }
        },
        EPred::And(a, b) => {
            put_open(out, Word::And);
            put_space(out);
            put_pred(out, a);
            put_space(out);
            put_pred(out, b);
            put_close(out);
            proof { lemma_node2(acc, Word::And, sx_pred(view_pred(**a)), sx_pred(view_pred(**b))); }
        },
        EPred::Or(a, b) => {
            put_open(out, Word::Or);
            put_space(out);
            put_pred(out, a);
            put_space(out);
            put_pred(out, b);
            put_close(out);
            proof { lemma_node2(acc, Word::Or, sx_pred(view_pred(**a)), sx_pred(view_pred(**b))); }
        },
        EPred::AnyCmp { op, e, q } => {
            put_open(out, Word::AnyCmp);
            put_field_word(out, cmp_op_word_exec(op));
            put_space(out);
            put_expr(out, e);
            put_space(out);
            put_query(out, q);
            put_close(out);
            proof { lemma_node3(acc, Word::AnyCmp, word(cmp_op_word(*op)), sx_expr(view_expr(*e)), sx_query(view_query(**q))); }
        },
        _ => {},
    }
}

fn put_agg(out: &mut Vec<u8>, a: &EAgg)
    ensures
        final(out)@ == old(out)@ + sx_agg(view_agg(*a)),
    decreases a, 1nat,
{
    let ghost acc = out@;
    match a {
        EAgg::CountStar => {
            put_open(out, Word::CountStar);
            put_close(out);
            proof { lemma_node0(acc, Word::CountStar); }
        },
        EAgg::Count(e) => {
            put_open(out, Word::Count);
            put_space(out);
            put_expr(out, e);
            put_close(out);
            proof { lemma_node1(acc, Word::Count, sx_expr(view_expr(*e))); }
        },
        EAgg::Min(e) => {
            put_open(out, Word::Min);
            put_space(out);
            put_expr(out, e);
            put_close(out);
            proof { lemma_node1(acc, Word::Min, sx_expr(view_expr(*e))); }
        },
        EAgg::Max(e) => {
            put_open(out, Word::Max);
            put_space(out);
            put_expr(out, e);
            put_close(out);
            proof { lemma_node1(acc, Word::Max, sx_expr(view_expr(*e))); }
        },
        EAgg::DistinctAgg(inner) => {
            put_open(out, Word::DistinctAgg);
            put_space(out);
            put_agg(out, inner);
            put_close(out);
            proof { lemma_node1(acc, Word::DistinctAgg, sx_agg(view_agg(**inner))); }
        },
        _ => put_agg_kinded(out, a),
    }
}

/// `put_agg` of `Sum` and `Avg` (an operand type and an argument).
fn put_agg_kinded(out: &mut Vec<u8>, a: &EAgg)
    requires
        a is Sum || a is Avg,
    ensures
        final(out)@ == old(out)@ + sx_agg(view_agg(*a)),
    decreases a, 0nat,
{
    let ghost acc = out@;
    match a {
        EAgg::Sum { kind, arg } => {
            put_open(out, Word::Sum);
            put_field_word(out, num_kind_word_exec(kind));
            put_space(out);
            put_expr(out, arg);
            put_close(out);
            proof { lemma_node2(acc, Word::Sum, word(num_kind_word(*kind)), sx_expr(view_expr(*arg))); }
        },
        EAgg::Avg { kind, arg } => {
            put_open(out, Word::Avg);
            put_field_word(out, num_kind_word_exec(kind));
            put_space(out);
            put_expr(out, arg);
            put_close(out);
            proof { lemma_node2(acc, Word::Avg, word(num_kind_word(*kind)), sx_expr(view_expr(*arg))); }
        },
        _ => {},
    }
}

fn put_aggs(out: &mut Vec<u8>, aggs: &Vec<EAgg>)
    ensures
        final(out)@ == old(out)@ + sx_aggs(view_aggs(aggs@)),
    decreases aggs, 2nat,
{
    let ghost parts = agg_texts(view_aggs(aggs@));
    let ghost prefix = old(out)@ + seq![b'['];
    proof {
        lemma_view_aggs_index(aggs@);
        lemma_list_open(old(out)@, parts);
    }
    out.push(b'[');
    let mut i: usize = 0;
    while i < aggs.len()
        invariant
            i <= aggs@.len(),
            parts.len() == aggs@.len(),
            forall|k: int| 0 <= k < aggs@.len() ==> #[trigger] parts[k] == sx_agg(view_agg(aggs@[k])),
            prefix == old(out)@ + seq![b'['],
            out@ == prefix + joined(parts.take(i as int)),
        decreases aggs@.len() - i,
    {
        if i > 0 {
            put_space(out);
        }
        put_agg(out, &aggs[i]);
        proof { lemma_list_step(prefix, parts, i as int); }
        i += 1;
    }
    out.push(b']');
    proof { lemma_list_close(old(out)@, parts); }
}

fn put_query(out: &mut Vec<u8>, q: &EQuery)
    ensures
        final(out)@ == old(out)@ + sx_query(view_query(*q)),
    decreases q, 1nat,
{
    let ghost acc = out@;
    match q {
        EQuery::Table(t) => {
            put_open(out, Word::Table);
            put_space(out);
            put_decimal(out, *t as i128);
            put_close(out);
            proof { lemma_node1(acc, Word::Table, decimal(*t as int)); }
        },
        EQuery::Filter { pred, input } => {
            put_open(out, Word::Filter);
            put_space(out);
            put_pred(out, pred);
            put_space(out);
            put_query(out, input);
            put_close(out);
            proof { lemma_node2(acc, Word::Filter, sx_pred(view_pred(*pred)), sx_query(view_query(**input))); }
        },
        EQuery::Product { left, right } => {
            put_open(out, Word::Product);
            put_space(out);
            put_query(out, left);
            put_space(out);
            put_query(out, right);
            put_close(out);
            proof { lemma_node2(acc, Word::Product, sx_query(view_query(**left)), sx_query(view_query(**right))); }
        },
        EQuery::Distinct(input) => {
            put_open(out, Word::Distinct);
            put_space(out);
            put_query(out, input);
            put_close(out);
            proof { lemma_node1(acc, Word::Distinct, sx_query(view_query(**input))); }
        },
        _ => put_query_compound(out, q),
    }
}

/// `put_query` of the queries with lists or three subterms (`Project`, `LeftJoin`, `Aggregate`, `GroupBy`).
fn put_query_compound(out: &mut Vec<u8>, q: &EQuery)
    requires
        q is Project || q is LeftJoin || q is Aggregate || q is GroupBy,
    ensures
        final(out)@ == old(out)@ + sx_query(view_query(*q)),
    decreases q, 0nat,
{
    let ghost acc = out@;
    match q {
        EQuery::Project { exprs, input } => {
            put_open(out, Word::Project);
            put_space(out);
            put_exprs(out, exprs);
            put_space(out);
            put_query(out, input);
            put_close(out);
            proof { lemma_node2(acc, Word::Project, sx_exprs(view_exprs(exprs@)), sx_query(view_query(**input))); }
        },
        EQuery::LeftJoin { left, right, on } => {
            put_open(out, Word::LeftJoin);
            put_space(out);
            put_query(out, left);
            put_space(out);
            put_query(out, right);
            put_space(out);
            put_pred(out, on);
            put_close(out);
            proof {
                lemma_node3(acc, Word::LeftJoin, sx_query(view_query(**left)), sx_query(view_query(**right)), sx_pred(view_pred(*on)));
            }
        },
        EQuery::Aggregate { aggs, input } => {
            put_open(out, Word::Aggregate);
            put_space(out);
            put_aggs(out, aggs);
            put_space(out);
            put_query(out, input);
            put_close(out);
            proof { lemma_node2(acc, Word::Aggregate, sx_aggs(view_aggs(aggs@)), sx_query(view_query(**input))); }
        },
        EQuery::GroupBy { keys, aggs, input } => {
            put_open(out, Word::GroupBy);
            put_space(out);
            put_exprs(out, keys);
            put_space(out);
            put_aggs(out, aggs);
            put_space(out);
            put_query(out, input);
            put_close(out);
            proof {
                lemma_node3(acc, Word::GroupBy, sx_exprs(view_exprs(keys@)), sx_aggs(view_aggs(aggs@)), sx_query(view_query(**input)));
            }
        },
        _ => {},
    }
}

/// Append one ORDER BY key's text.
fn put_key(out: &mut Vec<u8>, k: &EOrderKey)
    ensures
        final(out)@ == old(out)@ + sx_key(view_order_key(*k)),
{
    let ghost acc = out@;
    put_open(out, Word::OrderKey);
    put_space(out);
    put_decimal(out, k.col as i128);
    put_field_word(out, bool_word_exec(k.desc));
    put_field_word(out, bool_word_exec(k.nulls_first));
    put_close(out);
    proof { lemma_node3(acc, Word::OrderKey, decimal(k.col as int), word(bool_word(k.desc)), word(bool_word(k.nulls_first))); }
}

fn put_keys(out: &mut Vec<u8>, ks: &Vec<EOrderKey>)
    ensures
        final(out)@ == old(out)@ + sx_keys(view_order_keys(ks@)),
{
    let ghost parts = Seq::new(view_order_keys(ks@).len(), |i: int| sx_key(view_order_keys(ks@)[i]));
    let ghost prefix = old(out)@ + seq![b'['];
    proof {
        lemma_list_open(old(out)@, parts);
    }
    out.push(b'[');
    let mut i: usize = 0;
    while i < ks.len()
        invariant
            i <= ks@.len(),
            parts == Seq::new(view_order_keys(ks@).len(), |i: int| sx_key(view_order_keys(ks@)[i])),
            parts.len() == ks@.len(),
            prefix == old(out)@ + seq![b'['],
            out@ == prefix + joined(parts.take(i as int)),
        decreases ks@.len() - i,
    {
        if i > 0 {
            put_space(out);
        }
        put_key(out, &ks[i]);
        proof {
            assert(parts[i as int] == sx_key(view_order_key(ks@[i as int])));
            lemma_list_step(prefix, parts, i as int);
        }
        i += 1;
    }
    out.push(b']');
    proof { lemma_list_close(old(out)@, parts); }
}

/// The spec view of a decoded statement (or of its absence).
pub open spec fn view_decoded(q: Option<EOrderedQuery>) -> Option<OrderedQuery> {
    match q {
        Some(q) => Some(view_ordered(q)),
        None => None,
    }
}

/// Append the text of an optional LIMIT.
fn put_limit(out: &mut Vec<u8>, limit: Option<u64>)
    ensures
        final(out)@ == old(out)@ + sx_limit(match limit { Some(n) => Some(n as nat), None => None }),
{
    let ghost acc = out@;
    match limit {
        None => put_word(out, Word::NoneWord),
        Some(n) => {
            put_open(out, Word::SomeWord);
            put_space(out);
            put_decimal(out, n as i128);
            put_close(out);
            proof { lemma_node1(acc, Word::SomeWord, decimal(n as int)); }
        },
    }
}

/// THE EXECUTABLE ECHO: the echo text of a decoded statement, equal to `render_spec` of its view.
pub fn render_query(q: &Option<EOrderedQuery>) -> (r: Vec<u8>)
    ensures
        r@ == render_spec(view_decoded(*q)),
{
    let mut out: Vec<u8> = Vec::new();
    let ghost acc = out@;
    match q {
        None => {
            put_open(&mut out, Word::Malformed);
            put_close(&mut out);
            proof {
                lemma_node0(acc, Word::Malformed);
                assert(acc + node0(Word::Malformed) =~= node0(Word::Malformed));
            }
        },
        Some(q) => {
            put_open(&mut out, Word::OrderedQuery);
            put_space(&mut out);
            put_query(&mut out, &q.body);
            put_space(&mut out);
            put_keys(&mut out, &q.keys);
            put_space(&mut out);
            put_limit(&mut out, q.limit);
            put_space(&mut out);
            put_decimal(&mut out, q.offset as i128);
            put_close(&mut out);
            proof {
                let v = view_ordered(*q);
                lemma_node4(acc, Word::OrderedQuery, sx_query(v.body), sx_keys(v.keys), sx_limit(v.limit), decimal(v.offset as int));
                assert(acc + sx_ordered(v) =~= sx_ordered(v));
            }
        },
    }
    out
}

} // verus!
