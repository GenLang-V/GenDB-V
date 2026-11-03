//! Verified checkers of the evaluator's input domain. Each decides one `spec` predicate exactly:
//! - `check_schema` decides `spec::types::schema_wf`: declared column types (`tables_wf`) and declared
//!   constraints (`exec::relational::constraints::check_constraints_wf_exec`);
//! - `check_db` decides `spec::typing::db_wf`: a well-formed schema, one relation per table, and every value in
//!   its column's domain (`value_in_column`);
//! - `check_ordered` decides `spec::typing::wf_ordered`: a well-formed schema, a typed body and ORDER BY keys that
//!   name output columns. Typing is the executable mirror of the deterministic static typing of `spec::typing`
//!   (`type_query_exec` and the functions below it); `constraints` reuses it to type CHECK conditions.
//! `exec::relational::entry::evaluate` calls `check_db` and `check_ordered`; the evaluator's theorems are stated
//! for the inputs they accept. Nothing here refuses with `Capacity`: every check is exact.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::typing::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::numeric::*;
use crate::exec::datetime::*;
use crate::exec::scalar::*;
use crate::exec::expr::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::constraints::*;
use crate::exec::fns::*;
use crate::exec::aggs::avg::*;
use crate::exec::aggs::minmax::*;
use crate::exec::aggs::distinct::*;

verus! {

// `spec::limits::numeric_max_precision`: the largest `numeric(p, s)` precision.
const NUMERIC_MAX_PRECISION: u32 = 1000;
// `spec::limits::char_length_max`: the largest `varchar(n)` / `char(n)` length in characters.
const CHAR_LENGTH_MAX: u32 = 10485760;
// `spec::limits::numeric_dscale_max` is `exec::expr::NUMERIC_DSCALE_MAX`.

// ---------------------------------------------------------------- schema

/// `spec::types::schema_wf`.
pub fn check_schema(schema: &Vec<ETableSchema>) -> (b: bool)
    ensures b == schema_wf(view_schema(schema@)),
{
    tables_wf_exec(schema) && check_constraints_wf_exec(schema)
}

/// `spec::types::tables_wf`.
fn tables_wf_exec(schema: &Vec<ETableSchema>) -> (b: bool)
    ensures b == tables_wf(view_schema(schema@)),
{
    let ghost g = view_schema(schema@);
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<TableSchema>::empty()); }
    while i < schema.len()
        invariant i <= schema.len(), g == view_schema(schema@), tables_wf(g.take(i as int)),
        decreases schema.len() - i,
    {
        proof { assert(g[i as int] == view_table_schema(schema@[i as int])); }
        if !columns_wf_exec(&schema[i].columns) {
            proof { if tables_wf(g) { lemma_tables_wf_prefix(g, i as int); } }
            return false;
        }
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
        }
        i = i + 1;
    }
    proof { assert(g.take(schema.len() as int) =~= g); }
    true
}

proof fn lemma_tables_wf_prefix(s: Schema, k: int)
    requires 0 <= k <= s.len(), tables_wf(s),
    ensures tables_wf(s.take(k)), k < s.len() ==> columns_wf(s[k].columns),
    decreases s.len(),
{
    if k < s.len() {
        let d = s.drop_last();
        assert(d.take(k) =~= s.take(k));
        if k < d.len() {
            assert(d[k] == s[k]);
        }
        lemma_tables_wf_prefix(d, k);
    } else {
        assert(s.take(k) =~= s);
    }
}

/// `spec::types::columns_wf`.
fn columns_wf_exec(cols: &Vec<Column>) -> (b: bool)
    ensures b == columns_wf(cols@),
{
    let mut i: usize = 0;
    proof { assert(cols@.take(0) =~= Seq::<Column>::empty()); }
    while i < cols.len()
        invariant i <= cols.len(), columns_wf(cols@.take(i as int)),
        decreases cols.len() - i,
    {
        if !sql_type_wf_exec(cols[i].ty) {
            proof { if columns_wf(cols@) { lemma_columns_wf_prefix(cols@, i as int); } }
            return false;
        }
        proof {
            let t = cols@.take(i as int + 1);
            assert(t.drop_last() =~= cols@.take(i as int));
        }
        i = i + 1;
    }
    proof { assert(cols@.take(cols.len() as int) =~= cols@); }
    true
}

proof fn lemma_columns_wf_prefix(cols: Seq<Column>, k: int)
    requires 0 <= k <= cols.len(), columns_wf(cols),
    ensures columns_wf(cols.take(k)), k < cols.len() ==> sql_type_wf(cols[k].ty),
    decreases cols.len(),
{
    if k < cols.len() {
        let d = cols.drop_last();
        assert(d.take(k) =~= cols.take(k));
        if k < d.len() {
            assert(d[k] == cols[k]);
        }
        lemma_columns_wf_prefix(d, k);
    } else {
        assert(cols.take(k) =~= cols);
    }
}

/// `spec::types::sql_type_wf`.
fn sql_type_wf_exec(t: SqlType) -> (b: bool)
    ensures b == sql_type_wf(t),
{
    match t {
        SqlType::Numeric { precision, scale } => 1 <= precision && precision <= NUMERIC_MAX_PRECISION && scale <= precision,
        SqlType::Varchar { max_chars } => 1 <= max_chars && max_chars <= CHAR_LENGTH_MAX,
        SqlType::Bpchar { len } => 1 <= len && len <= CHAR_LENGTH_MAX,
        _ => true,
    }
}

// ---------------------------------------------------------------- database values

/// `spec::typing::db_wf`.
pub fn check_db(db: &EDatabase) -> (b: bool)
    ensures b == db_wf(db@),
{
    let ghost g = db@;
    if !check_schema(&db.schema) {
        return false;
    }
    if db.tables.len() != db.schema.len() {
        return false;
    }
    let mut t: usize = 0;
    while t < db.tables.len()
        invariant
            t <= db.tables.len(), db.tables.len() == db.schema.len(), g == db@,
            forall|tt: int, i: int| 0 <= tt < t && 0 <= i < g.tables[tt].len()
                ==> row_in_table(#[trigger] g.tables[tt][i], g.schema[tt]),
        decreases db.tables.len() - t,
    {
        let rel = &db.tables[t];
        proof {
            assert(g.tables[t as int] == view_rows(rel@));
            assert(g.schema[t as int] == view_table_schema(db.schema@[t as int]));
        }
        let mut i: usize = 0;
        while i < rel.len()
            invariant
                t < db.tables.len(), db.tables.len() == db.schema.len(), g == db@,
                i <= rel.len(), rel == &db.tables@[t as int],
                g.tables[t as int] == view_rows(rel@),
                g.schema[t as int] == view_table_schema(db.schema@[t as int]),
                forall|tt: int, k: int| 0 <= tt < t && 0 <= k < g.tables[tt].len()
                    ==> row_in_table(#[trigger] g.tables[tt][k], g.schema[tt]),
                forall|k: int| 0 <= k < i ==> row_in_table(#[trigger] g.tables[t as int][k], g.schema[t as int]),
            decreases rel.len() - i,
        {
            if !check_row(&rel[i], &db.schema[t]) {
                assert(!row_in_table(g.tables[t as int][i as int], g.schema[t as int]));
                return false;
            }
            i = i + 1;
        }
        t = t + 1;
    }
    true
}

/// `spec::typing::row_in_table`: the row's arity and every value in its column's domain.
pub fn check_row(r: &ERow, t: &ETableSchema) -> (b: bool)
    ensures b == row_in_table(view_row(r@), view_table_schema(*t)),
{
    let ghost g = view_row(r@);
    if r.len() != t.columns.len() {
        return false;
    }
    let mut c: usize = 0;
    while c < r.len()
        invariant
            c <= r.len(), r.len() == t.columns.len(), g == view_row(r@),
            forall|j: int| 0 <= j < c ==> value_in_column(#[trigger] g[j], t.columns@[j]),
        decreases r.len() - c,
    {
        if !value_in_column_exec(&r[c], t.columns[c]) {
            assert(!value_in_column(g[c as int], t.columns@[c as int]));
            return false;
        }
        c = c + 1;
    }
    true
}

/// `spec::typing::value_in_column`.
pub fn value_in_column_exec(v: &EVal, c: Column) -> (b: bool)
    ensures b == value_in_column(v@, c),
{
    match v {
        EVal::Null => c.nullable,
        EVal::Bool(_) => matches!(c.ty, SqlType::Bool),
        EVal::Int(x) => match c.ty {
            SqlType::Int4 => int_in_range_exec(IntKind::Int4, *x as i128),
            SqlType::Int8 => int_in_range_exec(IntKind::Int8, *x as i128),
            _ => false,
        },
        EVal::Num { coeff, scale } => match c.ty {
            SqlType::Numeric { precision, scale: s } => *scale == s && coeff_fits_precision(*coeff, precision),
            _ => false,
        },
        EVal::Date(d) => matches!(c.ty, SqlType::Date) && date_valid_exec(*d as i64),
        EVal::Ts(t) => matches!(c.ty, SqlType::Timestamp) && ts_valid_exec(*t as i128),
        EVal::Text(b) => match c.ty {
            SqlType::Text => text_ok_exec(b),
            SqlType::Varchar { max_chars } => text_ok_exec(b) && utf8_chars_exec(b) as u64 <= max_chars as u64,
            SqlType::Bpchar { len } => text_ok_exec(b) && utf8_chars_exec(b) as u64 <= len as u64
                && (b.len() == 0 || b[b.len() - 1] != 0x20u8),
            _ => false,
        },
    }
}

/// `abs(coeff) < 10^precision` for an `i128` coefficient: always true from 39 digits on (`i128::MAX < 10^39`),
/// otherwise compared against `10^precision`, which fits `i128` up to 38 digits.
fn coeff_fits_precision(coeff: i128, precision: u32) -> (r: bool)
    ensures r == (abs(coeff as int) < pow10(precision as nat)),
{
    if precision >= 39 {
        proof {
            lemma_pow10_i128_boundary();
            lemma_pow10_monotone(39, precision as nat);
        }
        true
    } else {
        proof {
            lemma_pow10_i128_boundary();
            lemma_pow10_monotone(precision as nat, 38);
            lemma_pow10_positive(precision as nat);
        }
        match pow10_exec(precision) {
            Some(p) => -p < coeff && coeff < p,
            None => { assert(false); false },
        }
    }
}

/// `spec::typing::text_ok`: no NUL byte.
fn text_ok_exec(b: &Vec<u8>) -> (r: bool)
    ensures r == text_ok(b@),
{
    let mut i: usize = 0;
    while i < b.len()
        invariant i <= b.len(), forall|j: int| 0 <= j < i ==> #[trigger] b@[j] != 0u8,
        decreases b.len() - i,
    {
        if b[i] == 0 {
            assert(b@[i as int] == 0u8);
            return false;
        }
        i = i + 1;
    }
    true
}

/// `spec::typing::utf8_chars`: the bytes that are not UTF-8 continuation bytes (`10xxxxxx`).
fn utf8_chars_exec(b: &Vec<u8>) -> (n: usize)
    ensures n as nat == utf8_chars(b@),
{
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < b.len()
        invariant i <= b.len(), n <= i, n as nat == utf8_chars(b@.take(i as int)),
        decreases b.len() - i,
    {
        proof {
            let t = b@.take(i as int + 1);
            assert(t.drop_last() =~= b@.take(i as int));
        }
        if !(0x80u8 <= b[i] && b[i] < 0xC0u8) {
            n = n + 1;
        }
        i = i + 1;
    }
    proof { assert(b@.take(b.len() as int) =~= b@); }
    n
}

// ---------------------------------------------------------------- checked statements

/// `spec::typing::wf_ordered`: well-formed schema, typed body, ORDER BY keys name output columns.
pub fn check_ordered(schema: &Vec<ETableSchema>, oq: &EOrderedQuery) -> (b: bool)
    ensures b == wf_ordered(view_schema(schema@), view_ordered(*oq)),
{
    if !check_schema(schema) {
        return false;
    }
    let ctx: Vec<ColTy> = Vec::new();
    proof { assert(ctx@ =~= Seq::<ColTy>::empty()); }
    let tys = match type_query_exec(schema, &ctx, &oq.body) {
        Some(t) => t,
        None => return false,
    };
    let ghost gk = view_ordered(*oq).keys;
    let mut i: usize = 0;
    proof { assert(gk.take(0) =~= Seq::<OrderKey>::empty()); }
    while i < oq.keys.len()
        invariant
            i <= oq.keys.len(), gk == view_ordered(*oq).keys, gk.len() == oq.keys.len(),
            schema_wf(view_schema(schema@)),
            type_query(view_schema(schema@), Seq::empty(), view_ordered(*oq).body) == Some(tys@),
            keys_in_range(gk.take(i as int), tys@.len()),
        decreases oq.keys.len() - i,
    {
        proof {
            let t = gk.take(i as int + 1);
            assert(t.drop_last() =~= gk.take(i as int));
            assert(t.last() == view_order_key(oq.keys@[i as int]));
        }
        if oq.keys[i].col >= tys.len() {
            proof { lemma_keys_in_range_prefix(gk, tys@.len(), i as int + 1); }
            return false;
        }
        i = i + 1;
    }
    proof { assert(gk.take(oq.keys.len() as int) =~= gk); }
    true
}

proof fn lemma_keys_in_range_prefix(keys: Seq<OrderKey>, n: nat, k: int)
    requires 0 <= k <= keys.len(), keys_in_range(keys.take(k), n) == false,
    ensures !keys_in_range(keys, n),
    decreases keys.len(),
{
    if k < keys.len() {
        let d = keys.drop_last();
        assert(d.take(k) =~= keys.take(k));
        lemma_keys_in_range_prefix(d, n, k);
    } else {
        assert(keys.take(k) =~= keys);
    }
}

// ---------------------------------------------------------------- static typing (`spec::typing`)
//
// `type_query_exec`, `type_pred_exec`, `type_expr_exec`, `type_exprs_exec`, `type_agg_exec` and `type_aggs_exec`
// are one mutual recursion, like their spec counterparts. `None` / `false` = ill-typed.

/// `spec::typing::type_query`: output column types of a query under outer context types `ctx`.
pub fn type_query_exec(schema: &Vec<ETableSchema>, ctx: &Vec<ColTy>, q: &EQuery) -> (r: Option<Vec<ColTy>>)
    ensures
        match r {
            Some(ts) => type_query(view_schema(schema@), ctx@, view_query(*q)) == Some(ts@),
            None => type_query(view_schema(schema@), ctx@, view_query(*q)) is None,
        },
    decreases q, 0nat,
{
    let ghost gs = view_schema(schema@);
    match q {
        EQuery::Table(t) => {
            if *t < schema.len() {
                proof { assert(gs[*t as int] == view_table_schema(schema@[*t as int])); }
                Some(table_tys_exec(&schema[*t]))
            } else {
                None
            }
        },
        EQuery::Filter { pred, input } => {
            let tys = type_query_exec(schema, ctx, input)?;
            let env = concat_tys(ctx, &tys);
            if type_pred_exec(schema, &env, pred) { Some(tys) } else { None }
        },
        EQuery::Project { exprs, input } => {
            let tys = type_query_exec(schema, ctx, input)?;
            let env = concat_tys(ctx, &tys);
            type_exprs_exec(schema, &env, exprs)
        },
        EQuery::Product { left, right } => {
            let l = type_query_exec(schema, ctx, left);
            let r = type_query_exec(schema, ctx, right);
            match (l, r) {
                (Some(l), Some(r)) => Some(concat_tys(&l, &r)),
                _ => None,
            }
        },
        EQuery::LeftJoin { left, right, on } => {
            let l = type_query_exec(schema, ctx, left);
            let r = type_query_exec(schema, ctx, right);
            match (l, r) {
                (Some(l), Some(r)) => {
                    let lr = concat_tys(&l, &r);
                    let env = concat_tys(ctx, &lr);
                    proof { assert(ctx@ + l@ + r@ =~= ctx@ + (l@ + r@)); }
                    if type_pred_exec(schema, &env, on) {
                        let nr = nullable_all_exec(&r);
                        Some(concat_tys(&l, &nr))
                    } else {
                        None
                    }
                },
                _ => None,
            }
        },
        EQuery::Aggregate { aggs, input } => {
            let tys = type_query_exec(schema, ctx, input)?;
            let env = concat_tys(ctx, &tys);
            type_aggs_exec(schema, &env, aggs)
        },
        EQuery::GroupBy { keys, aggs, input } => {
            let tys = type_query_exec(schema, ctx, input)?;
            let env = concat_tys(ctx, &tys);
            let k = type_exprs_exec(schema, &env, keys);
            let a = type_aggs_exec(schema, &env, aggs);
            match (k, a) {
                (Some(k), Some(a)) => Some(concat_tys(&k, &a)),
                _ => None,
            }
        },
        // `spec::typing::distinct_ty` is the identity: DISTINCT keeps the input's types.
        EQuery::Distinct(input) => type_query_exec(schema, ctx, input),
    }
}

/// `spec::typing::type_pred`: the condition is well-typed under the environment types `env`.
pub fn type_pred_exec(schema: &Vec<ETableSchema>, env: &Vec<ColTy>, p: &EPred) -> (b: bool)
    ensures b == type_pred(view_schema(schema@), env@, view_pred(*p)),
    decreases p, 0nat,
{
    match p {
        EPred::Cmp { op, a, b } => match (type_expr_exec(schema, env, a), type_expr_exec(schema, env, b)) {
            (Some(ta), Some(tb)) => family_exec(ta.ty) == family_exec(tb.ty),
            _ => false,
        },
        EPred::And(a, b) | EPred::Or(a, b) => {
            let x = type_pred_exec(schema, env, a);
            let y = type_pred_exec(schema, env, b);
            x && y
        },
        EPred::Not(a) => type_pred_exec(schema, env, a),
        EPred::IsNull(e) => type_expr_exec(schema, env, e).is_some(),
        EPred::OfBool(e) => match type_expr_exec(schema, env, e) {
            Some(t) => matches!(t.ty, ScalarTy::Bool),
            None => false,
        },
        EPred::Exists(q) => type_query_exec(schema, env, q).is_some(),
        EPred::AnyCmp { op, e, q } => {
            let te = type_expr_exec(schema, env, e);
            let tq = type_query_exec(schema, env, q);
            any_cmp_ok_exec(*op, te, tq)
        },
    }
}

/// `spec::typing::type_expr`: the type of an expression under the environment types `env`.
pub fn type_expr_exec(schema: &Vec<ETableSchema>, env: &Vec<ColTy>, e: &EExpr) -> (r: Option<ColTy>)
    ensures r == type_expr(view_schema(schema@), env@, view_expr(*e)),
    decreases e, 0nat,
{
    match e {
        EExpr::Col(i) => if *i < env.len() { Some(env[*i]) } else { None },
        EExpr::Lit(l) => type_lit_exec(l),
        EExpr::Neg { kind, arg } => match type_expr_exec(schema, env, arg) {
            Some(t) => if kind_accepts_exec(*kind, t.ty) { Some(t) } else { None },
            None => None,
        },
        EExpr::Arith { op, kind, a, b } => {
            let ta = type_expr_exec(schema, env, a);
            let tb = type_expr_exec(schema, env, b);
            match (ta, tb) {
                (Some(ta), Some(tb)) => match arith_ty_exec(*op, *kind, ta.ty, tb.ty) {
                    Some(t) => Some(ColTy { ty: t, nullable: ta.nullable || tb.nullable }),
                    None => None,
                },
                _ => None,
            }
        },
        EExpr::Cast { cast, arg } => match type_expr_exec(schema, env, arg) {
            Some(t) => match cast_ty_exec(*cast, t.ty) {
                Some(r) => Some(ColTy { ty: r, nullable: t.nullable }),
                None => None,
            },
            None => None,
        },
        EExpr::AddInterval { arg, .. } => match type_expr_exec(schema, env, arg) {
            Some(t) => if matches!(t.ty, ScalarTy::Timestamp) { Some(t) } else { None },
            None => None,
        },
        EExpr::Call { f, args } => match type_exprs_exec(schema, env, args) {
            Some(ts) => type_fn_exec(*f, &ts),
            None => None,
        },
        EExpr::If { cond, then_e, else_e } => {
            let c = type_pred_exec(schema, env, cond);
            let a = type_expr_exec(schema, env, then_e);
            let b = type_expr_exec(schema, env, else_e);
            if_ty_exec(c, a, b)
        },
        EExpr::Subquery(q) => {
            let tys = type_query_exec(schema, env, q);
            subquery_ty_exec(tys)
        },
    }
}

/// `spec::typing::type_exprs`: the types of a list of expressions (all must type).
pub fn type_exprs_exec(schema: &Vec<ETableSchema>, env: &Vec<ColTy>, es: &Vec<EExpr>) -> (r: Option<Vec<ColTy>>)
    ensures
        match r {
            Some(ts) => type_exprs(view_schema(schema@), env@, view_exprs(es@)) == Some(ts@),
            None => type_exprs(view_schema(schema@), env@, view_exprs(es@)) is None,
        },
    decreases es, 1nat,
{
    let ghost g = view_exprs(es@);
    let mut out: Vec<ColTy> = Vec::new();
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<Expr>::empty()); }
    while i < es.len()
        invariant
            i <= es.len(), g == view_exprs(es@),
            type_exprs(view_schema(schema@), env@, g.take(i as int)) == Some(out@),
        decreases es.len() - i,
    {
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == view_expr(es@[i as int]));
        }
        match type_expr_exec(schema, env, &es[i]) {
            Some(t) => { out.push(t); },
            None => {
                proof { lemma_type_exprs_prefix_none(view_schema(schema@), env@, g, i as int + 1); }
                return None;
            },
        }
        i = i + 1;
    }
    proof { assert(g.take(es.len() as int) =~= g); }
    Some(out)
}

proof fn lemma_type_exprs_prefix_none(schema: Schema, env: Seq<ColTy>, es: Seq<Expr>, k: int)
    requires 0 <= k <= es.len(), type_exprs(schema, env, es.take(k)) is None,
    ensures type_exprs(schema, env, es) is None,
    decreases es.len(),
{
    if k < es.len() {
        let d = es.drop_last();
        assert(d.take(k) =~= es.take(k));
        lemma_type_exprs_prefix_none(schema, env, d, k);
    } else {
        assert(es.take(k) =~= es);
    }
}

/// `spec::typing::type_agg`: the result type of an aggregate over rows of environment types `env`.
fn type_agg_exec(schema: &Vec<ETableSchema>, env: &Vec<ColTy>, a: &EAgg) -> (r: Option<ColTy>)
    ensures r == type_agg(view_schema(schema@), env@, view_agg(*a)),
    decreases a,
{
    match a {
        EAgg::CountStar => Some(nn_exec(ScalarTy::Int8)),
        EAgg::Count(e) => if type_expr_exec(schema, env, e).is_some() { Some(nn_exec(ScalarTy::Int8)) } else { None },
        EAgg::Sum { kind, arg } => match type_expr_exec(schema, env, arg) {
            Some(t) => if !kind_accepts_exec(*kind, t.ty) { None } else {
                Some(ColTy {
                    ty: match kind {
                        NumKind::Int4 => ScalarTy::Int8,
                        NumKind::Int8 => ScalarTy::Numeric { scale: 0 },
                        NumKind::Numeric => t.ty,
                    },
                    nullable: true,
                })
            },
            None => None,
        },
        EAgg::Min(e) | EAgg::Max(e) => match type_expr_exec(schema, env, e) {
            Some(t) => minmax_ty_exec(t),
            None => None,
        },
        EAgg::Avg { kind, arg } => match type_expr_exec(schema, env, arg) {
            Some(t) => avg_ty_exec(*kind, t),
            None => None,
        },
        EAgg::DistinctAgg(inner) => match type_agg_exec(schema, env, inner) {
            Some(t) => distinct_agg_ty_exec(inner, t),
            None => None,
        },
    }
}

/// `spec::typing::type_aggs`: the types of a list of aggregates (all must type).
fn type_aggs_exec(schema: &Vec<ETableSchema>, env: &Vec<ColTy>, aggs: &Vec<EAgg>) -> (r: Option<Vec<ColTy>>)
    ensures
        match r {
            Some(ts) => type_aggs(view_schema(schema@), env@, view_aggs(aggs@)) == Some(ts@),
            None => type_aggs(view_schema(schema@), env@, view_aggs(aggs@)) is None,
        },
    decreases aggs, 1nat,
{
    let ghost g = view_aggs(aggs@);
    let mut out: Vec<ColTy> = Vec::new();
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<Agg>::empty()); }
    while i < aggs.len()
        invariant
            i <= aggs.len(), g == view_aggs(aggs@),
            type_aggs(view_schema(schema@), env@, g.take(i as int)) == Some(out@),
        decreases aggs.len() - i,
    {
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == view_agg(aggs@[i as int]));
        }
        match type_agg_exec(schema, env, &aggs[i]) {
            Some(t) => { out.push(t); },
            None => {
                proof { lemma_type_aggs_prefix_none(view_schema(schema@), env@, g, i as int + 1); }
                return None;
            },
        }
        i = i + 1;
    }
    proof { assert(g.take(aggs.len() as int) =~= g); }
    Some(out)
}

proof fn lemma_type_aggs_prefix_none(schema: Schema, env: Seq<ColTy>, aggs: Seq<Agg>, k: int)
    requires 0 <= k <= aggs.len(), type_aggs(schema, env, aggs.take(k)) is None,
    ensures type_aggs(schema, env, aggs) is None,
    decreases aggs.len(),
{
    if k < aggs.len() {
        let d = aggs.drop_last();
        assert(d.take(k) =~= aggs.take(k));
        lemma_type_aggs_prefix_none(schema, env, d, k);
    } else {
        assert(aggs.take(k) =~= aggs);
    }
}

// ---------------------------------------------------------------- types of literals and operators

/// `spec::typing::nn`: the non-nullable column type of `ty`.
fn nn_exec(ty: ScalarTy) -> (c: ColTy)
    ensures c == nn(ty),
{
    ColTy { ty, nullable: false }
}

/// `spec::typing::type_lit`. `type_lit(l)` is defined exactly when `lit_val(l)` succeeds (both check the same
/// literal validity), so the literal's validity is decided by evaluating it.
fn type_lit_exec(l: &ELiteral) -> (r: Option<ColTy>)
    ensures r == type_lit(view_lit(*l)),
{
    let ok = lit_exec(l).is_ok();
    if !ok {
        return None;
    }
    match l {
        ELiteral::Null { ty } => Some(ColTy { ty: *ty, nullable: true }),
        ELiteral::Bool(_) => Some(nn_exec(ScalarTy::Bool)),
        ELiteral::Int { v, kind } => Some(nn_exec(match kind { IntKind::Int4 => ScalarTy::Int4, IntKind::Int8 => ScalarTy::Int8 })),
        ELiteral::Num { coeff, scale } => Some(nn_exec(ScalarTy::Numeric { scale: *scale })),
        ELiteral::Date { .. } => Some(nn_exec(ScalarTy::Date)),
        ELiteral::Text(_) => Some(nn_exec(ScalarTy::Text)),
    }
}

/// `spec::typing::kind_accepts`.
fn kind_accepts_exec(kind: NumKind, t: ScalarTy) -> (b: bool)
    ensures b == kind_accepts(kind, t),
{
    match (kind, t) {
        (NumKind::Int4, ScalarTy::Int4) => true,
        (NumKind::Int8, ScalarTy::Int8) => true,
        (NumKind::Numeric, ScalarTy::Numeric { .. }) => true,
        _ => false,
    }
}

/// `spec::typing::scale_of`.
fn scale_of_exec(t: ScalarTy) -> (s: u32)
    ensures s as nat == scale_of(t),
{
    match t {
        ScalarTy::Numeric { scale } => scale,
        _ => 0,
    }
}

/// `spec::typing::arith_ty` (scales are added in `u64`, so the sum of two `u32` scales cannot overflow).
fn arith_ty_exec(op: ArithOp, kind: NumKind, ta: ScalarTy, tb: ScalarTy) -> (r: Option<ScalarTy>)
    ensures r == arith_ty(op, kind, ta, tb),
{
    if !kind_accepts_exec(kind, ta) || !kind_accepts_exec(kind, tb) {
        return None;
    }
    match kind {
        NumKind::Numeric => {
            let (s1, s2) = (scale_of_exec(ta) as u64, scale_of_exec(tb) as u64);
            let s: u64 = match op {
                ArithOp::Mul => s1 + s2,
                _ => if s1 >= s2 { s1 } else { s2 },
            };
            if s <= NUMERIC_DSCALE_MAX as u64 { Some(ScalarTy::Numeric { scale: s as u32 }) } else { None }
        },
        _ => Some(ta),
    }
}

/// `spec::typing::cast_ty`.
fn cast_ty_exec(op: CastOp, t: ScalarTy) -> (r: Option<ScalarTy>)
    ensures r == cast_ty(op, t),
{
    match (op, t) {
        (CastOp::Int4ToInt8, ScalarTy::Int4) => Some(ScalarTy::Int8),
        (CastOp::IntToNumeric, ScalarTy::Int4) => Some(ScalarTy::Numeric { scale: 0 }),
        (CastOp::IntToNumeric, ScalarTy::Int8) => Some(ScalarTy::Numeric { scale: 0 }),
        (CastOp::DateToTimestamp, ScalarTy::Date) => Some(ScalarTy::Timestamp),
        _ => None,
    }
}

/// `spec::typing::family`: the comparison family.
fn family_exec(t: ScalarTy) -> (f: u8)
    ensures f as int == family(t),
{
    match t {
        ScalarTy::Bool => 0,
        ScalarTy::Int4 | ScalarTy::Int8 | ScalarTy::Numeric { .. } => 1,
        ScalarTy::Date | ScalarTy::Timestamp => 2,
        ScalarTy::Text => 3,
    }
}

/// `spec::typing::if_ty`.
fn if_ty_exec(cond_ok: bool, then_t: Option<ColTy>, else_t: Option<ColTy>) -> (r: Option<ColTy>)
    ensures r == if_ty(cond_ok, then_t, else_t),
{
    match (then_t, else_t) {
        (Some(a), Some(b)) => {
            if !cond_ok {
                return None;
            }
            let ty = match (a.ty, b.ty) {
                (ScalarTy::Numeric { scale: x }, ScalarTy::Numeric { scale: y }) =>
                    ScalarTy::Numeric { scale: if x >= y { x } else { y } },
                (ScalarTy::Numeric { .. }, _) | (_, ScalarTy::Numeric { .. }) => return None,
                _ => if scalar_ty_eq(a.ty, b.ty) { a.ty } else { return None },
            };
            Some(ColTy { ty, nullable: a.nullable || b.nullable })
        },
        _ => None,
    }
}

/// Equality of two `ScalarTy` values (`ScalarTy` has no executable `==`).
fn scalar_ty_eq(a: ScalarTy, b: ScalarTy) -> (r: bool)
    ensures r == (a == b),
{
    match (a, b) {
        (ScalarTy::Bool, ScalarTy::Bool) | (ScalarTy::Int4, ScalarTy::Int4) | (ScalarTy::Int8, ScalarTy::Int8)
        | (ScalarTy::Date, ScalarTy::Date) | (ScalarTy::Timestamp, ScalarTy::Timestamp)
        | (ScalarTy::Text, ScalarTy::Text) => true,
        (ScalarTy::Numeric { scale: x }, ScalarTy::Numeric { scale: y }) => x == y,
        _ => false,
    }
}

/// `spec::typing::subquery_ty` (given the exec output types).
fn subquery_ty_exec(q: Option<Vec<ColTy>>) -> (r: Option<ColTy>)
    ensures forall|tys: Option<Seq<ColTy>>| (match q { Some(v) => tys == Some(v@), None => tys is None })
        ==> r == #[trigger] subquery_ty(tys),
{
    match q {
        Some(v) => if v.len() == 1 { Some(ColTy { ty: v[0].ty, nullable: true }) } else { None },
        None => None,
    }
}

/// `spec::typing::any_cmp_ok` (given the exec output types).
fn any_cmp_ok_exec(op: CmpOp, e: Option<ColTy>, q: Option<Vec<ColTy>>) -> (r: bool)
    ensures forall|tys: Option<Seq<ColTy>>| (match q { Some(v) => tys == Some(v@), None => tys is None })
        ==> r == #[trigger] any_cmp_ok(op, e, tys),
{
    match (e, q) {
        (Some(t), Some(v)) => v.len() == 1 && family_exec(t.ty) == family_exec(v[0].ty),
        _ => false,
    }
}

// ---------------------------------------------------------------- column type lists

/// `spec::typing::table_tys`: the column types of a base table.
pub fn table_tys_exec(t: &ETableSchema) -> (r: Vec<ColTy>)
    ensures r@ == table_tys(view_table_schema(*t)),
{
    let mut r: Vec<ColTy> = Vec::new();
    let mut i: usize = 0;
    while i < t.columns.len()
        invariant i <= t.columns.len(), r@ == t.columns@.take(i as int).map_values(|c: Column| col_ty_of(c)),
        decreases t.columns.len() - i,
    {
        r.push(col_ty_of_exec(t.columns[i]));
        proof {
            assert(r@ =~= t.columns@.take(i as int + 1).map_values(|c: Column| col_ty_of(c)));
        }
        i = i + 1;
    }
    proof { assert(t.columns@.take(t.columns.len() as int) =~= t.columns@); }
    r
}

/// `spec::types::col_ty_of`: the static type of a declared column (`text`, `varchar(n)` and `char(n)` are one
/// comparison family).
fn col_ty_of_exec(c: Column) -> (r: ColTy)
    ensures r == col_ty_of(c),
{
    let ty = match c.ty {
        SqlType::Bool => ScalarTy::Bool,
        SqlType::Int4 => ScalarTy::Int4,
        SqlType::Int8 => ScalarTy::Int8,
        SqlType::Numeric { precision, scale } => ScalarTy::Numeric { scale },
        SqlType::Date => ScalarTy::Date,
        SqlType::Timestamp => ScalarTy::Timestamp,
        SqlType::Text | SqlType::Varchar { .. } | SqlType::Bpchar { .. } => ScalarTy::Text,
    };
    ColTy { ty, nullable: c.nullable }
}

/// `a ++ b`.
fn concat_tys(a: &Vec<ColTy>, b: &Vec<ColTy>) -> (r: Vec<ColTy>)
    ensures r@ == a@ + b@,
{
    let mut r = a.clone();
    let mut i: usize = 0;
    while i < b.len()
        invariant i <= b.len(), r@ == a@ + b@.take(i as int),
        decreases b.len() - i,
    {
        r.push(b[i]);
        proof { assert(r@ =~= a@ + b@.take(i as int + 1)); }
        i = i + 1;
    }
    proof { assert(b@.take(b.len() as int) =~= b@); }
    r
}

/// `spec::typing::nullable_all`: the same types, all nullable (the right side of a LEFT JOIN).
fn nullable_all_exec(tys: &Vec<ColTy>) -> (r: Vec<ColTy>)
    ensures r@ == nullable_all(tys@),
{
    let mut r: Vec<ColTy> = Vec::new();
    let mut i: usize = 0;
    while i < tys.len()
        invariant i <= tys.len(), r@ == nullable_all(tys@.take(i as int)),
        decreases tys.len() - i,
    {
        r.push(ColTy { ty: tys[i].ty, nullable: true });
        proof { assert(r@ =~= nullable_all(tys@.take(i as int + 1))); }
        i = i + 1;
    }
    proof { assert(tys@.take(tys.len() as int) =~= tys@); }
    r
}

} // verus!
