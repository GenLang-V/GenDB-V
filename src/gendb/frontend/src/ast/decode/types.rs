//! Types in the document: PostgreSQL-level types (annotations, schema columns, parameter declarations), the resolver's
//! column types, and the Verus `ScalarTy` of typed NULL literals.

use super::super::document::{ColType, PgType, ScalarTy};
use super::super::literals::{NUMERIC_DSCALE_MAX, NUMERIC_MAX_PRECISION, VARLENA_MAX_CHARS};
use super::super::schema::schema;
use super::super::{err, AstError};
use super::expect_keys;
use serde_json::Value;

pub(super) fn decode_pg_type(v: &Value) -> Result<PgType, AstError> {
    let o = v.as_object().ok_or_else(|| AstError("type must be an object".into()))?;
    let kind = o.get("kind").and_then(Value::as_str).ok_or_else(|| AstError("type.kind".into()))?;
    // A length modifier: null (unbounded) or 1..=VARLENA_MAX_CHARS.
    let opt_len = |k: &str| -> Result<Option<u64>, AstError> {
        match &o[k] {
            Value::Null => Ok(None),
            x => x.as_u64().filter(|&n| (1..=VARLENA_MAX_CHARS).contains(&n)).map(Some).ok_or_else(|| AstError(format!("type.{k}"))),
        }
    };
    let unmodified = match kind {
        "bool" => PgType::Bool,
        "int4" => PgType::Int4,
        "int8" => PgType::Int8,
        "date" => PgType::Date,
        "timestamp" => PgType::Timestamp,
        "text" => PgType::Text,
        "numeric" => {
            expect_keys(o, &["kind", "typmod"], "numeric type")?;
            let typmod = match &o["typmod"] {
                Value::Null => None,
                Value::Object(tm) => {
                    expect_keys(tm, &["precision", "scale"], "typmod")?;
                    match (tm["precision"].as_u64(), tm["scale"].as_u64()) {
                        (Some(p), Some(s)) if (1..=NUMERIC_MAX_PRECISION).contains(&p) && s <= p => Some((p, s)),
                        _ => return err("numeric typmod outside 1 <= p <= 1000, 0 <= s <= p"),
                    }
                }
                _ => return err("typmod"),
            };
            return Ok(PgType::Numeric { typmod });
        }
        "varchar" => {
            expect_keys(o, &["kind", "max_chars"], "varchar type")?;
            return Ok(PgType::Varchar { max_chars: opt_len("max_chars")? });
        }
        "bpchar" => {
            expect_keys(o, &["kind", "n"], "bpchar type")?;
            return Ok(PgType::Bpchar { n: opt_len("n")? });
        }
        _ => return err(format!("unknown type kind {kind}")),
    };
    expect_keys(o, &["kind"], "type")?;
    Ok(unmodified)
}

pub(super) fn decode_coltype(v: &Value) -> Result<ColType, AstError> {
    let o = v.as_object().ok_or_else(|| AstError("column type must be an object".into()))?;
    let dscale_exact = match o.get("dscale_exact") {
        None => true,
        Some(Value::Bool(false)) => false,
        Some(_) => return err("dscale_exact is only written as false"),
    };
    if dscale_exact {
        expect_keys(o, &["type", "nullable", "dscale"], "column type")?;
    } else {
        expect_keys(o, &["type", "nullable", "dscale", "dscale_exact"], "column type")?;
    }
    let ty = decode_pg_type(&o["type"])?;
    let nullable = o["nullable"].as_bool().ok_or_else(|| AstError("nullable".into()))?;
    let dscale = match &o["dscale"] {
        Value::Null => None,
        x => Some(x.as_u64().ok_or_else(|| AstError("dscale".into()))?),
    };
    if dscale.is_some() != matches!(ty, PgType::Numeric { .. }) {
        return err("dscale is required for numeric and absent otherwise");
    }
    if !dscale_exact && dscale.is_none() {
        return err("dscale_exact is only written on a numeric");
    }
    Ok(ColType { ty, nullable, dscale, dscale_exact })
}

/// A `ScalarTy` object: `kind` plus exactly the parameters the schema lists for it (`scale` of `Numeric`).
pub(super) fn decode_scalar_ty(v: &Value) -> Option<ScalarTy> {
    let o = v.as_object()?;
    let kind = o.get("kind")?.as_str()?;
    let params = schema().scalar_types.get(kind)?;
    let mut keys: Vec<&str> = vec!["kind"];
    keys.extend(params.iter().map(String::as_str));
    expect_keys(o, &keys, "scalar type").ok()?;
    let scale = match o.get("scale") {
        Some(s) => Some(s.as_u64().filter(|&s| s <= NUMERIC_DSCALE_MAX)?),
        None => None,
    };
    Some(ScalarTy { kind: kind.to_owned(), scale })
}
