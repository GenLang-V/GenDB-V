//! Statement arguments as the host passes them to a query entry.

use super::records::{ARGUMENT_DATE, ARGUMENT_INT, ARGUMENT_NUM, ARGUMENT_TEXT, ArgumentDescriptor};
use serde::{Deserialize, Serialize};

/// One statement argument, for one free parameter (slot order = ascending placeholder index of the free parameters).
/// `Int`: `integer`/`bigint` value; `Num`: `numeric(p, s)` coefficient at the declared scale; `Date`: civil date;
/// `Text`: a `text` value (v4 query crates only; the v3 shim refuses its kind), passed as its UTF-8 bytes.
///
/// The host converts request texts exactly before this point (no rounding). Domain membership is decided by the
/// verified entry (`ParamRefused`), never here. JSON form (saved requests and results): `{"int":24}`,
/// `{"num":"6"}` (i128 as decimal text, exact), `{"date":{"y":1994,"m":1,"d":1}}`, `{"text":"Brand#45"}`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub enum StatementArgument {
    Int(i64),
    Num(#[serde(with = "i128_text")] i128),
    Date { y: i32, m: i32, d: i32 },
    Text(String),
}

impl StatementArgument {
    /// The C record the shim decodes; unused fields are zero. A text record points at this argument's bytes: it is
    /// valid only while `self` is, and the shim requires them unchanged until the process exits (the worker child
    /// retains its arguments for its lifetime, `worker::inputs::retained_bindings`).
    pub fn descriptor(&self) -> ArgumentDescriptor {
        let mut record = ArgumentDescriptor { kind: 0, reserved: 0, int: 0, num_lo: 0, num_hi: 0, y: 0, m: 0, d: 0, reserved2: 0 };
        match self {
            Self::Int(value) => (record.kind, record.int) = (ARGUMENT_INT, *value),
            Self::Num(coefficient) => {
                let bits = *coefficient as u128;
                (record.kind, record.num_lo, record.num_hi) = (ARGUMENT_NUM, bits as u64, (bits >> 64) as u64);
            }
            Self::Date { y, m, d } => (record.kind, record.y, record.m, record.d) = (ARGUMENT_DATE, *y, *m, *d),
            Self::Text(text) => {
                (record.kind, record.num_lo, record.num_hi) = (ARGUMENT_TEXT, text.as_ptr() as usize as u64, text.len() as u64);
            }
        }
        record
    }
}

/// i128 as decimal JSON text: JSON numbers cannot carry every i128 exactly.
mod i128_text {
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S: Serializer>(value: &i128, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&value.to_string())
    }

    pub fn deserialize<'d, D: Deserializer<'d>>(deserializer: D) -> Result<i128, D::Error> {
        String::deserialize(deserializer)?.parse().map_err(serde::de::Error::custom)
    }
}
