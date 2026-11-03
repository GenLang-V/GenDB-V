//! Arrow result batches of the DataFusion reference as plain typed values (tests only; the reference is not a meaning).

use arrow::array::{Array, BooleanArray, Date32Array, Decimal128Array, Int32Array, Int64Array, StringArray, StringViewArray};
use arrow::datatypes::DataType;
use arrow::record_batch::RecordBatch;

/// One reference result value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferenceValue {
    Null,
    Bool(bool),
    I32(i32),
    I64(i64),
    /// Days since 1970-01-01.
    Date32(i32),
    /// Decimal128 coefficient `v` of `v * 10^-s`.
    Dec { v: i128, p: u8, s: i8 },
    Text(String),
}

/// Every row of `batches`, in order.
pub fn batch_rows(batches: &[RecordBatch]) -> Result<Vec<Vec<ReferenceValue>>, String> {
    let mut rows = Vec::new();
    for batch in batches {
        for row in 0..batch.num_rows() {
            rows.push(batch.columns().iter().map(|a| cell(a.as_ref(), row)).collect::<Result<_, _>>()?);
        }
    }
    Ok(rows)
}

fn cell(a: &dyn Array, row: usize) -> Result<ReferenceValue, String> {
    if a.is_null(row) {
        return Ok(ReferenceValue::Null);
    }
    fn typed<T: 'static>(a: &dyn Array) -> Result<&T, String> {
        a.as_any().downcast_ref::<T>().ok_or_else(|| format!("reference array of type {} does not match its data type", a.data_type()))
    }
    Ok(match a.data_type() {
        DataType::Int32 => ReferenceValue::I32(typed::<Int32Array>(a)?.value(row)),
        DataType::Int64 => ReferenceValue::I64(typed::<Int64Array>(a)?.value(row)),
        DataType::Boolean => ReferenceValue::Bool(typed::<BooleanArray>(a)?.value(row)),
        DataType::Date32 => ReferenceValue::Date32(typed::<Date32Array>(a)?.value(row)),
        DataType::Decimal128(p, s) => ReferenceValue::Dec { v: typed::<Decimal128Array>(a)?.value(row), p: *p, s: *s },
        DataType::Utf8 => ReferenceValue::Text(typed::<StringArray>(a)?.value(row).into()),
        DataType::Utf8View => ReferenceValue::Text(typed::<StringViewArray>(a)?.value(row).into()),
        other => return Err(format!("reference output type unsupported: {other}")),
    })
}
