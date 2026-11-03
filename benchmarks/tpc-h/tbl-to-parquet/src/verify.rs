//! The value check: stream the written parquet back and the raw text forward
//! in lockstep and compare every value exactly.
//!
//! Each value is checked twice, in opposite directions:
//!   * decode: the stored machine value must equal the exact parse of the token;
//!   * encode: the canonical text of the stored value must equal the canonical
//!     text of the token, produced lexically without arithmetic.
//!
//! A scale, sign or field-order error fails both; a parser bug that agreed with
//! itself would still have to survive the encode direction.

use std::fs::File;
use std::path::Path;
use std::sync::mpsc::sync_channel;
use std::time::Instant;

use arrow::array::{Array, Date32Array, Decimal128Array, Int64Array, RecordBatch, StringArray};
use parquet::arrow::arrow_reader::ParquetRecordBatchReaderBuilder;

use crate::materialize::{RowReader, assert_parquet_schema};
use crate::parse;
use crate::schema::{ColumnKind, TableSpec};
use crate::{Error, Result};

/// Rows per parquet read batch during the check. Small enough that the check
/// pass costs a few hundred MiB regardless of table size.
pub const VERIFY_BATCH_ROWS: usize = 65_536;

/// How many differing values are described in full before the report keeps
/// counting only.
const MAX_SAMPLES: usize = 20;

/// Per-column outcome of the value check.
#[derive(Debug, Clone)]
pub struct ColumnCheck {
    /// Column name.
    pub name: String,
    /// Arrow type, rendered.
    pub arrow_type: String,
    /// Values compared. Must equal the table row count.
    pub checked: u64,
    /// Values that differed. Must be zero.
    pub mismatches: u64,
}

/// Outcome of checking one table.
#[derive(Debug, Clone)]
pub struct VerifyReport {
    /// Rows seen on both sides.
    pub rows: u64,
    /// Per-column counts.
    pub columns: Vec<ColumnCheck>,
    /// Sum of per-column mismatches.
    pub mismatches: u64,
    /// Up to twenty rendered differences, for diagnosis.
    pub samples: Vec<String>,
    /// Wall time in milliseconds.
    pub wall_ms: u64,
}

enum ColumnView<'a> {
    Int(&'a Int64Array),
    Dec(&'a Decimal128Array),
    Date(&'a Date32Array),
    Str(&'a StringArray),
}

fn view<'a>(
    batch: &'a RecordBatch,
    index: usize,
    kind: ColumnKind,
    name: &str,
) -> Result<ColumnView<'a>> {
    let array = batch.column(index);
    let bad = || {
        Error::new(format!(
            "column {name}: parquet array is {:?}, schema declares {:?}",
            array.data_type(),
            kind.data_type()
        ))
    };
    Ok(match kind {
        ColumnKind::Int64 => ColumnView::Int(array.as_any().downcast_ref().ok_or_else(bad)?),
        ColumnKind::Decimal => ColumnView::Dec(array.as_any().downcast_ref().ok_or_else(bad)?),
        ColumnKind::Date => ColumnView::Date(array.as_any().downcast_ref().ok_or_else(bad)?),
        ColumnKind::Utf8 => ColumnView::Str(array.as_any().downcast_ref().ok_or_else(bad)?),
    })
}

/// Check every value of one materialized table against its raw text source.
///
/// Returns a report; a nonzero `mismatches` is a failure for the caller to act
/// on, never a tolerance to absorb.
pub fn verify_table(
    spec: &'static TableSpec,
    source: &Path,
    parquet: &Path,
) -> Result<VerifyReport> {
    let started = Instant::now();
    assert_parquet_schema(spec, parquet)?;

    let mut columns: Vec<ColumnCheck> = spec
        .columns
        .iter()
        .map(|c| ColumnCheck {
            name: c.name.to_string(),
            arrow_type: format!("{:?}", c.kind.data_type()),
            checked: 0,
            mismatches: 0,
        })
        .collect();
    let mut samples: Vec<String> = Vec::new();
    let mut rows: u64 = 0;

    let (tx, rx) = sync_channel::<Result<RecordBatch>>(1);
    let outcome = std::thread::scope(|scope| {
        // The parquet reader is created inside the thread, so only record
        // batches ever cross the hand-off.
        scope.spawn(move || {
            let opened = File::open(parquet)
                .map_err(|e| Error::new(format!("cannot open {}: {e}", parquet.display())))
                .and_then(|f| {
                    ParquetRecordBatchReaderBuilder::try_new(f)
                        .map_err(Error::from)
                        .and_then(|b| {
                            b.with_batch_size(VERIFY_BATCH_ROWS)
                                .build()
                                .map_err(Error::from)
                        })
                });
            match opened {
                Err(e) => {
                    let _ = tx.send(Err(e));
                }
                Ok(reader) => {
                    for batch in reader {
                        if tx.send(batch.map_err(Error::from)).is_err() {
                            return;
                        }
                    }
                }
            }
        });

        let mut text = RowReader::open(source, spec.field_count())?;
        let mut scratch = Scratch::default();
        for message in rx {
            let batch = message?;
            let views: Vec<ColumnView<'_>> = spec
                .columns
                .iter()
                .enumerate()
                .map(|(i, c)| view(&batch, i, c.kind, c.name))
                .collect::<Result<_>>()?;
            for (i, c) in spec.columns.iter().enumerate() {
                if batch.column(i).null_count() != 0 {
                    return Err(Error::new(format!(
                        "{}: column {} holds {} nulls; every TPC-H column is NOT NULL",
                        parquet.display(),
                        c.name,
                        batch.column(i).null_count()
                    )));
                }
            }

            for row in 0..batch.num_rows() {
                if !text.next_row()? {
                    return Err(Error::new(format!(
                        "{} ran out at line {} but {} still has rows",
                        source.display(),
                        text.line_no(),
                        parquet.display()
                    )));
                }
                rows += 1;
                for (index, spec_col) in spec.columns.iter().enumerate() {
                    let token = text.field(index);
                    let difference = match &views[index] {
                        ColumnView::Int(a) => check_int(a.value(row), token, &mut scratch),
                        ColumnView::Dec(a) => check_decimal(a.value(row), token, &mut scratch),
                        ColumnView::Date(a) => check_date(a.value(row), token, &mut scratch),
                        ColumnView::Str(a) => check_utf8(a.value(row), token),
                    }
                    .map_err(|e| text.field_error(spec_col.name, index, e))?;

                    columns[index].checked += 1;
                    if let Some(detail) = difference {
                        columns[index].mismatches += 1;
                        if samples.len() < MAX_SAMPLES {
                            samples.push(format!(
                                "{}:{}: column {}: {detail}",
                                source.display(),
                                text.line_no(),
                                spec_col.name
                            ));
                        }
                    }
                }
            }
        }

        if text.next_row()? {
            return Err(Error::new(format!(
                "{} has more rows than {} ({} rows checked, source line {} still present)",
                source.display(),
                parquet.display(),
                rows,
                text.line_no()
            )));
        }
        Ok(())
    });
    outcome?;

    let mismatches = columns.iter().map(|c| c.mismatches).sum();
    Ok(VerifyReport {
        rows,
        columns,
        mismatches,
        samples,
        wall_ms: crate::materialize::elapsed_ms(started),
    })
}

/// Reusable text buffers so the encode-direction check costs no allocation
/// per value. Only a genuine difference allocates, to render the message.
#[derive(Default)]
struct Scratch {
    rendered: String,
    canonical: String,
}

/// `Ok(None)` when the stored value matches the token in both directions.
fn check_int(
    stored: i64,
    token: &[u8],
    scratch: &mut Scratch,
) -> std::result::Result<Option<String>, parse::TokenError> {
    let expected = parse::parse_int(token)?;
    if stored != expected {
        return Ok(Some(format!(
            "stored {stored}, source text {:?} parses to {expected}",
            String::from_utf8_lossy(token)
        )));
    }
    parse::format_int_into(stored, &mut scratch.rendered);
    if scratch.rendered.as_bytes() != token {
        return Ok(Some(format!(
            "stored {stored} renders as {:?}, source text is {:?}",
            scratch.rendered,
            String::from_utf8_lossy(token)
        )));
    }
    Ok(None)
}

fn check_decimal(
    stored: i128,
    token: &[u8],
    scratch: &mut Scratch,
) -> std::result::Result<Option<String>, parse::TokenError> {
    let expected = parse::parse_decimal(token)?;
    if stored != expected {
        return Ok(Some(format!(
            "stored scaled {stored}, source text {:?} parses to scaled {expected}",
            String::from_utf8_lossy(token)
        )));
    }
    parse::format_decimal_into(stored, &mut scratch.rendered);
    parse::normalize_decimal_into(token, &mut scratch.canonical)?;
    if scratch.rendered != scratch.canonical {
        return Ok(Some(format!(
            "stored scaled {stored} renders as {:?}, source text normalizes to {:?}",
            scratch.rendered, scratch.canonical
        )));
    }
    Ok(None)
}

fn check_date(
    stored: i32,
    token: &[u8],
    scratch: &mut Scratch,
) -> std::result::Result<Option<String>, parse::TokenError> {
    let expected = parse::parse_date(token)?;
    if stored != expected {
        return Ok(Some(format!(
            "stored day {stored}, source text {:?} parses to day {expected}",
            String::from_utf8_lossy(token)
        )));
    }
    parse::format_date_into(stored, &mut scratch.rendered);
    if scratch.rendered.as_bytes() != token {
        return Ok(Some(format!(
            "stored day {stored} renders as {:?}, source text is {:?}",
            scratch.rendered,
            String::from_utf8_lossy(token)
        )));
    }
    Ok(None)
}

fn check_utf8(
    stored: &str,
    token: &[u8],
) -> std::result::Result<Option<String>, parse::TokenError> {
    if stored.as_bytes() != token {
        return Ok(Some(format!(
            "stored {stored:?}, source text {:?}",
            String::from_utf8_lossy(token)
        )));
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::materialize::{WriteOptions, write_table};
    use crate::schema::{table, test_scratch_dir};

    const LINEITEM_FIXTURE: &str = concat!(
        "1|155190|7706|1|17|21168.23|0.04|0.02|N|O|1996-03-13|1996-02-12|1996-03-22|DELIVER IN PERSON|TRUCK|egular courts above the|\n",
        "1|67310|7311|2|36|45983.16|0.09|0.06|N|O|1996-04-12|1996-02-28|1996-04-20|TAKE BACK RETURN|MAIL|ly final dependencies|\n",
        "3|19036|6540|1|49|46796.47|0.10|0.00|R|F|1993-11-14|1993-12-15|1993-11-24|TAKE BACK RETURN|RAIL|carefully|\n",
    );

    fn fixture(name: &str, body: &str) -> std::path::PathBuf {
        let dir = test_scratch_dir(name);
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("lineitem.tbl");
        std::fs::write(&path, body).unwrap();
        path
    }

    #[test]
    fn end_to_end_tbl_to_parquet_to_check_roundtrip() {
        let spec = table("lineitem").unwrap();
        let source = fixture("e2e-roundtrip", LINEITEM_FIXTURE);
        let parquet = source.with_extension("parquet");

        let written = write_table(spec, &source, &parquet, WriteOptions { batch_rows: 2 }).unwrap();
        assert_eq!(written.rows, 3);
        assert!(written.bytes > 0);

        let report = verify_table(spec, &source, &parquet).unwrap();
        assert_eq!(report.rows, 3);
        assert_eq!(report.mismatches, 0, "{:?}", report.samples);
        assert_eq!(report.columns.len(), 16);
        for column in &report.columns {
            assert_eq!(column.checked, 3, "column {} checked count", column.name);
            assert_eq!(column.mismatches, 0, "column {}", column.name);
        }
    }

    #[test]
    fn stored_values_are_the_exact_scaled_integers() {
        let spec = table("lineitem").unwrap();
        let source = fixture("e2e-values", LINEITEM_FIXTURE);
        let parquet = source.with_extension("parquet");
        write_table(spec, &source, &parquet, WriteOptions { batch_rows: 8 }).unwrap();

        let file = File::open(&parquet).unwrap();
        let mut reader = ParquetRecordBatchReaderBuilder::try_new(file)
            .unwrap()
            .build()
            .unwrap();
        let batch = reader.next().unwrap().unwrap();
        let extended = batch
            .column_by_name("l_extendedprice")
            .unwrap()
            .as_any()
            .downcast_ref::<Decimal128Array>()
            .unwrap();
        assert_eq!(extended.value(0), 2_116_823);
        assert_eq!(extended.value(1), 4_598_316);
        assert_eq!(extended.value(2), 4_679_647);

        let quantity = batch
            .column_by_name("l_quantity")
            .unwrap()
            .as_any()
            .downcast_ref::<Decimal128Array>()
            .unwrap();
        assert_eq!(quantity.value(0), 1700);

        let discount = batch
            .column_by_name("l_discount")
            .unwrap()
            .as_any()
            .downcast_ref::<Decimal128Array>()
            .unwrap();
        assert_eq!(discount.value(0), 4);
        assert_eq!(discount.value(2), 10);

        let shipdate = batch
            .column_by_name("l_shipdate")
            .unwrap()
            .as_any()
            .downcast_ref::<Date32Array>()
            .unwrap();
        assert_eq!(shipdate.value(0), 9568);
    }

    #[test]
    fn a_changed_source_value_is_reported_as_a_mismatch() {
        let spec = table("lineitem").unwrap();
        let source = fixture("e2e-drift", LINEITEM_FIXTURE);
        let parquet = source.with_extension("parquet");
        write_table(spec, &source, &parquet, WriteOptions { batch_rows: 8 }).unwrap();

        // Rewrite one cent of one row; the check must find exactly that value.
        let drifted = LINEITEM_FIXTURE.replacen("21168.23", "21168.24", 1);
        std::fs::write(&source, &drifted).unwrap();

        let report = verify_table(spec, &source, &parquet).unwrap();
        assert_eq!(report.mismatches, 1, "{:?}", report.samples);
        let extended = report
            .columns
            .iter()
            .find(|c| c.name == "l_extendedprice")
            .unwrap();
        assert_eq!(extended.mismatches, 1);
        assert_eq!(extended.checked, 3);
        assert!(
            report.samples[0].contains("l_extendedprice"),
            "{:?}",
            report.samples
        );
    }

    #[test]
    fn a_truncated_source_is_a_hard_error() {
        let spec = table("lineitem").unwrap();
        let source = fixture("e2e-short-source", LINEITEM_FIXTURE);
        let parquet = source.with_extension("parquet");
        write_table(spec, &source, &parquet, WriteOptions { batch_rows: 8 }).unwrap();

        let mut lines: Vec<&str> = LINEITEM_FIXTURE.lines().collect();
        lines.pop();
        std::fs::write(&source, format!("{}\n", lines.join("\n"))).unwrap();

        let err = verify_table(spec, &source, &parquet).unwrap_err();
        assert!(err.message().contains("ran out"), "{err}");
    }

    #[test]
    fn an_extended_source_is_a_hard_error() {
        let spec = table("lineitem").unwrap();
        let source = fixture("e2e-long-source", LINEITEM_FIXTURE);
        let parquet = source.with_extension("parquet");
        write_table(spec, &source, &parquet, WriteOptions { batch_rows: 8 }).unwrap();

        let mut extended = LINEITEM_FIXTURE.to_string();
        extended.push_str("4|88035|5560|1|30|30690.90|0.03|0.08|N|O|1996-01-10|1995-12-14|1996-01-18|DELIVER IN PERSON|REG AIR|- quickly regular|\n");
        std::fs::write(&source, &extended).unwrap();

        let err = verify_table(spec, &source, &parquet).unwrap_err();
        assert!(err.message().contains("more rows than"), "{err}");
    }

    #[test]
    fn check_helpers_catch_each_direction() {
        let s = &mut Scratch::default();
        assert!(check_decimal(2_116_823, b"21168.23", s).unwrap().is_none());
        assert!(check_decimal(2_116_824, b"21168.23", s).unwrap().is_some());
        // A scale slip: the value 17 stored where 17.00 (1700) was meant.
        assert!(check_decimal(17, b"17", s).unwrap().is_some());
        // A sign slip.
        assert!(check_decimal(-71_156, b"711.56", s).unwrap().is_some());
        assert!(check_int(5, b"5", s).unwrap().is_none());
        assert!(check_int(5, b"6", s).unwrap().is_some());
        assert!(check_date(9568, b"1996-03-13", s).unwrap().is_none());
        assert!(check_date(9569, b"1996-03-13", s).unwrap().is_some());
        assert!(check_utf8("MAIL", b"MAIL").unwrap().is_none());
        assert!(check_utf8("MAIL", b"RAIL").unwrap().is_some());
    }

    #[test]
    fn buffers_are_reused_without_leaking_state_between_values() {
        let s = &mut Scratch::default();
        // A long value followed by a short one: a stale tail in the reusable
        // buffer would make the short one look wrong.
        assert!(
            check_decimal(999_999_999_999_999, b"9999999999999.99", s)
                .unwrap()
                .is_none()
        );
        assert!(check_decimal(4, b"0.04", s).unwrap().is_none());
        assert!(
            check_int(-9_223_372_036_854_775_808, b"-9223372036854775808", s)
                .unwrap()
                .is_none()
        );
        assert!(check_int(0, b"0", s).unwrap().is_none());
    }
}
