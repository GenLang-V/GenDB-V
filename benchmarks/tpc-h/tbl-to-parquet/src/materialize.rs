//! Streaming `.tbl` -> Decimal128 parquet materialization.
//!
//! The raw text is read in bounded chunks, converted to Arrow arrays by the
//! exact integer parsers in [`crate::parse`], and handed to the parquet writer
//! one record batch at a time. Nothing ever holds a whole table in memory, and
//! no value passes through a floating point representation.

use std::fs::File;
use std::io::{BufReader, BufWriter, Read};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{Receiver, sync_channel};
use std::time::Instant;

use arrow::array::{
    ArrayRef, Date32Builder, Decimal128Builder, Int64Builder, RecordBatch, StringBuilder,
};
use arrow::datatypes::DataType;
use parquet::arrow::ArrowWriter;
use parquet::basic::Compression;
use parquet::file::properties::WriterProperties;

use crate::parse::{self, TokenError};
use crate::schema::{ColumnKind, TableSpec};
use crate::{Error, Result};

/// Rows per record batch and per parquet row group.
pub const DEFAULT_BATCH_ROWS: usize = 1_000_000;

/// Milliseconds since `started`, saturating rather than wrapping.
pub fn elapsed_ms(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX)
}

/// Read buffer for the raw text stream.
const READ_BUFFER_BYTES: usize = 4 << 20;
/// Write buffer in front of the parquet file.
const WRITE_BUFFER_BYTES: usize = 8 << 20;

/// A streaming reader over a `|`-terminated TPC-H raw table file.
///
/// Holds exactly one line at a time. Field boundaries are recorded as offsets
/// so no per-field allocation happens on the hot path.
pub struct RowReader {
    path: PathBuf,
    reader: BufReader<File>,
    line: Vec<u8>,
    separators: Vec<usize>,
    field_count: usize,
    line_no: u64,
}

impl RowReader {
    /// Open a raw table file, expecting `field_count` fields per row.
    pub fn open(path: &Path, field_count: usize) -> Result<Self> {
        let file = File::open(path)
            .map_err(|e| Error::new(format!("cannot open {}: {e}", path.display())))?;
        Ok(RowReader {
            path: path.to_path_buf(),
            reader: BufReader::with_capacity(READ_BUFFER_BYTES, file),
            line: Vec::with_capacity(512),
            separators: Vec::with_capacity(field_count),
            field_count,
            line_no: 0,
        })
    }

    /// Source path, used in every error message.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// 1-based number of the line currently held.
    pub fn line_no(&self) -> u64 {
        self.line_no
    }

    /// Advance to the next row. Returns `false` at clean end of file.
    pub fn next_row(&mut self) -> Result<bool> {
        use std::io::BufRead;

        self.line.clear();
        self.separators.clear();
        let read = self.reader.read_until(b'\n', &mut self.line)?;
        if read == 0 {
            return Ok(false);
        }
        self.line_no += 1;

        let mut len = self.line.len();
        if len > 0 && self.line[len - 1] == b'\n' {
            len -= 1;
        }
        if len > 0 && self.line[len - 1] == b'\r' {
            len -= 1;
        }
        self.line.truncate(len);

        if self.line.is_empty() {
            return Err(self.row_error("blank line"));
        }
        if self.line[len - 1] != b'|' {
            return Err(self.row_error("row does not end with the '|' terminator"));
        }
        for (i, &b) in self.line.iter().enumerate() {
            if b == b'|' {
                self.separators.push(i);
            }
        }
        if self.separators.len() != self.field_count {
            return Err(self.row_error(format!(
                "{} fields, schema declares {}",
                self.separators.len(),
                self.field_count
            )));
        }
        Ok(true)
    }

    /// Bytes of field `index` in the current row.
    pub fn field(&self, index: usize) -> &[u8] {
        let start = if index == 0 {
            0
        } else {
            self.separators[index - 1] + 1
        };
        &self.line[start..self.separators[index]]
    }

    /// A hard error naming the source file and line.
    pub fn row_error(&self, message: impl std::fmt::Display) -> Error {
        Error::new(format!(
            "{}:{}: {message}",
            self.path.display(),
            self.line_no
        ))
    }

    /// A hard error naming the source file, line, column and offending token.
    pub fn field_error(&self, column: &str, index: usize, cause: impl std::fmt::Display) -> Error {
        Error::new(format!(
            "{}:{}: column {column} (field {}) token {:?}: {cause}",
            self.path.display(),
            self.line_no,
            index + 1,
            String::from_utf8_lossy(self.field(index)),
        ))
    }
}

enum ColumnBuilder {
    Int(Int64Builder),
    Dec(Decimal128Builder),
    Date(Date32Builder),
    Str(StringBuilder),
}

/// Accumulates rows into one Arrow record batch.
struct BatchBuilder {
    spec: &'static TableSpec,
    columns: Vec<ColumnBuilder>,
    rows: usize,
}

impl BatchBuilder {
    fn new(spec: &'static TableSpec, capacity: usize) -> Self {
        let columns = spec
            .columns
            .iter()
            .map(|c| match c.kind {
                ColumnKind::Int64 => ColumnBuilder::Int(Int64Builder::with_capacity(capacity)),
                ColumnKind::Decimal => ColumnBuilder::Dec(
                    Decimal128Builder::with_capacity(capacity)
                        .with_data_type(ColumnKind::Decimal.data_type()),
                ),
                ColumnKind::Date => ColumnBuilder::Date(Date32Builder::with_capacity(capacity)),
                // 32 bytes per value is a starting guess for the values buffer;
                // it grows on demand and is reused across batches.
                ColumnKind::Utf8 => {
                    ColumnBuilder::Str(StringBuilder::with_capacity(capacity, capacity * 32))
                }
            })
            .collect();
        BatchBuilder {
            spec,
            columns,
            rows: 0,
        }
    }

    fn push_row(&mut self, reader: &RowReader) -> Result<()> {
        for (index, spec) in self.spec.columns.iter().enumerate() {
            let token = reader.field(index);
            match &mut self.columns[index] {
                ColumnBuilder::Int(b) => b.append_value(
                    parse::parse_int(token).map_err(|e| reader.field_error(spec.name, index, e))?,
                ),
                ColumnBuilder::Dec(b) => b.append_value(
                    parse::parse_decimal(token)
                        .map_err(|e| reader.field_error(spec.name, index, e))?,
                ),
                ColumnBuilder::Date(b) => b.append_value(
                    parse::parse_date(token)
                        .map_err(|e| reader.field_error(spec.name, index, e))?,
                ),
                ColumnBuilder::Str(b) => b.append_value(
                    std::str::from_utf8(token)
                        .map_err(|_| reader.field_error(spec.name, index, TokenError::NotUtf8))?,
                ),
            }
        }
        self.rows += 1;
        Ok(())
    }

    fn len(&self) -> usize {
        self.rows
    }

    /// Emit the accumulated rows and reset the builders for reuse.
    fn finish(&mut self) -> Result<RecordBatch> {
        let arrays: Vec<ArrayRef> = self
            .columns
            .iter_mut()
            .map(|c| -> ArrayRef {
                match c {
                    ColumnBuilder::Int(b) => std::sync::Arc::new(b.finish()),
                    ColumnBuilder::Dec(b) => std::sync::Arc::new(b.finish()),
                    ColumnBuilder::Date(b) => std::sync::Arc::new(b.finish()),
                    ColumnBuilder::Str(b) => std::sync::Arc::new(b.finish()),
                }
            })
            .collect();
        self.rows = 0;
        Ok(RecordBatch::try_new(self.spec.arrow_schema(), arrays)?)
    }
}

/// Knobs for one materialization run.
#[derive(Debug, Clone, Copy)]
pub struct WriteOptions {
    /// Rows per record batch and per parquet row group.
    pub batch_rows: usize,
}

impl Default for WriteOptions {
    fn default() -> Self {
        WriteOptions {
            batch_rows: DEFAULT_BATCH_ROWS,
        }
    }
}

/// What one materialized table cost and produced.
#[derive(Debug, Clone)]
pub struct WriteReport {
    /// Rows written.
    pub rows: u64,
    /// Bytes of the parquet file on disk.
    pub bytes: u64,
    /// Number of parquet row groups.
    pub row_groups: usize,
    /// `created_by` string the parquet writer stamped into the footer.
    pub created_by: Option<String>,
    /// Compression codec name.
    pub compression: String,
    /// Wall time in milliseconds.
    pub wall_ms: u64,
}

/// Materialize one raw `.tbl` file into a Decimal128 parquet file.
///
/// The parse/build side and the parquet encode/write side run on two threads
/// with a depth-1 hand-off, so at most three batches are resident at once.
pub fn write_table(
    spec: &'static TableSpec,
    source: &Path,
    destination: &Path,
    options: WriteOptions,
) -> Result<WriteReport> {
    let started = Instant::now();
    if let Some(parent) = destination.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let properties = WriterProperties::builder()
        .set_compression(Compression::SNAPPY)
        .set_max_row_group_row_count(Some(options.batch_rows))
        .build();
    let sink = BufWriter::with_capacity(
        WRITE_BUFFER_BYTES,
        File::create(destination)
            .map_err(|e| Error::new(format!("cannot create {}: {e}", destination.display())))?,
    );
    let writer = ArrowWriter::try_new(sink, spec.arrow_schema(), Some(properties))?;

    let (tx, rx) = sync_channel::<Result<RecordBatch>>(1);

    let outcome = std::thread::scope(|scope| {
        let producer = scope.spawn(move || -> Result<u64> {
            let mut reader = RowReader::open(source, spec.field_count())?;
            let mut builder = BatchBuilder::new(spec, options.batch_rows);
            let mut rows: u64 = 0;
            loop {
                let more = match reader.next_row() {
                    Ok(more) => more,
                    Err(e) => {
                        let _ = tx.send(Err(e.clone()));
                        return Err(e);
                    }
                };
                if !more {
                    break;
                }
                if let Err(e) = builder.push_row(&reader) {
                    let _ = tx.send(Err(e.clone()));
                    return Err(e);
                }
                rows += 1;
                if builder.len() >= options.batch_rows {
                    let batch = builder.finish();
                    // A closed receiver means the writer already failed; stop
                    // quietly and let that error be reported.
                    if tx.send(batch).is_err() {
                        return Ok(rows);
                    }
                }
            }
            if builder.len() > 0 {
                let batch = builder.finish();
                if tx.send(batch).is_err() {
                    return Ok(rows);
                }
            }
            Ok(rows)
        });

        // Consuming `rx` by value means an early error drops it, which unblocks
        // a producer parked in `send` instead of deadlocking the scope join.
        let consumed = consume(rx, writer);
        let produced = producer
            .join()
            .map_err(|_| Error::new("materialization producer thread panicked"));
        (produced, consumed)
    });

    let (produced, consumed) = outcome;
    // A parse failure is the root cause; report it ahead of any writer fallout.
    let rows = produced??;
    let metadata = consumed?;

    let bytes = std::fs::metadata(destination)?.len();
    Ok(WriteReport {
        rows,
        bytes,
        row_groups: metadata.num_row_groups(),
        created_by: metadata.file_metadata().created_by().map(str::to_owned),
        compression: format!("{:?}", Compression::SNAPPY),
        wall_ms: elapsed_ms(started),
    })
}

fn consume(
    rx: Receiver<Result<RecordBatch>>,
    mut writer: ArrowWriter<BufWriter<File>>,
) -> Result<parquet::file::metadata::ParquetMetaData> {
    for message in rx {
        writer.write(&message?)?;
    }
    Ok(writer.close()?)
}

/// Confirm the parquet file on disk carries exactly the declared schema.
/// Any drift in name, type, order or nullability is a hard failure.
pub fn assert_parquet_schema(spec: &TableSpec, path: &Path) -> Result<()> {
    use parquet::arrow::arrow_reader::ParquetRecordBatchReaderBuilder;

    let file =
        File::open(path).map_err(|e| Error::new(format!("cannot open {}: {e}", path.display())))?;
    let builder = ParquetRecordBatchReaderBuilder::try_new(file)?;
    let actual = builder.schema().clone();
    let expected = spec.arrow_schema();
    if actual.fields().len() != expected.fields().len() {
        return Err(Error::new(format!(
            "{}: {} columns, schema declares {}",
            path.display(),
            actual.fields().len(),
            expected.fields().len()
        )));
    }
    for (got, want) in actual.fields().iter().zip(expected.fields().iter()) {
        if got.name() != want.name()
            || got.data_type() != want.data_type()
            || got.is_nullable() != want.is_nullable()
        {
            return Err(Error::new(format!(
                "{}: column {} is {:?} nullable={}, schema declares {} {:?} nullable={}",
                path.display(),
                got.name(),
                got.data_type(),
                got.is_nullable(),
                want.name(),
                want.data_type(),
                want.is_nullable()
            )));
        }
        if let DataType::Decimal128(p, s) = got.data_type()
            && (*p, *s) != (parse::DECIMAL_PRECISION, parse::DECIMAL_SCALE)
        {
            return Err(Error::new(format!(
                "{}: column {} is Decimal128({p}, {s}), expected Decimal128({}, {})",
                path.display(),
                got.name(),
                parse::DECIMAL_PRECISION,
                parse::DECIMAL_SCALE
            )));
        }
    }
    Ok(())
}

/// Byte length of a file, for the manifest.
pub fn file_len(path: &Path) -> Result<u64> {
    Ok(std::fs::metadata(path)?.len())
}

/// Count the lines of a raw table file independently of the parser, used as a
/// second opinion on the row count.
pub fn count_source_lines(path: &Path) -> Result<u64> {
    let mut file = BufReader::with_capacity(READ_BUFFER_BYTES, File::open(path)?);
    let mut buffer = vec![0u8; READ_BUFFER_BYTES];
    let mut lines = 0u64;
    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        lines += buffer[..n].iter().filter(|&&b| b == b'\n').count() as u64;
    }
    Ok(lines)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schema::{TABLES, table, test_scratch_dir};

    fn write_fixture(name: &str, body: &str) -> PathBuf {
        let dir = test_scratch_dir(name);
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("fixture.tbl");
        std::fs::write(&path, body).unwrap();
        path
    }

    #[test]
    fn row_reader_splits_pipe_terminated_rows() {
        let path = write_fixture("reader-ok", "0|AFRICA|lar deposits|\n1|AMERICA|hs use|\n");
        let mut reader = RowReader::open(&path, 3).unwrap();
        assert!(reader.next_row().unwrap());
        assert_eq!(reader.field(0), b"0");
        assert_eq!(reader.field(1), b"AFRICA");
        assert_eq!(reader.field(2), b"lar deposits");
        assert!(reader.next_row().unwrap());
        assert_eq!(reader.field(1), b"AMERICA");
        assert_eq!(reader.line_no(), 2);
        assert!(!reader.next_row().unwrap());
    }

    #[test]
    fn row_reader_accepts_empty_trailing_field_text() {
        let path = write_fixture("reader-empty-field", "0|AFRICA||\n");
        let mut reader = RowReader::open(&path, 3).unwrap();
        assert!(reader.next_row().unwrap());
        assert_eq!(reader.field(2), b"");
    }

    #[test]
    fn row_reader_rejects_a_missing_terminator() {
        let path = write_fixture("reader-noterm", "0|AFRICA|lar deposits\n");
        let mut reader = RowReader::open(&path, 3).unwrap();
        let err = reader.next_row().unwrap_err();
        assert!(err.message().contains("'|' terminator"), "{err}");
        assert!(err.message().contains(":1:"), "{err}");
    }

    #[test]
    fn row_reader_rejects_a_wrong_field_count() {
        let path = write_fixture("reader-shortrow", "0|AFRICA|\n");
        let mut reader = RowReader::open(&path, 3).unwrap();
        let err = reader.next_row().unwrap_err();
        assert!(
            err.message().contains("2 fields, schema declares 3"),
            "{err}"
        );
    }

    #[test]
    fn a_bad_decimal_token_fails_hard_and_names_file_line_and_column() {
        // partsupp: ps_supplycost is field 4.
        let spec = table("partsupp").unwrap();
        let path = write_fixture("bad-decimal", "1|2|3325|771.6412|comment|\n");
        let out = path.with_extension("parquet");
        let err = write_table(spec, &path, &out, WriteOptions { batch_rows: 8 }).unwrap_err();
        assert!(err.message().contains("ps_supplycost"), "{err}");
        assert!(err.message().contains("(field 4)"), "{err}");
        assert!(err.message().contains("fixture.tbl:1:"), "{err}");
        assert!(err.message().contains("fraction digits"), "{err}");
    }

    #[test]
    fn a_bad_date_token_fails_hard() {
        let spec = table("orders").unwrap();
        let path = write_fixture(
            "bad-date",
            "1|36901|O|173665.47|1996-02-31|5-LOW|Clerk#000000951|0|note|\n",
        );
        let out = path.with_extension("parquet");
        let err = write_table(spec, &path, &out, WriteOptions { batch_rows: 8 }).unwrap_err();
        assert!(err.message().contains("o_orderdate"), "{err}");
        assert!(err.message().contains("day 31"), "{err}");
    }

    #[test]
    fn table_order_is_small_to_large() {
        assert_eq!(TABLES.first().unwrap().name, "region");
        assert_eq!(TABLES.last().unwrap().name, "lineitem");
    }

    #[test]
    fn count_source_lines_agrees_with_the_reader() {
        let path = write_fixture("line-count", "0|A|x|\n1|B|y|\n2|C|z|\n");
        assert_eq!(count_source_lines(&path).unwrap(), 3);
    }
}
