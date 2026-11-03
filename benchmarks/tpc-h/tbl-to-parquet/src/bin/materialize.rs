//! Driver: materialize TPC-H raw text into exact Decimal128 parquet and check
//! every value back against the text.
//!
//! Usage:
//!   materialize [--scale sf1] [--scale sf10]
//!               [--input DIR] [--output DIR]
//!               [--tables lineitem,orders] [--batch-rows N]
//!
//! Exit status is nonzero on any hard error or on any mismatch.

use std::path::{Path, PathBuf};
use std::time::Instant;

use decimal_store::manifest::{
    ColumnEntry, FAILED_MANIFEST_FILE, MANIFEST_FILE, MANIFEST_SCHEMA_VERSION, Manifest,
    PARTIAL_MANIFEST_FILE, TableEntry, Tools, Totals, WriterSettings, rustc_version, unix_now,
};
use decimal_store::materialize::{
    DEFAULT_BATCH_ROWS, WriteOptions, count_source_lines, elapsed_ms, write_table,
};
use decimal_store::schema::{ColumnKind, TABLES, table};
use decimal_store::verify::verify_table;
use decimal_store::{ARROW_PIN, Error, PARQUET_PIN, Result, peak_rss_kib, sha256_file};

const DEFAULT_SOURCE_ROOT: &str = "benchmarks/tpc-h/raw";
const DEFAULT_OUTPUT_ROOT: &str = "benchmarks/tpc-h/data";

struct Args {
    scales: Vec<String>,
    input: Option<PathBuf>,
    output: Option<PathBuf>,
    tables: Vec<String>,
    batch_rows: usize,
}

fn parse_args() -> Result<Args> {
    let mut args = Args {
        scales: Vec::new(),
        input: None,
        output: None,
        tables: Vec::new(),
        batch_rows: DEFAULT_BATCH_ROWS,
    };
    let mut argv = std::env::args().skip(1);
    while let Some(flag) = argv.next() {
        let mut value = || {
            argv.next()
                .ok_or_else(|| Error::new(format!("{flag} needs a value")))
        };
        match flag.as_str() {
            "--scale" => args.scales.push(value()?),
            "--input" => args.input = Some(PathBuf::from(value()?)),
            "--output" => args.output = Some(PathBuf::from(value()?)),
            "--tables" => {
                args.tables = value()?
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(str::to_string)
                    .collect()
            }
            "--batch-rows" => {
                args.batch_rows = value()?
                    .parse()
                    .map_err(|e| Error::new(format!("--batch-rows: {e}")))?
            }
            other => return Err(Error::new(format!("unknown argument {other}"))),
        }
    }
    if args.scales.is_empty() {
        args.scales.push("sf1".to_string());
    }
    if args.batch_rows == 0 {
        return Err(Error::new("--batch-rows must be positive"));
    }
    Ok(args)
}

fn main() {
    match run() {
        Ok(()) => {}
        Err(e) => {
            eprintln!("materialize: {e}");
            std::process::exit(1);
        }
    }
}

fn run() -> Result<()> {
    let args = parse_args()?;
    for scale in &args.scales {
        let source_dir = args
            .input
            .clone()
            .unwrap_or_else(|| Path::new(DEFAULT_SOURCE_ROOT).join(scale));
        let output_dir = args
            .output
            .clone()
            .unwrap_or_else(|| Path::new(DEFAULT_OUTPUT_ROOT).join(scale));
        materialize_scale(scale, &source_dir, &output_dir, &args)?;
    }
    Ok(())
}

fn selected(args: &Args) -> Vec<&'static decimal_store::schema::TableSpec> {
    if args.tables.is_empty() {
        TABLES.iter().collect()
    } else {
        args.tables.iter().filter_map(|name| table(name)).collect()
    }
}

fn materialize_scale(scale: &str, source_dir: &Path, output_dir: &Path, args: &Args) -> Result<()> {
    let run_started = Instant::now();
    let specs = selected(args);
    if !args.tables.is_empty() && specs.len() != args.tables.len() {
        return Err(Error::new("unknown table name in --tables"));
    }
    std::fs::create_dir_all(output_dir)?;

    // The done marker must never survive a run that is about to rewrite the
    // directory: a reader that raced this run would otherwise trust old bytes.
    let done_marker = output_dir.join(MANIFEST_FILE);
    if done_marker.exists() {
        std::fs::remove_file(&done_marker)?;
    }

    eprintln!(
        "== {scale}: {} -> {}",
        source_dir.display(),
        output_dir.display()
    );

    let mut entries: Vec<TableEntry> = Vec::new();
    let mut created_by: Option<String> = None;
    let mut failure: Option<Error> = None;

    for spec in &specs {
        let source = source_dir.join(format!("{}.tbl", spec.name));
        let parquet = output_dir.join(format!("{}.parquet", spec.name));

        let outcome = (|| -> Result<TableEntry> {
            let source_bytes = std::fs::metadata(&source)
                .map_err(|e| Error::new(format!("cannot stat {}: {e}", source.display())))?
                .len();

            let written = write_table(
                spec,
                &source,
                &parquet,
                WriteOptions {
                    batch_rows: args.batch_rows,
                },
            )?;
            eprintln!(
                "   {:<9} write   {:>12} rows  {:>7} ms  {:>10} MiB parquet",
                spec.name,
                written.rows,
                written.wall_ms,
                written.bytes / (1 << 20)
            );

            let checked = verify_table(spec, &source, &parquet)?;
            eprintln!(
                "   {:<9} check   {:>12} rows  {:>7} ms  mismatches {}",
                spec.name, checked.rows, checked.wall_ms, checked.mismatches
            );

            if checked.rows != written.rows {
                return Err(Error::new(format!(
                    "{}: wrote {} rows but checked {}",
                    spec.name, written.rows, checked.rows
                )));
            }

            let source_lines = count_source_lines(&source)?;
            if source_lines != written.rows {
                return Err(Error::new(format!(
                    "{}: {} newlines in {} but {} rows written",
                    spec.name,
                    source_lines,
                    source.display(),
                    written.rows
                )));
            }

            let hash_started = Instant::now();
            let parquet_sha256 = sha256_file(&parquet)?;
            let sha256_ms = elapsed_ms(hash_started);

            if created_by.is_none() {
                created_by = written.created_by.clone();
            }

            Ok(TableEntry {
                table: spec.name.to_string(),
                source_path: source.display().to_string(),
                source_bytes,
                source_lines,
                parquet_path: parquet.display().to_string(),
                parquet_bytes: written.bytes,
                parquet_sha256,
                rows: written.rows,
                row_groups: written.row_groups,
                write_ms: written.wall_ms,
                verify_ms: checked.wall_ms,
                sha256_ms,
                columns: checked
                    .columns
                    .iter()
                    .map(|c| ColumnEntry {
                        name: c.name.clone(),
                        arrow_type: c.arrow_type.clone(),
                        checked: c.checked,
                        mismatches: c.mismatches,
                    })
                    .collect(),
                mismatches: checked.mismatches,
                samples: checked.samples.clone(),
                peak_rss_kib: peak_rss_kib(),
            })
        })();

        match outcome {
            Ok(entry) => {
                if entry.mismatches != 0 {
                    failure = Some(Error::new(format!(
                        "{}: {} value mismatches",
                        spec.name, entry.mismatches
                    )));
                }
                entries.push(entry);
                if failure.is_some() {
                    break;
                }
            }
            Err(e) => {
                failure = Some(e);
                break;
            }
        }
    }

    // "Complete" means every table of the scale is present and clean; a
    // deliberately partial run never earns the done marker.
    let complete = failure.is_none() && entries.len() == TABLES.len();
    let manifest = Manifest {
        schema_version: MANIFEST_SCHEMA_VERSION,
        scale: scale.to_string(),
        source_dir: source_dir.display().to_string(),
        output_dir: output_dir.display().to_string(),
        generated_unix: unix_now(),
        complete,
        tools: Tools {
            decimal_store: env!("CARGO_PKG_VERSION").to_string(),
            arrow_pin: ARROW_PIN.to_string(),
            parquet_pin: PARQUET_PIN.to_string(),
            rustc: rustc_version(),
            parquet_created_by: created_by,
        },
        writer: WriterSettings {
            batch_rows: args.batch_rows,
            compression: "SNAPPY".to_string(),
            decimal_type: format!("{:?}", ColumnKind::Decimal.data_type()),
            date_type: format!("{:?}", ColumnKind::Date.data_type()),
            integer_type: format!("{:?}", ColumnKind::Int64.data_type()),
            nullable: false,
        },
        totals: Totals {
            tables: entries.len(),
            rows: entries.iter().map(|t| t.rows).sum(),
            values_checked: entries
                .iter()
                .flat_map(|t| t.columns.iter())
                .map(|c| c.checked)
                .sum(),
            mismatches: entries.iter().map(|t| t.mismatches).sum(),
            parquet_bytes: entries.iter().map(|t| t.parquet_bytes).sum(),
            wall_ms: elapsed_ms(run_started),
            peak_rss_kib: peak_rss_kib(),
        },
        tables: entries,
    };

    let name = if complete {
        MANIFEST_FILE
    } else if failure.is_none() {
        PARTIAL_MANIFEST_FILE
    } else {
        FAILED_MANIFEST_FILE
    };
    let path = output_dir.join(name);
    std::fs::write(&path, manifest.to_json()?)?;

    eprintln!(
        "== {scale}: {} tables, {} rows, {} values checked, {} mismatches, {} ms, peak RSS {} MiB -> {}",
        manifest.totals.tables,
        manifest.totals.rows,
        manifest.totals.values_checked,
        manifest.totals.mismatches,
        manifest.totals.wall_ms,
        manifest.totals.peak_rss_kib.unwrap_or(0) / 1024,
        path.display()
    );

    if let Some(e) = failure {
        return Err(e);
    }
    Ok(())
}
