//! `MANIFEST.json`: the done marker for one materialized scale factor.
//!
//! Written only after every table of the scale has been materialized and
//! value-checked with zero mismatches. A failed run writes
//! `MANIFEST.FAILED.json` instead, so the presence of `MANIFEST.json` always
//! means "this directory is exact and complete".

use serde::{Deserialize, Serialize};

/// File name other tools look for.
pub const MANIFEST_FILE: &str = "MANIFEST.json";
/// File name written instead when a run failed.
pub const FAILED_MANIFEST_FILE: &str = "MANIFEST.FAILED.json";
/// File name written when a run deliberately covered only some tables.
pub const PARTIAL_MANIFEST_FILE: &str = "MANIFEST.PARTIAL.json";
/// Bumped whenever the manifest shape changes.
pub const MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Versions of everything that shaped the bytes on disk.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Tools {
    /// Version of this crate.
    pub decimal_store: String,
    /// Workspace-pinned arrow version.
    pub arrow_pin: String,
    /// Workspace-pinned parquet version.
    pub parquet_pin: String,
    /// `rustc --version` on the machine that ran the materialization.
    pub rustc: Option<String>,
    /// `created_by` string the parquet writer stamped into the footers.
    pub parquet_created_by: Option<String>,
}

/// Writer settings that affect the physical layout.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WriterSettings {
    /// Rows per record batch and per row group.
    pub batch_rows: usize,
    /// Compression codec.
    pub compression: String,
    /// Arrow type used for every TPC-H decimal column.
    pub decimal_type: String,
    /// Arrow type used for every TPC-H date column.
    pub date_type: String,
    /// Arrow type used for every TPC-H integer column.
    pub integer_type: String,
    /// Every column is declared NOT NULL.
    pub nullable: bool,
}

/// One column's value-check outcome.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ColumnEntry {
    /// Column name.
    pub name: String,
    /// Arrow type.
    pub arrow_type: String,
    /// Values compared against the raw text.
    pub checked: u64,
    /// Values that differed. Must be zero.
    pub mismatches: u64,
}

/// One materialized table.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TableEntry {
    /// Table name.
    pub table: String,
    /// Raw source file.
    pub source_path: String,
    /// Raw source size in bytes.
    pub source_bytes: u64,
    /// Newline count of the raw source, counted independently of the parser.
    pub source_lines: u64,
    /// Materialized parquet file.
    pub parquet_path: String,
    /// Parquet size in bytes.
    pub parquet_bytes: u64,
    /// SHA-256 of the parquet file.
    pub parquet_sha256: String,
    /// Rows written and checked.
    pub rows: u64,
    /// Parquet row groups.
    pub row_groups: usize,
    /// Materialization wall time.
    pub write_ms: u64,
    /// Value-check wall time.
    pub verify_ms: u64,
    /// Hashing wall time.
    pub sha256_ms: u64,
    /// Per-column check counts.
    pub columns: Vec<ColumnEntry>,
    /// Sum of per-column mismatches. Must be zero.
    pub mismatches: u64,
    /// Rendered differences, empty on a clean run.
    pub samples: Vec<String>,
    /// Process peak RSS in KiB observed after this table finished.
    pub peak_rss_kib: Option<u64>,
}

/// Totals across the scale.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Totals {
    /// Tables materialized.
    pub tables: usize,
    /// Rows across all tables.
    pub rows: u64,
    /// Individual values compared.
    pub values_checked: u64,
    /// Values that differed. Must be zero.
    pub mismatches: u64,
    /// Parquet bytes written.
    pub parquet_bytes: u64,
    /// Wall time of the whole run.
    pub wall_ms: u64,
    /// Process peak RSS in KiB across the whole run.
    pub peak_rss_kib: Option<u64>,
}

/// The done marker for one scale.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
    /// Manifest shape version.
    pub schema_version: u32,
    /// Scale name, e.g. `sf10`.
    pub scale: String,
    /// Raw input directory.
    pub source_dir: String,
    /// Materialized output directory.
    pub output_dir: String,
    /// Unix seconds at which the run finished.
    pub generated_unix: u64,
    /// True only when every table checked clean.
    pub complete: bool,
    /// Versions.
    pub tools: Tools,
    /// Writer settings.
    pub writer: WriterSettings,
    /// Per-table entries.
    pub tables: Vec<TableEntry>,
    /// Totals.
    pub totals: Totals,
}

impl Manifest {
    /// Serialize to pretty JSON with a trailing newline.
    pub fn to_json(&self) -> crate::Result<String> {
        let mut text = serde_json::to_string_pretty(self)
            .map_err(|e| crate::Error::new(format!("cannot serialize manifest: {e}")))?;
        text.push('\n');
        Ok(text)
    }
}

/// `rustc --version`, or `None` if rustc is not on PATH.
pub fn rustc_version() -> Option<String> {
    let output = std::process::Command::new("rustc")
        .arg("--version")
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

/// Unix seconds now.
pub fn unix_now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Manifest {
        Manifest {
            schema_version: MANIFEST_SCHEMA_VERSION,
            scale: "sf1".into(),
            source_dir: "/src".into(),
            output_dir: "/out".into(),
            generated_unix: 1,
            complete: true,
            tools: Tools {
                decimal_store: "0.1.0".into(),
                arrow_pin: "58.1.0".into(),
                parquet_pin: "58.1.0".into(),
                rustc: Some("rustc 1.94.0".into()),
                parquet_created_by: Some("parquet-rs".into()),
            },
            writer: WriterSettings {
                batch_rows: 1_000_000,
                compression: "SNAPPY".into(),
                decimal_type: "Decimal128(15, 2)".into(),
                date_type: "Date32".into(),
                integer_type: "Int64".into(),
                nullable: false,
            },
            tables: vec![TableEntry {
                table: "region".into(),
                source_path: "/src/region.tbl".into(),
                source_bytes: 389,
                source_lines: 5,
                parquet_path: "/out/region.parquet".into(),
                parquet_bytes: 1234,
                parquet_sha256: "00".into(),
                rows: 5,
                row_groups: 1,
                write_ms: 1,
                verify_ms: 1,
                sha256_ms: 0,
                columns: vec![ColumnEntry {
                    name: "r_regionkey".into(),
                    arrow_type: "Int64".into(),
                    checked: 5,
                    mismatches: 0,
                }],
                mismatches: 0,
                samples: vec![],
                peak_rss_kib: Some(1000),
            }],
            totals: Totals {
                tables: 1,
                rows: 5,
                values_checked: 15,
                mismatches: 0,
                parquet_bytes: 1234,
                wall_ms: 3,
                peak_rss_kib: Some(1000),
            },
        }
    }

    #[test]
    fn manifest_round_trips_through_json() {
        let manifest = sample();
        let json = manifest.to_json().unwrap();
        assert!(json.ends_with('\n'));
        let back: Manifest = serde_json::from_str(&json).unwrap();
        assert_eq!(back.scale, "sf1");
        assert_eq!(back.totals.mismatches, 0);
        assert_eq!(back.tables[0].rows, 5);
        assert_eq!(back.writer.decimal_type, "Decimal128(15, 2)");
        assert!(!back.writer.nullable);
    }

    #[test]
    fn unix_now_is_after_2020() {
        assert!(unix_now() > 1_577_836_800);
    }
}
