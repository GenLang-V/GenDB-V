//! The materialized TPC-H schema.
//!
//! Fixed for the published runs: every decimal column is `Decimal128(15, 2)`,
//! every date is `Date32`, every integer is `Int64`, every character column is
//! `Utf8`. TPC-H declares every column NOT NULL, so every field is declared
//! non-nullable and the value check asserts a zero null count.

use std::path::PathBuf;
use std::sync::Arc;

use arrow::datatypes::{DataType, Field, Schema};

use crate::parse::{DECIMAL_PRECISION, DECIMAL_SCALE};

/// Logical kind of a materialized column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ColumnKind {
    /// Any TPC-H integer or key column.
    Int64,
    /// Any TPC-H decimal column, stored as `Decimal128(15, 2)`.
    Decimal,
    /// Any TPC-H date column, stored as `Date32`.
    Date,
    /// Any TPC-H character column.
    Utf8,
}

impl ColumnKind {
    /// Arrow type of this column kind.
    pub fn data_type(self) -> DataType {
        match self {
            ColumnKind::Int64 => DataType::Int64,
            ColumnKind::Decimal => DataType::Decimal128(DECIMAL_PRECISION, DECIMAL_SCALE),
            ColumnKind::Date => DataType::Date32,
            ColumnKind::Utf8 => DataType::Utf8,
        }
    }
}

/// One materialized column.
#[derive(Debug, Clone, Copy)]
pub struct ColumnSpec {
    /// Column name, lower case, TPC-H spelling.
    pub name: &'static str,
    /// Logical kind.
    pub kind: ColumnKind,
}

const fn col(name: &'static str, kind: ColumnKind) -> ColumnSpec {
    ColumnSpec { name, kind }
}

/// One materialized table.
#[derive(Debug, Clone, Copy)]
pub struct TableSpec {
    /// Table name, matching the `<name>.tbl` source file stem.
    pub name: &'static str,
    /// Column list in raw-file field order.
    pub columns: &'static [ColumnSpec],
}

impl TableSpec {
    /// Number of `|`-separated fields per raw line.
    pub fn field_count(&self) -> usize {
        self.columns.len()
    }

    /// Arrow schema of the materialized parquet file.
    pub fn arrow_schema(&self) -> Arc<Schema> {
        let fields: Vec<Field> = self
            .columns
            .iter()
            .map(|c| Field::new(c.name, c.kind.data_type(), false))
            .collect();
        Arc::new(Schema::new(fields))
    }
}

use ColumnKind::{Date, Decimal, Int64, Utf8};

/// All eight TPC-H tables, ordered small to large so a materialization run
/// surfaces a schema or parse failure on a cheap table before spending an hour
/// on lineitem.
pub const TABLES: &[TableSpec] = &[
    TableSpec {
        name: "region",
        columns: &[
            col("r_regionkey", Int64),
            col("r_name", Utf8),
            col("r_comment", Utf8),
        ],
    },
    TableSpec {
        name: "nation",
        columns: &[
            col("n_nationkey", Int64),
            col("n_name", Utf8),
            col("n_regionkey", Int64),
            col("n_comment", Utf8),
        ],
    },
    TableSpec {
        name: "supplier",
        columns: &[
            col("s_suppkey", Int64),
            col("s_name", Utf8),
            col("s_address", Utf8),
            col("s_nationkey", Int64),
            col("s_phone", Utf8),
            col("s_acctbal", Decimal),
            col("s_comment", Utf8),
        ],
    },
    TableSpec {
        name: "customer",
        columns: &[
            col("c_custkey", Int64),
            col("c_name", Utf8),
            col("c_address", Utf8),
            col("c_nationkey", Int64),
            col("c_phone", Utf8),
            col("c_acctbal", Decimal),
            col("c_mktsegment", Utf8),
            col("c_comment", Utf8),
        ],
    },
    TableSpec {
        name: "part",
        columns: &[
            col("p_partkey", Int64),
            col("p_name", Utf8),
            col("p_mfgr", Utf8),
            col("p_brand", Utf8),
            col("p_type", Utf8),
            col("p_size", Int64),
            col("p_container", Utf8),
            col("p_retailprice", Decimal),
            col("p_comment", Utf8),
        ],
    },
    TableSpec {
        name: "partsupp",
        columns: &[
            col("ps_partkey", Int64),
            col("ps_suppkey", Int64),
            col("ps_availqty", Int64),
            col("ps_supplycost", Decimal),
            col("ps_comment", Utf8),
        ],
    },
    TableSpec {
        name: "orders",
        columns: &[
            col("o_orderkey", Int64),
            col("o_custkey", Int64),
            col("o_orderstatus", Utf8),
            col("o_totalprice", Decimal),
            col("o_orderdate", Date),
            col("o_orderpriority", Utf8),
            col("o_clerk", Utf8),
            col("o_shippriority", Int64),
            col("o_comment", Utf8),
        ],
    },
    TableSpec {
        name: "lineitem",
        columns: &[
            col("l_orderkey", Int64),
            col("l_partkey", Int64),
            col("l_suppkey", Int64),
            col("l_linenumber", Int64),
            col("l_quantity", Decimal),
            col("l_extendedprice", Decimal),
            col("l_discount", Decimal),
            col("l_tax", Decimal),
            col("l_returnflag", Utf8),
            col("l_linestatus", Utf8),
            col("l_shipdate", Date),
            col("l_commitdate", Date),
            col("l_receiptdate", Date),
            col("l_shipinstruct", Utf8),
            col("l_shipmode", Utf8),
            col("l_comment", Utf8),
        ],
    },
];

/// Look a table up by name.
pub fn table(name: &str) -> Option<&'static TableSpec> {
    TABLES.iter().find(|t| t.name == name)
}

/// Repository-local scratch root. Never `/tmp` (project rule).
pub const SCRATCH_ROOT: &str = "target/decimal-store-test-scratch";

/// A named scratch subdirectory for tests.
pub fn test_scratch_dir(name: &str) -> PathBuf {
    PathBuf::from(SCRATCH_ROOT).join("t").join(name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_table_is_present_with_the_tpch_field_count() {
        let expected: &[(&str, usize)] = &[
            ("region", 3),
            ("nation", 4),
            ("supplier", 7),
            ("customer", 8),
            ("part", 9),
            ("partsupp", 5),
            ("orders", 9),
            ("lineitem", 16),
        ];
        assert_eq!(TABLES.len(), expected.len());
        for (name, fields) in expected {
            let spec = table(name).unwrap_or_else(|| panic!("missing table {name}"));
            assert_eq!(spec.field_count(), *fields, "field count for {name}");
        }
    }

    #[test]
    fn decimal_columns_are_exactly_the_tpch_money_columns() {
        let mut decimals: Vec<&str> = Vec::new();
        for t in TABLES {
            for c in t.columns {
                if c.kind == ColumnKind::Decimal {
                    decimals.push(c.name);
                }
            }
        }
        decimals.sort_unstable();
        assert_eq!(
            decimals,
            vec![
                "c_acctbal",
                "l_discount",
                "l_extendedprice",
                "l_quantity",
                "l_tax",
                "o_totalprice",
                "p_retailprice",
                "ps_supplycost",
                "s_acctbal",
            ]
        );
    }

    #[test]
    fn date_columns_are_exactly_the_tpch_date_columns() {
        let mut dates: Vec<&str> = Vec::new();
        for t in TABLES {
            for c in t.columns {
                if c.kind == ColumnKind::Date {
                    dates.push(c.name);
                }
            }
        }
        dates.sort_unstable();
        assert_eq!(
            dates,
            vec!["l_commitdate", "l_receiptdate", "l_shipdate", "o_orderdate"]
        );
    }

    #[test]
    fn arrow_schema_is_decimal128_15_2_and_not_null() {
        let lineitem = table("lineitem").unwrap();
        let schema = lineitem.arrow_schema();
        assert_eq!(schema.fields().len(), 16);
        for field in schema.fields() {
            assert!(!field.is_nullable(), "{} must be NOT NULL", field.name());
        }
        assert_eq!(
            schema
                .field_with_name("l_extendedprice")
                .unwrap()
                .data_type(),
            &DataType::Decimal128(15, 2)
        );
        assert_eq!(
            schema.field_with_name("l_shipdate").unwrap().data_type(),
            &DataType::Date32
        );
        assert_eq!(
            schema.field_with_name("l_orderkey").unwrap().data_type(),
            &DataType::Int64
        );
        assert_eq!(
            schema.field_with_name("l_comment").unwrap().data_type(),
            &DataType::Utf8
        );
    }
}
