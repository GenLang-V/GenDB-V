Fixtures of the gendb-frontend tests.

- `prepared_tpch_schema.sql`: the DDL the synthesis controller writes for a four-table prepared TPC-H dataset (lineitem = table 0, orders = 1, customer = 2, part = 3), read by `params_columns.rs`.

`saved_statements.rs` reads saved run records that are not in this repository, so it fails here.
