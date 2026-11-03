//! The TPC-H schema of `benchmarks/tpc-h/schema.sql` as `spec::types` data: table ids in DDL order, columns with
//! their declared types, and the PRIMARY KEY / REFERENCES constraints in the translator's declaration order.
//! `constraint_declarations` checks that it is well formed.
use vstd::prelude::*;
use crate::spec::types::*;

verus! {

/// 0: nation(n_nationkey, n_name, n_regionkey, n_comment)
pub open spec fn tpch_nation() -> TableSchema {
    TableSchema { columns: seq![
        Column { ty: SqlType::Int4, nullable: false }, // n_nationkey
        Column { ty: SqlType::Bpchar { len: 25 }, nullable: false }, // n_name
        Column { ty: SqlType::Int4, nullable: false }, // n_regionkey
        Column { ty: SqlType::Varchar { max_chars: 152 }, nullable: true }, // n_comment
    ], constraints: seq![pk(seq![0nat])] }
}

/// 1: region(r_regionkey, r_name, r_comment)
pub open spec fn tpch_region() -> TableSchema {
    TableSchema { columns: seq![
        Column { ty: SqlType::Int4, nullable: false }, // r_regionkey
        Column { ty: SqlType::Bpchar { len: 25 }, nullable: false }, // r_name
        Column { ty: SqlType::Varchar { max_chars: 152 }, nullable: true }, // r_comment
    ], constraints: seq![pk(seq![0nat])] }
}

/// 2: supplier(s_suppkey, s_name, s_address, s_nationkey, s_phone, s_acctbal, s_comment)
pub open spec fn tpch_supplier() -> TableSchema {
    TableSchema { columns: seq![
        Column { ty: SqlType::Int4, nullable: false }, // s_suppkey
        Column { ty: SqlType::Bpchar { len: 25 }, nullable: false }, // s_name
        Column { ty: SqlType::Varchar { max_chars: 40 }, nullable: false }, // s_address
        Column { ty: SqlType::Int4, nullable: false }, // s_nationkey
        Column { ty: SqlType::Bpchar { len: 15 }, nullable: false }, // s_phone
        Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }, // s_acctbal
        Column { ty: SqlType::Varchar { max_chars: 101 }, nullable: false }, // s_comment
    ], constraints: seq![pk(seq![0nat]), fk(seq![3nat], 0, seq![0nat])] }
}

/// 3: part(p_partkey, p_name, p_mfgr, p_brand, p_type, p_size, p_container, p_retailprice, p_comment)
pub open spec fn tpch_part() -> TableSchema {
    TableSchema { columns: seq![
        Column { ty: SqlType::Int4, nullable: false }, // p_partkey
        Column { ty: SqlType::Varchar { max_chars: 55 }, nullable: false }, // p_name
        Column { ty: SqlType::Bpchar { len: 25 }, nullable: false }, // p_mfgr
        Column { ty: SqlType::Bpchar { len: 10 }, nullable: false }, // p_brand
        Column { ty: SqlType::Varchar { max_chars: 25 }, nullable: false }, // p_type
        Column { ty: SqlType::Int4, nullable: false }, // p_size
        Column { ty: SqlType::Bpchar { len: 10 }, nullable: false }, // p_container
        Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }, // p_retailprice
        Column { ty: SqlType::Varchar { max_chars: 23 }, nullable: false }, // p_comment
    ], constraints: seq![pk(seq![0nat])] }
}

/// 4: partsupp(ps_partkey, ps_suppkey, ps_availqty, ps_supplycost, ps_comment)
pub open spec fn tpch_partsupp() -> TableSchema {
    TableSchema { columns: seq![
        Column { ty: SqlType::Int4, nullable: false }, // ps_partkey
        Column { ty: SqlType::Int4, nullable: false }, // ps_suppkey
        Column { ty: SqlType::Int4, nullable: false }, // ps_availqty
        Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }, // ps_supplycost
        Column { ty: SqlType::Varchar { max_chars: 199 }, nullable: false }, // ps_comment
    ], constraints: seq![fk(seq![0nat], 3, seq![0nat]), fk(seq![1nat], 2, seq![0nat]), pk(seq![0nat, 1nat])] }
}

/// 5: customer(c_custkey, c_name, c_address, c_nationkey, c_phone, c_acctbal, c_mktsegment, c_comment)
pub open spec fn tpch_customer() -> TableSchema {
    TableSchema { columns: seq![
        Column { ty: SqlType::Int4, nullable: false }, // c_custkey
        Column { ty: SqlType::Varchar { max_chars: 25 }, nullable: false }, // c_name
        Column { ty: SqlType::Varchar { max_chars: 40 }, nullable: false }, // c_address
        Column { ty: SqlType::Int4, nullable: false }, // c_nationkey
        Column { ty: SqlType::Bpchar { len: 15 }, nullable: false }, // c_phone
        Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }, // c_acctbal
        Column { ty: SqlType::Bpchar { len: 10 }, nullable: false }, // c_mktsegment
        Column { ty: SqlType::Varchar { max_chars: 117 }, nullable: false }, // c_comment
    ], constraints: seq![pk(seq![0nat]), fk(seq![3nat], 0, seq![0nat])] }
}

/// 6: orders(o_orderkey, o_custkey, o_orderstatus, o_totalprice, o_orderdate, o_orderpriority, o_clerk, o_shippriority, o_comment)
pub open spec fn tpch_orders() -> TableSchema {
    TableSchema { columns: seq![
        Column { ty: SqlType::Int4, nullable: false }, // o_orderkey
        Column { ty: SqlType::Int4, nullable: false }, // o_custkey
        Column { ty: SqlType::Bpchar { len: 1 }, nullable: false }, // o_orderstatus
        Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }, // o_totalprice
        Column { ty: SqlType::Date, nullable: false }, // o_orderdate
        Column { ty: SqlType::Bpchar { len: 15 }, nullable: false }, // o_orderpriority
        Column { ty: SqlType::Bpchar { len: 15 }, nullable: false }, // o_clerk
        Column { ty: SqlType::Int4, nullable: false }, // o_shippriority
        Column { ty: SqlType::Varchar { max_chars: 79 }, nullable: false }, // o_comment
    ], constraints: seq![pk(seq![0nat]), fk(seq![1nat], 5, seq![0nat])] }
}

/// 7: lineitem(l_orderkey, l_partkey, l_suppkey, l_linenumber, l_quantity, l_extendedprice, l_discount, l_tax, l_returnflag, l_linestatus, l_shipdate, l_commitdate, l_receiptdate, l_shipinstruct, l_shipmode, l_comment)
pub open spec fn tpch_lineitem() -> TableSchema {
    TableSchema { columns: seq![
        Column { ty: SqlType::Int4, nullable: false }, // l_orderkey
        Column { ty: SqlType::Int4, nullable: false }, // l_partkey
        Column { ty: SqlType::Int4, nullable: false }, // l_suppkey
        Column { ty: SqlType::Int4, nullable: false }, // l_linenumber
        Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }, // l_quantity
        Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }, // l_extendedprice
        Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }, // l_discount
        Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }, // l_tax
        Column { ty: SqlType::Bpchar { len: 1 }, nullable: false }, // l_returnflag
        Column { ty: SqlType::Bpchar { len: 1 }, nullable: false }, // l_linestatus
        Column { ty: SqlType::Date, nullable: false }, // l_shipdate
        Column { ty: SqlType::Date, nullable: false }, // l_commitdate
        Column { ty: SqlType::Date, nullable: false }, // l_receiptdate
        Column { ty: SqlType::Bpchar { len: 25 }, nullable: false }, // l_shipinstruct
        Column { ty: SqlType::Bpchar { len: 10 }, nullable: false }, // l_shipmode
        Column { ty: SqlType::Varchar { max_chars: 44 }, nullable: false }, // l_comment
    ], constraints: seq![fk(seq![0nat], 6, seq![0nat]), pk(seq![0nat, 3nat]), fk(seq![1nat, 2nat], 4, seq![0nat, 1nat])] }
}

/// `PRIMARY KEY (cols)`.
pub open spec fn pk(cols: Seq<nat>) -> Constraint {
    Constraint::Key { cols, primary: true, nulls_distinct: true }
}

/// `FOREIGN KEY (cols) REFERENCES table (ref_cols)` (MATCH SIMPLE).
pub open spec fn fk(cols: Seq<nat>, table: nat, ref_cols: Seq<nat>) -> Constraint {
    Constraint::ForeignKey { cols, table, ref_cols, match_full: false }
}

/// The eight tables, table id = position.
pub open spec fn tpch_schema() -> Schema {
    seq![tpch_nation(), tpch_region(), tpch_supplier(), tpch_part(), tpch_partsupp(), tpch_customer(), tpch_orders(), tpch_lineitem()]
}

} // verus!
