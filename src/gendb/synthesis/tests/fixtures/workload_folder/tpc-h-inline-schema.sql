-- The TPC-H schema of tpc-h/schema.sql with its keys written inside CREATE TABLE (column and table constraints);
-- it reads into the same request.
CREATE TABLE lineitem (
    l_orderkey bigint NOT NULL REFERENCES orders (o_orderkey),
    l_partkey bigint NOT NULL,
    l_suppkey bigint NOT NULL,
    l_linenumber bigint NOT NULL,
    l_quantity numeric(15, 2) NOT NULL,
    l_extendedprice numeric(15,2) NOT NULL,
    l_discount numeric(15,2) NOT NULL,
    l_tax numeric(15,2) NOT NULL,
    l_returnflag text NOT NULL,
    l_linestatus text NOT NULL,
    l_shipdate date NOT NULL,
    l_commitdate date NOT NULL,
    l_receiptdate date NOT NULL,
    l_shipinstruct text NOT NULL,
    l_shipmode text NOT NULL,
    l_comment text NOT NULL,
    PRIMARY KEY (l_orderkey, l_linenumber),
    FOREIGN KEY (l_partkey, l_suppkey)
        REFERENCES partsupp (ps_partkey, ps_suppkey)
);
CREATE TABLE orders (
    o_orderkey bigint NOT NULL PRIMARY KEY,
    o_custkey bigint NOT NULL REFERENCES customer(c_custkey),
    o_orderstatus text NOT NULL,
    o_totalprice numeric(15,2) NOT NULL,
    o_orderdate date NOT NULL,
    o_orderpriority text NOT NULL,
    o_clerk text NOT NULL,
    o_shippriority bigint NOT NULL,
    o_comment text NOT NULL
);
create table customer (
    c_custkey bigint primary key not null,
    c_name text NOT NULL,
    c_address text NOT NULL,
    c_nationkey bigint NOT NULL references nation (n_nationkey),
    c_phone text NOT NULL,
    c_acctbal numeric(15,2) NOT NULL,
    c_mktsegment text NOT NULL,
    c_comment text NOT NULL
);
CREATE TABLE part (
    p_partkey bigint NOT NULL PRIMARY KEY,
    p_name text NOT NULL,
    p_mfgr text NOT NULL,
    p_brand text NOT NULL,
    p_type text NOT NULL,
    p_size bigint NOT NULL,
    p_container text NOT NULL,
    p_retailprice numeric(15,2) NOT NULL,
    p_comment text NOT NULL
);
CREATE TABLE partsupp (
    ps_partkey bigint NOT NULL,
    ps_suppkey bigint NOT NULL,
    ps_availqty bigint NOT NULL,
    ps_supplycost numeric(15,2) NOT NULL,
    ps_comment text NOT NULL,
    PRIMARY KEY (ps_partkey, ps_suppkey),
    FOREIGN KEY (ps_partkey) REFERENCES part (p_partkey),
    FOREIGN KEY (ps_suppkey) REFERENCES supplier (s_suppkey)
);
CREATE TABLE supplier (
    s_suppkey bigint NOT NULL PRIMARY KEY,
    s_name text NOT NULL,
    s_address text NOT NULL,
    s_nationkey bigint NOT NULL REFERENCES nation (n_nationkey),
    s_phone text NOT NULL,
    s_acctbal numeric(15,2) NOT NULL,
    s_comment text NOT NULL
);
CREATE TABLE nation (
    n_nationkey bigint NOT NULL PRIMARY KEY,
    n_name text NOT NULL,
    n_regionkey bigint NOT NULL,
    n_comment text NOT NULL
);
CREATE TABLE region (
    r_regionkey bigint NOT NULL PRIMARY KEY,
    r_name text NOT NULL,
    r_comment text NOT NULL
);
