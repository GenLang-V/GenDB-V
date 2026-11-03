ALTER ROLE postgres WITH LOGIN SUPERUSER PASSWORD 'postgres';
CREATE TABLE region (
    r_regionkey BIGINT NOT NULL,
    r_name VARCHAR NOT NULL,
    r_comment VARCHAR NOT NULL,
    PRIMARY KEY (r_regionkey)
);

CREATE TABLE nation (
    n_nationkey BIGINT NOT NULL,
    n_name VARCHAR NOT NULL,
    n_regionkey BIGINT NOT NULL,
    n_comment VARCHAR NOT NULL,
    PRIMARY KEY (n_nationkey)
);

CREATE TABLE supplier (
    s_suppkey BIGINT NOT NULL,
    s_name VARCHAR NOT NULL,
    s_address VARCHAR NOT NULL,
    s_nationkey BIGINT NOT NULL,
    s_phone VARCHAR NOT NULL,
    s_acctbal DECIMAL(15,2) NOT NULL,
    s_comment VARCHAR NOT NULL,
    PRIMARY KEY (s_suppkey),
    FOREIGN KEY (s_nationkey) REFERENCES nation (n_nationkey)
);

CREATE TABLE customer (
    c_custkey BIGINT NOT NULL,
    c_name VARCHAR NOT NULL,
    c_address VARCHAR NOT NULL,
    c_nationkey BIGINT NOT NULL,
    c_phone VARCHAR NOT NULL,
    c_acctbal DECIMAL(15,2) NOT NULL,
    c_mktsegment VARCHAR NOT NULL,
    c_comment VARCHAR NOT NULL,
    PRIMARY KEY (c_custkey),
    FOREIGN KEY (c_nationkey) REFERENCES nation (n_nationkey)
);

CREATE TABLE part (
    p_partkey BIGINT NOT NULL,
    p_name VARCHAR NOT NULL,
    p_mfgr VARCHAR NOT NULL,
    p_brand VARCHAR NOT NULL,
    p_type VARCHAR NOT NULL,
    p_size BIGINT NOT NULL,
    p_container VARCHAR NOT NULL,
    p_retailprice DECIMAL(15,2) NOT NULL,
    p_comment VARCHAR NOT NULL,
    PRIMARY KEY (p_partkey)
);

CREATE TABLE partsupp (
    ps_partkey BIGINT NOT NULL,
    ps_suppkey BIGINT NOT NULL,
    ps_availqty BIGINT NOT NULL,
    ps_supplycost DECIMAL(15,2) NOT NULL,
    ps_comment VARCHAR NOT NULL,
    PRIMARY KEY (ps_partkey, ps_suppkey),
    FOREIGN KEY (ps_partkey) REFERENCES part (p_partkey),
    FOREIGN KEY (ps_suppkey) REFERENCES supplier (s_suppkey)
);

CREATE TABLE orders (
    o_orderkey BIGINT NOT NULL,
    o_custkey BIGINT NOT NULL,
    o_orderstatus VARCHAR NOT NULL,
    o_totalprice DECIMAL(15,2) NOT NULL,
    o_orderdate DATE NOT NULL,
    o_orderpriority VARCHAR NOT NULL,
    o_clerk VARCHAR NOT NULL,
    o_shippriority BIGINT NOT NULL,
    o_comment VARCHAR NOT NULL,
    PRIMARY KEY (o_orderkey),
    FOREIGN KEY (o_custkey) REFERENCES customer (c_custkey)
);

CREATE TABLE lineitem (
    l_orderkey BIGINT NOT NULL,
    l_partkey BIGINT NOT NULL,
    l_suppkey BIGINT NOT NULL,
    l_linenumber BIGINT NOT NULL,
    l_quantity DECIMAL(15,2) NOT NULL,
    l_extendedprice DECIMAL(15,2) NOT NULL,
    l_discount DECIMAL(15,2) NOT NULL,
    l_tax DECIMAL(15,2) NOT NULL,
    l_returnflag VARCHAR NOT NULL,
    l_linestatus VARCHAR NOT NULL,
    l_shipdate DATE NOT NULL,
    l_commitdate DATE NOT NULL,
    l_receiptdate DATE NOT NULL,
    l_shipinstruct VARCHAR NOT NULL,
    l_shipmode VARCHAR NOT NULL,
    l_comment VARCHAR NOT NULL,
    PRIMARY KEY (l_orderkey, l_linenumber),
    FOREIGN KEY (l_orderkey) REFERENCES orders (o_orderkey),
    FOREIGN KEY (l_partkey, l_suppkey) REFERENCES partsupp (ps_partkey, ps_suppkey)
);

COPY region FROM '/data/region.tbl' WITH (DELIMITER '|');
SELECT 'loaded' AS step, 'region' AS tbl, COUNT(*) AS n, now() AS at FROM region;
COPY nation FROM '/data/nation.tbl' WITH (DELIMITER '|');
SELECT 'loaded' AS step, 'nation' AS tbl, COUNT(*) AS n, now() AS at FROM nation;
COPY supplier FROM '/data/supplier.tbl' WITH (DELIMITER '|');
SELECT 'loaded' AS step, 'supplier' AS tbl, COUNT(*) AS n, now() AS at FROM supplier;
COPY customer FROM '/data/customer.tbl' WITH (DELIMITER '|');
SELECT 'loaded' AS step, 'customer' AS tbl, COUNT(*) AS n, now() AS at FROM customer;
COPY part FROM '/data/part.tbl' WITH (DELIMITER '|');
SELECT 'loaded' AS step, 'part' AS tbl, COUNT(*) AS n, now() AS at FROM part;
COPY partsupp FROM '/data/partsupp.tbl' WITH (DELIMITER '|');
SELECT 'loaded' AS step, 'partsupp' AS tbl, COUNT(*) AS n, now() AS at FROM partsupp;
COPY orders FROM '/data/orders.tbl' WITH (DELIMITER '|');
SELECT 'loaded' AS step, 'orders' AS tbl, COUNT(*) AS n, now() AS at FROM orders;
COPY lineitem FROM '/data/lineitem.tbl' WITH (DELIMITER '|');
SELECT 'loaded' AS step, 'lineitem' AS tbl, COUNT(*) AS n, now() AS at FROM lineitem;
SELECT c.relname, i.indisprimary, i.indisunique FROM pg_index i, pg_class c WHERE c.oid = i.indexrelid ORDER BY 1;
