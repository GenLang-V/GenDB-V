-- $1 date date
SELECT
    o_orderpriority,
    COUNT(*) AS order_count
FROM orders
WHERE
    o_orderdate >= $1
    AND o_orderdate < $1 + INTERVAL '3' MONTH
    AND EXISTS (
        SELECT * FROM lineitem
        WHERE l_orderkey = o_orderkey
          AND l_commitdate < l_receiptdate
    )
GROUP BY o_orderpriority
ORDER BY o_orderpriority;
