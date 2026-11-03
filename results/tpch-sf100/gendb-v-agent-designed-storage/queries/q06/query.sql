SELECT
    SUM(l_extendedprice * l_discount) AS revenue
FROM lineitem
WHERE
    l_shipdate >= $1
    AND l_shipdate < $1 + INTERVAL '1' YEAR
    AND l_discount BETWEEN $2 - 0.01 AND $2 + 0.01
    AND l_quantity < $3;
