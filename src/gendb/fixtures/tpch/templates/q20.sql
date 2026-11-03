SELECT
    s_name,
    s_address
FROM supplier, nation
WHERE
    s_suppkey IN (
        SELECT ps_suppkey FROM partsupp
        WHERE
            ps_partkey IN (
                SELECT p_partkey FROM part WHERE p_name LIKE $1
            )
            AND ps_availqty > (
                SELECT 0.5 * SUM(l_quantity)
                FROM lineitem
                WHERE
                    l_partkey = ps_partkey
                    AND l_suppkey = ps_suppkey
                    AND l_shipdate >= $2
                    AND l_shipdate < $2 + INTERVAL '1' YEAR
            )
    )
    AND s_nationkey = n_nationkey
    AND n_name = $3
ORDER BY s_name;
