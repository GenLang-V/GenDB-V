-- $1 nation text
-- $2 fraction numeric(38,10)
SELECT
    ps_partkey,
    SUM(ps_supplycost * ps_availqty) AS value
FROM partsupp, supplier, nation
WHERE
    ps_suppkey = s_suppkey
    AND s_nationkey = n_nationkey
    AND n_name = $1
GROUP BY ps_partkey
HAVING SUM(ps_supplycost * ps_availqty) > (
    SELECT SUM(ps_supplycost * ps_availqty) * $2
    FROM partsupp, supplier, nation
    WHERE
        ps_suppkey = s_suppkey
        AND s_nationkey = n_nationkey
        AND n_name = $1
)
ORDER BY value DESC;
