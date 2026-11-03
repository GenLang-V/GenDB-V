-- $1 i1 text
-- $2 i2 text
-- $3 i3 text
-- $4 i4 text
-- $5 i5 text
-- $6 i6 text
-- $7 i7 text
SELECT
    cntrycode,
    COUNT(*) AS numcust,
    SUM(c_acctbal) AS totacctbal
FROM (
    SELECT
        SUBSTRING(c_phone, 1, 2) AS cntrycode,
        c_acctbal
    FROM customer
    WHERE
        SUBSTRING(c_phone, 1, 2) IN ($1, $2, $3, $4, $5, $6, $7)
        AND c_acctbal > (
            SELECT AVG(c_acctbal) FROM customer
            WHERE
                c_acctbal > 0.00
                AND SUBSTRING(c_phone, 1, 2) IN ($1, $2, $3, $4, $5, $6, $7)
        )
        AND NOT EXISTS (
            SELECT * FROM orders WHERE o_custkey = c_custkey
        )
) AS custsale
GROUP BY cntrycode
ORDER BY cntrycode;
