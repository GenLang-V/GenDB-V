-- $1 brand1 text
-- $2 quantity1 integer
-- $3 brand2 text
-- $4 quantity2 integer
-- $5 brand3 text
-- $6 quantity3 integer
SELECT
    SUM(l_extendedprice * (1 - l_discount)) AS revenue
FROM lineitem, part
WHERE
    (
        p_partkey = l_partkey
        AND p_brand = $1
        AND p_container IN ('SM CASE', 'SM BOX', 'SM PACK', 'SM PKG')
        AND l_quantity >= $2 AND l_quantity <= $2 + 10
        AND p_size BETWEEN 1 AND 5
        AND l_shipmode IN ('AIR', 'AIR REG')
        AND l_shipinstruct = 'DELIVER IN PERSON'
    )
    OR (
        p_partkey = l_partkey
        AND p_brand = $3
        AND p_container IN ('MED BAG', 'MED BOX', 'MED PKG', 'MED PACK')
        AND l_quantity >= $4 AND l_quantity <= $4 + 10
        AND p_size BETWEEN 1 AND 10
        AND l_shipmode IN ('AIR', 'AIR REG')
        AND l_shipinstruct = 'DELIVER IN PERSON'
    )
    OR (
        p_partkey = l_partkey
        AND p_brand = $5
        AND p_container IN ('LG CASE', 'LG BOX', 'LG PACK', 'LG PKG')
        AND l_quantity >= $6 AND l_quantity <= $6 + 10
        AND p_size BETWEEN 1 AND 15
        AND l_shipmode IN ('AIR', 'AIR REG')
        AND l_shipinstruct = 'DELIVER IN PERSON'
    );
