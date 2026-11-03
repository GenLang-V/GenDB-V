-- $1 brand text
-- $2 type text
-- $3 size1 integer
-- $4 size2 integer
-- $5 size3 integer
-- $6 size4 integer
-- $7 size5 integer
-- $8 size6 integer
-- $9 size7 integer
-- $10 size8 integer
SELECT
    p_brand,
    p_type,
    p_size,
    COUNT(DISTINCT ps_suppkey) AS supplier_cnt
FROM partsupp, part
WHERE
    p_partkey = ps_partkey
    AND p_brand <> $1
    AND p_type NOT LIKE $2
    AND p_size IN ($3, $4, $5, $6, $7, $8, $9, $10)
    AND ps_suppkey NOT IN (
        SELECT s_suppkey FROM supplier
        WHERE s_comment LIKE '%Customer%Complaints%'
    )
GROUP BY p_brand, p_type, p_size
ORDER BY supplier_cnt DESC, p_brand, p_type, p_size;
