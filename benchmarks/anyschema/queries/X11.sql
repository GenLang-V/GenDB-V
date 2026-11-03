-- $1 not_code text
SELECT kd_weight, COUNT(*) AS n, COUNT(kd_group) AS groups, COUNT(DISTINCT kd_group) AS distinct_groups
FROM ax_kind
WHERE kd_code <> $1
GROUP BY kd_weight
ORDER BY kd_weight;
