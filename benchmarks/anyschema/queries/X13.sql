-- $1 min_rank integer
SELECT ow_born, COUNT(ow_weight) AS n, SUM(ow_weight) AS total, AVG(ow_weight) AS mean, MIN(ow_weight) AS low,
       MAX(ow_weight) AS high
FROM ax_owner
WHERE ow_rank IS NULL OR ow_rank >= $1
GROUP BY ow_born
ORDER BY ow_born;
