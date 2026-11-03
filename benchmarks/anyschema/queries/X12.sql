-- $1 from_day date
SELECT it_kind, it_flag, COUNT(*) AS n, SUM(it_qty) AS qty, AVG(it_qty) AS mean_qty, SUM(it_price) AS price,
       MIN(it_day) AS first_day, MAX(it_day) AS last_day
FROM ax_item
WHERE it_day >= $1
GROUP BY it_kind, it_flag
ORDER BY it_kind, it_flag;
