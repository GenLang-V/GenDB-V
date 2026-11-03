-- $1 min_qty numeric(12,4)
SELECT COUNT(*) AS n, SUM(it_qty) AS qty, AVG(it_price) AS mean_price, MAX(it_day) AS last_day
FROM ax_item
WHERE it_qty > $1;
