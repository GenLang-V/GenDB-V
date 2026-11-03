-- $1 min_items bigint
WITH totals AS (
    SELECT it_owner, SUM(it_qty) AS qty, COUNT(*) AS n
    FROM ax_item
    GROUP BY it_owner
)
SELECT ow_id, ow_name, t.qty, t.n
FROM ax_owner
JOIN (SELECT it_owner, qty, n FROM totals WHERE n >= $1) t ON t.it_owner = ow_id
ORDER BY t.qty DESC, ow_id
LIMIT 25;
