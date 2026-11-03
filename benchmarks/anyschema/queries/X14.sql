-- $1 min_items bigint
SELECT it_owner, MIN(it_kind) AS first_kind, MAX(it_kind) AS last_kind, MIN(it_day) AS first_day, MAX(it_qty) AS most,
       COUNT(*) AS n
FROM ax_item
GROUP BY it_owner
HAVING COUNT(*) >= $1
ORDER BY it_owner;
