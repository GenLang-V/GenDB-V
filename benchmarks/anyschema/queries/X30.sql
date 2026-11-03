-- $1 from_day date
SELECT it_kind, SUM(it_qty) AS qty
FROM ax_item
GROUP BY it_kind
HAVING SUM(it_qty) > (SELECT AVG(k.qty) FROM (SELECT SUM(it_qty) AS qty FROM ax_item WHERE it_day >= $1 GROUP BY it_kind) k)
ORDER BY it_kind;
