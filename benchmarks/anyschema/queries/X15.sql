-- $1 qty_split numeric(12,4)
-- $2 high text
-- $3 low text
SELECT CASE WHEN it_qty >= $1 THEN $2 ELSE $3 END AS band, COUNT(*) AS n, SUM(it_qty) AS qty
FROM ax_item
GROUP BY CASE WHEN it_qty >= $1 THEN $2 ELSE $3 END
ORDER BY band;
