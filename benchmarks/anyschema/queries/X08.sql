-- $1 min_day integer
SELECT EXTRACT(YEAR FROM it_day) AS y, EXTRACT(MONTH FROM it_day) AS m, COUNT(*) AS n
FROM ax_item
WHERE EXTRACT(DAY FROM it_day) >= $1
GROUP BY EXTRACT(YEAR FROM it_day), EXTRACT(MONTH FROM it_day)
ORDER BY y, m;
