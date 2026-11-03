-- $1 from_day date
SELECT it_owner, it_line, it_day
FROM ax_item
WHERE it_day >= $1 AND it_day < $1 + INTERVAL '1' YEAR
ORDER BY it_day, it_owner, it_line;
