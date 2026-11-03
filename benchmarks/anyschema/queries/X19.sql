-- $1 from_day date
-- $2 rank_above integer
SELECT ow_id, ow_name, it_line, it_qty
FROM ax_owner, ax_item
WHERE ow_id = it_owner AND it_day >= $1 AND ow_rank > $2
ORDER BY ow_id, it_line;
