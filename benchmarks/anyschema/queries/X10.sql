-- $1 weight_above numeric(38,6)
-- $2 weight_below numeric(38,6)
SELECT ow_id, ow_weight
FROM ax_owner
WHERE ow_weight > $1 OR ow_weight < $2
ORDER BY ow_weight DESC, ow_id
LIMIT 20;
