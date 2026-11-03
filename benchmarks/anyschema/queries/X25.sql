-- $1 min_qty numeric(12,4)
-- $2 before date
SELECT ow_id, ow_name
FROM ax_owner
WHERE EXISTS (SELECT 1 FROM ax_item WHERE it_owner = ow_id AND it_qty > $1)
  AND NOT EXISTS (SELECT 1 FROM ax_event WHERE ev_owner = ow_id AND ev_at < $2)
ORDER BY ow_id;
