-- $1 group_is text
-- $2 min_qty numeric(12,4)
SELECT ow_id, ow_credit
FROM ax_owner
WHERE ow_rank = ANY (SELECT kd_weight FROM ax_kind WHERE kd_group = $1)
   OR ow_credit > ALL (SELECT it_price FROM ax_item WHERE it_owner = ow_id AND it_price IS NOT NULL AND it_qty > $2)
ORDER BY ow_id;
