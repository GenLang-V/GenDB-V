-- $1 from_day date
SELECT ow_id, ow_name
FROM ax_owner
LEFT JOIN ax_item ON it_owner = ow_id AND it_day >= $1
WHERE it_owner IS NULL
ORDER BY ow_id;
