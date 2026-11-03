-- $1 not_group text
SELECT kd_group, ow_code, COUNT(*) AS n, SUM(it_qty) AS qty
FROM ax_item
JOIN ax_kind ON it_kind = kd_code
JOIN ax_owner ON it_owner = ow_id
WHERE kd_group <> $1
GROUP BY kd_group, ow_code
ORDER BY kd_group, ow_code;
