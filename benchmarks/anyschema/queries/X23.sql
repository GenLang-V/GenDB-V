-- $1 flag text
SELECT kd_code, COUNT(it_line) AS items, SUM(it_qty) AS qty
FROM ax_kind
LEFT JOIN ax_item ON it_kind = kd_code AND it_flag = $1
GROUP BY kd_code
ORDER BY kd_code;
