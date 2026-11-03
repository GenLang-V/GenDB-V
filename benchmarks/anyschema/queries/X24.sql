-- $1 max_id bigint
SELECT ow_id, ow_rank, vd_text
FROM ax_owner
LEFT JOIN ax_void ON vd_id = ow_rank
WHERE ow_id < $1
ORDER BY ow_id;
