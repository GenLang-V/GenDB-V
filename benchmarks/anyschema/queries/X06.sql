-- $1 name_pattern text
-- $2 part_start integer
SELECT ow_id, SUBSTRING(ow_name FROM $2 FOR 3) AS part
FROM ax_owner
WHERE ow_name LIKE $1
ORDER BY ow_id;
