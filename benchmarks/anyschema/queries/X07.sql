-- $1 code_from text
-- $2 code_to text
-- $3 name_is text
SELECT ow_id, ow_code, ow_name
FROM ax_owner
WHERE ow_code >= $1 AND ow_code < $2 OR ow_name = $3
ORDER BY ow_code, ow_id;
