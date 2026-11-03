-- $1 min_id bigint
-- $2 min_credit numeric(15,2)
-- $3 born_before date
-- $4 not_name text
SELECT ow_id, ow_name, ow_rank, ow_born, ow_credit
FROM ax_owner
WHERE ow_id > $1 AND ow_credit >= $2 AND ow_born < $3 AND ow_name <> $4
ORDER BY ow_id;
