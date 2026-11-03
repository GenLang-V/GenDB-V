-- $1 rank_shift bigint
-- $2 credit_split numeric(15,2)
-- $3 below text
-- $4 above text
-- $5 rank_null integer
SELECT ow_id,
       CAST(ow_rank AS bigint) + $1 AS widened,
       CASE WHEN ow_credit < $2 THEN $3 ELSE $4 END AS side,
       COALESCE(ow_note, ow_name) AS label,
       NULLIF(ow_rank, $5) AS rank_or_null
FROM ax_owner
ORDER BY ow_id;
