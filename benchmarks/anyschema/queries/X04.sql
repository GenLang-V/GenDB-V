-- $1 rank_divisor integer
-- $2 credit_divisor numeric(15,2)
SELECT ow_id, ow_rank / $1 AS whole_quotient, ow_credit / $2 AS quotient
FROM ax_owner
WHERE ow_rank IS NOT NULL
ORDER BY ow_id;
