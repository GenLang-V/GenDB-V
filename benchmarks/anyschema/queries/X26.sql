-- $1 credit_above numeric(15,2)
-- $2 credit_below numeric(15,2)
SELECT kd_code, kd_weight
FROM ax_kind
WHERE kd_weight IN (SELECT ow_rank FROM ax_owner WHERE ow_credit > $1)
   OR kd_weight NOT IN (SELECT ow_rank FROM ax_owner WHERE ow_credit < $2)
ORDER BY kd_code;
