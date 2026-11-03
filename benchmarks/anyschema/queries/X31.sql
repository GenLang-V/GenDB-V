-- $1 not_id bigint
-- $2 rank_below integer
SELECT DISTINCT ow_note, ow_rank
FROM ax_owner
WHERE ow_id <> $1 AND (ow_rank IS NULL OR ow_rank < $2)
ORDER BY ow_note, ow_rank;
