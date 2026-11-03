-- $1 rank_above integer
SELECT ow_id, ow_rank, ow_note
FROM ax_owner
WHERE (ow_rank IS NULL OR ow_rank > $1) AND ow_note IS NOT NULL
ORDER BY ow_id;
