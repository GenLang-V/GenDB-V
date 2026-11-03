-- $1 min_seq bigint
SELECT ev_memo, ev_at, COUNT(*) AS n, COUNT(ev_amount) AS amounts, SUM(ev_amount) AS total
FROM ax_event
WHERE ev_seq >= $1
GROUP BY ev_memo, ev_at
ORDER BY ev_at DESC
LIMIT 10;
