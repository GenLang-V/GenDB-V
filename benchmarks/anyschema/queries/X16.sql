-- $1 min_id integer
SELECT COUNT(*) AS n, COUNT(vd_text) AS texts, SUM(vd_id) AS total, MIN(vd_text) AS low, MAX(vd_id) AS high
FROM ax_void
WHERE vd_id > $1;
