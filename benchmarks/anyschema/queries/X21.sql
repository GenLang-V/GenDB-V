-- $1 max_seq bigint
SELECT ev_seq, it_kind, it_qty, ev_amount
FROM ax_event
JOIN ax_item ON ev_owner = it_owner AND ev_line = it_line
WHERE ev_seq <= $1
ORDER BY ev_seq;
