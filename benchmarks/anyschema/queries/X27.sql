-- $1 margin numeric(12,4)
SELECT it_owner, it_line, it_qty,
       (SELECT MAX(i2.it_qty) FROM ax_item i2) AS top_qty,
       (SELECT COUNT(*) FROM ax_event WHERE ev_owner = ax_item.it_owner AND ev_line = ax_item.it_line) AS events
FROM ax_item
WHERE it_qty > (SELECT AVG(i3.it_qty) FROM ax_item i3 WHERE i3.it_kind = ax_item.it_kind) - $1
ORDER BY it_owner, it_line;
