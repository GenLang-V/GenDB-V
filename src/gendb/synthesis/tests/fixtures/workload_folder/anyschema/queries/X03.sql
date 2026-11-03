-- $1 price_shift numeric(28,4)
-- $2 min_qty numeric(12,4)
SELECT it_owner, it_line, it_qty * it_price AS amount, it_qty + it_tiny AS adjusted, it_price - $1 AS shifted
FROM ax_item
WHERE it_price IS NOT NULL AND it_qty > $2
ORDER BY it_owner, it_line;
