SELECT id + $3 AS shifted, reading, tag
FROM sensor
WHERE reading >= $1 AND day < $2;
