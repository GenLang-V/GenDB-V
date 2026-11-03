SELECT id, reading
FROM sensor
WHERE day < $1;
