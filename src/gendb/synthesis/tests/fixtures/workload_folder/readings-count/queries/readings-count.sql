-- $1 k bigint
SELECT COUNT(*) AS n FROM readings WHERE value > $1;
