CREATE TABLE t (a integer NOT NULL, b integer NOT NULL, CHECK (CASE WHEN b = 0 THEN 2 ELSE a / b END > 1));
