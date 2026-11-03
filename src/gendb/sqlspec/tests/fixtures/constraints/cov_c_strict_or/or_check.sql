CREATE TABLE t (a integer NOT NULL, b integer NOT NULL, CHECK (b = 0 OR a / b > 1));
