-- VERUS_SQL_COVERAGE task C: constraint fixture schema (PostgreSQL 18 DDL; every constraint is enforced by
-- PostgreSQL and recorded/checked by the Verus semantics).
CREATE TABLE pk2 (a integer, b integer, v integer, PRIMARY KEY (a, b));
CREATE TABLE uq (id integer PRIMARY KEY, x integer, y integer, UNIQUE (x, y));
CREATE TABLE uqn (id integer PRIMARY KEY, x integer, y integer, UNIQUE NULLS NOT DISTINCT (x, y));
CREATE TABLE fks (id integer PRIMARY KEY, x integer, y integer, FOREIGN KEY (x, y) REFERENCES pk2 (a, b));
CREATE TABLE fkf (id integer PRIMARY KEY, x integer, y integer,
                  CONSTRAINT fkf_full FOREIGN KEY (y, x) REFERENCES pk2 (b, a) MATCH FULL ON DELETE CASCADE);
CREATE TABLE ck (id integer PRIMARY KEY, a integer CHECK (a > 0), b integer, c numeric(6,2),
                 CONSTRAINT ck_div CHECK (10 / b > 1),
                 CONSTRAINT ck_case CHECK (CASE WHEN c IS NULL THEN 0 ELSE c END < 100));
CREATE TABLE emp (id integer PRIMARY KEY, boss integer REFERENCES emp DEFERRABLE INITIALLY DEFERRED);
CREATE TABLE pkn (k numeric(6,2) PRIMARY KEY);
CREATE TABLE fkn (id integer PRIMARY KEY, k bigint REFERENCES pkn);
CREATE TABLE pkv (s varchar(5) PRIMARY KEY);
CREATE TABLE fkb (id integer PRIMARY KEY, s char(5) REFERENCES pkv (s));
CREATE TABLE pkd (d date PRIMARY KEY);
CREATE TABLE fkt (id integer PRIMARY KEY, t timestamp REFERENCES pkd);
CREATE TABLE cap (id integer PRIMARY KEY, c numeric(6,2) CHECK (c * c * c * c * c * c * c * c * c * c >= 0));
