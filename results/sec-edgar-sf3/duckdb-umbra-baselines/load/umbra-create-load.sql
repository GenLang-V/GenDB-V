ALTER ROLE postgres WITH LOGIN SUPERUSER PASSWORD 'postgres';
CREATE TABLE sub (
    adsh VARCHAR NOT NULL,
    cik INTEGER NOT NULL,
    name VARCHAR NOT NULL,
    sic INTEGER,
    countryba VARCHAR,
    stprba VARCHAR,
    cityba VARCHAR,
    countryinc VARCHAR,
    form VARCHAR NOT NULL,
    period INTEGER,
    fy INTEGER,
    fp VARCHAR,
    filed INTEGER NOT NULL,
    accepted VARCHAR NOT NULL,
    prevrpt INTEGER NOT NULL,
    nciks INTEGER NOT NULL,
    afs VARCHAR,
    wksi INTEGER NOT NULL,
    fye VARCHAR,
    instance VARCHAR NOT NULL,
    PRIMARY KEY (adsh)
);
CREATE TABLE tag (
    tag VARCHAR NOT NULL,
    version VARCHAR NOT NULL,
    custom INTEGER NOT NULL,
    abstract INTEGER NOT NULL,
    datatype VARCHAR,
    iord VARCHAR NOT NULL,
    crdr VARCHAR,
    tlabel VARCHAR,
    doc VARCHAR,
    PRIMARY KEY (tag, version)
);
CREATE TABLE num (
    adsh VARCHAR NOT NULL,
    tag VARCHAR NOT NULL,
    version VARCHAR NOT NULL,
    ddate INTEGER NOT NULL,
    qtrs INTEGER NOT NULL,
    uom VARCHAR NOT NULL,
    coreg VARCHAR,
    value NUMERIC(28,4) NOT NULL,
    footnote VARCHAR
);
CREATE TABLE pre (
    adsh VARCHAR NOT NULL,
    report INTEGER NOT NULL,
    line INTEGER NOT NULL,
    stmt VARCHAR,
    inpth INTEGER NOT NULL,
    rfile VARCHAR NOT NULL,
    tag VARCHAR NOT NULL,
    version VARCHAR NOT NULL,
    plabel VARCHAR,
    negating INTEGER NOT NULL,
    PRIMARY KEY (adsh, report, line)
);
COPY sub FROM '/data/sub.csv' WITH (FORMAT csv, DELIMITER '|', NULL '', QUOTE '"');
SELECT 'loaded' AS step, 'sub' AS tbl, COUNT(*) AS n, now() AS at FROM sub;
COPY tag FROM '/data/tag.csv' WITH (FORMAT csv, DELIMITER '|', NULL '', QUOTE '"');
SELECT 'loaded' AS step, 'tag' AS tbl, COUNT(*) AS n, now() AS at FROM tag;
COPY num FROM '/data/num.csv' WITH (FORMAT csv, DELIMITER '|', NULL '', QUOTE '"');
SELECT 'loaded' AS step, 'num' AS tbl, COUNT(*) AS n, now() AS at FROM num;
COPY pre FROM '/data/pre.csv' WITH (FORMAT csv, DELIMITER '|', NULL '', QUOTE '"');
SELECT 'loaded' AS step, 'pre' AS tbl, COUNT(*) AS n, now() AS at FROM pre;
ALTER TABLE num ADD FOREIGN KEY (adsh) REFERENCES sub (adsh);
SELECT 'constraint' AS step, 'ALTER TABLE num ADD FOREIGN KEY (adsh) REFERENCES sub (adsh)' AS what, now() AS at;
ALTER TABLE pre ADD FOREIGN KEY (adsh) REFERENCES sub (adsh);
SELECT 'constraint' AS step, 'ALTER TABLE pre ADD FOREIGN KEY (adsh) REFERENCES sub (adsh)' AS what, now() AS at;
ALTER TABLE num ADD FOREIGN KEY (tag, version) REFERENCES tag (tag, version);
SELECT 'constraint' AS step, 'ALTER TABLE num ADD FOREIGN KEY (tag, version) REFERENCES tag (tag, version)' AS what, now() AS at;
ALTER TABLE pre ADD FOREIGN KEY (tag, version) REFERENCES tag (tag, version);
SELECT 'constraint' AS step, 'ALTER TABLE pre ADD FOREIGN KEY (tag, version) REFERENCES tag (tag, version)' AS what, now() AS at;
SELECT c.relname, i.indisprimary, i.indisunique FROM pg_index i, pg_class c WHERE c.oid = i.indexrelid ORDER BY 1;
