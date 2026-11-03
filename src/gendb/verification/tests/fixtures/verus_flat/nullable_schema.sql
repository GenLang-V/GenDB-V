CREATE TABLE filing (
    id integer NOT NULL,
    fy integer,
    big bigint,
    amount numeric(28,4),
    filed date,
    label text,
    code varchar(4),
    kind char(2),
    name text NOT NULL
);
CREATE TABLE line (
    filing integer NOT NULL,
    stmt text,
    n bigint NOT NULL
);
CREATE TABLE unit (
    code text NOT NULL,
    scale integer NOT NULL
);
ALTER TABLE filing ADD PRIMARY KEY (id);
ALTER TABLE line ADD FOREIGN KEY (filing) REFERENCES filing (id);
