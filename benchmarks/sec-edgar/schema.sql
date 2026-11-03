CREATE TABLE sub (
    adsh text NOT NULL,
    cik integer NOT NULL,
    name text NOT NULL,
    sic integer,
    countryba text,
    stprba text,
    cityba text,
    countryinc text,
    form text NOT NULL,
    period integer,
    fy integer,
    fp text,
    filed integer NOT NULL,
    accepted text NOT NULL,
    prevrpt integer NOT NULL,
    nciks integer NOT NULL,
    afs text,
    wksi integer NOT NULL,
    fye text,
    instance text NOT NULL
);
CREATE TABLE num (
    adsh text NOT NULL,
    tag text NOT NULL,
    version text NOT NULL,
    ddate integer NOT NULL,
    qtrs integer NOT NULL,
    uom text NOT NULL,
    coreg text,
    value numeric(28,4) NOT NULL,
    footnote text
);
CREATE TABLE tag (
    tag text NOT NULL,
    version text NOT NULL,
    custom integer NOT NULL,
    abstract integer NOT NULL,
    datatype text,
    iord text NOT NULL,
    crdr text,
    tlabel text,
    doc text
);
CREATE TABLE pre (
    adsh text NOT NULL,
    report integer NOT NULL,
    line integer NOT NULL,
    stmt text,
    inpth integer NOT NULL,
    rfile text NOT NULL,
    tag text NOT NULL,
    version text NOT NULL,
    plabel text,
    negating integer NOT NULL
);
ALTER TABLE sub ADD PRIMARY KEY (adsh);
ALTER TABLE tag ADD PRIMARY KEY (tag, version);
ALTER TABLE pre ADD PRIMARY KEY (adsh, report, line);
ALTER TABLE num ADD FOREIGN KEY (adsh) REFERENCES sub (adsh);
ALTER TABLE pre ADD FOREIGN KEY (adsh) REFERENCES sub (adsh);
ALTER TABLE num ADD FOREIGN KEY (tag, version) REFERENCES tag (tag, version);
ALTER TABLE pre ADD FOREIGN KEY (tag, version) REFERENCES tag (tag, version);
