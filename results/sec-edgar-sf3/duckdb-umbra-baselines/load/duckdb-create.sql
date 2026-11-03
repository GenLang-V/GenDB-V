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
    value DECIMAL(28,4) NOT NULL,
    footnote VARCHAR,
    FOREIGN KEY (adsh) REFERENCES sub (adsh),
    FOREIGN KEY (tag, version) REFERENCES tag (tag, version)
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
    PRIMARY KEY (adsh, report, line),
    FOREIGN KEY (adsh) REFERENCES sub (adsh),
    FOREIGN KEY (tag, version) REFERENCES tag (tag, version)
);
