CREATE TABLE site (
    code char(3) NOT NULL,
    region integer NOT NULL
);
CREATE TABLE sensor (
    id integer NOT NULL,
    site integer NOT NULL,
    reading numeric(10,2) NOT NULL,
    day date NOT NULL,
    tag varchar(8) NOT NULL,
    note text
);
