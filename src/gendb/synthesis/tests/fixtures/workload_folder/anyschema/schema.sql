CREATE TABLE ax_owner (
    ow_id bigint NOT NULL,
    ow_name text NOT NULL,
    ow_rank integer,
    ow_born date,
    ow_credit numeric(15,2) NOT NULL,
    ow_weight numeric(38,6),
    ow_note text,
    ow_code text NOT NULL
);
CREATE TABLE ax_kind (
    kd_code text NOT NULL,
    kd_group text NOT NULL,
    kd_weight integer
);
CREATE TABLE ax_item (
    it_owner bigint NOT NULL,
    it_line integer NOT NULL,
    it_kind text NOT NULL,
    it_qty numeric(12,4) NOT NULL,
    it_price numeric(28,4),
    it_day date NOT NULL,
    it_flag text NOT NULL,
    it_tiny numeric(3,0)
);
CREATE TABLE ax_event (
    ev_seq bigint NOT NULL,
    ev_owner bigint,
    ev_line integer,
    ev_at date,
    ev_amount numeric(18,9),
    ev_memo text
);
CREATE TABLE ax_void (
    vd_id integer NOT NULL,
    vd_text text
);
ALTER TABLE ax_owner ADD PRIMARY KEY (ow_id);
ALTER TABLE ax_kind ADD PRIMARY KEY (kd_code);
ALTER TABLE ax_item ADD PRIMARY KEY (it_owner, it_line);
ALTER TABLE ax_event ADD PRIMARY KEY (ev_seq);
ALTER TABLE ax_void ADD PRIMARY KEY (vd_id);
ALTER TABLE ax_item ADD FOREIGN KEY (it_owner) REFERENCES ax_owner (ow_id);
ALTER TABLE ax_item ADD FOREIGN KEY (it_kind) REFERENCES ax_kind (kd_code);
ALTER TABLE ax_event ADD FOREIGN KEY (ev_owner, ev_line) REFERENCES ax_item (it_owner, it_line);
