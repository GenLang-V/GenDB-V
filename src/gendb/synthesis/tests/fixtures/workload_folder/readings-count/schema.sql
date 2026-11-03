CREATE TABLE readings (
    value bigint NOT NULL
);
ALTER TABLE readings ADD CONSTRAINT value_nonnegative CHECK (value >= 0);
