# Example: one query, end to end

One small query with its whole path in GenDB-V: the SQL template, the statement it means in SQLSpec, the agent's verified code, and the complete crate that Verus checked.

```sql
SELECT COUNT(*) AS n FROM readings WHERE value > $1;
```

| | |
|---|---|
| Schema | [`schema.sql`](schema.sql): one table `readings`, one column `value bigint NOT NULL`, and the declared constraint `CHECK (value >= 0)` |
| Data | 4 rows, `value` = 5, 5, 9, 0, in this order: [`data/readings.parquet`](data/readings.parquet), written by [`data/make_data.py`](data/make_data.py) |
| Parameter | `$1`, bigint, every value of the type |
| Statement in SQLSpec | [`spec.rs`](spec.rs), emitted from [`query.sql`](query.sql) |
| Code | [`code/`](code/): `mod.rs` (the query and its loop proof) and `normal_form.rs` (the link to the SQL meaning) |
| Complete crate | [`crates/example-readings-count/`](crates/example-readings-count/README.md) |

Verus verified the complete crate (916 verified, 0 errors); at `$1 = 4` the query returns `[[3]]`.

What a verified query guarantees, and what it trusts: [What is proved, and what is trusted](../../GUIDE.md#what-is-proved-and-what-is-trusted).
