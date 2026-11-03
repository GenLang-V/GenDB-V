//! General pieces of the query (no query constants, no storage layout): `LIKE '%s1%...%sk%'` as ordered byte
//! segments with a greedy matcher, a windowed literal search, a matching-rows kernel over a text column, GROUP BY
//! over blocks with one key each, even range splits and zero-filled vectors.
pub mod find;
pub mod groups;
pub mod segments;
pub mod split;
pub mod text_rows;
pub mod zeroed;
