//! General pieces of this query that mention no query constant: `SUBSTRING(s, 1, 2)` at the byte level (`sub2`),
//! the integer threshold of a decimal comparison (`numthr`), sums reindexed over a bijection (`perm`) and dense
//! strictly increasing integer sequences (`dense`).
pub mod sub2;
pub mod numthr;
pub mod perm;
pub mod dense;
