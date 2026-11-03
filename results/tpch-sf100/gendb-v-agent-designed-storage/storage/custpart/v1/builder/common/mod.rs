//! Generic builder pieces: code widths, dictionaries, value sources, frame-of-reference encoding, permutation
//! checks, clustering orders, text copies and the assembly of encoded columns into parts.
pub mod codes;
pub mod dict;
pub mod colsrc;
pub mod forenc;
pub mod perm;
pub mod cluster;
pub mod textcopy;
pub mod assemble;
pub mod keyed;
