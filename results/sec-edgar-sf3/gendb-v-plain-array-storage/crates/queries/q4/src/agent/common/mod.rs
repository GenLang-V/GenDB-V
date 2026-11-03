//! General building blocks (no query constants): hashing of byte strings, a static chained hash index, no_unwind text access.
pub mod hash;
pub mod chains;
pub mod text;
pub mod buf;
pub mod grow;
pub mod distinct;
pub mod select;
