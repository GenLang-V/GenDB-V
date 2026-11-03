//! `ContentId`: the SHA-256 name of a stored object, written as 64 lower-case hex characters.

use serde::de::{Error as DeError, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

const HEX_DIGITS: &[u8; 16] = b"0123456789abcdef";

/// A 32-byte SHA-256 content identity. Serialized as a lower-case hex string, so identities read the same in every
/// JSON record and across languages.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ContentId([u8; 32]);

impl ContentId {
    pub const fn from_bytes(digest: [u8; 32]) -> Self {
        Self(digest)
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub fn to_hex(&self) -> String {
        let mut out = String::with_capacity(64);
        for byte in self.0 {
            out.push(HEX_DIGITS[(byte >> 4) as usize] as char);
            out.push(HEX_DIGITS[(byte & 0x0f) as usize] as char);
        }
        out
    }

    /// Parse exactly 64 lower-case hex characters (upper case is refused: one identity has one spelling).
    pub fn parse_hex(text: &str) -> Result<Self, ContentIdParseError> {
        if text.len() != 64 {
            return Err(ContentIdParseError::BadLength(text.len()));
        }
        let mut digest = [0u8; 32];
        for (slot, pair) in digest.iter_mut().zip(text.as_bytes().chunks_exact(2)) {
            *slot = (hex_digit(pair[0])? << 4) | hex_digit(pair[1])?;
        }
        Ok(Self(digest))
    }
}

fn hex_digit(byte: u8) -> Result<u8, ContentIdParseError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err(ContentIdParseError::BadDigit(byte as char)),
    }
}

impl fmt::Display for ContentId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_hex())
    }
}

impl fmt::Debug for ContentId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ContentId({})", self.to_hex())
    }
}

impl Serialize for ContentId {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_hex())
    }
}

impl<'de> Deserialize<'de> for ContentId {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct HexVisitor;
        impl Visitor<'_> for HexVisitor {
            type Value = ContentId;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a 64-character lower-case hex sha256 content id")
            }
            fn visit_str<E: DeError>(self, value: &str) -> Result<ContentId, E> {
                ContentId::parse_hex(value).map_err(E::custom)
            }
        }
        deserializer.deserialize_str(HexVisitor)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContentIdParseError {
    /// Not 64 characters long.
    BadLength(usize),
    /// A character outside `[0-9a-f]`.
    BadDigit(char),
}

impl fmt::Display for ContentIdParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadLength(len) => write!(f, "content id must be 64 hex characters, got {len}"),
            Self::BadDigit(ch) => write!(f, "content id contains non-hex character {ch:?}"),
        }
    }
}

impl std::error::Error for ContentIdParseError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex_and_serde_round_trip_and_refuse_other_spellings() {
        let id = ContentId::from_bytes(std::array::from_fn(|i| (i * 7) as u8));
        assert_eq!(ContentId::parse_hex(&id.to_hex()).unwrap(), id);
        let json = serde_json::to_string(&id).unwrap();
        assert_eq!(json, format!("\"{}\"", id.to_hex()));
        assert_eq!(serde_json::from_str::<ContentId>(&json).unwrap(), id);
        assert_eq!(ContentId::parse_hex("00"), Err(ContentIdParseError::BadLength(2)));
        assert!(ContentId::parse_hex(&id.to_hex().to_uppercase()).is_err());
    }
}
