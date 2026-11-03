//! Canonical JSON and content identity: the one byte encoding every stored record uses.
//!
//! Canonical form, defined only here:
//! * object keys appear once each, sorted by byte order;
//! * no insignificant whitespace;
//! * arrays keep their order, so array order is content (an owner normalizes any list whose order is not semantic);
//! * floating-point numbers are refused, because a float makes an identity platform dependent;
//! * integers keep their exact token, so the full `i128` range survives (`serde_json::Value` would turn an integer
//!   outside `i64`/`u64` into a lossy float, so this module parses serializer output itself).
//!
//! A stored object is the canonical envelope `{"format_version":<u32>,"kind":"<tag>","payload":<value>}` and its
//! identity is the SHA-256 of exactly those bytes. `kind` separates domains: equal payloads of different kinds get
//! different identities. The byte format is shared with every saved library; changing it would rename every record.

use crate::content_id::ContentId;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fmt;

#[derive(Debug)]
pub enum CanonError {
    /// The value could not be serialized to JSON at all.
    Serialize(serde_json::Error),
    /// A float at this JSON path; identity-bearing records may not contain floats.
    FloatNotAllowed { path: String },
    /// The bytes are not well-formed JSON (reachable only through malformed custom serializers or stored bytes).
    InvalidJson(String),
}

impl fmt::Display for CanonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Serialize(error) => write!(f, "canonical serialization failed: {error}"),
            Self::FloatNotAllowed { path } => write!(f, "float at {path} is not allowed in an identity-bearing structure"),
            Self::InvalidJson(detail) => write!(f, "canonical JSON parser refused: {detail}"),
        }
    }
}

impl std::error::Error for CanonError {}

/// Content identity of `payload` stored as a `kind` object of `format_version`.
pub fn content_id<T: Serialize>(format_version: u32, kind: &str, payload: &T) -> Result<ContentId, CanonError> {
    let envelope = canonical_envelope(format_version, kind, payload)?;
    Ok(sha256(envelope.as_bytes()))
}

pub(crate) fn sha256(bytes: &[u8]) -> ContentId {
    ContentId::from_bytes(Sha256::digest(bytes).into())
}

/// Canonical bytes of the versioned envelope around `payload`.
pub fn canonical_envelope<T: Serialize>(format_version: u32, kind: &str, payload: &T) -> Result<String, CanonError> {
    let payload = canonical_document(payload)?;
    let mut out = String::from(r#"{"format_version":"#);
    out.push_str(&format_version.to_string());
    out.push_str(r#","kind":"#);
    write_json_string(kind, &mut out);
    out.push_str(r#","payload":"#);
    out.push_str(&payload);
    out.push('}');
    Ok(out)
}

/// Canonical bytes of a value without an envelope (derived index files), under the same rules.
pub(crate) fn canonical_document<T: Serialize>(value: &T) -> Result<String, CanonError> {
    let bytes = serde_json::to_vec(value).map_err(CanonError::Serialize)?;
    let mut out = String::new();
    write_canonical(&JsonParser::parse(&bytes)?, "$", &mut out)?;
    Ok(out)
}

/// The fields of a stored envelope whose bytes are exactly canonical.
pub(crate) struct Envelope {
    pub format_version: u32,
    pub kind: String,
    pub canonical_payload: String,
}

pub(crate) enum EnvelopeError {
    Canonical(CanonError),
    /// Well-formed JSON, but not an envelope.
    Invalid(String),
    /// A valid envelope whose bytes are not its canonical form.
    NotCanonical,
}

impl From<CanonError> for EnvelopeError {
    fn from(error: CanonError) -> Self {
        Self::Canonical(error)
    }
}

/// Parse stored object bytes: exactly the keys `format_version` (u32), `kind` (non-empty string) and `payload`, with
/// the bytes equal to their canonical form. Checks run in this order so a malformed envelope is reported as such
/// before any canonical-form difference.
pub(crate) fn parse_envelope(bytes: &[u8]) -> Result<Envelope, EnvelopeError> {
    let parsed = JsonParser::parse(bytes)?;
    let Json::Object(fields) = &parsed else {
        return Err(EnvelopeError::Invalid("object envelope is not an object".into()));
    };
    let (Some(version), Some(kind), Some(payload), 3) =
        (fields.get("format_version"), fields.get("kind"), fields.get("payload"), fields.len())
    else {
        return Err(EnvelopeError::Invalid("object envelope must contain exactly format_version, kind, payload".into()));
    };
    let format_version = match version {
        Json::Number(digits) if digits.bytes().all(|b| b.is_ascii_digit()) => digits
            .parse::<u32>()
            .map_err(|error| EnvelopeError::Invalid(format!("invalid format_version: {error}")))?,
        _ => return Err(EnvelopeError::Invalid("format_version must be a u32".into())),
    };
    let kind = match kind {
        Json::String(kind) if !kind.is_empty() => kind.clone(),
        _ => return Err(EnvelopeError::Invalid("kind must be a non-empty string".into())),
    };
    let mut canonical_payload = String::new();
    write_canonical(payload, "$.payload", &mut canonical_payload)?;
    let mut canonical = String::new();
    write_canonical(&parsed, "$", &mut canonical)?;
    if canonical.as_bytes() != bytes {
        return Err(EnvelopeError::NotCanonical);
    }
    Ok(Envelope { format_version, kind, canonical_payload })
}

/// A JSON tree that keeps each number's exact token.
enum Json {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}

fn write_canonical(value: &Json, path: &str, out: &mut String) -> Result<(), CanonError> {
    match value {
        Json::Null => out.push_str("null"),
        Json::Bool(true) => out.push_str("true"),
        Json::Bool(false) => out.push_str("false"),
        Json::Number(token) => {
            if token.contains(['.', 'e', 'E']) {
                return Err(CanonError::FloatNotAllowed { path: path.to_string() });
            }
            out.push_str(token);
        }
        Json::String(text) => write_json_string(text, out),
        Json::Array(items) => {
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_canonical(item, &format!("{path}[{index}]"), out)?;
            }
            out.push(']');
        }
        // BTreeMap iteration is byte-order sorted.
        Json::Object(fields) => {
            out.push('{');
            for (index, (key, value)) in fields.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_json_string(key, out);
                out.push(':');
                write_canonical(value, &format!("{path}.{key}"), out)?;
            }
            out.push('}');
        }
    }
    Ok(())
}

/// Strings use `serde_json`'s escaping, so a string's canonical spelling is the serializer's.
pub(crate) fn write_json_string(text: &str, out: &mut String) {
    out.push_str(&serde_json::to_string(text).expect("string encoding is infallible"));
}

/// A small strict JSON parser: duplicate keys, control bytes in strings and trailing bytes are refused.
struct JsonParser<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> JsonParser<'a> {
    fn parse(bytes: &'a [u8]) -> Result<Json, CanonError> {
        let mut parser = Self { bytes, at: 0 };
        let value = parser.value()?;
        parser.skip_whitespace();
        if parser.at != bytes.len() {
            return Err(parser.error("trailing bytes"));
        }
        Ok(value)
    }

    fn value(&mut self) -> Result<Json, CanonError> {
        self.skip_whitespace();
        match self.peek() {
            Some(b'n') => self.keyword(b"null").map(|()| Json::Null),
            Some(b't') => self.keyword(b"true").map(|()| Json::Bool(true)),
            Some(b'f') => self.keyword(b"false").map(|()| Json::Bool(false)),
            Some(b'"') => self.string().map(Json::String),
            Some(b'[') => self.array(),
            Some(b'{') => self.object(),
            Some(b'-' | b'0'..=b'9') => self.number(),
            _ => Err(self.error("expected JSON value")),
        }
    }

    fn array(&mut self) -> Result<Json, CanonError> {
        self.expect(b'[')?;
        self.skip_whitespace();
        let mut items = Vec::new();
        if self.peek() == Some(b']') {
            self.at += 1;
            return Ok(Json::Array(items));
        }
        loop {
            items.push(self.value()?);
            self.skip_whitespace();
            match self.next() {
                Some(b',') => self.skip_whitespace(),
                Some(b']') => return Ok(Json::Array(items)),
                _ => return Err(self.error("expected `,` or `]` in array")),
            }
        }
    }

    fn object(&mut self) -> Result<Json, CanonError> {
        self.expect(b'{')?;
        self.skip_whitespace();
        let mut fields = BTreeMap::new();
        if self.peek() == Some(b'}') {
            self.at += 1;
            return Ok(Json::Object(fields));
        }
        loop {
            if self.peek() != Some(b'"') {
                return Err(self.error("object key is not a string"));
            }
            let key = self.string()?;
            self.skip_whitespace();
            self.expect(b':')?;
            let value = self.value()?;
            if fields.insert(key, value).is_some() {
                return Err(self.error("duplicate object key"));
            }
            self.skip_whitespace();
            match self.next() {
                Some(b',') => self.skip_whitespace(),
                Some(b'}') => return Ok(Json::Object(fields)),
                _ => return Err(self.error("expected `,` or `}` in object")),
            }
        }
    }

    /// Finds the string's extent, then lets `serde_json` decode its escapes.
    fn string(&mut self) -> Result<String, CanonError> {
        let start = self.at;
        self.expect(b'"')?;
        loop {
            match self.next() {
                None => return Err(self.error("unterminated string")),
                Some(b'"') => break,
                Some(b'\\') => {
                    if self.next().is_none() {
                        return Err(self.error("unterminated string escape"));
                    }
                }
                Some(0..=0x1f) => return Err(self.error("control byte in string")),
                Some(_) => {}
            }
        }
        serde_json::from_slice(&self.bytes[start..self.at]).map_err(|error| CanonError::InvalidJson(error.to_string()))
    }

    /// Keeps the token text; `write_canonical` decides whether it is an integer.
    fn number(&mut self) -> Result<Json, CanonError> {
        let start = self.at;
        while self.peek().is_some_and(|b| !matches!(b, b',' | b']' | b'}' | b' ' | b'\n' | b'\r' | b'\t')) {
            self.at += 1;
        }
        let token = std::str::from_utf8(&self.bytes[start..self.at]).map_err(|_| self.error("number is not UTF-8"))?;
        if token.is_empty() || !token.bytes().all(|b| matches!(b, b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9')) {
            return Err(self.error("invalid number token"));
        }
        Ok(Json::Number(token.to_string()))
    }

    fn keyword(&mut self, expected: &[u8]) -> Result<(), CanonError> {
        if self.bytes.get(self.at..self.at + expected.len()) == Some(expected) {
            self.at += expected.len();
            Ok(())
        } else {
            Err(self.error("invalid keyword"))
        }
    }

    fn expect(&mut self, expected: u8) -> Result<(), CanonError> {
        if self.next() == Some(expected) { Ok(()) } else { Err(self.error("unexpected byte")) }
    }

    fn skip_whitespace(&mut self) {
        while self.peek().is_some_and(|b| matches!(b, b' ' | b'\n' | b'\r' | b'\t')) {
            self.at += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.at).copied()
    }

    fn next(&mut self) -> Option<u8> {
        let byte = self.peek()?;
        self.at += 1;
        Some(byte)
    }

    fn error(&self, detail: &str) -> CanonError {
        CanonError::InvalidJson(format!("{detail} at byte {}", self.at))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Known-answer vector carried unchanged from the earlier GenDB version: canonical bytes and identity of saved records depend on it.
    #[test]
    fn known_answer_vector() {
        let value = serde_json::json!({"b": [1, -2], "a": {"z": "x\"y", "": null}});
        assert_eq!(
            canonical_envelope(1, "gendb.m30.kat", &value).unwrap(),
            r#"{"format_version":1,"kind":"gendb.m30.kat","payload":{"a":{"":null,"z":"x\"y"},"b":[1,-2]}}"#
        );
        assert_eq!(
            content_id(1, "gendb.m30.kat", &value).unwrap().to_hex(),
            "c6eb259e741f4099ba198c1192086040103fa3bef6e4f9d5cc6cc8e679cb48e5"
        );
    }

    #[test]
    fn i128_min_is_kept_exactly() {
        #[derive(Serialize)]
        struct Boundary {
            value: i128,
        }
        assert_eq!(
            canonical_envelope(1, "test", &Boundary { value: i128::MIN }).unwrap(),
            r#"{"format_version":1,"kind":"test","payload":{"value":-170141183460469231731687303715884105728}}"#
        );
    }

    #[test]
    fn floats_are_refused_and_kind_and_version_separate_identities() {
        let err = content_id(1, "test", &serde_json::json!({"ratio": 1.35})).unwrap_err();
        assert!(matches!(err, CanonError::FloatNotAllowed { path } if path == "$.ratio"));
        let value = serde_json::json!({"same": "payload"});
        assert_ne!(content_id(1, "a", &value).unwrap(), content_id(1, "b", &value).unwrap());
        assert_ne!(content_id(1, "a", &value).unwrap(), content_id(2, "a", &value).unwrap());
    }

    #[test]
    fn stored_envelopes_must_be_exactly_canonical() {
        let canonical = canonical_envelope(1, "k", &serde_json::json!({"b": 1, "a": [2, 1]})).unwrap();
        let envelope = parse_envelope(canonical.as_bytes()).ok().unwrap();
        assert_eq!((envelope.format_version, envelope.kind.as_str()), (1, "k"));
        assert_eq!(envelope.canonical_payload, r#"{"a":[2,1],"b":1}"#);
        let spaced = canonical.replace(":1", ": 1");
        assert!(matches!(parse_envelope(spaced.as_bytes()), Err(EnvelopeError::NotCanonical)));
        assert!(matches!(parse_envelope(br#"{"kind":"k","payload":1}"#), Err(EnvelopeError::Invalid(_))));
    }
}
