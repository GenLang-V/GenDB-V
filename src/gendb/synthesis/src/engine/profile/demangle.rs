//! Rust symbol names as readable paths, for profile reports: the legacy scheme (`_ZN<len><ident>...E`) and the v0
//! scheme (`_R...`, RFC 2603), which the Verus toolchain's `rustc` uses for engine libraries. Paths only: hashes,
//! disambiguators and lifetimes are dropped and the instantiating crate is not shown (closures read `{closure#N}`).
//! A name that does not parse is returned unchanged; nothing here decides anything.

/// The readable path of `symbol` (see the module notes), or `symbol` itself.
pub fn demangle(symbol: &str) -> String {
    let parsed = match (symbol.strip_prefix("_R").or_else(|| symbol.strip_prefix("__R")), symbol.strip_prefix("_ZN").or_else(|| symbol.strip_prefix("__ZN"))) {
        (Some(v0), _) => V0 { text: v0.as_bytes(), pos: 0, depth: 0 }.symbol(),
        (None, Some(legacy)) => legacy_path(legacy),
        (None, None) => None,
    };
    parsed.unwrap_or_else(|| symbol.to_string())
}

/// `<len><ident>...E` without the trailing `h<16 hex>` hash, each segment's `$..$` escapes and `..` decoded.
fn legacy_path(mut rest: &str) -> Option<String> {
    let mut parts = vec![];
    while !rest.starts_with('E') {
        let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
        let len: usize = rest[..digits].parse().ok()?;
        parts.push(rest.get(digits..digits + len)?);
        rest = &rest[digits + len..];
    }
    if parts.last().is_some_and(|last| last.len() == 17 && last.starts_with('h') && last[1..].bytes().all(|b| b.is_ascii_hexdigit())) {
        parts.pop();
    }
    Some(parts.iter().map(|p| unescape_legacy(p)).collect::<Vec<_>>().join("::"))
}

/// The `$LT$`, `$GT$`, `$u20$`, ... escapes and `..` (`::`) of one legacy path segment.
fn unescape_legacy(segment: &str) -> String {
    let segment = segment.strip_prefix("_$").map_or(segment.to_string(), |s| format!("${s}"));
    let mut out = String::new();
    let mut rest = segment.as_str();
    while let Some(c) = rest.chars().next() {
        if rest.starts_with("..") {
            out.push_str("::");
            rest = &rest[2..];
            continue;
        }
        if let Some((decoded, after)) = rest.strip_prefix('$').and_then(|r| r.split_once('$')).and_then(|(code, after)| Some((legacy_escape(code)?, after))) {
            out.push(decoded);
            rest = after;
            continue;
        }
        out.push(c);
        rest = &rest[c.len_utf8()..];
    }
    out
}

fn legacy_escape(code: &str) -> Option<char> {
    Some(match code {
        "SP" => '@',
        "BP" => '*',
        "RF" => '&',
        "LT" => '<',
        "GT" => '>',
        "LP" => '(',
        "RP" => ')',
        "C" => ',',
        _ => char::from_u32(u32::from_str_radix(code.strip_prefix('u')?, 16).ok()?)?,
    })
}

/// Nesting bound of the v0 parser (back references always point backwards, so parsing ends; this bounds the stack).
const MAX_DEPTH: u32 = 256;

/// A v0 symbol after its `_R` prefix; `pos` indexes `text` (back references are offsets into it).
struct V0<'a> {
    text: &'a [u8],
    pos: usize,
    depth: u32,
}

impl V0<'_> {
    /// `[<decimal version>] <path> [<instantiating crate>] [<vendor suffix>]`: the path.
    fn symbol(mut self) -> Option<String> {
        if self.peek()?.is_ascii_digit() {
            self.decimal()?;
        }
        self.path(true)
    }

    fn peek(&self) -> Option<u8> {
        self.text.get(self.pos).copied()
    }

    fn next(&mut self) -> Option<u8> {
        let b = self.peek()?;
        self.pos += 1;
        Some(b)
    }

    fn eat(&mut self, b: u8) -> bool {
        let found = self.peek() == Some(b);
        self.pos += usize::from(found);
        found
    }

    fn decimal(&mut self) -> Option<usize> {
        let start = self.pos;
        if self.eat(b'0') {
            return Some(0);
        }
        while self.peek().is_some_and(|b| b.is_ascii_digit()) {
            self.pos += 1;
        }
        std::str::from_utf8(&self.text[start..self.pos]).ok()?.parse().ok()
    }

    /// `_` is 0; `<digits>_` is the base-62 value plus 1.
    fn base62(&mut self) -> Option<u64> {
        if self.eat(b'_') {
            return Some(0);
        }
        let mut value: u64 = 0;
        loop {
            let digit = match self.next()? {
                b'_' => return value.checked_add(1),
                b @ b'0'..=b'9' => b - b'0',
                b @ b'a'..=b'z' => b - b'a' + 10,
                b @ b'A'..=b'Z' => b - b'A' + 36,
                _ => return None,
            };
            value = value.checked_mul(62)?.checked_add(u64::from(digit))?;
        }
    }

    fn disambiguator(&mut self) -> Option<u64> {
        if self.eat(b's') { self.base62() } else { Some(0) }
    }

    /// `["u"] <decimal> ["_"] <bytes>` (a punycode name, marked `u`, is shown encoded).
    fn ident(&mut self) -> Option<String> {
        self.eat(b'u');
        let len = self.decimal()?;
        self.eat(b'_');
        let bytes = self.text.get(self.pos..self.pos.checked_add(len)?)?;
        self.pos += len;
        Some(String::from_utf8_lossy(bytes).into_owned())
    }

    /// Parse with `parse` at the back reference that follows a consumed `B` (it must point before that `B`).
    fn backref(&mut self, parse: impl FnOnce(&mut Self) -> Option<String>) -> Option<String> {
        let at_b = self.pos - 1;
        let target = usize::try_from(self.base62()?).ok()?;
        if target >= at_b {
            return None;
        }
        let resume = std::mem::replace(&mut self.pos, target);
        let parsed = parse(self);
        self.pos = resume;
        parsed
    }

    fn nested(&mut self, parse: impl FnOnce(&mut Self) -> Option<String>) -> Option<String> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return None;
        }
        let parsed = parse(self);
        self.depth -= 1;
        parsed
    }

    /// A path; `value`: generic arguments print as `::<..>` (value paths) rather than `<..>` (types).
    fn path(&mut self, value: bool) -> Option<String> {
        self.nested(|s| match s.next()? {
            b'C' => {
                s.disambiguator()?;
                s.ident()
            }
            b'N' => {
                let namespace = s.next()?;
                let parent = s.path(value)?;
                let disambiguator = s.disambiguator()?;
                let name = s.ident()?;
                Some(match namespace {
                    b'C' => format!("{parent}::{{closure#{disambiguator}}}"),
                    b'S' => format!("{parent}::{{shim:{name}#{disambiguator}}}"),
                    b'A'..=b'Z' => format!("{parent}::{{{}:{name}#{disambiguator}}}", namespace as char),
                    _ => format!("{parent}::{name}"),
                })
            }
            b'M' => {
                s.disambiguator()?;
                s.path(false)?;
                Some(format!("<{}>", s.ty()?))
            }
            b'X' => {
                s.disambiguator()?;
                s.path(false)?;
                let ty = s.ty()?;
                Some(format!("<{ty} as {}>", s.path(false)?))
            }
            b'Y' => {
                let ty = s.ty()?;
                Some(format!("<{ty} as {}>", s.path(false)?))
            }
            b'I' => {
                let path = s.path(value)?;
                let args = s.generic_args()?;
                Some(format!("{path}{}<{}>", if value { "::" } else { "" }, args.join(", ")))
            }
            b'B' => s.backref(|s| s.path(value)),
            _ => None,
        })
    }

    /// Generic arguments up to `E` (lifetimes are not shown).
    fn generic_args(&mut self) -> Option<Vec<String>> {
        let mut args = vec![];
        while !self.eat(b'E') {
            if self.eat(b'L') {
                self.base62()?;
            } else if self.eat(b'K') {
                args.push(self.konst()?);
            } else {
                args.push(self.ty()?);
            }
        }
        Some(args)
    }

    fn ty(&mut self) -> Option<String> {
        self.nested(|s| {
            let tag = s.next()?;
            if let Some(basic) = basic_type(tag) {
                return Some(basic.to_string());
            }
            match tag {
                b'A' => {
                    let ty = s.ty()?;
                    Some(format!("[{ty}; {}]", s.konst()?))
                }
                b'S' => Some(format!("[{}]", s.ty()?)),
                b'T' => {
                    let mut items = vec![];
                    while !s.eat(b'E') {
                        items.push(s.ty()?);
                    }
                    Some(format!("({}{})", items.join(", "), if items.len() == 1 { "," } else { "" }))
                }
                b'R' | b'Q' => {
                    if s.eat(b'L') {
                        s.base62()?;
                    }
                    Some(format!("&{}{}", if tag == b'Q' { "mut " } else { "" }, s.ty()?))
                }
                b'P' => Some(format!("*const {}", s.ty()?)),
                b'O' => Some(format!("*mut {}", s.ty()?)),
                b'F' => s.fn_sig(),
                b'D' => s.dyn_bounds(),
                b'B' => s.backref(|s| s.ty()),
                b'C' | b'N' | b'M' | b'X' | b'Y' | b'I' => {
                    s.pos -= 1;
                    s.path(false)
                }
                _ => None,
            }
        })
    }

    /// `[G<binder>] [U] [K<abi>] {type} E <return type>`.
    fn fn_sig(&mut self) -> Option<String> {
        if self.eat(b'G') {
            self.base62()?;
        }
        let unsafe_fn = self.eat(b'U');
        let abi = match self.eat(b'K') {
            true if self.eat(b'C') => Some("C".to_string()),
            true => Some(self.ident()?.replace('_', "-")),
            false => None,
        };
        let mut params = vec![];
        while !self.eat(b'E') {
            params.push(self.ty()?);
        }
        let ret = self.ty()?;
        Some(format!(
            "{}{}fn({}){}",
            if unsafe_fn { "unsafe " } else { "" },
            abi.map(|a| format!("extern \"{a}\" ")).unwrap_or_default(),
            params.join(", "),
            if ret == "()" { String::new() } else { format!(" -> {ret}") }
        ))
    }

    /// `[G<binder>] {<trait path> {p <name> <type>}} E L<lifetime>`.
    fn dyn_bounds(&mut self) -> Option<String> {
        if self.eat(b'G') {
            self.base62()?;
        }
        let mut traits = vec![];
        while !self.eat(b'E') {
            let mut bound = self.path(false)?;
            let mut bindings = vec![];
            while self.eat(b'p') {
                let name = self.ident()?;
                bindings.push(format!("{name} = {}", self.ty()?));
            }
            if !bindings.is_empty() {
                bound = format!("{bound}<{}>", bindings.join(", "));
            }
            traits.push(bound);
        }
        if !self.eat(b'L') {
            return None;
        }
        self.base62()?;
        Some(format!("dyn {}", traits.join(" + ")))
    }

    /// A constant generic argument: `p` (placeholder), a back reference, or an integer, `bool` or `char` value
    /// (`<type> [n] <hex> _`). Other constants are not parsed.
    fn konst(&mut self) -> Option<String> {
        if self.eat(b'p') {
            return Some("_".into());
        }
        if self.eat(b'B') {
            return self.backref(|s| s.konst());
        }
        let ty = self.next()?;
        if !b"abchijlmnostxy".contains(&ty) {
            return None;
        }
        let negative = self.eat(b'n');
        let start = self.pos;
        while self.peek()? != b'_' {
            if !self.next()?.is_ascii_hexdigit() {
                return None;
            }
        }
        let hex = std::str::from_utf8(&self.text[start..self.pos]).ok()?;
        self.pos += 1;
        let value = if hex.is_empty() { 0 } else { u128::from_str_radix(hex, 16).ok()? };
        Some(match ty {
            b'b' => (value != 0).to_string(),
            b'c' => format!("{:?}", char::from_u32(u32::try_from(value).ok()?)?),
            _ => format!("{}{value}", if negative { "-" } else { "" }),
        })
    }
}

/// The v0 basic types.
fn basic_type(tag: u8) -> Option<&'static str> {
    Some(match tag {
        b'a' => "i8",
        b'b' => "bool",
        b'c' => "char",
        b'd' => "f64",
        b'e' => "str",
        b'f' => "f32",
        b'h' => "u8",
        b'i' => "isize",
        b'j' => "usize",
        b'l' => "i32",
        b'm' => "u32",
        b'n' => "i128",
        b'o' => "u128",
        b'p' => "_",
        b's' => "i16",
        b't' => "u16",
        b'u' => "()",
        b'v' => "...",
        b'x' => "i64",
        b'y' => "u64",
        b'z' => "!",
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::demangle;

    /// Names taken from a compiled engine library (v0) and the legacy scheme.
    #[test]
    fn engine_symbols_read_as_paths() {
        let cases = [
            ("_RNvNtNtNtCseiCpEFsCofR_12gendb_engine4exec10relational4rows9clone_row", "gendb_engine::exec::relational::rows::clone_row"),
            ("_RNvNtNtNtCseiCpEFsCofR_12gendb_engine4exec10relational3ops17product_rows_exec", "gendb_engine::exec::relational::ops::product_rows_exec"),
            ("_RNvMs5_NtCs6i54tJFfzR_5alloc7raw_vecNtB5_11RawVecInner15try_allocate_inCsepY7R6AGWjB_5gimli", "<alloc::raw_vec::RawVecInner>::try_allocate_in"),
            ("_RNvCs1njKG4L9aB3_7___rustc11___rdl_alloc", "__rustc::__rdl_alloc"),
            ("_RINvNtCs1_4core3mem4swapjEB4_", "core::mem::swap::<usize>"),
            ("_RNvXs_NtCs1_5alloc3vecINtB4_3VecpENtNtCs2_4core5clone5Clone5clone", "<alloc::vec::Vec<_> as core::clone::Clone>::clone"),
            ("_RNCNvCs1_4main4main0", "main::main::{closure#0}"),
            ("_ZN12gendb_engine4exec10relational3ops17product_rows_exec17h0123456789abcdefE", "gendb_engine::exec::relational::ops::product_rows_exec"),
            ("_ZN67_$LT$alloc..vec..Vec$LT$T$C$A$GT$$u20$as$u20$core..clone..Clone$GT$5clone17h0123456789abcdefE", "<alloc::vec::Vec<T,A> as core::clone::Clone>::clone"),
            ("malloc", "malloc"),
            ("_ZN3bad", "_ZN3bad"),
            ("_RNvB9_1x", "_RNvB9_1x"),
        ];
        for (symbol, path) in cases {
            assert_eq!(demangle(symbol), path, "{symbol}");
        }
    }
}
