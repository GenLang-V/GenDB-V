//! Rust token stream for the refusal scan: identifiers, punctuation, two-character operators and opaque literals.
//!
//! Comments are dropped, and string, char and numeric literals become [`Tok::Literal`], so text inside them can
//! never trigger a refusal rule. This is not a Rust parser: it only needs to find identifiers, attributes and
//! delimiter groups reliably. Lines are 1-based. Its one user is the refusal scan (`super::refusal`), which the
//! composition rule reaches through `verus::scan_source`. Each token also carries its source span, so the engine rules
//! (`refusal::engine_rules`) can read a literal's text; no other rule looks at it.

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Tok {
    Ident(String),
    Punct(char),
    /// `::`, `!=` and the other two-character operators, so that `!=` is never mistaken for a macro `!`.
    Op(&'static str),
    Literal,
}

#[derive(Clone, Debug)]
pub(crate) struct Token {
    pub tok: Tok,
    pub line: usize,
    /// Character positions (not bytes) of the token in the lexed text.
    pub span: std::ops::Range<usize>,
}

impl Token {
    pub fn ident(&self) -> Option<&str> {
        match &self.tok {
            Tok::Ident(name) => Some(name),
            _ => None,
        }
    }

    pub fn is_punct(&self, ch: char) -> bool {
        self.tok == Tok::Punct(ch)
    }

    fn opens_group(&self) -> bool {
        matches!(self.tok, Tok::Punct('(' | '[' | '{'))
    }

    fn closes_group(&self) -> bool {
        matches!(self.tok, Tok::Punct(')' | ']' | '}'))
    }
}

/// Source that cannot be tokenized (an unterminated comment or literal), at the line where it starts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LexError {
    pub line: usize,
    pub message: &'static str,
}

const TWO_CHARACTER_OPERATORS: [&str; 20] =
    ["::", "!=", "==", "<=", ">=", "&&", "||", "=>", "->", "..", "+=", "-=", "*=", "/=", "%=", "^=", "&=", "|=", "<<", ">>"];

pub(crate) fn lex(text: &str) -> Result<Vec<Token>, LexError> {
    let mut lexer = Lexer { chars: text.chars().collect(), pos: 0, line: 1, tokens: Vec::new() };
    while lexer.pos < lexer.chars.len() {
        lexer.next_token()?;
    }
    Ok(lexer.tokens)
}

/// Index just past the delimiter group that opens at `open` (a `(`, `[` or `{`); the end of `tokens` if unclosed.
pub(crate) fn group_end(tokens: &[Token], open: usize) -> usize {
    let mut depth = 0i64;
    for (i, token) in tokens.iter().enumerate().skip(open) {
        if token.opens_group() {
            depth += 1;
        } else if token.closes_group() {
            depth -= 1;
            if depth == 0 {
                return i + 1;
            }
        }
    }
    tokens.len()
}

struct Lexer {
    chars: Vec<char>,
    pos: usize,
    line: usize,
    tokens: Vec<Token>,
}

impl Lexer {
    fn peek(&self, offset: usize) -> Option<char> {
        self.chars.get(self.pos + offset).copied()
    }

    /// Pushes a token; [`Self::next_token`] sets its span once the token is consumed.
    fn push(&mut self, tok: Tok, line: usize) {
        self.tokens.push(Token { tok, line, span: 0..0 });
    }

    /// Consumes whitespace, one comment or one token starting at `pos`, and records the token's span.
    fn next_token(&mut self) -> Result<(), LexError> {
        let (start, before) = (self.pos, self.tokens.len());
        self.consume()?;
        if self.tokens.len() > before {
            self.tokens.last_mut().expect("a token was pushed").span = start..self.pos;
        }
        Ok(())
    }

    /// The body of [`Self::next_token`]: at most one token is pushed.
    fn consume(&mut self) -> Result<(), LexError> {
        let ch = self.chars[self.pos];
        let next = self.peek(1);
        if ch == '\n' {
            self.line += 1;
            self.pos += 1;
        } else if ch.is_whitespace() {
            self.pos += 1;
        } else if ch == '/' && next == Some('/') {
            self.skip_line_comment();
        } else if ch == '/' && next == Some('*') {
            self.skip_block_comment()?;
        } else if let Some(end) = raw_string_end(&self.chars, self.pos) {
            self.raw_string(end);
        } else if ch == '"' || (matches!(ch, 'b' | 'c') && next == Some('"')) {
            self.string_literal()?;
        } else if ch == '\'' || (ch == 'b' && next == Some('\'')) {
            self.char_literal_or_lifetime()?;
        } else if ch == '_' || ch.is_alphabetic() {
            self.identifier();
        } else if ch.is_ascii_digit() {
            self.number();
        } else {
            self.operator_or_punct();
        }
        Ok(())
    }

    /// Up to, not including, the newline.
    fn skip_line_comment(&mut self) {
        while self.pos < self.chars.len() && self.chars[self.pos] != '\n' {
            self.pos += 1;
        }
    }

    /// Block comments nest, as in Rust.
    fn skip_block_comment(&mut self) -> Result<(), LexError> {
        let start = self.line;
        let mut depth = 0usize;
        loop {
            match (self.peek(0), self.peek(1)) {
                (None, _) => return Err(LexError { line: start, message: "unterminated block comment" }),
                (Some('/'), Some('*')) => {
                    depth += 1;
                    self.pos += 2;
                }
                (Some('*'), Some('/')) => {
                    depth -= 1;
                    self.pos += 2;
                    if depth == 0 {
                        return Ok(());
                    }
                }
                (Some(ch), _) => {
                    if ch == '\n' {
                        self.line += 1;
                    }
                    self.pos += 1;
                }
            }
        }
    }

    fn raw_string(&mut self, end: usize) {
        self.push(Tok::Literal, self.line);
        self.line += self.chars[self.pos..end].iter().filter(|&&ch| ch == '\n').count();
        self.pos = end;
    }

    /// `"..."`, `b"..."` or `c"..."` with backslash escapes; the token carries the opening line.
    fn string_literal(&mut self) -> Result<(), LexError> {
        let start = self.line;
        self.pos += if self.chars[self.pos] == '"' { 1 } else { 2 };
        loop {
            match self.peek(0) {
                None => return Err(LexError { line: start, message: "unterminated string literal" }),
                Some('\\') => {
                    if self.peek(1) == Some('\n') {
                        self.line += 1;
                    }
                    self.pos += 2;
                }
                Some('"') => {
                    self.pos += 1;
                    break;
                }
                Some(ch) => {
                    if ch == '\n' {
                        self.line += 1;
                    }
                    self.pos += 1;
                }
            }
        }
        self.push(Tok::Literal, start);
        Ok(())
    }

    /// `'x'`, `'\n'`, `b'x'` become literals. Otherwise the quote starts a lifetime or label: it becomes
    /// `Punct('\'')` and the name is lexed next as an identifier.
    fn char_literal_or_lifetime(&mut self) -> Result<(), LexError> {
        let quote = if self.chars[self.pos] == '\'' { self.pos } else { self.pos + 1 };
        let at = |i: usize| self.chars.get(i).copied();
        if at(quote + 1) == Some('\\') {
            // Escaped char literal: up to the next quote on the same line.
            let mut close = quote + 2;
            while close < self.chars.len() && self.chars[close] != '\'' && self.chars[close] != '\n' {
                close += 1;
            }
            if at(close) != Some('\'') {
                return Err(LexError { line: self.line, message: "unterminated char literal" });
            }
            self.push(Tok::Literal, self.line);
            self.pos = close + 1;
        } else if at(quote + 2) == Some('\'') {
            self.push(Tok::Literal, self.line);
            self.pos = quote + 3;
        } else {
            self.push(Tok::Punct('\''), self.line);
            self.pos = quote + 1;
        }
        Ok(())
    }

    /// A raw identifier `r#name` names the same item as `name`, so it lexes to `Ident(name)`.
    fn identifier(&mut self) {
        let word_end = |from: usize| {
            let mut end = from;
            while end < self.chars.len() && (self.chars[end] == '_' || self.chars[end].is_alphanumeric()) {
                end += 1;
            }
            end
        };
        let mut end = word_end(self.pos);
        let mut name: String = self.chars[self.pos..end].iter().collect();
        let raw_name_starts = self.chars.get(end + 1).is_some_and(|ch| *ch == '_' || ch.is_alphabetic());
        if name == "r" && self.chars.get(end) == Some(&'#') && raw_name_starts {
            let raw_end = word_end(end + 1);
            name = self.chars[end + 1..raw_end].iter().collect();
            end = raw_end;
        }
        self.push(Tok::Ident(name), self.line);
        self.pos = end;
    }

    /// Digits, letters, `_` (suffixes, hex) and a `.` followed by a digit.
    fn number(&mut self) {
        let mut end = self.pos;
        while end < self.chars.len() {
            let ch = self.chars[end];
            let decimal_point = ch == '.' && self.chars.get(end + 1).is_some_and(|d| d.is_ascii_digit());
            if !(ch == '_' || ch.is_alphanumeric() || decimal_point) {
                break;
            }
            end += 1;
        }
        self.push(Tok::Literal, self.line);
        self.pos = end;
    }

    fn operator_or_punct(&mut self) {
        let two: String = self.chars[self.pos..(self.pos + 2).min(self.chars.len())].iter().collect();
        match TWO_CHARACTER_OPERATORS.into_iter().find(|op| *op == two) {
            Some(op) => {
                self.push(Tok::Op(op), self.line);
                self.pos += 2;
            }
            None => {
                self.push(Tok::Punct(self.chars[self.pos]), self.line);
                self.pos += 1;
            }
        }
    }
}

/// End index of a raw (byte/C) string literal `r#"..."#` starting at `i`, if one starts there. An unterminated one
/// runs to the end of the text.
fn raw_string_end(chars: &[char], i: usize) -> Option<usize> {
    let mut j = i;
    if matches!(chars.get(j), Some('b' | 'c')) {
        j += 1;
    }
    if chars.get(j) != Some(&'r') {
        return None;
    }
    // Must not be the tail of a longer identifier.
    if i > 0 && (chars[i - 1] == '_' || chars[i - 1].is_alphanumeric()) {
        return None;
    }
    j += 1;
    let mut hashes = 0;
    while chars.get(j) == Some(&'#') {
        hashes += 1;
        j += 1;
    }
    if chars.get(j) != Some(&'"') {
        return None;
    }
    j += 1;
    while j < chars.len() {
        if chars[j] == '"' && (0..hashes).all(|h| chars.get(j + 1 + h) == Some(&'#')) {
            return Some(j + 1 + hashes);
        }
        j += 1;
    }
    Some(chars.len())
}
