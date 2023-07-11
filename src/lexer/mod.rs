/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */
pub mod common;

use common::{keyword_hash, Base, Token, KEYWORD_MAP, MAX_KW_LEN};
use std::{
    iter::Peekable,
    str::{from_utf8_unchecked, Chars},
};

/// Generic lexer implementation. This is used as a fallback implementation
/// for platforms without a specialized SIMD implementation.
pub struct Lexer<'a> {
    pub chars: Peekable<Chars<'a>>,
    text: &'a [u8],
    pos: usize,
    current: Option<Token>,
    current_len: u32,
}

impl<'a> Lexer<'a> {
    pub fn new(s: &str) -> Lexer<'_> {
        Lexer {
            chars: s.chars().peekable(),
            text: s.as_bytes(),
            pos: 0,
            current: None,
            current_len: 0,
        }
    }
    #[must_use]
    #[inline]
    pub fn current(&self) -> Option<Token> {
        self.current
    }
    #[inline]
    pub fn slice(&self) -> &'a str {
        let s = &self.text[(self.pos - self.current_len as usize)..(self.pos)];
        // SAFETY: The `text` was derived from a checked utf-8 string.
        // We increment the position in [`Self::advance`] by the number of
        // bytes the character occupies in utf-8.
        unsafe { from_utf8_unchecked(s) }
    }
    #[inline]
    pub fn next(&mut self) -> Option<Token> {
        // return peeked token if it was set
        let old_pos = self.pos;
        let kind = match self.advance()? {
            c if is_ident_prefix(c) => self.read_name(c),
            c if c.is_ascii_whitespace() => {
                self.advance_while(|c| c.is_ascii_whitespace());
                Token::Whitespace
            }
            c @ '0'..='9' => self.read_numeral(c),
            ';' => Token::Semicolon,
            ',' => Token::Comma,
            '.' => Token::Dot,
            '(' => Token::ParensOpen,
            ')' => Token::ParensClose,
            '{' => Token::BraceOpen,
            '}' => Token::BraceClose,
            '[' => Token::BracketOpen,
            ']' => Token::BracketClose,
            '+' => Token::Plus,
            '-' => Token::Minus,
            '*' => Token::Star,
            '=' => Token::Eq,
            '>' => Token::Gt,
            ':' => Token::Colon,
            _ => Token::Ident,
        };
        self.current_len = self.pos as u32 - old_pos as u32;
        self.current = Some(kind);
        self.current
    }
    #[inline]
    fn advance(&mut self) -> Option<char> {
        match self.chars.next() {
            None => None,
            Some(next) => {
                self.pos += next.len_utf8();
                Some(next)
            }
        }
    }
    #[inline]
    fn peek_char(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }
    #[inline]
    fn read_numeral(&mut self, first: char) -> Token {
        let second = match self.peek_char() {
            None => return Token::Number(Base::Decimal),
            Some(digit) => digit,
        };
        if first == '0' {
            match second {
                '0'..='9' => {
                    self.advance_while(|c| c.is_ascii_digit());
                    Token::Number(Base::Decimal)
                }
                'b' => {
                    self.advance(); // skips the `b`
                    self.advance_while(|c| c == '0' || c == '1');
                    Token::Number(Base::Binary)
                }
                'x' => {
                    self.advance(); // skips the `x`
                    self.advance_while(|c| c.is_ascii_hexdigit());
                    Token::Number(Base::Hex)
                }
                _ => Token::Number(Base::Decimal),
            }
        } else {
            self.advance_while(|c| c.is_ascii_digit());
            Token::Number(Base::Decimal)
        }
    }
    /// Returns either Ident or Keyword
    #[inline]
    fn read_name(&mut self, first: char) -> Token {
        let mut cursor = 1;
        let mut kw_buf = [0u8; MAX_KW_LEN];
        let mut keyword_candidate = true;
        if first.is_ascii_lowercase() {
            kw_buf[0] = first as u8;
        } else {
            keyword_candidate = false;
        }
        while let Some(c) = self.chars.peek() {
            // requirement for keyword
            if keyword_candidate
                && cursor < MAX_KW_LEN
                && c.is_ascii_lowercase()
            {
                kw_buf[cursor] = *c as u8;
                cursor += 1;
            } else if c.is_ascii_alphanumeric() {
                keyword_candidate = false;
            } else {
                break;
            }
            self.advance();
        }

        if keyword_candidate {
            let (hash, keyword) = keyword_hash(&kw_buf);
            if kw_buf == KEYWORD_MAP[hash] {
                return keyword.expect("hash fn and keyword map don't match");
            }
        }
        Token::Ident
    }
    // Consumes characters that fulfil the given condition.
    #[inline]
    fn advance_while(&mut self, condition: fn(char) -> bool) {
        while let Some(c) = self.peek_char() {
            if !condition(c) {
                break;
            }
            self.advance();
        }
    }
}

// Returns true if the given character can be the start of an identifier.
#[inline]
pub fn is_ident_prefix(c: char) -> bool {
    c.is_ascii_alphabetic()
}

#[cfg(test)]
mod test {
    use super::Lexer;
    use super::{Base::*, Token};
    use std::assert_matches::assert_matches;

    #[test]
    fn number() {
        let mut l = Lexer::new("0 ");
        assert_matches!(l.next().unwrap(), Token::Number(_));
        assert_eq!(l.slice(), "0");

        let mut l = Lexer::new("12384359");
        assert_matches!(l.next().unwrap(), Token::Number(_));
    }

    #[test]
    fn number_binary() {
        let mut l = Lexer::new("0b1 0b1010101011");
        assert_matches!(l.next().unwrap(), Token::Number(Binary));
        assert_matches!(l.next().unwrap(), Token::Whitespace);
        assert_matches!(l.next().unwrap(), Token::Number(Binary));
    }

    #[test]
    fn number_hex() {
        let mut l = Lexer::new("0x1 0x12384359");
        assert_matches!(l.next().unwrap(), Token::Number(Hex));
        assert_eq!(l.slice().len(), 3);
        assert_matches!(l.next().unwrap(), Token::Whitespace);
        assert_matches!(l.next().unwrap(), Token::Number(Hex));
    }

    #[test]
    fn fn_call() {
        let mut l = Lexer::new("let x = foo(0b1010)");
        assert_matches!(l.next().unwrap(), Token::Let);
        assert_matches!(l.next().unwrap(), Token::Whitespace);
        assert_matches!(l.next().unwrap(), Token::Ident);
        assert_matches!(l.next().unwrap(), Token::Whitespace);
        assert_matches!(l.next().unwrap(), Token::Eq);
        assert_matches!(l.next().unwrap(), Token::Whitespace);
        assert_matches!(l.next().unwrap(), Token::Ident);
        assert_matches!(l.next().unwrap(), Token::ParensOpen);
        assert_matches!(l.next().unwrap(), Token::Number(Binary));
        assert_matches!(l.next().unwrap(), Token::ParensClose);
    }
}
