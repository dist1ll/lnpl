/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */
use std::{iter::Peekable, str::Chars};

pub const MAX_KW_LEN: usize = 8;

#[derive(Debug, Clone)]
pub struct Token<'a> {
    pub text: &'a [u8],
    pub kind: TokenKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Keyword(Keyword),
    Ident,
    Literal(LiteralKind),
    Whitespace,
    Eq,
    Plus,
    Minus,
    Star,
    Colon,
    Semicolon,
    // ()
    ParensOpen,
    ParensClose,
    /// [
    BracketOpen,
    /// ]
    BracketClose,
    /// {
    BraceOpen,
    /// }
    BraceClose,

    End,
}

impl TokenKind {
    pub fn bp(&self) -> (u8, u8) {
        match self {
            TokenKind::Plus => (1, 2),
            _ => panic!("this token is not an expression operator"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Keyword {
    Class,
    For,
    Fn,
    Let,
    Match,
    Struct,
    Type,
    While,
}

const fn conv(s: &'static str) -> [u8; 8] {
    let mut res = [0; 8];
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        res[i] = b[i];
        i += 1;
    }
    res
}
// Indices: [4, 12, 2, 13, 8, 0, 1, 6], i = 3
pub fn keyword_hash(b: &[u8; 8]) -> (usize, Option<Keyword>) {
    let hash = (b[1] as usize + 3 + b[2] as usize * 3) & 0b1111;
    let keyword = match hash {
        0 => Keyword::Match,
        1 => Keyword::Fn,
        2 => Keyword::Class,
        4 => Keyword::Let,
        6 => Keyword::While,
        8 => Keyword::For,
        12 => Keyword::Type,
        13 => Keyword::Struct,
        _ => return (hash, None),
    };
    (hash, Some(keyword))
}

const KEYWORD_MAP: [[u8; 8]; 16] = [
    conv("match"),            // 0
    conv("fn"),               // 1
    conv("class"),            // 2
    [0, 0, 0, 0, 0, 0, 0, 0], //
    conv("let"),              // 4
    [0, 0, 0, 0, 0, 0, 0, 0], //
    conv("while"),            // 6
    [0, 0, 0, 0, 0, 0, 0, 0], //
    conv("for"),              // 8
    [0, 0, 0, 0, 0, 0, 0, 0], //
    [0, 0, 0, 0, 0, 0, 0, 0], //
    [0, 0, 0, 0, 0, 0, 0, 0], //
    conv("type"),             //
    conv("struct"),           //
    [0, 0, 0, 0, 0, 0, 0, 0], //
    [0, 0, 0, 0, 0, 0, 0, 0], //
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LiteralKind {
    Int { base: Base },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Base {
    Decimal,
    Binary,
    Hex,
}

pub struct Lexer<'a> {
    pub chars: Peekable<Chars<'a>>,
    text: &'a [u8],
    pos: usize,
    peeked: Option<Token<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new<'s>(s: &'s str) -> Lexer<'_> {
        Lexer {
            chars: s.chars().peekable(),
            text: s.as_bytes(),
            pos: 0,
            peeked: None,
        }
    }
    pub fn next_token(&mut self) -> Option<Token<'a>> {
        if self.peeked.is_some() {
            let res = self.peeked.clone();
            self.peeked = None;
            return res;
        }
        let old_pos = self.pos;
        let kind = match self.advance()? {
            c if is_ident_prefix(c) => self.read_name(c),
            c if c.is_ascii_whitespace() => self.read_whitespace(),
            '0'..='9' => self.read_numeral(),
            ';' => TokenKind::Semicolon,
            '(' => TokenKind::ParensOpen,
            ')' => TokenKind::ParensClose,
            '{' => TokenKind::BraceOpen,
            '}' => TokenKind::BraceClose,
            '[' => TokenKind::BracketOpen,
            ']' => TokenKind::BracketClose,
            '+' => TokenKind::Plus,
            '-' => TokenKind::Minus,
            '*' => TokenKind::Star,
            '=' => TokenKind::Eq,
            ':' => TokenKind::Colon,
            _ => TokenKind::Ident,
        };
        Some(Token {
            kind,
            text: &self.text[old_pos..self.pos],
        })
    }
    pub fn peek_token(&mut self) -> Option<Token<'a>> {
        if self.peeked.is_some() {
            return self.peeked.clone();
        }
        self.peeked = self.next_token();
        self.peeked.clone()
    }
    // use advance() instead of self.text.next()
    fn advance(&mut self) -> Option<char> {
        self.pos += 1;
        self.chars.next()
    }
    fn peek(&mut self) -> Option<&char> {
        self.chars.peek()
    }
    fn read_numeral(&mut self) -> TokenKind {
        while let Some(c) = self.peek() {
            if !c.is_ascii_digit() {
                break;
            }
            self.advance();
        }
        TokenKind::Literal(LiteralKind::Int {
            base: Base::Decimal,
        })
    }
    /// Returns either Ident or Keyword
    fn read_name(&mut self, first_char: char) -> TokenKind {
        let mut cursor = 1;
        let mut kw_buf = [0u8; MAX_KW_LEN];
        let mut keyword_candidate = true;
        if first_char.is_ascii_lowercase() {
            kw_buf[0] = first_char as u8;
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
                return TokenKind::Keyword(
                    keyword.expect("hash fn and keyword map don't match"),
                );
            }
        }
        TokenKind::Ident
    }
    fn read_whitespace(&mut self) -> TokenKind {
        while let Some(c) = self.chars.peek() {
            if !c.is_ascii_whitespace() {
                break;
            }
            self.advance();
        }
        TokenKind::Whitespace
    }
}
// Returns true if the given character can be the start of an identifier.
pub fn is_ident_prefix(c: char) -> bool {
    c.is_ascii_alphabetic()
}

mod test {
    use super::*;

    #[test]
    pub fn peek() {
        let mut t = Lexer::new("+ +");
        // peek, peek, next
        assert_eq!(t.peek_token().unwrap().kind, TokenKind::Plus);
        assert_eq!(t.peek_token().unwrap().kind, TokenKind::Plus);
        assert_eq!(t.next_token().unwrap().kind, TokenKind::Plus);

        // peek, peek, next
        assert_eq!(t.peek_token().unwrap().kind, TokenKind::Whitespace);
        assert_eq!(t.peek_token().unwrap().kind, TokenKind::Whitespace);
        assert_eq!(t.next_token().unwrap().kind, TokenKind::Whitespace);
    }
}
