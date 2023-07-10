/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

//! This module contains common lexer-related definitions.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Token {
    /// Keyword `ln`
    Ln,
    /// Keyword `class`
    Class,
    /// Keyword `for`
    For,
    /// Keyword `fn`
    Fn,
    /// Keyword `let`
    Let,
    /// Keyword `match`
    Match,
    /// Keyword `struct`
    Struct,
    ///
    While,
    /// Whitespace sequencee
    Whitespace,
    /// Number literal
    Number(Base),
    /// Identifier
    Ident,
    /// =
    Eq = 61,
    /// >
    Gt = 62,
    /// +
    Plus = 43,
    /// -
    Minus = 45,
    /// *
    Star = 42,
    /// :
    Colon = 58,
    /// ,
    Comma = 44,
    /// .
    Dot = 46,
    /// ;
    Semicolon = 59,
    /// (
    ParensOpen = 40,
    /// )
    ParensClose = 41,
    /// [
    BracketOpen = 91,
    /// ]
    BracketClose = 93,
    /// {
    BraceOpen = 123,
    /// }
    BraceClose = 125,
}

impl Token {
    pub fn bp(&self) -> (u8, u8) {
        match self {
            Token::Plus => (1, 2),
            _ => panic!("this token is not an expression operator"),
        }
    }
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

/// Maximum keyword length
pub const MAX_KW_LEN: usize = 8;

/// A perfect hash table for keywords. Use [`keyword_hash`] to compute a hash
/// value from a given 8-byte slice. 
#[rustfmt::skip]
pub const KEYWORD_MAP: [[u8; 8]; 16] = [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    conv("ln"),
    conv("while"),
    [0, 0, 0, 0, 0, 0, 0, 0],
    conv("struct"),
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    conv("for"),
    [0, 0, 0, 0, 0, 0, 0, 0],
    conv("let"),
    conv("match"),
    conv("fn"),
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    conv("class"),
];

pub const KW_MAGIC_NUMBER: usize = 6;

#[inline]
pub fn keyword_hash(b: &[u8; 8]) -> (usize, Option<Token>) {
    let hash =
        (b[0] as usize + KW_MAGIC_NUMBER + b[2] as usize * KW_MAGIC_NUMBER)
            & 0b1111;
    let keyword = match hash {
        2 => Token::Ln,
        3 => Token::While,
        5 => Token::Struct,
        8 => Token::For,
        10 => Token::Let,
        11 => Token::Match,
        12 => Token::Fn,
        15 => Token::Class,
        _ => return (hash, None),
    };
    (hash, Some(keyword))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Base {
    Decimal,
    Binary,
    Hex,
}
