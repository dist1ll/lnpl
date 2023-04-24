/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![allow(unused)]

pub mod lexer;

use lexer::{Base, Keyword, Lexer, LiteralKind, Token, TokenKind};

pub enum ItemKind {
    Type,
}
// TODO: Make ExprId a 32-bit integer
pub type ExprId = usize;
pub const MAX_FN_ARGS: usize = 3;

#[derive(Debug)]
pub struct Expr<'a> {
    kind: ExprKind<'a>,
}
#[derive(Debug, PartialEq)]
pub enum ExprKind<'a> {
    /// A number literal
    Number(usize),
    /// A binary operation (e.g. `+`, `-`)
    Binary(BinOp, ExprId, ExprId),
    /// An identifier (variable, type, function name)
    Ident(&'a str),
    /// `()`
    Unit,
    /// Evaluation operator (e.g. `foo()`, `Bar(1, 2)`)
    Eval(ExprId, [Option<ExprId>; MAX_FN_ARGS]),
}
#[derive(Debug)]
pub enum Operator {
    Infix(BinOp),
    /// Start of an evaluation via '('
    StartEval,
    Prefix,
}
#[derive(Debug)]
pub enum Bracket {
    Parens,
    Bracket,
    Brace,
}
#[derive(Debug, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl BinOp {
    pub fn binding_power(&self) -> (u8, u8) {
        match self {
            BinOp::Add | BinOp::Sub => (1, 2), // left assoc
            BinOp::Mul | BinOp::Div => (3, 4), // left assoc
        }
    }
}

/// Type declaration via `struct` or `fn`.
fn parse_typedecl_rhs_keyword(_: &mut Lexer<'_>, k: Keyword) {
    match k {
        Keyword::Struct => println!("Parsing struct in type decl"),
        Keyword::Fn => println!("Parsing function in type decl"),
        _ => println!("Error: Expected 'struct' or 'fn' in type declaration."),
    }
}

struct Parser<'a> {
    lexer: Lexer<'a>,
    exprs: Vec<Expr<'a>>,
}
impl<'a> Parser<'a> {
    fn new(s: &'a str) -> Self {
        Self {
            lexer: Lexer::new(s),
            exprs: vec![],
        }
    }
    fn parse(&mut self) {
        self.exprs.clear();
        if let Some(t) = self.lexer.next_token() {
            self.parse_expr(t, 0);
        }
    }
    /// Type declaration via expression.
    fn parse_expr(&mut self, first: Token<'a>, min_bp: u8) -> Option<ExprId> {
        // ignore leading whitespace
        let first = if first.kind == TokenKind::Whitespace {
            self.next_non_whitespace().expect("no expression found")
        } else {
            first
        };

        // Ident position
        let mut lhs_id = match first.kind {
            TokenKind::ParensOpen => {
                let next =
                    self.next_non_whitespace().expect("no close parens");
                match next.kind {
                    TokenKind::ParensClose => self.push_expr(Expr {
                        kind: ExprKind::Unit,
                    }),
                    _ => {
                        let ret =
                            self.parse_expr(next, 0).expect("no close parens");
                        let next = self
                            .lexer
                            .next_token()
                            .expect("matching closing parenthesis");
                        assert_eq!(next.kind, TokenKind::ParensClose);
                        ret
                    }
                }
            }
            TokenKind::Literal(ref k) => {
                let number = match k {
                    LiteralKind::Int { base } => {
                        parse_number(base.clone(), first.text)
                            .expect("parsing literal into number")
                    }
                };
                self.push_expr(Expr {
                    kind: ExprKind::Number(number),
                })
            }
            TokenKind::Ident => self.push_expr(Expr {
                kind: ExprKind::Ident(
                    std::str::from_utf8(first.text)
                        .expect("convert ident to utf-8"),
                ),
            }),
            t => panic!("unsupported token: {t:?}"),
        };
        // Operator Position
        // Pratt-Parsing loop. Peeks and consumes operators.
        while let Some(op) = self.peek_operator() {
            match op {
                Operator::Infix(b) => {
                    let bp = b.binding_power();
                    if bp.0 < min_bp {
                        // bind on a precedence cliff
                        break;
                    }
                    // this eats the operator we peeked
                    self.lexer.next_token();

                    let next = self
                        .next_non_whitespace()
                        .expect("operator can't terminate expression");
                    let rhs_id = self.parse_expr(next, bp.1).unwrap();
                    lhs_id = self.push_expr(Expr {
                        kind: ExprKind::Binary(b, lhs_id, rhs_id),
                    });
                }
                Operator::StartEval => {
                    // eat the '('
                    self.lexer.next_token();
                    lhs_id = self.parse_eval(lhs_id).expect("parse eval");
                }
                other => panic!("unsupported operator: {other:?}"),
            };
        }

        Some(lhs_id)
    }
    /// Parses the inside of an evaluation operation, starting from the first
    /// token after the opening parenthesis.
    /// ```
    ///   foo(a, b, c)
    ///       ^
    ///   start here
    /// ```
    fn parse_eval(&mut self, caller: ExprId) -> Option<ExprId> {
        let mut cursor = self
            .next_non_whitespace()
            .expect("eval has closing parenthesis");
        // no arguments
        if cursor.kind == TokenKind::ParensClose {
            return Some(self.push_expr(Expr {
                kind: ExprKind::Eval(caller, Default::default()),
            }));
        }
        // parse arguments
        let mut args: [Option<ExprId>; MAX_FN_ARGS] = Default::default();
        let mut i = 0;

        loop {
            // first argument
            args[i] = Some(
                self.parse_expr(cursor, 0)
                    .expect("eval operator was not finished"),
            );

            cursor = self
                .lexer
                .next_token()
                .expect("matching closing parenthesis");

            if cursor.kind == TokenKind::Comma {
                // eat the ','
                cursor = self.lexer.next_token().unwrap();
                i += 1;
                if i >= MAX_FN_ARGS {
                    panic!("too many fn arguments. Maximum: {}", MAX_FN_ARGS);
                }
            } else {
                break;
            }
        }

        match cursor.kind {
            TokenKind::ParensClose => Some(self.push_expr(Expr {
                kind: ExprKind::Eval(caller, args),
            })),
            t => panic!("wrong eval expression termination token: {t:?}"),
        }
    }
    /// Advances to the next non-whitspace token
    fn next_non_whitespace(&mut self) -> Option<Token<'a>> {
        while let Some(t) = self.lexer.next_token() {
            match t.kind {
                TokenKind::Whitespace => continue,
                _ => return Some(t),
            };
        }
        None
    }
    fn peek_operator(&mut self) -> Option<Operator> {
        while let Some(t) = self.lexer.peek_token() {
            use TokenKind::*;
            match t.kind {
                Whitespace => {
                    self.lexer.next_token();
                    continue;
                }
                Plus => return Some(Operator::Infix(BinOp::Add)),
                Minus => return Some(Operator::Infix(BinOp::Sub)),
                Star => return Some(Operator::Infix(BinOp::Mul)),
                ParensOpen => return Some(Operator::StartEval),
                _ => return None,
            };
        }
        None
    }
    /// Pushes expression to the expr buffer and returns its id.
    fn push_expr(&mut self, expr: Expr<'a>) -> ExprId {
        self.exprs.push(expr);
        self.exprs.len() - 1
    }
    /// Pretty-print the AST
    fn pprint_ast(&mut self) {
        let current = self.exprs.last().expect("AST is empty");
        let mut stack = vec![(current, 0, false)];
        while let Some((elem, depth, last_sub)) = stack.pop() {
            let line_char = if last_sub { "└" } else { "├" };
            print!("{}{}─", "┆  ".repeat(depth / 3), line_char);
            match elem.kind {
                ExprKind::Number(n) => println!("({n})"),
                ExprKind::Binary(ref op, l, r) => {
                    let op_str = match op {
                        BinOp::Add => " +",
                        BinOp::Sub => " -",
                        BinOp::Mul => " *",
                        BinOp::Div => " ÷",
                    };
                    println!("{op_str}",);
                    stack.push((&self.exprs[r], depth + 3, true));
                    stack.push((&self.exprs[l], depth + 3, false));
                }
                ExprKind::Ident(ref n) => println!("({n})"),
                ExprKind::Unit => println!("()"),
                ExprKind::Eval(caller, args) => {
                    println!("(eval: {:?})", self.exprs[caller]);
                    args.iter().rev().for_each(|arg| {
                        if let Some(id) = arg {
                            stack.push((&self.exprs[*id], depth + 3, true));
                        }
                    });
                }
            };
        }
    }
}

fn parse_number(base: Base, s: &[u8]) -> Result<usize, &'static str> {
    let mut iter = s.iter().rev();
    let mut result = (iter.next().unwrap() - b'0') as usize;
    let mut mult = 1;
    for b in iter {
        mult *= match base {
            Base::Decimal => 10,
            Base::Binary => 2,
            Base::Hex => 16,
        }; // base
        result = result
            .checked_add((*b - b'0') as usize * mult)
            .ok_or("parsing literal overflowed")?;
    }
    Ok(result)
}

mod test {
    use super::*;
    macro_rules! extract_int {
        ($t:ident) => {
            match $t.kind {
                TokenKind::Literal(k) => match k {
                    LiteralKind::Int { base } => base,
                },
                _ => panic!(""),
            }
        };
    }

    #[test]
    pub fn number_overflow() {
        let t = Lexer::new("18073701615").next_token().unwrap();
        assert_eq!(Ok(18073701615), parse_number(extract_int!(t), t.text));

        let t = Lexer::new("18446744073709551616").next_token().unwrap();
        assert!(parse_number(extract_int!(t), t.text).is_err());
    }

    #[test]
    pub fn expr_numeric() {
        let mut p = Parser::new("(1 + 2) * 3");
        p.parse();
        assert_eq!(p.exprs[2].kind, ExprKind::Binary(BinOp::Add, 0, 1));
        assert_eq!(p.exprs[4].kind, ExprKind::Binary(BinOp::Mul, 2, 3));
    }

    #[test]
    pub fn expr_numeric_with_ident() {
        let mut p = Parser::new("(((a)) + b)");
        p.parse();
        assert_eq!(p.exprs[2].kind, ExprKind::Binary(BinOp::Add, 0, 1));
    }

    #[test]
    pub fn expr_fneval() {
        let mut p = Parser::new("f(a, b, c + 32)");
        p.parse();
        p.pprint_ast();
    }
}