/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */
#![feature(assert_matches)]
#![feature(map_try_insert)]

pub mod ast;
pub mod interner;
pub mod lexer;
pub mod stackvec;

use std::str::from_utf8;

use ast::{
    Arguments, BinOp, Container, Expr, ExprKind, ExprRef, Operator, Stmt,
    StmtKind, StmtSlice, MAX_FN_ARGS, MAX_STMTS_PER_BLOCK,
};
use interner::SymbolInterner;
use lexer::{
    common::{Base, Token},
    Lexer,
};
use stackvec::StackVec;

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    exprs: Container<Expr>,
    stmts: Container<Stmt>,
    symbols: SymbolInterner<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(s: &'a str) -> Self {
        let mut p = Self {
            lexer: Lexer::new(s),
            exprs: Default::default(),
            stmts: Default::default(),
            symbols: Default::default(),
        };
        // lexer should point at first non-whitespace token.
        p.next_non_wspace();
        p
    }
    #[inline]
    pub fn parse(&mut self) {
        self.parse_expr(0);
    }
    /// Parses an expression. Must not have leading whitespace.
    /// After parsing an expression, does not leave trailing whitespace.
    #[inline]
    fn parse_expr(&mut self, min_bp: u8) -> Option<ExprRef> {
        let first = self.lexer.current().expect("non-whitespace tokens");
        // Start of expression
        let mut lhs_id = match &first {
            Token::BraceOpen => self.parse_expr_block(),
            Token::ParensOpen => self.parse_expr_parens(),
            Token::Number(base) => {
                let number = parse_number(*base, self.lexer.slice())
                    .expect("parsing literal into number");
                self.push_expr(Expr {
                    kind: ExprKind::Number(number),
                })
            }
            Token::Ident => {
                let text =
                    from_utf8(self.lexer.slice()).expect("convert to utf-8");
                let sym_ref = self.symbols.intern(text);
                self.push_expr(Expr {
                    kind: ExprKind::Ident(sym_ref),
                })
            }
            t => panic!("expected expression, found `{t:?}`"),
        };

        // eat the lhs token
        self.lexer.next();

        // (Pratt-parsing) Consumes token, and checks if it's an operator.
        // All non-operator tokens in operator position terminate the expr.
        while let Some(operator) = self.consume_operator() {
            // `op` is the token at `self.lexer.current()` position
            match operator {
                Operator::Infix(b) => {
                    let bp = b.binding_power();
                    if bp.0 < min_bp {
                        // bind on a precedence cliff
                        break;
                    }
                    // skip to first meaningful token after operator
                    self.next_non_wspace()
                        .expect("operator can't terminate expression");
                    let rhs_id = self.parse_expr(bp.1).unwrap();
                    lhs_id = self.push_expr(Expr {
                        kind: ExprKind::Binary(b, lhs_id, rhs_id),
                    });
                }
                Operator::StartEval => {
                    lhs_id = self.parse_eval(lhs_id).expect("parse eval");
                    // skip to next meaningful token after `)`
                    self.next_non_wspace();
                }
                Operator::Statement => {
                    break;
                }
                other => panic!("expected operator, found `{other:?}`"),
            };
        }
        Some(lhs_id)
    }

    /// Parse parenthesized expression. Examples: `(1)`, `(x + y)`
    /// Starts at opening parenthesis, ends at closing parenthesis.
    #[inline]
    fn parse_expr_parens(&mut self) -> ExprRef {
        debug_assert_eq!(
            self.lexer.current().unwrap(),
            Token::ParensOpen,
            "parenthesized expression needs to start with `(`"
        );

        let next = self.next_non_wspace().expect("no close parens");

        // empty parentheses ()
        if next == Token::ParensClose {
            return self.push_expr(Expr {
                kind: ExprKind::Unit,
            });
        }
        let ret = self.parse_expr(0).expect("no close parens");
        let next = self.lexer.current().expect("matching closing parenthesis");

        match next {
            Token::ParensClose => (),
            Token::Semicolon => {
                panic!("parenthesized expressions cannot contain statements")
            }
            k => panic!("expected closing parenthesis ')', found {:?}", k),
        };
        ret
    }
    /// Parse block expression. A block expression is a '{}'-delimited block,
    /// which contains one or more statements, and ends with an expression.
    ///
    /// Examples of block expressions:
    ///
    /// ```
    /// { min(x, y) + 2 }
    ///
    /// {
    ///    let x = 1; // <-- statement
    ///    let y = 2; // <-- statement
    ///    (x + y)    // <-- expression
    /// }
    /// ```
    #[inline]
    fn parse_expr_block(&mut self) -> ExprRef {
        debug_assert_eq!(
            self.lexer.current().unwrap(),
            Token::BraceOpen,
            "block expression needs to start with `{{`"
        );

        let mut next = self.next_non_wspace().expect("missing '}'");

        let mut block_members = 0;
        let mut stmts: StackVec<Stmt, MAX_STMTS_PER_BLOCK> =
            Default::default();

        let mut expr = ExprRef::new(0);
        // Iterates over statements and expressions inside the block expr.
        // If we find a statement, we consume it, add it to the list of
        // statements, and continue looping until we find an expression.
        while next != Token::BraceClose {
            block_members += 1;
            expr = self.parse_expr(0).expect("missing '}'");
            next = self.lexer.current().expect("missing '}'");

            match next {
                Token::Semicolon => (),
                Token::BraceClose => break,
                k => panic!("block expr need to end with '}}', found {:?}", k),
            }
            // add statement to current expr block
            stmts
                .push(Stmt {
                    kind: StmtKind::Expr(expr),
                })
                .unwrap();
            next = self.next_non_wspace().expect("missing '}'");
        }
        // special case: empty expression block
        if block_members == 0 {
            return self.push_expr(Expr {
                kind: ExprKind::Unit,
            });
        }
        // block expr ends with statement
        if stmts.len() == block_members {
            expr = self.push_expr(Expr {
                kind: ExprKind::Unit,
            });
        }
        let stmt_ref = match stmts.len() {
            0 => StmtSlice::new(0, 0),
            _ => self.push_stmts(stmts.as_slice()),
        };
        self.push_expr(Expr {
            kind: ExprKind::Block(expr, stmt_ref),
        })
    }
    /// Parses the inside of an evaluation operation, starting from the
    /// opening parenthesis and ends at the closing parenthesis `)`.
    /// ```
    ///   foo(a, b, c, d, e, f)
    ///      ^                ^
    ///   start here      end here
    /// ```
    #[inline]
    fn parse_eval(&mut self, caller: ExprRef) -> Option<ExprRef> {
        debug_assert_eq!(
            self.lexer.current().unwrap(),
            Token::ParensOpen,
            "rhs of eval expression needs to start with `(`"
        );
        let cursor = self.next_non_wspace().expect("has closing parenthesis");

        // no arguments
        if cursor == Token::ParensClose {
            return Some(self.push_expr(Expr {
                kind: ExprKind::Eval(caller, Default::default()),
            }));
        }
        // parse arguments
        let mut args: [Expr; MAX_FN_ARGS] = Default::default();
        let mut i = 0;

        loop {
            // parse & pop argument, so they can be added later
            self.parse_expr(0).expect("eval operator was not finished");
            // EX: we already asserted existence of at least 1 expression
            args[i] = self.exprs.pop().unwrap();

            if self.lexer.current().expect("matching closing parenthesis")
                == Token::Comma
            {
                // eat the ',' and any subsequent whitespace
                self.next_non_wspace();
                i += 1;
                if i >= MAX_FN_ARGS {
                    panic!("too many fn arguments. Maximum: {MAX_FN_ARGS}");
                }
            } else {
                break;
            }
        }

        let args = self.push_expr_slice(&args[0..(i + 1)]);

        match &self.lexer.current().unwrap() {
            Token::ParensClose => Some(self.push_expr(Expr {
                kind: ExprKind::Eval(caller, args),
            })),
            t => panic!("wrong eval expression termination token: {t:?}"),
        }
    }
    /// Returns the next token that is not whitespace
    #[inline]
    fn next_non_wspace(&mut self) -> Option<Token> {
        while let Some(t) = self.lexer.next() {
            match t {
                Token::Whitespace => continue,
                _ => return Some(t),
            }
        }
        None
    }
    /// Starts from current token, consuming whitespace and finally an operator.
    /// The operator returned by this function equals `Lexer::current`.
    #[inline]
    fn consume_operator(&mut self) -> Option<Operator> {
        use Token::*;
        let mut current = self.lexer.current();
        while let Some(t) = current {
            match t {
                Whitespace => {
                    current = self.lexer.next();
                    continue;
                }
                Plus => return Some(Operator::Infix(BinOp::Add)),
                Minus => return Some(Operator::Infix(BinOp::Sub)),
                Star => return Some(Operator::Infix(BinOp::Mul)),
                ParensOpen => return Some(Operator::StartEval),
                Semicolon => return Some(Operator::Statement),
                _ => return None,
            };
        }
        None
    }
    /// Pushes expression to the expr buffer and returns its id.
    #[inline]
    fn push_expr(&mut self, expr: Expr) -> ExprRef {
        self.exprs.push(expr);
        ExprRef::new(self.exprs.len() - 1)
    }
    /// Pushes argument to the args buffer and returns the argument id
    #[inline]
    fn push_expr_slice(&mut self, expr_ids: &[Expr]) -> Arguments {
        let len = self.exprs.len();
        assert!((len + expr_ids.len()) <= ExprRef::MAX);
        self.exprs.extend_from_slice(expr_ids);
        Arguments::new(len, expr_ids.len())
    }
    /// Pushes statements to the stmts buffer and returns the statement id
    #[inline]
    fn push_stmts(&mut self, stmts: &[Stmt]) -> StmtSlice {
        let len = stmts.len();
        assert!(len > 0, "non-zero number of statements expected");
        self.stmts.extend_from_slice(stmts);
        StmtSlice::new(self.stmts.len() - len, len)
    }
    /// Pretty-print the AST
    pub fn pprint_ast(&mut self) {
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
                    stack.push((self.exprs.get(r), depth + 3, true));
                    stack.push((self.exprs.get(l), depth + 3, false));
                }
                ExprKind::Ident(n) => println!("({})", self.symbols.lookup(n)),
                ExprKind::Unit => println!("()"),
                ExprKind::Eval(caller, args) => {
                    println!("(eval: {:?})", self.exprs.get(caller).kind);
                    self.exprs.get_slice(args).iter().rev().for_each(|expr| {
                        stack.push((expr, depth + 3, true));
                    });
                }
                ExprKind::Block(expr, stmt_ref) => {
                    println!("(blockexpr)");
                    stack.push((self.exprs.get(expr), depth + 3, true));
                    self.stmts.get_slice(stmt_ref).iter().rev().for_each(
                        |s| match s.kind {
                            StmtKind::Expr(expr_ref) => stack.push((
                                self.exprs.get(expr_ref),
                                depth + 3,
                                false,
                            )),
                            StmtKind::Let(ident_ref, expr_ref) => {
                                println!(
                                    "(let {:?})",
                                    self.symbols.lookup(ident_ref)
                                );
                                stack.push((
                                    self.exprs.get(expr_ref),
                                    depth + 3,
                                    false,
                                ));
                            }
                        },
                    );
                }
            };
        }
    }
}

#[inline]
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

#[cfg(test)]
mod test {
    use super::*;
    macro_rules! extract_int {
        ($t:ident) => {
            match &$t {
                Token::Number(base) => *base,
                _ => panic!(""),
            }
        };
    }

    #[test]
    pub fn number_overflow() {
        let mut lexer = Lexer::new("1801615");
        let t = lexer.next().unwrap();
        assert_eq!(Ok(1801615), parse_number(extract_int!(t), lexer.slice()));

        let mut lexer = Lexer::new("18446744073709551616");
        let t = lexer.next().unwrap();
        assert!(parse_number(extract_int!(t), lexer.slice()).is_err());
    }

    #[test]
    pub fn expr_numeric() {
        let mut p = Parser::new("(1 + 2) * 3");
        p.parse();
        assert_eq!(
            p.exprs.get(ExprRef::new(2)).kind,
            ExprKind::Binary(BinOp::Add, ExprRef::new(0), ExprRef::new(1))
        );
        assert_eq!(
            p.exprs.get(ExprRef::new(4)).kind,
            ExprKind::Binary(BinOp::Mul, ExprRef::new(2), ExprRef::new(3))
        );
    }

    #[test]
    pub fn expr_with_ident() {
        let mut p = Parser::new("(((a)) + b)");
        p.parse();
        assert_eq!(
            p.exprs.get(ExprRef::new(2)).kind,
            ExprKind::Binary(BinOp::Add, ExprRef::new(0), ExprRef::new(1))
        );
    }

    #[test]
    pub fn expr_fneval() {
        let mut p = Parser::new("f(a, b, c, 4)");
        p.parse();
        match p.exprs.last().unwrap().kind {
            ExprKind::Eval(_, args) => {
                assert_eq!(args.count(), 4, "expected 4 arguments");
            }
            _ => panic!("expected ExprKind::Eval"),
        };
    }

    #[test]
    pub fn expr_block() {
        let mut p = Parser::new("{ 2 * 3 }");
        p.parse_expr_block();
        p.pprint_ast();
        assert_eq!(
            p.exprs.get(ExprRef::new(2)).kind,
            ExprKind::Binary(BinOp::Mul, ExprRef::new(0), ExprRef::new(1))
        );
    }

    #[test]
    pub fn stmt_simple_expr() {
        // weird whitespace on purpose
        let mut p = Parser::new("2+ ( { f(2+1); 2; 2 +3; } )");
        p.parse();
        match p.exprs.get(ExprRef::new(11)).kind {
            ExprKind::Block(end, slice) => {
                assert_eq!(p.exprs.get(end).kind, ExprKind::Unit);
                assert_eq!(p.stmts.get_slice(slice).len(), 3);
            }
            ref expr => panic!("unexpected expression type: {:?}", expr),
        }
    }
}
