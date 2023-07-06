/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

// Pretty-printing functionality for the Ast

use crate::ast::{Ast, BinOp, ExprKind, StmtKind};

impl<'a> Ast<'a> {
    pub fn pretty_print(&self) {
        let current = self.exprs.last().expect("AST is empty");
        let mut stack = vec![(current, 0, false)];
        while let Some((elem, depth, last_sub)) = stack.pop() {
            let line_char = if last_sub { "└" } else { "├" };
            print!("{}{}─", "┆  ".repeat(depth / 3), line_char);

            self.print_exprkind(&elem.kind);
            println!(""); /* newline after exprkind header */

            match elem.kind {
                ExprKind::Number(_) => (),
                ExprKind::Binary(_, l, r) => {
                    stack.push((self.exprs.get(r), depth + 3, true));
                    stack.push((self.exprs.get(l), depth + 3, false));
                }
                ExprKind::Ident(_) => (),
                ExprKind::Unit => (),
                ExprKind::Eval(_, args) => {
                    self.exprs.get_slice(args).iter().rev().for_each(|expr| {
                        stack.push((expr, depth + 3, true));
                    });
                }
                ExprKind::Block(expr, stmt_ref) => {
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
    /// Prints the first line of an ExprKind
    fn print_exprkind(&self, e: &ExprKind) {
        match e {
            ExprKind::Number(n) => print!("({n})"),
            ExprKind::Binary(ref op, _, _) => {
                let op_str = match op {
                    BinOp::Add => " +",
                    BinOp::Sub => " -",
                    BinOp::Mul => " *",
                    BinOp::Div => " ÷",
                };
                print!("{op_str}",);
            }
            ExprKind::Ident(n) => {
                print!("({})", self.symbols.lookup(*n))
            }
            ExprKind::Unit => print!("()"),
            ExprKind::Eval(caller, _) => {
                print!("(eval: ");
                self.print_exprkind(&self.exprs.get(*caller).kind);
                print!(")");
            }
            ExprKind::Block(_, _) => {
                print!("(blockexpr)");
            }
        };
    }
}
