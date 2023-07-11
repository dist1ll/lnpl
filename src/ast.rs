/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::ops::Range;

use crate::interner::{SymbolInterner, SymbolRef};

pub const MAX_FN_ARGS: usize = 5;
pub const MAX_STMTS_PER_BLOCK: usize = 30;

/// An abstract syntax tree
#[derive(Default)]
pub struct Ast<'a> {
    pub exprs: Container<Expr>,
    pub stmts: Container<Stmt>,
    pub types: Container<Type>,
    pub symbols: SymbolInterner<'a>,
}

// TODO(#4): Full TypeRefs are not necessary in most cases. We could consider
// reserving a bit and implementing a manual tagged union.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// A simple identifier representing a type
    Simple(SymbolRef),
    /// A pointer type (e.g. `*T`)
    Ptr(TypeRef),
    /// A basic, single-dimensional slice type (e.g. `[]T`)
    Slice(TypeRef),
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
}
#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind {
    /// An expression + semicolon, like `foo();`, `a + b;`, `{ let x = 5; };`
    Expr(ExprRef),
    /// A let binding (identifier, optional type ascription, bound expression)
    Let(SymbolRef, Option<Type>, ExprRef),
}

#[derive(Default, Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
}
#[derive(Default, Debug, Clone, PartialEq)]
pub enum ExprKind {
    #[default]
    Unit,
    /// A number literal
    Number(usize),
    /// A binary operation (e.g. `+`, `-`)
    Binary(BinOp, ExprRef, ExprRef),
    /// An identifier (variable, type, function name)
    Ident(SymbolRef),
    /// Evaluation operator (e.g. `foo()`, `Bar(1, 2)`)
    Eval(ExprRef, Arguments),
    /// Block expression delimited by `{}`
    Block(ExprRef, StmtSlice),
}

#[derive(Default, Debug, Clone, Copy, PartialEq)]
pub struct Ident<'a>(pub &'a str);

pub struct Container<T: Clone>(Vec<T>);
impl<T: Clone> Container<T> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn get<R: ContainerIndex<T>>(&self, value: R) -> &T {
        &self.0[value.index()]
    }
    pub fn get_slice<R: ContainerRange<T>>(&self, value: R) -> &[T] {
        &self.0[value.range()]
    }
    pub fn push(&mut self, value: T) {
        self.0.push(value)
    }
    pub fn pop(&mut self) -> Option<T> {
        self.0.pop()
    }
    pub fn last(&self) -> Option<&T> {
        self.0.last()
    }
    pub fn extend_from_slice(&mut self, slice: &[T]) {
        self.0.extend_from_slice(slice)
    }
}
impl<T: Clone> IntoIterator for Container<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
impl<T: Clone> Default for Container<T> {
    fn default() -> Self {
        Container(Vec::new())
    }
}
/// Structs implementing this for T can be used as references into Container<T>.
pub trait ContainerIndex<T: Clone> {
    fn index(&self) -> usize;
}
/// Structs implementing this for T can be used as slices of Container<T> elems.
pub trait ContainerRange<T: Clone> {
    fn range(&self) -> Range<usize>;
}

#[derive(Default, Debug, Clone, Copy, PartialEq)]
pub struct TypeRef(u32);
impl TypeRef {
    pub fn new(value: usize) -> Self {
        Self(value.try_into().expect("type use limit hit"))
    }
}
impl ContainerIndex<Type> for TypeRef {
    fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq)]
pub struct ExprRef(u32);
impl ExprRef {
    pub const MAX: usize = (1 << 22);
    pub fn new(value: usize) -> Self {
        assert!(value < Self::MAX, "expression limit hit");
        Self(value as u32)
    }
}
impl ContainerIndex<Expr> for ExprRef {
    fn index(&self) -> usize {
        self.0 as usize
    }
}

/// Arguments is a fat pointer into [`Container<Expr>`]
#[derive(Default, Debug, Clone, Copy, PartialEq)]
pub struct Arguments(u32);
impl Arguments {
    pub fn new(index: usize, count: usize) -> Self {
        assert!((index + count) < ExprRef::MAX);
        assert!(count < 0xff, "exceeded maximum number of arguments (255)");
        let upper = (index as u32) << 8;
        let lower = (count as u32) & 0xff;
        Self(upper | lower)
    }
    pub fn count(&self) -> usize {
        (self.0 & 0xff) as usize
    }
}
impl ContainerRange<Expr> for Arguments {
    fn range(&self) -> Range<usize> {
        let lower = (self.0) & 0xff;
        let upper = (self.0) >> 8;
        (upper as usize)..(upper + lower) as usize
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq)]
pub struct StmtRef(pub u32);
impl ContainerIndex<Stmt> for StmtRef {
    fn index(&self) -> usize {
        self.0 as usize
    }
}

/// StmtSlice is a fat pointer into [`Container<Stmt>`]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct StmtSlice(u32);
impl StmtSlice {
    pub fn new(index: usize, statement_count: usize) -> Self {
        assert!(index < 1 << 24);
        assert!(statement_count < 1 << 8);
        Self(((index << 8) + statement_count) as u32)
    }
}

impl ContainerRange<Stmt> for StmtSlice {
    fn range(&self) -> Range<usize> {
        let index = (self.0 >> 8) as usize;
        let count = (self.0 & 0xff) as usize;
        index..(index + count)
    }
}

#[derive(Debug)]
pub enum Operator {
    Infix(BinOp),
    /// Start of an evaluation via '('
    StartEval,
    Statement,
    Prefix,
}
#[derive(Debug)]
pub enum Bracket {
    Parens,
    Bracket,
    Brace,
}
#[derive(Debug, Clone, PartialEq)]
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
