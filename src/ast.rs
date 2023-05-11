/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::ops::Range;

pub enum ItemKind {
    Type,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
}
#[derive(Debug, Clone)]
pub enum StmtKind {
    /// An expression + semicolon, like `foo();`, `a + b;`, `{ let x = 5; };`
    Expr(ExprRef),
}
#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
}

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
pub struct ExprRef(pub u32);
impl ExprRef {
    pub const MAX: usize = u32::MAX as usize;
}
impl<'a> ContainerIndex<Expr<'a>> for ExprRef {
    fn index(&self) -> usize {
        self.0 as usize
    }
}

/// ArgsSlice is a fat pointer into [`Container<Expr>`]
#[derive(Default, Debug, Clone, Copy, PartialEq)]
pub struct ArgsSlice(pub usize, pub usize);
impl ContainerRange<ExprRef> for ArgsSlice {
    fn range(&self) -> Range<usize> {
        self.0..(self.0 + self.1)
    }
}

/// StmtSlice is a fat pointer into [`Container<Expr>`]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct StmtSlice(u32);
impl ContainerRange<Stmt> for StmtSlice {
    fn range(&self) -> Range<usize> {
        let index = (self.0 >> 8) as usize;
        let count = (self.0 & 0xff) as usize;
        index..(index + count)
    }
}

impl StmtSlice {
    pub fn new(index: usize, statement_count: usize) -> Self {
        assert!(index < 1 << 24);
        assert!(statement_count < 1 << 8);
        Self((index << 8 + statement_count) as u32)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind<'a> {
    /// A number literal
    Number(usize),
    /// A binary operation (e.g. `+`, `-`)
    Binary(BinOp, ExprRef, ExprRef),
    /// An identifier (variable, type, function name)
    Ident(&'a str),
    /// `()`
    Unit,
    /// Evaluation operator (e.g. `foo()`, `Bar(1, 2)`)
    /// TODO: Reduce size with bitpacking
    Eval(ExprRef, ArgsSlice),
    /// Block expression delimited by `{}`
    Block(ExprRef, StmtSlice),
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