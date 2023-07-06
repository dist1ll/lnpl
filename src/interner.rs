/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use rustc_hash::FxHashMap;

/// A unique reference for interned strings. Used for bi-directional lookup.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SymbolRef(u32);

/// A data structure for interning strings.
#[derive(Default)]
pub struct SymbolInterner<'a> {
    map: FxHashMap<&'a str, SymbolRef>,
    vec: Vec<&'a str>,
}

impl<'a> SymbolInterner<'a> {
    /// Interns the string if it hasn't been, and returns the symbol's
    pub fn intern(&mut self, s: &'a str) -> SymbolRef {
        let v: u32 = self
            .vec
            .len()
            .try_into()
            .expect("cannot intern more strings");
        let v = SymbolRef(v);
        match self.map.try_insert(s, v) {
            Ok(val) => {
                self.vec.push(s);
                *val
            }
            Err(e) => e.value,
        }
    }
    pub fn lookup(&'a self, s: SymbolRef) -> &'a str {
        self.vec[s.0 as usize]
    }
}
