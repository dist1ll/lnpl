/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use lnpl::Parser;

const SOURCE: &str = include_str!("../example.ln");

fn main() {
    let mut p = Parser::new(SOURCE);
    p.parse();
    p.ast.pretty_print();
}
