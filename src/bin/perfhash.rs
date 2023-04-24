/*
 * Copyright (c) Adrian Alic <contact@alic.dev>
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::BTreeSet;

fn main() {
    println!("Collision-free hash function: ");

    let kw_raw = [
        "class",  //
        "for",    //
        "fn",     //
        "let",    //
        "match",  //
        "struct", //
        "type",   //
        "while",  //
    ];
    let keywords: Vec<[u8; 8]> = kw_raw
        .iter()
        .map(|kw| {
            let mut res = [0u8; 8];
            for (idx, b) in kw.as_bytes().iter().enumerate() {
                res[idx] = *b;
            }
            res
        })
        .collect();

    let mut map = BTreeSet::<u8>::new();
    for i in 1..1000 {
        let mut indices = vec![];
        for b in keywords.iter() {
            let mut hash = 0usize;
            hash += b[1] as usize + i;
            hash += (b[2] as usize) * i;
            hash = hash & 0b1111;
            indices.push(hash as u8);
        }
        // check collision free-ness
        map.clear();
        let mut collision_free = true;
        for idx in indices.iter() {
            if !map.insert(*idx) {
                collision_free = false;
                break;
            }
        }
        if collision_free {
            indices.iter().zip(kw_raw.iter()).for_each(|(idx, kw)| {
                println!("{:<6} => {:?}", kw, idx);
            });
            break;
        }
    }
}
