#![feature(proc_macro_hygiene, decl_macro)]

#[macro_use]
extern crate rocket;

use std::path::PathBuf;

mod interface;
mod serapi_protocol;
mod universally_deserializable;

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    interface::run(
        PathBuf::from(arguments[1].clone()),
        PathBuf::from(arguments[2].clone()),
    );
}
