#![feature(proc_macro_hygiene, decl_macro, default_free_fn)]

#[macro_use]
extern crate rocket;

use std::path::PathBuf;

mod goals_analysis;
mod interface;
mod serapi_protocol;
mod tactics;
mod universally_deserializable;

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    interface::run(PathBuf::from(arguments[1].clone()));
}
