#![feature(proc_macro_hygiene, decl_macro, default_free_fn)]

#[macro_use]
extern crate rocket;

use std::path::PathBuf;

mod global_state_types;
mod goals_analysis;
mod interface;
mod serapi_protocol;
mod startup;
mod supervisor_thread;
mod tactics;
mod universally_deserializable;
mod utils;
mod webserver_glue;

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    startup::run(PathBuf::from(arguments[1].clone()));
}
