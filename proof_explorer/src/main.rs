#![feature(proc_macro_hygiene, decl_macro, default_free_fn)]

#[macro_use]
extern crate rocket;

use std::path::PathBuf;

#[macro_use]
mod utils;
mod global_state_types;
mod goals_analysis;
mod main_thread_infrastructure;
mod serapi_protocol;
mod sertop_glue;
mod startup;
mod supervisor_thread;
mod tactics;
mod ui_html_generation;
mod universally_deserializable;
mod webserver_glue;
use clap::{App, Arg};
use std::iter::FromIterator;

fn main() {
    let arguments = App::new("EliDupree Proof Explorer")
        .version("0.1")
        .author("Eli Dupree <vcs@elidupree.com>")
        .arg(Arg::with_name("source_file").required(true).help("The source file to do proof exploration in."))
        .arg(Arg::with_name("sertop_args").raw(true).help("Extra arguments to pass to `sertop`, the child process that Proof Explorer uses to run Coq commands."))
        .get_matches();
    startup::run(
        PathBuf::from(arguments.value_of("source_file").unwrap()),
        arguments
            .values_of_os("sertop_args")
            .map_or(Vec::new(), Vec::from_iter)
            .as_slice(),
    );
}
