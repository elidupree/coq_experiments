# EliDupree Proof Explorer

An experimental GUI for proof exploration in Coq.

Currently extremely unfinished.

- Usage: `cargo run path_to_this_crate_root path_to_coq_file`
- Serves a web app to localhost:3508 displaying tactics that can be run from the end of the file (or from the latest command in the file that does not error). Currently is also hardcoded to treat the text `STOP` (anywhere) as the end of the file. Updates automatically as you change the file.
- Non-Rust dependencies: [SerAPI](https://github.com/ejgallego/coq-serapi/). This program runs an instance of `sertop` as a child process. I have only tested it on Linux.
