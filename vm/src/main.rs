#![feature(unboxed_closures, try_from)]

#[macro_use]
extern crate gc_derive;
extern crate gc;
extern crate clap;
extern crate libloading;
extern crate libffi;

mod parse;
mod data;
mod code;
mod vm;

use std::io::{self, Read};
use std::fs::File;
use clap::{App, Arg};

use parse::{Input, parse_program};
use vm::VM;

fn main() {
    let cmdline_parser = App::new("Complot VM")
                         .arg(Arg::with_name("INPUT"));
    let cmdline = cmdline_parser.get_matches();

    let mut chunk = Vec::new();
    if let Some(input_filename) = cmdline.value_of("INPUT") {
        File::open(input_filename).unwrap()
             .read_to_end(&mut chunk).unwrap();
    } else {
        io::stdin().read_to_end(&mut chunk).unwrap();
    }
    
    let program = parse_program(&mut Input::new(&chunk)).unwrap();
    
    let mut vm = VM::new(&program);
    println!("{:?}", vm.run());
}
