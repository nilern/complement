#![feature(try_from)]

#[macro_use]
extern crate gc_derive;
extern crate gc;
extern crate clap;

use std::io::{self, Read};
use std::fs::File;
use clap::{App, Arg};

mod value;
mod bytecode;
mod vm;
mod deserialize;

use vm::VM;
use deserialize::{Input, parse_program};

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
