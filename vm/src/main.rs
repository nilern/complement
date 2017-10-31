#[macro_use]
extern crate gc_derive;
extern crate gc;
extern crate clap;

use std::io::Read;
use std::fs::File;
use clap::{App, Arg};

mod value;
mod bytecode;
mod deserialize;

use deserialize::{Input, parse_program};

fn main() {
    let cmdline_parser = App::new("Complot VM")
                         .arg(Arg::with_name("INPUT")
                                  .required(true));
    let cmdline = cmdline_parser.get_matches();
    let input_filename = cmdline.value_of("INPUT").unwrap();
    
    let mut input_file = File::open(input_filename).unwrap();
    let mut chunk = Vec::new();
    input_file.read_to_end(&mut chunk).unwrap();
    let program = parse_program(&mut Input::new(&chunk));
    
    println!("{:#?}", program);
}
