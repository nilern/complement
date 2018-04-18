use std::mem::size_of;
use std::str::{self, Utf8Error};
use gc::Gc;

use code::Instr;
use data::{Program, Proc, Value, ValueRef};

#[derive(Debug)]
pub enum ParseError {
    Utf8(Utf8Error),
    EOF
}

type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug)]
pub struct Input<'a> {
    slice: &'a [u8],
    index: usize
}

impl<'a> Input<'a> {
    pub fn new(slice: &[u8]) -> Input { Input { slice, index: 0 } }

    fn len(&self) -> usize { self.slice.len() - self.index }

    fn parse_copy<T: Copy>(&mut self) -> ParseResult<T> {
        let size = size_of::<T>();
        if self.len() >= size {
            let ptr: *const T = self.slice[self.index..].as_ptr() as _;
            self.index += size;
            Ok(unsafe { *ptr })
        } else {
            Err(ParseError::EOF)
        }
    }

    fn parse_str(&mut self) -> ParseResult<&str> {
        let len = self.parse_copy::<usize>()?;
        if self.len() >= len {
            let old_index = self.index;
            self.index = self.index + len;
            str::from_utf8(&self.slice[old_index..self.index])
                .map_err(|err| ParseError::Utf8(err))
        } else {
            Err(ParseError::EOF) 
        }
    }
    
    fn parse_char(&mut self) -> ParseResult<char> {
        match str::from_utf8(&self.slice[self.index..]) {
            Ok(str) => {
                let mut cs = str.char_indices();
                if let Some((_, c)) = cs.next() {
                    if let Some((i, _)) = cs.next() {
                        self.index += i;
                    }
                    Ok(c)
                } else {
                    Err(ParseError::EOF)
                }
            },
            Err(err) => Err(ParseError::Utf8(err))
        }
    }

    fn parse_vec<T, F>(&mut self, parse_elem: F) -> ParseResult<Vec<T>>
        where F: Fn(&mut Input) -> ParseResult<T>
    {
        let len = self.parse_copy::<usize>()?;
        (0..len).map(|_| parse_elem(self)).collect()
    }
}

fn parse_string(input: &mut Input) -> ParseResult<String> {
    input.parse_str().map(str::to_string)
}

fn parse_instr(input: &mut Input) -> ParseResult<Instr> {
    input.parse_copy::<u32>().map(Instr::from)
}

fn parse_const(input: &mut Input) -> ParseResult<ValueRef> {
    match input.parse_copy::<u8>()? {
        0 => input.parse_copy::<isize>().map(|i| Gc::new(Value::Int(i))),
        1 => input.parse_char().map(|c| Gc::new(Value::Char(c))),
        2 => parse_string(input).map(|s| Gc::new(Value::Symbol(s))),
        3 => parse_string(input).map(|s| Gc::new(Value::String(s))),
        _ => unimplemented!()
    }
}

fn parse_proc(input: &mut Input) -> ParseResult<Gc<Proc>> {
    let name = parse_string(input)?;
    let consts = input.parse_vec(parse_const)?;
    let instrs = input.parse_vec(parse_instr)?;
    Ok(Gc::new(Proc { name, consts, instrs }))
}

pub fn parse_program(input: &mut Input) -> ParseResult<Program> {
    let register_demand = input.parse_copy::<usize>()?;
    let entry = input.parse_copy::<usize>()?;
    let procs = input.parse_vec(parse_proc)?;
    Ok(Program { register_demand, procs, entry })    
}
