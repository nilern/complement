use std::mem::size_of;
use std::str::{self, Utf8Error};
use gc::Gc;

use value::{Program, Proc, Value};
use bytecode::Instr;

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
    pub fn new(bytes: &[u8]) -> Input {
        Input {
            slice: bytes,
            index: 0    
        }     
    }

    fn len(&self) -> usize {
        self.slice.len() - self.index    
    }

    fn peek(&self) -> Option<u8> {
        if self.index < self.slice.len() {
            Some(self.slice[self.index])    
        } else {
            None     
        }
    }

    fn pop(&mut self) -> Option<u8> {
        let res = self.peek();
        if res.is_some() {
            self.index += 1;     
        }
        res     
    }

    #[cfg(target_endian = "little")]
    fn parse_usize(&mut self) -> ParseResult<usize> {
        let mut res = 0usize;
        for i in 0..size_of::<usize>() {
             res += (self.pop().ok_or(ParseError::EOF)? as usize) << (8 * i);
        }
        Ok(res)
    }
    
    fn parse_isize(&mut self) -> ParseResult<isize> {
        self.parse_usize().map(|n| n as isize)
    }

    fn parse_str(&mut self, len: usize) -> ParseResult<&str> {
        if self.len() >= len {
            let old_index = self.index;
            self.index = self.index + len;
            str::from_utf8(&self.slice[old_index..self.index])
                .map_err(|err| ParseError::Utf8(err))
        } else {
            Err(ParseError::EOF) 
        }
    }

    fn parse_vec<T, F>(&mut self, len: usize, parse_elem: F) -> ParseResult<Vec<T>>
        where F: Fn(&mut Input) -> ParseResult<T>
    {
        let mut res = Vec::with_capacity(len);
        for _ in 0..len {
            res.push(parse_elem(self)?);     
        }
        Ok(res)
    }
}

fn parse_string(input: &mut Input) -> ParseResult<String> {
    let len = input.parse_usize()?;
    input.parse_str(len).map(str::to_string)
}

fn parse_instr(input: &mut Input) -> ParseResult<Instr> {
    input.parse_usize().map(Instr::from)
}

fn parse_const(input: &mut Input) -> ParseResult<Value> {
    let tag = input.pop().ok_or(ParseError::EOF)?;
    match tag {
        0 => input.parse_isize().map(Value::Int),
        1 => parse_string(input).map(Value::Symbol),
        _ => unimplemented!()
    }
}

fn parse_proc(input: &mut Input) -> ParseResult<Proc> {
    let name = parse_string(input)?;
    let consts_len = input.parse_usize()?;
    let consts = input.parse_vec(consts_len, |input| parse_const(input).map(Gc::new))?;
    let instrs_len = input.parse_usize()?;
    let instrs = input.parse_vec(instrs_len, parse_instr)?;
    Ok(Proc {
        name: name,
        consts: consts,
        instrs: instrs     
    })
}

pub fn parse_program(input: &mut Input) -> ParseResult<Program> {
    let regc = input.parse_usize()?;
    let entry = input.parse_usize()?;
    let procs_len = input.parse_usize()?;
    let procs = input.parse_vec(procs_len, |input| parse_proc(input).map(Gc::new))?;
    Ok(Program {
        register_demand: regc,
        procs: procs,
        entry: entry 
    })    
}
