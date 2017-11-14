use std::mem::size_of;
use std::marker::PhantomData;
use std::str::{self, Utf8Error};
use gc::Gc;

use data::{Program, Proc, Value, ValueRef};

const BYTE_MASK: u32 = (1 << 8) - 1;
const ATOM_INDEX_SHIFT: usize = 1;
const ATOM_TAG_MASK: u8 = (1 << ATOM_INDEX_SHIFT) - 1;

pub const MOV: u8 = 0x00;

pub const IEQ: u8 = 0x10;
pub const ILT: u8 = 0x11;
pub const ILE: u8 = 0x12;
pub const IGT: u8 = 0x13;
pub const IGE: u8 = 0x14;

pub const INEG: u8 = 0x20;
pub const IADD: u8 = 0x21;
pub const ISUB: u8 = 0x22;
pub const IMUL: u8 = 0x23;
pub const IDIV: u8 = 0x24;
pub const IREM: u8 = 0x25;
pub const IMOD: u8 = 0x26;

pub const BOX_NEW : u8 = 0x30;
pub const BOX_INIT: u8 = 0x31;
pub const BOX_GET : u8 = 0x32;

pub const TUPLE_NEW : u8 = 0x40;
pub const TUPLE_INIT: u8 = 0x41;
pub const TUPLE_LEN : u8 = 0x42;
pub const TUPLE_GET : u8 = 0x43;

pub const FN_NEW      : u8 = 0x50;
pub const FN_INIT_CODE: u8 = 0x51;
pub const FN_INIT     : u8 = 0x52;
pub const FN_CODE     : u8 = 0x53;
pub const FN_GET      : u8 = 0x54;

pub const CONT_NEW      : u8 = 0x60;
pub const CONT_INIT_CODE: u8 = 0x61;
pub const CONT_INIT     : u8 = 0x62;
pub const CONT_CODE     : u8 = 0x63;
pub const CONT_GET      : u8 = 0x64;

pub const DENV_NEW: u8 = 0x70;

pub const REC_NEW      : u8 = 0x80;
pub const REC_INIT_TYPE: u8 = 0x81;
pub const REC_INIT     : u8 = 0x82;
pub const REC_TYPE     : u8 = 0x83;
pub const REC_GET      : u8 = 0x84;

pub const BRF: u8 = 0x91;

pub const IJMP: u8 = 0xA1;

pub const HALT: u8 = 0xB0;

pub const FLIB_OPEN      : u8 = 0xC0;
pub const FLIB_SYM       : u8 = 0xC1;
pub const FFN_NEW        : u8 = 0xC2;
pub const FFN_INIT_TYPE  : u8 = 0xC3;
pub const FFN_INIT_CCONV : u8 = 0xC4;
pub const FFN_CALL       : u8 = 0xC5;

#[derive(Debug, Clone, Copy)]
pub struct AnySrcReg(u8);

#[derive(Debug, Clone, Copy)]
pub struct SrcReg<T>(AnySrcReg, PhantomData<T>);
    
impl<T> From<AnySrcReg> for SrcReg<T> {
    fn from(reg: AnySrcReg) -> SrcReg<T> { SrcReg(reg, PhantomData::default()) }
}

impl<T> From<SrcReg<T>> for AnySrcReg {
    fn from(reg: SrcReg<T>) -> AnySrcReg { reg.0 }
}
    
impl From<AnySrcReg> for usize {
    fn from(reg: AnySrcReg) -> usize { reg.0 as usize }
}

#[derive(Debug, Clone, Copy)]
pub struct DestReg(u8);

impl From<DestReg> for usize {
    fn from(reg: DestReg) -> usize { reg.0 as usize }
}

#[derive(Debug, Clone, Copy)]
pub struct Offset(i16);

impl From<Offset> for isize {
    fn from(offset: Offset) -> isize { offset.0 as isize }
}

#[derive(Debug, Clone, Copy)]
pub struct ProcIndex(u16);

impl From<ProcIndex> for usize {
    fn from(i: ProcIndex) -> usize { i.0 as usize }
}

#[derive(Debug, Clone, Copy)]
pub struct AnyAtom(u8);
    
impl AnyAtom {
    pub fn tag(self) -> u8 { (self.0 & ATOM_TAG_MASK) as u8 }

    pub fn index(self) -> usize { self.0 as usize >> ATOM_INDEX_SHIFT }
}

#[derive(Debug, Clone, Copy)]
pub struct Atom<T>(AnyAtom, PhantomData<T>);

impl<T> From<AnyAtom> for Atom<T> {
    fn from(atom: AnyAtom) -> Atom<T> { Atom(atom, PhantomData::default()) }
}

impl<T> From<Atom<T>> for AnyAtom {
    fn from(atom: Atom<T>) -> AnyAtom { atom.0 }
}

#[derive(Debug, Clone, Copy)]
pub struct Instr(u32);

impl Instr {
    pub fn op(self) -> u8 { (self.0 & BYTE_MASK) as u8 }

    fn byte_arg(self, index: usize) -> u32 {
        let shift = 8 * (index + 1);
        (self.0 >> shift) & BYTE_MASK
    }

    fn u8_arg(self, index: usize) -> u8 { self.byte_arg(index) as u8 }

    fn reg_arg(self, index: usize) -> DestReg { DestReg(self.u8_arg(index)) }
        
    fn src_reg_arg(self, index: usize) -> AnySrcReg { AnySrcReg(self.u8_arg(index)) }
    
    fn atom_arg(self, index: usize) -> AnyAtom { AnyAtom(self.u8_arg(index)) }
        
    fn short_arg(self) -> u32 { self.0 >> 16 }
    
    fn offset_arg(self) -> Offset { Offset(self.short_arg() as i16) }
        
    fn proc_arg(self) -> ProcIndex { ProcIndex(self.short_arg() as u16) }
}

impl From<u32> for Instr {
    fn from(bits: u32) -> Instr { Instr(bits) }
}

pub trait ParseFields<T> {
    fn parse(self) -> T;
}

impl ParseFields<DestReg> for Instr {
    fn parse(self) -> DestReg { self.reg_arg(0) }
}
    
impl<T> ParseFields<SrcReg<T>> for Instr {
    fn parse(self) -> SrcReg<T> { From::from(self.src_reg_arg(0)) }
}
    
impl ParseFields<AnyAtom> for Instr {
    fn parse(self) -> AnyAtom { self.atom_arg(0) }
}

impl<T> ParseFields<Atom<T>> for Instr {
    fn parse(self) -> Atom<T> { Atom::from(self.atom_arg(0)) }
}
    
impl ParseFields<(DestReg, AnyAtom)> for Instr {
    fn parse(self) -> (DestReg, AnyAtom) {
        (self.reg_arg(0), self.atom_arg(1))
    }
}
        
impl<T> ParseFields<(SrcReg<T>, AnyAtom)> for Instr {
    fn parse(self) -> (SrcReg<T>, AnyAtom) {
        (SrcReg::from(self.src_reg_arg(0)), self.atom_arg(1))
    }
}

impl<T> ParseFields<(DestReg, SrcReg<T>)> for Instr {
    fn parse(self) -> (DestReg, SrcReg<T>) {
        (self.reg_arg(0), SrcReg::from(self.src_reg_arg(1)))
    }
}

impl<T> ParseFields<(DestReg, Atom<T>)> for Instr {
    fn parse(self) -> (DestReg, Atom<T>) {
        (self.reg_arg(0), Atom::from(self.atom_arg(1)))
    }
}

impl<T, U> ParseFields<(SrcReg<T>, Atom<U>)> for Instr {
    fn parse(self) -> (SrcReg<T>, Atom<U>) {
        (From::from(self.src_reg_arg(0)), Atom::from(self.atom_arg(1)))
    }
}


impl<T> ParseFields<(SrcReg<T>, ProcIndex)> for Instr {
    fn parse(self) -> (SrcReg<T>, ProcIndex) {
        (From::from(self.src_reg_arg(0)), self.proc_arg())
    }
}

impl<T> ParseFields<(SrcReg<T>, Offset)> for Instr {
    fn parse(self) -> (SrcReg<T>, Offset) {
        (From::from(self.src_reg_arg(0)), self.offset_arg())
    }
}

impl ParseFields<(DestReg, AnyAtom, AnyAtom)> for Instr {
    fn parse(self) -> (DestReg, AnyAtom, AnyAtom) {
        (self.reg_arg(0), self.atom_arg(1), self.atom_arg(2))
    }
}
            
impl<T, U> ParseFields<(SrcReg<T>, SrcReg<U>, AnyAtom)> for Instr {
    fn parse(self) -> (SrcReg<T>, SrcReg<U>, AnyAtom) {
        (SrcReg::from(self.src_reg_arg(0)), From::from(self.src_reg_arg(1)), self.atom_arg(2))
    }
}
            
impl<T, U, V> ParseFields<(SrcReg<T>, SrcReg<U>, Atom<V>)> for Instr {
    fn parse(self) -> (SrcReg<T>, SrcReg<U>, Atom<V>) {
        (SrcReg::from(self.src_reg_arg(0)), From::from(self.src_reg_arg(1)), From::from(self.atom_arg(2)))
    }
}
            
impl<T, U> ParseFields<(SrcReg<T>, Atom<U>, AnyAtom)> for Instr {
    fn parse(self) -> (SrcReg<T>, Atom<U>, AnyAtom) {
        (SrcReg::from(self.src_reg_arg(0)), From::from(self.atom_arg(1)), self.atom_arg(2))
    }
}
        
impl<T> ParseFields<(DestReg, Atom<T>, AnyAtom)> for Instr {
    fn parse(self) -> (DestReg, Atom<T>, AnyAtom) {
        (self.reg_arg(0), From::from(self.atom_arg(1)), self.atom_arg(2))
    }
}
    
impl<T, U> ParseFields<(DestReg, Atom<T>, Atom<U>)> for Instr {
    fn parse(self) -> (DestReg, Atom<T>, Atom<U>) {
        (self.reg_arg(0), From::from(self.atom_arg(1)), From::from(self.atom_arg(2)))
    }
}

impl<T> ParseFields<(DestReg, AnySrcReg, Atom<T>)> for Instr {
    fn parse(self) -> (DestReg, AnySrcReg, Atom<T>) {
        (self.reg_arg(0), self.src_reg_arg(1), Atom::from(self.atom_arg(2)))
    }
}

impl<T, U> ParseFields<(DestReg, SrcReg<T>, Atom<U>)> for Instr {
    fn parse(self) -> (DestReg, SrcReg<T>, Atom<U>) {
        (self.reg_arg(0), From::from(self.src_reg_arg(1)), Atom::from(self.atom_arg(2)))
    }
}

impl<T> ParseFields<(Atom<T>, Offset)> for Instr {
    fn parse(self) -> (Atom<T>, Offset) {
        (Atom::from(self.atom_arg(0)), self.offset_arg())
    }
}
    
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
