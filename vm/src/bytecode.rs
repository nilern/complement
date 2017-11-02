const BYTE_MASK: u32 = (1 << 8) - 1;
const ATOM_INDEX_SHIFT: usize = 1;
const ATOM_TAG_MASK: u8 = (1 << ATOM_INDEX_SHIFT) - 1;

pub const MOV: u8 = 0;
pub const IEQ: u8 = 1;
pub const IADD: u8 = 2;
pub const ISUB: u8 = 3;
pub const IMUL: u8 = 4;

pub const BOX_NEW: u8 = 5;
pub const BOX_INIT: u8 = 6;
pub const BOX_GET: u8 = 7;

pub const TUPLE_NEW: u8 = 8;
pub const TUPLE_INIT: u8 = 9;
pub const TUPLE_LEN: u8 = 10;
pub const TUPLE_GET: u8 = 11;

pub const FN_NEW: u8 = 12;
pub const FN_INIT_CODE: u8 = 13;
pub const FN_INIT: u8 = 14;
pub const FN_CODE: u8 = 15;
pub const FN_GET: u8 = 16;

pub const CONT_NEW: u8 = 17;
pub const CONT_INIT_CODE: u8 = 18;
pub const CONT_INIT: u8 = 19;
pub const CONT_CODE: u8 = 20;
pub const CONT_GET: u8 = 21;

pub const DENV_NEW: u8 = 22;

pub const BRF: u8 = 26;

pub const IJMP: u8 = 28;

pub const HALT: u8 = 29;

#[derive(Debug, Clone, Copy)]
pub struct Reg(u8);

impl From<u8> for Reg {
    fn from(byte: u8) -> Reg { Reg(byte) }
}

impl From<Reg> for usize {
    fn from(reg: Reg) -> usize { reg.0 as usize }
}

#[derive(Debug, Clone, Copy)]
pub struct Offset(i16);

impl From<i16> for Offset {
    fn from(i: i16) -> Offset { Offset(i) }
}

impl From<Offset> for isize {
    fn from(offset: Offset) -> isize { offset.0 as isize }
}

#[derive(Debug, Clone, Copy)]
pub struct ProcIndex(u16);

impl From<u16> for ProcIndex {
    fn from(i: u16) -> ProcIndex { ProcIndex(i) }
}

impl From<ProcIndex> for usize {
    fn from(i: ProcIndex) -> usize { i.0 as usize }
}

#[derive(Debug, Clone, Copy)]
pub struct Atom(u8);

impl Atom {
    pub fn tag(self) -> u8 { (self.0 & ATOM_TAG_MASK) as u8 }

    pub fn index(self) -> usize { self.0 as usize >> ATOM_INDEX_SHIFT }
}

#[derive(Debug, Clone, Copy)]
pub struct Instr(u32);

impl Instr {
    pub fn op(self) -> u8 { (self.0 & BYTE_MASK) as u8 }

    fn byte_arg(self, index: usize) -> u32 {
        (self.0 >> (8*(index + 1))) & BYTE_MASK
    }

    fn u8_arg(self, index: usize) -> u8 { self.byte_arg(index) as u8 }

    fn reg_arg(self, index: usize) -> Reg { Reg::from(self.u8_arg(index)) }
    
    fn atom_arg(self, index: usize) -> Atom { Atom(self.u8_arg(index)) }
        
    fn short_arg(self) -> u32 { self.0 >> 16 }
    
    fn offset_arg(self) -> Offset { Offset::from(self.short_arg() as i16) }
        
    fn proc_arg(self) -> ProcIndex { ProcIndex::from(self.short_arg() as u16) }
}

impl From<usize> for Instr {
    fn from(bits: usize) -> Instr {
        Instr(bits as u32)     
    }
}

pub trait ParseFields<T> {
    fn parse(self) -> T;
}

impl ParseFields<Reg> for Instr {
    fn parse(self) -> Reg { self.reg_arg(0) }
}

impl ParseFields<Atom> for Instr {
    fn parse(self) -> Atom { self.atom_arg(0) }
}

impl ParseFields<(Reg, Atom)> for Instr {
    fn parse(self) -> (Reg, Atom) {
        (self.reg_arg(0), self.atom_arg(1))
    }
}

impl ParseFields<(Reg, ProcIndex)> for Instr {
    fn parse(self) -> (Reg, ProcIndex) {
        (self.reg_arg(0), self.proc_arg())
    }
}

impl ParseFields<(Reg, Offset)> for Instr {
    fn parse(self) -> (Reg, Offset) {
        (self.reg_arg(0), self.offset_arg())
    }
}

impl ParseFields<(Reg, Atom, Atom)> for Instr {
    fn parse(self) -> (Reg, Atom, Atom) {
        (self.reg_arg(0), self.atom_arg(1), self.atom_arg(2))
    }
}

impl ParseFields<(Reg, Reg, Atom)> for Instr {
    fn parse(self) -> (Reg, Reg, Atom) {
        (self.reg_arg(0), self.reg_arg(1), self.atom_arg(2))
    }
}

impl ParseFields<(Atom, Offset)> for Instr {
    fn parse(self) -> (Atom, Offset) {
        (self.atom_arg(0), self.offset_arg())
    }
}
