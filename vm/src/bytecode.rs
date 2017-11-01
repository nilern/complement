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
pub struct Atom(u8);

impl Atom {
    pub fn tag(self) -> u8 {
        (self.0 & ATOM_TAG_MASK) as u8 
    }

    pub fn index(self) -> usize {
        self.0 as usize >> ATOM_INDEX_SHIFT
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Instr(u32);

impl Instr {
    pub fn op(self) -> u8 {
        (self.0 & BYTE_MASK) as u8  
    }

    fn reg_arg(self, index: usize) -> usize {
        ((self.0 >> (8*(index + 1))) & BYTE_MASK) as usize   
    }

    fn byte_arg(self, index: usize) -> u8 {
        self.reg_arg(index) as u8
    }

    fn short_arg(self) -> usize {
        (self.0 >> 16) as usize 
    }
    
    fn atom_arg(self, index: usize) -> Atom {
        Atom(self.byte_arg(index))
    }
}

impl From<usize> for Instr {
    fn from(bits: usize) -> Instr {
        Instr(bits as u32)     
    }
}

pub trait ParseFields<T> {
    fn parse(self) -> T;
}

impl ParseFields<u8> for Instr {
    fn parse(self) -> u8 { self.byte_arg(0) }
}

impl ParseFields<Atom> for Instr {
    fn parse(self) -> Atom { self.atom_arg(0) }
}

impl ParseFields<(u8, Atom)> for Instr {
    fn parse(self) -> (u8, Atom) {
        (self.byte_arg(0), self.atom_arg(1))
    }
}

impl ParseFields<(u8, u16)> for Instr {
    fn parse(self) -> (u8, u16) {
        (self.byte_arg(0), self.short_arg() as u16)
    }
}

impl ParseFields<(u8, i16)> for Instr {
    fn parse(self) -> (u8, i16) {
        (self.byte_arg(0), self.short_arg() as i16)
    }
}

impl ParseFields<(u8, Atom, Atom)> for Instr {
    fn parse(self) -> (u8, Atom, Atom) {
        (self.byte_arg(0), self.atom_arg(1), self.atom_arg(2))
    }
}

impl ParseFields<(u8, u8, Atom)> for Instr {
    fn parse(self) -> (u8, u8, Atom) {
        (self.byte_arg(0), self.byte_arg(1), self.atom_arg(2))
    }
}

impl ParseFields<(Atom, i16)> for Instr {
    fn parse(self) -> (Atom, i16) {
        (self.atom_arg(0), self.short_arg() as i16)
    }
}
