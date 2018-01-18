use std::marker::PhantomData;

use data::{Tuple, VMBox, Closure, CodePtr, Record, ForeignPtr, ForeignFn};

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

pub const BR : u8 = 0x90;
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

pub enum InstrView<'a> {
    Mov { dest: DestReg, src: AnyAtom },

    IEq { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },
    ILt { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },
    ILe { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },
    IGt { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },
    IGe { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },

    INeg { dest: DestReg, src: Atom<isize> },
    IAdd { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },
    ISub { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },
    IMul { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },
    IDiv { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },
    IRem { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },
    IMod { dest: DestReg, arg1: Atom<isize>, arg2: Atom<isize> },

    BoxNew { dest: DestReg },
    BoxInit { lvbox: SrcReg<&'a VMBox>, value: AnyAtom },
    BoxGet { dest: DestReg, rvbox: Atom<&'a VMBox> },

    TupleNew { dest: DestReg, len: Atom<usize> },
    TupleInit { lvtuple: SrcReg<&'a Tuple>, index: Atom<usize>, value: AnyAtom },
    TupleLen { dest: DestReg, rvtuple: Atom<&'a Tuple> },
    TupleGet { dest: DestReg, rvtuple: Atom<&'a Tuple>, index: Atom<usize> },

    FnNew { dest: DestReg, len: Atom<usize> },
    FnInitCode { lvfn: SrcReg<&'a Closure>, index: ProcIndex },
    FnInit { lvfn: SrcReg<&'a Closure>, index: Atom<usize>, value: AnyAtom },
    FnCode { dest: DestReg, rvfn: Atom<&'a Closure> },
    FnGet { dest: DestReg, rvfn: SrcReg<&'a Closure>, index: Atom<usize> },

    ContNew { dest: DestReg, len: Atom<usize> },
    ContInitCode { lvcont: SrcReg<&'a Closure>, offset: Offset },
    ContInit { lvcont: SrcReg<&'a Closure>, index: Atom<usize>, value: AnyAtom },
    ContCode { dest: DestReg, rvcont: Atom<&'a Closure> },
    ContGet { dest: DestReg, rvcont: SrcReg<&'a Closure>, index: Atom<usize> },

    DenvNew { dest: DestReg },

    RecNew { dest: DestReg, len: Atom<usize> },
    RecInitType { lvrec: SrcReg<&'a Record>, typ: AnyAtom },
    RecInit { lvrec: SrcReg<&'a Record>, index: Atom<usize>, value: AnyAtom },
    RecType { dest: DestReg, rvrec: Atom<&'a Record> },
    RecGet { dest: DestReg, rvrec: Atom<&'a Record>, index: Atom<usize> },

    Br { offset: Offset },
    Brf { cond: Atom<bool>, offset: Offset },

    IJmp { code: SrcReg<&'a CodePtr> },

    Halt { value: AnyAtom },

    FLibOpen { dest: DestReg, path: Atom<&'a str> },
    FLibSym { dest: DestReg, lib: AnySrcReg, name: Atom<&'a str> },
    FFnNew { dest: DestReg, ptr: SrcReg<&'a ForeignPtr> },
    FFnInitType { ffn: SrcReg<&'a ForeignFn>, arg_types: SrcReg<&'a Tuple>, ret_type: AnyAtom },
    FFnInitCConv { ffn: SrcReg<&'a ForeignFn>, conv_name: Atom<&'a str> },
    FFnCall { ffn: SrcReg<&'a ForeignFn> }
}

impl Instr {
    pub fn decode(&self) -> InstrView {
        use self::InstrView::*;

        match self.op() {
            MOV => Mov { dest: self.reg_arg(0), src: self.atom_arg(1) },

            IEQ => IEq { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                         arg2: From::from(self.atom_arg(2)) },
            ILT => ILt { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                         arg2: From::from(self.atom_arg(2)) },
            ILE => ILe { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                         arg2: From::from(self.atom_arg(2)) },
            IGT => IGt { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                         arg2: From::from(self.atom_arg(2)) },
            IGE => IGe { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                         arg2: From::from(self.atom_arg(2)) },

            INEG => INeg { dest: self.reg_arg(0), src: From::from(self.atom_arg(1)) },
            IADD => IAdd { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                           arg2: From::from(self.atom_arg(2)) },
            ISUB => ISub { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                           arg2: From::from(self.atom_arg(2)) },
            IMUL => IMul { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                           arg2: From::from(self.atom_arg(2)) },
            IDIV => IDiv { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                           arg2: From::from(self.atom_arg(2)) },
            IREM => IRem { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                           arg2: From::from(self.atom_arg(2)) },
            IMOD => IMod { dest: self.reg_arg(0), arg1: From::from(self.atom_arg(1)),
                           arg2: From::from(self.atom_arg(2)) },

            BOX_NEW  => BoxNew { dest: self.reg_arg(0) },
            BOX_INIT => BoxInit { lvbox: SrcReg::from(self.src_reg_arg(0)),
                                  value: self.atom_arg(1) },
            BOX_GET  => BoxGet { dest: self.reg_arg(0), rvbox: From::from(self.atom_arg(1)) },

            TUPLE_NEW  => TupleNew { dest: self.reg_arg(0), len: From::from(self.atom_arg(1)) },
            TUPLE_INIT => TupleInit { lvtuple: SrcReg::from(self.src_reg_arg(0)),
                                      index: From::from(self.atom_arg(1)),
                                      value: self.atom_arg(2) },
            TUPLE_LEN  => TupleLen { dest: self.reg_arg(0), rvtuple: From::from(self.atom_arg(1)) },
            TUPLE_GET  => TupleGet { dest: self.reg_arg(0), rvtuple: From::from(self.atom_arg(1)),
                                     index: From::from(self.atom_arg(2)) },

            FN_NEW  => FnNew { dest: self.reg_arg(0), len: From::from(self.atom_arg(1)) },
            FN_INIT_CODE => FnInitCode { lvfn: SrcReg::from(self.src_reg_arg(0)),
                                         index: self.proc_arg() },
            FN_INIT => FnInit { lvfn: SrcReg::from(self.src_reg_arg(0)),
                                index: From::from(self.atom_arg(1)),
                                value: self.atom_arg(2) },
            FN_CODE => FnCode { dest: self.reg_arg(0), rvfn: From::from(self.atom_arg(1)) },
            FN_GET  => FnGet { dest: self.reg_arg(0), rvfn: From::from(self.src_reg_arg(1)),
                               index: From::from(self.atom_arg(2)) },

            CONT_NEW  => ContNew { dest: self.reg_arg(0), len: From::from(self.atom_arg(1)) },
            CONT_INIT_CODE => ContInitCode { lvcont: SrcReg::from(self.src_reg_arg(0)),
                                             offset: self.offset_arg() },
            CONT_INIT => ContInit { lvcont: SrcReg::from(self.src_reg_arg(0)),
                                    index: From::from(self.atom_arg(1)),
                                    value: self.atom_arg(2) },
            CONT_CODE => ContCode { dest: self.reg_arg(0), rvcont: From::from(self.atom_arg(1)) },
            CONT_GET  => ContGet { dest: self.reg_arg(0), rvcont: From::from(self.src_reg_arg(1)),
                                   index: From::from(self.atom_arg(2)) },

            DENV_NEW => DenvNew { dest: self.reg_arg(0) },

            REC_NEW  => RecNew { dest: self.reg_arg(0), len: From::from(self.atom_arg(1)) },
            REC_INIT_TYPE => RecInitType { lvrec: SrcReg::from(self.src_reg_arg(0)),
                                           typ: self.atom_arg(1) },
            REC_INIT => RecInit { lvrec: SrcReg::from(self.src_reg_arg(0)),
                                  index: From::from(self.atom_arg(1)),
                                  value: self.atom_arg(2) },
            REC_TYPE  => RecType { dest: self.reg_arg(0), rvrec: From::from(self.atom_arg(1)) },
            REC_GET   => RecGet { dest: self.reg_arg(0), rvrec: From::from(self.atom_arg(1)),
                                  index: From::from(self.atom_arg(2)) },

            BR  => Br { offset: self.offset_arg() },
            BRF => Brf { cond: From::from(self.atom_arg(0)), offset: self.offset_arg() },

            IJMP => IJmp { code: From::from(self.src_reg_arg(0)) },

            HALT => Halt { value: self.atom_arg(0) },

            FLIB_OPEN => FLibOpen { dest: self.reg_arg(0), path: From::from(self.atom_arg(1)) },
            FLIB_SYM => FLibSym { dest: self.reg_arg(0), lib: self.src_reg_arg(1),
                                  name: From::from(self.atom_arg(2)) },
            FFN_NEW => FFnNew { dest: self.reg_arg(0), ptr: From::from(self.src_reg_arg(1)) },
            FFN_INIT_TYPE => FFnInitType { ffn: From::from(self.src_reg_arg(0)),
                                           arg_types: From::from(self.src_reg_arg(1)),
                                           ret_type: self.atom_arg(2) },
            FFN_INIT_CCONV => FFnInitCConv { ffn: From::from(self.src_reg_arg(0)),
                                             conv_name: From::from(self.atom_arg(1)) },
            FFN_CALL => FFnCall { ffn: From::from(self.src_reg_arg(0)) },

            opcode => panic!("Unknown opcode 0x{:x}", opcode)
        }
    }
}
